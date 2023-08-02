// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A bounded model checker for flyvy programs. Use `translate` to turn a flyvy `Module`
//! into a `BoundedProgram`, then use `interpret` to evaluate it.

use fly::{ouritertools::OurItertools, semantics::*, syntax::*, transitions::*};
use itertools::Itertools;
use std::collections::VecDeque;
use std::fmt::{Debug, Formatter};
use thiserror::Error;

// We use FxHashMap and FxHashSet because the hash function performance is about 25% faster
// and the bounded model checker is essentially a hashing microbenchmark :)
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

/// Map from uninterpreted sort names to their sizes.
// Here is the one place we use a std HashMap. It's not a performance problem because it's not used
// in the inner loop of the model checker, and it provides a more ergonomic public api to this module.
type UniverseBounds = std::collections::HashMap<String, usize>;

fn cardinality(universe: &UniverseBounds, sort: &Sort) -> usize {
    match sort {
        Sort::Bool => 2,
        Sort::Uninterpreted(sort) => *universe.get(sort).unwrap(),
    }
}

/// The result of a successful run of the bounded model checker
#[derive(Debug, PartialEq)]
pub enum CheckerAnswer {
    /// The checker found a counterexample
    Counterexample(Vec<Model>),
    /// The checker did not find a counterexample
    Unknown,
    /// The checker found that the set of states stopped changing
    Convergence,
}

/// The result of an unsuccessful attempt to translate the input module.
#[derive(Error, Debug, PartialEq)]
pub enum TranslationError {
    /// The module contained a sort that wasn't in the universe
    #[error("sort {0} not found in universe {1:#?}")]
    UnknownSort(String, UniverseBounds),
    /// The transition system extraction failed
    #[error("{0}")]
    ExtractionError(ExtractionError),
    /// The translated formula was not a conjunction
    #[error("the set checker currently only handles initial conditions that are a conjunction")]
    InitNotConj,
    /// The transition system extraction found more than one transition relation
    #[error("the set checker currently only handles a single transition relation")]
    MultipleTrs,
    /// The term could not be translated to an imperative transition
    #[error("could not translate to transition {0}")]
    CouldNotTranslateToTransition(Term),
    /// The term could not be translated to a formula
    #[error("could not translate to propositional logic {0}")]
    CouldNotTranslateToFormula(Term),
    /// The term could not be translated to an element of a sort
    #[error("could not translate to element {0}")]
    CouldNotTranslateToElement(Term),
}

/// Combined entry point to both translate and search the module.
pub fn check(
    module: &Module,
    universe: &UniverseBounds,
    depth: Option<usize>,
    compress_traces: TraceCompression,
    print_timing: bool,
) -> Result<CheckerAnswer, TranslationError> {
    let (program, context) = translate(module, universe, print_timing)?;
    match interpret(&program, depth, compress_traces, print_timing) {
        InterpreterResult::Unknown => Ok(CheckerAnswer::Unknown),
        InterpreterResult::Convergence => Ok(CheckerAnswer::Convergence),
        InterpreterResult::Counterexample(trace) => {
            let u = module.signature.sorts.iter().map(|s| universe[s]).collect();
            let states = match compress_traces {
                TraceCompression::Yes => {
                    let (state, depth) = match trace {
                        Trace::Trace(..) => unreachable!(),
                        Trace::CompressedTrace(state, depth) => (state, depth),
                    };
                    println!("counterexample is at depth {depth}, not 0");
                    vec![state]
                }
                TraceCompression::No => match trace {
                    Trace::Trace(states) => states,
                    Trace::CompressedTrace(..) => unreachable!(),
                },
            };
            let models = states
                .into_iter()
                .map(|state| {
                    Model::new(
                        &module.signature,
                        &u,
                        module
                            .signature
                            .relations
                            .iter()
                            .map(|r| {
                                let shape = r
                                    .args
                                    .iter()
                                    .map(|s| cardinality(universe, s))
                                    .chain([2])
                                    .collect();
                                Interpretation::new(&shape, |elements| {
                                    state
                                        .get(context.indices[&(r.name.as_str(), elements.to_vec())])
                                        as Element
                                })
                            })
                            .collect(),
                    )
                })
                .collect();
            Ok(CheckerAnswer::Counterexample(models))
        }
    }
}

/// A map from (name, arguments) pairs to their index in the [BoundedState] bit vector.
#[derive(Debug, PartialEq)]
struct Context<'a> {
    signature: &'a Signature,
    universe: &'a UniverseBounds,
    indices: HashMap<(&'a str, Vec<Element>), usize>,
}

impl Context<'_> {
    /// Compute an index for the given signature and universe bounds
    fn new<'a>(signature: &'a Signature, universe: &'a UniverseBounds) -> Context<'a> {
        let indices = signature
            .relations
            .iter()
            .flat_map(|relation| {
                relation
                    .args
                    .iter()
                    .map(|sort| 0..cardinality(universe, sort))
                    .multi_cartesian_product_fixed()
                    .map(|elements| (relation.name.as_str(), elements))
                    .collect::<Vec<_>>()
            })
            .enumerate()
            .map(|(i, x)| (x, i))
            .collect();
        Context {
            signature,
            universe,
            indices,
        }
    }
}

/// Compile-time upper bound on the bounded universe size.
const STATE_LEN: usize = 128;
type StateData = u8;
const STATE_DATA_BITS: usize = std::mem::size_of::<StateData>() * 8;

/// A state in the bounded system. Conceptually, this is an interpretation of the signature on the
/// bounded universe. We represent states concretely as a bitvector, where each bit represents the
/// presence of a tuple in a relation. The order of the bits is determined by [Context].
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd)]
struct BoundedState([StateData; STATE_LEN / STATE_DATA_BITS]);

impl BoundedState {
    const ZERO: BoundedState = BoundedState([0; STATE_LEN / STATE_DATA_BITS]);

    fn get(&self, index: usize) -> bool {
        assert!(index < STATE_LEN, "STATE_LEN is too small");
        let idx = index / STATE_DATA_BITS;
        // `STATE_DATA_BITS - 1 - ` fixes ordering
        let bit = STATE_DATA_BITS - 1 - (index % STATE_DATA_BITS);

        ((self.0[idx] >> bit) & 1) != 0
    }

    fn set(&mut self, index: usize, value: bool) {
        assert!(index < STATE_LEN, "STATE_LEN is too small");
        let idx = index / STATE_DATA_BITS;
        // `STATE_DATA_BITS - 1 - ` fixes ordering
        let bit = STATE_DATA_BITS - 1 - (index % STATE_DATA_BITS);

        if value {
            self.0[idx] |= 1 << bit;
        } else {
            self.0[idx] &= !(1 << bit);
        }
    }
}

impl Debug for BoundedState {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "[")?;
        let mut max = STATE_LEN - 1;
        while !self.get(max) {
            if max == 0 {
                return write!(f, "]");
            }
            max -= 1;
        }
        for i in 0..=max {
            write!(f, "{}", self.get(i) as usize)?;
        }
        write!(f, "]")
    }
}

/// A BoundedProgram is a set of initial states, a set of transitions, and a safety property
#[derive(Clone, Debug, PartialEq)]
struct BoundedProgram {
    /// List of initial states
    inits: Vec<BoundedState>,
    /// List of transitions to potentially take at each step. The transition relation is the
    /// disjunction of all these transitions.
    trs: Vec<Transition>,
    /// Safety property to check in each reachable state.
    safe: Formula,
}

/// A Transition is a deterministic partial function on states expressed as a guarded update.
/// If the (and of the) guard(s) is true, then the transition is enabled and can step to the updated
/// state.
/// If the (and of the) guard(s) is false, then the transition is not enabled.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Transition {
    guards: Vec<Guard>,
    updates: Vec<Update>,
    slow_guard: Formula,
}

/// A Guard is a logical literal, i.e., a possibly negated relation applied to an argument tuple
/// such as `r(x, y)` or `!r(x, y)`. The relation and argument tuple are represented by an index
/// into an ambient `Context` map.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Guard {
    /// The index representing the relation and argument tuple. Indexes into an ambient `Context`
    /// map.
    index: usize,
    /// True for positive literal, false for negative literal
    value: bool,
}

/// An Update is either an insertion or a removal of a tuple from a relation. The relation and
/// argument tuple are represented by an index into an ambient `Context` map.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Update {
    /// The index representing the relation and argument tuple. Indexes into an ambient `Context`
    /// map.
    index: usize,
    /// True for insertion, false for removal
    formula: Formula,
}

impl Transition {
    fn from_conjunction(trs: impl IntoIterator<Item = Transition>) -> Transition {
        let mut guards: HashSet<_> = HashSet::default();
        let mut updates: HashSet<_> = HashSet::default();
        let mut slow_guard = Formula::always_true();
        for tr in trs {
            guards.extend(tr.guards);
            updates.extend(tr.updates);
            slow_guard = Formula::and([slow_guard, tr.slow_guard]);
        }
        Transition {
            guards: guards.into_iter().sorted().collect(),
            updates: updates.into_iter().sorted().collect(),
            slow_guard,
        }
    }
}

/// Translate a flyvy module into a BoundedProgram, given the bounds on the sort sizes.
/// Universe should contain the sizes of all the sorts in module.signature.sorts.
/// The module is assumed to have already been typechecked.
/// The translator ignores proof blocks.
fn translate<'a>(
    module: &'a Module,
    universe: &'a UniverseBounds,
    print_timing: bool,
) -> Result<(BoundedProgram, Context<'a>), TranslationError> {
    for relation in &module.signature.relations {
        if relation.sort != Sort::Bool {
            panic!("non-bool relations in checker (use Module::convert_non_bool_relations)")
        }
    }

    let context = Context::new(&module.signature, universe);

    for sort in &module.signature.sorts {
        if !universe.contains_key(sort) {
            return Err(TranslationError::UnknownSort(
                sort.clone(),
                universe.clone(),
            ));
        }
    }

    if !module.defs.is_empty() {
        panic!("definitions in checker (use Module::inline_defs)")
    }

    println!("starting translation...");
    let timer = std::time::Instant::now();

    let d = extract(module).map_err(TranslationError::ExtractionError)?;

    let formula = |term| term_to_formula(&normalize(term, &context), &context, &HashMap::default());

    // get cube
    let mut init = BoundedState::ZERO;
    let mut constrained = HashSet::default();
    let inits = formula(Term::and(&d.inits))?;
    for constraint in inits.get_and() {
        if let Formula::Guard(Guard { index, value }) = constraint {
            init.set(index, value);
            constrained.insert(index);
        } else {
            return Err(TranslationError::InitNotConj);
        }
    }
    // enumerate cube
    let mut inits = vec![init];
    for index in 0..context.indices.len() {
        if !constrained.contains(&index) {
            let mut with_unconstrained = inits.clone();
            for init in &mut with_unconstrained {
                init.set(index, true);
            }
            inits.append(&mut with_unconstrained);
        }
    }
    // filter by axioms
    let axiom = formula(Term::and(&d.axioms))?;
    let inits = inits
        .into_iter()
        .filter(|init| axiom.evaluate(init))
        .collect();

    // compute imperative transitions
    assert!(d
        .mutable_axioms(&module.signature.relations)
        .next()
        .is_none());
    let trs = match d.transitions.len() {
        0 => vec![],
        1 => traverse_disjunction(
            &normalize(d.transitions[0].clone(), &context),
            &context,
            &HashMap::default(),
            &|term, assignments| term_to_transition(term, &context, assignments),
        )?,
        _ => return Err(TranslationError::MultipleTrs),
    };
    let trs: Vec<_> = trs
        .into_iter()
        .filter(|tr| tr.slow_guard != Formula::always_false())
        .flat_map(|tr| {
            // get cube
            let mut constrained: HashSet<usize> = HashSet::default();
            for &Update { index, .. } in &tr.updates {
                constrained.insert(index);
            }
            // enumerate cube
            let mut trs = vec![tr];
            for ((name, _), index) in &context.indices {
                let mut relations = module.signature.relations.iter();
                if !constrained.contains(index)
                    && relations.find(|r| &r.name == name).unwrap().mutable
                {
                    let mut with_unconstrained = trs.clone();
                    for i in 0..trs.len() {
                        if !trs[i].guards.iter().any(|g| g.index == *index && g.value) {
                            with_unconstrained[i].updates.push(Update {
                                index: *index,
                                formula: Formula::always_true(),
                            });
                        }
                        if !trs[i].guards.iter().any(|g| g.index == *index && !g.value) {
                            trs[i].updates.push(Update {
                                index: *index,
                                formula: Formula::always_false(),
                            });
                        }
                    }
                    trs.append(&mut with_unconstrained);
                }
            }
            // filter out no-ops
            for tr in &mut trs {
                tr.updates.retain(|update| {
                    update.formula
                        != Formula::Guard(Guard {
                            index: update.index,
                            value: true,
                        })
                });
            }
            trs
        })
        .collect();

    // compute safety property
    let safes = d.proofs.iter().map(|proof| proof.safety.x.clone());
    let safe = formula(Term::and(safes))?;

    if print_timing {
        println!(
            "translation finished in {:0.1}s",
            timer.elapsed().as_secs_f64()
        );
    }

    // do sanity checks on the transitions
    for tr in &trs {
        let mut indices_to_sets: Vec<&str> = Vec::with_capacity(context.indices.len());
        indices_to_sets.resize(context.indices.len(), ""); // cap vs len
        for ((r, _), i) in &context.indices {
            indices_to_sets[*i] = r;
        }

        // check that none of the transitions violate immutability
        for update in &tr.updates {
            if !module
                .signature
                .relations
                .iter()
                .find(|r| r.name == indices_to_sets[update.index])
                .unwrap()
                .mutable
            {
                panic!("one of the generated updates violated immutability");
            }
        }
        // check that all guards and updates target different indices
        for a in &tr.guards {
            if tr.guards.iter().any(|b| a != b && a.index == b.index) {
                panic!("found two guards with the same index\n{tr:?}");
            }
        }
        for a in &tr.updates {
            if tr.updates.iter().any(|b| a != b && a.index == b.index) {
                panic!("found two updates with the same index\n{tr:?}");
            }
        }
        // check no updates are redundant
        for &Guard { index, value } in &tr.guards {
            if tr.updates.contains(&Update {
                index,
                formula: match value {
                    true => Formula::always_true(),
                    false => Formula::always_false(),
                },
            }) {
                panic!("found an update that was redundant with a guard")
            }
        }
        for Update { index, formula } in &tr.updates {
            if let Formula::Guard(guard) = formula {
                if *index == guard.index && guard.value {
                    panic!("found an update that doesn't do anything")
                }
            }
        }
        assert!(tr.slow_guard != Formula::always_false());
    }

    Ok((BoundedProgram { inits, trs, safe }, context))
}

/// A first-order, single-vocabulary propositional formula.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Formula {
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Guard(Guard),
}

impl Formula {
    fn always_true() -> Formula {
        Formula::And(vec![])
    }

    fn always_false() -> Formula {
        Formula::Or(vec![])
    }

    fn and(terms: impl IntoIterator<Item = Formula>) -> Formula {
        let terms: HashSet<_> = terms.into_iter().flat_map(Formula::get_and).collect();
        if terms.iter().any(|term| *term == Formula::always_false()) {
            return Formula::always_false();
        }
        if terms.len() == 1 {
            terms.into_iter().next().unwrap()
        } else {
            Formula::And(terms.into_iter().sorted().collect())
        }
    }

    fn get_and(self) -> Vec<Formula> {
        match self {
            Formula::And(terms) => terms,
            term => vec![term],
        }
    }

    fn or(terms: impl IntoIterator<Item = Formula>) -> Formula {
        let terms: HashSet<_> = terms.into_iter().flat_map(Formula::get_or).collect();
        if terms.iter().any(|term| *term == Formula::always_true()) {
            return Formula::always_true();
        }
        if terms.len() == 1 {
            terms.into_iter().next().unwrap()
        } else {
            Formula::Or(terms.into_iter().sorted().collect())
        }
    }

    fn get_or(self) -> Vec<Formula> {
        match self {
            Formula::Or(terms) => terms,
            term => vec![term],
        }
    }

    fn not(self) -> Formula {
        match self {
            Formula::And(terms) => Formula::or(terms.into_iter().map(Formula::not)),
            Formula::Or(terms) => Formula::and(terms.into_iter().map(Formula::not)),
            Formula::Guard(Guard { index, value }) => Formula::Guard(Guard {
                index,
                value: !value,
            }),
        }
    }

    fn iff(self, other: Formula) -> Formula {
        Formula::or(vec![
            Formula::and(vec![self.clone(), other.clone()]),
            Formula::and(vec![self.not(), other.not()]),
        ])
    }

    fn ite(self, t: Formula, f: Formula) -> Formula {
        Formula::or(vec![
            Formula::and(vec![self.clone(), t]),
            Formula::and(vec![self.not(), f]),
        ])
    }

    fn evaluate(&self, state: &BoundedState) -> bool {
        match self {
            Formula::And(terms) => terms.iter().all(|term| term.evaluate(state)),
            Formula::Or(terms) => terms.iter().any(|term| term.evaluate(state)),
            Formula::Guard(Guard { index, value }) => state.get(*index) == *value,
        }
    }
}

fn normalize(term: Term, context: &Context) -> Term {
    let term = nullary_id_to_app(term, &context.signature.relations);
    let term = fly::term::prime::Next::new(context.signature).normalize(&term);
    term
}

fn nullary_id_to_app(term: Term, relations: &[RelationDecl]) -> Term {
    match term {
        Term::Id(id) if relations.iter().any(|r| r.name == id) => Term::App(id, 0, vec![]),
        Term::App(name, primes, args) => Term::App(
            name,
            primes,
            args.into_iter()
                .map(|arg| nullary_id_to_app(arg, relations))
                .collect(),
        ),
        Term::UnaryOp(op, term) => Term::UnaryOp(op, Box::new(nullary_id_to_app(*term, relations))),
        Term::BinOp(op, a, b) => Term::BinOp(
            op,
            Box::new(nullary_id_to_app(*a, relations)),
            Box::new(nullary_id_to_app(*b, relations)),
        ),
        Term::NAryOp(op, args) => Term::NAryOp(
            op,
            args.into_iter()
                .map(|arg| nullary_id_to_app(arg, relations))
                .collect(),
        ),
        Term::Ite { cond, then, else_ } => Term::Ite {
            cond: Box::new(nullary_id_to_app(*cond, relations)),
            then: Box::new(nullary_id_to_app(*then, relations)),
            else_: Box::new(nullary_id_to_app(*else_, relations)),
        },
        Term::Quantified {
            quantifier,
            binders,
            body,
        } => Term::Quantified {
            quantifier,
            binders,
            body: Box::new(nullary_id_to_app(*body, relations)),
        },
        term => term,
    }
}

fn traverse_disjunction<T>(
    term: &Term,
    context: &Context,
    assignments: &HashMap<String, Element>,
    func: &impl Fn(&Term, &HashMap<String, Element>) -> Result<T, TranslationError>,
) -> Result<Vec<T>, TranslationError> {
    let traverse = |term| traverse_disjunction(term, context, assignments, func);
    let vec: Vec<T> = match term {
        Term::NAryOp(NOp::Or, terms) => {
            let vecs = terms
                .iter()
                .map(traverse)
                .collect::<Result<Vec<Vec<T>>, _>>()?;
            vecs.into_iter().flatten().collect()
        }
        Term::Quantified {
            quantifier: Quantifier::Exists,
            binders,
            body,
        } => {
            let vecs = binders
                .iter()
                .map(|b| cardinality(context.universe, &b.sort))
                .map(|card| (0..card).collect::<Vec<Element>>())
                .multi_cartesian_product_fixed()
                .map(|elements| {
                    let mut new_assignments = assignments.clone();
                    assert_eq!(binders.len(), elements.len());
                    for (binder, element) in binders.iter().zip(elements) {
                        new_assignments.insert(binder.name.to_string(), element);
                    }
                    traverse_disjunction(body, context, &new_assignments, func)
                })
                .collect::<Result<Vec<_>, _>>()?;
            vecs.into_iter().flatten().collect()
        }
        term => vec![func(term, assignments)?],
    };
    Ok(vec)
}

fn term_to_transition(
    term: &Term,
    context: &Context,
    assignments: &HashMap<String, Element>,
) -> Result<Transition, TranslationError> {
    let transition = |term| term_to_transition(term, context, assignments);
    let formula = |term| term_to_formula(term, context, assignments);
    let element = |term| term_to_element(term, context, assignments);

    let transition: Transition = match term {
        Term::NAryOp(NOp::And, terms) => {
            let trs = terms
                .iter()
                .map(transition)
                .collect::<Result<Vec<_>, _>>()?;
            Transition::from_conjunction(trs)
        }
        Term::Quantified {
            quantifier: Quantifier::Forall,
            binders,
            body,
        } => {
            let trs = binders
                .iter()
                .map(|b| cardinality(context.universe, &b.sort))
                .map(|card| (0..card).collect::<Vec<Element>>())
                .multi_cartesian_product_fixed()
                .map(|elements| {
                    let mut new_assignments = assignments.clone();
                    assert_eq!(binders.len(), elements.len());
                    for (binder, element) in binders.iter().zip(elements) {
                        new_assignments.insert(binder.name.to_string(), element);
                    }
                    term_to_transition(body, context, &new_assignments)
                })
                .collect::<Result<Vec<_>, _>>()?;
            Transition::from_conjunction(trs)
        }
        Term::Literal(true) => Transition {
            guards: vec![],
            updates: vec![],
            slow_guard: Formula::always_true(),
        },
        Term::App(_, 0, _) => match formula(term)? {
            Formula::Guard(guard) => Transition {
                guards: vec![guard],
                updates: vec![],
                slow_guard: Formula::always_true(),
            },
            _ => unreachable!(),
        },
        Term::App(name, 1, args) => match formula(&Term::App(name.clone(), 0, args.clone()))? {
            Formula::Guard(Guard { index, value }) => Transition {
                guards: vec![],
                updates: vec![Update {
                    index,
                    formula: match value {
                        true => Formula::always_true(),
                        false => Formula::always_false(),
                    },
                }],
                slow_guard: Formula::always_true(),
            },
            _ => unreachable!(),
        },
        Term::UnaryOp(UOp::Not, body) => {
            let mut tr = transition(body)?;
            if tr.guards.len() == 1
                && tr.updates.is_empty()
                && tr.slow_guard == Formula::always_true()
            {
                tr.guards[0].value = !tr.guards[0].value;
            } else if tr.guards.is_empty()
                && tr.updates.len() == 1
                && tr.slow_guard == Formula::always_true()
            {
                tr.updates[0].formula = tr.updates[0].formula.clone().not();
            } else if tr.guards.is_empty() && tr.updates.is_empty() {
                tr.slow_guard = tr.slow_guard.not();
            } else {
                return Err(TranslationError::CouldNotTranslateToTransition(
                    term.clone(),
                ));
            }
            tr
        }
        Term::BinOp(BinOp::Iff | BinOp::Equals, left, right)
            if matches!(**left, Term::App(_, 1, _)) =>
        {
            if let Term::App(name, 1, args) = &**left {
                let args = args.iter().map(element).collect::<Result<Vec<_>, _>>()?;
                let index = context.indices[&(name.as_str(), args)];
                let formula = formula(right)?;
                Transition {
                    guards: vec![],
                    updates: vec![Update { index, formula }],
                    slow_guard: Formula::always_true(),
                }
            } else {
                unreachable!()
            }
        }
        Term::BinOp(BinOp::NotEquals, left, right) => transition(&Term::UnaryOp(
            UOp::Not,
            Box::new(Term::equals(&**left, &**right)),
        ))?,
        Term::BinOp(BinOp::Implies, left, right) if element(left) == Ok(1) => transition(right)?,
        Term::BinOp(BinOp::Implies, left, _) if element(left) == Ok(0) => Transition {
            guards: vec![],
            updates: vec![],
            slow_guard: Formula::always_true(),
        },
        term => Transition {
            guards: vec![],
            updates: vec![],
            slow_guard: formula(term)?,
        },
    };
    Ok(transition)
}

fn term_to_formula(
    term: &Term,
    context: &Context,
    assignments: &HashMap<String, Element>,
) -> Result<Formula, TranslationError> {
    let formula = |term| term_to_formula(term, context, assignments);
    let element = |term| term_to_element(term, context, assignments);

    let formula: Formula = match term {
        Term::Literal(true) => Formula::always_true(),
        Term::Literal(false) => Formula::always_false(),
        Term::Id(id) => match assignments.get(id) {
            Some(1) => Formula::always_true(),
            Some(0) => Formula::always_false(),
            _ => {
                return Err(TranslationError::CouldNotTranslateToTransition(
                    term.clone(),
                ))
            }
        },
        Term::App(name, 0, args) => {
            let args = args.iter().map(element).collect::<Result<Vec<_>, _>>()?;
            Formula::Guard(Guard {
                index: context.indices[&(name.as_str(), args)],
                value: true,
            })
        }
        Term::UnaryOp(UOp::Not, term) => formula(term)?.not(),
        Term::BinOp(BinOp::Iff, a, b) => formula(a)?.iff(formula(b)?),
        Term::BinOp(BinOp::Equals, a, b) => match (element(a), element(b)) {
            (Ok(a), Ok(b)) if a == b => Formula::always_true(),
            (Ok(a), Ok(b)) if a != b => Formula::always_false(),
            _ => formula(a)?.iff(formula(b)?),
        },
        Term::BinOp(BinOp::NotEquals, a, b) => {
            formula(&Term::BinOp(BinOp::Equals, a.clone(), b.clone()))?.not()
        }
        Term::BinOp(BinOp::Implies, a, b) => Formula::or(vec![formula(a)?.not(), formula(b)?]),
        Term::NAryOp(NOp::And, terms) => {
            Formula::and(terms.iter().map(formula).collect::<Result<Vec<_>, _>>()?)
        }
        Term::NAryOp(NOp::Or, terms) => {
            Formula::or(terms.iter().map(formula).collect::<Result<Vec<_>, _>>()?)
        }
        Term::Ite { cond, then, else_ } => formula(cond)?.ite(formula(then)?, formula(else_)?),
        Term::Quantified {
            quantifier,
            binders,
            body,
        } => {
            let terms = binders
                .iter()
                .map(|b| cardinality(context.universe, &b.sort))
                .map(|card| (0..card).collect::<Vec<Element>>())
                .multi_cartesian_product_fixed()
                .map(|elements| {
                    let mut new_assignments = assignments.clone();
                    assert_eq!(binders.len(), elements.len());
                    for (binder, element) in binders.iter().zip(elements) {
                        new_assignments.insert(binder.name.to_string(), element);
                    }
                    term_to_formula(body, context, &new_assignments)
                })
                .collect::<Result<Vec<_>, _>>()?;
            match quantifier {
                Quantifier::Forall => Formula::and(terms),
                Quantifier::Exists => Formula::or(terms),
            }
        }
        Term::UnaryOp(UOp::Prime | UOp::Always | UOp::Eventually, _)
        | Term::UnaryOp(UOp::Next | UOp::Previous, _)
        | Term::BinOp(BinOp::Until | BinOp::Since, ..)
        | Term::App(..) => return Err(TranslationError::CouldNotTranslateToFormula(term.clone())),
    };
    Ok(formula)
}

fn term_to_element(
    term: &Term,
    context: &Context,
    assignments: &HashMap<String, Element>,
) -> Result<Element, TranslationError> {
    let formula = |term| term_to_formula(term, context, assignments);
    let element = |term| term_to_element(term, context, assignments);

    let element: Element = match term {
        Term::Literal(_)
        | Term::UnaryOp(UOp::Not, ..)
        | Term::BinOp(BinOp::Iff | BinOp::Equals | BinOp::NotEquals | BinOp::Implies, ..)
        | Term::NAryOp(NOp::And | NOp::Or, ..)
        | Term::Quantified { .. } => match formula(term)? {
            formula if formula == Formula::always_true() => 1,
            formula if formula == Formula::always_false() => 0,
            _ => return Err(TranslationError::CouldNotTranslateToElement(term.clone())),
        },
        Term::Id(id) => match assignments.get(id) {
            Some(x) => *x,
            None => panic!("no assignment found for {id}"),
        },
        Term::Ite { cond, then, else_ } => match element(cond)? {
            1 => element(then)?,
            0 => element(else_)?,
            _ => unreachable!(),
        },
        Term::UnaryOp(UOp::Prime | UOp::Always | UOp::Eventually, _)
        | Term::UnaryOp(UOp::Next | UOp::Previous, _)
        | Term::BinOp(BinOp::Until | BinOp::Since, ..)
        | Term::App(..) => return Err(TranslationError::CouldNotTranslateToElement(term.clone())),
    };
    Ok(element)
}

/// Whether to compress traces by keeping only the last state
#[derive(Clone, Copy)]
pub enum TraceCompression {
    /// Compress traces
    Yes,
    /// Don't compress traces
    No,
}

impl From<bool> for TraceCompression {
    fn from(b: bool) -> TraceCompression {
        if b {
            TraceCompression::Yes
        } else {
            TraceCompression::No
        }
    }
}

/// A sequence of states that may or may not be compressed. Here, a "compressed" trace is just its
/// last state together with its depth. (The depth of a trace is the number of transitions it
/// contains, or one less than the number of states it contains.)
#[derive(Clone, Debug, PartialEq)]
enum Trace {
    /// Uncompressed trace, which keeps all states
    Trace(Vec<BoundedState>),
    /// Compressed trace, keeping only the last state and its depth
    CompressedTrace(BoundedState, usize),
}

impl Trace {
    /// Construct a singleton trace. Note that the decision of whether to compress or not is made at
    /// construction time. If the trace is constructed as compressed (`TraceCompression::Yes`), then
    /// future calls to `push` on this trace will only increment the depth and replace the (one)
    /// state.
    fn new(state: BoundedState, compression: TraceCompression) -> Trace {
        match compression {
            TraceCompression::Yes => Trace::CompressedTrace(state, 0),
            TraceCompression::No => Trace::Trace(vec![state]),
        }
    }

    /// The depth of this trace, which is the number of transitions it represents.
    fn depth(&self) -> usize {
        match self {
            Trace::CompressedTrace(_, n) => *n,
            Trace::Trace(v) => v.len() - 1,
        }
    }

    /// The last state of a trace. Since all traces are constructed to be nonempty, this never fails.
    fn last(&self) -> &BoundedState {
        match self {
            Trace::CompressedTrace(s, _) => s,

            // unwrap is safe here since there's no way to construct an empty trace
            Trace::Trace(v) => v.last().unwrap(),
        }
    }

    /// Extend the trace with one new state on the end. Note that if `self` is a compressed trace,
    /// then only the last state is tracked, so `push` will lose the information about the previous
    /// state.
    fn push(&mut self, state: BoundedState) {
        match self {
            Trace::CompressedTrace(s, n) => {
                *s = state;
                *n += 1;
            }
            Trace::Trace(v) => {
                v.push(state);
            }
        }
    }
}

/// The bounded model checker will either find a counterexample or say "no bugs found"
#[derive(Debug, PartialEq)]
enum InterpreterResult {
    /// The checker found a counterexample, here it is
    Counterexample(Trace),
    /// The checker could not find any counterexamples
    Unknown,
    /// The checker found that the set of states stopped changing
    Convergence,
}

/// Explore reachable states of a BoundedProgram up to (and including) the given max_depth using
/// breadth-first search.
///
/// Note that max_depth refers to the number of transitions, not the number of states,
/// so if max_depth is Some(3), it means there will be 3 transitions (so 4 states).
/// If max_depth is None, it means "no upper bound". The program will run until its
/// state space is exhausted or the process is killed.
fn interpret(
    program: &BoundedProgram,
    max_depth: Option<usize>,
    compress_traces: TraceCompression,
    print_timing: bool,
) -> InterpreterResult {
    // States we have seen so far.
    let mut seen: HashSet<BoundedState> = program.inits.iter().cloned().collect();

    // The BFS queue, i.e., states on the frontier that need to be explored.
    // The queue is always a subset of seen.
    let mut queue: VecDeque<Trace> = program
        .inits
        .iter()
        .cloned()
        .map(|state| Trace::new(state, compress_traces))
        .collect();

    let mut transitions = Transitions::new();
    for tr in &program.trs {
        transitions.insert(tr);
    }

    let mut current_depth = 0;
    let start_time = std::time::Instant::now();
    println!(
        "starting search from depth 0. there are {} initial states in the queue.",
        queue.len()
    );

    while let Some(trace) = queue.pop_front() {
        let depth = trace.depth();
        if depth > current_depth {
            current_depth += 1;
            if print_timing {
                print!("({:0.1}s since start) ", start_time.elapsed().as_secs_f64());
            }
            println!(
                "considering new depth: {current_depth}. \
                 queue length is {}. seen {} unique states.",
                queue.len(),
                seen.len()
            );
        }

        let state = trace.last();
        if !program.safe.evaluate(state) {
            return InterpreterResult::Counterexample(trace);
        }

        if max_depth.map(|md| depth < md).unwrap_or(true) {
            let trs = transitions.get_subsets(state);

            for tr in trs {
                let mut next = *state;
                tr.updates
                    .iter()
                    .for_each(|update| next.set(update.index, update.formula.evaluate(state)));
                if !seen.contains(&next) {
                    seen.insert(next);
                    if seen.len() % 1_000_000 == 0 {
                        let elapsed = start_time.elapsed().as_secs_f64();
                        println!(
                            "progress report: ({elapsed:0.1}s since start) considering depth {current_depth}. \
                             queue length is {}. visited {} states.",
                            queue.len(),
                            seen.len()
                        );
                    }
                    let mut trace = trace.clone();
                    trace.push(next);
                    queue.push_back(trace);
                }
            }
        }
    }

    if max_depth.map(|md| current_depth < md).unwrap_or(true) {
        InterpreterResult::Convergence
    } else {
        InterpreterResult::Unknown
    }
}

/// A set of transitions indexed by their guards, i.e., a map from guards to transitions. We use a
/// set trie data structure that allows efficiently answering the question "give me all the
/// transitions whose guard sets are *subsets* of the given set". During model checking, this allows
/// efficiently retrieving the set of enabled transitions in a given state without searching through
/// all transitions.
#[derive(Clone, Debug)]
struct Transitions<'a> {
    data: Vec<&'a Transition>,
    children: HashMap<&'a Guard, Transitions<'a>>,
}

impl<'a> Transitions<'a> {
    /// Construct an empty set of transitions
    fn new() -> Transitions<'a> {
        Transitions {
            data: Vec::new(),
            children: HashMap::default(),
        }
    }

    /// Insert the given transition into the set
    fn insert(&mut self, value: &'a Transition) {
        self.insert_from_iter(value.guards.iter(), value)
    }

    // Recursive helper function to insert an iterator of guards into the trie
    fn insert_from_iter(
        &mut self,
        mut set: impl Iterator<Item = &'a Guard>,
        value: &'a Transition,
    ) {
        match set.next() {
            None => {
                self.data.push(value);
            }
            Some(key) => self
                .children
                .entry(key)
                .or_insert_with(Transitions::new)
                .insert_from_iter(set, value),
        }
    }

    /// Get all the transitions whose guards are a subset of the given set.
    fn get_subsets(&self, set: &BoundedState) -> Vec<&'a Transition> {
        let mut out = vec![];
        self.get_subsets_into_vec(set, &mut out);
        out
    }

    // Destination passing style helper to recursively collect all the transitions whose guards are
    // a subset of the given set.
    fn get_subsets_into_vec(&self, set: &BoundedState, out: &mut Vec<&'a Transition>) {
        out.extend(self.data.iter().filter(|tr| tr.slow_guard.evaluate(set)));
        for (key, child) in &self.children {
            if set.get(key.index) == key.value {
                child.get_subsets_into_vec(set, out);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fly::sorts::sort_check_and_infer;

    fn includes(set: &str, elements: Vec<Element>, context: &Context) -> Guard {
        Guard {
            index: context.indices[&(set, elements)],
            value: true,
        }
    }
    fn excludes(set: &str, elements: Vec<Element>, context: &Context) -> Guard {
        Guard {
            index: context.indices[&(set, elements)],
            value: false,
        }
    }
    fn insert(set: &str, elements: Vec<Element>, context: &Context) -> Update {
        Update {
            index: context.indices[&(set, elements)],
            formula: Formula::always_true(),
        }
    }
    fn remove(set: &str, elements: Vec<Element>, context: &Context) -> Update {
        Update {
            index: context.indices[&(set, elements)],
            formula: Formula::always_false(),
        }
    }
    fn transition(guards: Vec<Guard>, updates: Vec<Update>) -> Transition {
        Transition {
            guards: guards.into_iter().sorted().collect(),
            updates: updates.into_iter().sorted().collect(),
            slow_guard: Formula::always_true(),
        }
    }
    fn state(iter: impl IntoIterator<Item = u8>) -> BoundedState {
        let mut out = BoundedState::ZERO;
        for (i, x) in iter.into_iter().enumerate() {
            out.set(i, x == 1);
        }
        out
    }

    #[test]
    fn checker_set_states() {
        let mut s = state([0, 1, 0, 1]);

        assert!(!s.get(0));
        assert!(s.get(1));
        assert!(!s.get(2));
        assert!(s.get(3));

        s.set(0, true);
        s.set(2, true);

        assert!(s.get(0));
        assert!(s.get(1));
        assert!(s.get(2));
        assert!(s.get(3));

        s.set(2, false);
        s.set(3, false);

        assert!(s.get(0));
        assert!(s.get(1));
        assert!(!s.get(2));
        assert!(!s.get(3));

        let mut a = BoundedState::ZERO;
        let mut b = BoundedState::ZERO;
        a.0[1] = 1; // [0, 1, 0, 0, ...]
        b.0[0] = 1; // [1, 0, 0, 0, ...]
        assert!(a < b);

        assert!(state([0]) < state([1]));
        assert!(state([0, 1, 0, 1]) < state([1, 0, 1, 0]));
        assert!(state([0, 1, 0, 0]) < state([0, 1, 0, 1]));
        assert!(state([0, 0, 1, 1]) < state([0, 1, 0, 0]));
        assert!(state([0, 0, 1, 0]) < state([0, 0, 1, 1]));
    }

    #[test]
    fn checker_set_basic() {
        let program = BoundedProgram {
            inits: vec![state([0])],
            trs: vec![
                transition(vec![], vec![]),
                transition(
                    vec![],
                    vec![Update {
                        index: 0,
                        formula: Formula::always_true(),
                    }],
                ),
            ],
            safe: Formula::Guard(Guard {
                index: 0,
                value: false,
            }),
        };
        let result0 = interpret(&program, Some(0), TraceCompression::No, false);
        let result1 = interpret(&program, Some(1), TraceCompression::No, false);
        assert_eq!(result0, InterpreterResult::Unknown);
        let mut expected1 = Trace::new(state([0]), TraceCompression::No);
        expected1.push(state([1]));
        assert_eq!(result1, InterpreterResult::Counterexample(expected1));
    }

    #[test]
    fn checker_set_cycle() {
        let program = BoundedProgram {
            inits: vec![state([1, 0, 0, 0])],
            trs: vec![
                transition(
                    vec![Guard {
                        index: 0,
                        value: true,
                    }],
                    vec![
                        Update {
                            index: 0,
                            formula: Formula::always_false(),
                        },
                        Update {
                            index: 1,
                            formula: Formula::always_true(),
                        },
                    ],
                ),
                transition(
                    vec![Guard {
                        index: 1,
                        value: true,
                    }],
                    vec![
                        Update {
                            index: 1,
                            formula: Formula::always_false(),
                        },
                        Update {
                            index: 2,
                            formula: Formula::always_true(),
                        },
                    ],
                ),
                transition(
                    vec![Guard {
                        index: 2,
                        value: true,
                    }],
                    vec![
                        Update {
                            index: 2,
                            formula: Formula::always_false(),
                        },
                        Update {
                            index: 3,
                            formula: Formula::always_true(),
                        },
                    ],
                ),
                transition(
                    vec![Guard {
                        index: 3,
                        value: true,
                    }],
                    vec![
                        Update {
                            index: 3,
                            formula: Formula::always_false(),
                        },
                        Update {
                            index: 0,
                            formula: Formula::always_true(),
                        },
                    ],
                ),
            ],
            safe: Formula::Guard(Guard {
                index: 3,
                value: false,
            }),
        };
        let result1 = interpret(&program, Some(0), TraceCompression::No, false);
        let result2 = interpret(&program, Some(1), TraceCompression::No, false);
        let result3 = interpret(&program, Some(2), TraceCompression::No, false);
        let result4 = interpret(&program, Some(3), TraceCompression::No, false);
        let result5 = interpret(&program, Some(4), TraceCompression::No, false);
        assert_eq!(result1, InterpreterResult::Unknown);
        assert_eq!(result2, InterpreterResult::Unknown);
        assert_eq!(result3, InterpreterResult::Unknown);
        let mut expected4 = Trace::new(state([1, 0, 0, 0]), TraceCompression::No);
        for state in [
            state([0, 1, 0, 0]),
            state([0, 0, 1, 0]),
            state([0, 0, 0, 1]),
        ] {
            expected4.push(state);
        }
        assert_eq!(result4, InterpreterResult::Counterexample(expected4));
        assert_eq!(result5, result4);
    }

    #[test]
    fn checker_set_lockserver_translation() -> Result<(), TranslationError> {
        let source = include_str!("../../temporal-verifier/examples/lockserver.fly");

        let mut m = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut m).unwrap();
        let universe = std::collections::HashMap::from([("node".to_string(), 2)]);
        let context = Context::new(&m.signature, &universe);

        let trs = vec![
            transition(
                vec![includes("grant_msg", vec![0], &context)],
                vec![
                    insert("holds_lock", vec![0], &context),
                    remove("grant_msg", vec![0], &context),
                ],
            ),
            transition(
                vec![includes("grant_msg", vec![1], &context)],
                vec![
                    insert("holds_lock", vec![1], &context),
                    remove("grant_msg", vec![1], &context),
                ],
            ),
            transition(
                vec![includes("holds_lock", vec![0], &context)],
                vec![
                    insert("unlock_msg", vec![0], &context),
                    remove("holds_lock", vec![0], &context),
                ],
            ),
            transition(
                vec![includes("holds_lock", vec![1], &context)],
                vec![
                    insert("unlock_msg", vec![1], &context),
                    remove("holds_lock", vec![1], &context),
                ],
            ),
            transition(
                vec![
                    includes("lock_msg", vec![0], &context),
                    includes("server_holds_lock", vec![], &context),
                ],
                vec![
                    insert("grant_msg", vec![0], &context),
                    remove("lock_msg", vec![0], &context),
                    remove("server_holds_lock", vec![], &context),
                ],
            ),
            transition(
                vec![
                    includes("lock_msg", vec![1], &context),
                    includes("server_holds_lock", vec![], &context),
                ],
                vec![
                    insert("grant_msg", vec![1], &context),
                    remove("lock_msg", vec![1], &context),
                    remove("server_holds_lock", vec![], &context),
                ],
            ),
            transition(
                vec![includes("unlock_msg", vec![0], &context)],
                vec![
                    insert("server_holds_lock", vec![], &context),
                    remove("unlock_msg", vec![0], &context),
                ],
            ),
            transition(
                vec![includes("unlock_msg", vec![1], &context)],
                vec![
                    insert("server_holds_lock", vec![], &context),
                    remove("unlock_msg", vec![1], &context),
                ],
            ),
            transition(vec![], vec![insert("lock_msg", vec![0], &context)]),
            transition(vec![], vec![insert("lock_msg", vec![1], &context)]),
        ];

        let expected = BoundedProgram {
            inits: vec![state([0, 0, 0, 0, 0, 0, 0, 0, 1])],
            trs,
            safe: Formula::Or(vec![
                Formula::Guard(excludes("holds_lock", vec![0], &context)),
                Formula::Guard(excludes("holds_lock", vec![1], &context)),
            ]),
        };

        let (target, _) = translate(&m, &universe, false)?;
        assert_eq!(target.inits, expected.inits);
        assert_eq!(target.safe, expected.safe);
        assert_eq!(
            expected.trs.iter().sorted().collect::<Vec<_>>(),
            target.trs.iter().sorted().collect::<Vec<_>>(),
        );

        let output = interpret(&target, None, TraceCompression::No, false);
        assert_eq!(output, InterpreterResult::Convergence);

        Ok(())
    }

    #[test]
    fn checker_set_lockserver_buggy() -> Result<(), TranslationError> {
        let source = include_str!("../../temporal-verifier/tests/examples/lockserver_buggy.fly");

        let mut m = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut m).unwrap();
        let universe = std::collections::HashMap::from([("node".to_string(), 2)]);
        let (target, _) = translate(&m, &universe, false)?;

        let bug = interpret(&target, Some(12), TraceCompression::No, false);
        if let InterpreterResult::Counterexample(trace) = &bug {
            assert_eq!(trace.depth(), 12);
        } else {
            assert!(matches!(bug, InterpreterResult::Counterexample(_)));
        }

        let too_short = interpret(&target, Some(11), TraceCompression::No, false);
        assert_eq!(too_short, InterpreterResult::Unknown);

        Ok(())
    }

    #[test]
    fn checker_set_consensus() -> Result<(), TranslationError> {
        let source = include_str!("../../temporal-verifier/examples/consensus.fly");

        let mut m = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut m).unwrap();
        let universe = std::collections::HashMap::from([
            ("node".to_string(), 2),
            ("quorum".to_string(), 2),
            ("value".to_string(), 2),
        ]);
        let output = check(&m, &universe, Some(10), TraceCompression::No, false)?;
        assert_eq!(output, CheckerAnswer::Unknown);

        Ok(())
    }

    #[test]
    fn checker_set_immutability() {
        let source =
            include_str!("../../temporal-verifier/tests/examples/success/immutability.fly");
        let mut module = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();
        let universe = std::collections::HashMap::new();
        assert_eq!(
            Ok(CheckerAnswer::Convergence),
            check(&module, &universe, Some(10), true.into(), false)
        );
    }

    #[test]
    fn checker_set_copy_relation_size() -> Result<(), TranslationError> {
        let source = "
sort x
mutable f(x): bool
mutable g(x): bool

assume forall a:x. !f(a) & !g(a)
assume always forall a:x. ((g'(a) <-> f(a)) & (f'(a) <-> f(a)))
        ";
        let mut m = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut m).unwrap();
        let universe = std::collections::HashMap::from([("x".to_string(), 5)]);
        let (target, _) = translate(&m, &universe, false)?;
        assert_eq!(1, target.trs.len());
        Ok(())
    }
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A bounded model checker for flyvy programs. Use `translate` to turn a flyvy Module
//! into a bounded::Program, then use `interpret` to evaluate it.

use crate::fly::{sorts::*, syntax::*};
use bitvec::prelude::*;
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};
use itertools::Itertools;
use std::collections::{BTreeSet, VecDeque};
use std::iter::zip;
use thiserror::Error;

macro_rules! btreeset {
    ($($v:expr),* $(,)?) => {{
        BTreeSet::from([$($v,)*])
    }};
}

/// Upper bounds on sizes of arrays
const ELEMENT_LEN: usize = 15; // should be 1 less than a multiple of 8
const STATE_LEN: usize = 128; // should be a multiple of 64

/// This is not the same as a semantics::Element
/// This is a tuple of semantics::Elements that represents the arguments to a relation
/// We use a fixed size array to avoid allocating a Vec
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Element {
    len: u8,
    data: [u8; ELEMENT_LEN],
}
impl Element {
    /// Creates a new elemnt from the given vector
    pub fn new(vec: Vec<usize>) -> Element {
        let len = vec.len();
        if len > ELEMENT_LEN {
            todo!("raise ELEMENT_LEN to {}", (len >> 3) * 8 + 15);
        }
        let mut out = Element {
            len: len as u8,
            data: [0; ELEMENT_LEN],
        };
        for (i, x) in vec.into_iter().enumerate() {
            if let Ok(x) = x.try_into() {
                out.data[i] = x;
            } else {
                todo!("sort size was too large, increase Element data type");
            }
        }
        out
    }
}
impl std::fmt::Debug for Element {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "[")?;
        if self.len > 0 {
            write!(f, "{:?}", self.data[0])?;
            for x in &self.data[1..self.len as usize] {
                write!(f, ", {:?}", x)?;
            }
        }
        write!(f, "]")
    }
}
macro_rules! element {
    ($($v:expr),* $(,)?) => {{
        Element::new(vec![$($v,)*])
    }};
}

/// Represents all (set, element) pairs with a bit for each one's inclusion
#[derive(Clone, Debug, Eq, PartialOrd, Ord)]
pub struct State(BitArr!(for STATE_LEN));

impl std::hash::Hash for State {
    fn hash<H>(&self, h: &mut H)
    where
        H: std::hash::Hasher,
    {
        usize::hash_slice(self.0.as_raw_slice(), h)
    }
}

impl PartialEq for State {
    fn eq(&self, other: &State) -> bool {
        let xs = self.0.as_raw_slice();
        let ys = other.0.as_raw_slice();
        let mut i = 0;
        while i < xs.len() {
            if xs[i] != ys[i] {
                return false;
            }
            i += 1;
        }
        true
    }
}

// holds an ordering of all (relation, element) pairs
struct Indices<'a>(HashMap<(&'a str, Element), usize>);

impl Indices<'_> {
    fn new<'a>(signature: &'a Signature, universe: &'a Universe) -> Indices<'a> {
        let indices = signature
            .relations
            .iter()
            .flat_map(|relation| {
                if relation.args.is_empty() {
                    vec![(relation.name.as_str(), (element![]))]
                } else {
                    relation
                        .args
                        .iter()
                        .map(|sort| cardinality(universe, sort))
                        .map(|card| (0..card).collect::<Vec<usize>>())
                        .multi_cartesian_product()
                        .map(|element| (relation.name.as_str(), Element::new(element)))
                        .collect()
                }
            })
            .enumerate()
            .map(|(i, x)| (x, i))
            .collect();
        Indices(indices)
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}

impl<'a> std::ops::Index<&'a (&'a str, Element)> for Indices<'a> {
    type Output = usize;
    fn index(&self, key: &'a (&'a str, Element)) -> &usize {
        &self.0[key]
    }
}

/// A Program is a set of initial states, a set of transitions, and a safety property
#[derive(Clone, Debug, PartialEq)]
pub struct Program {
    /// List of initial states
    inits: Vec<State>,
    /// Set of transitions to potentially take at each timestep
    pub trs: Vec<Transition>,
    /// Disjunction of conjunction of guards that the interpreter will verify always hold
    safes: Vec<Vec<Guard>>,
}

/// A Transition is a guarded function from one state to another
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Transition {
    guards: Vec<Guard>,
    updates: Vec<Update>,
}

impl Transition {
    /// Helper function to initialize a Transition
    pub fn new(guards: Vec<Guard>, updates: Vec<Update>) -> Transition {
        Transition { guards, updates }
    }
}

/// A Guard is either an inclusion or an exclusion assertion of an element from a set
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Guard {
    index: usize,
    value: bool,
}

/// An Update is either an insertion or a removal of an element from a set
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Update {
    index: usize,
    value: bool,
}

/// We use a set trie to optimize looping over all guards
#[derive(Clone, Debug)]
struct Transitions<'a> {
    data: Vec<&'a Transition>,
    children: HashMap<&'a Guard, Transitions<'a>>,
}

impl<'a> Transitions<'a> {
    fn new() -> Transitions<'a> {
        Transitions {
            data: Vec::new(),
            children: HashMap::default(),
        }
    }

    /// set should be sorted
    fn insert(&mut self, mut set: impl Iterator<Item = &'a Guard>, value: &'a Transition) {
        match set.next() {
            None => {
                self.data.push(value);
            }
            Some(key) => self
                .children
                .entry(key)
                .or_insert_with(Transitions::new)
                .insert(set, value),
        }
    }

    fn get(&self, set: &State, out: &mut Vec<&'a Transition>) {
        out.extend(self.data.iter().cloned());
        for (key, child) in &self.children {
            if set.0[key.index] == key.value {
                child.get(set, out);
            }
        }
    }
}

/// A sequence of states that may or may not be compressed only the last state.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Trace {
    /// Uncompressed trace, which keeps all states
    Trace(Vec<State>),
    /// Compressed trace, keeping only the last state and its depth
    CompressedTrace(State, usize),
}

impl Trace {
    fn new(state: State, compressed: bool) -> Trace {
        if compressed {
            Trace::CompressedTrace(state, 1)
        } else {
            Trace::Trace(vec![state])
        }
    }

    fn len(&self) -> usize {
        match self {
            Trace::CompressedTrace(_, n) => *n,
            Trace::Trace(v) => v.len(),
        }
    }

    fn last(&self) -> &State {
        match self {
            Trace::CompressedTrace(s, _) => s,

            // unwrap is safe here since there's no way to construct an empty trace
            Trace::Trace(v) => v.last().unwrap(),
        }
    }

    fn push(&mut self, state: State) {
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

/// A bounded model checker will either find a counterexample or else not tell us anything
#[derive(Debug, PartialEq)]
pub enum InterpreterResult {
    /// The checker found a counterexample, here it is
    Counterexample(Trace),
    /// The checker could not find any counterexamples
    Unknown,
}

/// Run a given Program out to some depth
/// Note that max_depth refers to the number of timesteps,
/// e.g. a max_depth of 0 means only evaluate the initial states
#[allow(dead_code)]
pub fn interpret(program: &Program, max_depth: usize, compress_traces: bool) -> InterpreterResult {
    let mut queue: VecDeque<Trace> = program
        .inits
        .iter()
        .map(|state| Trace::new(state.clone(), compress_traces))
        .collect();
    // cache stores states that have ever been present in the queue
    let mut cache: HashSet<State> = program.inits.iter().cloned().collect();

    let mut transitions = Transitions::new();
    for tr in &program.trs {
        transitions.insert(tr.guards.iter(), tr);
    }

    let mut current_depth = 0;
    let start_time = std::time::Instant::now();
    println!(
        "considering depth {}. queue length is {}",
        current_depth,
        queue.len()
    );

    while let Some(trace) = queue.pop_front() {
        let depth = trace.len() - 1;
        if depth > current_depth {
            current_depth += 1;
            let now = std::time::Instant::now();
            let delta = now - start_time;
            println!(
                "({:?} since start) considering depth {}. queue length is {}. visited {} states.",
                delta,
                current_depth,
                queue.len(),
                cache.len()
            );
        }

        let state = trace.last();
        if !program.safes.iter().any(|guards| {
            guards
                .iter()
                .all(|guard| state.0[guard.index] == guard.value)
        }) {
            return InterpreterResult::Counterexample(trace);
        }

        if depth < max_depth {
            let mut trs = vec![];
            transitions.get(state, &mut trs);

            for tr in trs {
                let mut next = state.clone();
                tr.updates
                    .iter()
                    .for_each(|update| next.0.set(update.index, update.value));
                if !cache.contains(&next) {
                    cache.insert(next.clone());
                    if cache.len() % 1_000_000 == 0 {
                        println!("intermediate cache update ({:?} since start) considering depth {}. queue length is {}. visited {} states.", start_time.elapsed(), current_depth, queue.len(), cache.len());
                    }
                    let mut trace = trace.clone();
                    trace.push(next);
                    queue.push_back(trace);
                }
            }
        }
    }

    InterpreterResult::Unknown
}

#[allow(missing_docs)]
#[derive(Error, Debug, PartialEq)]
pub enum TranslationError {
    #[error("sort checking error: {0}")]
    SortError(SortError),
    #[error("sort {0} not found in universe {1:#?}")]
    UnknownSort(String, Universe),
    #[error("all assumes should precede all asserts, but found {0:?}")]
    OutOfOrderStatement(ThmStmt),
    #[error("expected no primes or only one prime in {0:#?}")]
    TooFuture(Term),
    #[error("found an assert that isn't a safety property")]
    AssertWithoutAlways(Term),
    #[error("unknown identifier {0}")]
    UnknownId(String),
    #[error("can't translate term ({0}) with context {1:#?}")]
    UnsupportedTerm(Term, HashMap<String, usize>),
    #[error("could not reduce term {0:#?} to an element")]
    NoValue(Valued),
    #[error("we don't support negating no-ops, but found {0:?}")]
    NegatedNoOp(Valued),
    #[error("expected guard, found: {0:#?}")]
    ExpectedGuard(Valued),
    #[error("expected update, found: {0:#?}")]
    ExpectedUpdate(Valued),
    #[error("expected guard or update, found: {0:#?}")]
    ExpectedGuardOrUpdate(Valued),
    #[error("one of the generated updates updated the immutable relation {0}")]
    UpdateViolatedImmutability(String),
    #[error("transition did not constrain all elements in relation {0}")]
    UnconstrainedTransition(String),
}

/// Map from uninterpreted sort names to sizes
// We use a std HashMap because this isn't hot and it's part of the API
type Universe = std::collections::HashMap<String, usize>;

/// Translate a flyvy module into a bounded::Program, given the bounds on the sort sizes.
/// Universe should contain the sizes of all the sorts in module.signature.sorts.
/// The module is mutable for sort inference, but the caller should not rely on
/// this being the only change that translation makes to the module.
#[allow(dead_code)]
pub fn translate(module: &mut Module, universe: &Universe) -> Result<Program, TranslationError> {
    for relation in &module.signature.relations {
        if relation.sort != Sort::Bool {
            todo!("non-bool relations")
        }
    }

    if let Err((e, _)) = sort_check_and_infer(module) {
        return Err(TranslationError::SortError(e));
    }

    let indices = Indices::new(&module.signature, universe);

    for sort in &module.signature.sorts {
        if !universe.contains_key(sort) {
            return Err(TranslationError::UnknownSort(
                sort.clone(),
                universe.clone(),
            ));
        }
    }

    if !module.defs.is_empty() {
        todo!("definitions are not supported yet");
    }

    let mut assumes = Vec::new();
    let mut asserts = Vec::new();
    for statement in &module.statements {
        match statement {
            ThmStmt::Assume(term) if asserts.is_empty() => assumes.push(term.clone()),
            ThmStmt::Assert(Proof { assert, invariants }) => {
                asserts.push(assert.x.clone());
                if !invariants.is_empty() {
                    eprintln!("note: invariants are not yet supported, and do nothing")
                }
            }
            _ => return Err(TranslationError::OutOfOrderStatement(statement.clone())),
        }
    }

    let mut inits = Vec::new();
    let mut trs = Vec::new();
    let mut safes = Vec::new();
    for assume in assumes {
        match assume {
            Term::UnaryOp(UOp::Always, tr_or_axiom) => {
                // for axioms, also restrict inits
                match crate::term::FirstOrder::unrolling(&tr_or_axiom) {
                    Some(0) => {
                        inits.push(*tr_or_axiom.clone());
                        trs.push(*tr_or_axiom)
                    }
                    Some(1) => trs.push(*tr_or_axiom),
                    _ => return Err(TranslationError::TooFuture(*tr_or_axiom)),
                }
            }
            init => inits.push(init),
        }
    }
    for assert in asserts {
        match assert {
            Term::UnaryOp(UOp::Always, safe) => safes.push(*safe),
            assert => return Err(TranslationError::AssertWithoutAlways(assert)),
        }
    }

    let normalize = |term| {
        // change uses of nullary relations from Term::Id(name) to Term::App(name, 0, vec![])
        // because expand_quantifiers doesn't know about what names correspond to relations
        // and only cares about Apps with 0 vs. 1 prime
        let term = nullary_id_to_app(term, &module.signature.relations);
        // push primes inwards
        let term = crate::term::Next::new(&module.signature).normalize(&term);
        // convert Forall to And and Exists to Or, eagerly evaluating when possible
        let term = expand_quantifiers(&term, universe, &HashMap::default())?;
        // simplify Ands and Ors into DNF
        Ok(distribute_conjunction(term))
    };

    let inits = normalize(Term::NAryOp(NOp::And, inits))?;
    let trs = normalize(Term::NAryOp(NOp::And, trs))?;
    let safes = normalize(Term::NAryOp(NOp::And, safes))?;

    let get_guards_from_dnf = |valued: Valued| {
        valued
            .get_or()
            .into_iter()
            .map(|term| {
                term.get_and()
                    .into_iter()
                    .map(|term| term.get_guard(&indices))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()
    };

    // inits should just be guards at this point
    let inits: Vec<Vec<Guard>> = get_guards_from_dnf(inits)?;

    // change inits from guards over the state space to states
    let inits: Vec<State> = inits
        .into_iter()
        .flat_map(|conjunction| {
            // compute all the constrained elements by adding them to a single state
            let mut init = State(BitArray::ZERO);
            let mut constrained = btreeset![];
            for guard in &conjunction {
                init.0.set(guard.index, guard.value);
                constrained.insert(guard.index);
            }

            let unconstrained = module
                .signature
                .relations
                .iter()
                .flat_map(|relation| {
                    if relation.args.is_empty() {
                        btreeset![(relation.name.as_str(), (element![]))]
                    } else {
                        relation
                            .args
                            .iter()
                            .map(|sort| cardinality(universe, sort))
                            .map(|card| (0..card).collect::<Vec<usize>>())
                            .multi_cartesian_product()
                            .map(|element| (relation.name.as_str(), Element::new(element)))
                            .collect()
                    }
                })
                .filter(|(set, element)| !constrained.contains(&indices[&(*set, *element)]));

            // compute all the unconstrained elements by doubling the number of states each time
            let mut inits: BTreeSet<State> = btreeset![init];
            for (set, element) in unconstrained {
                inits = inits
                    .into_iter()
                    .flat_map(|state| {
                        let mut with_unconstrained = state.clone();
                        with_unconstrained.0.set(indices[&(set, element)], true);
                        btreeset![state, with_unconstrained]
                    })
                    .collect();
            }
            inits
        })
        .collect();

    let trs = trs
        .get_or()
        .into_iter()
        .map(|term| {
            // build transitions from constrained elements
            let mut tr = Transition::new(vec![], vec![]);
            let mut constrained = btreeset![];
            for term in term.get_and() {
                if let Ok(guard) = term.clone().get_guard(&indices) {
                    tr.guards.push(guard);
                } else if let Ok(update) = term.clone().get_update(&indices) {
                    constrained.insert(update.index);
                    tr.updates.push(update);
                } else if let Valued::NoOp(set, element) = term {
                    constrained.insert(indices[&(set.as_str(), element)]);
                } else {
                    return Err(TranslationError::ExpectedGuardOrUpdate(term));
                }
            }
            // check that constrained contains every element of every set
            for relation in &module.signature.relations {
                if relation.mutable {
                    if relation.args.is_empty() {
                        if !constrained.contains(&indices[&(relation.name.as_str(), (element![]))])
                        {
                            return Err(TranslationError::UnconstrainedTransition(
                                relation.name.clone(),
                            ));
                        }
                    } else {
                        for elements in relation
                            .args
                            .iter()
                            .map(|sort| cardinality(universe, sort))
                            .map(|card| (0..card).collect::<Vec<usize>>())
                            .multi_cartesian_product()
                        {
                            if !constrained.contains(
                                &indices[&(relation.name.as_str(), Element::new(elements))],
                            ) {
                                return Err(TranslationError::UnconstrainedTransition(
                                    relation.name.clone(),
                                ));
                            }
                        }
                    }
                }
            }
            Ok(tr)
        })
        .collect::<Result<Vec<Transition>, _>>()?;

    // disjunction of conjunction of guards
    let safes: Vec<Vec<Guard>> = get_guards_from_dnf(safes)?;

    for tr in &trs {
        let mut indices_to_sets: Vec<&str> = Vec::with_capacity(indices.len());
        indices_to_sets.resize(indices.len(), ""); // cap vs len
        for ((r, _), i) in &indices.0 {
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
                return Err(TranslationError::UpdateViolatedImmutability(
                    indices_to_sets[update.index].to_string(),
                ));
            }
        }
        // check that all of the transitions can be run
        for a in &tr.guards {
            if tr.guards.iter().any(|b| {
                matches!((a, b), (
                    Guard { index: a, value: false },
                    Guard { index: b, value: true },
                )
                | (
                    Guard { index: a, value: true, },
                    Guard { index: b, value: false, },
                ) if a == b)
            }) {
                panic!("found an untakeable transition\n{:?}", tr);
            }
        }
        // check that all redundant updates have been removed
        for a in &tr.guards {
            if tr.updates.contains(&Update {
                index: a.index,
                value: a.value,
            }) {
                panic!("found an unremoved redundant update")
            }
        }
    }

    Ok(Program { inits, trs, safes })
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

fn cardinality(universe: &Universe, sort: &Sort) -> usize {
    match sort {
        Sort::Bool => 2,
        Sort::Id(sort) => *universe.get(sort).unwrap(),
    }
}

/// A simplified syntax::Term that disallows quantifiers and also supports Values.
/// It structurally enforces negation normal form, and has logical semantics.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Valued {
    // logic
    /// An element of some sort
    Value(usize),
    /// A conjunction of terms
    And(BTreeSet<Valued>),
    /// A disjunction of terms
    Or(BTreeSet<Valued>),

    // guards
    /// An inclusion test
    Includes(String, Element), // r(x)
    /// An exclusion test
    Excludes(String, Element), // !r(x)

    // updates
    /// An insertion
    Insert(String, Element), // r'(x)
    /// A removal
    Remove(String, Element), // !r'(x)
    /// A no-op (used for verifying that the module constrains all elements)
    NoOp(String, Element), // r'(x) = r(x)
                           // r'(x) != r(x) could exist but isn't supported
}

impl Valued {
    fn get_value(&self) -> Result<usize, TranslationError> {
        match self {
            Valued::Value(v) => Ok(*v),
            _ => Err(TranslationError::NoValue(self.clone())),
        }
    }

    fn get_and(self) -> BTreeSet<Valued> {
        match self {
            Valued::And(terms) => terms,
            _ => btreeset![self],
        }
    }

    fn get_or(self) -> BTreeSet<Valued> {
        match self {
            Valued::Or(terms) => terms,
            _ => btreeset![self],
        }
    }

    fn get_guard(self, indices: &Indices) -> Result<Guard, TranslationError> {
        match self {
            Valued::Includes(set, element) => Ok(Guard {
                index: indices[&(set.as_str(), element)],
                value: true,
            }),
            Valued::Excludes(set, element) => Ok(Guard {
                index: indices[&(set.as_str(), element)],
                value: false,
            }),
            _ => Err(TranslationError::ExpectedGuard(self)),
        }
    }

    fn get_update(self, indices: &Indices) -> Result<Update, TranslationError> {
        match self {
            Valued::Insert(set, element) => Ok(Update {
                index: indices[&(set.as_str(), element)],
                value: true,
            }),
            Valued::Remove(set, element) => Ok(Update {
                index: indices[&(set.as_str(), element)],
                value: false,
            }),
            _ => Err(TranslationError::ExpectedUpdate(self)),
        }
    }

    fn contradicts(&self, other: &Valued) -> bool {
        matches!((self, other),
            (Valued::Includes(a, b), Valued::Excludes(c, d))
            | (Valued::Excludes(a, b), Valued::Includes(c, d))
            | (Valued::Insert(a, b), Valued::Remove(c, d))
            | (Valued::Insert(a, b), Valued::NoOp(c, d))
            | (Valued::Remove(a, b), Valued::Insert(c, d))
            | (Valued::Remove(a, b), Valued::NoOp(c, d))
            | (Valued::NoOp(a, b), Valued::Insert(c, d))
            | (Valued::NoOp(a, b), Valued::Remove(c, d))
                if a == c && b == d
        )
    }
}

fn and(terms: BTreeSet<Valued>) -> Valued {
    // flatten
    let terms: BTreeSet<Valued> = terms
        .into_iter()
        .flat_map(|term| match term {
            Valued::And(terms) => terms,
            Valued::Value(1) => btreeset![], // remove identity
            term => btreeset![term],
        })
        .collect();
    // short circuit if possible
    for a in &terms {
        if *a == Valued::Value(0) || terms.iter().any(|b| a.contradicts(b)) {
            return Valued::Value(0);
        }
    }
    // remove redundant updates
    let old = terms;
    let mut terms = btreeset![];
    for term in &old {
        if let Valued::Insert(set, element) = term.clone() {
            if old.contains(&Valued::Includes(set.clone(), element)) {
                terms.insert(Valued::NoOp(set, element));
                continue;
            }
        } else if let Valued::Remove(set, element) = term.clone() {
            if old.contains(&Valued::Excludes(set.clone(), element)) {
                terms.insert(Valued::NoOp(set, element));
                continue;
            }
        }

        terms.insert(term.clone());
    }
    // check for `(A or B) and (A or C)`
    'outer: loop {
        let old = terms.clone();
        for a in &old {
            if let Valued::Or(xs) = a {
                for b in &old {
                    if a != b {
                        if let Valued::Or(ys) = b {
                            for x in xs {
                                if ys.contains(x) {
                                    let mut xs = xs.clone();
                                    let mut ys = ys.clone();
                                    xs.remove(x);
                                    ys.remove(x);

                                    let c = and(btreeset![or(xs), or(ys)]);
                                    let mut zs = distribute_conjunction(c).get_or();
                                    zs.insert(x.clone());

                                    terms.remove(a);
                                    terms.remove(b);
                                    terms.insert(or(zs));
                                    continue 'outer;
                                }
                            }
                        }
                    }
                }
            }
        }
        break;
    }
    // true and true = true
    if terms.is_empty() {
        Valued::Value(1)
    } else if terms.len() == 1 {
        terms.pop_last().unwrap()
    } else {
        Valued::And(terms)
    }
}

fn or(terms: BTreeSet<Valued>) -> Valued {
    // flatten
    let mut terms: BTreeSet<Valued> = terms
        .into_iter()
        .flat_map(|term| match term {
            Valued::Or(terms) => terms,
            Valued::Value(0) => btreeset![], // remove identity
            term => btreeset![term],
        })
        .collect();
    // short circuit if possible
    for a in &terms {
        if *a == Valued::Value(1) || terms.iter().any(|b| a.contradicts(b)) {
            return Valued::Value(1);
        }
    }
    // check for `(A and B) or (A and B and C)` and remove the superset
    let old = terms.clone();
    for a in &old {
        if let Valued::And(xs) = a {
            for b in &old {
                if a != b && (xs.contains(b) || matches!(b, Valued::And(ys) if xs.is_superset(ys)))
                {
                    terms.remove(a);
                    break;
                }
            }
        }
    }
    // check for `(A and B) or (A and (not B))`
    'outer: loop {
        let old = terms.clone();
        for a in &old {
            if let Valued::And(xs) = a {
                for b in &old {
                    if a != b {
                        if let Valued::And(ys) = b {
                            if xs.len() == ys.len() {
                                let mut unique = xs.symmetric_difference(ys);
                                let p = unique.next().unwrap();
                                let q = unique.next().unwrap();
                                if unique.next().is_none() && p.contradicts(q) {
                                    let zs = xs.intersection(ys).cloned().collect();
                                    terms.remove(a);
                                    terms.remove(b);
                                    terms.insert(and(zs));
                                    continue 'outer;
                                }
                            }
                        }
                    }
                }
            }
        }
        break;
    }
    // false or false = false
    if terms.is_empty() {
        Valued::Value(0)
    } else if terms.len() == 1 {
        terms.pop_last().unwrap()
    } else {
        Valued::Or(terms)
    }
}

fn not(term: Valued) -> Result<Valued, TranslationError> {
    match term {
        Valued::Value(v) => Ok(Valued::Value(1 - v)),
        Valued::And(terms) => Ok(or(terms.into_iter().map(not).collect::<Result<_, _>>()?)),
        Valued::Or(terms) => Ok(and(terms.into_iter().map(not).collect::<Result<_, _>>()?)),
        Valued::Includes(set, element) => Ok(Valued::Excludes(set, element)),
        Valued::Excludes(set, element) => Ok(Valued::Includes(set, element)),
        // this makes sense because Valued has logical semantics
        Valued::Insert(set, element) => Ok(Valued::Remove(set, element)),
        Valued::Remove(set, element) => Ok(Valued::Insert(set, element)),
        Valued::NoOp(_, _) => Err(TranslationError::NegatedNoOp(term)),
    }
}

fn expand_quantifiers(
    term: &Term,
    universe: &Universe,
    context: &HashMap<String, usize>,
) -> Result<Valued, TranslationError> {
    match term {
        Term::Literal(true) => Ok(Valued::Value(1)),
        Term::Literal(false) => Ok(Valued::Value(0)),
        Term::Id(id) => match context.get(id) {
            Some(v) => Ok(Valued::Value(*v)),
            None => Err(TranslationError::UnknownId(id.clone())),
        },
        Term::App(name, 0, args) => Ok(Valued::Includes(
            name.clone(),
            Element::new(
                args.iter()
                    .map(|arg| expand_quantifiers(arg, universe, context)?.get_value())
                    .collect::<Result<Vec<_>, _>>()?,
            ),
        )),
        Term::App(name, 1, args) => Ok(Valued::Insert(
            name.clone(),
            Element::new(
                args.iter()
                    .map(|arg| expand_quantifiers(arg, universe, context)?.get_value())
                    .collect::<Result<Vec<_>, _>>()?,
            ),
        )),
        Term::UnaryOp(UOp::Not, term) => Ok(not(expand_quantifiers(term, universe, context)?)?),
        Term::BinOp(BinOp::Iff, a, b) => {
            let a = expand_quantifiers(a, universe, context)?;
            let b = expand_quantifiers(b, universe, context)?;
            Ok(or(btreeset![
                and(btreeset![a.clone(), b.clone()]),
                and(btreeset![not(a)?, not(b)?])
            ]))
        }
        Term::BinOp(BinOp::Equals, a, b) => {
            let a = expand_quantifiers(a, universe, context)?;
            let b = expand_quantifiers(b, universe, context)?;
            if let Valued::Insert(insert_set, insert_element) = &a {
                let b = match b {
                    Valued::And(terms) if terms.len() == 1 => terms.into_iter().next().unwrap(),
                    Valued::Or(terms) if terms.len() == 1 => terms.into_iter().next().unwrap(),
                    b => b,
                };
                match b {
                    Valued::Value(1) => Ok(a),
                    Valued::Value(0) => Ok(not(a)?),
                    Valued::Includes(includes_set, includes_element)
                        if includes_set == *insert_set && includes_element == *insert_element =>
                    {
                        Ok(Valued::NoOp(includes_set, includes_element))
                    }
                    _ => Err(TranslationError::UnsupportedTerm(
                        term.clone(),
                        context.clone(),
                    )),
                }
            } else if let (Valued::Value(a), Valued::Value(b)) = (&a, &b) {
                Ok(Valued::Value(if a == b { 1 } else { 0 }))
            } else {
                Err(TranslationError::UnsupportedTerm(
                    term.clone(),
                    context.clone(),
                ))
            }
        }
        Term::BinOp(BinOp::NotEquals, a, b) => Ok(not(expand_quantifiers(
            &Term::BinOp(BinOp::Equals, a.clone(), b.clone()),
            universe,
            context,
        )?)?),
        Term::BinOp(BinOp::Implies, a, b) => Ok(or(btreeset![
            not(expand_quantifiers(a, universe, context)?)?,
            expand_quantifiers(b, universe, context)?
        ])),
        Term::NAryOp(NOp::And, terms) => Ok(and(terms
            .iter()
            .map(|arg| expand_quantifiers(arg, universe, context))
            .collect::<Result<_, _>>()?)),
        Term::NAryOp(NOp::Or, terms) => Ok(or(terms
            .iter()
            .map(|arg| expand_quantifiers(arg, universe, context))
            .collect::<Result<_, _>>()?)),
        Term::Ite { cond, then, else_ } => Ok(or(btreeset![
            and(btreeset![
                expand_quantifiers(cond, universe, context)?,
                expand_quantifiers(then, universe, context)?
            ]),
            and(btreeset![
                not(expand_quantifiers(cond, universe, context)?)?,
                expand_quantifiers(else_, universe, context)?
            ])
        ])),
        Term::Quantified {
            quantifier,
            binders,
            body,
        } => {
            // adapted from semantics.rs
            assert!(!binders.is_empty());
            let shape: Vec<usize> = binders
                .iter()
                .map(|b| cardinality(universe, &b.sort))
                .collect();
            let names: Vec<&String> = binders.iter().map(|b| &b.name).collect();
            // evaluate on all combinations of values for quantified sorts
            let set = shape
                .iter()
                .map(|&card| (0..card).collect::<Vec<usize>>())
                .multi_cartesian_product()
                .map(|elements| {
                    // extend context with all variables bound to these `elements`
                    let mut context = context.clone();
                    for (name, element) in zip(&names, elements) {
                        context.insert(name.to_string(), element);
                    }
                    expand_quantifiers(body, universe, &context)
                })
                .collect::<Result<BTreeSet<_>, _>>()?;
            match quantifier {
                Quantifier::Forall => Ok(and(set)),
                Quantifier::Exists => Ok(or(set)),
            }
        }
        _ => Err(TranslationError::UnsupportedTerm(
            term.clone(),
            context.clone(),
        )),
    }
}

// this actually ends up converting to DNF in context
// steps from en.wikipedia.org/wiki/Conjunctive_normal_form
// 1. Convert to negation normal form
//    - the not() constructor does this internally
// 2. Standardize variables
//    - expand_quantifiers() deals with this
// 3. Skolemize the statement
//    - expand_quantifiers() deals with this
// 4. Drop all universal quantifiers
//    - expand_quantifiers() deals with this
// 5. Distribute ORs inwards over ANDs
//    - what this function does
fn distribute_conjunction(term: Valued) -> Valued {
    match term {
        Valued::And(terms) => {
            // A and (B or C or D) and (E or F) =
            // (A and B and E) or (A and C and E) or (A and D and E) or
            // (A and B and F) or (A and C and F) or (A and D and F)
            // so we actually just want multi_cartesian_product, great
            // we have to convert to and from Vec for multi_cartesian_product
            or(terms
                .into_iter()
                .map(distribute_conjunction)
                .map(|term| term.get_or().into_iter().collect::<Vec<_>>())
                .multi_cartesian_product()
                .map(|vec| and(vec.into_iter().collect::<BTreeSet<_>>()))
                .collect())
        }
        Valued::Or(terms) => {
            // or() internally flattens nested Ors
            or(terms.into_iter().map(distribute_conjunction).collect())
        }
        _ => term,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn includes(set: &str, element: Element, indices: &Indices) -> Guard {
        Guard {
            index: indices[&(set, element)],
            value: true,
        }
    }
    fn excludes(set: &str, element: Element, indices: &Indices) -> Guard {
        Guard {
            index: indices[&(set, element)],
            value: false,
        }
    }
    fn insert(set: &str, element: Element, indices: &Indices) -> Update {
        Update {
            index: indices[&(set, element)],
            value: true,
        }
    }
    fn remove(set: &str, element: Element, indices: &Indices) -> Update {
        Update {
            index: indices[&(set, element)],
            value: false,
        }
    }
    fn state(iter: impl IntoIterator<Item = u8>) -> State {
        let mut out = State(BitArray::ZERO);
        for (i, x) in iter.into_iter().enumerate() {
            out.0.set(i, x == 1);
        }
        out
    }

    #[test]
    fn interpreter_basic() {
        let program = Program {
            inits: vec![state([0])],
            trs: vec![
                Transition::new(vec![], vec![]),
                Transition::new(
                    vec![],
                    vec![Update {
                        index: 0,
                        value: true,
                    }],
                ),
            ],
            safes: vec![vec![Guard {
                index: 0,
                value: false,
            }]],
        };
        let result0 = interpret(&program, 0, false);
        let result1 = interpret(&program, 1, false);
        assert_eq!(result0, InterpreterResult::Unknown);
        let mut expected1 = Trace::new(state([0]), false);
        expected1.push(state([1]));
        assert_eq!(result1, InterpreterResult::Counterexample(expected1));
    }

    #[test]
    fn interpreter_cycle() {
        let program = Program {
            inits: vec![state([1, 0, 0, 0])],
            trs: vec![
                Transition::new(
                    vec![Guard {
                        index: 0,
                        value: true,
                    }],
                    vec![
                        Update {
                            index: 0,
                            value: false,
                        },
                        Update {
                            index: 1,
                            value: true,
                        },
                    ],
                ),
                Transition::new(
                    vec![Guard {
                        index: 1,
                        value: true,
                    }],
                    vec![
                        Update {
                            index: 1,
                            value: false,
                        },
                        Update {
                            index: 2,
                            value: true,
                        },
                    ],
                ),
                Transition::new(
                    vec![Guard {
                        index: 2,
                        value: true,
                    }],
                    vec![
                        Update {
                            index: 2,
                            value: false,
                        },
                        Update {
                            index: 3,
                            value: true,
                        },
                    ],
                ),
                Transition::new(
                    vec![Guard {
                        index: 3,
                        value: true,
                    }],
                    vec![
                        Update {
                            index: 3,
                            value: false,
                        },
                        Update {
                            index: 0,
                            value: true,
                        },
                    ],
                ),
            ],
            safes: vec![vec![Guard {
                index: 3,
                value: false,
            }]],
        };
        let result1 = interpret(&program, 0, false);
        let result2 = interpret(&program, 1, false);
        let result3 = interpret(&program, 2, false);
        let result4 = interpret(&program, 3, false);
        let result5 = interpret(&program, 4, false);
        assert_eq!(result1, InterpreterResult::Unknown);
        assert_eq!(result2, InterpreterResult::Unknown);
        assert_eq!(result3, InterpreterResult::Unknown);
        let mut expected4 = Trace::new(state([1, 0, 0, 0]), false);
        for state in vec![
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
    fn interpreter_translate_lockserver() -> Result<(), TranslationError> {
        let source = "
sort node

mutable lock_msg(node): bool
mutable grant_msg(node): bool
mutable unlock_msg(node): bool
mutable holds_lock(node): bool
mutable server_holds_lock: bool

# inits:
assume (forall N:node. !lock_msg(N)) & (forall N:node. !grant_msg(N)) & (forall N:node.
    !unlock_msg(N)) & (forall N:node. !holds_lock(N)) & (server_holds_lock)

# transitions:
assume always
    (exists n:node. 
        (forall N:node. ((lock_msg(N))') <-> lock_msg(N) | N = n) & 
        (forall x0:node. ((grant_msg(x0))') = grant_msg(x0)) & 
        (forall x0:node. ((unlock_msg(x0))') = unlock_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0)) & 
        ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. server_holds_lock & lock_msg(n) & 
            !((server_holds_lock)') & 
            (((lock_msg(N))') <-> lock_msg(N) & N != n) & 
            (((grant_msg(N))') <-> grant_msg(N) | N = n)) & 
        (forall x0:node. ((unlock_msg(x0))') = unlock_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0))) | 
    (exists n:node. 
        (forall N:node. grant_msg(n) & 
            (((grant_msg(N))') <-> grant_msg(N) & N != n) & 
            (((holds_lock(N))') <-> holds_lock(N) | N = n)) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) & 
        (forall x0:node. 
            ((unlock_msg(x0))') = unlock_msg(x0)) & 
            ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. holds_lock(n) & 
            (((holds_lock(N))') <-> holds_lock(N) & N != n) & 
            (((unlock_msg(N))') <-> unlock_msg(N) | N = n)) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) &
        (forall x0:node. 
            ((grant_msg(x0))') = grant_msg(x0)) & 
            ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. unlock_msg(n) & 
            (((unlock_msg(N))') <-> unlock_msg(N) & N != n) & 
            ((server_holds_lock)')) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) & 
        (forall x0:node. ((grant_msg(x0))') = grant_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0)))

# safety:
assert always (forall N1:node, N2:node. holds_lock(N1) & holds_lock(N2) -> N1 = N2)
        ";

        let mut m = crate::fly::parse(source).unwrap();
        let universe = std::collections::HashMap::from([("node".to_string(), 2)]);
        let indices = Indices::new(&m.signature, &universe);

        let mut trs = vec![];
        // (forall N:node. ((lock_msg(N))') <-> lock_msg(N) | N = n)
        trs.extend(vec![
            Transition::new(vec![], vec![insert("lock_msg", element![0], &indices)]),
            Transition::new(vec![], vec![insert("lock_msg", element![1], &indices)]),
        ]);
        // (forall N:node. server_holds_lock & lock_msg(n) &
        //     !((server_holds_lock)') &
        //     (((lock_msg(N))') <-> lock_msg(N) & N != n) &
        //     (((grant_msg(N))') <-> grant_msg(N) | N = n)) &
        trs.extend(vec![
            Transition::new(
                vec![
                    includes("lock_msg", element![1], &indices),
                    includes("server_holds_lock", element![], &indices),
                ],
                vec![
                    insert("grant_msg", element![1], &indices),
                    remove("lock_msg", element![1], &indices),
                    remove("server_holds_lock", element![], &indices),
                ],
            ),
            Transition::new(
                vec![
                    includes("lock_msg", element![0], &indices),
                    includes("server_holds_lock", element![], &indices),
                ],
                vec![
                    insert("grant_msg", element![0], &indices),
                    remove("lock_msg", element![0], &indices),
                    remove("server_holds_lock", element![], &indices),
                ],
            ),
        ]);
        // (forall N:node. grant_msg(n) &
        //     (((grant_msg(N))') <-> grant_msg(N) & N != n) &
        //     (((holds_lock(N))') <-> holds_lock(N) | N = n)) &
        trs.extend(vec![
            Transition::new(
                vec![includes("grant_msg", element![0], &indices)],
                vec![
                    insert("holds_lock", element![0], &indices),
                    remove("grant_msg", element![0], &indices),
                ],
            ),
            Transition::new(
                vec![includes("grant_msg", element![1], &indices)],
                vec![
                    insert("holds_lock", element![1], &indices),
                    remove("grant_msg", element![1], &indices),
                ],
            ),
        ]);
        // (forall N:node. holds_lock(n) &
        //     (((holds_lock(N))') <-> holds_lock(N) & N != n) &
        //     (((unlock_msg(N))') <-> unlock_msg(N) | N = n)) &
        trs.extend(vec![
            Transition::new(
                vec![includes("holds_lock", element![0], &indices)],
                vec![
                    insert("unlock_msg", element![0], &indices),
                    remove("holds_lock", element![0], &indices),
                ],
            ),
            Transition::new(
                vec![includes("holds_lock", element![1], &indices)],
                vec![
                    insert("unlock_msg", element![1], &indices),
                    remove("holds_lock", element![1], &indices),
                ],
            ),
        ]);
        // (forall N:node. unlock_msg(n) &
        //     (((unlock_msg(N))') <-> unlock_msg(N) & N != n) &
        //     ((server_holds_lock)'))
        trs.extend(vec![
            Transition::new(
                vec![includes("unlock_msg", element![0], &indices)],
                vec![
                    insert("server_holds_lock", element![], &indices),
                    remove("unlock_msg", element![0], &indices),
                ],
            ),
            Transition::new(
                vec![includes("unlock_msg", element![1], &indices)],
                vec![
                    insert("server_holds_lock", element![], &indices),
                    remove("unlock_msg", element![1], &indices),
                ],
            ),
        ]);

        let expected = Program {
            inits: vec![state([0, 0, 0, 0, 0, 0, 0, 0, 1])],
            trs,
            safes: vec![
                vec![excludes("holds_lock", element![0], &indices)],
                vec![excludes("holds_lock", element![1], &indices)],
            ],
        };

        let target = translate(&mut m, &universe)?;
        assert_eq!(target.inits, expected.inits);
        assert_eq!(target.safes, expected.safes);
        assert_eq!(
            target.trs.iter().collect::<BTreeSet<_>>(),
            expected.trs.iter().collect::<BTreeSet<_>>()
        );

        let output = interpret(&target, 100, false);
        assert_eq!(output, InterpreterResult::Unknown);

        Ok(())
    }

    #[test]
    fn interpreter_translate_lockserver_buggy() -> Result<(), TranslationError> {
        let source = "
sort node

mutable lock_msg(node): bool
mutable grant_msg(node): bool
mutable unlock_msg(node): bool
mutable holds_lock(node): bool
mutable server_holds_lock: bool

# inits:
assume (forall N:node. !lock_msg(N)) & (forall N:node. !grant_msg(N)) & (forall N:node.
    !unlock_msg(N)) & (forall N:node. !holds_lock(N)) & (server_holds_lock)

# transitions:
assume always
    (exists n:node. 
        (forall N:node. ((lock_msg(N))') <-> lock_msg(N) | N = n) & 
        (forall x0:node. ((grant_msg(x0))') = grant_msg(x0)) & 
        (forall x0:node. ((unlock_msg(x0))') = unlock_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0)) & 
        ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. server_holds_lock & lock_msg(n) & 
            !((server_holds_lock)') & 
            (((lock_msg(N))') <-> lock_msg(N) & N != n) & 
            (((grant_msg(N))') <-> grant_msg(N) | N = n)) & 
        (forall x0:node. ((unlock_msg(x0))') = unlock_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0))) | 
    (exists n:node. 
        (forall N:node. grant_msg(n) & 
            (((grant_msg(N))') <-> grant_msg(N) & N != n) & 
            (((holds_lock(N))') <-> holds_lock(N) | N = n)) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) & 
        (forall x0:node. 
            ((unlock_msg(x0))') = unlock_msg(x0)) & 
            ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. holds_lock(n) & 
            (((holds_lock(N))') <-> holds_lock(N) & N != n) & 
            (((unlock_msg(N))') <-> unlock_msg(N) | N = n)) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) &
        (forall x0:node. 
            ((grant_msg(x0))') = grant_msg(x0)) & 
            ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. unlock_msg(n) & 
            (((unlock_msg(N))') <-> unlock_msg(N)) & 
            ((server_holds_lock)')) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) & 
        (forall x0:node. ((grant_msg(x0))') = grant_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0)))

# safety:
assert always (forall N1:node, N2:node. holds_lock(N1) & holds_lock(N2) -> N1 = N2)
        ";

        let mut m = crate::fly::parse(source).unwrap();
        let universe = std::collections::HashMap::from([("node".to_string(), 2)]);
        let target = translate(&mut m, &universe)?;

        let bug = interpret(&target, 12, false);
        if let InterpreterResult::Counterexample(trace) = &bug {
            println!("{:#?}", trace);
            assert_eq!(trace.len(), 13);
        } else {
            assert!(matches!(bug, InterpreterResult::Counterexample(_)));
        }

        let too_short = interpret(&target, 11, false);
        assert_eq!(too_short, InterpreterResult::Unknown);

        Ok(())
    }

    #[test]
    fn interpreter_translate_consensus() -> Result<(), TranslationError> {
        let source = "
sort node
sort quorum
sort value

# relations:
immutable member(node, quorum): bool
mutable vote_request_msg(node, node): bool
mutable voted(node): bool
mutable vote_msg(node, node): bool
mutable votes(node, node): bool
mutable leader(node): bool
mutable decided(node, value): bool

# init:
assume (forall N1:node, N2:node. !vote_request_msg(N1, N2)) & (forall N:node. !voted(N)) &
    (forall N1:node, N2:node. !vote_msg(N1, N2)) & (forall N1:node, N2:node. !votes(N1, N2)) &
    (forall N1:node. !leader(N1)) & (forall N:node, V:value. !decided(N, V))

# transitions:
assume always (exists src:node, dst:node. (forall N1:node, N2:node. (vote_request_msg(N1, N2))' <->
    vote_request_msg(N1, N2) | N1 = src & N2 = dst) & (forall x0:node. (voted(x0))' = voted(x0)) &
    (forall x0:node, x1:node. (vote_msg(x0, x1))' = vote_msg(x0, x1)) & (forall x0:node, x1:node.
    (votes(x0, x1))' = votes(x0, x1)) & (forall x0:node. (leader(x0))' = leader(x0)) &
    (forall x0:node, x1:value. (decided(x0, x1))' = decided(x0, x1))) | (exists src:node, dst:node.
    (forall N1:node, N2:node, N:node. !voted(src) & vote_request_msg(dst, src) & !vote_request_msg'(dst, src) & 
    ((vote_msg(N1, N2))' <->
    vote_msg(N1, N2) | N1 = src & N2 = dst) & ((voted(N))' <-> voted(N) | N = src) & (!(N1 = dst &
    N2 = src) -> ((vote_request_msg(N1, N2))' <-> vote_request_msg(N1, N2)))) & (forall x0:node, x1:node.
    (votes(x0, x1))' = votes(x0, x1)) & (forall x0:node. (leader(x0))' = leader(x0)) & (forall x0:node,
    x1:value. (decided(x0, x1))' = decided(x0, x1))) | (exists n:node, sender:node. (forall N1:node, N2:node.
    vote_msg(sender, n) & ((votes(N1, N2))' <-> votes(N1, N2) | N1 = n & N2 = sender)) & (forall x0:node,
    x1:node. (vote_request_msg(x0, x1))' = vote_request_msg(x0, x1)) & (forall x0:node. (voted(x0))' = voted(x0))
    & (forall x0:node, x1:node. (vote_msg(x0, x1))' = vote_msg(x0, x1)) & (forall x0:node. (leader(x0))' =
    leader(x0)) & (forall x0:node, x1:value. (decided(x0, x1))' = decided(x0, x1))) | (exists n:node, q:quorum.
    (forall N:node. (member(N, q) -> votes(n, N)) & ((leader(N))' <-> leader(N) | N = n)) & (forall x0:node,
    x1:node. (vote_request_msg(x0, x1))' = vote_request_msg(x0, x1)) & (forall x0:node. (voted(x0))' = voted(x0))
    & (forall x0:node, x1:node. (vote_msg(x0, x1))' = vote_msg(x0, x1)) & (forall x0:node, x1:node.
    (votes(x0, x1))' = votes(x0, x1)) & (forall x0:node, x1:value. (decided(x0, x1))' = decided(x0, x1))) |
    (exists n:node, v:value. (forall V:value, N:node. leader(n) & !decided(n, V) & ((decided(N, V))' <->
    decided(N, V) | N = n & V = v)) & (forall x0:node, x1:node. (vote_request_msg(x0, x1))' =
    vote_request_msg(x0, x1)) & (forall x0:node. (voted(x0))' = voted(x0)) & (forall x0:node, x1:node.
    (vote_msg(x0, x1))' = vote_msg(x0, x1)) & (forall x0:node, x1:node. (votes(x0, x1))' = votes(x0, x1)) &
    (forall x0:node. (leader(x0))' = leader(x0)))

# added by hand
# axiom
assume always (forall Q1:quorum, Q2:quorum. exists N:node. member(N, Q1) & member(N, Q2))

# safety:
assert always (forall N1:node, V1:value, N2:node, V2:value. decided(N1, V1) & decided(N2, V2) -> V1 = V2)
        ";

        let mut m = crate::fly::parse(source).unwrap();
        let universe = std::collections::HashMap::from([
            ("node".to_string(), 2),
            ("value".to_string(), 2),
            ("quorum".to_string(), 1),
        ]);
        let target = translate(&mut m, &universe)?;
        let output = interpret(&target, 1, false);
        assert_eq!(output, InterpreterResult::Unknown);

        Ok(())
    }

    #[test]
    fn interpreter_primes_in_inits() -> Result<(), TranslationError> {
        let source = "
mutable f: bool

# inits:
assume !f & !f'

# transitions:
assume always (f & f') | (!f & !f')

# safety:
assert always !f
        ";

        let mut m = crate::fly::parse(source).unwrap();
        let universe = std::collections::HashMap::from([("node".to_string(), 2)]);
        let target = translate(&mut m, &universe);
        assert_eq!(
            target,
            Err(TranslationError::ExpectedGuard(Valued::NoOp(
                "f".to_string(),
                element![]
            )))
        );
        Ok(())
    }
}

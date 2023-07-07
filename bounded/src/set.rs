// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A bounded model checker for flyvy programs. Use `translate` to turn a flyvy `Module`
//! into a `BoundedProgram`, then use `interpret` to evaluate it.

use bitvec::prelude::*;
use fly::{sorts::*, syntax::*, term::fo::FirstOrder};
use itertools::Itertools;
use std::collections::{BTreeSet, VecDeque};
use thiserror::Error;

/// The result of a successful run of the bounded model checker
#[derive(Debug, PartialEq)]
pub enum CheckerAnswer {
    /// The checker found a counterexample
    Counterexample,
    /// The checker did not find a counterexample
    Unknown,
}

/// Combined entry point to both translate and search the module.
pub fn check(
    module: &Module,
    universe: &UniverseBounds,
    depth: Option<usize>,
    compress_traces: TraceCompression,
) -> Option<CheckerAnswer> {
    match translate(module, universe) {
        Err(e) => {
            eprintln!("{}", e);
            None
        }
        Ok(program) => match interpret(&program, depth, compress_traces) {
            InterpreterResult::Unknown => {
                println!("no counterexample found");
                Some(CheckerAnswer::Unknown)
            }
            InterpreterResult::Counterexample(trace) => {
                println!("found counterexample!");
                let indices = Indices::new(&module.signature, universe);
                match compress_traces {
                    TraceCompression::Yes => {
                        let (state, depth) = match trace {
                            Trace::Trace(..) => unreachable!(),
                            Trace::CompressedTrace(state, depth) => (state, depth),
                        };
                        println!("final state (depth {}):", depth);
                        for r in &module.signature.relations {
                            let relation = &r.name;
                            print!("{}: {{", relation);
                            for ((r, elements), i) in &indices.0 {
                                if r == relation && state.0[*i] {
                                    print!("{:?}, ", elements);
                                }
                            }
                            println!("}}");
                        }
                        println!();
                    }
                    TraceCompression::No => {
                        let states = match trace {
                            Trace::Trace(states) => states,
                            Trace::CompressedTrace(..) => unreachable!(),
                        };
                        for (i, state) in states.iter().enumerate() {
                            println!("state {}:", i);
                            for r in &module.signature.relations {
                                let relation = &r.name;
                                print!("{}: {{", relation);
                                for ((r, elements), i) in &indices.0 {
                                    if r == relation && state.0[*i] {
                                        print!("{:?}, ", elements);
                                    }
                                }
                                println!("}}");
                            }
                            println!();
                        }
                    }
                }
                Some(CheckerAnswer::Counterexample)
            }
        },
    }
}

// We use FxHashMap and FxHashSet because the hash function performance is about 25% faster
// and the bounded model checker is essentially a hashing microbenchmark :)
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

macro_rules! btreeset {
    ($($v:expr),* $(,)?) => {{
        BTreeSet::from([$($v,)*])
    }};
}

/// Compile-time upper bound on the arity of a relation
const ELEMENT_LEN: usize = 15; // should be 1 less than a multiple of 8 for alignment reasons
const _: () = assert!(ELEMENT_LEN <= u8::MAX as usize); // ELEMENT_LEN must fit in a u8

/// Compile-time upper bound on the bounded universe size. The bounded
const STATE_LEN: usize = 128; // should be a multiple of 64 for alignment reasons

/// A tuple of universe elements, as would be passed as arguments to a relation.
/// Uses a fixed size array to avoid allocating a Vec.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Elements {
    len: u8,
    data: [u8; ELEMENT_LEN],
}
impl Elements {
    /// Creates a new Elements tuple from the given vector.
    /// Each item in the given vector must fit in a u8, or this function will panic.
    pub fn new(vec: Vec<usize>) -> Elements {
        let len = vec.len();
        if len > ELEMENT_LEN {
            panic!("raise ELEMENT_LEN to be at least {}", len);
        }
        let mut out = Elements {
            len: len as u8,
            data: [0; ELEMENT_LEN],
        };
        for (i, x) in vec.into_iter().enumerate() {
            if let Ok(xu8) = x.try_into() {
                out.data[i] = xu8;
            } else {
                panic!(
                    "vec[{}] = {} size was too large (must be less than 256)",
                    i, x
                );
            }
        }
        out
    }
}
impl std::fmt::Debug for Elements {
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
        Elements::new(vec![$($v,)*])
    }};
}

/// A state in the bounded system. Conceptually, this is an interpretation of the signature on the
/// bounded universe. We represent states concretely as a bitvector, where each bit represents the
/// presence of a tuple in a relation. The order of the bits is determined by [Indices].
#[derive(Clone, Debug, Eq, PartialOrd, Ord)]
pub struct BoundedState(BitArr!(for STATE_LEN));

impl std::hash::Hash for BoundedState {
    // Override the hash for bitvec::BitArray to use a slice of words rather than bit-by-bit.
    fn hash<H>(&self, h: &mut H)
    where
        H: std::hash::Hasher,
    {
        usize::hash_slice(self.0.as_raw_slice(), h)
    }
}

impl PartialEq for BoundedState {
    // Override eq for bitvec::BitArray to use a slice of words rather than bit-by-bit.
    fn eq(&self, other: &BoundedState) -> bool {
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

/// A map from (relation name, Elements) pairs to their index in the [BoundedState] bit vector.
struct Indices<'a>(HashMap<(&'a str, Elements), usize>);

impl Indices<'_> {
    /// Compute an index for the given signature and universe bounds
    fn new<'a>(signature: &'a Signature, universe: &UniverseBounds) -> Indices<'a> {
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
                        .map(|element| (relation.name.as_str(), Elements::new(element)))
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

impl<'a> std::ops::Index<&(&'a str, Elements)> for Indices<'a> {
    type Output = usize;
    fn index(&self, key: &(&'a str, Elements)) -> &usize {
        &self.0[key]
    }
}

/// A BoundedProgram is a set of initial states, a set of transitions, and a safety property
#[derive(Clone, Debug, PartialEq)]
pub struct BoundedProgram {
    /// List of initial states
    inits: Vec<BoundedState>,
    /// List of transitions to potentially take at each step. The transition relation is the
    /// disjunction of all these transitions.
    trs: Vec<Transition>,
    /// Safety property to check in each reachable state, expressed in DNF, i.e., the outer Vec is
    /// an "or" of the inner Vecs, and each inner Vec is the "and" of its Guards.
    safes: Vec<Vec<Guard>>,
}

/// A Transition is a deterministic partial function on states expressed as a guarded update.
/// If the (and of the) guard(s) is true, then the transition is enabled and can step to the updated
/// state.
/// If the (and of the) guard(s) is false, then the transition is not enabled.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Transition {
    guards: Vec<Guard>,
    updates: Vec<Update>,
}

impl Transition {
    /// Make a Transition
    pub fn new(guards: Vec<Guard>, updates: Vec<Update>) -> Transition {
        Transition { guards, updates }
    }
}

/// A Guard is a logical literal, i.e., a possibly negated relation applied to an argument tuple
/// such as `r(x, y)` or `!r(x, y)`. The relation and argument tuple are represented by an index
/// into an ambient `Indices` map.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Guard {
    /// The index representing the relation and argument tuple. Indexes into an ambient `Indices`
    /// map.
    index: usize,

    /// True for positive literal, false for negative literal
    value: bool,
}

/// An Update is either an insertion or a removal of a tuple from a relation. The relation and
/// argument tuple are represented by an index into an ambient `Indices` map.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Update {
    /// The index representing the relation and argument tuple. Indexes into an ambient `Indices`
    /// map.
    index: usize,

    /// True for insertion, false for removal
    value: bool,
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
        out.extend(self.data.iter().cloned());
        for (key, child) in &self.children {
            if set.0[key.index] == key.value {
                child.get_subsets_into_vec(set, out);
            }
        }
    }
}

impl<'a> FromIterator<&'a Transition> for Transitions<'a> {
    fn from_iter<I: IntoIterator<Item = &'a Transition>>(iter: I) -> Self {
        let mut ans = Transitions::new();
        for tr in iter {
            ans.insert(tr);
        }
        ans
    }
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
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Trace {
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
pub enum InterpreterResult {
    /// The checker found a counterexample, here it is
    Counterexample(Trace),
    /// The checker could not find any counterexamples
    Unknown,
}

/// Explore reachable states of a BoundedProgram up to (and including) the given max_depth using
/// breadth-first search.
///
/// Note that max_depth refers to the number of transitions, not the number of states,
/// so if max_depth is Some(3), it means there will be 3 transitions (so 4 states).
/// If max_depth is None, it means "no upper bound". The program will run until its
/// state space is exhausted or the process is killed.
#[allow(dead_code)]
pub fn interpret(
    program: &BoundedProgram,
    max_depth: Option<usize>,
    compress_traces: TraceCompression,
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

    let transitions: Transitions = program.trs.iter().collect();

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
            println!(
                "({:?} since start) considering new depth: {}. \
                 queue length is {}. seen {} unique states.",
                start_time.elapsed(),
                current_depth,
                queue.len(),
                seen.len()
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

        if max_depth.map(|md| depth < md).unwrap_or(true) {
            let trs = transitions.get_subsets(state);

            for tr in trs {
                let mut next = state.clone();
                tr.updates
                    .iter()
                    .for_each(|update| next.0.set(update.index, update.value));
                if !seen.contains(&next) {
                    seen.insert(next.clone());
                    if seen.len() % 1_000_000 == 0 {
                        println!(
                            "progress report: ({:?} since start) considering depth {}. \
                             queue length is {}. visited {} states.",
                            start_time.elapsed(),
                            current_depth,
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

    InterpreterResult::Unknown
}

#[allow(missing_docs)]
#[derive(Error, Debug, PartialEq)]
pub enum TranslationError {
    #[error("sort checking error: {0}")]
    SortError(SortError),
    #[error("sort {0} not found in universe {1:#?}")]
    UnknownSort(String, UniverseBounds),
    #[error("all assumes should precede all asserts, but found {0:?}")]
    OutOfOrderStatement(ThmStmt),
    #[error("expected no primes in {0}")]
    AnyFuture(Term),
    #[error("expected no primes or only one prime in {0}")]
    TooFuture(Term),
    #[error("found an assert that isn't a safety property")]
    AssertWithoutAlways(Term),
    #[error("unknown identifier {0}")]
    UnknownId(String),
    #[error("could not translate to propositional logic {0}")]
    CouldNotTranslateToAst(Term),
    #[error("could not translate to element {0}")]
    CouldNotTranslateToElement(Term),
    #[error("we don't support negating no-ops, but found {0:?}")]
    NegatedNoOp(Ast),
    #[error("expected guard, found: {0:#?}")]
    ExpectedGuard(Ast),
    #[error("expected update, found: {0:#?}")]
    ExpectedUpdate(Ast),
    #[error("expected guard or update, found: {0:#?}")]
    ExpectedGuardOrUpdate(Ast),
    #[error("one of the generated updates updated the immutable relation {0}")]
    UpdateViolatedImmutability(String),
}

/// Map from uninterpreted sort names to sizes
// Here is the one place we use a std HashMap. It's not a performance problem because it's not used
// in the inner loop of the model checker, and it provides a more ergonomic public api to this module.
type UniverseBounds = std::collections::HashMap<String, usize>;

/// Translate a flyvy module into a BoundedProgram, given the bounds on the sort sizes.
/// Universe should contain the sizes of all the sorts in module.signature.sorts.
/// The module is assumed to have already been typechecked.
pub fn translate(
    module: &Module,
    universe: &UniverseBounds,
) -> Result<BoundedProgram, TranslationError> {
    for relation in &module.signature.relations {
        if relation.sort != Sort::Bool {
            todo!("non-bool relations")
        }
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
    for assume in assumes {
        match assume {
            Term::UnaryOp(UOp::Always, axiom) if FirstOrder::unrolling(&axiom) == Some(0) => {
                inits.push(*axiom.clone());
                trs.push(*axiom);
            }
            Term::UnaryOp(UOp::Always, tr) if FirstOrder::unrolling(&tr) == Some(1) => {
                trs.push(*tr)
            }
            Term::UnaryOp(UOp::Always, term) => return Err(TranslationError::TooFuture(*term)),
            init if FirstOrder::unrolling(&init) == Some(0) => inits.push(init),
            init => return Err(TranslationError::AnyFuture(init)),
        }
    }

    let mut safes = Vec::new();
    for assert in asserts {
        match assert {
            Term::UnaryOp(UOp::Always, safe) if FirstOrder::unrolling(&safe) == Some(0) => {
                safes.push(*safe)
            }
            Term::UnaryOp(UOp::Always, safe) => return Err(TranslationError::AnyFuture(*safe)),
            assert => return Err(TranslationError::AssertWithoutAlways(assert)),
        }
    }

    let normalize = |term: Term| -> Result<Ast, TranslationError> {
        // change uses of nullary relations from Term::Id(name) to Term::App(name, 0, vec![])
        // because expand_quantifiers doesn't know about what names correspond to relations
        // and only cares about Apps with 0 vs. 1 prime
        let term = nullary_id_to_app(term, &module.signature.relations);
        // push primes inwards
        let term = fly::term::prime::Next::new(&module.signature).normalize(&term);
        // convert Forall to And and Exists to Or, eagerly evaluating when possible
        let term = term_to_ast(&term, universe, &HashMap::default())?;
        // simplify Ands and Ors into DNF
        Ok(distribute_conjunction(term))
    };

    let inits = normalize(Term::NAryOp(NOp::And, inits))?;
    let trs = normalize(Term::NAryOp(NOp::And, trs))?;
    let safes = normalize(Term::NAryOp(NOp::And, safes))?;

    let get_guards_from_dnf = |valued: Ast| -> Result<Vec<Vec<Guard>>, TranslationError> {
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
    let inits: Vec<BoundedState> = inits
        .into_iter()
        .flat_map(|conjunction| {
            // compute all the constrained elements by adding them to a single state
            let mut init = BoundedState(BitArray::ZERO);
            let mut constrained = btreeset![];
            for guard in &conjunction {
                init.0.set(guard.index, guard.value);
                constrained.insert(guard.index);
            }

            // compute all the unconstrained elements by doubling the number of states each time
            let mut inits = vec![init];
            for index in 0..indices.len() {
                if !constrained.contains(&index) {
                    inits = inits
                        .into_iter()
                        .flat_map(|state| {
                            let mut with_unconstrained = state.clone();
                            with_unconstrained.0.set(index, true);
                            vec![state, with_unconstrained]
                        })
                        .collect();
                }
            }
            inits
        })
        .collect();

    let mut unconstrained_delta = 0;
    let trs: Vec<Transition> = trs
        .get_or()
        .into_iter()
        .map(|term: Ast| {
            // build transitions from constrained elements
            let mut tr = Transition::new(vec![], vec![]);
            let mut constrained = btreeset![];
            for term in term.get_and() {
                if let Ok(guard) = term.clone().get_guard(&indices) {
                    tr.guards.push(guard);
                } else if let Ok(update) = term.clone().get_update(&indices) {
                    constrained.insert(update.index);
                    tr.updates.push(update);
                } else if let Ast::NoOp(set, element) = term {
                    constrained.insert(indices[&(set.as_str(), element)]);
                } else {
                    return Err(TranslationError::ExpectedGuardOrUpdate(term));
                }
            }

            // compute all the unconstrained future elements by doubling
            let mut trs = vec![tr];
            for index in 0..indices.len() {
                if !constrained.contains(&index) {
                    let ((relation, _), _) = indices.0.iter().find(|(_, i)| **i == index).unwrap();
                    let mut relations = module.signature.relations.iter();
                    if relations.find(|r| &r.name == relation).unwrap().mutable {
                        trs = trs
                            .into_iter()
                            .flat_map(|tr| {
                                let mut a = tr.clone();
                                let mut b = tr;
                                let matches = |g: &Guard, value| *g == Guard { index, value };
                                if !a.guards.iter().any(|g| matches(g, true)) {
                                    a.updates.push(Update { index, value: true });
                                }
                                if !b.guards.iter().any(|g| matches(g, false)) {
                                    b.updates.push(Update {
                                        index,
                                        value: false,
                                    });
                                }
                                vec![a, b]
                            })
                            .collect();
                    }
                }
            }
            unconstrained_delta += trs.len() - 1;
            Ok(trs)
        })
        .collect::<Result<Vec<Vec<Transition>>, _>>()?
        .into_iter()
        .flatten()
        .collect();

    if unconstrained_delta > 0 {
        println!(
            "some relations were unconstrained, added {} transitions to constrain them",
            unconstrained_delta
        );
    }

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
        for &Guard { index, value } in &tr.guards {
            if tr.updates.contains(&Update { index, value }) {
                panic!("found an unremoved redundant update")
            }
        }
    }

    Ok(BoundedProgram { inits, trs, safes })
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

fn cardinality(universe: &UniverseBounds, sort: &Sort) -> usize {
    match sort {
        Sort::Bool => 2,
        Sort::Id(sort) => *universe.get(sort).unwrap(),
    }
}

/// A simplified syntax::Term that appears after quantifier enumeration.
/// It structurally enforces negation normal form, and has logical semantics.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Ast {
    // logic
    /// A conjunction of terms. True is represented by And(set![]).
    And(BTreeSet<Ast>),
    /// A disjunction of terms. False is represented by Or(set![]).
    Or(BTreeSet<Ast>),

    // guards
    /// An inclusion test
    Includes(String, Elements), // r(x)
    /// An exclusion test
    Excludes(String, Elements), // !r(x)

    // updates
    /// An insertion
    Insert(String, Elements), // r'(x)
    /// A removal
    Remove(String, Elements), // !r'(x)
    /// A no-op (used for verifying that the module constrains all elements)
    NoOp(String, Elements), // r'(x) = r(x)
                            // r'(x) != r(x) could exist but isn't supported
}

impl Ast {
    fn get_and(self) -> BTreeSet<Ast> {
        match self {
            Ast::And(terms) => terms,
            _ => btreeset![self],
        }
    }

    fn get_or(self) -> BTreeSet<Ast> {
        match self {
            Ast::Or(terms) => terms,
            _ => btreeset![self],
        }
    }

    fn get_guard(self, indices: &Indices) -> Result<Guard, TranslationError> {
        match self {
            Ast::Includes(set, element) => Ok(Guard {
                index: indices[&(set.as_str(), element)],
                value: true,
            }),
            Ast::Excludes(set, element) => Ok(Guard {
                index: indices[&(set.as_str(), element)],
                value: false,
            }),
            _ => Err(TranslationError::ExpectedGuard(self)),
        }
    }

    fn get_update(self, indices: &Indices) -> Result<Update, TranslationError> {
        match self {
            Ast::Insert(set, element) => Ok(Update {
                index: indices[&(set.as_str(), element)],
                value: true,
            }),
            Ast::Remove(set, element) => Ok(Update {
                index: indices[&(set.as_str(), element)],
                value: false,
            }),
            _ => Err(TranslationError::ExpectedUpdate(self)),
        }
    }

    fn contradicts(&self, other: &Ast) -> bool {
        matches!((self, other),
            (Ast::Includes(a, b), Ast::Excludes(c, d))
            | (Ast::Excludes(a, b), Ast::Includes(c, d))
            | (Ast::Insert(a, b), Ast::Remove(c, d))
            | (Ast::Insert(a, b), Ast::NoOp(c, d))
            | (Ast::Remove(a, b), Ast::Insert(c, d))
            | (Ast::Remove(a, b), Ast::NoOp(c, d))
            | (Ast::NoOp(a, b), Ast::Insert(c, d))
            | (Ast::NoOp(a, b), Ast::Remove(c, d))
                if a == c && b == d
        )
    }
}

fn and(terms: BTreeSet<Ast>) -> Ast {
    // flatten
    let terms: BTreeSet<Ast> = terms.into_iter().flat_map(Ast::get_and).collect();
    // short circuit if possible
    for a in &terms {
        if *a == Ast::Or(btreeset![]) || terms.iter().any(|b| a.contradicts(b)) {
            return Ast::Or(btreeset![]);
        }
    }
    // remove redundant updates
    let old = terms;
    let mut terms = btreeset![];
    for term in &old {
        if let Ast::Insert(set, element) = term.clone() {
            if old.contains(&Ast::Includes(set.clone(), element)) {
                terms.insert(Ast::NoOp(set, element));
                continue;
            }
        } else if let Ast::Remove(set, element) = term.clone() {
            if old.contains(&Ast::Excludes(set.clone(), element)) {
                terms.insert(Ast::NoOp(set, element));
                continue;
            }
        }

        terms.insert(term.clone());
    }
    // check for `(A or B) and (A or C)`
    'outer: loop {
        let old = terms.clone();
        for a in &old {
            if let Ast::Or(xs) = a {
                for b in &old {
                    if a != b {
                        if let Ast::Or(ys) = b {
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
    // unwrap if there's just one element
    if terms.len() == 1 {
        terms.pop_last().unwrap()
    } else {
        Ast::And(terms)
    }
}

fn or(terms: BTreeSet<Ast>) -> Ast {
    // flatten
    let mut terms: BTreeSet<Ast> = terms.into_iter().flat_map(Ast::get_or).collect();
    // short circuit if possible
    for a in &terms {
        if *a == Ast::And(btreeset![]) || terms.iter().any(|b| a.contradicts(b)) {
            return Ast::And(btreeset![]);
        }
    }
    // check for `(A and B) or (A and B and C)` and remove the superset
    let old = terms.clone();
    for a in &old {
        if let Ast::And(xs) = a {
            for b in &old {
                if a != b && (xs.contains(b) || matches!(b, Ast::And(ys) if xs.is_superset(ys))) {
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
            if let Ast::And(xs) = a {
                for b in &old {
                    if a != b {
                        if let Ast::And(ys) = b {
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
    // unwrap if there's just one element
    if terms.len() == 1 {
        terms.pop_last().unwrap()
    } else {
        Ast::Or(terms)
    }
}

fn not(term: Ast) -> Result<Ast, TranslationError> {
    match term {
        Ast::And(terms) => Ok(or(terms.into_iter().map(not).collect::<Result<_, _>>()?)),
        Ast::Or(terms) => Ok(and(terms.into_iter().map(not).collect::<Result<_, _>>()?)),
        Ast::Includes(set, element) => Ok(Ast::Excludes(set, element)),
        Ast::Excludes(set, element) => Ok(Ast::Includes(set, element)),
        // this makes sense because Ast has logical semantics
        Ast::Insert(set, element) => Ok(Ast::Remove(set, element)),
        Ast::Remove(set, element) => Ok(Ast::Insert(set, element)),
        Ast::NoOp(_, _) => Err(TranslationError::NegatedNoOp(term)),
    }
}

fn iff(x: Ast, y: Ast) -> Result<Ast, TranslationError> {
    Ok(or(btreeset![
        and(btreeset![x.clone(), y.clone()]),
        and(btreeset![not(x)?, not(y)?]),
    ]))
}

fn term_to_ast(
    term: &Term,
    universe: &UniverseBounds,
    assignments: &HashMap<String, usize>,
) -> Result<Ast, TranslationError> {
    let ast = |term| term_to_ast(term, universe, assignments);
    let element = |term| term_to_element(term, universe, assignments);

    let ast: Ast = match term {
        Term::Literal(true) => Ast::And(btreeset![]),
        Term::Literal(false) => Ast::Or(btreeset![]),
        Term::App(name, 0, args) => {
            let args = args.iter().map(element).collect::<Result<Vec<_>, _>>()?;
            Ast::Includes(name.clone(), Elements::new(args))
        }
        Term::App(name, 1, args) => {
            let args = args.iter().map(element).collect::<Result<Vec<_>, _>>()?;
            Ast::Insert(name.clone(), Elements::new(args))
        }
        Term::UnaryOp(UOp::Not, term) => not(ast(term)?)?,
        Term::BinOp(BinOp::Iff, a, b) => iff(ast(a)?, ast(b)?)?,
        Term::BinOp(BinOp::Equals, a, b) => match (element(a), element(b)) {
            (Ok(a), Ok(b)) if a == b => Ast::And(btreeset![]),
            (Ok(a), Ok(b)) if a != b => Ast::Or(btreeset![]),
            _ => iff(ast(a)?, ast(b)?)?,
        },
        Term::BinOp(BinOp::NotEquals, a, b) => {
            not(ast(&Term::BinOp(BinOp::Equals, a.clone(), b.clone()))?)?
        }
        Term::BinOp(BinOp::Implies, a, b) => or(btreeset![not(ast(a)?)?, ast(b)?]),
        Term::NAryOp(NOp::And, terms) => and(terms.iter().map(ast).collect::<Result<_, _>>()?),
        Term::NAryOp(NOp::Or, terms) => or(terms.iter().map(ast).collect::<Result<_, _>>()?),
        Term::Ite { cond, then, else_ } => or(btreeset![
            and(btreeset![ast(cond)?, ast(then)?]),
            and(btreeset![not(ast(cond)?)?, ast(else_)?])
        ]),
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
                    let mut new_assignments = assignments.clone();
                    for (name, element) in names.iter().zip(elements) {
                        new_assignments.insert(name.to_string(), element);
                    }
                    term_to_ast(body, universe, &new_assignments)
                })
                .collect::<Result<BTreeSet<_>, _>>()?;
            match quantifier {
                Quantifier::Forall => and(set),
                Quantifier::Exists => or(set),
            }
        }
        Term::UnaryOp(UOp::Prime | UOp::Always | UOp::Eventually, _)
        | Term::UnaryOp(UOp::Next | UOp::Previously, _)
        | Term::BinOp(BinOp::Until | BinOp::Since, ..)
        | Term::Id(_)
        | Term::App(..) => return Err(TranslationError::CouldNotTranslateToAst(term.clone())),
    };
    Ok(ast)
}

fn term_to_element(
    term: &Term,
    universe: &UniverseBounds,
    assignments: &HashMap<String, usize>,
) -> Result<usize, TranslationError> {
    let ast = |term| term_to_ast(term, universe, assignments);
    let element = |term| term_to_element(term, universe, assignments);

    let element: usize = match term {
        Term::Literal(_)
        | Term::UnaryOp(UOp::Not, ..)
        | Term::BinOp(BinOp::Iff | BinOp::Equals | BinOp::NotEquals | BinOp::Implies, ..)
        | Term::NAryOp(NOp::And | NOp::Or, ..)
        | Term::Quantified { .. } => match ast(term)? {
            Ast::And(set) if set.is_empty() => 1,
            Ast::Or(set) if set.is_empty() => 0,
            _ => return Err(TranslationError::CouldNotTranslateToElement(term.clone())),
        },
        Term::Id(id) => assignments[id],
        Term::Ite { cond, then, else_ } => match element(cond)? {
            1 => element(then)?,
            0 => element(else_)?,
            _ => unreachable!(),
        },
        Term::UnaryOp(UOp::Prime | UOp::Always | UOp::Eventually, _)
        | Term::UnaryOp(UOp::Next | UOp::Previously, _)
        | Term::BinOp(BinOp::Until | BinOp::Since, ..)
        | Term::App(..) => return Err(TranslationError::CouldNotTranslateToElement(term.clone())),
    };
    Ok(element)
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
fn distribute_conjunction(term: Ast) -> Ast {
    match term {
        Ast::And(terms) if !terms.is_empty() => {
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
        Ast::Or(terms) => {
            // or() internally flattens nested Ors
            or(terms.into_iter().map(distribute_conjunction).collect())
        }
        _ => term,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn includes(set: &str, element: Elements, indices: &Indices) -> Guard {
        Guard {
            index: indices[&(set, element)],
            value: true,
        }
    }
    fn excludes(set: &str, element: Elements, indices: &Indices) -> Guard {
        Guard {
            index: indices[&(set, element)],
            value: false,
        }
    }
    fn insert(set: &str, element: Elements, indices: &Indices) -> Update {
        Update {
            index: indices[&(set, element)],
            value: true,
        }
    }
    fn remove(set: &str, element: Elements, indices: &Indices) -> Update {
        Update {
            index: indices[&(set, element)],
            value: false,
        }
    }
    fn state(iter: impl IntoIterator<Item = u8>) -> BoundedState {
        let mut out = BoundedState(BitArray::ZERO);
        for (i, x) in iter.into_iter().enumerate() {
            out.0.set(i, x == 1);
        }
        out
    }

    #[test]
    fn checker_set_basic() {
        let program = BoundedProgram {
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
        let result0 = interpret(&program, Some(0), TraceCompression::No);
        let result1 = interpret(&program, Some(1), TraceCompression::No);
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
        let result1 = interpret(&program, Some(0), TraceCompression::No);
        let result2 = interpret(&program, Some(1), TraceCompression::No);
        let result3 = interpret(&program, Some(2), TraceCompression::No);
        let result4 = interpret(&program, Some(3), TraceCompression::No);
        let result5 = interpret(&program, Some(4), TraceCompression::No);
        assert_eq!(result1, InterpreterResult::Unknown);
        assert_eq!(result2, InterpreterResult::Unknown);
        assert_eq!(result3, InterpreterResult::Unknown);
        let mut expected4 = Trace::new(state([1, 0, 0, 0]), TraceCompression::No);
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
    fn checker_set_translate_lockserver() -> Result<(), TranslationError> {
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

        let mut m = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut m).unwrap();
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

        let expected = BoundedProgram {
            inits: vec![state([0, 0, 0, 0, 0, 0, 0, 0, 1])],
            trs,
            safes: vec![
                vec![excludes("holds_lock", element![0], &indices)],
                vec![excludes("holds_lock", element![1], &indices)],
            ],
        };

        let target = translate(&m, &universe)?;
        assert_eq!(target.inits, expected.inits);
        assert_eq!(target.safes, expected.safes);
        assert_eq!(
            target.trs.iter().collect::<BTreeSet<_>>(),
            expected.trs.iter().collect::<BTreeSet<_>>()
        );

        let output = interpret(&target, None, TraceCompression::No);
        assert_eq!(output, InterpreterResult::Unknown);

        Ok(())
    }

    #[test]
    fn checker_set_translate_lockserver_buggy() -> Result<(), TranslationError> {
        // A buggy version of lockserv. See "here is the bug" below.
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
            ### here is the bug: we don't remove n from the unlock_msg relation
            (((unlock_msg(N))') <-> unlock_msg(N)) &
            ((server_holds_lock)')) &
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) &
        (forall x0:node. ((grant_msg(x0))') = grant_msg(x0)) &
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0)))

# safety:
assert always (forall N1:node, N2:node. holds_lock(N1) & holds_lock(N2) -> N1 = N2)
        ";

        // To exploit this bug into a safety violation, you first need to have one node acquire and
        // release the lock via the following 5 transitions:
        // - send lock_msg, send grant, receive grant, send unlock, receive unlock
        // then you need two nodes to both acquire the lock:
        // - send lock_msg, send grant, receive grant (3 transitions)
        // - receive unlock (1 transition, exploiting the fact that it was not removed)
        // - send lock_msg, send grant, receive grant (3 transitions)
        //
        // In total, that's 5 + 3 + 1 + 3 = 12 transitions to exploit it.
        //
        // The test below asserts that interpret finds the bug at depth 12 but not at depth 11.

        let mut m = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut m).unwrap();
        let universe = std::collections::HashMap::from([("node".to_string(), 2)]);
        let target = translate(&m, &universe)?;

        let bug = interpret(&target, Some(12), TraceCompression::No);
        if let InterpreterResult::Counterexample(trace) = &bug {
            println!("{:#?}", trace);
            assert_eq!(trace.depth(), 12);
        } else {
            assert!(matches!(bug, InterpreterResult::Counterexample(_)));
        }

        let too_short = interpret(&target, Some(11), TraceCompression::No);
        assert_eq!(too_short, InterpreterResult::Unknown);

        Ok(())
    }

    #[test]
    fn checker_set_translate_consensus() -> Result<(), TranslationError> {
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
    (forall N1:node, N2:node, N:node. !voted(src) & vote_request_msg(dst, src) & ((vote_msg(N1, N2))' <->
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

        let mut m = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut m).unwrap();
        let universe = std::collections::HashMap::from([
            ("node".to_string(), 2),
            ("quorum".to_string(), 2),
            ("value".to_string(), 2),
        ]);
        let target = translate(&m, &universe)?;
        let output = interpret(&target, Some(10), TraceCompression::No);
        assert_eq!(output, InterpreterResult::Unknown);

        Ok(())
    }

    #[test]
    fn checker_set_immutability() {
        let source = "
immutable r: bool
assume r
assert always r
        ";
        let mut module = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();
        let universe = std::collections::HashMap::new();
        assert_eq!(
            Some(CheckerAnswer::Unknown),
            check(&module, &universe, Some(10), true.into())
        );
    }
}

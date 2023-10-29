// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Implement simple components, lemma domains and data structures for use in inference.

use fly::ouritertools::OurItertools;
use itertools::Itertools;
use solver::basics::{BasicCanceler, BasicSolver, MultiCanceler};
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::sync::{Arc, Mutex, RwLock};
use std::time::Instant;

use fly::semantics::Model;
use fly::syntax::{Module, Signature, Term};

use bounded::simulator::MultiSimulator;

use crate::{
    basics::{CexResult, FOModule, QalphaConfig},
    hashmap::{HashMap, HashSet},
    parallel::Tasks,
    parallel::{paralllelism, ParallelWorker},
    qalpha::{
        atoms::Literals,
        fixpoint::{defaults, SamplePriority, SimulationOptions},
        subsume::{Clause, Cnf, Dnf, Element, PDnf, Structure},
        weaken::{Domain, LemmaKey, LemmaQf, WeakenLemmaSet},
    },
};

/// The minimal number of disjuncts a lemma is allowed to have.
/// This corresponds to number of cubes in DNF, or the clause size in CNF.
const MIN_DISJUNCTS: usize = 3;

fn choose(n: usize, k: usize) -> usize {
    if n < k {
        0
    } else {
        ((n - k + 1)..=n).product::<usize>() / (1..=k).product::<usize>()
    }
}

fn choose_combinations(n: usize, k: usize, count: usize) -> usize {
    let combinations: usize = (0..=k).map(|i| choose(n, i)).sum();
    choose(combinations, count)
}

#[derive(Clone)]
pub struct LemmaCnf {
    clauses: usize,
    clause_size: usize,
    literals: Arc<Literals>,
}

impl Debug for LemmaCnf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CNF")
            .field("clauses", &self.clauses)
            .field("clause_size", &self.clause_size)
            .finish()
    }
}

impl LemmaQf for LemmaCnf {
    type Body = Cnf;

    fn new(
        cfg: &QalphaConfig,
        literals: Arc<Literals>,
        non_universal_vars: &HashSet<String>,
    ) -> Self {
        let clauses = if non_universal_vars.is_empty() {
            1
        } else {
            cfg.clauses
                .expect("Maximum number of clauses not provided.")
        };
        let clause_size = cfg
            .clause_size
            .expect("Maximum number of literals per clause not provided.");

        Self {
            clauses,
            clause_size,
            literals,
        }
    }

    fn weaken<I>(&self, body: Self::Body, structure: &Structure, ignore: I) -> Vec<Self::Body>
    where
        I: Fn(&Self::Body) -> bool,
    {
        let cfg = (self.clauses, (self.clause_size, self.literals.clone()));
        body.weaken(&cfg, structure)
            .into_iter()
            .filter(|cnf| !ignore(cnf))
            .collect_vec()
    }

    fn approx_space_size(&self) -> usize {
        choose_combinations(self.literals.len(), self.clause_size, self.clauses)
    }

    fn sub_spaces(&self) -> Vec<Self> {
        (1..=self.clauses)
            .flat_map(|clauses| {
                (MIN_DISJUNCTS..=self.clause_size).map(move |clause_size| Self {
                    clauses,
                    clause_size,
                    literals: self.literals.clone(),
                })
            })
            .collect_vec()
    }

    fn contains(&self, other: &Self) -> bool {
        self.clauses >= other.clauses
            && self.clause_size >= other.clause_size
            && self.literals.is_superset(&other.literals)
    }

    fn body_from_clause(clause: Clause) -> Self::Body {
        clause.to_cnf()
    }
}

#[derive(Clone)]
pub struct LemmaDnf {
    cubes: usize,
    cube_size: usize,
    literals: Arc<Literals>,
}

impl Debug for LemmaDnf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DNF")
            .field("cubes", &self.cubes)
            .field("cube_size", &self.cube_size)
            .finish()
    }
}

impl LemmaQf for LemmaDnf {
    type Body = Dnf;

    fn new(
        cfg: &QalphaConfig,
        literals: Arc<Literals>,
        non_universal_vars: &HashSet<String>,
    ) -> Self {
        let cubes = cfg.cubes.expect("Maximum number of cubes not provided.");
        let cube_size = if non_universal_vars.is_empty() {
            1
        } else {
            cfg.cube_size
                .expect("Maximum size of non-unit cubes not provided.")
        };

        Self {
            cubes,
            cube_size,
            literals,
        }
    }

    fn weaken<I>(&self, body: Self::Body, structure: &Structure, ignore: I) -> Vec<Self::Body>
    where
        I: Fn(&Self::Body) -> bool,
    {
        let cfg = (self.cubes, (self.cube_size, self.literals.clone()));
        body.weaken(&cfg, structure)
            .into_iter()
            .filter(|dnf| !ignore(dnf))
            .collect_vec()
    }

    fn approx_space_size(&self) -> usize {
        choose_combinations(self.literals.len(), self.cube_size, self.cubes)
    }

    fn sub_spaces(&self) -> Vec<Self> {
        (MIN_DISJUNCTS..=self.cubes)
            .flat_map(|cubes| {
                (1..=self.cube_size).map(move |cube_size| Self {
                    cubes,
                    cube_size,
                    literals: self.literals.clone(),
                })
            })
            .collect_vec()
    }

    fn contains(&self, other: &Self) -> bool {
        self.cubes >= other.cubes
            && self.cube_size >= other.cube_size
            && self.literals.is_superset(&other.literals)
    }

    fn body_from_clause(clause: Clause) -> Self::Body {
        clause.to_dnf()
    }
}

#[derive(Clone)]
pub struct LemmaPDnf {
    cubes: usize,
    cube_size: usize,
    non_unit: usize,
    literals: Arc<Literals>,
    non_universal_literals: Arc<Literals>,
}

impl Debug for LemmaPDnf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("pDNF")
            .field("cubes", &self.cubes)
            .field("cube_size", &self.cube_size)
            .field("non_unit", &self.non_unit)
            .finish()
    }
}

fn unit_resolution(mut base: <PDnf as Element>::Base) -> <PDnf as Element>::Base {
    let neg_clause: Vec<_> = base.0.iter().map(|literal| literal.negate()).collect();

    for cube in &mut base.1 {
        cube.retain(|literal| !neg_clause.contains(literal));
    }

    base
}

impl LemmaQf for LemmaPDnf {
    type Body = PDnf;
    fn new(
        cfg: &QalphaConfig,
        literals: Arc<Literals>,
        non_universal_vars: &HashSet<String>,
    ) -> Self {
        let cubes = cfg.cubes.expect("Maximum number of cubes not provided.");
        let mut cube_size = cfg
            .cube_size
            .expect("Maximum size of non-unit cubes not provided.");
        let mut non_unit = cfg
            .non_unit
            .expect("Number of pDNF non-unit cubes not provided.");

        if non_universal_vars.is_empty() {
            non_unit = 0;
        }

        if non_unit == 0 {
            cube_size = 1;
        }

        assert!(cubes >= non_unit && cube_size > 0);

        let non_universal_literals = Arc::new(
            literals
                .iter()
                .filter(|lit| !lit.ids().is_disjoint(non_universal_vars))
                .cloned()
                .collect(),
        );

        Self {
            cubes,
            non_unit,
            cube_size,
            literals,
            non_universal_literals,
        }
    }

    fn weaken<I>(&self, body: Self::Body, structure: &Structure, ignore: I) -> Vec<Self::Body>
    where
        I: Fn(&Self::Body) -> bool + Sync,
    {
        let base = body.to_base(true);
        let clause_literals = Arc::new(
            self.literals
                .iter()
                .filter(|lit| {
                    !lit.is_neq()
                        && !base.0.contains(&lit.negate().into())
                        && !base
                            .1
                            .iter()
                            .any(|cube| cube.contains(&(*lit).clone().into()))
                })
                .cloned()
                .collect(),
        );
        let dnf_literals = Arc::new(
            self.non_universal_literals
                .iter()
                .filter(|lit| !base.0.contains(&lit.negate().into()))
                .cloned()
                .collect(),
        );
        let clause_cfg = (self.cubes - base.1.len(), clause_literals);
        let dnf_cfg = (
            self.non_unit.min(self.cubes - base.0.len()),
            (self.cube_size, dnf_literals),
        );

        body.weaken(&(clause_cfg, dnf_cfg), structure)
            .into_iter()
            .map(|pdnf| unit_resolution(pdnf.to_base(true)))
            .filter(|base| {
                assert!(base.0.len() + base.1.len() <= self.cubes);
                base.1.iter().all(|cube| cube.len() > 1)
            })
            .map(|base| PDnf::from_base(base, true))
            .filter(|pdnf| !ignore(pdnf))
            .collect()
    }

    fn approx_space_size(&self) -> usize {
        (0..=self.non_unit)
            .map(|non_unit| {
                let clauses = choose_combinations(self.literals.len(), self.cubes - non_unit, 1);
                let dnfs = choose_combinations(
                    self.non_universal_literals.len(),
                    self.cube_size,
                    non_unit,
                );
                clauses * dnfs
            })
            .sum()
    }

    fn sub_spaces(&self) -> Vec<Self> {
        (1..=self.cube_size)
            .flat_map(|cube_size| {
                let max_cubes =
                    self.cubes
                        .min(choose_combinations(self.literals.len(), cube_size, 1));
                (MIN_DISJUNCTS..=max_cubes).flat_map(move |cubes| {
                    let max_non_unit = if cube_size <= 1 { 0 } else { self.non_unit };
                    (0..=max_non_unit).map(move |non_unit| Self {
                        cubes,
                        cube_size,
                        non_unit,
                        literals: self.literals.clone(),
                        non_universal_literals: self.non_universal_literals.clone(),
                    })
                })
            })
            .collect_vec()
    }

    fn contains(&self, other: &Self) -> bool {
        self.cubes >= other.cubes
            && self.non_unit >= other.non_unit
            && self.cube_size >= other.cube_size
            && self.literals.is_superset(&other.literals)
            && self
                .non_universal_literals
                .is_superset(&other.non_universal_literals)
    }

    fn body_from_clause(clause: Clause) -> Self::Body {
        (clause, Dnf::bottom()).into()
    }
}

/// Compute the names of [`Term::Id`]'s present in the given term.
///
/// Supports only quantifier-free terms.
pub fn ids(term: &Term) -> HashSet<String> {
    match term {
        Term::Id(name) => HashSet::from_iter([name.clone()]),
        Term::App(_, _, vt) => vt.iter().flat_map(ids).collect(),
        Term::UnaryOp(_, t) => ids(t),
        Term::BinOp(_, t1, t2) => [t1, t2].iter().flat_map(|t| ids(t)).collect(),
        Term::NAryOp(_, vt) => vt.iter().flat_map(ids).collect(),
        Term::Ite { cond, then, else_ } => {
            [cond, then, else_].iter().flat_map(|t| ids(t)).collect()
        }
        _ => HashSet::default(),
    }
}

#[derive(PartialEq, Eq, Debug)]
enum Blocked<I: Eq + Hash> {
    Initial,
    Consequence(HashSet<I>),
    Transition(HashSet<I>),
}

impl<I: Eq + Hash + Copy> Blocked<I> {
    fn constituents(&self) -> HashSet<I> {
        match self {
            Blocked::Initial => HashSet::default(),
            Blocked::Consequence(core) | Blocked::Transition(core) => core.clone(),
        }
    }

    fn contains(&self, id: &I) -> bool {
        match self {
            Blocked::Initial => false,
            Blocked::Consequence(core) | Blocked::Transition(core) => core.contains(id),
        }
    }
}

struct LemmaManager<I: Hash + Eq + Copy> {
    /// The set of lemmas inductively implied by the frame, mapped to the unsat-cores implying them.
    blocked_to_core: HashMap<I, Blocked<I>>,
    /// Mapping from each lemma to the lemmas whose inductiveness proof they paricipate in.
    core_to_blocked: HashMap<I, HashSet<I>>,
    /// A subset of the frame's lemmas which inductively implies the safety assertions.
    safety_core: Option<Blocked<I>>,
}

impl<I: Hash + Eq + Copy> LemmaManager<I> {
    fn new() -> Self {
        Self {
            blocked_to_core: HashMap::default(),
            core_to_blocked: HashMap::default(),
            safety_core: None,
        }
    }

    fn inductively_proven(&self, id: &I) -> bool {
        self.blocked_to_core
            .get(id)
            .is_some_and(|core| matches!(core, Blocked::Transition(_)))
    }

    fn add_blocked(&mut self, id: I, core: Blocked<I>) {
        for core_id in core.constituents() {
            if let Some(hs) = self.core_to_blocked.get_mut(&core_id) {
                hs.insert(id);
            } else {
                self.core_to_blocked
                    .insert(core_id, HashSet::from_iter([id]));
            }
        }
        self.blocked_to_core.insert(id, core);
    }

    fn remove_from_blocked(&mut self, id: &I) {
        let core = self.blocked_to_core.remove(id).unwrap();
        for core_id in &core.constituents() {
            if let Some(b) = self.core_to_blocked.get_mut(core_id) {
                b.remove(id);
                if b.is_empty() {
                    self.core_to_blocked.remove(core_id);
                }
            }
        }
    }

    fn remove_from_cores(&mut self, id: &I) {
        if let Some(blocked) = self.core_to_blocked.remove(id) {
            for blocked_id in &blocked {
                self.remove_from_blocked(blocked_id);
            }
        }
    }

    fn remove(&mut self, id: &I) {
        if self
            .safety_core
            .as_ref()
            .is_some_and(|core| core.contains(id))
        {
            self.safety_core = None;
        }
        if self.blocked_to_core.contains_key(id) {
            self.remove_from_blocked(id);
        }
        if self.core_to_blocked.contains_key(id) {
            self.remove_from_cores(id);
        }
    }

    fn blocked_closure(&self, core: HashSet<I>) -> Option<HashSet<I>> {
        let mut extended_core: HashSet<I> = HashSet::default();
        let mut new_ids: HashSet<I> = core;

        while !new_ids.is_empty() {
            let mut new_new_ids = HashSet::default();
            for id in &new_ids {
                new_new_ids.extend(self.blocked_to_core.get(id)?.constituents());
            }

            extended_core.extend(new_ids);
            new_ids = new_new_ids
                .into_iter()
                .filter(|id| !extended_core.contains(id))
                .collect();
        }

        extended_core.retain(|id| self.inductively_proven(id));

        Some(extended_core)
    }
}

/// A [`InductionFrame`] maintains quantified formulas during invariant inference.
pub struct InductionFrame<'a, E, L>
where
    E: Element,
    L: LemmaQf<Body = E>,
{
    /// Manages lemmas inductively proven by the frame.
    lemmas: RwLock<LemmaManager<LemmaKey>>,
    /// The mapping from a key to the lemma's position in the ordering.
    key_to_idx: HashMap<LemmaKey, usize>,
    /// The signature of the frame's lemmas.
    signature: Arc<Signature>,
    /// The lemmas in the frame, maintained in a way that supports weakening them.
    weaken_lemmas: WeakenLemmaSet<E, L>,
    /// Whether to extend CTI traces, and how much.
    sim_options: SimulationOptions,
    /// The time of creation of the frame (for logging purposes)
    start_time: Instant,
    /// The simulator to run simulations from reachable states or previous samples
    simulator: MultiSimulator<'a>,
    /// Whether the search for the invariant is property-directed
    property_directed: bool,
}

impl<'a, E, L> InductionFrame<'a, E, L>
where
    E: Element,
    L: LemmaQf<Body = E>,
{
    /// Create a new frame using the given configuration.
    pub fn new(
        module: &'a Module,
        signature: Arc<Signature>,
        domains: Vec<Domain<L>>,
        sim_options: SimulationOptions,
        property_directed: bool,
    ) -> Self {
        let mut weaken_lemmas = WeakenLemmaSet::new(signature.clone(), domains);
        weaken_lemmas.init();
        let key_to_idx = weaken_lemmas.key_to_idx();

        InductionFrame {
            lemmas: RwLock::new(LemmaManager::new()),
            key_to_idx,
            signature,
            weaken_lemmas,
            sim_options,
            start_time: Instant::now(),
            simulator: MultiSimulator::new(module),
            property_directed,
        }
    }

    /// Get the term representation of the lemmas in the frame.
    pub fn proof(&self) -> Vec<Term> {
        self.weaken_lemmas.to_terms()
    }

    /// Get a reduced (but equivalent) fixpoint representations.
    pub fn reduced_proof(&self) -> Option<Vec<Term>> {
        let manager = self.lemmas.read().unwrap();
        let mut reduced_proof = vec![];
        let mut indices = vec![];
        for (i, (t, id)) in self.weaken_lemmas.to_terms_keys().enumerate() {
            // Not inductive
            if !manager.blocked_to_core.contains_key(&id) {
                return None;
            }
            // Necessary
            if manager.inductively_proven(&id) {
                reduced_proof.push(t);
                indices.push(i);
            }
        }

        self.log_info(format!("Reduced lemmas at indices {indices:?}"));

        Some(reduced_proof)
    }

    /// Get a minimized inductive set of lemmas in the frame which inductively implies safety,
    /// provided that `is_safe` has been called and returned `true`.
    pub fn safety_proof(&self) -> Option<Vec<Term>> {
        let manager = self.lemmas.read().unwrap();
        let extended_core: HashSet<LemmaKey> =
            manager.blocked_closure(manager.safety_core.as_ref().unwrap().constituents())?;

        let indices = extended_core
            .iter()
            .map(|key| self.key_to_idx[key])
            .collect_vec();
        let core = extended_core
            .iter()
            .map(|key| self.weaken_lemmas.key_to_term(key))
            .collect_vec();

        self.log_info(format!("Safety lemmas at indices {indices:?}"));

        Some(core)
    }

    /// Add details about the frame to the given [`Display`].
    pub fn add_details<D: Display>(&self, d: D) -> String {
        format!(
            "[{:.5}s] [{}] {}",
            self.start_time.elapsed().as_secs_f64(),
            self.weaken_lemmas.len(),
            d,
        )
    }

    /// Log at `info` level along with details about the frame.
    pub fn log_info<D: Display>(&self, d: D) {
        log::info!("{}", self.add_details(d));
    }

    /// Get an initial state which violates one of the frame's lemmas.
    pub fn init_cex<S: BasicSolver>(&self, fo: &FOModule, solver: &S) -> Vec<Model> {
        self.log_info("Finding initial CTI...");
        let results = ParallelWorker::new(
            &mut self.weaken_lemmas.keys().map(|key| (*key, *key)).collect(),
            |_, key| {
                {
                    let manager = self.lemmas.read().unwrap();
                    if manager.blocked_to_core.contains_key(key) {
                        return (None, vec![], false);
                    }
                }

                let term = self.weaken_lemmas.key_to_term(key);
                let res = fo.init_cex(solver, &term);
                let found = res.is_some();
                return (res, vec![], found);
            },
            paralllelism(),
        )
        .run();

        let mut ctis = vec![];
        let mut manager = self.lemmas.write().unwrap();
        for (key, out) in results {
            match out {
                Some(model) => ctis.push(model),
                None => {
                    manager.blocked_to_core.insert(key, Blocked::Initial);
                }
            }
        }

        self.log_info(format!("{} initial CTI(s) found.", ctis.len()));

        ctis
    }

    /// Weaken the lemmas in the frame.
    pub fn weaken(&mut self, models: &[Model]) -> bool {
        let removed = models
            .iter()
            .flat_map(|model| {
                let rem = self.weaken_lemmas.weaken(model).0;
                if !rem.is_empty() {
                    self.log_info("Weakened.");
                }
                rem
            })
            .collect_vec();
        if removed.is_empty() {
            false
        } else {
            self.remove_by_keys(&removed);
            self.log_info("Cores updated.");
            self.key_to_idx = self.weaken_lemmas.key_to_idx();
            self.log_info("Indices updated.");
            true
        }
    }

    pub fn remove_unsat(&mut self, models: &[Model]) {
        let removed = models
            .iter()
            .flat_map(|model| {
                let rem = self.weaken_lemmas.remove_unsat(model);
                if !rem.is_empty() {
                    self.log_info("Removed unsatisfied.");
                }
                rem
            })
            .collect_vec();
        if !removed.is_empty() {
            self.remove_by_keys(&removed);
            self.log_info("Cores updated.");
            self.key_to_idx = self.weaken_lemmas.key_to_idx();
            self.log_info("Indices updated.");
        }
    }

    fn remove_by_keys(&self, removed: &[LemmaKey]) {
        {
            let mut manager = self.lemmas.write().unwrap();
            for key in removed {
                manager.remove(key);
            }
        }
    }

    /// Extend simulations of traces in order to find a CTI for the current frame.
    pub fn extend<C: BasicCanceler>(
        &self,
        samples: &mut Tasks<SamplePriority, Model>,
        canceler: C,
    ) -> Vec<Model> {
        self.log_info("Simulating CTI traces...");
        // Maps models to whether they violate the current frame, and extends them using the simulator.
        let results = ParallelWorker::new(
            samples,
            |(_, t_depth, mut since_weaken), model| {
                let unsat = !self.weaken_lemmas.unsat(model).is_empty();
                let cancel = if unsat {
                    since_weaken = 0;
                    canceler.cancel();
                    true
                } else {
                    canceler.is_canceled()
                };

                let new_samples = if let Some(p) = self.sim_options.sample_priority(
                    &model.universe,
                    t_depth.depth() + 1,
                    since_weaken + 1,
                ) {
                    let sim = self
                        .simulator
                        .simulate_new(model)
                        .into_iter()
                        .map(|sample| (p.clone(), sample))
                        .collect_vec();
                    log::debug!("Found {} simulated samples from CTI.", sim.len());
                    sim
                } else {
                    vec![]
                };

                (unsat, new_samples, cancel)
            },
            paralllelism(),
        )
        .run();

        let models = results
            .into_iter()
            .filter(|(_, unsat)| *unsat)
            .map(|(m, _)| m)
            .collect_vec();

        self.log_info(format!("{} simulated CTI(s) found.", models.len()));

        models
    }

    /// Make sure that all lemmas overapproximate initial states and remove the corresponding proofs.
    pub fn finish_initial(&self) {
        let mut manager = self.lemmas.write().unwrap();
        for key in self.weaken_lemmas.keys() {
            assert_eq!(manager.blocked_to_core.get(key), Some(&Blocked::Initial));
        }
        manager.blocked_to_core = HashMap::default();
        manager.core_to_blocked = HashMap::default();
    }

    /// Get an post-state of the frame which violates one of the frame's lemmas.
    pub fn trans_cex<S: BasicSolver>(
        &self,
        fo: &FOModule,
        solver: &S,
        cancelers: MultiCanceler<MultiCanceler<S::Canceler>>,
    ) -> Vec<Model> {
        self.log_info("Finding transition CTI...");
        let mut tasks = if self.property_directed {
            let manager = self.lemmas.read().unwrap();
            manager
                .safety_core
                .as_ref()
                .unwrap()
                .constituents()
                .into_iter()
                .map(|key| ((0_u8, key), key))
                .collect()
        } else {
            self.weaken_lemmas
                .keys()
                .map(|key| ((1_u8, *key), *key))
                .collect()
        };

        let first_sat = Mutex::new(None);
        let start_time = Instant::now();
        // The tasks here are lemmas ID's, and each result is an Option<CexResult>.
        let results = ParallelWorker::new(
            &mut tasks,
            |(check_implied, _), key| {
                {
                    let blocked = self.lemmas.read().unwrap();
                    if let Some(core) = blocked.blocked_to_core.get(key) {
                        return (
                            None,
                            core.constituents()
                                .into_iter()
                                .map(|k| ((1, k), k))
                                .collect(),
                            false,
                        );
                    }
                }

                let idx = self.key_to_idx[key];
                let term = self.weaken_lemmas.key_to_term(key);
                // Check if the lemma is implied by the lemmas preceding it.
                if *check_implied == 1 {
                    let query_start = Instant::now();
                    // Begin with a syntactic implication check.
                    if let Some(blocking_core) = self.weaken_lemmas.get_implying(key) {
                        log::info!(
                            "{:>8}ms. ({idx}) Syntactic implication found UNSAT with {} formulas in core",
                            query_start.elapsed().as_millis(),
                            blocking_core.len(),
                        );
                        let core_tasks = blocking_core.iter().cloned().map(|k| ((1, k), k)).collect();
                        let core = blocking_core.iter().cloned().collect();
                        {
                            let mut manager = self.lemmas.write().unwrap();
                            manager.add_blocked(*key, Blocked::Consequence(blocking_core));
                        }
                        return (Some(CexResult::UnsatCore(core)), core_tasks, false);
                    }

                    let query_start = Instant::now();
                    // If that fails, use a semantic implication check.
                    let res = fo.implication_cex(
                        solver,
                        &self.weaken_lemmas.hypotheses(Some(*key), vec![]),
                        &term,
                        Some(cancelers.clone()),
                        false,
                    );
                    if let CexResult::UnsatCore(core) = &res {
                        log::info!(
                            "{:>8}ms. ({idx}) Semantic implication found UNSAT with {} formulas in core",
                            query_start.elapsed().as_millis(),
                            core.len(),
                        );
                        let blocking_core = Blocked::Consequence(core.iter().cloned().collect());
                        {
                            let mut manager = self.lemmas.write().unwrap();
                            manager.add_blocked(*key, blocking_core);
                        }
                        let core_tasks = core.iter().cloned().map(|k| ((0, k), k)).collect();
                        return (Some(res), core_tasks, false);
                    }
                }

                // Check if the lemma is inductively implied by the entire frame.
                let query_start = Instant::now();
                let res = fo.trans_cex(
                    solver,
                    &self.weaken_lemmas.hypotheses(None, vec![*key]),
                    &term,
                    false,
                    Some(cancelers.clone()),
                    false,
                );
                match &res {
                    CexResult::Cex(_) => {
                        cancelers.cancel();
                        {
                            let mut first_sat_lock = first_sat.lock().unwrap();
                            if first_sat_lock.is_none() {
                                *first_sat_lock = Some(Instant::now());
                            }
                        }
                        log::info!(
                            "{:>8}ms. ({idx}) Transition found SAT",
                            query_start.elapsed().as_millis()
                        );
                        (Some(res), vec![], true)
                    }
                    CexResult::UnsatCore(core) => {
                        log::info!(
                            "{:>8}ms. ({idx}) Transition found UNSAT with {} formulas in core",
                            start_time.elapsed().as_millis(),
                            core.len()
                        );
                        let core = Blocked::Transition(core.iter().cloned().collect());
                        let core_tasks = core
                            .constituents()
                            .into_iter()
                            .map(|k| ((0, k), k))
                            .collect();
                        {
                            let mut manager = self.lemmas.write().unwrap();
                            manager.add_blocked(*key, core);
                        }
                        (Some(res), core_tasks, false)
                    }
                    CexResult::Canceled => (Some(res), vec![], true),
                    CexResult::Unknown(reason) => {
                        log::info!(
                            "{:>8}ms. ({idx}) Transition found unknown: {reason}",
                            query_start.elapsed().as_millis()
                        );
                        (Some(res), vec![], false)
                    }
                }
            },
            paralllelism(),
        )
        .run();

        cancelers.cancel();

        let mut ctis = vec![];
        let mut total_sat = 0_usize;
        let mut total_unsat = 0_usize;
        let mut unknown = false;
        for (_, out) in results {
            match out {
                Some(CexResult::Cex(mut models)) => {
                    total_sat += 1;
                    ctis.push(models.pop().unwrap());
                }
                Some(CexResult::UnsatCore(_)) => {
                    total_unsat += 1;
                }
                Some(CexResult::Unknown(_)) => {
                    unknown = true;
                }
                _ => (),
            }
        }

        if ctis.is_empty() && unknown {
            panic!("SMT queries got 'unknown' and no SAT results.")
        }

        log::info!(
            "    SMT STATS: total_time={:.5}s, until_sat={:.5}s, sat_found={}, unsat_found={}",
            (Instant::now() - start_time).as_secs_f64(),
            (first_sat.into_inner().unwrap().unwrap_or(start_time) - start_time).as_secs_f64(),
            total_sat,
            total_unsat,
        );
        self.log_info(format!("{} transition CTI(s) found.", ctis.len()));

        ctis
    }

    /// Return whether the current frame inductively implies the safety assertions
    /// of the given module.
    pub fn is_safe<S: BasicSolver>(&self, fo: &FOModule, solver: &S) -> bool {
        let mut manager = self.lemmas.write().unwrap();
        if manager.safety_core.is_some() {
            return true;
        }

        let start_time = Instant::now();
        let hyp = self.weaken_lemmas.hypotheses(None, vec![]);
        if let CexResult::UnsatCore(core) = fo.safe_implication_cex(solver, &hyp) {
            log::info!(
                "{:>8}ms. Safety implied with {} formulas in core",
                start_time.elapsed().as_millis(),
                core.len()
            );
            manager.safety_core = Some(Blocked::Consequence(HashSet::from_iter(core)));
            return true;
        }

        match fo.trans_safe_cex(solver, &hyp) {
            CexResult::Cex(_) => {
                log::info!("{:>8}ms. Safety violated", start_time.elapsed().as_millis());
                false
            }
            CexResult::UnsatCore(core) => {
                log::info!(
                    "{:>8}ms. Safety proven using transition with {} formulas in core",
                    start_time.elapsed().as_millis(),
                    core.len()
                );
                manager.safety_core = Some(Blocked::Transition(HashSet::from_iter(core)));
                true
            }
            _ => panic!("safety check failed"),
        }
    }

    pub fn initial_samples(&mut self) -> Tasks<SamplePriority, Model> {
        let max_model_size = self
            .sim_options
            .max_size
            .unwrap_or(defaults::MAX_MODEL_SIZE);
        let universe_sizes = (0..self.signature.sorts.len())
            .map(|_| 1..=self.sim_options.max_size.unwrap_or(max_model_size))
            .multi_cartesian_product_fixed()
            .filter(|u| u.iter().copied().sum::<usize>() <= max_model_size)
            .sorted_by_key(|u| u.iter().copied().sorted().collect_vec());
        let models = universe_sizes
            .flat_map(|universe| self.simulator.initials_new(&universe))
            .collect_vec();

        self.weaken(&models);

        let mut samples = Tasks::new();
        for model in models {
            samples.insert(
                self.sim_options
                    .sample_priority(&model.universe, 0, 0)
                    .unwrap(),
                model,
            )
        }

        samples
    }

    pub fn see(&self, model: &Model) -> bool {
        self.simulator.see(model)
    }
}

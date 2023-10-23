// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Implement simple components, lemma domains and data structures for use in inference.

use fly::ouritertools::OurItertools;
use itertools::Itertools;
use solver::basics::{BasicSolver, BasicSolverCanceler, SolverCancelers};
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
    parallel::PriorityTasks,
    parallel::{paralllelism, PriorityWorker},
    qalpha::{
        atoms::Literals,
        fixpoint::{defaults, SamplePriority, SimulationOptions},
        quant::QuantifierPrefix,
        subsume::{Clause, Cnf, Dnf, Element, PDnf, Structure},
        weaken::{Domain, LemmaId, LemmaQf, WeakenLemmaSet},
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
}

struct LemmaManager<I: Hash + Eq + Copy, E: Element> {
    /// The lemmas in the frame, mapped from their ID's, with some syntactic reduction.
    lemmas: Vec<(Arc<QuantifierPrefix>, E, LemmaId)>,
    /// The set of lemmas inductively implied by the frame, mapped to the unsat-cores implying them.
    blocked_to_core: HashMap<I, Blocked<I>>,
    /// Mapping from each lemma to the lemmas whose inductiveness proof they paricipate in.
    core_to_blocked: HashMap<I, HashSet<I>>,
    /// A subset of the frame's lemmas which inductively implies the safety assertions.
    safety_core: Option<Blocked<I>>,
}

impl<I: Hash + Eq + Copy, E: Element> LemmaManager<I, E> {
    fn new(lemmas: Vec<(Arc<QuantifierPrefix>, E, LemmaId)>) -> Self {
        Self {
            lemmas,
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

    fn retain<F: Fn(&I) -> bool + Copy>(&mut self, f: F) {
        if self
            .safety_core
            .as_ref()
            .is_some_and(|core| !core.constituents().iter().all(f))
        {
            self.safety_core = None;
        }
        for id in &self
            .blocked_to_core
            .keys()
            .filter(|id| !f(id))
            .copied()
            .collect_vec()
        {
            self.remove_from_blocked(id);
        }
        for id in &self
            .core_to_blocked
            .keys()
            .filter(|id| !f(id))
            .copied()
            .collect_vec()
        {
            self.remove_from_cores(id);
        }
    }
}

/// A [`InductionFrame`] maintains quantified formulas during invariant inference.
pub struct InductionFrame<'a, E, L>
where
    E: Element,
    L: LemmaQf<Body = E>,
{
    /// Manages lemmas inductively proven by the frame.
    lemmas: RwLock<LemmaManager<LemmaId, E>>,
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
        let lemmas = weaken_lemmas.as_iter().collect_vec();

        InductionFrame {
            lemmas: RwLock::new(LemmaManager::new(lemmas)),
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
        for (i, (t, id)) in self.weaken_lemmas.to_terms_ids().enumerate() {
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
        let lemmas = self.lemmas.read().unwrap();
        lemmas.safety_core.as_ref()?;

        let mut extended_core: HashSet<LemmaId> = HashSet::default();
        let mut new_ids: HashSet<LemmaId> = lemmas.safety_core.as_ref().unwrap().constituents();

        while !new_ids.is_empty() {
            let mut new_new_ids = HashSet::default();
            for lemma in &new_ids {
                if let Some(blocking_lemmas) = lemmas.blocked_to_core.get(lemma) {
                    new_new_ids.extend(blocking_lemmas.constituents());
                }
            }

            extended_core.extend(new_ids);
            new_ids = new_new_ids
                .into_iter()
                .filter(|lemma| !extended_core.contains(lemma))
                .collect();
        }

        let indices = self
            .weaken_lemmas
            .as_iter()
            .enumerate()
            .filter_map(|(i, (_, _, id))| {
                if extended_core.contains(&id) {
                    Some(i)
                } else {
                    None
                }
            })
            .collect_vec();
        let core = extended_core
            .into_iter()
            .filter(|id| lemmas.inductively_proven(id))
            .map(|id| self.weaken_lemmas.id_to_term(&id))
            .collect_vec();

        self.log_info(format!("Safety lemmas at indices {indices:?}"));

        Some(core)
    }

    /// Add details about the frame to the given [`Display`].
    pub fn add_details<D: Display>(&self, d: D) -> String {
        format!(
            "[{:.2}s] [{}] {}",
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
        let mut lemmas = {
            self.lemmas
                .read()
                .unwrap()
                .lemmas
                .iter()
                .cloned()
                .enumerate()
                .collect()
        };
        let results = PriorityWorker::run(
            &mut lemmas,
            |_, (prefix, body, id)| {
                {
                    let blocked = self.lemmas.read().unwrap();
                    if blocked.blocked_to_core.contains_key(id) {
                        return (None, vec![], false);
                    }
                }

                let term = prefix.quantify(&self.signature, body.to_term(true));
                return (fo.init_cex(solver, &term), vec![], false);
            },
            paralllelism(),
        );

        let mut ctis = vec![];
        let mut manager = self.lemmas.write().unwrap();
        for ((_, _, id), out) in results {
            match out {
                Some(model) => ctis.push(model),
                None => {
                    manager.blocked_to_core.insert(id, Blocked::Initial);
                }
            }
        }

        self.log_info(format!("{} initial CTI(s) found.", ctis.len()));

        ctis
    }

    /// Weaken the lemmas in the frame.
    pub fn weaken(&mut self, model: &Model) -> bool {
        if self.weaken_lemmas.weaken(model) {
            self.log_info("Weakened.");
            true
        } else {
            false
        }
    }

    pub fn remove_unsat(&mut self, model: &Model) {
        self.weaken_lemmas.remove_unsat(model)
    }

    /// Extend simulations of traces in order to find a CTI for the current frame.
    pub fn extend<C: BasicSolverCanceler>(
        &self,
        canceler: C,
        samples: &mut PriorityTasks<SamplePriority, Model>,
    ) -> Vec<Model> {
        if samples.len() == 0 {
            return vec![];
        }
        self.log_info("Simulating CTI traces...");
        // Maps models to whether they violate the current frame, and extends them using the simulator.
        let results = PriorityWorker::run(
            samples,
            |(_, t_depth, mut since_weaken), model| {
                let unsat = self.weaken_lemmas.unsat(model);
                if unsat {
                    since_weaken = 0;
                }
                let cancel = canceler.is_canceled();

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

                (unsat, new_samples, unsat || cancel)
            },
            paralllelism(),
        );

        let counterexamples = results
            .into_iter()
            .filter(|(_, unsat)| *unsat)
            .map(|(m, _)| m)
            .collect_vec();

        if !counterexamples.is_empty() {
            canceler.cancel();
        }

        counterexamples
    }

    /// Make sure that all lemmas overapproximate initial states and remove the corresponding proofs.
    pub fn finish_initial(&self) {
        let mut manager = self.lemmas.write().unwrap();
        for (_, _, id) in &manager.lemmas {
            assert_eq!(manager.blocked_to_core.get(id), Some(&Blocked::Initial));
        }
        manager.blocked_to_core = HashMap::default();
        manager.core_to_blocked = HashMap::default();
    }

    /// Get an post-state of the frame which violates one of the frame's lemmas.
    pub fn trans_cex<S: BasicSolver>(
        &self,
        fo: &FOModule,
        solver: &S,
        cancelers: SolverCancelers<SolverCancelers<S::Canceler>>,
    ) -> Vec<Model> {
        self.log_info("Finding transition CTI...");
        let lemma_ids;
        let lemma_terms;
        let tasks;
        {
            let manager = self.lemmas.read().unwrap();
            lemma_ids = manager.lemmas.iter().map(|(_, _, id)| *id).collect_vec();
            lemma_terms = manager
                .lemmas
                .iter()
                .map(|(_, _, id)| self.weaken_lemmas.id_to_term(id))
                .collect_vec();
            tasks = if self.property_directed {
                Vec::from_iter(manager.safety_core.as_ref().unwrap().constituents())
            } else {
                lemma_ids.clone()
            };
        }
        let id_to_idx: HashMap<LemmaId, usize> = lemma_ids
            .iter()
            .enumerate()
            .map(|(idx, id)| (*id, idx))
            .collect();

        let first_sat = Mutex::new(None);
        let start_time = Instant::now();
        // The tasks here are lemmas ID's, and each result is an Option<CexResult>.
        let results = PriorityWorker::run(
            &mut tasks.into_iter().map(|id| (id_to_idx[&id], id)).collect(),
            |idx, lemma_id| {
                {
                    let blocked = self.lemmas.read().unwrap();
                    if let Some(core) = blocked.blocked_to_core.get(lemma_id) {
                        return (
                            None,
                            core.constituents()
                                .into_iter()
                                .map(|id| (id_to_idx[&id], id))
                                .collect(),
                            false,
                        );
                    }
                }

                let term = self.weaken_lemmas.id_to_term(lemma_id);
                // Check if the lemma is implied by the lemmas preceding it.
                // If property directed is enabled this will never happen since we only try to violate
                // lemmas in UNSAT-cores.
                if !self.property_directed {
                    let query_start = Instant::now();
                    let res = fo.implication_cex(
                        solver,
                        &lemma_terms[..*idx],
                        &term,
                        Some(cancelers.clone()),
                        false,
                    );
                    if let CexResult::UnsatCore(core) = &res {
                        log::info!(
                            "{:>8}ms. ({idx}) Implication found UNSAT with {} formulas in core",
                            query_start.elapsed().as_millis(),
                            core.len(),
                        );
                        let core =
                            Blocked::Consequence(core.iter().map(|i| lemma_ids[*i]).collect());
                        {
                            let mut manager = self.lemmas.write().unwrap();
                            manager.add_blocked(*lemma_id, core);
                        }
                        return (Some(res), vec![], false);
                    }
                }

                // Check if the lemma is inductively implied by the entire frame.
                let pre_ids = [&[*lemma_id], &lemma_ids[..*idx], &lemma_ids[(idx + 1)..]].concat();
                let pre_terms = [
                    &[term.clone()],
                    &lemma_terms[..*idx],
                    &lemma_terms[(idx + 1)..],
                ]
                .concat();
                let query_start = Instant::now();
                let res = fo.trans_cex(
                    solver,
                    &pre_terms,
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
                        let core = Blocked::Transition(core.iter().map(|i| pre_ids[*i]).collect());
                        let new_tasks = core
                            .constituents()
                            .into_iter()
                            .map(|id| (id_to_idx[&id], id))
                            .collect();
                        {
                            let mut manager = self.lemmas.write().unwrap();
                            manager.add_blocked(*lemma_id, core);
                        }
                        (Some(res), new_tasks, false)
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
        );

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
        let (terms, ids): (Vec<Term>, Vec<LemmaId>) = manager
            .lemmas
            .iter()
            .map(|(prefix, body, id)| (prefix.quantify(&self.signature, body.to_term(true)), *id))
            .unzip();
        if let CexResult::UnsatCore(core) = fo.safe_implication_cex(solver, &terms) {
            log::info!(
                "{:>8}ms. Safety implied with {} formulas in core",
                start_time.elapsed().as_millis(),
                core.len()
            );
            manager.safety_core = Some(Blocked::Consequence(
                core.into_iter().map(|i| ids[i]).collect(),
            ));
            return true;
        }

        match fo.trans_safe_cex(solver, &terms) {
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
                manager.safety_core = Some(Blocked::Transition(
                    core.into_iter().map(|i| ids[i]).collect(),
                ));
                true
            }
            _ => panic!("safety check failed"),
        }
    }

    pub fn update(&self) {
        self.log_info("Updating frame...");
        let mut manager = self.lemmas.write().unwrap();
        manager.lemmas = self.weaken_lemmas.as_iter().collect_vec();
        manager.retain(|id| self.weaken_lemmas.contains_id(id));
        self.log_info(format!("Updated ({}).", manager.lemmas.len()));
    }

    pub fn initial_samples(&mut self) -> PriorityTasks<SamplePriority, Model> {
        let max_model_size = defaults::MAX_MODEL_SIZE;
        let universe_sizes = (0..self.signature.sorts.len())
            .map(|_| 1..=self.sim_options.max_size.unwrap_or(max_model_size))
            .multi_cartesian_product_fixed()
            .filter(|u| u.iter().copied().sum::<usize>() <= max_model_size)
            .sorted_by_key(|u| u.iter().copied().sorted().collect_vec());

        let mut samples = PriorityTasks::new();
        for universe in universe_sizes {
            for model in self.simulator.initials_new(&universe) {
                self.weaken(&model);
                samples.insert(
                    self.sim_options
                        .sample_priority(&model.universe, 0, 0)
                        .unwrap(),
                    model,
                )
            }
        }

        samples
    }
}

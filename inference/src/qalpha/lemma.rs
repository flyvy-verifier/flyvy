// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Implement simple components, lemma domains and data structures for use in inference.

use itertools::Itertools;
use solver::basics::{BasicSolver, BasicSolverCanceler, SolverCancelers};
use std::collections::VecDeque;
use std::fmt::{Debug, Display};
use std::sync::{Arc, Mutex, RwLock};
use std::time::Instant;

use fly::semantics::Model;
use fly::syntax::{Signature, Term};

use crate::{
    basics::{CexResult, FOModule, InferenceConfig},
    hashmap::{HashMap, HashSet},
    parallel::DequeWorker,
    qalpha::{
        atoms::Literals,
        quant::QuantifierPrefix,
        subsume::{Clause, Cnf, Dnf, Element, PDnf, Structure},
        transform::into_equivalent_clause,
        weaken::{Domain, LemmaQf, LemmaSet, WeakenLemmaSet},
    },
};

/// The minimal number of disjuncts a lemma is allowed to have.
/// This corresponds to number of cubes in DNF, or the clause size in CNF.
const MIN_DISJUNCTS: usize = 3;

type Lemma<E> = (Arc<QuantifierPrefix>, E);

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
        cfg: &InferenceConfig,
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
        cfg: &InferenceConfig,
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
        cfg: &InferenceConfig,
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

/// A [`InductionFrame`] maintains quantified formulas during invariant inference.
pub struct InductionFrame<E, L>
where
    E: Element,
    L: LemmaQf<Body = E>,
{
    /// The signature of the frame's lemmas.
    signature: Arc<Signature>,
    /// The set of lemmas in the frame.
    lemmas: LemmaSet<E>,
    /// The lemmas in the frame, maintained in a way that supports weakening them.
    weaken_lemmas: WeakenLemmaSet<E, L>,
    /// The set of lemmas inductively implied by the current frame, mapped to the unsat-cores implying them.
    blocked_to_core: HashMap<usize, HashSet<usize>>,
    /// Mapping from each lemma to the lemmas whose inductiveness proof they paricipate in.
    core_to_blocked: HashMap<usize, HashSet<usize>>,
    /// Lemmas which are proven inductively, and are therefore necessary.
    /// This is in contrast to lemmas proved via implication, which are redundant.
    necessary: HashSet<usize>,
    /// Whether to extend CTI traces, and how much.
    extend: Option<(usize, usize)>,
    /// A set of CTI's to extend.
    ctis: VecDeque<Model>,
    /// A subset of the frame's lemmas which inductively implies the safety assertions.
    safety_core: Option<HashSet<usize>>,
    /// The time of creation of the frame (for logging purposes)
    start_time: Instant,
    /// Whether the search for the invariant is property-directed
    property_directed: bool,
}

impl<E, L> InductionFrame<E, L>
where
    E: Element,
    L: LemmaQf<Body = E>,
{
    /// Create a new frame from the given set of lemmas.
    pub fn new(
        infer_cfg: Arc<InferenceConfig>,
        signature: Arc<Signature>,
        domains: Vec<Domain<L>>,
        extend: Option<(usize, usize)>,
        property_directed: bool,
    ) -> Self {
        let config = Arc::new(infer_cfg.cfg.clone());
        let mut weaken_lemmas = WeakenLemmaSet::new(domains);
        weaken_lemmas.init();
        let mut lemmas = LemmaSet::new(signature.clone(), config);
        lemmas.init();

        InductionFrame {
            signature,
            lemmas,
            weaken_lemmas,
            blocked_to_core: HashMap::default(),
            core_to_blocked: HashMap::default(),
            necessary: HashSet::default(),
            extend,
            ctis: VecDeque::new(),
            safety_core: None,
            start_time: Instant::now(),
            property_directed,
        }
    }

    /// Get the length of the frame.
    pub fn len(&self) -> usize {
        self.lemmas.len()
    }

    /// Get the number of lemmas in the weaken-supporting representation.
    pub fn weaken_len(&self) -> usize {
        self.weaken_lemmas.len()
    }

    /// Get the term representation of the lemmas in the frame.
    pub fn proof(&self) -> Vec<Term> {
        self.lemmas.to_terms()
    }

    /// Get a reduced (but equivalent) fixpoint representations.
    pub fn reduced_proof(&self) -> Option<Vec<Term>> {
        let mut reduced_proof = vec![];
        let mut indices = vec![];
        for (i, (id, t)) in self.lemmas.to_terms_ids().enumerate() {
            // Not inductive
            if !self.blocked_to_core.contains_key(&id) {
                return None;
            }
            // Necessary
            if self.necessary.contains(&id) {
                reduced_proof.push(t);
                indices.push(i);
            }
        }

        self.log_info(format!("Reduced lemmas at indices {:?}", indices));

        Some(reduced_proof)
    }

    /// Get a minimized inductive set of lemmas in the frame which inductively implies safety,
    /// provided that `is_safe` has been called and returned `true`.
    pub fn safety_proof(&self) -> Option<Vec<Term>> {
        self.safety_core.as_ref()?;

        let mut extended_core: HashSet<usize> = HashSet::default();
        let mut new_ids: HashSet<usize> = self.safety_core.as_ref().unwrap().clone();

        while !new_ids.is_empty() {
            let mut new_new_ids = HashSet::default();
            for lemma in &new_ids {
                if let Some(blocking_lemmas) = self.blocked_to_core.get(lemma) {
                    new_new_ids.extend(blocking_lemmas.iter().cloned());
                }
            }

            extended_core.extend(new_ids);
            new_ids = new_new_ids
                .into_iter()
                .filter(|lemma| !extended_core.contains(lemma))
                .collect();
        }

        let indices = self
            .lemmas
            .as_iter()
            .enumerate()
            .filter_map(|(i, (_, id))| {
                if extended_core.contains(&id) {
                    Some(i)
                } else {
                    None
                }
            })
            .collect_vec();
        let core = extended_core
            .into_iter()
            .filter(|id| self.necessary.contains(id))
            .map(|id| {
                let (prefix, body) = self.lemmas.id_to_lemma(&id);
                prefix.quantify(&self.signature, body.to_term(true))
            })
            .collect_vec();

        self.log_info(format!("Safety lemmas at indices {:?}", indices));

        Some(core)
    }

    /// Add details about the frame to the given [`Display`].
    pub fn add_details<D: Display>(&self, d: D) -> String {
        format!(
            "[{:.2}s] [{} | {}] {}",
            self.start_time.elapsed().as_secs_f64(),
            self.len(),
            self.weaken_len(),
            d,
        )
    }

    /// Log at `info` level along with details about the frame.
    pub fn log_info<D: Display>(&self, d: D) {
        log::info!("{}", self.add_details(d));
    }

    /// Get an initial state which violates one of the frame's lemmas.
    fn init_cex<S: BasicSolver>(&mut self, fo: &FOModule, solver: &S) -> Vec<Model> {
        let results = DequeWorker::run(self.lemmas.as_iter(), |((prefix, body), id)| {
            if self.blocked_to_core.contains_key(id) {
                return (None, vec![], vec![], false);
            }

            let term = prefix.quantify(&self.signature, body.to_term(true));
            return (fo.init_cex(solver, &term), vec![], vec![], false);
        });

        let mut ctis = vec![];
        for ((_, id), out) in results {
            match out {
                Some(Some(model)) => ctis.push(model),
                Some(None) => {
                    self.blocked_to_core.insert(id, HashSet::default());
                }
                _ => (),
            }
        }

        ctis
    }

    /// Perform an initiation cycle, which attempts to sample an initial state
    /// violating the frame and weaken it. Return whether such a counterexample was found.
    ///
    /// Note: only when no initial counterexamples are found, the frame is updated.
    pub fn init_cycle<S: BasicSolver>(&mut self, fo: &FOModule, solver: &S) -> bool {
        self.log_info("Finding CTI...");

        let ctis = self.init_cex(fo, solver);
        if ctis.is_empty() {
            self.log_info("No initial CTI found");
            false
        } else {
            self.log_info(format!("{} CTI found, type=initial", ctis.len()));
            self.log_info("Weakening...");
            for cti in &ctis {
                self.weaken_lemmas.weaken(cti);
            }
            self.ctis.extend(ctis);
            self.log_info("Updating frame...");
            self.update();
            true
        }
    }

    /// Extend CTI traces and weaken the given lemmas accordingly,
    /// until no more states can be sampled.
    pub fn extend<S: BasicSolver>(&mut self, fo: &FOModule, solver: &S) {
        self.log_info("Simulating CTI traces...");
        let (width, depth) = self.extend.unwrap();
        let sample_count;
        let weakened;
        {
            let weaken_lemmas = RwLock::new((&mut self.weaken_lemmas, false));
            sample_count = DequeWorker::run(
                self.ctis.drain(..).map(|state| (state, depth)),
                |(state, more_depth)| {
                    let unsat = {
                        let wl = weaken_lemmas.read().unwrap();
                        wl.0.unsat(state)
                    };

                    let mut weakened = false;
                    if unsat {
                        let mut wl = weaken_lemmas.write().unwrap();
                        if wl.0.weaken(state) {
                            log::info!("[{}] Weakened", wl.0.len());
                            wl.1 = true;
                            weakened = true;
                        }
                    }

                    let new_depth = if weakened { depth } else { *more_depth };

                    let samples = if new_depth > 0 {
                        let sim = fo
                            .simulate_from(solver, state, width)
                            .into_iter()
                            .map(|sample| (sample, new_depth - 1))
                            .collect_vec();
                        log::debug!("Found {} simulated samples from CTI.", sim.len());
                        sim
                    } else {
                        vec![]
                    };

                    ((), vec![], samples, false)
                },
            )
            .len();
            weakened = weaken_lemmas.into_inner().unwrap().1;
        }

        self.log_info(format!("Sampled {sample_count} states using simulations."));

        if weakened {
            self.log_info("Updating frame...");
            self.update();
        }
    }

    /// Clear the blocked caching which maintains lemmas that have been shown to be valid.
    /// This is used whenever the notion of "validity" change, for example when transitioning from
    /// initial state counterexamples to transition counterexamples.
    pub fn clear_blocked(&mut self) {
        self.blocked_to_core = HashMap::default();
        self.core_to_blocked = HashMap::default();
    }

    /// Get an post-state of the frame which violates one of the frame's lemmas.
    fn trans_cex<S: BasicSolver>(&mut self, fo: &FOModule, solver: &S) -> Vec<Model> {
        let lemmas = self.lemmas.as_vec();
        let lemma_ids = lemmas.iter().map(|(_, id)| *id).collect_vec();
        let lemma_terms = lemmas
            .iter()
            .map(|((prefix, body), _)| prefix.quantify(&self.signature, body.to_term(true)))
            .collect_vec();
        let id_to_idx: HashMap<usize, usize> = lemma_ids
            .iter()
            .enumerate()
            .map(|(idx, id)| (*id, idx))
            .collect();

        let cancelers = SolverCancelers::new();
        let first_sat = Mutex::new(None);
        let start_time = Instant::now();
        let tasks = if self.property_directed {
            if self.safety_core.is_none() && !self.is_safe(fo, solver) {
                return vec![];
            }
            self.safety_core.as_ref().unwrap().iter().copied().collect()
        } else {
            lemma_ids.clone()
        };
        // The tasks here are lemmas ID's, and each result is an Option<CexResult> together with a bool
        // which specifies whether the result if of a transitions query (true) or an implication query (false).
        let results = DequeWorker::run(tasks, |lemma_id| {
            if let Some(core) = self.blocked_to_core.get(lemma_id) {
                return (None, core.iter().copied().collect(), vec![], false);
            }

            let idx: usize = id_to_idx[lemma_id];
            let (prefix, body) = &lemmas[idx].0;

            let term = prefix.quantify(&self.signature, body.to_term(true));
            // Check if the lemma is implied by the lemmas preceding it.
            // If property directed is enabled this will never happen since we only try to violate
            // lemmas in UNSAT-cores.
            if !self.property_directed {
                let query_start = Instant::now();
                if let CexResult::UnsatCore(core) = fo.implication_cex(
                    solver,
                    &lemma_terms[..idx],
                    &term,
                    Some(cancelers.clone()),
                    false,
                ) {
                    log::info!(
                        "{:>8}ms. ({idx}) Implication found UNSAT with {} formulas in core",
                        query_start.elapsed().as_millis(),
                        core.len(),
                    );
                    let id_core = core.into_iter().map(|i| lemma_ids[i]).collect();
                    return (
                        Some((CexResult::UnsatCore(id_core), false)),
                        vec![],
                        vec![],
                        false,
                    );
                }
            }

            // Check if the lemma is inductively implied by the entire frame.
            let pre_ids = [&[*lemma_id], &lemma_ids[..idx], &lemma_ids[(idx + 1)..]].concat();
            let pre_terms = [
                &[term.clone()],
                &lemma_terms[..idx],
                &lemma_terms[(idx + 1)..],
            ]
            .concat();
            let query_start = Instant::now();
            match fo.trans_cex(
                solver,
                &pre_terms,
                &term,
                false,
                Some(cancelers.clone()),
                false,
            ) {
                CexResult::Cex(models) => {
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
                    (Some((CexResult::Cex(models), true)), vec![], vec![], true)
                }
                CexResult::UnsatCore(core) => {
                    log::info!(
                        "{:>8}ms. ({idx}) Transition found UNSAT with {} formulas in core",
                        start_time.elapsed().as_millis(),
                        core.len()
                    );
                    let id_core_vec = core.into_iter().map(|i| pre_ids[i]).collect_vec();
                    let id_core = id_core_vec.iter().copied().collect();
                    (
                        Some((CexResult::UnsatCore(id_core), true)),
                        id_core_vec,
                        vec![],
                        false,
                    )
                }
                CexResult::Canceled => (Some((CexResult::Canceled, true)), vec![], vec![], false),
                CexResult::Unknown(reason) => {
                    log::info!(
                        "{:>8}ms. ({idx}) Transition found unknown",
                        query_start.elapsed().as_millis()
                    );
                    (
                        Some((CexResult::Unknown(reason), true)),
                        vec![],
                        vec![],
                        false,
                    )
                }
            }
        });

        let mut ctis = vec![];
        let mut total_sat = 0_usize;
        let mut total_unsat = 0_usize;
        let mut unknown = false;
        for (id, out) in results {
            match out {
                Some(Some((CexResult::Cex(mut models), _))) => {
                    total_sat += 1;
                    ctis.push(models.pop().unwrap());
                }
                Some(Some((CexResult::UnsatCore(core), transition))) => {
                    total_unsat += 1;
                    for core_id in &core {
                        if let Some(hs) = self.core_to_blocked.get_mut(core_id) {
                            hs.insert(id);
                        } else {
                            self.core_to_blocked
                                .insert(*core_id, HashSet::from_iter([id]));
                        }
                    }
                    self.blocked_to_core.insert(id, HashSet::from_iter(core));
                    if transition {
                        self.necessary.insert(id);
                    }
                }
                Some(Some((CexResult::Unknown(_), _))) => {
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

        ctis
    }

    /// Perform a transition cycle, which attempts to sample a transition from the frame
    /// whose post-state violates the frame, and weaken it. Return whether such a counterexample was found.
    pub fn trans_cycle<S: BasicSolver>(&mut self, fo: &FOModule, solver: &S) -> bool {
        self.log_info("Finding CTI...");
        let ctis = self.trans_cex(fo, solver);
        if ctis.is_empty() {
            self.log_info("No transition CTI found");

            false
        } else {
            self.log_info(format!("{} CTI found, type=transition", ctis.len()));
            self.log_info("Weakening...");
            for cti in &ctis {
                self.weaken_lemmas.weaken(cti);
            }
            self.ctis.extend(ctis);
            self.log_info("Updating frame...");
            self.update();

            true
        }
    }

    /// Return whether the current frame inductively implies the safety assertions
    /// of the given module.
    pub fn is_safe<S: BasicSolver>(&mut self, fo: &FOModule, solver: &S) -> bool {
        if self.safety_core.is_some() {
            return true;
        }

        let start_time = Instant::now();
        let (ids, terms): (Vec<usize>, Vec<Term>) = self.lemmas.to_terms_ids().unzip();
        if let CexResult::UnsatCore(core) = fo.safe_implication_cex(solver, &terms) {
            log::info!(
                "{:>8}ms. Safety implied with {} formulas in core",
                start_time.elapsed().as_millis(),
                core.len()
            );
            self.safety_core = Some(core.into_iter().map(|i| ids[i]).collect());
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
                self.safety_core = Some(core.into_iter().map(|i| ids[i]).collect());
                true
            }
            _ => panic!("safety check failed"),
        }
    }

    fn remove_lemma(&mut self, id: &usize) {
        // Remove the lemma from the frame.
        self.lemmas.remove(id);
        // Nullify the safey core if it includes this lemma.
        if self
            .safety_core
            .as_ref()
            .is_some_and(|core| core.contains(id))
        {
            self.safety_core = None;
        }
        // Remove blocking cores that contain the replaced lemma.
        if let Some(unblocked) = self.core_to_blocked.remove(id) {
            for unblocked_lemma in &unblocked {
                // Signal that the lemma isn't blocked anymore.
                // For any other frame lemma in the core, signal that it doesn't block the previously blocked lemma anymore.
                for id_in_core in &self.blocked_to_core.remove(unblocked_lemma).unwrap() {
                    if id_in_core != id {
                        let blocked_by_in_core = self.core_to_blocked.get_mut(id_in_core).unwrap();
                        blocked_by_in_core.remove(unblocked_lemma);
                        if blocked_by_in_core.is_empty() {
                            self.core_to_blocked.remove(id_in_core);
                        }
                    }
                }
            }
        }
        self.necessary.remove(id);
    }

    /// Update the frame. That is, remove each lemma in `self.lemmas` which isn't in the weakened lemmas,
    /// and add all weakenings of it (lemmas subsumed by it) to the frame. However, to keep the frame minimized,
    /// do not add lemmas that are subsumed by existing, unweakened lemmas.
    fn update(&mut self) {
        let (mut universal, mut non_universal): (HashSet<Lemma<E>>, HashSet<Lemma<E>>) = self
            .weaken_lemmas
            .as_iter()
            .partition(|(prefix, _)| prefix.existentials() == 0);
        // Ignore universal non-clauses.
        universal.retain(|(_, body)| body.to_cnf().0.len() <= 1);
        // Remove weakened universal lemmas and ignore unweakened universal lemmas.
        for (lemma, id) in self.lemmas.as_vec() {
            if lemma.0.existentials() == 0 && !universal.remove(&lemma) {
                self.remove_lemma(&id);
            }
        }
        for (prefix, body) in universal {
            self.lemmas.insert_minimized(prefix, body.clone());
        }

        // Try to substitute each formula with an equivalent clause.
        non_universal = non_universal
            .into_iter()
            .filter_map(|(prefix, body)| {
                into_equivalent_clause::<E, L>(
                    prefix,
                    body.clone(),
                    &self.lemmas.config,
                    &self.lemmas,
                )
            })
            .collect();

        // Remove weakened non-universal lemmas and ignore unweakened non-universal lemmas.
        for (lemma, id) in self.lemmas.as_vec() {
            if lemma.0.existentials() != 0 && !non_universal.remove(&lemma) {
                self.remove_lemma(&id);
            }
        }
        for (prefix, body) in non_universal {
            self.lemmas.insert_minimized(prefix, body);
        }
    }
}

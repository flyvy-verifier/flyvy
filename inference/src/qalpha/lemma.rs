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
    qalpha::{
        atoms::Literals,
        quant::QuantifierPrefix,
        subsume::{Clause, Cnf, Dnf, Element, PDnf, Structure},
        transform::into_equivalent_clause,
        weaken::{Domain, LemmaQf, LemmaSet, WeakenLemmaSet},
    },
};

use rayon::prelude::*;

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
    blocked_to_core: HashMap<Lemma<E>, HashSet<Lemma<E>>>,
    /// Mapping from each lemmas to the lemmas whose inductiveness proof they paricipate in.
    core_to_blocked: HashMap<Lemma<E>, HashSet<Lemma<E>>>,
    /// Whether to extend CTI traces, and how much.
    extend: Option<(usize, usize)>,
    /// A set of CTI's to extend.
    ctis: VecDeque<Model>,
    /// A subset of the frame's lemmas which inductively implies the safety assertions.
    safety_core: Option<HashSet<Lemma<E>>>,
    /// The time of creation of the frame (for logging purposes)
    start_time: Instant,
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
            extend,
            ctis: VecDeque::new(),
            safety_core: None,
            start_time: Instant::now(),
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

    /// Get a minimized inductive set of lemmas in the frame which inductively implies safety,
    /// provided that `is_safe` has been called and returned `true`.
    pub fn minimized_proof(&self) -> Option<Vec<Term>> {
        self.safety_core.as_ref()?;

        let mut extended_core: HashSet<Lemma<E>> = HashSet::default();
        let mut new_lemmas: HashSet<Lemma<E>> = self.safety_core.as_ref().unwrap().clone();

        while !new_lemmas.is_empty() {
            let mut new_new_lemmas = HashSet::default();
            for lemma in &new_lemmas {
                if let Some(blocking_lemmas) = self.blocked_to_core.get(lemma) {
                    new_new_lemmas.extend(blocking_lemmas.iter().cloned());
                }
            }

            extended_core.extend(new_lemmas);
            new_lemmas = new_new_lemmas
                .into_iter()
                .filter(|lemma| !extended_core.contains(lemma))
                .collect();
        }

        Some(
            extended_core
                .into_iter()
                .map(|(prefix, body)| prefix.quantify(&self.signature, body.to_term(true)))
                .collect_vec(),
        )
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
    fn init_cex<S: BasicSolver>(&mut self, fo: &FOModule, solver: &S) -> Option<Model> {
        let blocked_lock = RwLock::new((&mut self.blocked_to_core, &mut self.core_to_blocked));

        let res = self
            .lemmas
            .as_vec()
            .into_par_iter()
            .filter(|(lemma, _)| {
                let blocked_read = blocked_lock.read().unwrap();
                !blocked_read.0.contains_key(lemma)
            })
            .find_map_any(|((prefix, body), _)| {
                let term = prefix.quantify(&self.signature, body.to_term(true));
                if let Some(model) = fo.init_cex(solver, &term) {
                    return Some(model);
                } else {
                    let mut blocked_write = blocked_lock.write().unwrap();
                    blocked_write.0.insert((prefix, body), HashSet::default());
                }

                None
            });

        if self.extend.is_some() {
            self.ctis.extend(res.iter().cloned());
        }

        res
    }

    /// Perform an initiation cycle, which attempts to sample an initial state
    /// violating the frame and weaken it. Return whether such a counterexample was found.
    ///
    /// Note: only when no initial counterexamples are found, the frame is updated.
    pub fn init_cycle<S: BasicSolver>(&mut self, fo: &FOModule, solver: &S) -> bool {
        self.log_info("Finding CTI...");
        match self.init_cex(fo, solver) {
            Some(cti) => {
                self.log_info("CTI found, type=initial");
                self.log_info("Weakening...");
                self.weaken_lemmas.weaken(&cti);
                self.log_info("Updating frame...");
                self.update();

                true
            }
            None => {
                self.log_info("No initial CTI found");

                false
            }
        }
    }

    /// Extend CTI traces and weaken the given lemmas accordingly,
    /// until no more states can be sampled.
    pub fn extend<S: BasicSolver>(&mut self, fo: &FOModule, solver: &S) {
        self.log_info("Simulating CTI traces...");
        let (width, depth) = self.extend.unwrap();
        let mut weakened = false;
        while !self.ctis.is_empty() {
            let mut new_ctis = VecDeque::new();
            self.log_info(format!(
                "Extending traces from {} CTI's...",
                self.ctis.len()
            ));
            let samples: Vec<Model> = self
                .ctis
                .par_iter()
                .enumerate()
                .flat_map_iter(|(id, state)| {
                    self.log_info(format!("Extending CTI trace #{id}..."));
                    let samples = fo.simulate_from(solver, state, width, depth);
                    self.log_info(format!(
                        "Found {} simulated samples from CTI #{id}...",
                        samples.len(),
                    ));

                    samples
                })
                .collect();

            let samples_len = samples.len();
            self.log_info(format!(
                "Found a total of {samples_len} simulated samples from {} CTI's...",
                self.ctis.len(),
            ));
            let mut idx = 0;
            while let Some(i) = (idx..samples.len())
                .into_par_iter()
                .find_first(|i| self.weaken_lemmas.unsat(&samples[*i]))
            {
                assert!(self.weaken_lemmas.weaken(&samples[i]));
                weakened = true;
                self.log_info(format!("Weakened ({} / {samples_len}).", i + 1));
                new_ctis.push_back(samples[i].clone());
                idx = i + 1;
            }

            self.ctis = new_ctis;
        }

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
    fn trans_cex<S: BasicSolver>(&mut self, fo: &FOModule, solver: &S) -> Option<Model> {
        let lemmas = self.lemmas.as_vec();
        let lemma_ids = lemmas.iter().map(|(_, id)| *id).collect_vec();
        let lemma_terms = lemmas
            .iter()
            .map(|((prefix, body), _)| prefix.quantify(&self.signature, body.to_term(true)))
            .collect_vec();

        let cancelers = SolverCancelers::new();
        let unknown = Mutex::new(false);
        let first_sat = Mutex::new(None);
        let total_sat = Mutex::new(0_usize);
        let total_unsat = Mutex::new(0_usize);
        let blocked_lock = RwLock::new((&mut self.blocked_to_core, &mut self.core_to_blocked));

        let start_time = Instant::now();
        let res = lemmas
            .into_par_iter()
            .enumerate()
            .filter(|(_, (lemma, _))| {
                let blocked_read = blocked_lock.read().unwrap();
                !blocked_read.0.contains_key(lemma)
            })
            .find_map_any(|(idx, ((prefix, body), lemma_id))| {
                let handle_core = |core: std::collections::HashSet<usize>, ids: &[usize]| {
                    {
                        let mut total_unsat_lock = total_unsat.lock().unwrap();
                        *total_unsat_lock += 1;
                    }

                    {
                        let lemma = (prefix.clone(), body.clone());
                        let mut blocked_write = blocked_lock.write().unwrap();
                        let core = core
                            .into_iter()
                            .map(|i| self.lemmas.id_to_lemma(&ids[i]))
                            .collect();
                        for core_lemma in &core {
                            if let Some(hs) = blocked_write.1.get_mut::<Lemma<E>>(core_lemma) {
                                hs.insert(lemma.clone());
                            } else {
                                blocked_write.1.insert(
                                    core_lemma.clone(),
                                    HashSet::from_iter([lemma.clone()]),
                                );
                            }
                        }
                        blocked_write.0.insert(lemma, core);
                    }
                };

                let term = prefix.quantify(&self.signature, body.to_term(true));
                // Check if the lemma is implied by the lemmas preceding it.
                let implication_time = Instant::now();
                if let CexResult::UnsatCore(core) = fo.implication_cex(
                    solver,
                    &lemma_terms[..idx],
                    &term,
                    Some(cancelers.clone()),
                    false,
                ) {
                    log::info!(
                        "{:>8}ms. Implication found UNSAT with {} formulas in core",
                        implication_time.elapsed().as_millis(),
                        core.len(),
                    );

                    handle_core(core, &lemma_ids);

                    return None;
                }

                // Check if the lemma is inductively implied by the entire frame.
                let pre_ids = [&[lemma_id], &lemma_ids[..idx], &lemma_ids[(idx + 1)..]].concat();
                let pre_terms = [
                    &[term.clone()],
                    &lemma_terms[..idx],
                    &lemma_terms[(idx + 1)..],
                ]
                .concat();
                match fo.trans_cex(
                    solver,
                    &pre_terms,
                    &term,
                    false,
                    Some(cancelers.clone()),
                    false,
                ) {
                    CexResult::Cex(mut models) => {
                        cancelers.cancel();
                        {
                            let mut first_sat_lock = first_sat.lock().unwrap();
                            if first_sat_lock.is_none() {
                                *first_sat_lock = Some(Instant::now());
                            }
                        }
                        {
                            let mut total_sat_lock = total_sat.lock().unwrap();
                            *total_sat_lock += 1;
                        }

                        assert_eq!(models.len(), 2);
                        return Some(models.pop().unwrap());
                    }
                    CexResult::UnsatCore(core) => handle_core(core, &pre_ids),
                    CexResult::Canceled => (),
                    CexResult::Unknown(_) => *unknown.lock().unwrap() = true,
                }

                None
            });

        if res.is_none() && unknown.into_inner().unwrap() {
            panic!("SMT queries got 'unknown' and no SAT results.")
        }

        log::info!(
            "    SMT STATS: total_time={:.5}s, until_sat={:.5}s, sat_found={}, unsat_found={}",
            (Instant::now() - start_time).as_secs_f64(),
            (first_sat.into_inner().unwrap().unwrap_or(start_time) - start_time).as_secs_f64(),
            total_sat.into_inner().unwrap(),
            total_unsat.into_inner().unwrap(),
        );

        if self.extend.is_some() {
            self.ctis.extend(res.iter().cloned());
        }

        res
    }

    /// Perform a transition cycle, which attempts to sample a transition from the frame
    /// whose post-state violates the frame, and weaken it. Return whether such a counterexample was found.
    pub fn trans_cycle<S: BasicSolver>(&mut self, fo: &FOModule, solver: &S) -> bool {
        self.log_info("Finding CTI...");
        match self.trans_cex(fo, solver) {
            Some(cti) => {
                self.log_info("CTI found, type=transition");
                self.log_info("Weakening...");
                self.weaken_lemmas.weaken(&cti);
                self.log_info("Updating frame...");
                self.update();

                true
            }
            None => {
                self.log_info("No transition CTI found");

                false
            }
        }
    }

    /// Return whether the current frame inductively implies the safety assertions
    /// of the given module.
    pub fn is_safe<S: BasicSolver>(&mut self, fo: &FOModule, solver: &S) -> bool {
        if self.safety_core.is_some() {
            return true;
        }

        let (ids, terms): (Vec<usize>, Vec<Term>) = self.lemmas.to_terms_ids().unzip();
        match fo.trans_safe_cex(solver, &terms) {
            CexResult::Cex(_) => false,
            CexResult::UnsatCore(core) => {
                self.safety_core = Some(
                    core.into_iter()
                        .map(|i| self.lemmas.id_to_lemma(&ids[i]))
                        .collect(),
                );
                true
            }
            _ => panic!("safety check failed"),
        }
    }

    fn remove_lemma(&mut self, id: &usize) {
        // Remove the lemma from the frame.
        let lemma = self.lemmas.remove(id);
        // Nullify the safey core if it includes this lemma.
        if self
            .safety_core
            .as_ref()
            .is_some_and(|core| core.contains(&lemma))
        {
            self.safety_core = None;
        }
        // Remove blocking cores that contain the replaced lemma.
        if let Some(unblocked) = self.core_to_blocked.remove(&lemma) {
            for unblocked_lemma in &unblocked {
                // Signal that the lemma isn't blocked anymore.
                // For any other frame lemma in the core, signal that it doesn't block the previously blocked lemma anymore.
                for lemma_in_core in &self.blocked_to_core.remove(unblocked_lemma).unwrap() {
                    if lemma_in_core != &lemma {
                        let blocked_by_in_core =
                            self.core_to_blocked.get_mut(lemma_in_core).unwrap();
                        blocked_by_in_core.remove(unblocked_lemma);
                        if blocked_by_in_core.is_empty() {
                            self.core_to_blocked.remove(lemma_in_core);
                        }
                    }
                }
            }
        }
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

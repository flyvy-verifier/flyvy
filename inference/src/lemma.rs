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
use fly::syntax::Term;

use crate::subsume::{Dnf, PDnf, Structure};
use crate::{
    atoms::Literals,
    basics::{CexResult, FOModule, InferenceConfig},
    hashmap::{HashMap, HashSet},
    subsume::{Cnf, Element},
    weaken::{Domain, LemmaQf, LemmaSet, WeakenLemmaSet},
};

use rayon::prelude::*;

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
}

#[derive(Clone)]
pub struct LemmaDnf {
    cubes: usize,
    cube_size: usize,
    literals: Arc<Literals>,
}

impl Debug for LemmaDnf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("pDNF (naive)")
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
                .filter(|lit| lit.ids().is_disjoint(non_universal_vars))
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
        I: Fn(&Self::Body) -> bool,
    {
        let clause_cfg = (self.cubes, self.literals.clone());
        let dnf_cfg = (
            self.non_unit,
            (self.cube_size, self.non_universal_literals.clone()),
        );
        let res = body
            .weaken(&(clause_cfg, dnf_cfg), structure)
            .into_iter()
            .filter(|pdnf| !ignore(pdnf))
            .filter(|pdnf| {
                let base = pdnf.to_base(true);
                base.0.len() + base.1.len() <= self.cubes
            })
            .collect_vec();
        for b in &res {
            println!("{}", b.to_term(true));
        }

        res
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
        (MIN_DISJUNCTS..=self.cubes)
            .flat_map(|cubes| {
                // The case for non_unit=0, cube_size=1
                [Self {
                    cubes,
                    cube_size: 1,
                    non_unit: 0,
                    literals: self.literals.clone(),
                    non_universal_literals: self.non_universal_literals.clone(),
                }]
                .into_iter()
                // All other cases for non-unit > 0, cube_size > 1
                .chain((2..=self.cube_size).flat_map(move |cube_size| {
                    (1..=self.non_unit).map(move |non_unit| Self {
                        cubes,
                        cube_size,
                        non_unit,
                        literals: self.literals.clone(),
                        non_universal_literals: self.non_universal_literals.clone(),
                    })
                }))
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
    /// The set of lemmas in the frame.
    lemmas: LemmaSet<E, L>,
    /// The lemmas in the frame, maintained in a way that supports weakening them.
    weaken_lemmas: WeakenLemmaSet<E, L>,
    /// The set of lemmas inductively implied by the current frame. That is, any post-state of
    /// a transition from the frame satisfies `blocked`.
    blocked: LemmaSet<E, L>,
    /// A mapping between each blocked lemma and a core in the frame that blocks it.
    blocked_to_core: HashMap<usize, HashSet<usize>>,
    /// A mapping between frame lemmas and the lemmas they block.
    core_to_blocked: HashMap<usize, HashSet<usize>>,
    /// Whether to extend CTI traces, and how much.
    extend: Option<(usize, usize)>,
    /// A set of CTI's to extend.
    ctis: VecDeque<Model>,
    /// A subset of the frame's lemmas which inductively implies the safety assertions.
    safety_core: Option<HashSet<usize>>,
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
        literals: Arc<Literals>,
        domains: Vec<Domain<L>>,
        extend: Option<(usize, usize)>,
    ) -> Self {
        let mut weaken_lemmas: WeakenLemmaSet<E, L> = WeakenLemmaSet::new(
            Arc::new(infer_cfg.cfg.clone()),
            infer_cfg,
            literals,
            domains,
        );
        weaken_lemmas.init();
        let lemmas = weaken_lemmas.minimized();

        let blocked = lemmas.clone_empty();

        InductionFrame {
            lemmas,
            weaken_lemmas,
            blocked,
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

        let mut extended_core = HashSet::default();
        let mut new_ids = self.safety_core.as_ref().unwrap().clone();

        while !new_ids.is_empty() {
            let mut new_new_ids = HashSet::default();
            for id in &new_ids {
                let (prefix, body) = self.lemmas.id_to_lemma(id);
                let blocked_id = self.blocked.get_id(&prefix, body).unwrap();
                new_new_ids.extend(
                    self.blocked_to_core[&blocked_id]
                        .difference(&extended_core)
                        .copied(),
                );
            }

            extended_core.extend(new_ids);
            new_ids = new_new_ids;
        }

        Some(
            extended_core
                .into_iter()
                .map(|id| self.lemmas.id_to_term(&id))
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

    /// Log at `debug` level along with details about the frame.
    pub fn log_debug<D: Display>(&self, d: D) {
        log::debug!("{}", self.add_details(d));
    }

    /// Get an initial state which violates one of the frame's lemmas.
    fn init_cex<S: BasicSolver>(&mut self, fo: &FOModule, solver: &S) -> Option<Model> {
        let blocked_lock = RwLock::new((
            &mut self.blocked,
            &mut self.blocked_to_core,
            &mut self.core_to_blocked,
        ));

        let res = self
            .weaken_lemmas
            .as_vec()
            .into_par_iter()
            .filter(|(prefix, body)| {
                let blocked_read = blocked_lock.read().unwrap();
                !blocked_read.0.subsumes(prefix, body)
            })
            .find_map_any(|(prefix, body)| {
                let term = prefix.quantify(body.to_term(true));
                if let Some(model) = fo.init_cex(solver, &term) {
                    return Some(model);
                } else {
                    let mut blocked_write = blocked_lock.write().unwrap();
                    let core = self.lemmas.ids().collect();
                    let blocked_id = blocked_write.0.insert(prefix, body.clone());
                    for i in &core {
                        if let Some(hs) = blocked_write.2.get_mut(i) {
                            hs.insert(blocked_id);
                        } else {
                            blocked_write.2.insert(*i, HashSet::from_iter([blocked_id]));
                        }
                    }
                    blocked_write.1.insert(blocked_id, core);
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

                true
            }
            None => {
                self.log_info("No initial CTI found");
                self.log_info("Updating frame...");
                self.update();

                false
            }
        }
    }

    /// Extend CTI traces and weaken the given lemmas accordingly,
    /// until no more states can be sampled.
    pub fn extend<S: BasicSolver>(&mut self, fo: &FOModule, solver: &S) {
        self.log_info("Simulating CTI traces...");
        let (width, depth) = self.extend.unwrap();
        while !self.ctis.is_empty() {
            let mut new_ctis = VecDeque::new();
            self.log_debug(format!(
                "Extending traces from {} CTI's...",
                self.ctis.len()
            ));
            let samples: Vec<Model> = self
                .ctis
                .par_iter()
                .enumerate()
                .flat_map_iter(|(id, state)| {
                    self.log_debug(format!("Extending CTI trace #{id}..."));
                    let samples = fo.simulate_from(solver, state, width, depth);
                    self.log_debug(format!(
                        "Found {} simulated samples from CTI #{id}...",
                        samples.len(),
                    ));

                    samples
                })
                .collect();

            let samples_len = samples.len();
            self.log_debug(format!(
                "Found a total of {samples_len} simulated samples from {} CTI's...",
                self.ctis.len(),
            ));
            let mut idx = 0;
            while let Some(i) = (idx..samples.len())
                .into_par_iter()
                .find_first(|i| self.weaken_lemmas.unsat(&samples[*i]))
            {
                assert!(self.weaken_lemmas.weaken(&samples[i]));
                self.log_debug(format!("Weakened ({} / {samples_len}).", i + 1));
                new_ctis.push_back(samples[i].clone());
                idx = i + 1;
            }

            self.ctis = new_ctis;
        }

        self.log_info("Updating frame...");
        self.update();
    }

    /// Get an post-state of the frame which violates one of the frame's lemmas.
    fn trans_cex<S: BasicSolver>(&mut self, fo: &FOModule, solver: &S) -> Option<Model> {
        let (pre_ids, pre_terms): (Vec<usize>, Vec<Term>) = self.lemmas.to_terms_ids().unzip();

        let cancelers = SolverCancelers::new();
        let unknown = Mutex::new(false);
        let first_sat = Mutex::new(None);
        let total_sat = Mutex::new(0_usize);
        let total_unsat = Mutex::new(0_usize);
        let blocked_lock = RwLock::new((
            &mut self.blocked,
            &mut self.blocked_to_core,
            &mut self.core_to_blocked,
        ));

        let start_time = Instant::now();
        let res = self
            .weaken_lemmas
            .as_vec()
            .into_par_iter()
            .filter(|(prefix, body)| {
                let blocked_read = blocked_lock.read().unwrap();
                !blocked_read.0.subsumes(prefix, body)
            })
            .find_map_any(|(prefix, body)| {
                let term = prefix.quantify(body.to_term(true));
                // If a lemmas is not in `self.lemmas`, there is a stronger lemma in `self.lemmas` that subsumes it,
                // so it doesn't need to be checked.
                let lemma_id = self.lemmas.get_id(&prefix, body)?;
                let pre_ids: &[usize] = &[&[lemma_id], &pre_ids[..]].concat();
                let pre_terms: &[Term] = &[&[term.clone()], &pre_terms[..]].concat();
                match fo.trans_cex(
                    solver,
                    pre_terms,
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
                    CexResult::UnsatCore(core) => {
                        {
                            let mut total_unsat_lock = total_unsat.lock().unwrap();
                            *total_unsat_lock += 1;
                        }

                        {
                            let mut blocked_write = blocked_lock.write().unwrap();
                            let core = core.into_iter().map(|i| pre_ids[i]).collect();
                            let blocked_id = blocked_write.0.insert(prefix, body.clone());
                            for i in &core {
                                if let Some(hs) = blocked_write.2.get_mut(i) {
                                    hs.insert(blocked_id);
                                } else {
                                    blocked_write.2.insert(*i, HashSet::from_iter([blocked_id]));
                                }
                            }
                            blocked_write.1.insert(blocked_id, core);
                        }
                    }
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
            for lemma in &unblocked {
                // Signal that the lemma isn't blocked anymore.
                self.blocked.remove(lemma);
                // For any other frame lemma in the core, signal that it doesn't block the previously blocked lemma anymore.
                for in_core in &self.blocked_to_core.remove(lemma).unwrap() {
                    if in_core != id {
                        let blocked_by_in_core = self.core_to_blocked.get_mut(in_core).unwrap();
                        blocked_by_in_core.remove(lemma);
                        if blocked_by_in_core.is_empty() {
                            self.core_to_blocked.remove(in_core);
                        }
                    }
                }
            }
        }
    }

    /// Update the frame. That is, remove each lemma in `self.lemmas` which isn't in the weakened lemmas,
    /// and add all weakenings of it (lemmas subsumed by it) to the frame. However, to keep the frame minimized,
    /// do not add lemmas that are subsumed by existing, unweakened lemmas.
    ///
    /// Return whether the update caused any change in the frame.
    fn update(&mut self) -> bool {
        // If there are no lemmas in the frame, it cannot be advanced.
        if self.lemmas.is_empty() {
            return false;
        }

        // Find all lemmas in the frame (parents) which have been weakened in the new lemmas.
        // These are precisely the lemmas in the frame which are not part of the new lemmas.
        let weakened_parents: HashSet<usize> = self
            .lemmas
            .as_iter()
            .filter_map(|(prefix, body, id)| {
                if !self.weaken_lemmas.contains(&prefix, body) {
                    Some(id)
                } else {
                    None
                }
            })
            .collect();

        let advanced = !weakened_parents.is_empty();
        for id in &weakened_parents {
            self.remove_lemma(id)
        }

        let new_lemmas = Mutex::new(self.lemmas.clone_empty());
        self.weaken_lemmas
            .as_vec()
            .into_par_iter()
            .for_each(|(prefix, body)| {
                if !self.lemmas.subsumes(prefix.as_ref(), body) {
                    let mut new_lemmas_lock = new_lemmas.lock().unwrap();
                    new_lemmas_lock.insert_minimized(prefix, body.clone());
                }
            });

        for (prefix, body, _) in new_lemmas.into_inner().unwrap().as_iter() {
            self.lemmas.insert(prefix, body.clone());
        }

        advanced
    }
}

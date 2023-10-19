// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use itertools;
use itertools::Itertools;
use std::{
    collections::{HashMap, HashSet},
    sync::{Arc, Mutex},
    thread,
};

use crate::qalpha::quant::QuantifierConfig;
use fly::syntax::BinOp;
use fly::syntax::Term::*;
use fly::syntax::*;
use fly::term::{prime::clear_next, prime::Next};
use fly::{ouritertools::OurItertools, semantics::Model, transitions::*};
use smtlib::proc::{SatResp, SolverError};
use solver::{
    basics::{BasicSolver, BasicSolverCanceler, BasicSolverResp, QueryConf, SolverCancelers},
    conf::SolverConf,
};

pub enum CexResult {
    Cex(Vec<Model>),
    UnsatCore(HashSet<usize>),
    Canceled,
    Unknown(String),
}

impl CexResult {
    /// Convert into an [`Option`], which either contains a counterexample or [`None`].
    pub fn into_option(self) -> Option<Vec<Model>> {
        match self {
            CexResult::Cex(models) => Some(models),
            CexResult::UnsatCore(_) => None,
            _ => panic!("cex result is neither sat or unsat"),
        }
    }

    /// Return `true` if the [`CexResult`] contains a counterexample, or `false` if it contains an UNSAT-core.
    /// If the query is either `Canceled` or `Unknown`, this panics.
    pub fn is_cex(&self) -> bool {
        match self {
            CexResult::Cex(_) => true,
            CexResult::UnsatCore(_) => false,
            _ => panic!("cex result is neither sat or unsat"),
        }
    }
}

/// Manages a subset of formulas based on the counter-models they do not satisfy.
///
/// This is used to find a small UNSAT-core of some SMT query by iteratively adding negative
/// counterexamples to be blocked and growing the core in a minimal way to block all of them.
/// If `minimal` is set, the core is guaranteed to be minimal in the local sense that
/// no formula can be dropped from it while still blocking all the previous counterexamples.
struct Core<'a> {
    formulas: &'a [Term],
    participants: HashSet<usize>,
    counter_models: Vec<Model>,
    to_participants: HashMap<usize, HashSet<usize>>,
    to_counter_models: HashMap<usize, HashSet<usize>>,
    minimal: bool,
}

impl<'a> Core<'a> {
    /// Create a new core from the given formulas. `participants` specifies which formulas
    /// to intialize the core with, and `minimal` determines whether to minimize the core
    /// when adding future participants.
    fn new(formulas: &'a [Term], participants: HashSet<usize>, minimal: bool) -> Self {
        Core {
            formulas,
            participants,
            counter_models: vec![],
            to_participants: HashMap::new(),
            to_counter_models: HashMap::new(),
            minimal,
        }
    }

    /// Update the core so that it blocks the given model and all previously blocked models.
    /// This involves adding a blocking formula to the core and potentially minimizing it.
    /// We assume that the new model satisfies the current core (i.e. is not blocked by it).
    ///
    /// Returns `true` if the model has been successfully blocked or `false` if it couldn't be
    /// blocked because it satisfied all candidate formulas.
    fn add_counter_model(&mut self, counter_model: Model) -> bool {
        // We assume that the new counter-model satisfies all previous formulas.
        for &p_idx in &self.participants {
            assert_eq!(counter_model.eval(&self.formulas[p_idx]), 1);
        }

        let new_participant = self.formulas.iter().enumerate().find(|(i, formula)| {
            !self.participants.contains(i) && counter_model.eval(formula) == 0
        });

        match new_participant {
            Some((p_idx, _)) => {
                let model_idx = self.counter_models.len();
                self.participants.insert(p_idx);
                self.to_participants.insert(model_idx, HashSet::new());
                let mut counter_models: HashSet<usize> = (0..self.counter_models.len())
                    .filter(|i| self.counter_models[*i].eval(&self.formulas[p_idx]) == 0)
                    .collect();
                counter_models.insert(model_idx);
                self.counter_models.push(counter_model);
                for m_idx in &counter_models {
                    self.to_participants.get_mut(m_idx).unwrap().insert(p_idx);
                }
                self.to_counter_models.insert(p_idx, counter_models);

                if self.minimal {
                    while self.reduce() {}

                    assert!(self.participants.iter().all(|p_idx| {
                        self.to_counter_models[p_idx]
                            .iter()
                            .any(|m_idx| self.to_participants[m_idx] == HashSet::from([*p_idx]))
                    }));
                }

                true
            }
            None => false,
        }
    }

    /// Reduces the size of the core by one if possible, by trying to find a formula such that any model it blocks
    /// is also blocked by a different formula in the core. Formulas with a higher index are prioritized for removal.
    ///
    /// Returns `true` if the core has been reduced, or `false` otherwise.
    fn reduce(&mut self) -> bool {
        if let Some(p_idx) = self
            .participants
            .iter()
            .copied()
            .sorted()
            .rev()
            .find(|p_idx| {
                self.to_counter_models[p_idx]
                    .iter()
                    .all(|m_idx| self.to_participants[m_idx].len() > 1)
            })
        {
            assert!(self.participants.remove(&p_idx));
            for m_idx in self.to_counter_models.remove(&p_idx).unwrap() {
                assert!(self.to_participants.get_mut(&m_idx).unwrap().remove(&p_idx));
            }

            true
        } else {
            false
        }
    }

    /// Convert the current core to a set of assumption for use by the solver.
    /// This yields a map which maps each participant index to its [`Term`] and Boolean assumption,
    /// in this case always `true`.
    fn to_assumptions(&self) -> HashMap<usize, (Term, bool)> {
        self.participants
            .iter()
            .map(|i| (*i, (self.formulas[*i].clone(), true)))
            .collect()
    }
}

#[derive(Debug, Clone)]
pub enum TermOrModel {
    Model(Model),
    Term(Term),
}

pub enum CexOrCore {
    Cex((Term, Model)),
    Core(HashMap<Term, bool>),
}

/// A first-order module is represented using first-order formulas,
/// namely single-vocabulary axioms, initial assertions and safety assertions,
/// and double-vocabulary transition assertions.
/// `disj` denotes whether to split the transitions disjunctively, if possible.
pub struct FOModule {
    signature: Arc<Signature>,
    pub module: DestructuredModule,
    disj: bool,
    gradual: bool,
    minimal: bool,
}

impl FOModule {
    pub fn new(m: &Module, disj: bool, gradual: bool, minimal: bool) -> Self {
        FOModule {
            signature: m.signature.clone(),
            module: extract(m).unwrap(),
            disj,
            gradual,
            minimal,
        }
    }

    fn disj_trans(&self) -> Vec<Vec<&Term>> {
        if self.disj {
            self.module
                .transitions
                .iter()
                .map(|t| match t {
                    Term::NAryOp(NOp::Or, args) => args.iter().collect_vec(),
                    _ => vec![t],
                })
                .multi_cartesian_product_fixed()
                .collect_vec()
        } else {
            vec![self.module.transitions.iter().collect_vec()]
        }
    }

    pub fn init_cex<B: BasicSolver>(&self, solver: &B, t: &Term) -> Option<Model> {
        self.implication_cex(solver, &self.module.inits, t, None, false)
            .into_option()
            .map(|mut models| {
                assert_eq!(models.len(), 1);
                models.pop().unwrap()
            })
    }

    pub fn trans_cex<B, C>(
        &self,
        solver: &B,
        hyp: &[Term],
        t: &Term,
        with_safety: bool,
        cancelers: Option<SolverCancelers<SolverCancelers<C>>>,
        save_tee: bool,
    ) -> CexResult
    where
        C: BasicSolverCanceler,
        B: BasicSolver<Canceler = C>,
    {
        let transitions = self.disj_trans();
        let local_cancelers: SolverCancelers<C> = SolverCancelers::new();

        if cancelers
            .as_ref()
            .is_some_and(|c| !c.add_canceler(local_cancelers.clone()))
        {
            return CexResult::Canceled;
        }

        let query_conf = QueryConf {
            sig: &self.signature,
            n_states: 2,
            cancelers: Some(local_cancelers.clone()),
            minimal_model: true,
            save_tee,
        };
        let next = Next::new(&self.signature);
        let mut assertions = self.module.axioms.clone();
        assertions.extend(self.module.axioms.iter().map(|a| next.prime(a)));
        if with_safety {
            assertions.extend(self.module.proofs.iter().map(|p| p.safety.x.clone()))
        }
        assertions.push(Term::not(next.prime(t)));

        let cex_results: Vec<CexResult> = thread::scope(|s| {
            transitions
                .into_iter()
                .map(|transition| {
                    s.spawn(|| {
                        let mut core: Core = if self.gradual {
                            Core::new(hyp, HashSet::new(), self.minimal)
                        } else {
                            Core::new(hyp, (0..hyp.len()).collect(), self.minimal)
                        };

                        let mut local_assertions = assertions.clone();
                        local_assertions.extend(transition.into_iter().cloned());
                        loop {
                            let assumptions = core.to_assumptions();
                            match solver.check_sat(&query_conf, &local_assertions, &assumptions) {
                                Ok(BasicSolverResp::Sat(models)) => {
                                    if !core.add_counter_model(models[0].clone()) {
                                        // A counter-example to the transition was found, no need to search further.
                                        local_cancelers.cancel();
                                        return CexResult::Cex(models);
                                    }
                                }
                                Ok(BasicSolverResp::Unsat(core)) => {
                                    return CexResult::UnsatCore(core)
                                }
                                Ok(BasicSolverResp::Unknown(reason)) => {
                                    return CexResult::Unknown(reason)
                                }
                                Err(SolverError::Killed) => return CexResult::Canceled,
                                Err(e) => panic!("error in solver: {e}"),
                            }
                        }
                    })
                })
                .collect_vec()
                .into_iter()
                .map(|h| h.join().unwrap())
                .collect_vec()
        });

        // Check whether any counterexample has been found
        if cex_results
            .iter()
            .any(|res| matches!(res, CexResult::Cex(_)))
        {
            return cex_results
                .into_iter()
                .find(|res| matches!(res, CexResult::Cex(_)))
                .unwrap();
        }

        // Check whether any query has been canceled
        if cex_results
            .iter()
            .any(|res| matches!(res, CexResult::Canceled))
        {
            return CexResult::Canceled;
        }

        // Check whether any query has returned 'unknown'
        if cex_results
            .iter()
            .any(|res| matches!(res, CexResult::Unknown(_)))
        {
            return CexResult::Unknown(
                cex_results
                    .into_iter()
                    .filter_map(|res| match res {
                        CexResult::Unknown(reason) => Some(reason),
                        _ => None,
                    })
                    .join("\n"),
            );
        }

        // Otherwise, all results must be UNSAT-cores
        let unsat_core = cex_results
            .into_iter()
            .flat_map(|res| match res {
                CexResult::UnsatCore(core) => core,
                _ => unreachable!(),
            })
            .collect();

        CexResult::UnsatCore(unsat_core)
    }

    pub fn implication_cex<B, C>(
        &self,
        solver: &B,
        hyp: &[Term],
        t: &Term,
        cancelers: Option<SolverCancelers<SolverCancelers<C>>>,
        save_tee: bool,
    ) -> CexResult
    where
        C: BasicSolverCanceler,
        B: BasicSolver<Canceler = C>,
    {
        let local_cancelers: SolverCancelers<C> = SolverCancelers::new();
        if cancelers
            .as_ref()
            .is_some_and(|c| !c.add_canceler(local_cancelers.clone()))
        {
            return CexResult::Canceled;
        }

        let mut core: Core = if self.gradual {
            Core::new(hyp, HashSet::new(), self.minimal)
        } else {
            Core::new(hyp, (0..hyp.len()).collect(), self.minimal)
        };

        let query_conf = QueryConf {
            sig: &self.signature,
            n_states: 1,
            cancelers: Some(local_cancelers),
            minimal_model: true,
            save_tee,
        };
        let mut assertions = self.module.axioms.clone();
        assertions.push(Term::not(t));
        loop {
            match solver.check_sat(&query_conf, &assertions, &core.to_assumptions()) {
                Ok(BasicSolverResp::Sat(models)) => {
                    if !core.add_counter_model(models[0].clone()) {
                        return CexResult::Cex(models);
                    }
                }
                Ok(BasicSolverResp::Unsat(core)) => return CexResult::UnsatCore(core),
                Ok(BasicSolverResp::Unknown(reason)) => return CexResult::Unknown(reason),
                Err(SolverError::Killed) => return CexResult::Canceled,
                Err(e) => panic!("error in solver: {e}"),
            }
        }
    }

    pub fn simulate_from<B, C>(&self, solver: &B, state: &Model, width: usize) -> Vec<Model>
    where
        C: BasicSolverCanceler,
        B: BasicSolver<Canceler = C>,
    {
        let transitions = self.disj_trans();
        let cancelers = SolverCancelers::new();
        let empty_assumptions = HashMap::new();
        let next = Next::new(&self.signature);
        let query_conf = QueryConf {
            sig: &self.signature,
            n_states: 2,
            cancelers: Some(cancelers.clone()),
            minimal_model: false,
            save_tee: false,
        };

        let state_term = state.to_term();
        let samples = Mutex::new(vec![]);
        thread::scope(|s| {
            for transition in &transitions {
                s.spawn(|| {
                    let mut assertions = vec![state_term.clone()];
                    assertions.extend(self.module.axioms.iter().map(|a| next.prime(a)));
                    assertions.extend(transition.iter().copied().cloned());

                    'this_loop: loop {
                        let resp = solver.check_sat(&query_conf, &assertions, &empty_assumptions);
                        match resp {
                            Ok(BasicSolverResp::Sat(mut models)) => {
                                assert_eq!(models.len(), 2);
                                let new_sample = models.pop().unwrap();
                                assertions.push(Term::negate(next.prime(&new_sample.to_term())));
                                {
                                    let mut samples_lock = samples.lock().unwrap();
                                    if samples_lock.len() < width {
                                        samples_lock.push(new_sample);
                                    }
                                    if samples_lock.len() >= width {
                                        cancelers.cancel();
                                        break 'this_loop;
                                    }
                                }
                            }
                            _ => break 'this_loop,
                        }
                    }
                });
            }
        });

        samples.into_inner().unwrap()
    }

    pub fn get_pred(&self, conf: &SolverConf, hyp: &[Term], t: &TermOrModel) -> CexOrCore {
        let as_term: Term = match t {
            TermOrModel::Term(t) => t.clone(),
            TermOrModel::Model(m) => m.to_diagram(),
        };
        assert_eq!(self.module.transitions.len(), 1);
        if let NAryOp(NOp::Or, _) = self.module.transitions[0].clone() {
        } else {
            panic!("malformed transitions!")
        }
        let separate_trans = self
            .module
            .transitions
            .iter()
            .flat_map(|t| match t {
                NAryOp(NOp::Or, args) => args.iter().collect_vec(),
                _ => vec![t],
            })
            .collect_vec();

        let mut core = HashMap::new();
        for trans in separate_trans {
            let mut solver = conf.solver(&self.signature, 2);
            for a in self
                .module
                .axioms
                .iter()
                .chain(hyp.iter())
                .chain(vec![trans])
            {
                solver.assert(a);
            }
            for a in self.module.axioms.iter() {
                solver.assert(&Next::new(&self.signature).prime(a));
            }
            let mut indicators = HashMap::new();
            let mut ind_to_term = HashMap::new();
            let mut new_terms = vec![];
            if let TermOrModel::Term(term) = t {
                // println!("got term, asserting with no core");
                solver.assert(&Next::new(&self.signature).prime(term));
            } else if let Quantified {
                quantifier: Quantifier::Exists,
                body,
                binders,
            } = Next::new(&self.signature).prime(&as_term)
            {
                if let NAryOp(NOp::And, terms) = *body {
                    for (i, clause) in terms.into_iter().enumerate() {
                        let ind = solver.get_indicator(&i.to_string());
                        new_terms.push(Term::BinOp(
                            BinOp::Equals,
                            Box::new(ind.clone()),
                            Box::new(clause.clone()),
                        ));
                        // println!("adding clause {}", &clause);
                        indicators.insert(ind.clone(), true);
                        ind_to_term.insert(ind, clause);
                    }
                    let new_term = Quantified {
                        quantifier: Quantifier::Exists,
                        body: Box::new(NAryOp(NOp::And, new_terms)),
                        binders,
                    };
                    solver.assert(&new_term);
                } else {
                    panic!("bad term for pred!");
                }
            } else {
                panic!("bad term for pred!");
            }

            let resp = solver.check_sat(indicators).expect("error in solver");
            match resp {
                SatResp::Sat => {
                    let states = solver.get_minimal_model().expect("error in solver");
                    assert_eq!(states.len(), 2);
                    // println!("trans: {}", &trans);
                    return CexOrCore::Cex((trans.clone(), states[0].clone()));
                }
                SatResp::Unsat => {
                    // println!("adding group");
                    for (ind, b) in solver
                        .get_unsat_core()
                        .expect("could not get unsat assumptions")
                    {
                        assert!(b, "got false in core");
                        // println!("adding to core: {}", clear_next(ind_to_term[&ind].clone()));
                        core.insert(clear_next(ind_to_term[&ind].clone()), b);
                    }
                }
                SatResp::Unknown(error) => panic!("{}", error),
            }
            solver.save_tee();
        }
        return CexOrCore::Core(core);
    }

    pub fn implies_cex(&self, conf: &SolverConf, hyp: &[Term], t: &Term) -> Option<Model> {
        let mut solver = conf.solver(&self.signature, 1);
        for a in hyp {
            solver.assert(a);
        }
        solver.assert(&Term::negate(t.clone()));

        let resp = solver.check_sat(HashMap::new()).expect("error in solver");
        solver.save_tee();
        match resp {
            SatResp::Sat => {
                let states = solver.get_minimal_model().expect("error in solver");
                assert_eq!(states.len(), 1);
                return Some(states[0].clone());
            }
            SatResp::Unsat => None,
            SatResp::Unknown(_) => panic!(),
        }
    }

    pub fn safe_implication_cex<B: BasicSolver>(&self, solver: &B, hyp: &[Term]) -> CexResult {
        let mut core = HashSet::new();
        for s in self.module.proofs.iter() {
            match self.implication_cex(solver, hyp, &s.safety.x, None, false) {
                CexResult::UnsatCore(new_core) => core.extend(new_core),
                res => return res,
            }
        }

        CexResult::UnsatCore(core)
    }

    pub fn trans_safe_cex<B: BasicSolver>(&self, solver: &B, hyp: &[Term]) -> CexResult {
        let mut core = HashSet::new();
        for s in self.module.proofs.iter() {
            match self.trans_cex(solver, hyp, &s.safety.x, true, None, false) {
                CexResult::UnsatCore(new_core) => core.extend(new_core),
                res => return res,
            }
        }

        CexResult::UnsatCore(core)
    }

    pub fn safe_cex(&self, conf: &SolverConf, hyp: &[Term]) -> Option<Model> {
        for s in self.module.proofs.iter() {
            if let Some(model) = self.implies_cex(conf, hyp, &s.safety.x) {
                return Some(model);
            }
        }

        None
    }
}

pub enum QfBody {
    CNF,
    PDnf,
    Dnf,
}

pub struct InferenceConfig {
    pub fname: String,

    pub fallback: bool,
    pub cfg: QuantifierConfig,
    pub qf_body: QfBody,
    pub property_directed: bool,

    pub max_size: usize,
    pub max_existentials: Option<usize>,

    pub clauses: Option<usize>,
    pub clause_size: Option<usize>,

    pub cubes: Option<usize>,
    pub cube_size: Option<usize>,
    pub non_unit: Option<usize>,

    pub nesting: Option<usize>,
    pub include_eq: bool,

    pub disj: bool,
    pub gradual_smt: bool,
    pub minimal_smt: bool,

    pub extend_depth: Option<usize>,

    pub until_safe: bool,
    pub abort_unsafe: bool,
    pub no_search: bool,
    pub growth_factor: Option<usize>,
}

pub fn parse_quantifier(
    sig: &Signature,
    s: &str,
) -> Result<(Option<Quantifier>, Sort, usize), String> {
    let mut parts = s.split_whitespace();

    let quantifier = match parts.next().unwrap() {
        "*" => None,
        "F" => Some(Quantifier::Forall),
        "E" => Some(Quantifier::Exists),
        _ => return Err("invalid quantifier (choose F/E/*)".to_string()),
    };

    let sort_id = parts.next().unwrap().to_string();
    let sort = if sig.sorts.contains(&sort_id) {
        Sort::Uninterpreted(sort_id)
    } else {
        return Err(format!("invalid sort {sort_id}"));
    };

    let count = parts.next().unwrap().parse::<usize>().unwrap();
    Ok((quantifier, sort, count))
}

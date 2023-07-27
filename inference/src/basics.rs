// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use itertools;
use itertools::Itertools;
use rayon::prelude::*;
use std::{
    collections::{HashMap, HashSet},
    sync::Mutex,
};

use crate::quant::QuantifierConfig;
use fly::syntax::BinOp;
use fly::syntax::Term::*;
use fly::syntax::*;
use fly::term::{prime::clear_next, prime::Next};
use fly::{ouritertools::OurItertools, semantics::Model, transitions::*};
use smtlib::proc::{SatResp, SmtPid, SolverError};
use solver::{
    conf::SolverConf,
    imp::{Backend, Solver},
};

pub enum CexResult {
    Cex(Vec<Model>),
    UnsatCore(HashSet<usize>),
    Cancelled,
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
    pub fn is_cex(&self) -> bool {
        match self {
            CexResult::Cex(_) => true,
            CexResult::UnsatCore(_) => false,
            _ => panic!("cex result is neither sat or unsat"),
        }
    }
}

/// Manages a subset of constraints, based on the counter-models they do not satisfy.
struct Core<'a> {
    formulas: &'a [Term],
    participants: HashSet<usize>,
    counter_models: Vec<Model>,
    to_participants: HashMap<usize, HashSet<usize>>,
    to_counter_models: HashMap<usize, HashSet<usize>>,
    minimal: bool,
}

impl<'a> Core<'a> {
    fn new(terms: &'a [Term], initial: HashSet<usize>, minimal: bool) -> Self {
        Core {
            formulas: terms,
            participants: initial,
            counter_models: vec![],
            to_participants: HashMap::new(),
            to_counter_models: HashMap::new(),
            minimal,
        }
    }

    fn add_counter_model(
        &mut self,
        counter_model: Model,
        check_first: Option<&HashSet<usize>>,
    ) -> bool {
        // We assume that the new counter-model satisfies all previous formulas.
        for &p_idx in &self.participants {
            assert_eq!(counter_model.eval(&self.formulas[p_idx]), 1);
        }

        let new_participant = check_first
            .unwrap_or(&HashSet::new())
            .iter()
            .cloned()
            .chain(0..self.formulas.len())
            .find(|i| {
                !self.participants.contains(i) && counter_model.eval(&self.formulas[*i]) == 0
            });

        match new_participant {
            Some(p_idx) => {
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

    fn len(&self) -> usize {
        self.participants.len()
    }
}

/// Maintains a set of [`SmtPid`]'s which can be canceled whenever necessary.
/// Composed of a `bool` which tracks whether the set has been canceled, followed by the
/// [`SmtPid`]'s of the solvers it contains.
pub struct SolverPids(Mutex<(bool, Vec<SmtPid>)>);

impl SolverPids {
    /// Create a new empty [`SolverPids`].
    pub fn new() -> Self {
        SolverPids(Mutex::new((false, vec![])))
    }

    /// Add the given [`SmtPid`] to the [`SolverPids`].
    ///
    /// Returns `true` if the [`SmtPid`] was added, or `false` if the [`SolverPids`] was already canceled.
    pub fn add_pid(&self, pid: SmtPid) -> bool {
        let mut pids = self.0.lock().unwrap();
        if pids.0 {
            false
        } else {
            pids.1.push(pid);
            true
        }
    }

    /// Cancel all solvers added to this [`SolverPids`].
    pub fn cancel(&self) {
        let mut pids = self.0.lock().unwrap();
        pids.0 = true;
        for pid in pids.1.drain(..) {
            pid.kill();
        }
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
    signature: Signature,
    pub module: DestructuredModule,
    disj: bool,
    gradual: bool,
    minimal: bool,
}

fn get_minimal_model<B: Backend>(solver: &mut Solver<B>) -> CexResult {
    match solver.get_minimal_model() {
        Ok(states_vec) => CexResult::Cex(states_vec),
        Err(SolverError::Killed) => CexResult::Cancelled,
        Err(SolverError::CouldNotMinimize(reason)) => CexResult::Unknown(reason),
        Err(e) => panic!("error in solver: {e}"),
    }
}

fn get_unsat_core<B: Backend>(solver: &mut Solver<B>) -> CexResult {
    match solver.get_unsat_core() {
        Ok(solver_core) => {
            let mut core = HashSet::new();
            for ind in solver_core {
                if let Term::Id(s) = ind.0 {
                    let ind = s[6..].parse::<usize>().unwrap();
                    core.insert(ind);
                }
            }
            CexResult::UnsatCore(core)
        }
        Err(SolverError::Killed) => CexResult::Cancelled,
        Err(e) => panic!("error in solver: {e}"),
    }
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

    pub fn init_cex(&self, confs: &[&SolverConf], t: &Term) -> Option<Model> {
        self.implication_cex(confs, &self.module.inits, t)
            .into_option()
            .map(|mut models| {
                assert_eq!(models.len(), 1);
                models.pop().unwrap()
            })
    }

    pub fn trans_cex(
        &self,
        confs: &[&SolverConf],
        hyp: &[Term],
        t: &Term,
        with_safety: bool,
        solver_pids: Option<&SolverPids>,
    ) -> CexResult {
        let transitions = self.disj_trans();
        let mut separate_cores: Vec<Option<HashSet<usize>>> = vec![None; transitions.len()];
        let mut unsat_core = HashSet::new();

        let try_conf = |conf: &SolverConf, core: &mut Core, transition: &[&Term]| {
            let mut solver = conf.solver(&self.signature, 2);
            if solver_pids.is_some_and(|pids| !pids.add_pid(solver.pid())) {
                return CexResult::Cancelled;
            }
            let mut assumptions = HashMap::new();

            let mut prestate = vec![];
            for &i in &core.participants {
                let ind = solver.get_indicator(i.to_string().as_str());
                assumptions.insert(ind.clone(), true);
                prestate.push(Term::BinOp(
                    BinOp::Iff,
                    Box::new(ind),
                    Box::new(hyp[i].clone()),
                ));
            }

            for p in &prestate {
                solver.assert(p)
            }

            for a in &self.module.axioms {
                solver.assert(a);
                solver.assert(&Next::new(&self.signature).prime(a));
            }

            for a in transition {
                solver.assert(a);
            }

            if with_safety {
                for a in &self.module.proofs {
                    solver.assert(&a.safety.x);
                }
            }

            solver.assert(&Term::negate(Next::new(&self.signature).prime(t)));

            let resp = solver.check_sat(assumptions);
            let cex_res = match resp {
                Ok(SatResp::Sat) => get_minimal_model(&mut solver),
                Ok(SatResp::Unsat) => get_unsat_core(&mut solver),
                Err(SolverError::Killed) => CexResult::Cancelled,
                Ok(SatResp::Unknown(reason)) | Err(SolverError::CouldNotMinimize(reason)) => {
                    CexResult::Unknown(reason)
                }
                Err(e) => panic!("error in solver: {e}"),
            };

            solver.save_tee();

            cex_res
        };

        let mut unknown_reasons = vec![];
        for t_idx in 0..transitions.len() {
            let mut core: Core = if self.gradual {
                Core::new(hyp, HashSet::new(), self.minimal)
            } else {
                Core::new(hyp, (0..hyp.len()).collect(), self.minimal)
            };

            let mut conf_idx = 0;
            'this_transition: while conf_idx < confs.len() {
                match try_conf(confs[conf_idx], &mut core, &transitions[t_idx]) {
                    CexResult::Cex(models) => {
                        if !core.add_counter_model(models[0].clone(), Some(&unsat_core)) {
                            log::debug!("Found SAT with {} formulas in prestate.", core.len());
                            return CexResult::Cex(models);
                        }
                    }
                    CexResult::UnsatCore(my_core) => {
                        unsat_core.extend(my_core.iter().copied());
                        separate_cores[t_idx] = Some(my_core);
                        break 'this_transition;
                    }
                    CexResult::Cancelled => return CexResult::Cancelled,
                    CexResult::Unknown(reason) => {
                        unknown_reasons.push(reason);
                        conf_idx += 1
                    }
                }
            }
        }

        if separate_cores.iter().any(|core| core.is_none()) {
            log::debug!("Found unknown.");
            return CexResult::Unknown(unknown_reasons.join("\n"));
        }

        let core_sizes = separate_cores
            .iter()
            .map(|core| core.as_ref().unwrap().len())
            .collect_vec();
        log::debug!(
            "Found UNSAT with {} formulas in core (by transition: {:?})",
            unsat_core.len(),
            core_sizes
        );
        CexResult::UnsatCore(unsat_core)
    }

    pub fn implication_cex(&self, confs: &[&SolverConf], hyp: &[Term], t: &Term) -> CexResult {
        let mut core: Core = if self.gradual {
            Core::new(hyp, HashSet::new(), self.minimal)
        } else {
            Core::new(hyp, (0..hyp.len()).collect(), self.minimal)
        };

        let try_conf = |conf: &SolverConf, core: &mut Core| -> CexResult {
            let mut solver = conf.solver(&self.signature, 1);
            for a in &self.module.axioms {
                solver.assert(a);
            }
            for &i in &core.participants {
                solver.assert(&hyp[i])
            }
            solver.assert(&Term::negate(t.clone()));

            let resp = solver.check_sat(HashMap::new()).expect("error in solver");
            let cex_res = match resp {
                SatResp::Sat => get_minimal_model(&mut solver),
                SatResp::Unsat => get_unsat_core(&mut solver),
                SatResp::Unknown(reason) => CexResult::Unknown(reason),
            };

            solver.save_tee();

            cex_res
        };

        let mut conf_idx = 0;
        let mut unknown_reasons = vec![];
        while conf_idx < confs.len() {
            match try_conf(confs[conf_idx], &mut core) {
                CexResult::Cex(model) => {
                    if !core.add_counter_model(model[0].clone(), None) {
                        return CexResult::Cex(model);
                    }
                }
                CexResult::Unknown(reason) => {
                    unknown_reasons.push(reason);
                    conf_idx += 1
                }
                res => return res,
            }
        }

        return CexResult::Unknown(unknown_reasons.join("\n"));
    }

    pub fn simulate_from(
        &self,
        conf: &SolverConf,
        state: &Model,
        width: usize,
        depth: usize,
    ) -> Vec<Model> {
        assert!(depth >= 1);

        let transitions = self.disj_trans();
        let state_term = state.to_term();
        let samples = Mutex::new(vec![]);
        let solver_pids = SolverPids::new();

        transitions.into_par_iter().for_each(|transition| {
            let mut solver = conf.solver(&self.signature, 2);
            solver_pids.add_pid(solver.pid());
            solver.assert(&state_term);
            for a in &self.module.axioms {
                solver.assert(&Next::new(&self.signature).prime(a));
            }
            for t in transition {
                solver.assert(t);
            }

            'this_loop: loop {
                let resp = solver.check_sat(HashMap::new());
                match resp {
                    Ok(SatResp::Sat) => match solver.get_model() {
                        Ok(mut states) => {
                            assert_eq!(states.len(), 2);
                            let new_sample = states.pop().unwrap();
                            solver.assert(&Term::negate(
                                Next::new(&self.signature).prime(&new_sample.to_term()),
                            ));
                            {
                                let mut samples_lock = samples.lock().unwrap();
                                if samples_lock.len() < width {
                                    samples_lock.push(new_sample);
                                }
                                if samples_lock.len() >= width {
                                    solver_pids.cancel();
                                    break 'this_loop;
                                }
                            }
                        }
                        _ => break 'this_loop,
                    },
                    _ => break 'this_loop,
                }
            }

            solver.save_tee();
        });

        let mut samples = samples.into_inner().unwrap();

        if depth > 1 {
            let mut deep_samples: Vec<Model> = samples
                .par_iter()
                .flat_map(|sample| self.simulate_from(conf, sample, width, depth - 1))
                .collect();
            samples.append(&mut deep_samples);
        }

        samples
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

    pub fn trans_safe_cex(&self, confs: &[&SolverConf], hyp: &[Term]) -> CexResult {
        let mut core = HashSet::new();
        for s in self.module.proofs.iter() {
            match self.trans_cex(confs, hyp, &s.safety.x, true, None) {
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
    PDnfNaive,
}

pub struct InferenceConfig {
    pub fname: String,

    pub cfg: QuantifierConfig,
    pub qf_body: QfBody,

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

    pub extend_width: Option<usize>,
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

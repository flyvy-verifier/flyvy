// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use itertools::Itertools;
use rayon::prelude::*;
use std::{
    collections::{HashMap, HashSet},
    sync::RwLock,
};

use crate::quant::QuantifierConfig;
use fly::syntax::BinOp;
use fly::syntax::Term::*;
use fly::syntax::*;
use fly::term::{prime::clear_next, prime::Next};
use fly::{ouritertools::OurItertools, semantics::Model, transitions::*};
use smtlib::proc::{SatResp, SmtPid, SolverError};
use solver::conf::SolverConf;

pub enum TransCexResult {
    CTI(Model, Model),
    UnsatCore(HashSet<usize>),
    Cancelled,
    Unknown,
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

    fn add_counter_model(&mut self, counter_model: Model) -> bool {
        // We assume that the new counter-model satisfies all previous formulas.
        for &p_idx in &self.participants {
            assert_eq!(counter_model.eval(&self.formulas[p_idx]), 1);
        }

        let new_participant = (0..self.formulas.len()).find(|i| {
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
pub struct SolverPids(RwLock<(bool, Vec<SmtPid>)>);

impl SolverPids {
    /// Create a new empty [`SolverPids`].
    pub fn new() -> Self {
        SolverPids(RwLock::new((false, vec![])))
    }

    /// Add the given [`SmtPid`] to the [`SolverPids`].
    ///
    /// Returns `true` if the [`SmtPid`] was added, or `false` if the [`SolverPids`] was already canceled.
    pub fn add_pid(&self, pid: SmtPid) -> bool {
        let mut pids = self.0.write().unwrap();
        if pids.0 {
            false
        } else {
            pids.1.push(pid);
            true
        }
    }

    /// Cancel all solvers added to this [`SolverPids`].
    pub fn cancel(&self) {
        let mut pids = self.0.write().unwrap();
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

    pub fn init_cex(&self, conf: &SolverConf, t: &Term) -> Option<Model> {
        self.implication_cex(conf, &self.module.inits, t)
    }

    pub fn trans_cex(
        &self,
        conf: &SolverConf,
        hyp: &[Term],
        t: &Term,
        with_init: bool,
        with_safety: bool,
        solver_pids: Option<&SolverPids>,
    ) -> TransCexResult {
        let mut core: Core = if self.gradual {
            Core::new(hyp, HashSet::new(), self.minimal)
        } else {
            Core::new(hyp, (0..hyp.len()).collect(), self.minimal)
        };

        let transitions = self.disj_trans();
        let mut check_transition: Vec<bool> = vec![true; transitions.len()];
        let mut unsat_cores: Vec<HashSet<usize>> = vec![HashSet::new(); transitions.len()];
        let mut unknown = false;

        while let Some(t_idx) = (0..transitions.len()).find(|i| check_transition[*i]) {
            check_transition[t_idx] = false;
            'inner: loop {
                let mut solver = conf.solver(&self.signature, 2);
                if solver_pids.is_some() && !solver_pids.unwrap().add_pid(solver.pid()) {
                    return TransCexResult::Cancelled;
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

                if with_init {
                    let init = Term::and(self.module.inits.iter().cloned());
                    solver.assert(&Term::or([init, Term::and(prestate)]));
                } else {
                    for p in &prestate {
                        solver.assert(p)
                    }
                }

                for a in &self.module.axioms {
                    solver.assert(a);
                    solver.assert(&Next::new(&self.signature).prime(a));
                }

                for a in &transitions[t_idx] {
                    solver.assert(a);
                }

                if with_safety {
                    for a in &self.module.proofs {
                        solver.assert(&a.safety.x);
                    }
                }

                if with_init {
                    let init = Term::and(self.module.inits.iter().cloned());
                    solver.assert(&Term::negate(Next::new(&self.signature).prime(&init)));
                }

                solver.assert(&Term::negate(Next::new(&self.signature).prime(t)));

                let resp = solver.check_sat(assumptions);
                match resp {
                    Ok(SatResp::Sat) => match solver.get_minimal_model() {
                        Ok(states_vec) => {
                            let mut states = states_vec.into_iter();
                            let pre = states.next().unwrap();
                            let post = states.next().unwrap();
                            assert_eq!(states.next(), None);

                            if !core.add_counter_model(pre.clone()) {
                                log::debug!("Found SAT with {} formulas in prestate.", core.len());
                                return TransCexResult::CTI(pre, post);
                            }

                            for i in 0..transitions.len() {
                                if i != t_idx
                                    && !check_transition[i]
                                    && !unsat_cores[i].is_subset(&core.participants)
                                {
                                    check_transition[i] = true;
                                    unsat_cores[i] = HashSet::new();
                                }
                            }
                        }
                        Err(SolverError::Killed) => return TransCexResult::Cancelled,
                        Err(e) => panic!("error in solver: {e}"),
                    },
                    Ok(SatResp::Unsat) => {
                        assert!(unsat_cores[t_idx].is_empty());
                        for ind in solver.get_unsat_core() {
                            if let Term::Id(s) = ind.0 {
                                unsat_cores[t_idx].insert(s[6..].parse().unwrap());
                            }
                        }
                        break 'inner;
                    }
                    Ok(SatResp::Unknown(_)) => {
                        unknown = true;
                        break 'inner;
                    }
                    Err(SolverError::Killed) => return TransCexResult::Cancelled,
                    Err(e) => panic!("error in solver: {e}"),
                }
                solver.save_tee();
            }
        }

        if unknown {
            log::debug!("Found unknown.");
            return TransCexResult::Unknown;
        }

        let unsat_core = unsat_cores
            .into_iter()
            .reduce(|x, y| x.union(&y).cloned().collect())
            .unwrap();

        log::debug!(
            "Found UNSAT with {} formulas in prestate.",
            unsat_core.len()
        );

        if self.minimal {
            assert_eq!(unsat_core, core.participants);
        }

        TransCexResult::UnsatCore(unsat_core)
    }

    pub fn implication_cex(&self, conf: &SolverConf, hyp: &[Term], t: &Term) -> Option<Model> {
        let mut core: Core = if self.gradual {
            Core::new(hyp, HashSet::new(), self.minimal)
        } else {
            Core::new(hyp, (0..hyp.len()).collect(), self.minimal)
        };

        loop {
            let mut solver = conf.solver(&self.signature, 1);
            for a in &self.module.axioms {
                solver.assert(a);
            }
            for &i in &core.participants {
                solver.assert(&hyp[i])
            }
            solver.assert(&Term::negate(t.clone()));

            let resp = solver.check_sat(HashMap::new()).expect("error in solver");
            match resp {
                SatResp::Sat => {
                    let mut states = solver
                        .get_minimal_model()
                        .expect("solver error while minimizing");
                    assert_eq!(states.len(), 1);

                    if !core.add_counter_model(states[0].clone()) {
                        solver.save_tee();
                        return Some(states.pop().unwrap());
                    }
                }
                SatResp::Unsat => {
                    solver.save_tee();
                    return None;
                }
                SatResp::Unknown(reason) => panic!("sat solver returned unknown: {reason}"),
            }
        }
    }

    pub fn simulate_from(
        &self,
        conf: &SolverConf,
        state: &Model,
        width: usize,
        depth: usize,
    ) -> Vec<Model> {
        assert!(depth >= 1);

        let disj_trans = self.disj_trans();
        let state_term = state.to_term();
        let mut samples = vec![];
        let mut block_models = vec![vec![]; disj_trans.len()];

        let mut solver = conf.solver(&self.signature, 2);
        solver.assert(&state_term);
        for a in &self.module.axioms {
            solver.assert(&Next::new(&self.signature).prime(a));
        }

        let mut unblocked_trans: HashSet<usize> = HashSet::from_iter(0..disj_trans.len());
        while !unblocked_trans.is_empty() && samples.len() < width {
            for i in unblocked_trans.iter().copied().sorted().collect_vec() {
                if samples.len() >= width {
                    break;
                }

                let mut new_sample = None;
                solver.push();
                for t in &disj_trans[i] {
                    solver.assert(t);
                }
                for t in &block_models[i] {
                    solver.assert(t);
                }

                let resp = solver.check_sat(HashMap::new()).expect("error in solver");
                match resp {
                    SatResp::Sat => {
                        let mut states = solver.get_model().expect("could not get model");
                        assert_eq!(states.len(), 2);

                        new_sample = states.pop();
                    }
                    SatResp::Unsat | SatResp::Unknown(_) => {
                        unblocked_trans.remove(&i);
                    }
                }

                solver.pop();

                if let Some(sample) = new_sample {
                    block_models[i].push(Term::negate(
                        Next::new(&self.signature).prime(&sample.to_term()),
                    ));
                    samples.push(sample);
                }
            }
        }

        solver.save_tee();

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
                    for (ind, b) in solver.get_unsat_core() {
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

    pub fn trans_safe_cex(&self, conf: &SolverConf, hyp: &[Term]) -> Option<Model> {
        for s in self.module.proofs.iter() {
            if let TransCexResult::CTI(model, _) =
                self.trans_cex(conf, hyp, &s.safety.x, false, true, None)
            {
                return Some(model);
            }
        }

        None
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
    pub cfg: QuantifierConfig,
    pub qf_body: QfBody,

    pub max_size: Option<usize>,
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
    pub gradual_advance: bool,
    pub indiv: bool,

    pub extend_width: Option<usize>,
    pub extend_depth: Option<usize>,
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
        Sort::Id(sort_id)
    } else {
        return Err(format!("invalid sort {sort_id}"));
    };

    let count = parts.next().unwrap().parse::<usize>().unwrap();
    Ok((quantifier, sort, count))
}

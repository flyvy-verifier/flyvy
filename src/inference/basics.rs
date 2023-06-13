// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use itertools::Itertools;
use std::{
    collections::{HashMap, HashSet},
    sync::{Arc, RwLock},
};

use crate::{
    fly::{
        semantics::Model,
        syntax::{BinOp, Module, NOp, Quantifier, Signature, Sort, Term, ThmStmt, UOp},
    },
    inference::quant::QuantifierConfig,
    smtlib::proc::SatResp,
    solver::SolverConf,
    term::{FirstOrder, Next},
};

use rayon::prelude::*;

/// A first-order module is represented using first-order formulas,
/// namely single-vocabulary axioms, initial assertions and safety assertions,
/// and double-vocabulary transition assertions.
/// `disj` denotes whether to split the transitions disjunctively, if possible.
pub struct FOModule {
    signature: Signature,
    pub axioms: Vec<Term>,
    pub inits: Vec<Term>,
    pub transitions: Vec<Term>,
    pub safeties: Vec<Term>,
    disj: bool,
    gradual: bool,
}

pub enum TransCexResult {
    CTI(Model, Model),
    UnsatCore(HashSet<usize>),
    Cancelled,
}

impl FOModule {
    pub fn new(m: &Module, disj: bool, gradual: bool) -> Self {
        let mut fo = FOModule {
            signature: m.signature.clone(),
            axioms: vec![],
            inits: vec![],
            transitions: vec![],
            safeties: vec![],
            disj,
            gradual,
        };

        for statement in &m.statements {
            match statement {
                ThmStmt::Assume(t) => {
                    if FirstOrder::unrolling(t) == Some(0) {
                        fo.inits.push(t.clone());
                    } else if let Term::UnaryOp(UOp::Always, t) = t {
                        match FirstOrder::unrolling(t) {
                            Some(0) => fo.axioms.push(t.as_ref().clone()),
                            Some(1) => fo
                                .transitions
                                .push(Next::new(&m.signature).normalize(t.as_ref())),
                            _ => (),
                        }
                    }
                }
                ThmStmt::Assert(pf) => {
                    if let Term::UnaryOp(UOp::Always, t) = &pf.assert.x {
                        if FirstOrder::unrolling(t) == Some(0) {
                            fo.safeties.push(t.as_ref().clone());
                        }
                    }
                }
            }
        }

        fo
    }

    fn disj_trans(&self) -> Vec<Vec<&Term>> {
        if self.disj {
            self.transitions
                .iter()
                .map(|t| match t {
                    Term::NAryOp(NOp::Or, args) => args.iter().collect_vec(),
                    _ => vec![t],
                })
                .multi_cartesian_product()
                .collect_vec()
        } else {
            vec![self.transitions.iter().collect_vec()]
        }
    }

    pub fn init_cex(&self, conf: &SolverConf, t: &Term) -> Option<Model> {
        self.implication_cex(conf, &self.inits, t)
    }

    pub fn trans_cex(
        &self,
        conf: &SolverConf,
        hyp: &[Term],
        t: &Term,
        with_init: bool,
        with_safety: bool,
        cancel: Option<Arc<RwLock<bool>>>,
    ) -> TransCexResult {
        let cancelled = || match &cancel {
            None => false,
            Some(lock) => *lock.read().unwrap(),
        };
        let mut participants: Vec<usize> = if self.gradual {
            vec![]
        } else {
            (0..hyp.len()).collect()
        };

        loop {
            let mut core: HashSet<usize> = HashSet::new();
            let mut new_participants: HashSet<usize> = HashSet::new();
            for trans in self.disj_trans() {
                if cancelled() {
                    return TransCexResult::Cancelled;
                }

                let mut solver = conf.solver(&self.signature, 2);
                let mut assumptions = HashMap::new();

                let mut prestate = vec![];
                for &i in &participants {
                    let ind = solver.get_indicator(i.to_string().as_str());
                    assumptions.insert(ind.clone(), true);
                    prestate.push(Term::BinOp(
                        BinOp::Iff,
                        Box::new(ind),
                        Box::new(hyp[i].clone()),
                    ));
                }

                if with_init {
                    let init = Term::and(self.inits.iter().cloned());
                    solver.assert(&Term::or([init, Term::and(prestate)]));
                } else {
                    solver.assert(&Term::and(prestate));
                }

                for a in self.axioms.iter() {
                    solver.assert(a);
                    solver.assert(&Next::new(&self.signature).prime(a));
                }

                for a in trans {
                    solver.assert(a);
                }

                if with_safety {
                    for a in self.safeties.iter() {
                        solver.assert(a);
                    }
                }

                if with_init {
                    let init = Term::and(self.inits.iter().cloned());
                    solver.assert(&Term::negate(Next::new(&self.signature).prime(&init)));
                }

                solver.assert(&Term::negate(Next::new(&self.signature).prime(t)));

                let resp = solver.check_sat(assumptions).expect("error in solver");
                match resp {
                    SatResp::Sat => {
                        let mut states = solver.get_minimal_model().into_iter();
                        let pre = states.next().unwrap();
                        let post = states.next().unwrap();
                        assert_eq!(states.next(), None);

                        if let Some(i) = (0..hyp.len())
                            .find(|i| !participants.contains(i) && pre.eval(&hyp[*i]) == 0)
                        {
                            new_participants.insert(i);
                        } else {
                            return TransCexResult::CTI(pre, post);
                        }
                    }
                    SatResp::Unsat => {
                        for ind in solver.get_unsat_core() {
                            match ind.0 {
                                Term::Id(s) => {
                                    core.insert(s[6..].parse().unwrap());
                                }
                                _ => (),
                            }
                        }
                    }
                    SatResp::Unknown(reason) => panic!("sat solver returned unknown: {reason}"),
                }
            }

            if new_participants.is_empty() {
                return TransCexResult::UnsatCore(core);
            } else {
                participants.extend(new_participants);
            }
        }
    }

    pub fn trans_safe_cex(&self, conf: &SolverConf, hyp: &[Term]) -> Option<Model> {
        for s in self.safeties.iter() {
            if let TransCexResult::CTI(model, _) = self.trans_cex(conf, hyp, s, false, true, None) {
                return Some(model);
            }
        }

        None
    }

    pub fn implication_cex(&self, conf: &SolverConf, hyp: &[Term], t: &Term) -> Option<Model> {
        let mut solver = conf.solver(&self.signature, 1);
        for a in self.axioms.iter().chain(hyp.iter()) {
            solver.assert(a);
        }
        solver.assert(&Term::negate(t.clone()));

        let resp = solver.check_sat(HashMap::new()).expect("error in solver");
        match resp {
            SatResp::Sat => {
                let mut states = solver.get_minimal_model();
                assert_eq!(states.len(), 1);

                Some(states.remove(0))
            }
            SatResp::Unsat => None,
            SatResp::Unknown(_) => panic!(),
        }
    }

    pub fn simulate_from(
        &self,
        conf: &SolverConf,
        state: &Model,
        width: usize,
        depth: usize,
    ) -> Vec<Model> {
        let mut samples = vec![];
        assert!(depth >= 1);

        let disj_trans = self.disj_trans();
        let state_term = state.to_term();

        let mut solver = conf.solver(&self.signature, 2);
        solver.assert(&state_term);
        for a in &self.axioms {
            solver.assert(&Next::new(&self.signature).prime(a));
        }

        let mut unblocked_trans: HashSet<usize> = HashSet::from_iter(0..disj_trans.len());
        while !unblocked_trans.is_empty() && samples.len() < width {
            for i in unblocked_trans.iter().copied().collect_vec() {
                if samples.len() >= width {
                    break;
                }

                let mut new_sample = None;
                solver.push();
                for t in &disj_trans[i] {
                    solver.assert(t);
                }

                let resp = solver.check_sat(HashMap::new()).expect("error in solver");

                match resp {
                    SatResp::Sat => {
                        let mut states = solver.get_model();
                        assert_eq!(states.len(), 2);

                        new_sample = states.pop();
                    }
                    SatResp::Unsat => {
                        unblocked_trans.remove(&i);
                    }
                    SatResp::Unknown(reason) => panic!("sat solver returned unknown: {reason}"),
                }

                solver.pop();

                if let Some(sample) = new_sample {
                    solver.assert(&Term::negate(
                        Next::new(&self.signature).prime(&sample.to_term()),
                    ));
                    samples.push(sample);
                }
            }
        }

        if depth > 1 {
            let mut deep_samples: Vec<Model> = samples
                .par_iter()
                .flat_map(|sample| self.simulate_from(conf, sample, width, depth - 1))
                .collect();
            samples.append(&mut deep_samples);
        }

        samples
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
    pub gradual: bool,
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

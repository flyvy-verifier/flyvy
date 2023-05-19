// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use itertools::Itertools;
use std::collections::HashMap;

use crate::{
    fly::{
        semantics::Model,
        syntax::{Module, NOp, Quantifier, Signature, Sort, Term, ThmStmt, UOp},
    },
    inference::quant::QuantifierConfig,
    smtlib::proc::SatResp,
    term::{FirstOrder, Next},
    verify::SolverConf,
};

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
}

impl FOModule {
    pub fn new(m: &Module, disj: bool) -> Self {
        let mut fo = FOModule {
            signature: m.signature.clone(),
            axioms: vec![],
            inits: vec![],
            transitions: vec![],
            safeties: vec![],
            disj,
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

    pub fn init_cex(&self, conf: &SolverConf, t: &Term) -> Option<Model> {
        let mut solver = conf.solver(&self.signature, 1);
        for a in self.axioms.iter().chain(self.inits.iter()) {
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

    pub fn trans_cex(&self, conf: &SolverConf, hyp: &[Term], t: &Term) -> Option<(Model, Model)> {
        let disj_trans = if self.disj {
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
        };

        for trans in disj_trans {
            let mut solver = conf.solver(&self.signature, 2);
            for a in self
                .axioms
                .iter()
                .chain(self.safeties.iter())
                .chain(hyp.iter())
                .chain(trans.into_iter())
            {
                solver.assert(a);
            }
            for a in self.axioms.iter() {
                solver.assert(&Next::new(&self.signature).prime(a));
            }
            solver.assert(&Term::negate(Next::new(&self.signature).prime(t)));

            let resp = solver.check_sat(HashMap::new()).expect("error in solver");
            match resp {
                SatResp::Sat => {
                    let states = solver.get_minimal_model();
                    assert_eq!(states.len(), 2);

                    return Some(states.into_iter().collect_tuple().unwrap());
                }
                SatResp::Unsat => (),
                SatResp::Unknown(reason) => panic!("sat solver returned unknown: {reason}"),
            }
        }

        None
    }

    pub fn trans_safe_cex(&self, conf: &SolverConf, hyp: &[Term]) -> Option<Model> {
        for s in self.safeties.iter() {
            if let Some(models) = self.trans_cex(conf, hyp, s) {
                return Some(models.0);
            }
        }

        None
    }
}

pub struct InferenceConfig {
    pub cfg: QuantifierConfig,
    pub max_clauses: usize,
    pub max_clause_len: usize,
    pub nesting: Option<usize>,
    pub include_eq: bool,
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

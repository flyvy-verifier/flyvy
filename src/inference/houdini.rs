// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Implementation of the Houdini algorithm, which infers inductive invariants
//! to prove an assertion.

use std::collections::{HashMap, HashSet};

use rayon::prelude::*;

use crate::{
    fly::{
        semantics::Model,
        syntax::{Module, Signature, Term, ThmStmt},
    },
    smtlib::proc::SatResp,
    term::Next,
    verify::{
        safety::InvariantAssertion, AssertionFailure, FailureType, QueryError, SolveError,
        SolverConf,
    },
};

// TODO: the error reporting should be specific to Houdini, and these errors
// should later be converted into spanned errors that can be reported to the
// user. The code currently overloads AssertionFailure which was only intended
// for failures that are the direct result of checking a user assertion.

struct Houdini {
    conf: SolverConf,
    sig: Signature,
    assert: InvariantAssertion,
    invs: Vec<Term>,
}

#[derive(Debug, Clone)]
pub enum HoudiniError {
    InitInvUnknown(String),
    InductiveInvUnknown(String),
    NotInductive,
}

enum SatResult {
    Sat(Vec<Model>),
    Unsat,
    Unknown(String),
}

impl Houdini {
    fn new(conf: SolverConf, sig: &Signature, assert: InvariantAssertion) -> Self {
        let mut invs = vec![assert.inv.clone()];
        // TODO: support customization of initial candidate invariants
        invs.extend(assert.proof_invs.iter().cloned());
        log::info!("Running Houdini, candidate invariants are:");
        for p in &invs {
            log::info!("    {p}")
        }
        log::info!("");
        Self {
            conf,
            sig: sig.clone(),
            assert,
            invs,
        }
    }

    fn initiation_filter(&mut self) -> Result<(), HoudiniError> {
        log::info!("Checking initiation:");
        let mut not_implied: HashSet<Term> = HashSet::new();
        for q in &self.invs {
            if not_implied.contains(q) {
                continue;
            };
            log::info!("    Checking {q}");
            let mut solver = self.conf.solver(&self.sig, 1);
            solver.assert(&self.assert.init);
            solver.assert(&Term::negate(q.clone()));
            let resp = solver.check_sat(HashMap::new()).expect("error in solver");
            match resp {
                SatResp::Sat => {
                    log::info!("        Got model");
                    let states = solver.get_model();
                    assert_eq!(states.len(), 1);
                    // TODO(oded): make 0 and 1 special constants for this use
                    assert_eq!(states[0].eval(&self.assert.init, None), 1);
                    assert_eq!(states[0].eval(q, None), 0);
                    for qq in &self.invs {
                        if states[0].eval(qq, None) == 0 {
                            log::info!("        Pruning {qq}");
                            not_implied.insert(qq.clone());
                        }
                    }
                }
                SatResp::Unsat => (),
                SatResp::Unknown(m) => {
                    return Err(HoudiniError::InitInvUnknown(m));
                }
            }
        }
        self.invs.retain(|q| !not_implied.contains(q));
        Ok(())
    }

    fn inductive_iteration(&mut self) -> Result<bool, HoudiniError> {
        let mut not_implied: HashSet<Term> = HashSet::new();
        let inv_checks = self
            .invs
            .par_iter()
            .filter(|q| !not_implied.contains(*q))
            .map(|q| {
                log::info!("    Checking {q}");
                let mut solver = self.conf.solver(&self.sig, 2);
                for p in &self.invs {
                    solver.assert(p);
                }
                solver.assert(&self.assert.next);
                solver.assert(&Term::negate(Next::prime(q)));
                let resp = solver.check_sat(HashMap::new()).expect("error in solver");
                (
                    q,
                    match resp {
                        SatResp::Sat => {
                            log::info!("        Got model");
                            let states = solver.get_model();
                            assert_eq!(states.len(), 2);
                            SatResult::Sat(states)
                        }
                        SatResp::Unsat => SatResult::Unsat,
                        SatResp::Unknown(err) => SatResult::Unknown(err),
                    },
                )
            })
            .collect::<Vec<_>>();
        for (q, resp) in inv_checks {
            match resp {
                SatResult::Sat(states) => {
                    // TODO(oded): make 0 and 1 special constants for their use as Booleans
                    assert_eq!(states[1].eval(q, None), 0);
                    for qq in &self.invs {
                        if states[1].eval(qq, None) == 0 {
                            log::info!("        Pruning {qq}");
                            not_implied.insert(qq.clone());
                        }
                    }
                }
                SatResult::Unsat => (),
                SatResult::Unknown(m) => return Err(HoudiniError::InductiveInvUnknown(m)),
            }
        }
        if not_implied.is_empty() {
            log::info!("Fixed point reached");
            return Ok(true);
        }
        self.invs.retain(|q| !not_implied.contains(q));
        Ok(false)
    }
}

/// Attempt to infer inductive invariants to prove `assert`.
///
/// On success, returns a list of invariants which are together inductive and
/// include `assert.inv`.
pub fn infer(
    conf: &SolverConf,
    sig: &Signature,
    assert: &InvariantAssertion,
) -> Result<Vec<Term>, HoudiniError> {
    let mut state = Houdini::new(conf.clone(), sig, assert.clone());
    state.initiation_filter()?;

    log::info!("Candidate invariants are:");
    for p in &state.invs {
        log::info!("    {p}")
    }
    log::info!("");

    // compute fixed point
    log::info!("Computing fixed point:");
    loop {
        let done = state.inductive_iteration()?;
        if done {
            log::info!("Fixed point reached");
            break;
        }
        log::info!("Candidate invariants are:");
        for p in &state.invs {
            log::info!("    {p}")
        }
        log::info!("");
    }
    if state.invs.is_empty() || state.invs[0] != assert.inv {
        return Err(HoudiniError::NotInductive);
    }
    Ok(state.invs)
}

/// Prove the assertions in a module using Houdini invariant inference.
pub fn infer_module(conf: &SolverConf, m: &Module) -> Result<(), SolveError> {
    // TODO: this is highly redundant with verify_module, some refactoring is
    // needed to separate the generic module processing with what kind of
    // inference/proof process we want for each assertion.

    // assumptions/assertions so far
    let mut assumes: Vec<&Term> = vec![];
    let mut errors = SolveError::default();
    for step in &m.statements {
        match step {
            ThmStmt::Assume(e) => assumes.push(e),
            ThmStmt::Assert(pf) => {
                let proof_invariants: Vec<&Term> = pf.invariants.iter().map(|s| &s.x).collect();
                if let Ok(assert) =
                    InvariantAssertion::for_assert(&assumes, &pf.assert.x, &proof_invariants)
                {
                    let res = infer(conf, &m.signature, &assert);
                    match res {
                        Ok(invs) => {
                            println!("# inferred invariant:");
                            println!("assert {}", &pf.assert.x);
                            println!("proof {{");
                            for inv in invs {
                                println!("  invariant {inv}");
                            }
                            println!("}}");
                        }

                        Err(err) => errors.push(match err {
                            HoudiniError::InitInvUnknown(m) => AssertionFailure {
                                loc: pf.assert.span,
                                reason: FailureType::InitInv,
                                error: QueryError::Unknown(m),
                            },
                            HoudiniError::InductiveInvUnknown(m) => AssertionFailure {
                                loc: pf.assert.span,
                                reason: FailureType::NotInductive,
                                error: QueryError::Unknown(m),
                            },
                            HoudiniError::NotInductive => AssertionFailure {
                                loc: pf.assert.span,
                                reason: FailureType::NotInductive,
                                // TODO(oded): better error reporting here
                                error: QueryError::Unknown("assertion not in fixed point".to_string()),
                            },
                        }),
                    }
                } else {
                    errors.push(AssertionFailure {
                        loc: pf.assert.span,
                        error: QueryError::Unknown("unsupported".to_string()),
                        reason: FailureType::Unsupported,
                    })
                }
                // for future assertions, treat this assertion as an assumption
                assumes.push(&pf.assert.x);
            }
        }
    }
    if errors.fails.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

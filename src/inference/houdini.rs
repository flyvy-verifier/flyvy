// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Implementation of the Houdini algorithm, which infers inductive invariants
//! to prove an assertion.

use std::collections::{HashMap, HashSet};

use crate::{
    fly::syntax::{Module, Signature, Span, Term, ThmStmt},
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

/// Attempt to infer inductive invariants to prove `assert`.
///
/// On success, returns a list of invariants which are together inductive and
/// include `assert.inv`.
pub fn infer<'a>(
    conf: &SolverConf,
    sig: &Signature,
    span: Span,
    assert: &'a InvariantAssertion,
) -> Result<Vec<&'a Term>, AssertionFailure> {
    let mut invs = vec![&assert.inv];
    invs.extend(assert.proof_invs.iter());
    log::info!("Running Houdini, candidate invariants are:");
    for &p in &invs {
        log::info!("    {p}")
    }
    log::info!("");

    {
        // filter based on initiation
        log::info!("Checking initiation:");
        let mut not_implied: HashSet<&Term> = HashSet::new();
        for &q in &invs {
            if not_implied.contains(q) {
                continue;
            };
            log::info!("    Checking {q}");
            let mut solver = conf.solver(sig, 1);
            solver.assert(&assert.init);
            solver.assert(&Term::negate(q.clone()));
            let resp = solver.check_sat(HashMap::new()).expect("error in solver");
            match resp {
                SatResp::Sat => {
                    log::info!("        Got model");
                    let states = solver.get_model();
                    assert_eq!(states.len(), 1);
                    // TODO(oded): make 0 and 1 special constants for this use
                    assert_eq!(states[0].eval(&assert.init, None), 1);
                    assert_eq!(states[0].eval(q, None), 0);
                    for &qq in &invs {
                        if states[0].eval(qq, None) == 0 {
                            log::info!("        Pruning {qq}");
                            not_implied.insert(qq);
                        }
                    }
                }
                SatResp::Unsat => (),
                SatResp::Unknown(m) => {
                    return Err(AssertionFailure {
                        loc: span,
                        reason: FailureType::InitInv,
                        error: QueryError::Unknown(m),
                    });
                }
            }
        }
        invs.retain(|q| !not_implied.contains(q));
    }
    log::info!("Candidate invariants are:");
    for &p in &invs {
        log::info!("    {p}")
    }
    log::info!("");

    // compute fixed point
    log::info!("Computing fixed point:");
    loop {
        let mut not_implied: HashSet<&Term> = HashSet::new();
        for &q in &invs {
            if not_implied.contains(q) {
                continue;
            };
            log::info!("    Checking {q}");
            let mut solver = conf.solver(sig, 2);
            for &p in &invs {
                solver.assert(p);
            }
            solver.assert(&assert.next);
            solver.assert(&Term::negate(Next::prime(q)));
            let resp = solver.check_sat(HashMap::new()).expect("error in solver");
            match resp {
                SatResp::Sat => {
                    log::info!("        Got model");
                    let states = solver.get_model();
                    assert_eq!(states.len(), 2);
                    // TODO(oded): make 0 and 1 special constants for their use as Booleans
                    assert_eq!(states[1].eval(q, None), 0);
                    for &qq in &invs {
                        if states[1].eval(qq, None) == 0 {
                            log::info!("        Pruning {qq}");
                            not_implied.insert(qq);
                        }
                    }
                }
                SatResp::Unsat => (),
                SatResp::Unknown(m) => {
                    return Err(AssertionFailure {
                        loc: span,
                        reason: FailureType::NotInductive,
                        error: QueryError::Unknown(m),
                    });
                }
            }
        }
        if not_implied.is_empty() {
            log::info!("Fixed point reached");
            break;
        }
        invs.retain(|q| !not_implied.contains(q));
        log::info!("Candidate invariants are:");
        for &p in &invs {
            log::info!("    {p}")
        }
        log::info!("");
    }
    if invs.is_empty() || invs[0] != &assert.inv {
        return Err(AssertionFailure {
            loc: span,
            reason: FailureType::NotInductive,
            error: QueryError::Unknown("assertion not in fixed point".to_string()), // TODO(oded): better error reporting
        });
    }
    Ok(invs)
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
                    let res = infer(conf, &m.signature, pf.assert.span, &assert);
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

                        Err(err) => errors.push(err),
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

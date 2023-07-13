// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Implementation of the Houdini algorithm, which infers inductive invariants
//! to prove an assertion.

use std::{
    collections::{HashMap, HashSet},
    sync::Mutex,
};

use rayon::prelude::*;

use fly::{syntax::*, term::prime::Next, transitions::*};
use solver::{conf::SolverConf, SatResp};
use verify::{
    error::{AssertionFailure, FailureType, QueryError, SolveError},
    safety::InvariantAssertion,
};

// TODO: the error reporting should be specific to Houdini, and these errors
// should later be converted into spanned errors that can be reported to the
// user. The code currently overloads AssertionFailure which was only intended
// for failures that are the direct result of checking a user assertion.

struct Houdini {
    conf: SolverConf,
    sig: Signature,
    init: Term,
    next: Term,
    /// These are the candidate invariants remaining.
    // (this is the only mutable state)
    invs: Vec<Term>,
}

#[derive(Debug, Clone)]
pub enum HoudiniError {
    InitInvUnknown(String),
    InductiveInvUnknown(String),
    NotInductive,
}

impl Houdini {
    fn new(conf: SolverConf, sig: &Signature, assert: InvariantAssertion) -> Self {
        let mut invs = vec![assert.inv.x.clone()];
        // TODO: support customization of initial candidate invariants
        invs.extend(assert.proof_invs.iter().map(|inv| inv.x.clone()));
        log::info!("Running Houdini, candidate invariants are:");
        for p in &invs {
            log::info!("    {p}")
        }
        log::info!("");
        Self {
            conf,
            sig: sig.clone(),
            init: assert.init,
            next: assert.next,
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
            solver.assert(&self.init);
            solver.assert(&Term::negate(q.clone()));
            let resp = solver.check_sat(HashMap::new()).expect("error in solver");
            match resp {
                SatResp::Sat => {
                    log::info!("        Got model");
                    let states = solver.get_model();
                    assert_eq!(states.len(), 1);
                    // TODO(oded): make 0 and 1 special constants for this use
                    assert_eq!(states[0].eval(&self.init), 1);
                    assert_eq!(states[0].eval(q), 0);
                    for qq in &self.invs {
                        if states[0].eval(qq) == 0 {
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
        let mut not_implied: Mutex<HashSet<Term>> = Mutex::new(HashSet::new());
        let inv_checks = self
            .invs
            .par_iter()
            .map(|q| {
                log::info!("    Checking {q}");
                // create a new scope to lock not_implied for the shortest duration possible
                {
                    // NOTE: this set is mutated concurrently by these invariant
                    // checks, so this check is just an optimization - a later
                    // Sat result might prove that this invariant check is
                    // redundant, but it'll be too late by then
                    let not_implied = not_implied.lock().unwrap();
                    if not_implied.contains(q) {
                        return None;
                    }
                }
                let mut solver = self.conf.solver(&self.sig, 2);
                for p in &self.invs {
                    solver.assert(p);
                }
                solver.assert(&self.next);
                solver.assert(&Term::negate(Next::new(&self.sig).prime(q)));
                let resp = solver.check_sat(HashMap::new()).expect("error in solver");
                if matches!(resp, SatResp::Sat) {
                    log::info!("        Got model");
                    let states = solver.get_model();
                    assert_eq!(states.len(), 2);
                    // TODO(oded): make 0 and 1 special constants for their use as Booleans
                    assert_eq!(states[1].eval(q), 0);
                    for qq in &self.invs {
                        if states[1].eval(qq) == 0 {
                            log::info!("        Pruning {qq}");
                            let mut not_implied = not_implied.lock().unwrap();
                            not_implied.insert(qq.clone());
                        }
                    }
                }
                Some(resp)
            })
            .flatten()
            .collect::<Vec<_>>();
        for resp in inv_checks {
            match resp {
                SatResp::Sat => {}
                SatResp::Unsat => (),
                SatResp::Unknown(m) => return Err(HoudiniError::InductiveInvUnknown(m)),
            }
        }
        // We have a `&mut Mutex` here, which proves that no other thread has a
        // reference to the mutex, so we can use `get_mut()` to get its contents
        // without actually locking. The `.unwrap()` is still needed for poison
        // checking.
        let not_implied = not_implied.get_mut().unwrap();
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
    if state.invs.is_empty() || state.invs[0] != assert.inv.x {
        return Err(HoudiniError::NotInductive);
    }
    Ok(state.invs)
}

/// Prove the assertions in a module using Houdini invariant inference.
pub fn infer_module(conf: &SolverConf, m: &Module) -> Result<(), SolveError> {
    // TODO: this is highly redundant with verify_module, some refactoring is
    // needed to separate the generic module processing with what kind of
    // inference/proof process we want for each assertion.
    infer_destructured_module(conf, &extract(m).unwrap(), &m.signature)
}

fn infer_destructured_module(
    conf: &SolverConf,
    module: &DestructuredModule,
    signature: &Signature,
) -> Result<(), SolveError> {
    let inits = &module.inits;
    let transitions = &module.transitions;
    // we push verified safety properties as axioms
    let mut axioms = module.axioms.clone();
    let mut errors = SolveError::default();

    for proof in &module.proofs {
        if let Ok(assert) =
            InvariantAssertion::for_assert(signature, inits, transitions, &axioms, proof)
        {
            let res = infer(conf, signature, &assert);
            match res {
                Ok(invs) => {
                    println!("# inferred invariant:");
                    println!("assert always {}", &proof.safety.x);
                    println!("proof {{");
                    for inv in invs {
                        println!("  invariant {inv}");
                    }
                    println!("}}");
                }
                Err(err) => errors.push(match err {
                    HoudiniError::InitInvUnknown(m) => AssertionFailure {
                        loc: proof.safety.span,
                        reason: FailureType::InitInv,
                        error: QueryError::Unknown(m),
                    },
                    HoudiniError::InductiveInvUnknown(m) => AssertionFailure {
                        loc: proof.safety.span,
                        reason: FailureType::NotInductive,
                        error: QueryError::Unknown(m),
                    },
                    HoudiniError::NotInductive => AssertionFailure {
                        loc: proof.safety.span,
                        reason: FailureType::NotInductive,
                        // TODO(oded): better error reporting here
                        error: QueryError::Unknown("assertion not in fixed point".to_string()),
                    },
                }),
            }
        } else {
            errors.push(AssertionFailure {
                loc: proof.safety.span,
                error: QueryError::Unknown("unsupported".to_string()),
                reason: FailureType::Unsupported,
            })
        }
        // for future assertions, treat this assertion as an assumption
        axioms.push(proof.safety.x.clone());
    }
    if errors.fails.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

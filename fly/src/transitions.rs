// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Extract a first-order transition system from a Module.

use crate::syntax::*;
use crate::term::fo::FirstOrder;
use crate::term::prime::Next;
use thiserror::Error;

/// Contains the different parts of the extracted transition system.
pub struct DestructuredModule {
    /// The initial conditions (assumes with no primes)
    pub inits: Vec<Term>,
    /// The transitions (assume-alwayses with one prime)
    pub transitions: Vec<Term>,
    /// The axioms (assume-alwayses with no primes)
    pub axioms: Vec<Term>,
    /// The assertions about the transition system
    pub proofs: Vec<Proof>,
}

/// Contains the parts of assertions in the module.
/// Checking an Assert means checking safety & invariants.
pub struct Proof {
    /// The safety property to check
    pub safety: Term,
    /// The invariants that we want to verify prove the safety property
    pub invariants: Vec<Term>,
}

/// An error during transition system extraction
#[derive(Debug, Error, PartialEq)]
pub enum ExtractionError {
    /// `extract` is only correct on modules where all assumes come before all asserts
    #[error("all assumes should precede all asserts, but found {0:?}")]
    OutOfOrderStatement(ThmStmt),
    /// The term should not have any primes (one-state)
    #[error("expected no primes in {0}")]
    AnyFuture(Term),
    /// The term should have at most one prime (two-state)
    #[error("expected no primes or only one prime in {0}")]
    TooFuture(Term),
    /// All asserts must have a top-level always
    #[error("expected all assertions to be safety properties but found {0}")]
    AssertWithoutAlways(Term),
}

/// Extract the different types of terms from a Module
pub fn extract(module: &Module) -> Result<DestructuredModule, ExtractionError> {
    let mut assumes = Vec::new();
    let mut asserts = Vec::new();
    for statement in &module.statements {
        match statement {
            ThmStmt::Assert(proof) => asserts.push(proof),
            ThmStmt::Assume(term) if asserts.is_empty() => assumes.push(term.clone()),
            _ => return Err(ExtractionError::OutOfOrderStatement(statement.clone())),
        }
    }

    let mut inits = Vec::new();
    let mut transitions = Vec::new();
    let mut axioms = Vec::new();
    for assume in assumes {
        match assume {
            Term::UnaryOp(UOp::Always, term) if FirstOrder::unrolling(&term) == Some(0) => {
                axioms.push(*term)
            }
            Term::UnaryOp(UOp::Always, term) if FirstOrder::unrolling(&term) == Some(1) => {
                transitions.push(*term)
            }
            Term::UnaryOp(UOp::Always, term) => return Err(ExtractionError::TooFuture(*term)),
            term if FirstOrder::unrolling(&term) == Some(0) => inits.push(term),
            term => return Err(ExtractionError::AnyFuture(term)),
        }
    }

    let mut proofs = Vec::new();
    for assert in asserts {
        let safety = match &assert.assert.x {
            Term::UnaryOp(UOp::Always, term) if FirstOrder::unrolling(term) == Some(0) => {
                *term.clone()
            }
            Term::UnaryOp(UOp::Always, term) => {
                return Err(ExtractionError::AnyFuture(*term.clone()))
            }
            assert => return Err(ExtractionError::AssertWithoutAlways(assert.clone())),
        };
        let invariants = assert.invariants.iter().map(|s| s.x.clone()).collect();
        for invariant in &invariants {
            if FirstOrder::unrolling(invariant) != Some(0) {
                return Err(ExtractionError::AnyFuture(invariant.clone()));
            }
        }
        proofs.push(Proof { safety, invariants })
    }

    let next = Next::new(&module.signature);
    for term in inits.iter_mut().chain(&mut transitions).chain(&mut axioms) {
        *term = next.normalize(term);
    }
    for proof in &mut proofs {
        proof.safety = next.normalize(&proof.safety);
        for invariant in &mut proof.invariants {
            *invariant = next.normalize(invariant);
        }
    }

    Ok(DestructuredModule {
        inits,
        transitions,
        axioms,
        proofs,
    })
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Extract a first-order transition system from a Module.

use crate::syntax::*;
use crate::term::fo::FirstOrder;
use thiserror::Error;

/// Contains the different parts of the extracted transition system
pub struct Destructured {
    /// The initial conditions (assumes with no primes)
    pub inits: Vec<Term>,
    /// The transitions (assume-alwayses with one prime)
    pub transitions: Vec<Term>,
    /// The axioms (assume-alwayses with no primes)
    pub axioms: Vec<Term>,
    /// The safety properties (assert-alwayses with no primes)
    pub safeties: Vec<Term>,
    /// The proof blocks from the original module,
    /// which correspond to the safety property with matching index
    pub proofs: Vec<Vec<Term>>,
}

/// An error during transition system extraction
#[derive(Debug, Error)]
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
pub fn extract(module: &Module) -> Result<Destructured, ExtractionError> {
    let mut assumes = Vec::new();
    let mut asserts = Vec::new();
    let mut proofs: Vec<&[Spanned<Term>]> = Vec::new();
    for statement in &module.statements {
        match statement {
            ThmStmt::Assert(Proof { assert, invariants }) => {
                asserts.push(assert.x.clone());
                proofs.push(invariants);
            }
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

    let mut safeties = Vec::new();
    for assert in asserts {
        match assert {
            Term::UnaryOp(UOp::Always, term) if FirstOrder::unrolling(&term) == Some(0) => {
                safeties.push(*term);
            }
            Term::UnaryOp(UOp::Always, term) => return Err(ExtractionError::AnyFuture(*term)),
            assert => return Err(ExtractionError::AssertWithoutAlways(assert)),
        }
    }

    let proofs: Vec<Vec<Term>> = proofs
        .iter()
        .map(|proof| proof.iter().map(|s| s.x.clone()).collect())
        .collect();
    for proof in &proofs {
        for invariant in proof {
            if FirstOrder::unrolling(invariant) != Some(0) {
                return Err(ExtractionError::AnyFuture(invariant.clone()));
            }
        }
    }

    Ok(Destructured {
        inits,
        transitions,
        axioms,
        safeties,
        proofs,
    })
}

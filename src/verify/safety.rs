// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Prove safety temporal assertions using invariants.

use thiserror::Error;

use crate::{
    fly::syntax::{Term, UOp::Always},
    term::{FirstOrder, Next},
};

/// A temporal property expressed as an invariant problem.
#[derive(Debug, Clone)]
pub struct InvariantAssertion {
    pub init: Term,
    pub next: Term,
    pub assumed_inv: Term,
    pub inv: Term,
    pub proof_invs: Vec<Term>,
}

#[derive(Error, Debug)]
pub enum InvariantError {
    #[error("assertion is not of the form (always p)")]
    NotSafety,
    #[error("proof invariant is not a well-formed single-state fomula")]
    BadProofInvariant,
}

impl InvariantAssertion {
    /// Construct an invariant assertion to represent a temporal assertion.
    pub fn for_assert(
        assumes: &[&Term],
        assert: &Term,
        proof_invs: &[&Term],
    ) -> Result<Self, InvariantError> {
        let inv = match assert {
            Term::UnaryOp(Always, p) => *p.clone(),
            _ => return Err(InvariantError::NotSafety),
        };

        let mut init: Vec<Term> = vec![];
        let mut assumed_invs: Vec<Term> = vec![];
        let mut next: Vec<Term> = vec![];

        for &t in assumes {
            if let Term::UnaryOp(Always, t) = t {
                match FirstOrder::unrolling(t) {
                    Some(0) => assumed_invs.push(*t.clone()),
                    Some(1) => next.push(*t.clone()),
                    _ => (), // drop
                }
            } else if FirstOrder::unrolling(t) == Some(0) {
                init.push(t.clone())
            }
        }

        for &t in proof_invs {
            if FirstOrder::unrolling(t) != Some(0) {
                // TODO(oded): better error reporting
                return Err(InvariantError::BadProofInvariant);
            }
        }

        Ok(Self {
            init: Term::and(init),
            next: Next::normalize(&Term::and(next)),
            assumed_inv: Term::and(assumed_invs),
            inv,
            proof_invs: proof_invs.iter().map(|&t| t.clone()).collect(),
        })
    }

    fn inductive_invariant(&self) -> Term {
        let mut invs = vec![self.inv.clone()];
        invs.extend(self.proof_invs.iter().cloned());
        Term::and(invs)
    }

    pub fn initiation(&self) -> FirstOrder {
        let lhs = Term::and(vec![self.init.clone(), self.assumed_inv.clone()]);
        let rhs = self.inductive_invariant();
        FirstOrder::new(Term::implies(lhs, rhs))
    }

    pub fn consecution(&self) -> FirstOrder {
        // TODO: note that in this process we will generate p' even when p is immutable.
        //
        // Fixing this requires some stage (either the prime processing or the
        // sexp solver encoding) to be aware of the signature. It would help if
        // symbols were resolved once, so that at each occurrence of a function
        // it was easy to look it up.
        let lhs = Term::and(vec![
            self.inductive_invariant(),
            self.next.clone(),
            self.assumed_inv.clone(),
            Next::prime(&self.assumed_inv),
        ]);
        let rhs = Next::prime(&self.inductive_invariant());
        FirstOrder::new(Term::implies(lhs, rhs))
    }
}

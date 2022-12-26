// Copyright 2022 VMware, Inc.
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
    init: Term,
    next: Term,
    known_invs: Term,
    pub inv: Term,
}

#[derive(Error, Debug)]
pub enum InvariantError {
    #[error("assertion is not of the form (always p)")]
    NotSafety,
}

impl InvariantAssertion {
    /// Construct an invariant assertion to represent a temporal assertion.
    pub fn for_assert(assumes: &[&Term], assert: &Term) -> Result<Self, InvariantError> {
        let inv = match assert {
            Term::UnaryOp(Always, p) => *p.clone(),
            _ => return Err(InvariantError::NotSafety),
        };

        let mut init: Vec<Term> = vec![];
        let mut known_invs: Vec<Term> = vec![];
        let mut next: Vec<Term> = vec![];

        for &t in assumes {
            if let Term::UnaryOp(Always, t) = t {
                match FirstOrder::unrolling(t) {
                    Some(0) => known_invs.push(*t.clone()),
                    Some(1) => next.push(*t.clone()),
                    _ => (), // drop
                }
            } else if FirstOrder::unrolling(t) == Some(0) {
                init.push(t.clone())
            }
        }

        Ok(Self {
            init: Term::and(init),
            next: Term::and(next),
            known_invs: Term::and(known_invs),
            inv,
        })
    }

    pub fn inv_assertion(&self) -> FirstOrder {
        let lhs = Term::and(vec![self.init.clone(), self.known_invs.clone()]);
        let rhs = self.inv.clone();
        FirstOrder::new(Term::implies(lhs, rhs))
    }

    pub fn next_assertion(&self) -> FirstOrder {
        // TODO: note that in this process we will generate p' even when p is immutable.
        //
        // Fixing this requires some stage (either the prime processing or the
        // sexp solver encoding) to be aware of the signature. It would help if
        // symbols were resolved once, so that at each occurrence of a function
        // it was easy to look it up.
        let lhs = Term::and(vec![
            self.inv.clone(),
            self.next.clone(),
            self.known_invs.clone(),
            Next::prime(&self.known_invs),
        ]);
        let rhs = Next::prime(&self.inv);
        FirstOrder::new(Term::implies(lhs, rhs))
    }
}

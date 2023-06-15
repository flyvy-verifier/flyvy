// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Normalize primes (next) down to constants.

use crate::fly::syntax::{Signature, Term, UOp};

/// Wrap t in `next` primes.
fn with_primes(mut t: Term, next: usize) -> Term {
    for _ in 0..next {
        t = Term::UnaryOp(UOp::Prime, Box::new(t));
    }
    t
}

/// Push occurrences of prime inward in `t`, adding `next` primes at the bottom.
/// Keeps track of a set of bound variables `bound` that should not be primed.
fn with_next(sig: &Signature, t: &Term, bound: im::HashSet<String>, next: usize) -> Term {
    let go = |t| with_next(sig, t, bound.clone(), next);
    let go_box = |t| Box::new(go(t));
    match t {
        // increase next
        Term::UnaryOp(UOp::Prime, t) => with_next(sig, t, bound.clone(), next + 1),
        // apply accumulated next
        Term::Id(s) => with_primes(
            Term::Id(s.clone()),
            if bound.contains(s) || sig.is_immutable(s) {
                0
            } else {
                next
            },
        ),
        Term::App(f, p, xs) => {
            let n_primes = if sig.is_immutable(f) { 0 } else { p + next };
            Term::App(f.clone(), n_primes, xs.iter().map(go).collect())
        }

        // boring recursive cases
        Term::Literal(b) => Term::Literal(*b),
        Term::UnaryOp(op, t) => Term::UnaryOp(*op, go_box(t)),
        Term::BinOp(op, lhs, rhs) => Term::BinOp(*op, go_box(lhs), go_box(rhs)),
        Term::NAryOp(op, xs) => Term::NAryOp(*op, xs.iter().map(go).collect()),
        Term::Ite { cond, then, else_ } => Term::Ite {
            cond: go_box(cond),
            then: go_box(then),
            else_: go_box(else_),
        },
        Term::Quantified {
            quantifier,
            binders,
            body,
        } => Term::Quantified {
            quantifier: *quantifier,
            binders: binders.clone(),
            body: {
                let mut bound = bound.clone();
                bound.extend(binders.iter().map(|binder| binder.name.clone()));
                Box::new(with_next(sig, body, bound, next))
            },
        },
    }
}

/// Context for normalizing primes in terms.
pub struct Next<'a> {
    sig: &'a Signature,
}

impl<'a> Next<'a> {
    /// Create a new instance of `Next` that uses `sig` to resolve mutability of
    /// symbols.
    pub fn new(sig: &'a Signature) -> Self {
        Self { sig }
    }

    /// Normalize any occurrences of (p)' to push the prime as deep as possible,
    /// down to terms.
    pub fn normalize(&self, t: &Term) -> Term {
        let bound = im::hashset! {};
        with_next(self.sig, t, bound, 0)
    }

    /// Add a prime to t and push it as far as possible.
    pub fn prime(&self, t: &Term) -> Term {
        self.normalize(&Term::UnaryOp(UOp::Prime, Box::new(t.clone())))
    }
}

#[cfg(test)]
mod tests {
    use crate::fly::parser::{parse_signature, term};

    use super::Next;

    #[test]
    fn test_normalize() {
        let sig = parse_signature(
            r#"
        sort s
        mutable z: bool
        mutable r(s): bool
    "#,
        );
        assert_eq!(
            Next::new(&sig).normalize(&term("r'(x) | z")),
            term("r'(x) | z")
        );
        assert_eq!(
            Next::new(&sig).normalize(&term("(r(x) | z & forall x:t. p(x)')'")),
            // this x gets primed because it's a free variable
            term("r'(x') | z' & forall x:t. p''(x)")
        );
        assert_eq!(
            Next::new(&sig).prime(&term("r(x) | z & forall x:t. p(x)'")),
            term("r'(x') | z' & forall x:t. p''(x)")
        );
    }

    #[test]
    fn test_normalize_immutable() {
        // same as above but this time r is immutable so r' should evaluate to r
        let sig = parse_signature(
            r#"
        sort s
        mutable z: bool
        immutable r(s): bool
        mutable p(s): bool
    "#,
        );
        assert!(!sig.is_immutable("z"));
        assert!(sig.is_immutable("r"));
        assert_eq!(
            Next::new(&sig).normalize(&term("r'(x) | z")),
            term("r(x) | z")
        );
        assert_eq!(
            Next::new(&sig).normalize(&term("(r(x) | z & forall x:t. p(x)')'")),
            // this x gets primed because it's a free variable
            term("r(x') | z' & forall x:t. p''(x)")
        );
        assert_eq!(
            Next::new(&sig).prime(&term("r(x) | z & forall x:t. p(x)'")),
            term("r(x') | z' & forall x:t. p''(x)")
        );
    }
}

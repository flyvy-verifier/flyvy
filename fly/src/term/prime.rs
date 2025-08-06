// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Normalize primes (next) down to constants.

use core::panic;

use crate::syntax::{Module, Proof, Signature, Spanned, Term, ThmStmt, UOp};

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

/// Flip all occurrences of primes in a term to unprimed and vice versa.
fn flip_primed_unprimed(
    sig: &Signature,
    t: &Term,
    bound: im::HashSet<String>,
    next: usize,
) -> Term {
    assert!(
        next == 0 || next == 1,
        "term {} has {} primes, expected 0 or 1",
        t,
        next,
    );
    let go = |t| flip_primed_unprimed(sig, t, bound.clone(), next);
    let go_box = |t| Box::new(go(t));
    match t {
        // increase next
        Term::UnaryOp(UOp::Prime, t) => flip_primed_unprimed(sig, t, bound.clone(), next + 1),
        // apply accumulated next
        Term::Id(s) => with_primes(
            Term::Id(s.clone()),
            if bound.contains(s) || sig.is_immutable(s) {
                0
            } else {
                1 - next
            },
        ),
        Term::App(f, p, xs) => {
            let n_primes = if sig.is_immutable(f) { 0 } else { p + next };
            assert!(
                n_primes == 0 || n_primes == 1,
                "term {} has {} primes ({} external), expected 0 or 1",
                t,
                n_primes,
                next
            );
            Term::App(
                f.clone(),
                if sig.is_immutable(f) { 0 } else { 1 - n_primes },
                xs.iter().map(go).collect(),
            )
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
                Box::new(flip_primed_unprimed(sig, body, bound, next))
            },
        },
    }
}

fn has_primes(t: &Term) -> bool {
    match t {
        Term::Literal(_) | Term::Id(_) => false,
        Term::App(_, primes, terms) => *primes > 0 || terms.iter().any(has_primes),
        Term::UnaryOp(UOp::Prime, _) => true,
        Term::UnaryOp(_, t) => has_primes(t),
        Term::BinOp(_, t1, t2) => has_primes(t1) || has_primes(t2),
        Term::NAryOp(_, terms) => terms.iter().any(has_primes),
        Term::Ite { cond, then, else_ } => {
            has_primes(cond) || has_primes(then) || has_primes(else_)
        }
        Term::Quantified {
            quantifier: _,
            binders: _,
            body,
        } => has_primes(body),
    }
}

/// Reverse the module, flipping all primes to unprimed and vice versa.
pub fn reverse_module(m: &Module) -> Module {
    let mut inits: Vec<Term> = vec![];
    let mut safeties: Vec<Term> = vec![];
    let mut transitions: Vec<Term> = vec![];
    let mut statements: Vec<ThmStmt> = vec![];

    let next = Next::new(&m.signature);

    for st in &m.statements {
        match st {
            ThmStmt::Assume(term) => match term {
                Term::UnaryOp(UOp::Always, t) => {
                    if has_primes(t) {
                        transitions.push(next.flip_primed_unprimed(&next.normalize(t)))
                    } else {
                        statements.push(st.clone())
                    }
                }
                _ => inits.push(term.clone()),
            },
            ThmStmt::Assert(proof) => match &proof.assert.x {
                Term::UnaryOp(UOp::Always, t) => safeties.push(t.as_ref().clone()),
                _ => panic!("expected always term in assert, got {}", proof.assert.x),
            },
        }
    }

    statements.push(ThmStmt::Assume(Term::not(Term::and(safeties))));
    for tr in transitions {
        statements.push(ThmStmt::Assume(Term::always(tr)))
    }
    statements.push(ThmStmt::Assert(Proof {
        assert: Spanned {
            x: Term::always(Term::not(Term::and(inits))),
            span: None,
        },
        invariants: vec![],
    }));

    Module {
        signature: m.signature.clone(),
        defs: m.defs.clone(),
        statements,
    }
}

/// removes occurrences of prime  in `t`.
pub fn clear_next(t: Term) -> Term {
    match t {
        Term::UnaryOp(UOp::Prime, t) => clear_next(*t),
        Term::App(f, _, xs) => Term::App(f, 0, xs.iter().map(|t| clear_next(t.clone())).collect()),
        Term::UnaryOp(op, t) => Term::UnaryOp(op, Box::new(clear_next(*t))),
        Term::Literal(b) => Term::Literal(b),
        Term::BinOp(op, lhs, rhs) => {
            Term::BinOp(op, Box::new(clear_next(*lhs)), Box::new(clear_next(*rhs)))
        }
        Term::NAryOp(op, terms) => Term::NAryOp(op, terms.into_iter().map(clear_next).collect()),
        Term::Quantified {
            quantifier: quant,
            binders,
            body,
        } => Term::Quantified {
            quantifier: quant,
            binders,
            body: Box::new(clear_next(*body)),
        },
        Term::Id(_) => t,
        _ => panic!("got illegal operator in negate and simplify"),
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

    /// Flip all occurrences of primes in a term to unprimed and vice versa.
    pub fn flip_primed_unprimed(&self, t: &Term) -> Term {
        let bound = im::hashset! {};
        flip_primed_unprimed(self.sig, t, bound, 0)
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::{parse_signature, term};

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

    #[test]
    fn test_flip_primed_unprimed() {
        let sig = parse_signature(
            r#"
        sort s
        immutable c: s
        mutable z: bool
        mutable r(s): bool
    "#,
        );
        assert_eq!(
            Next::new(&sig).flip_primed_unprimed(&term("r'(c) | z")),
            term("r(c) | z'")
        );
        assert_eq!(
            Next::new(&sig).flip_primed_unprimed(&term("r(x') | z & forall x:s. p'(x)")),
            // this x gets primed because it's a free variable
            term("r'(x) | z' & forall x:s. p(x)")
        );
    }
}

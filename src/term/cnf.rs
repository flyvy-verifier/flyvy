// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Convert terms to CNF.
//!
//! See the documentation for [`Cnf`] for details.

// turned out to not be needed (yet)
#![allow(dead_code)]
use crate::fly::{
    printer,
    syntax::{NOp, Term, UOp},
};

use NOp::And;
use Term::{NAryOp, UnaryOp};
use UOp::Always;

/// Conjunctive normal form terms.
///
/// These terms have the shape (p1 & ... & pn) or (always (p1 & ... & pn)),
/// where the terms are not conjunctions.
///
/// Creates a single conjunction so that the root is always NAryOp(And, _) or
/// UnaryOp(Always, NAryOp(And, _)).
///
/// Does not recurse into forall and exists and normalize there.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cnf(pub Term);

fn not_and(t: &Term) {
    assert!(
        !matches!(t, NAryOp(And, _)),
        "contains a conjunction {}",
        printer::term(t)
    );
}

fn flat_disjunction(t: &Term) {
    match t {
        NAryOp(And, terms) => {
            for t in terms {
                not_and(t);
            }
        }
        _ => panic!("{} is not a conjunction", printer::term(t)),
    }
}

/// The well-formedness predicate for [`Cnf`].
fn cnf(t: &Term) {
    match t {
        NAryOp(_, _) => flat_disjunction(t),
        UnaryOp(Always, t) => flat_disjunction(t),
        _ => panic!("{} is not an always or conjunction", printer::term(t)),
    }
}

/// If t is an always, get its body. Collapses consecutive always.
fn get_always(t: &Term) -> Option<Term> {
    match t {
        UnaryOp(Always, t) => Some(get_always(t).unwrap_or_else(|| *t.clone())),
        _ => None,
    }
}

fn conjuncts(t: Term) -> Vec<Term> {
    match t {
        NAryOp(And, ts) => ts.into_iter().flat_map(conjuncts).collect(),
        _ => vec![t],
    }
}

impl Cnf {
    pub fn new(t: Term) -> Self {
        let t = if let Some(body) = get_always(&t) {
            UnaryOp(Always, Box::new(body))
        } else {
            NAryOp(And, conjuncts(t))
        };
        cnf(&t);
        Self(t)
    }
}

#[cfg(test)]
mod tests {
    use crate::fly::parser::parse_term;
    use crate::fly::syntax::{NOp, Term};

    use super::{cnf, Cnf};

    #[test]
    fn test_already_cnf() {
        cnf(&parse_term("p & q & r & (a | b)").unwrap());
        cnf(&parse_term("always p & q & r & (a | b)").unwrap());
    }

    #[test]
    fn test_cnf_and() {
        let t = Term::NAryOp(
            NOp::And,
            vec![parse_term("a").unwrap(), parse_term("b & c").unwrap()],
        );
        let cnf = Cnf::new(t.clone());
        // make sure this test is non-trivial
        assert_ne!(t, cnf.0);
        assert_eq!(cnf.0, parse_term("a & b & c").unwrap());
    }

    #[test]
    fn test_cnf_always() {
        let t = parse_term("always (always (always p & q))").unwrap();
        let cnf = Cnf::new(t.clone());
        assert_ne!(t, cnf.0);
        assert_eq!(cnf.0, parse_term("always p & q").unwrap());
    }

    #[test]
    fn test_cnf_single() {
        let t = parse_term("p | q").unwrap();
        let cnf = Cnf::new(t.clone());
        assert_eq!(cnf.0, Term::NAryOp(NOp::And, vec![t]));
    }
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Convert terms to CNF.
//!
//! See the documentation for [`Cnf`] for details.

use crate::syntax::Term::{App, Id, Quantified};
use crate::syntax::{NOp, Term, UOp};
use crate::{printer, syntax};
use NOp::And;
use Term::{BinOp, Literal, NAryOp, UnaryOp};
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

fn cartesian_product(v: &[Vec<Term>]) -> Vec<Vec<Term>> {
    if v.is_empty() {
        return vec![vec![]];
    }

    let mut result: Vec<Vec<Term>> = vec![];

    for i in &v[0] {
        for rest in cartesian_product(&v[1..]) {
            let mut prod = vec![i.clone()];
            prod.extend(rest);
            result.push(prod);
        }
    }

    result
}

fn body_to_clauses(t: Term, is_negated: bool) -> Vec<Term> {
    match t {
        Literal(b) => vec![Term::Literal(b ^ !is_negated)],
        UnaryOp(UOp::Not, t) => body_to_clauses(*t, !is_negated),
        UnaryOp(..) => panic!("got UnaryOp other than Not!"),
        BinOp(syntax::BinOp::NotEquals, lhs, rhs) => {
            if is_negated {
                vec![BinOp(syntax::BinOp::Equals, lhs, rhs)]
            } else {
                vec![BinOp(syntax::BinOp::NotEquals, lhs, rhs)]
            }
        }
        BinOp(syntax::BinOp::Equals, lhs, rhs) => {
            if !is_negated {
                vec![BinOp(syntax::BinOp::Equals, lhs, rhs)]
            } else {
                vec![BinOp(syntax::BinOp::NotEquals, lhs, rhs)]
            }
        }
        BinOp(syntax::BinOp::Implies, lhs, rhs) => {
            body_to_clauses(NAryOp(NOp::Or, vec![Term::negate(*lhs), *rhs]), is_negated)
        }
        BinOp(syntax::BinOp::Iff, lhs, rhs) => body_to_clauses(
            NAryOp(
                NOp::And,
                vec![
                    NAryOp(NOp::Or, vec![Term::negate(*lhs.clone()), *rhs.clone()]),
                    NAryOp(NOp::Or, vec![Term::negate(*rhs), *lhs]),
                ],
            ),
            is_negated,
        ),
        NAryOp(NOp::And, terms) => {
            if is_negated {
                body_to_clauses(
                    NAryOp(NOp::Or, terms.into_iter().map(Term::negate).collect()),
                    !is_negated,
                )
            } else {
                let mut res: Vec<Term> = Vec::new();
                for t in terms {
                    res.extend(body_to_clauses(t, is_negated));
                }
                res
            }
        }
        NAryOp(NOp::Or, terms) => {
            if is_negated {
                body_to_clauses(
                    NAryOp(NOp::And, terms.into_iter().map(Term::negate).collect()),
                    !is_negated,
                )
            } else {
                let sub_formulas: Vec<Vec<Term>> = terms
                    .into_iter()
                    .map(|t| body_to_clauses(t, false))
                    .collect();
                let product = cartesian_product(&sub_formulas);
                product
                    .into_iter()
                    .map(|ts: Vec<Term>| NAryOp(NOp::Or, ts))
                    .collect()
            }
        }
        Id(_) | App(_, _, _) => {
            if is_negated {
                vec![Term::negate(t)]
            } else {
                vec![t]
            }
        }
        _ => panic!("got illegal operator"),
    }
}

/// Convert a quantified term to separate clauses forming a cnf term
pub fn term_to_cnf_clauses(t: &Term) -> Vec<Term> {
    return match t {
        Quantified {
            quantifier: syntax::Quantifier::Forall,
            body,
            binders,
        } => body_to_clauses(*body.clone(), false)
            .into_iter()
            .map(|b| Quantified {
                quantifier: syntax::Quantifier::Forall,
                body: Box::new(b),
                binders: binders.clone(),
            })
            .collect(),
        _ => body_to_clauses(t.clone(), false),
    };
}

impl Cnf {
    /// Build a Term in CNF out of any Term
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
    use crate::parser::term;
    use crate::syntax::{NOp, Term};
    use crate::term::cnf::{body_to_clauses, term_to_cnf_clauses};
    use std::collections::HashSet;

    use super::{cnf, Cnf};

    #[test]
    fn test_already_cnf() {
        cnf(&term("p & q & r & (a | b)"));
        cnf(&term("always p & q & r & (a | b)"));
    }

    #[test]
    fn test_cnf_and() {
        let t = Term::NAryOp(NOp::And, vec![term("a"), term("b & c")]);
        let cnf = Cnf::new(t.clone());
        // make sure this test is non-trivial
        assert_ne!(t, cnf.0);
        assert_eq!(cnf.0, term("a & b & c"));
    }

    #[test]
    fn test_cnf_always() {
        let t = term("always (always (always p & q))");
        let cnf = Cnf::new(t.clone());
        assert_ne!(t, cnf.0);
        assert_eq!(cnf.0, term("always p & q"));
    }

    #[test]
    fn test_cnf_single() {
        let t = term("p | q");
        let cnf = Cnf::new(t.clone());
        assert_eq!(cnf.0, Term::NAryOp(NOp::And, vec![t]));
    }

    #[test]
    fn test_cnf_eq() {
        let t = term("p = q");
        let cnf = Cnf::new(t);
        assert_eq!(cnf.0, Term::NAryOp(NOp::And, vec![term("p = q")]));
    }

    #[test]
    fn test_body_to_clauses() {
        let t = term("(a | (b & c)) | (e & (f = g))");
        let terms: HashSet<_> = body_to_clauses(t, false).into_iter().collect();
        let expected: HashSet<_> = vec![
            term("a | b | e"),
            term("a | c | e"),
            term("a | b | (f = g)"),
            term("a | c | (f = g)"),
        ]
        .into_iter()
        .collect();
        assert_eq!(terms, expected);
    }

    #[test]
    fn test_term_to_clauses() {
        let t = term("forall a:t, b:t. (a & b)");
        let terms: HashSet<_> = term_to_cnf_clauses(&t).into_iter().collect();
        let expected: HashSet<_> = vec![term("forall a:t, b:t. a"), term("forall a:t, b:t. b")]
            .into_iter()
            .collect();
        assert_eq!(terms, expected);
    }
}

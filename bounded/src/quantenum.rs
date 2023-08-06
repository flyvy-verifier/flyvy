// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A translation from terms with quantifiers to simplified terms without them.

use fly::{ouritertools::OurItertools, semantics::*, syntax::*};
use itertools::Itertools;
use std::collections::HashMap;
use thiserror::Error;

/// The result of enumerating the quantifiers of a term.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Enumerated {
    /// Conjunction. `And(vec![])` represents true.
    And(Vec<Enumerated>),
    /// Disjunction. `Or(vec![])` represents false.
    Or(Vec<Enumerated>),
    /// Negation.
    Not(Box<Enumerated>),
    /// Equality.
    Eq(Box<Enumerated>, Box<Enumerated>),
    /// Variable.
    App(String, usize, Vec<Element>),
}

/// Map from uninterpreted sort names to their sizes.
// Here is the one place we use a std HashMap. It's not a performance problem because it's not used
// in the inner loop of the model checker, and it provides a more ergonomic public api to this module.
pub type UniverseBounds = std::collections::HashMap<String, usize>;

/// Get the size of a sort from the given universe.
pub fn cardinality(universe: &UniverseBounds, sort: &Sort) -> usize {
    match sort {
        Sort::Bool => 2,
        Sort::Uninterpreted(sort) => *universe.get(sort).unwrap(),
    }
}

/// The result of a failed quantifier enumeration attempt.
#[derive(Debug, Error)]
pub enum EnumerationError {
    /// Temporal operators are not supported by Enumerated
    #[error("found temporal operators in {0}")]
    TemporalOperator(Term),
    /// The maximum number of primes is bounded by an argument
    #[error("too many primes in {0}")]
    TooManyPrimes(Term),
    /// An identifier that was never bound exists
    #[error("unknown identifier {0}")]
    UnknownId(Term),
    /// A term could not be statically evaluated to a constant sort element
    #[error("could not translate to a constant {0}")]
    NotAnElement(Term),
}

/// Convert a `Term` with quantifiers into an `Enumerated` term without them.
/// Fails if the input term contains temporal operators that can't be normalized into an `App`.
pub fn enumerate_quantifiers(
    term: &Term,
    signature: &Signature,
    universe: &UniverseBounds,
    max_primes: usize,
) -> Result<Enumerated, EnumerationError> {
    let term = nullary_id_to_app(term, &signature.relations);
    let term = fly::term::prime::Next::new(signature).normalize(&term);
    term_to_enumerated(&term, universe, max_primes, &HashMap::default())
}

fn nullary_id_to_app(term: &Term, rs: &[RelationDecl]) -> Term {
    let go = |term| nullary_id_to_app(term, rs);
    match term {
        Term::Id(id) if rs.iter().any(|r| r.name == *id) => Term::App(id.clone(), 0, vec![]),

        Term::Literal(b) => Term::Literal(*b),
        Term::Id(id) => Term::Id(id.clone()),
        Term::App(name, primes, args) => {
            Term::App(name.clone(), *primes, args.iter().map(go).collect())
        }
        Term::UnaryOp(op, x) => Term::UnaryOp(*op, Box::new(go(x))),
        Term::BinOp(op, x, y) => Term::BinOp(*op, Box::new(go(x)), Box::new(go(y))),
        Term::NAryOp(op, xs) => Term::NAryOp(*op, xs.iter().map(go).collect()),
        Term::Ite { cond, then, else_ } => Term::Ite {
            cond: Box::new(go(cond)),
            then: Box::new(go(then)),
            else_: Box::new(go(else_)),
        },
        Term::Quantified {
            quantifier,
            binders,
            body,
        } => Term::Quantified {
            quantifier: *quantifier,
            binders: binders.to_vec(),
            body: Box::new(go(body)),
        },
    }
}

impl Enumerated {
    fn always_true() -> Enumerated {
        Enumerated::And(vec![])
    }

    fn always_false() -> Enumerated {
        Enumerated::Or(vec![])
    }

    fn and(terms: impl IntoIterator<Item = Enumerated>) -> Enumerated {
        let mut terms: Vec<_> = terms
            .into_iter()
            .flat_map(Enumerated::get_and)
            .sorted()
            .collect();
        terms.dedup();

        if terms.iter().any(|term| *term == Enumerated::always_false()) {
            Enumerated::always_false()
        } else if terms.len() == 1 {
            terms.pop().unwrap()
        } else {
            Enumerated::And(terms)
        }
    }

    fn or(terms: impl IntoIterator<Item = Enumerated>) -> Enumerated {
        let mut terms: Vec<_> = terms
            .into_iter()
            .flat_map(Enumerated::get_or)
            .sorted()
            .collect();
        terms.dedup();

        if terms.iter().any(|term| *term == Enumerated::always_true()) {
            Enumerated::always_true()
        } else if terms.len() == 1 {
            terms.pop().unwrap()
        } else {
            Enumerated::Or(terms)
        }
    }

    fn get_and(self) -> Vec<Enumerated> {
        match self {
            Enumerated::And(terms) => terms,
            term => vec![term],
        }
    }

    fn get_or(self) -> Vec<Enumerated> {
        match self {
            Enumerated::Or(terms) => terms,
            term => vec![term],
        }
    }
}

fn term_to_enumerated(
    term: &Term,
    universe: &UniverseBounds,
    max_primes: usize,
    assignments: &HashMap<String, Element>,
) -> Result<Enumerated, EnumerationError> {
    let go = |term| term_to_enumerated(term, universe, max_primes, assignments);
    let element = |term: &Term| match term {
        Term::Id(id) => match assignments.get(id) {
            Some(x) => Ok(*x),
            None => Err(EnumerationError::UnknownId(term.clone())),
        },
        term => match term_to_enumerated(term, universe, max_primes, assignments) {
            Ok(formula) if formula == Enumerated::always_true() => Ok(1),
            Ok(formula) if formula == Enumerated::always_false() => Ok(0),
            _ => Err(EnumerationError::NotAnElement(term.clone())),
        },
    };

    let enumerated = match term {
        Term::Literal(true) => Enumerated::always_true(),
        Term::Literal(false) => Enumerated::always_false(),
        Term::Id(_) => match element(term)? {
            1 => Enumerated::always_true(),
            0 => Enumerated::always_false(),
            _ => unreachable!(),
        },
        Term::App(name, primes, args) => {
            if *primes > max_primes {
                return Err(EnumerationError::TooManyPrimes(term.clone()));
            }
            let args = args.iter().map(element).collect::<Result<Vec<_>, _>>()?;
            Enumerated::App(name.clone(), *primes, args)
        }
        Term::UnaryOp(UOp::Not, term) => Enumerated::Not(Box::new(go(term)?)),
        Term::BinOp(BinOp::Equals | BinOp::Iff, a, b) => match (element(a), element(b)) {
            (Ok(a), Ok(b)) if a == b => Enumerated::always_true(),
            (Ok(a), Ok(b)) if a != b => Enumerated::always_false(),
            _ => Enumerated::Eq(Box::new(go(a)?), Box::new(go(b)?)),
        },
        Term::BinOp(BinOp::NotEquals, a, b) => Enumerated::Not(Box::new(go(&Term::BinOp(
            BinOp::Equals,
            a.clone(),
            b.clone(),
        ))?)),
        Term::BinOp(BinOp::Implies, a, b) => {
            Enumerated::or(vec![Enumerated::Not(Box::new(go(a)?)), go(b)?])
        }
        Term::NAryOp(NOp::And, terms) => {
            Enumerated::and(terms.iter().map(go).collect::<Result<Vec<_>, _>>()?)
        }
        Term::NAryOp(NOp::Or, terms) => {
            Enumerated::or(terms.iter().map(go).collect::<Result<Vec<_>, _>>()?)
        }
        Term::Ite { cond, then, else_ } => Enumerated::or([
            Enumerated::and([go(cond)?, go(then)?]),
            Enumerated::and([Enumerated::Not(Box::new(go(cond)?)), go(else_)?]),
        ]),
        Term::Quantified {
            quantifier,
            binders,
            body,
        } => {
            let terms = binders
                .iter()
                .map(|b| cardinality(universe, &b.sort))
                .map(|card| (0..card).collect::<Vec<Element>>())
                .multi_cartesian_product_fixed()
                .map(|elements| {
                    let mut new_assignments = assignments.clone();
                    for (binder, element) in binders.iter().zip_eq(elements) {
                        new_assignments.insert(binder.name.clone(), element);
                    }
                    term_to_enumerated(body, universe, max_primes, &new_assignments)
                })
                .collect::<Result<Vec<_>, _>>()?;
            match quantifier {
                Quantifier::Forall => Enumerated::and(terms),
                Quantifier::Exists => Enumerated::or(terms),
            }
        }
        Term::UnaryOp(UOp::Prime | UOp::Always | UOp::Eventually, _)
        | Term::UnaryOp(UOp::Next | UOp::Previous, _)
        | Term::BinOp(BinOp::Until | BinOp::Since, ..) => {
            return Err(EnumerationError::TemporalOperator(term.clone()))
        }
    };
    Ok(enumerated)
}

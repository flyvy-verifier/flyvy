// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Perform substitutions of Id terms by other terms.

use std::{collections::HashMap, fmt::Display};

use crate::syntax::{Term, UOp};

/// A possible substitute for something else in a generalized substitution that supports renaming symbols:
/// either a new name (with a new number of primes) or a [`Term`] (only if the thing being replaced is some [`Term::Id`]).
#[derive(Clone, Debug)]
pub enum Substitutable {
    /// A new name for a symbols, along with a number of primes
    Name(String, usize),
    /// A [`Term`]
    Term(Term),
}

impl Substitutable {
    /// Return a name with no primes.
    pub fn name<S: Into<String>>(s: S) -> Self {
        Self::Name(s.into(), 0)
    }

    fn to_term(&self) -> Term {
        match self {
            Substitutable::Name(name, primes) => {
                let mut t = Term::id(name);
                for _ in 0..*primes {
                    t = Term::UnaryOp(UOp::Prime, Box::new(t));
                }
                t
            }
            Substitutable::Term(t) => t.clone(),
        }
    }
}

impl Display for Substitutable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Substitutable::Name(name, primes) => write!(f, "{name}{}", "\'".repeat(*primes)),
            Substitutable::Term(t) => write!(f, "{t}"),
        }
    }
}

/// A map from identifiers to Terms.
pub type Substitution = HashMap<String, Term>;
/// A generalized substitution that can also rename symbols and change the number of primes.
pub type NameSubstitution = HashMap<(String, usize), Substitutable>;

/// Perform a substitution.
pub fn substitute(term: &Term, substitution: &Substitution) -> Term {
    substitute_rec(term, substitution, &im::HashSet::new())
}

/// Rename functions and relations and modify their number of primes. The given term is required
/// to be normalized, with the primes pushed as deep as possible (e.g., using [`crate::term::prime::Next::normalize`]).
/// The given substitution maps a function or relation name with certain number of primes
/// to a new function of relation name with a new number of primes.
pub fn rename_symbols(term: &Term, substitution: &NameSubstitution) -> Term {
    rename_symbols_rec(term, substitution, &im::HashSet::new(), 0)
}

fn rename_symbols_rec(
    term: &Term,
    substitution: &NameSubstitution,
    bound_ids: &im::HashSet<String>,
    primes: usize,
) -> Term {
    if primes > 0 && !matches!(term, Term::Id(_)) {
        panic!("term is not normalized")
    }

    match term {
        Term::Literal(_) | Term::Int(_) => term.clone(),
        Term::Id(s) => match substitution.get(&(s.clone(), primes)) {
            Some(x) if primes > 0 || !bound_ids.contains(s) => x.to_term(),
            _ => Term::id(s),
        },

        Term::App(f, p, args) => {
            let v = substitution.get(&(f.clone(), *p));
            let (new_f, new_p) = match v {
                Some(Substitutable::Name(new_f, new_p)) if !bound_ids.contains(f) => {
                    (new_f.clone(), *new_p)
                }
                Some(Substitutable::Term(_)) => {
                    panic!("cannot rename function application to term")
                }
                _ => (f.clone(), *p),
            };

            Term::App(
                new_f,
                new_p,
                args.iter()
                    .map(|a| rename_symbols_rec(a, substitution, bound_ids, primes))
                    .collect(),
            )
        }

        Term::UnaryOp(UOp::Next | UOp::Prime, arg) => {
            rename_symbols_rec(arg, substitution, bound_ids, primes + 1)
        }

        Term::UnaryOp(UOp::Previous, arg) => {
            assert!(primes > 0);
            rename_symbols_rec(arg, substitution, bound_ids, primes - 1)
        }

        Term::UnaryOp(UOp::Not, arg) => Term::UnaryOp(
            UOp::Not,
            Box::new(rename_symbols_rec(arg, substitution, bound_ids, primes)),
        ),

        Term::BinOp(op, arg1, arg2) => Term::BinOp(
            *op,
            Box::new(rename_symbols_rec(arg1, substitution, bound_ids, primes)),
            Box::new(rename_symbols_rec(arg2, substitution, bound_ids, primes)),
        ),

        Term::NAryOp(op, args) => Term::NAryOp(
            *op,
            args.iter()
                .map(|a| rename_symbols_rec(a, substitution, bound_ids, primes))
                .collect(),
        ),

        Term::Ite { cond, then, else_ } => Term::Ite {
            cond: Box::new(rename_symbols_rec(cond, substitution, bound_ids, primes)),
            then: Box::new(rename_symbols_rec(then, substitution, bound_ids, primes)),
            else_: Box::new(rename_symbols_rec(else_, substitution, bound_ids, primes)),
        },

        Term::Quantified {
            quantifier,
            binders,
            body,
        } => {
            let mut new_bound_ids = bound_ids.clone();
            new_bound_ids.extend(binders.iter().map(|b| b.name.clone()));
            Term::Quantified {
                quantifier: *quantifier,
                binders: binders.clone(),
                body: Box::new(rename_symbols_rec(
                    body,
                    substitution,
                    &new_bound_ids,
                    primes,
                )),
            }
        }

        Term::NumOp(op, x, y) => Term::NumOp(
            *op,
            Box::new(rename_symbols_rec(x, substitution, bound_ids, primes)),
            Box::new(rename_symbols_rec(y, substitution, bound_ids, primes)),
        ),

        Term::NumRel(rel, x, y) => Term::NumRel(
            *rel,
            Box::new(rename_symbols_rec(x, substitution, bound_ids, primes)),
            Box::new(rename_symbols_rec(y, substitution, bound_ids, primes)),
        ),

        _ => panic!("unsupported term in subsutitution: {term:?}"),
    }
}

/// Perform a substitution, accounting for the given bound variables
fn substitute_rec(
    term: &Term,
    substitution: &Substitution,
    bound_vars: &im::HashSet<String>,
) -> Term {
    match term {
        Term::Literal(b) => Term::Literal(*b),
        Term::Id(s) => {
            if !bound_vars.contains(s) && substitution.contains_key(s) {
                substitution[s].clone()
            } else {
                Term::id(s)
            }
        }

        Term::App(f, p, args) => Term::App(
            f.clone(),
            *p,
            args.iter()
                .map(|a| substitute_rec(a, substitution, bound_vars))
                .collect(),
        ),

        Term::UnaryOp(UOp::Not, arg) => Term::UnaryOp(
            UOp::Not,
            Box::new(substitute_rec(arg, substitution, bound_vars)),
        ),

        Term::BinOp(op, arg1, arg2) => Term::BinOp(
            *op,
            Box::new(substitute_rec(arg1, substitution, bound_vars)),
            Box::new(substitute_rec(arg2, substitution, bound_vars)),
        ),

        Term::NAryOp(op, args) => Term::NAryOp(
            *op,
            args.iter()
                .map(|a| substitute_rec(a, substitution, bound_vars))
                .collect(),
        ),

        Term::Ite { cond, then, else_ } => Term::Ite {
            cond: Box::new(substitute_rec(cond, substitution, bound_vars)),
            then: Box::new(substitute_rec(then, substitution, bound_vars)),
            else_: Box::new(substitute_rec(else_, substitution, bound_vars)),
        },

        Term::Quantified {
            quantifier,
            binders,
            body,
        } => {
            let mut new_bound_vars = bound_vars.clone();
            new_bound_vars.extend(binders.iter().map(|b| b.name.clone()));
            Term::Quantified {
                quantifier: *quantifier,
                binders: binders.clone(),
                body: Box::new(substitute_rec(body, substitution, &new_bound_vars)),
            }
        }

        _ => panic!("unsupported term in subsutitution: {term:?}"),
    }
}

#[cfg(test)]
#[allow(clippy::redundant_clone)]
mod tests {
    use super::*;
    use crate::parser::term;

    #[test]
    fn test_subst_qf() {
        let x = Term::Id("x".to_string());
        let y = Term::Id("y".to_string());

        let t1 = term("(x | z) -> !y");
        let t1_subx = term("(y | z) -> !y");
        let t1_suby = term("(x | z) -> !x");
        let t1_subt = term("(((x | z) -> !y) | y) -> !x");

        let mut subx = Substitution::new();
        subx.insert("x".to_string(), y.clone());
        let mut suby = Substitution::new();
        suby.insert("y".to_string(), x.clone());
        let mut subt = Substitution::new();
        subt.insert("x".to_string(), t1.clone());
        subt.insert("y".to_string(), x.clone());
        subt.insert("z".to_string(), y.clone());

        assert_eq!(substitute(&t1, &subx), t1_subx);
        assert_eq!(substitute(&t1, &suby), t1_suby);
        assert_eq!(substitute(&t1, &subt), t1_subt);
    }
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Converts `Term`s to S-expressions.

use fly::syntax::{BinOp, Binder, NOp, NumOp, NumRel, Quantifier, Sort, Term, UOp};
pub use smtlib::sexp::parse;
use smtlib::sexp::{app, atom_i, atom_s, sexp_l, Sexp};

/// Convert a `Sort` to an S-expression.
pub fn sort(s: &Sort) -> Sexp {
    match s {
        Sort::Bool => atom_s("Bool"),
        Sort::Int => atom_s("Int"),
        Sort::Array { index, element } => app("Array", [sort(index), sort(element)]),
        Sort::Uninterpreted(s) => atom_s(s),
    }
}

fn binder(b: &Binder) -> Sexp {
    app(&b.name, vec![sort(&b.sort)])
}

fn term_primes(t: &Term, num_primes: usize) -> Sexp {
    if !matches!(t, Term::UnaryOp(UOp::Prime, _) | Term::Id(_)) {
        assert_eq!(
            num_primes, 0,
            "by the time we convert to smtlib, the only primes allowed are over identifiers (t={t})"
        );
        // TODO(oded): simplify the conversion based on this assumption
    }
    let term = |t: &Term| term_primes(t, num_primes);
    match t {
        Term::Literal(false) => atom_s("false"),
        Term::Literal(true) => atom_s("true"),
        Term::Id(s) => atom_s(format!("{s}{}", "'".repeat(num_primes))),
        Term::App(f, p, args) => {
            let head = vec![term_primes(&Term::Id(f.clone()), p + num_primes)].into_iter();
            let args = args.iter().map(term);
            sexp_l(head.chain(args))
        }
        Term::UnaryOp(op, arg) => {
            match op {
                UOp::Not => app("not", vec![term(arg)]),
                UOp::Prime => {
                    assert!(
                        matches!(**arg, Term::UnaryOp(UOp::Prime, _) | Term::Id(_)),
                       "by the time we convert to smtlib, the only primes allowed are over identifiers (t={t})",
                    );
                    // TODO(oded): simplify the conversion based on this assumption
                    term_primes(arg, num_primes + 1)
                }
                // TODO: temporal stuff should be eliminated before here
                UOp::Always | UOp::Eventually | UOp::Next | UOp::Previous => {
                    panic!("attempt to encode a temporal formula for smt")
                }
            }
        }
        Term::BinOp(op, arg1, arg2) => {
            let args = vec![term(arg1), term(arg2)];
            match op {
                BinOp::Equals => app("=", args),
                BinOp::NotEquals => app("distinct", args),
                BinOp::Implies => app("=>", args),
                BinOp::Iff => app("=", args),
                BinOp::Until | BinOp::Since => {
                    panic!("attempt to encode a temporal formula for smt")
                }
            }
        }
        Term::NAryOp(op, args) => {
            let args = args.iter().map(term).collect::<Vec<_>>();
            match (op, args.is_empty()) {
                (NOp::And, false) => app("and", args),
                (NOp::Or, false) => app("or", args),
                // the solver can error if no arguments are provided like `(and)`, `(or)`
                (NOp::And, true) => atom_s("true"),
                (NOp::Or, true) => atom_s("false"),
            }
        }
        Term::Ite { cond, then, else_ } => app("ite", vec![term(cond), term(then), term(else_)]),
        Term::Quantified {
            quantifier,
            binders,
            body,
        } => {
            let quantifier = match quantifier {
                Quantifier::Forall => "forall",
                Quantifier::Exists => "exists",
            };
            let binders = Sexp::List(binders.iter().map(binder).collect());
            let body = term(body);
            app(quantifier, vec![binders, body])
        }
        Term::Int(i) => {
            if i.is_positive() {
                atom_i(i.unsigned_abs())
            } else {
                app("-", [atom_i(i.unsigned_abs())])
            }
        }
        Term::NumRel(NumRel::Lt, x, y) => app("<", [term(x), term(y)]),
        Term::NumRel(NumRel::Leq, x, y) => app("<=", [term(x), term(y)]),
        Term::NumRel(NumRel::Geq, x, y) => app(">=", [term(x), term(y)]),
        Term::NumRel(NumRel::Gt, x, y) => app(">", [term(x), term(y)]),
        Term::NumOp(op, args) => {
            assert!(!args.is_empty());
            let args = args.iter().map(term).collect::<Vec<_>>();
            let op = match op {
                NumOp::Add => "+",
                NumOp::Sub => "-",
                NumOp::Mul => "*",
            };
            app(op, args)
        }
        Term::ArrayStore {
            array,
            index,
            value,
        } => app("store", [term(array), term(index), term(value)]),
        Term::ArraySelect { array, index } => app("select", [term(array), term(index)]),
    }
}

/// Convert a `Term` to an S-expression.
pub fn term(t: &Term) -> Sexp {
    term_primes(t, 0)
}

/// Convert a `Term` to an S-expression, then negate it.
pub fn negated_term(t: &Term) -> Sexp {
    app("not", [term(t)])
}

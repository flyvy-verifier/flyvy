// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use crate::fly::syntax::{BinOp, Binder, NOp, Quantifier, Sort, Term, UOp};
use crate::smtlib::sexp::{app, atom_s, sexp_l, Sexp};

pub fn sort(s: &Sort) -> Sexp {
    match s {
        Sort::Bool => atom_s("Bool"),
        Sort::Id(s) => atom_s(s),
    }
}

fn binder(b: &Binder) -> Sexp {
    match &b.typ {
        None => panic!("unexpected binder without sort"),
        Some(t) => app(&b.name, vec![sort(t)]),
    }
}

fn term_primes(t: &Term, num_primes: usize) -> Sexp {
    let term = |t: &Term| term_primes(t, num_primes);
    match t {
        Term::Id(s) => atom_s(format!("{s}{}", "'".repeat(num_primes))),
        Term::App(f, args) => {
            let head = vec![term(f)].into_iter();
            let args = args.iter().map(term);
            sexp_l(head.chain(args))
        }
        Term::UnaryOp(op, arg) => {
            match op {
                UOp::Not => app("not", vec![term(arg)]),
                UOp::Prime => term_primes(arg, num_primes + 1),
                // TODO: temporal stuff should be eliminated before here
                UOp::Always | UOp::Eventually => {
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
            }
        }
        Term::NAryOp(op, args) => {
            let args = args.iter().map(term).collect::<Vec<_>>();
            match op {
                NOp::And => app("and", args),
                NOp::Or => app("or", args),
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
    }
}

pub fn term(t: &Term) -> Sexp {
    term_primes(t, 0)
}

pub fn negated_term(t: &Term) -> Sexp {
    app("not", [term(t)])
}

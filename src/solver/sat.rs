// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A bounded model checker for flyvy programs using symbolic evaluation.

use crate::fly::{sorts::*, syntax::*};
use crate::term::FirstOrder;
use itertools::Itertools;
use std::collections::HashMap;
use thiserror::Error;

/// Holds an ordering of all (relation, elements) pairs
#[allow(dead_code)]
struct Context<'a> {
    signature: &'a Signature,
    universe: &'a Universe,
    indices: HashMap<&'a str, HashMap<Vec<usize>, usize>>,
    indices_flat_len: usize,
    vars: usize,
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Variable(usize);

impl Context<'_> {
    fn new<'a>(signature: &'a Signature, universe: &'a Universe, depth: usize) -> Context<'a> {
        let order = signature.relations.iter().flat_map(|relation| {
            if relation.args.is_empty() {
                vec![(relation.name.as_str(), (vec![]))]
            } else {
                relation
                    .args
                    .iter()
                    .map(|sort| cardinality(universe, sort))
                    .map(|card| (0..card).collect::<Vec<usize>>())
                    .multi_cartesian_product()
                    .map(|element| (relation.name.as_str(), element))
                    .collect()
            }
        });

        let mut indices_flat_len = 0;
        let mut indices: HashMap<_, HashMap<_, _>> = HashMap::new();
        for (i, (r, e)) in order.enumerate() {
            indices_flat_len += 1;
            indices.entry(r).or_default().insert(e, i);
        }

        Context {
            signature,
            universe,
            indices,
            indices_flat_len,
            vars: indices_flat_len * depth,
        }
    }

    fn get_var(&self, index: usize, primes: usize) -> Variable {
        Variable(index + primes * self.indices_flat_len)
    }

    fn new_var(&mut self) -> Variable {
        self.vars += 1;
        Variable(self.vars - 1)
    }
}

#[allow(missing_docs)]
#[derive(Error, Debug)]
pub enum CheckerError {
    #[error("sort checking error: {0}")]
    SortError(SortError),
    #[error("sort {0} not found in universe {1:#?}")]
    UnknownSort(String, Universe),

    #[error("all assumes should precede all asserts, but found {0:?}")]
    OutOfOrderStatement(ThmStmt),
    #[error("expected no primes in {0}")]
    AnyFuture(Term),
    #[error("expected no primes or only one prime in {0}")]
    TooFuture(Term),
    #[error("expected all asserts be safety properties but found {0}")]
    AssertWithoutAlways(Term),

    #[error("could not translate to propositional logic {0}")]
    CouldNotTranslateToAst(Term),
    #[error("could not translate to element {0}")]
    CouldNotTranslateToElement(Term),
}

/// Map from uninterpreted sort names to sizes
type Universe = HashMap<String, usize>;

fn cardinality(universe: &Universe, sort: &Sort) -> usize {
    match sort {
        Sort::Bool => 2,
        Sort::Id(id) => universe[id],
    }
}

/// Check a given Module out to some depth
#[allow(dead_code)]
pub fn check(
    module: &mut Module,
    universe: &Universe,
    depth: usize,
) -> Result<String, CheckerError> {
    if let Err((error, _)) = sort_check_and_infer(module) {
        return Err(CheckerError::SortError(error));
    }

    for sort in &module.signature.sorts {
        if !universe.contains_key(sort) {
            return Err(CheckerError::UnknownSort(sort.clone(), universe.clone()));
        }
    }

    for relation in &module.signature.relations {
        if relation.sort != Sort::Bool {
            todo!("non-bool relations")
        }
    }

    if !module.defs.is_empty() {
        todo!("definitions are not supported yet");
    }

    let mut assumes = Vec::new();
    let mut asserts = Vec::new();
    for statement in &module.statements {
        match statement {
            ThmStmt::Assert(Proof { assert, invariants }) => {
                asserts.push(assert.x.clone());
                if !invariants.is_empty() {
                    eprintln!("note: invariants are not yet supported, and do nothing")
                }
            }
            ThmStmt::Assume(term) if asserts.is_empty() => assumes.push(term.clone()),
            _ => return Err(CheckerError::OutOfOrderStatement(statement.clone())),
        }
    }

    let mut inits = Vec::new();
    let mut trs = Vec::new();
    for assume in assumes {
        match assume {
            Term::UnaryOp(UOp::Always, axiom) if FirstOrder::unrolling(&axiom) == Some(0) => {
                inits.push(*axiom.clone());
                trs.push(*axiom);
            }
            Term::UnaryOp(UOp::Always, tr) if FirstOrder::unrolling(&tr) == Some(1) => {
                trs.push(*tr)
            }
            Term::UnaryOp(UOp::Always, term) => return Err(CheckerError::TooFuture(*term)),
            init if FirstOrder::unrolling(&init) == Some(0) => inits.push(init),
            init => return Err(CheckerError::AnyFuture(init)),
        }
    }

    let mut safes = Vec::new();
    for assert in asserts {
        match assert {
            Term::UnaryOp(UOp::Always, safe) if FirstOrder::unrolling(&safe) == Some(0) => {
                safes.push(*safe)
            }
            Term::UnaryOp(UOp::Always, safe) => return Err(CheckerError::AnyFuture(*safe)),
            assert => return Err(CheckerError::AssertWithoutAlways(assert)),
        }
    }

    let mut context = Context::new(&module.signature, universe, depth);

    let translate = |terms| {
        let term = Term::NAryOp(NOp::And, terms);
        let term = nullary_id_to_app(term, &module.signature.relations);
        let term = crate::term::Next::new(&module.signature).normalize(&term);
        term_to_ast(&term, &context, &HashMap::new())
    };

    let init = translate(inits)?;
    let tr = translate(trs)?;
    let safe = translate(safes)?;

    let mut program = vec![init];
    for i in 0..depth {
        program.push(tr.clone().prime(i));
    }
    program.push(safe.prime(depth));

    let cnf = tseytin(Ast::And(program), &mut context);
    let dimacs = dimacs(&cnf, &context);

    Ok(dimacs)
}

fn nullary_id_to_app(term: Term, relations: &[RelationDecl]) -> Term {
    match term {
        Term::Id(id) if relations.iter().any(|r| r.name == id) => Term::App(id, 0, vec![]),
        Term::App(name, primes, args) => Term::App(
            name,
            primes,
            args.into_iter()
                .map(|arg| nullary_id_to_app(arg, relations))
                .collect(),
        ),
        Term::UnaryOp(op, term) => Term::UnaryOp(op, Box::new(nullary_id_to_app(*term, relations))),
        Term::BinOp(op, a, b) => Term::BinOp(
            op,
            Box::new(nullary_id_to_app(*a, relations)),
            Box::new(nullary_id_to_app(*b, relations)),
        ),
        Term::NAryOp(op, args) => Term::NAryOp(
            op,
            args.into_iter()
                .map(|arg| nullary_id_to_app(arg, relations))
                .collect(),
        ),
        Term::Ite { cond, then, else_ } => Term::Ite {
            cond: Box::new(nullary_id_to_app(*cond, relations)),
            then: Box::new(nullary_id_to_app(*then, relations)),
            else_: Box::new(nullary_id_to_app(*else_, relations)),
        },
        Term::Quantified {
            quantifier,
            binders,
            body,
        } => Term::Quantified {
            quantifier,
            binders,
            body: Box::new(nullary_id_to_app(*body, relations)),
        },
        term => term,
    }
}

#[derive(Clone, Debug, PartialEq)]
enum Ast {
    Bool(bool),
    Var { index: usize, primes: usize },
    And(Vec<Ast>),
    Or(Vec<Ast>),
    Not(Box<Ast>),
}

impl Ast {
    fn iff(x: Ast, y: Ast) -> Ast {
        Ast::Or(vec![
            Ast::And(vec![x.clone(), y.clone()]),
            Ast::And(vec![Ast::Not(Box::new(x)), Ast::Not(Box::new(y))]),
        ])
    }
    fn imp(x: Ast, y: Ast) -> Ast {
        Ast::Or(vec![Ast::Not(Box::new(x)), y])
    }
    fn ite(cond: Ast, then: Ast, else_: Ast) -> Ast {
        Ast::Or(vec![
            Ast::And(vec![cond.clone(), then]),
            Ast::And(vec![Ast::Not(Box::new(cond)), else_]),
        ])
    }

    fn truth(&self) -> Option<bool> {
        match self {
            Ast::Bool(b) => Some(*b),
            Ast::Var { .. } => None,
            Ast::And(vec) => vec
                .iter()
                .fold(Some(true), |acc, ast| match (acc, ast.truth()) {
                    (Some(true), x) => x,
                    (Some(false), _) => Some(false),
                    (None, Some(false)) => Some(false),
                    (None, Some(true) | None) => None,
                }),
            Ast::Or(vec) => vec
                .iter()
                .fold(Some(false), |acc, ast| match (acc, ast.truth()) {
                    (Some(false), x) => x,
                    (Some(true), _) => Some(true),
                    (None, Some(true)) => Some(true),
                    (None, Some(false) | None) => None,
                }),
            Ast::Not(ast) => ast.truth().map(|b| !b),
        }
    }
    fn prime(self, depth: usize) -> Ast {
        match self {
            Ast::Bool(b) => Ast::Bool(b),
            Ast::Var { index, primes } => Ast::Var {
                index,
                primes: primes + depth,
            },
            Ast::And(vec) => Ast::And(vec.into_iter().map(|ast| ast.prime(depth)).collect()),
            Ast::Or(vec) => Ast::Or(vec.into_iter().map(|ast| ast.prime(depth)).collect()),
            Ast::Not(ast) => Ast::Not(Box::new(ast.prime(depth))),
        }
    }
}

fn term_to_ast(
    term: &Term,
    context: &Context,
    assignments: &HashMap<String, usize>,
) -> Result<Ast, CheckerError> {
    let ast = |term| term_to_ast(term, context, assignments);
    let element = |term| term_to_element(term, context, assignments);

    let ast: Ast = match term {
        Term::Literal(value) => Ast::Bool(*value),
        Term::App(relation, primes, args) => {
            let args = args.iter().map(element).collect::<Result<Vec<_>, _>>()?;
            Ast::Var {
                index: context.indices[relation.as_str()][&args],
                primes: *primes,
            }
        }
        Term::UnaryOp(UOp::Not, term) => Ast::Not(Box::new(ast(term)?)),
        Term::BinOp(BinOp::Iff, a, b) => Ast::iff(ast(a)?, ast(b)?),
        Term::BinOp(BinOp::Equals, a, b) => match (element(a), element(b)) {
            (Ok(a), Ok(b)) => Ast::Bool(a == b),
            _ => Ast::iff(ast(a)?, ast(b)?),
        },
        Term::BinOp(BinOp::NotEquals, a, b) => Ast::Not(Box::new(ast(&Term::BinOp(
            BinOp::Equals,
            a.clone(),
            b.clone(),
        ))?)),
        Term::BinOp(BinOp::Implies, a, b) => Ast::imp(ast(a)?, ast(b)?),
        Term::NAryOp(NOp::And, terms) => {
            Ast::And(terms.iter().map(ast).collect::<Result<Vec<_>, _>>()?)
        }
        Term::NAryOp(NOp::Or, terms) => {
            Ast::Or(terms.iter().map(ast).collect::<Result<Vec<_>, _>>()?)
        }
        Term::Ite { cond, then, else_ } => Ast::ite(ast(cond)?, ast(then)?, ast(else_)?),
        Term::Quantified {
            quantifier,
            binders,
            body,
        } => {
            assert!(!binders.is_empty());
            let shape: Vec<usize> = binders
                .iter()
                .map(|b| cardinality(context.universe, &b.sort))
                .collect();
            let names: Vec<&String> = binders.iter().map(|b| &b.name).collect();
            let bodies = shape
                .iter()
                .map(|&card| (0..card).collect::<Vec<usize>>())
                .multi_cartesian_product()
                .map(|elements| {
                    let mut new_assignments = assignments.clone();
                    for (name, element) in names.iter().zip(elements) {
                        new_assignments.insert(name.to_string(), element);
                    }
                    term_to_ast(body, context, &new_assignments)
                })
                .collect::<Result<Vec<_>, _>>()?;
            match quantifier {
                Quantifier::Forall => Ast::And(bodies),
                Quantifier::Exists => Ast::Or(bodies),
            }
        }
        Term::UnaryOp(UOp::Prime | UOp::Always | UOp::Eventually, _)
        | Term::UnaryOp(UOp::Next | UOp::Previously, _)
        | Term::BinOp(BinOp::Until | BinOp::Since, ..)
        | Term::Id(_) => return Err(CheckerError::CouldNotTranslateToAst(term.clone())),
    };
    Ok(ast)
}

fn term_to_element(
    term: &Term,
    context: &Context,
    assignments: &HashMap<String, usize>,
) -> Result<usize, CheckerError> {
    let ast = |term| term_to_ast(term, context, assignments);
    let element = |term| term_to_element(term, context, assignments);

    let element: usize = match term {
        Term::Literal(_)
        | Term::UnaryOp(UOp::Not, ..)
        | Term::BinOp(BinOp::Iff | BinOp::Equals | BinOp::NotEquals | BinOp::Implies, ..)
        | Term::NAryOp(NOp::And | NOp::Or, ..)
        | Term::Quantified { .. } => match ast(term)?.truth() {
            Some(true) => 1,
            Some(false) => 0,
            None => return Err(CheckerError::CouldNotTranslateToElement(term.clone())),
        },
        Term::Id(id) => assignments[id],
        Term::Ite { cond, then, else_ } => match element(cond)? {
            1 => element(then)?,
            0 => element(else_)?,
            _ => unreachable!(),
        },
        Term::UnaryOp(UOp::Prime | UOp::Always | UOp::Eventually, _)
        | Term::UnaryOp(UOp::Next | UOp::Previously, _)
        | Term::BinOp(BinOp::Until | BinOp::Since, ..)
        | Term::App(..) => return Err(CheckerError::CouldNotTranslateToElement(term.clone())),
    };
    Ok(element)
}

#[derive(Clone, Debug, PartialEq)]
struct Literal {
    var: Variable,
    pos: bool,
}
type Clause = Vec<Literal>;
type Cnf = Vec<Clause>;

impl Literal {
    fn t(var: Variable) -> Literal {
        Literal { var, pos: true }
    }
    fn f(var: Variable) -> Literal {
        Literal { var, pos: false }
    }
}

fn tseytin(ast: Ast, context: &mut Context) -> Cnf {
    fn inner(ast: Ast, context: &mut Context, out: &mut Cnf) -> Variable {
        let mut go = |ast| inner(ast, context, out);
        match ast {
            Ast::Bool(pos) => {
                let var = context.new_var();
                out.push(vec![Literal { var, pos }]);
                var
            }
            Ast::Var { index, primes } => context.get_var(index, primes),
            Ast::And(vec) => {
                let olds: Vec<_> = vec.into_iter().map(go).collect();
                let new = context.new_var();
                for old in &olds {
                    out.push(vec![Literal::t(*old), Literal::f(new)]);
                }
                let mut olds: Vec<_> = olds.into_iter().map(Literal::f).collect();
                olds.push(Literal::t(new));
                out.push(olds);
                new
            }
            Ast::Or(vec) => {
                let olds: Vec<_> = vec.into_iter().map(go).collect();
                let new = context.new_var();
                for old in &olds {
                    out.push(vec![Literal::f(*old), Literal::t(new)]);
                }
                let mut olds: Vec<_> = olds.into_iter().map(Literal::t).collect();
                olds.push(Literal::f(new));
                out.push(olds);
                new
            }
            Ast::Not(ast) => {
                let old = go(*ast);
                let new = context.new_var();
                out.push(vec![Literal::t(old), Literal::t(new)]);
                out.push(vec![Literal::f(old), Literal::f(new)]);
                new
            }
        }
    }

    let mut out = vec![];
    let var = inner(ast, context, &mut out);
    out.push(vec![Literal::t(var)]);
    out
}

fn dimacs(cnf: &Cnf, context: &Context) -> String {
    let mut out = format!("p cnf {} {}", context.vars, cnf.len());
    out.push_str(
        &cnf.iter()
            .map(|clause| {
                clause
                    .iter()
                    .map(|literal| match literal {
                        Literal {
                            var: Variable(x),
                            pos: true,
                        } => format!("{}", x),
                        Literal {
                            var: Variable(x),
                            pos: false,
                        } => format!("-{}", x),
                    })
                    .join(" ")
            })
            .join("\n"),
    );
    out
}

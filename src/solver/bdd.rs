// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A bounded model checker for flyvy programs using symbolic evaluation.

use crate::fly::{sorts::*, syntax::*};
use crate::term::FirstOrder;
use biodivine_lib_bdd::*;
use itertools::Itertools;
use std::collections::HashMap;
use thiserror::Error;

/// Holds an ordering of all (relation, elements) pairs
#[allow(dead_code)]
struct Context<'a> {
    signature: &'a Signature,
    universe: &'a Universe,

    len: usize,
    idxs: HashMap<&'a str, HashMap<Vec<usize>, usize>>,

    bdds: BddVariableSet,
    vars: Vec<BddVariable>,
}

impl Context<'_> {
    fn new<'a>(signature: &'a Signature, universe: &'a Universe) -> Context<'a> {
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

        let mut len = 0;
        let mut idxs: HashMap<_, HashMap<_, _>> = HashMap::new();
        for (i, (r, e)) in order.enumerate() {
            len += 1;
            idxs.entry(r).or_default().insert(e, i);
        }

        let bdds = BddVariableSet::new_anonymous((idxs.len() * 2).try_into().unwrap());
        let vars = bdds.variables();

        Context {
            signature,
            universe,
            len,
            idxs,
            bdds,
            vars,
        }
    }

    fn get(&self, relation: &str, element: &[usize], prime: bool) -> Bdd {
        self.bdds
            .mk_var(self.vars[self.idxs[relation][element] + if prime { self.len } else { 0 }])
    }
}

/// The result of a successful run of the bounded model checker
#[derive(Debug)]
pub enum CheckerResult {
    /// The checker found a counterexample
    Counterexample,
    /// The checker did not find a counterexample
    Unknown,
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

    #[error("expected a boolean expression but found an element")]
    ExpectedBdd,
    #[error("expected an element of a sort but found an expression {0:?}")]
    ExpectedElement(Bdd),
    #[error("could not translate term {0}")]
    UnsupportedTerm(Term),
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
pub fn check(
    module: &mut Module,
    universe: &Universe,
    _depth: usize,
) -> Result<CheckerResult, CheckerError> {
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

    let context = Context::new(&module.signature, universe);

    let translate = |terms| {
        let term = Term::NAryOp(NOp::And, terms);
        let term = nullary_id_to_app(term, &module.signature.relations);
        let term = crate::term::Next::new(&module.signature).normalize(&term);
        term_to_bdd(&term, &context, &HashMap::new())?.bdd()
    };
    let _init = translate(inits)?;
    let _tr = translate(trs)?;
    let _safe = translate(safes)?;

    todo!()
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

#[derive(Debug)]
enum BddOrElement {
    Bdd(Bdd),
    Element(usize),
}

impl BddOrElement {
    fn bdd(self) -> Result<Bdd, CheckerError> {
        match self {
            BddOrElement::Bdd(bdd) => Ok(bdd),
            BddOrElement::Element(_) => Err(CheckerError::ExpectedBdd),
        }
    }

    fn element(self) -> Result<usize, CheckerError> {
        match self {
            BddOrElement::Element(element) => Ok(element),
            BddOrElement::Bdd(bdd) => Err(CheckerError::ExpectedElement(bdd)),
        }
    }
}

fn term_to_bdd(
    term: &Term,
    context: &Context,
    assignments: &HashMap<String, usize>,
) -> Result<BddOrElement, CheckerError> {
    let go = |term| term_to_bdd(term, context, assignments);

    let bdd: Bdd = match term {
        Term::Literal(true) => context.bdds.mk_true(),
        Term::Literal(false) => context.bdds.mk_false(),
        Term::Id(id) => return Ok(BddOrElement::Element(assignments[id])),
        Term::App(relation, primes, args) => context.get(
            relation,
            &args
                .iter()
                .map(|arg| go(arg)?.element())
                .collect::<Result<Vec<_>, _>>()?,
            *primes == 1,
        ),
        Term::UnaryOp(UOp::Not, term) => go(term)?.bdd()?.not(),
        Term::BinOp(BinOp::Iff, a, b) => go(a)?.bdd()?.iff(&go(b)?.bdd()?),
        Term::BinOp(BinOp::Equals, a, b) => match (go(a)?, go(b)?) {
            (BddOrElement::Bdd(a), BddOrElement::Bdd(b)) => a.iff(&b),
            (BddOrElement::Element(a), BddOrElement::Element(b)) if a == b => {
                context.bdds.mk_true()
            }
            (BddOrElement::Element(a), BddOrElement::Element(b)) if a == b => {
                context.bdds.mk_false()
            }
            _ => return Err(CheckerError::UnsupportedTerm(term.clone())),
        },
        Term::BinOp(BinOp::NotEquals, a, b) => {
            go(&Term::BinOp(BinOp::Equals, a.clone(), b.clone()))?
                .bdd()?
                .not()
        }
        Term::BinOp(BinOp::Implies, a, b) => go(a)?.bdd()?.imp(&go(b)?.bdd()?),
        Term::NAryOp(NOp::And, terms) => {
            terms.iter().fold(Ok(context.bdds.mk_true()), |and, term| {
                Ok(and?.and(&go(term)?.bdd()?))
            })?
        }
        Term::NAryOp(NOp::Or, terms) => {
            terms.iter().fold(Ok(context.bdds.mk_false()), |or, term| {
                Ok(or?.or(&go(term)?.bdd()?))
            })?
        }
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
                    // extend assignments with all variables bound to these `elements`
                    let mut assignments = assignments.clone();
                    for (name, element) in names.iter().zip(elements) {
                        assignments.insert(name.to_string(), element);
                    }
                    go(body)?.bdd()
                })
                .collect::<Result<Vec<_>, _>>()?;
            match quantifier {
                Quantifier::Forall => bodies
                    .into_iter()
                    .fold(context.bdds.mk_true(), |and, term| and.and(&term)),
                Quantifier::Exists => bodies
                    .into_iter()
                    .fold(context.bdds.mk_false(), |or, term| or.or(&term)),
            }
        }
        _ => return Err(CheckerError::UnsupportedTerm(term.clone())),
    };
    Ok(BddOrElement::Bdd(bdd))
}

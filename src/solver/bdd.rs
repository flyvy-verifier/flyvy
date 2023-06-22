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

        let bdds = BddVariableSet::new_anonymous((len * 2).try_into().unwrap());
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

    fn mk_bool(&self, value: bool) -> Bdd {
        match value {
            true => self.bdds.mk_true(),
            false => self.bdds.mk_false(),
        }
    }

    fn mk_and(&self, bdds: impl IntoIterator<Item = Bdd>) -> Bdd {
        bdds.into_iter()
            .fold(self.bdds.mk_true(), |acc, term| acc.and(&term))
    }

    fn mk_or(&self, bdds: impl IntoIterator<Item = Bdd>) -> Bdd {
        bdds.into_iter()
            .fold(self.bdds.mk_false(), |acc, term| acc.or(&term))
    }
}

/// The result of a successful run of the bounded model checker
#[derive(Debug, PartialEq)]
pub enum CheckerAnswer {
    /// The checker found a counterexample
    Counterexample(BddValuation),
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

    #[error("could not translate to bdd {0}")]
    CouldNotTranslateToBdd(Term),
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
pub fn check(
    module: &mut Module,
    universe: &Universe,
    depth: usize,
) -> Result<CheckerAnswer, CheckerError> {
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
        term_to_bdd(&term, &context, &HashMap::new())
    };
    let init = translate(inits)?;
    let tr = translate(trs)?;
    let not_safe = translate(safes)?.not();

    let mut current = init;
    if let Some(valuation) = current.and(&not_safe).sat_witness() {
        return Ok(CheckerAnswer::Counterexample(valuation));
    }
    for _ in 0..depth {
        current = Bdd::binary_op_with_exists(
            &current,
            &tr,
            op_function::and,
            &context.vars[0..context.len],
        );
        for i in 0..context.len {
            unsafe {
                current.rename_variable(context.vars[i + context.len], context.vars[i]);
            }
        }

        if let Some(valuation) = current.and(&not_safe).sat_witness() {
            return Ok(CheckerAnswer::Counterexample(valuation));
        }
    }

    Ok(CheckerAnswer::Unknown)
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

fn term_to_bdd(
    term: &Term,
    context: &Context,
    assignments: &HashMap<String, usize>,
) -> Result<Bdd, CheckerError> {
    let bdd = |term| term_to_bdd(term, context, assignments);
    let element = |term| term_to_element(term, context, assignments);

    let bdd: Bdd = match term {
        Term::Literal(value) => context.mk_bool(*value),
        Term::App(relation, primes, args) => context.get(
            relation,
            &args.iter().map(element).collect::<Result<Vec<_>, _>>()?,
            *primes == 1,
        ),
        Term::UnaryOp(UOp::Not, term) => bdd(term)?.not(),
        Term::BinOp(BinOp::Iff, a, b) => bdd(a)?.iff(&bdd(b)?),
        Term::BinOp(BinOp::Equals, a, b) => match (element(a), element(b)) {
            (Ok(a), Ok(b)) => context.mk_bool(a == b),
            _ => bdd(a)?.iff(&bdd(b)?),
        },
        Term::BinOp(BinOp::NotEquals, a, b) => {
            bdd(&Term::BinOp(BinOp::Equals, a.clone(), b.clone()))?.not()
        }
        Term::BinOp(BinOp::Implies, a, b) => bdd(a)?.imp(&bdd(b)?),
        Term::NAryOp(NOp::And, terms) => {
            context.mk_and(terms.iter().map(bdd).collect::<Result<Vec<_>, _>>()?)
        }
        Term::NAryOp(NOp::Or, terms) => {
            context.mk_or(terms.iter().map(bdd).collect::<Result<Vec<_>, _>>()?)
        }
        Term::Ite { cond, then, else_ } => {
            Bdd::if_then_else(&bdd(cond)?, &bdd(then)?, &bdd(else_)?)
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
                    let mut new_assignments = assignments.clone();
                    for (name, element) in names.iter().zip(elements) {
                        new_assignments.insert(name.to_string(), element);
                    }
                    term_to_bdd(body, context, &new_assignments)
                })
                .collect::<Result<Vec<_>, _>>()?;
            match quantifier {
                Quantifier::Forall => context.mk_and(bodies),
                Quantifier::Exists => context.mk_or(bodies),
            }
        }
        Term::UnaryOp(UOp::Prime | UOp::Always | UOp::Eventually, _)
        | Term::UnaryOp(UOp::Next | UOp::Previously, _)
        | Term::BinOp(BinOp::Until | BinOp::Since, ..)
        | Term::Id(_) => return Err(CheckerError::CouldNotTranslateToBdd(term.clone())),
    };
    Ok(bdd)
}

fn term_to_element(
    term: &Term,
    context: &Context,
    assignments: &HashMap<String, usize>,
) -> Result<usize, CheckerError> {
    let bdd = |term| term_to_bdd(term, context, assignments);
    let element = |term| term_to_element(term, context, assignments);

    let element: usize = match term {
        Term::Literal(_)
        | Term::UnaryOp(UOp::Not, ..)
        | Term::BinOp(BinOp::Iff | BinOp::Equals | BinOp::NotEquals | BinOp::Implies, ..)
        | Term::NAryOp(NOp::And | NOp::Or, ..)
        | Term::Quantified { .. } => match bdd(term)? {
            bdd if bdd.is_true() => 1,
            bdd if bdd.is_false() => 0,
            _ => return Err(CheckerError::CouldNotTranslateToElement(term.clone())),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checker_basic() -> Result<(), CheckerError> {
        let source = "
mutable x: bool

assume x

assume always (x -> !x')

assert always x
        ";

        let mut module = crate::fly::parse(source).unwrap();
        let universe = HashMap::from([]);

        assert_eq!(CheckerAnswer::Unknown, check(&mut module, &universe, 0)?);
        assert_eq!(
            CheckerAnswer::Counterexample(BddValuation::new(vec![false, false])),
            check(&mut module, &universe, 1)?
        );

        Ok(())
    }

    #[test]
    fn checker_lockserver() -> Result<(), CheckerError> {
        let source = "
sort node

mutable lock_msg(node): bool
mutable grant_msg(node): bool
mutable unlock_msg(node): bool
mutable holds_lock(node): bool
mutable server_holds_lock: bool

# inits:
assume (forall N:node. !lock_msg(N)) & (forall N:node. !grant_msg(N)) & (forall N:node.
    !unlock_msg(N)) & (forall N:node. !holds_lock(N)) & (server_holds_lock)

# transitions:
assume always
    (exists n:node. 
        (forall N:node. ((lock_msg(N))') <-> lock_msg(N) | N = n) & 
        (forall x0:node. ((grant_msg(x0))') = grant_msg(x0)) & 
        (forall x0:node. ((unlock_msg(x0))') = unlock_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0)) & 
        ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. server_holds_lock & lock_msg(n) & 
            !((server_holds_lock)') & 
            (((lock_msg(N))') <-> lock_msg(N) & N != n) & 
            (((grant_msg(N))') <-> grant_msg(N) | N = n)) & 
        (forall x0:node. ((unlock_msg(x0))') = unlock_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0))) | 
    (exists n:node. 
        (forall N:node. grant_msg(n) & 
            (((grant_msg(N))') <-> grant_msg(N) & N != n) & 
            (((holds_lock(N))') <-> holds_lock(N) | N = n)) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) & 
        (forall x0:node. 
            ((unlock_msg(x0))') = unlock_msg(x0)) & 
            ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. holds_lock(n) & 
            (((holds_lock(N))') <-> holds_lock(N) & N != n) & 
            (((unlock_msg(N))') <-> unlock_msg(N) | N = n)) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) &
        (forall x0:node. 
            ((grant_msg(x0))') = grant_msg(x0)) & 
            ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. unlock_msg(n) & 
            (((unlock_msg(N))') <-> unlock_msg(N) & N != n) & 
            ((server_holds_lock)')) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) & 
        (forall x0:node. ((grant_msg(x0))') = grant_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0)))

# safety:
assert always (forall N1:node, N2:node. holds_lock(N1) & holds_lock(N2) -> N1 = N2)
        ";

        let mut module = crate::fly::parse(source).unwrap();
        let universe = HashMap::from([("node".to_string(), 2)]);

        assert_eq!(CheckerAnswer::Unknown, check(&mut module, &universe, 10)?);

        Ok(())
    }

    #[test]
    fn checker_lockserver_buggy() -> Result<(), CheckerError> {
        let source = "
sort node

mutable lock_msg(node): bool
mutable grant_msg(node): bool
mutable unlock_msg(node): bool
mutable holds_lock(node): bool
mutable server_holds_lock: bool

# inits:
assume (forall N:node. !lock_msg(N)) & (forall N:node. !grant_msg(N)) & (forall N:node.
    !unlock_msg(N)) & (forall N:node. !holds_lock(N)) & (server_holds_lock)

# transitions:
assume always
    (exists n:node. 
        (forall N:node. ((lock_msg(N))') <-> lock_msg(N) | N = n) & 
        (forall x0:node. ((grant_msg(x0))') = grant_msg(x0)) & 
        (forall x0:node. ((unlock_msg(x0))') = unlock_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0)) & 
        ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. server_holds_lock & lock_msg(n) & 
            !((server_holds_lock)') & 
            (((lock_msg(N))') <-> lock_msg(N) & N != n) & 
            (((grant_msg(N))') <-> grant_msg(N) | N = n)) & 
        (forall x0:node. ((unlock_msg(x0))') = unlock_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0))) | 
    (exists n:node. 
        (forall N:node. grant_msg(n) & 
            (((grant_msg(N))') <-> grant_msg(N) & N != n) & 
            (((holds_lock(N))') <-> holds_lock(N) | N = n)) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) & 
        (forall x0:node. 
            ((unlock_msg(x0))') = unlock_msg(x0)) & 
            ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. holds_lock(n) & 
            (((holds_lock(N))') <-> holds_lock(N) & N != n) & 
            (((unlock_msg(N))') <-> unlock_msg(N) | N = n)) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) &
        (forall x0:node. 
            ((grant_msg(x0))') = grant_msg(x0)) & 
            ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. unlock_msg(n) & 
            (((unlock_msg(N))') <-> unlock_msg(N)) & 
            ((server_holds_lock)')) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) & 
        (forall x0:node. ((grant_msg(x0))') = grant_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0)))

# safety:
assert always (forall N1:node, N2:node. holds_lock(N1) & holds_lock(N2) -> N1 = N2)
        ";

        let mut module = crate::fly::parse(source).unwrap();
        let universe = HashMap::from([("node".to_string(), 2)]);

        let bug = check(&mut module, &universe, 12)?;
        assert!(matches!(bug, CheckerAnswer::Counterexample(_)));

        let too_short = check(&mut module, &universe, 11)?;
        assert_eq!(CheckerAnswer::Unknown, too_short);

        Ok(())
    }
}

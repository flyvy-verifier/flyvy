// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A bounded model checker for flyvy programs using symbolic evaluation.

// use biodivine_lib_bdd::*;
use crate::fly::{sorts::*, syntax::*};
use itertools::Itertools;
use std::collections::HashMap;
use thiserror::Error;

/// Holds an ordering of all (relation, elements) pairs
struct Indices<'a>(HashMap<&'a str, HashMap<Vec<usize>, usize>>);

impl Indices<'_> {
    fn new<'a>(signature: &'a Signature, universe: &'a Universe) -> Indices<'a> {
        let ordering: Vec<(usize, (&str, Vec<usize>))> = signature
            .relations
            .iter()
            .flat_map(|relation| {
                if relation.args.is_empty() {
                    vec![(relation.name.as_str(), (vec![]))]
                } else {
                    relation
                        .args
                        .iter()
                        .map(|sort| match sort {
                            Sort::Bool => 2,
                            Sort::Id(id) => universe[id],
                        })
                        .map(|card| (0..card).collect::<Vec<usize>>())
                        .multi_cartesian_product()
                        .map(|element| (relation.name.as_str(), element))
                        .collect()
                }
            })
            .enumerate()
            .collect();

        let mut out = Indices(HashMap::new());
        for (i, (r, e)) in ordering {
            out.0.entry(r).or_default().insert(e, i);
        }
        out
    }

    fn len(&self) -> usize {
        self.0.values().map(HashMap::len).sum()
    }

    fn get(&self, relation: &str, element: &[usize]) -> usize {
        self.0[relation][element]
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

    #[error("expected no primes or only one prime in {0:#?}")]
    TooFuture(Term),
    #[error("expected no primes in {0:#?}")]
    FutureInit(Term),
    #[error("found an assert that isn't a safety property")]
    AssertWithoutAlways(Term),
}

/// Map from uninterpreted sort names to sizes
type Universe = HashMap<String, usize>;

/// Check a given Module out to some depth
pub fn check(
    module: &mut Module,
    universe: &Universe,
    _depth: usize,
) -> Result<CheckerResult, CheckerError> {
    if let Err((error, _)) = sort_check_and_infer(module) {
        return Err(CheckerError::SortError(error));
    }

    let _indices = Indices::new(&module.signature, universe);

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
            Term::UnaryOp(UOp::Always, tr_or_axiom) => {
                // for axioms, also restrict inits
                match crate::term::FirstOrder::unrolling(&tr_or_axiom) {
                    Some(0) => {
                        inits.push(*tr_or_axiom.clone());
                        trs.push(*tr_or_axiom)
                    }
                    Some(1) => trs.push(*tr_or_axiom),
                    _ => return Err(CheckerError::TooFuture(*tr_or_axiom)),
                }
            }
            init => {
                if crate::term::FirstOrder::unrolling(&init) != Some(0) {
                    return Err(CheckerError::FutureInit(init));
                }
                inits.push(init);
            }
        }
    }

    let mut safes = Vec::new();
    for assert in asserts {
        match assert {
            Term::UnaryOp(UOp::Always, safe) => safes.push(*safe),
            assert => return Err(CheckerError::AssertWithoutAlways(assert)),
        }
    }

    todo!()
}

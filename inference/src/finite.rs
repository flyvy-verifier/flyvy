// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Infer an inductive invariant from the set of reachable states
//! with small sort bounds.

use bounded::bdd::*;
use fly::{semantics::*, syntax::*, transitions::*};
use solver::conf::SolverConf;
use std::collections::HashMap;
use thiserror::Error;
use verify::{error::SolveError, module::verify_destructured_module};

/// The result of a successful run of finite::invariant.
pub enum FiniteAnswer {
    /// The module wasn't safe to begin with
    BddCounterexample(Vec<Model>),
    /// The inferred invariant failed
    InvariantFail(Term, SolveError),
    /// The inferred invariant succeeded
    InvariantInferred(Term),
}

#[allow(missing_docs)]
#[derive(Debug, Error)]
pub enum FiniteError {
    #[error("{0}")]
    ExtractionError(ExtractionError),
    #[error("{0}")]
    CheckerError(CheckerError),
}

/// Try to find an invariant by getting the set of all backwards reachable states.
/// Returns Some((inv, true)) if an invariant is found, or None if a counterexample is found.
/// If the invariant that is guessed does not work, it returns Some((inv, false)).
pub fn invariant(
    module: &Module,
    universe: HashMap<String, usize>,
    conf: &SolverConf,
    print_timing: bool,
) -> Result<FiniteAnswer, FiniteError> {
    // Get the set of reachable states
    let (bdd, context) = match check_reversed(module, &universe, None, print_timing) {
        Ok(CheckerAnswer::Convergence(bdd, context)) => (bdd, context),
        Ok(CheckerAnswer::Counterexample(models)) => {
            return Ok(FiniteAnswer::BddCounterexample(models))
        }
        Ok(CheckerAnswer::Unknown) => unreachable!(),
        Err(e) => return Err(FiniteError::CheckerError(e)),
    };

    // Convert the Bdd to a Term
    let (ast, bindings) = bdd_to_term(&bdd.not(), &context);

    // Add not-equal clauses between same-sort elements
    let mut not_equals = vec![];
    for ((sort_1, element_1), name_1) in &bindings {
        for ((sort_2, element_2), name_2) in &bindings {
            if element_1 < element_2 && sort_1 == sort_2 {
                not_equals.push(Term::BinOp(
                    BinOp::NotEquals,
                    Box::new(Term::Id(name_1.to_string())),
                    Box::new(Term::Id(name_2.to_string())),
                ));
            }
        }
    }

    // Wrap the Term in foralls
    let binders = bindings
        .into_iter()
        .map(|((sort, _), name)| Binder {
            name,
            sort: Sort::Id(sort.to_string()),
        })
        .collect();
    let ast = Term::Quantified {
        quantifier: Quantifier::Forall,
        body: Box::new(Term::BinOp(
            BinOp::Implies,
            Box::new(Term::NAryOp(NOp::And, not_equals)),
            Box::new(ast),
        )),
        binders,
    };

    // Try to verify the term
    let mut destructured = extract(module).map_err(FiniteError::ExtractionError)?;
    assert_eq!(1, destructured.proofs.len());
    destructured.proofs[0].invariants = vec![MaybeSpannedTerm::Term(ast.clone())];

    if let Err(err) = verify_destructured_module(conf, &destructured, &module.signature) {
        Ok(FiniteAnswer::InvariantFail(ast, err))
    } else {
        Ok(FiniteAnswer::InvariantInferred(ast))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fly::sorts::sort_check_and_infer;
    use solver::{backends::GenericBackend, backends::SolverType, solver_path};

    #[test]
    fn finite_lockserver() -> Result<(), FiniteError> {
        let source = include_str!("../../temporal-verifier/examples/lockserver.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();

        let universe = HashMap::from([("node".to_string(), 2)]);
        let conf = SolverConf {
            backend: GenericBackend::new(SolverType::Z3, &solver_path("z3")),
            tee: None,
        };

        match invariant(&module, universe, &conf, false)? {
            FiniteAnswer::InvariantInferred(_) => Ok(()),
            FiniteAnswer::InvariantFail(inv, _) => panic!("invariant wasn't inductive: {}", inv),
            FiniteAnswer::BddCounterexample(_) => panic!("counterexample found"),
        }
    }
}

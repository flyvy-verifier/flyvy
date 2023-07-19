// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Infer an inductive invariant from the set of reachable states
//! with small sort bounds.

use bounded::bdd::*;
use fly::{syntax::*, transitions::*};
use solver::conf::SolverConf;
use std::collections::HashMap;
use thiserror::Error;
use verify::module::verify_destructured_module;

#[allow(missing_docs)]
#[derive(Debug, Error)]
pub enum FiniteError {
    #[error("{0}")]
    ExtractionError(ExtractionError),
    #[error("{0}")]
    CheckerError(CheckerError),
    #[error("could not verify inferred invariant")]
    VerifyError,
}

pub fn invariant(
    module: &Module,
    universe: HashMap<String, usize>,
    conf: &SolverConf,
    print_timing: bool,
) -> Result<Option<Term>, FiniteError> {
    // Get the set of reachable states
    let (bdd, context) = match check_reversed(module, &universe, None, print_timing) {
        Ok(CheckerAnswer::Convergence(bdd, context)) => (bdd, context),
        Ok(CheckerAnswer::Counterexample(_)) => return Ok(None),
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
        eprintln!("\nverification errors:");
        for fail in &err.fails {
            use verify::error::*;
            match fail.reason {
                FailureType::InitInv => eprintln!("not implied by init:"),
                FailureType::NotInductive => eprintln!("not inductive:"),
                FailureType::Unsupported => eprintln!("unsupported:"),
            }
            match &fail.error {
                QueryError::Sat(models) => {
                    for (i, model) in models.iter().enumerate() {
                        eprintln!("state {}:", i);
                        eprintln!("{}", model.fmt());
                    }
                }
                QueryError::Unknown(message) => eprintln!("{}", message),
            }
        }
        return Err(FiniteError::VerifyError);
    }
    Ok(Some(ast))
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

        invariant(&module, universe, &conf, false)?;

        Ok(())
    }

    #[test]
    fn finite_consensus() -> Result<(), FiniteError> {
        let source = include_str!("../../temporal-verifier/examples/consensus.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();

        let universe = HashMap::from([
            ("node".to_string(), 3),
            ("quorum".to_string(), 3),
            ("value".to_string(), 3),
        ]);
        let conf = SolverConf {
            backend: GenericBackend::new(SolverType::Z3, &solver_path("z3")),
            tee: None,
        };

        invariant(&module, universe, &conf, true)?;

        Ok(())
    }
}

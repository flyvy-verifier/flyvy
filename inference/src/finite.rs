// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Infer an inductive invariant from the set of reachable states
//! with small sort bounds.

use biodivine_lib_bdd::*;
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
) -> Result<Option<Term>, FiniteError> {
    // Get the set of reachable states
    let (bdd, context) = match check(module, &universe, None, false) {
        Ok(CheckerAnswer::Convergence(bdd, context)) => (bdd, context),
        Ok(CheckerAnswer::Counterexample(_)) => return Ok(None),
        Ok(CheckerAnswer::Unknown) => unreachable!(),
        Err(e) => return Err(FiniteError::CheckerError(e)),
    };

    // Convert the Bdd to a Term
    let bdd = underapproximate(bdd.not(), 10000, &context.bdds, false).not();
    let (ast, bindings) = bdd_to_term(&bdd, &context);

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

    println!("\ntesting invariant: {}", ast);
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

// Produces a short Bdd that represents a subset of the original Bdd's states
fn underapproximate(
    mut bdd: Bdd,
    num_clauses: usize,
    bdds: &BddVariableSet,
    minimize_clauses: bool,
) -> Bdd {
    let mut clauses = vec![];
    for _ in 0..num_clauses {
        let clause = match bdd.most_free_clause() {
            Some(clause) => clause,
            None => {
                println!("underapproximate() ended with original bdd");
                break;
            }
        };
        if minimize_clauses {
            todo!("minimize the clause (greedily or with MARCO?)")
        }
        let clause = bdds.mk_conjunctive_clause(&clause);
        bdd = bdd.and(&clause.not());
        clauses.push(clause);
    }
    clauses.into_iter().fold(bdds.mk_false(), |a, b| a.or(&b))
}

#[cfg(test)]
mod tests {
    use super::*;
    use fly::sorts::sort_check_and_infer;
    use solver::{backends::GenericBackend, backends::SolverType, solver_path};

    #[ignore]
    #[test]
    fn finite_lockserver() -> Result<(), FiniteError> {
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

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();

        let universe = HashMap::from([("node".to_string(), 2)]);
        let conf = SolverConf {
            backend: GenericBackend::new(SolverType::Z3, &solver_path("z3")),
            tee: None,
        };

        println!("{:?}", invariant(&module, universe, &conf)?);

        Ok(())
    }
}

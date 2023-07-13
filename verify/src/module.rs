// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Verify that a module is correct.

use std::collections::HashMap;

use rayon::prelude::*;

use super::error::{AssertionFailure, FailureType, QueryError, SolveError};
use super::safety::InvariantAssertion;
use fly::{printer, syntax::*, transitions::*};
use solver::{
    conf::SolverConf,
    imp::{Backend, Solver},
    SatResp,
};

fn verify_term<B: Backend>(solver: &mut Solver<B>, t: Term) -> Result<(), QueryError> {
    solver.assert(&Term::negate(t));
    let resp = solver.check_sat(HashMap::new()).expect("error in solver");
    match resp {
        SatResp::Sat { .. } => {
            // TODO: should be configurable whether to minimize or not
            let states = solver
                .get_minimal_model()
                .expect("solver error while minimizing");
            // TODO: need a way to report traces rather than just single models
            let s0 = states.into_iter().next().unwrap();
            Err(QueryError::Sat(s0))
        }
        SatResp::Unsat => Ok(()),
        SatResp::Unknown(m) => Err(QueryError::Unknown(m)),
    }
}

/// Verify that a module is correct.
pub fn verify_module(conf: &SolverConf, m: &Module) -> Result<(), SolveError> {
    verify_destructured_module(conf, &extract(m).unwrap(), &m.signature)
}

/// Verify that a destructured module is correct
pub fn verify_destructured_module(
    conf: &SolverConf,
    module: &DestructuredModule,
    signature: &Signature,
) -> Result<(), SolveError> {
    let check_invariant = |assert: &InvariantAssertion| -> Result<(), Vec<AssertionFailure>> {
        let mut failures = vec![];
        {
            // check initiation (init implies invariant)
            let mut solver = conf.solver(signature, 1);
            solver.comment_with(|| format!("init implies: {}", printer::term(&assert.inv.x)));
            // TODO: break this down per invariant, as with consecutions()
            let res = verify_term(&mut solver, assert.initiation().0);
            solver.save_tee();
            if let Err(cex) = res {
                failures.push(AssertionFailure {
                    loc: assert.inv.span,
                    reason: FailureType::InitInv,
                    error: cex,
                });
            }
        }
        {
            // check consecution (transitions preserve invariant)
            let new_failures = assert
                .consecutions()
                .into_par_iter()
                .map(|(span, t)| {
                    let mut solver = conf.solver(signature, 2);
                    solver.comment_with(|| format!("inductive: {}", printer::term(&assert.inv.x)));
                    let res = verify_term(&mut solver, t.0);
                    solver.save_tee();
                    if let Err(cex) = res {
                        Some(AssertionFailure {
                            loc: span.unwrap_or(assert.inv.span),
                            reason: FailureType::NotInductive,
                            error: cex,
                        })
                    } else {
                        None
                    }
                })
                .flatten()
                .collect::<Vec<_>>();
            failures.extend(new_failures);
        }
        if !failures.is_empty() {
            return Err(failures);
        }
        Ok(())
    };

    let inits = &module.inits;
    let transitions = &module.transitions;
    // we push verified safety properties as axioms
    let mut axioms = module.axioms.clone();
    let mut errors = SolveError::default();

    for proof in &module.proofs {
        if let Ok(assert) =
            InvariantAssertion::for_assert(signature, inits, transitions, &axioms, proof)
        {
            log::info!("checking invariant {}", proof.safety.x);
            let res = check_invariant(&assert);
            if res.is_err() {
                errors.fails.extend(res.err().unwrap())
            }
        } else {
            errors.push(AssertionFailure {
                loc: proof.safety.span,
                error: QueryError::Unknown("unsupported".to_string()),
                reason: FailureType::Unsupported,
            })
        }
        // for future assertions, treat this assertion as an assumption
        axioms.push(proof.safety.x.clone());
    }

    if errors.fails.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

#[cfg(test)]
mod tests {
    use std::{env, fs};

    use fly::{self, syntax::Module};
    use solver::backends::{GenericBackend, SolverType};
    use solver::solver_path;

    use super::{verify_module, SolveError, SolverConf};

    fn z3_verify(m: &Module) -> Result<(), SolveError> {
        let z3_cmd = solver_path("z3");
        let conf = SolverConf {
            backend: GenericBackend::new(SolverType::Z3, &z3_cmd),
            tee: None,
        };
        verify_module(&conf, m)
    }

    #[test]
    fn test_verify_failing2() {
        let file = fs::read_to_string("../temporal-verifier/tests/examples/fail/basic.fly")
            .expect("could not read input");
        let m = fly::parser::parse(&file).expect("parse error");
        insta::assert_yaml_snapshot!(z3_verify(&m).expect_err("verification should fail"), {
            ".fails[].error.symbols" => insta::sorted_redaction(),
        });
    }

    #[test]
    fn test_verify_safety1() {
        let file = fs::read_to_string("../temporal-verifier/tests/examples/success/safety1.fly")
            .expect("could not read input");
        let m = fly::parser::parse(&file).expect("parse error");
        assert_eq!(z3_verify(&m), Ok(()));
    }

    #[test]
    fn test_verify_safety1_fail() {
        let file = fs::read_to_string("../temporal-verifier/tests/examples/fail/safety1_ind.fly")
            .expect("could not read input");
        let m = fly::parser::parse(&file).expect("parse error");
        insta::assert_yaml_snapshot!(z3_verify(&m).expect_err("verification should fail"), {
            ".fails[].error.symbols" => insta::sorted_redaction(),
        });
    }
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::collections::HashMap;
use std::path::PathBuf;

use super::error::{AssertionFailure, FailureType, QueryError, SolveError};
use super::safety::InvariantAssertion;
use crate::fly::syntax::Proof;
use crate::{
    fly::{
        printer,
        syntax::{Module, Signature, Term, ThmStmt},
    },
    smtlib::proc::SatResp,
    solver::{backends::GenericBackend, Backend, Solver},
    term::FirstOrder,
};

pub struct SolverConf {
    pub backend: GenericBackend,
    pub tee: Option<PathBuf>,
}

impl SolverConf {
    pub fn solver(&self, sig: &Signature, n_states: usize) -> Solver<&GenericBackend> {
        // TODO: failures to start the solver should be bubbled up to user nicely
        Solver::new(sig, n_states, &self.backend, self.tee.as_deref())
            .expect("could not start solver")
    }
}

fn verify_term<B: Backend>(solver: &mut Solver<B>, t: Term) -> Result<(), QueryError> {
    solver.assert(&Term::negate(t));
    let resp = solver.check_sat(HashMap::new()).expect("error in solver");
    match resp {
        SatResp::Sat { .. } => {
            // TODO: should be configurable whether to minimize or not
            let states = solver.get_minimal_model();
            // TODO: need a way to report traces rather than just single models
            let s0 = states.into_iter().next().unwrap();
            Err(QueryError::Sat(s0))
        }
        SatResp::Unsat => Ok(()),
        SatResp::Unknown(m) => Err(QueryError::Unknown(m)),
    }
}

fn verify_firstorder(
    conf: &SolverConf,
    sig: &Signature,
    n: usize,
    assumes: &[&Term],
    assert: &Term,
) -> Result<(), QueryError> {
    let mut solver =
        Solver::new(sig, n, &conf.backend, conf.tee.as_deref()).expect("could not start solver");
    for assume in assumes {
        solver.assert(assume);
    }
    solver.comment_with(|| format!("assert {}", printer::term(assert)));
    verify_term(&mut solver, assert.clone())
}

pub fn verify_module(conf: &SolverConf, m: &Module) -> Result<(), SolveError> {
    let check_invariant =
        |pf: &Proof, assert: &InvariantAssertion| -> Result<(), AssertionFailure> {
            {
                // check initiation (init implies invariant)
                let mut solver = conf.solver(&m.signature, 1);
                solver.comment_with(|| format!("init implies: {}", printer::term(&assert.inv)));
                let res = verify_term(&mut solver, assert.initiation().0);
                if let Err(cex) = res {
                    return Err(AssertionFailure {
                        loc: pf.assert.span,
                        reason: FailureType::InitInv,
                        error: cex,
                    });
                }
            }
            {
                // check consecution (transitions preserve invariant)
                let mut solver = conf.solver(&m.signature, 2);
                solver.comment_with(|| format!("inductive: {}", printer::term(&assert.inv)));
                let res = verify_term(&mut solver, assert.consecution().0);
                if let Err(cex) = res {
                    return Err(AssertionFailure {
                        loc: pf.assert.span,
                        reason: FailureType::NotInductive,
                        error: cex,
                    });
                }
            }
            Ok(())
        };

    // assumptions/assertions so far
    let mut assumes: Vec<&Term> = vec![];
    let mut errors = SolveError::default();
    for step in &m.statements {
        match step {
            ThmStmt::Assume(e) => assumes.push(e),
            ThmStmt::Assert(pf) => {
                let proof_invariants: Vec<&Term> = pf.invariants.iter().map(|s| &s.x).collect();
                if let Some(n) = FirstOrder::unrolling(&pf.assert.x) {
                    let res = verify_firstorder(conf, &m.signature, n + 1, &assumes, &pf.assert.x);
                    if let Err(cex) = res {
                        errors.push(AssertionFailure {
                            loc: pf.assert.span,
                            reason: FailureType::FirstOrder,
                            error: cex,
                        });
                    }
                } else if let Ok(assert) =
                    InvariantAssertion::for_assert(&assumes, &pf.assert.x, &proof_invariants)
                {
                    let res = check_invariant(pf, &assert);
                    if res.is_err() {
                        errors.push(res.err().unwrap())
                    }
                } else {
                    errors.push(AssertionFailure {
                        loc: pf.assert.span,
                        error: QueryError::Unknown("unsupported".to_string()),
                        reason: FailureType::Unsupported,
                    })
                }
                // for future assertions, treat this assertion as an assumption
                assumes.push(&pf.assert.x);
            }
        }
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

    use crate::{
        fly::{self, syntax::Module},
        solver::{
            backends::{GenericBackend, SolverType},
            solver_path,
        },
    };

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
        let file =
            fs::read_to_string("tests/examples/fail/basic.fly").expect("could not read input");
        let m = fly::parse(&file).expect("parse error");
        insta::assert_yaml_snapshot!(z3_verify(&m).expect_err("verification should fail"), {
            ".fails[].error.symbols" => insta::sorted_redaction(),
        });
    }

    #[test]
    fn test_verify_safety1() {
        let file =
            fs::read_to_string("tests/examples/success/safety1.fly").expect("could not read input");
        let m = fly::parse(&file).expect("parse error");
        assert_eq!(z3_verify(&m), Ok(()));
    }

    #[test]
    fn test_verify_safety1_fail() {
        let file = fs::read_to_string("tests/examples/fail/safety1_ind.fly")
            .expect("could not read input");
        let m = fly::parse(&file).expect("parse error");
        insta::assert_yaml_snapshot!(z3_verify(&m).expect_err("verification should fail"), {
            ".fails[].error.symbols" => insta::sorted_redaction(),
        });
    }
}

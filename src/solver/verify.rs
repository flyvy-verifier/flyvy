// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::collections::HashMap;

use codespan_reporting::diagnostic::{Diagnostic, Label};
use serde::Serialize;

use super::{
    backends::GenericBackend,
    safety::InvariantAssertion,
    solver::{Backend, Solver},
};
use crate::{
    fly::{
        printer,
        semantics::Model,
        syntax::{Module, Signature, Span, Term, ThmStmt},
    },
    smtlib::proc::SatResp,
    term::FirstOrder,
};

#[derive(Debug, Copy, Clone, Serialize, PartialEq, Eq)]
pub enum FailureType {
    FirstOrder,
    InitInv,
    NotInductive,
    Unsupported,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub enum QueryError {
    Sat(Model),
    Unknown(String),
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct AssertionFailure {
    loc: Span,
    reason: FailureType,
    pub error: QueryError,
}

impl AssertionFailure {
    pub fn diagnostic<FileId>(&self, file_id: FileId) -> Diagnostic<FileId> {
        let msg = match self.reason {
            FailureType::FirstOrder => "assertion failure",
            FailureType::InitInv => "init does not imply invariant",
            FailureType::NotInductive => "invariant is not inductive",
            FailureType::Unsupported => "unsupported assertion",
        };
        Diagnostic::error()
            .with_message(msg)
            .with_labels(vec![Label::primary(file_id, self.loc.start..self.loc.end)])
            .with_notes(vec![match &self.error {
                QueryError::Sat(model) => format!("counter example:\n{}", model.fmt()),
                QueryError::Unknown(err) => format!("smt solver returned unknown: {err}"),
            }])
    }
}

#[derive(Debug, Clone, Default, Serialize, PartialEq, Eq)]
pub struct SolveError {
    pub fails: Vec<AssertionFailure>,
}

impl SolveError {
    fn push(&mut self, e: AssertionFailure) {
        self.fails.push(e);
    }
}

pub struct SolverConf {
    pub backend: GenericBackend,
    pub tee: Option<String>,
}

impl SolverConf {
    fn solver(&self, sig: &Signature, n_states: usize) -> Solver<&GenericBackend> {
        // TODO: failures to start the solver should be bubbled up to user nicely
        Solver::new(sig, n_states, &self.backend, self.tee.clone()).expect("could not start solver")
    }
}

fn verify_term<B: Backend>(solver: &mut Solver<B>, t: Term) -> Result<(), QueryError> {
    solver.assert(&Term::negate(t));
    let resp = solver.check_sat(HashMap::new()).expect("error in solver");
    match resp {
        SatResp::Sat { .. } => {
            let states = solver.get_model();
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
        Solver::new(sig, n, &conf.backend, conf.tee.clone()).expect("could not start solver");
    for assume in assumes {
        solver.assert(assume);
    }
    solver.comment_with(|| format!("assert {}", printer::term(assert)));
    verify_term(&mut solver, assert.clone())
}

pub fn verify(conf: &SolverConf, m: &Module) -> Result<(), SolveError> {
    // assumptions/assertions so far
    let mut assumes: Vec<&Term> = vec![];
    let mut errors = SolveError::default();
    for step in &m.statements {
        match step {
            ThmStmt::Assume(e) => assumes.push(e),
            ThmStmt::Assert(pf) => {
                if let Some(n) = FirstOrder::unrolling(&pf.assert.x) {
                    let res = verify_firstorder(conf, &m.signature, n + 1, &assumes, &pf.assert.x);
                    if let Err(cex) = res {
                        errors.push(AssertionFailure {
                            loc: pf.assert.span,
                            reason: FailureType::FirstOrder,
                            error: cex,
                        });
                    }
                } else if let Ok(assert) = InvariantAssertion::for_assert(&assumes, &pf.assert.x) {
                    {
                        let inv_assert = assert.inv_assertion();
                        let mut solver = conf.solver(&m.signature, 2);
                        solver.comment_with(|| {
                            format!("init implies: {}", printer::term(&assert.inv))
                        });
                        let res = verify_term(&mut solver, inv_assert.0);
                        if let Err(cex) = res {
                            errors.push(AssertionFailure {
                                loc: pf.assert.span,
                                reason: FailureType::InitInv,
                                error: cex,
                            })
                        }
                    }
                    {
                        let next_assert = assert.next_assertion();
                        let mut solver = conf.solver(&m.signature, 2);
                        solver
                            .comment_with(|| format!("inductive: {}", printer::term(&assert.inv)));
                        let res = verify_term(&mut solver, next_assert.0);
                        if let Err(cex) = res {
                            errors.push(AssertionFailure {
                                loc: pf.assert.span,
                                reason: FailureType::NotInductive,
                                error: cex,
                            })
                        }
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
        solver::backends::{GenericBackend, SolverType},
    };

    use super::{verify, SolveError, SolverConf};

    fn z3_verify(m: &Module) -> Result<(), SolveError> {
        // optionally override Z3 command
        let z3_cmd = env::var_os("Z3_BIN")
            .map(|val| val.to_string_lossy().to_string())
            .unwrap_or("z3".to_string());
        let conf = SolverConf {
            backend: GenericBackend::new(SolverType::Z3, &z3_cmd),
            tee: None,
        };
        verify(&conf, m)
    }

    #[test]
    fn test_verify_failing2() {
        let file = fs::read_to_string("examples/fail/basic.fly").expect("could not read input");
        let m = fly::parse(&file).expect("parse error");
        insta::assert_yaml_snapshot!(z3_verify(&m).expect_err("verification should fail"), {
            ".fails[].error.symbols" => insta::sorted_redaction(),
        });
    }

    #[test]
    fn test_verify_safety1() {
        let file =
            fs::read_to_string("examples/success/safety1.fly").expect("could not read input");
        let m = fly::parse(&file).expect("parse error");
        assert_eq!(z3_verify(&m), Ok(()));
    }

    #[test]
    fn test_verify_safety1_fail() {
        let file =
            fs::read_to_string("examples/fail/safety1_ind.fly").expect("could not read input");
        let m = fly::parse(&file).expect("parse error");
        insta::assert_yaml_snapshot!(z3_verify(&m).expect_err("verification should fail"), {
            ".fails[].error.symbols" => insta::sorted_redaction(),
        });
    }
}

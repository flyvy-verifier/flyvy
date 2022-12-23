// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use codespan_reporting::diagnostic::{Diagnostic, Label};
use serde::Serialize;

use super::{
    conf::{Backend, SolverConf},
    models::{parse_model, Model},
    safety::InvariantAssertion,
    sexp,
};
use crate::{
    fly::{
        printer,
        syntax::{Module, Signature, Span, Term, ThmStmt},
    },
    smtlib::{
        proc::{SatResp, SmtProc},
        sexp::{app, atom_i, atom_s, sexp_l, Sexp},
    },
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

struct Context {
    solver: SmtProc,
    backend: Backend,
}

impl Context {
    fn new(solver: SmtProc, backend: Backend) -> Self {
        Context { solver, backend }
    }

    /// Emit encoding of signature, with mutable function unrolled to depth
    /// `unroll` (for example, 1 will emit each mutable function twice - one
    /// unprimed and one primed).
    fn signature(&mut self, s: &Signature, unroll: usize) {
        for sort in &s.sorts {
            self.solver
                .send(&app("declare-sort", [sexp::sort(sort), atom_i(0)]));
        }
        for r in &s.relations {
            self.solver.send(&app(
                "declare-fun",
                [
                    atom_s(&r.name),
                    sexp_l(r.args.iter().map(sexp::sort)),
                    sexp::sort(&r.typ),
                ],
            ));
            if r.mutable {
                for n_primes in 1..=unroll {
                    let name = &r.name;
                    self.solver.send(&app(
                        "declare-fun",
                        [
                            atom_s(format!("{name}{}", "'".repeat(n_primes))),
                            sexp_l(r.args.iter().map(sexp::sort)),
                            sexp::sort(&r.typ),
                        ],
                    ));
                }
            }
        }
    }

    fn assume(&mut self, t: &Term) {
        self.solver.send(&app("assert", [sexp::term(t)]));
    }

    fn assumes<'a, I>(&'a mut self, ts: I)
    where
        I: IntoIterator,
        I::IntoIter: Iterator<Item = &'a Term>,
    {
        for t in ts.into_iter() {
            self.assume(t)
        }
    }

    fn parse_sat(&self, sat: SatResp<Sexp>) -> Result<(), QueryError> {
        match sat {
            SatResp::Unsat => Ok(()),
            SatResp::Sat { model } => Err(QueryError::Sat(parse_model(self.backend, &model))),
            SatResp::Unknown(reason) => Err(QueryError::Unknown(reason)),
        }
    }

    /// Try to prove t and return an error if it does not hold.
    ///
    /// Consumes self because this leaves the solver in an unusable state.
    fn assert_one(mut self, t: &Term) -> Result<(), QueryError> {
        let e = sexp::negated_term(t);
        self.solver.send(&app("assert", [e]));
        let sat = self
            .solver
            .check_sat_model()
            .expect("could not check assertion");
        self.parse_sat(sat)
    }
}

impl SolverConf {
    fn new_ctx(&self, sig: &Signature, unrolling: usize) -> Context {
        let mut ctx = Context::new(self.launch(), self.backend);
        ctx.signature(sig, unrolling);
        ctx
    }

    fn verify_separate(&self, m: &Module) -> Result<(), SolveError> {
        // assumptions/assertions so far
        let mut assumes: Vec<&Term> = vec![];
        let mut errors = SolveError::default();
        for step in &m.statements {
            match step {
                ThmStmt::Assume(e) => assumes.push(e),
                ThmStmt::Assert(pf) => {
                    if let Some(n) = FirstOrder::unrolling(&pf.assert.x) {
                        let mut ctx = self.new_ctx(&m.signature, n);
                        ctx.assumes(assumes.iter().copied());
                        ctx.solver
                            .comment_with(|| format!("assert {}", printer::term(&pf.assert.x)));
                        // this runs the solver and terminates the instance
                        if let Err(cex) = ctx.assert_one(&pf.assert.x) {
                            errors.push(AssertionFailure {
                                loc: pf.assert.span,
                                reason: FailureType::FirstOrder,
                                error: cex,
                            });
                        }
                    } else if let Ok(assert) =
                        InvariantAssertion::for_assert(&assumes, &pf.assert.x)
                    {
                        {
                            let inv_assert = assert.inv_assertion();
                            let mut ctx = self.new_ctx(&m.signature, 0);
                            ctx.solver.comment_with(|| {
                                format!("init implies: {}", printer::term(&assert.inv))
                            });
                            if let Err(cex) = ctx.assert_one(&inv_assert.0) {
                                errors.push(AssertionFailure {
                                    loc: pf.assert.span,
                                    reason: FailureType::InitInv,
                                    error: cex,
                                })
                            }
                        }
                        {
                            let next_assert = assert.next_assertion();
                            let mut ctx = self.new_ctx(&m.signature, 1);
                            ctx.solver.comment_with(|| {
                                format!("inductive: {}", printer::term(&assert.inv))
                            });
                            if let Err(cex) = ctx.assert_one(&next_assert.0) {
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

    pub fn verify(&self, m: &Module) -> Result<(), SolveError> {
        self.verify_separate(m)
    }
}

#[cfg(test)]
mod tests {
    use std::{env, fs};

    use crate::{
        fly::{self, syntax::Module},
        solver::conf::{Backend, SolverConf},
    };

    use super::SolveError;

    fn z3_verify(m: &Module) -> Result<(), SolveError> {
        // optionally override Z3 command
        let z3_cmd = env::var_os("Z3_BIN")
            .map(|val| val.to_string_lossy().to_string())
            .unwrap_or("z3".to_string());
        let conf = SolverConf {
            tee: None,
            backend: Backend::Z3,
            solver_bin: z3_cmd,
        };
        conf.verify(m)
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

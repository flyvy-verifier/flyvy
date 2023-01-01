// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::collections::{HashMap, HashSet};

use super::error::{AssertionFailure, FailureType, QueryError, SolveError};
use super::safety::InvariantAssertion;
use crate::fly::syntax::Proof;
use crate::term::Next;
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

pub fn verify_module(conf: &SolverConf, m: &Module, houdini: bool) -> Result<(), SolveError> {
    let check_invariant = |pf: &Proof, assert: &InvariantAssertion| {
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

    let run_houdini = |pf: &Proof, assert: &InvariantAssertion| {
        let mut invs = vec![&assert.inv];
        invs.extend(assert.proof_invs.iter());
        println!("Running Houdinig, candidate invariants are:");
        for &p in &invs {
            println!("    {p}")
        }
        println!("");

        {
            // filter based on initiation
            println!("Checking initiation:");
            let mut not_implied: HashSet<&Term> = HashSet::new();
            for &q in &invs {
                if not_implied.contains(q) {
                    continue;
                };
                println!("    Checking {q}");
                let mut solver = conf.solver(&m.signature, 1);
                solver.assert(&assert.init);
                solver.assert(&Term::negate(q.clone()));
                let resp = solver.check_sat(HashMap::new()).expect("error in solver");
                match resp {
                    SatResp::Sat => {
                        println!("        Got model");
                        let states = solver.get_model();
                        assert_eq!(states.len(), 1);
                        // TODO(oded): make 0 and 1 special constants for this use
                        assert_eq!(states[0].eval(&assert.init, None), 1);
                        assert_eq!(states[0].eval(q, None), 0);
                        for &qq in &invs {
                            if states[0].eval(qq, None) == 0 {
                                println!("        Pruning {qq}");
                                not_implied.insert(qq);
                            }
                        }
                    }
                    SatResp::Unsat => (),
                    SatResp::Unknown(m) => {
                        return Err(AssertionFailure {
                            loc: pf.assert.span,
                            reason: FailureType::InitInv,
                            error: QueryError::Unknown(m),
                        });
                    }
                }
            }
            invs = invs
                .into_iter()
                .filter(|q| !not_implied.contains(q))
                .collect();
        }
        println!("Candidate invariants are:");
        for &p in &invs {
            println!("    {p}")
        }
        println!("");

        // compute fixed point
        println!("Computing fixed point:");
        loop {
            let mut not_implied: HashSet<&Term> = HashSet::new();
            for &q in &invs {
                if not_implied.contains(q) {
                    continue;
                };
                println!("    Checking {q}");
                let mut solver = conf.solver(&m.signature, 2);
                for &p in &invs {
                    solver.assert(p);
                }
                solver.assert(&assert.next);
                solver.assert(&Term::negate(Next::prime(q)));
                let resp = solver.check_sat(HashMap::new()).expect("error in solver");
                match resp {
                    SatResp::Sat => {
                        println!("        Got model");
                        let states = solver.get_model();
                        assert_eq!(states.len(), 2);
                        // TODO(oded): make 0 and 1 special constants for their use as Booleans
                        assert_eq!(states[1].eval(q, None), 0);
                        for &qq in &invs {
                            if states[1].eval(qq, None) == 0 {
                                println!("        Pruning {qq}");
                                not_implied.insert(qq);
                            }
                        }
                    }
                    SatResp::Unsat => (),
                    SatResp::Unknown(m) => {
                        return Err(AssertionFailure {
                            loc: pf.assert.span,
                            reason: FailureType::NotInductive,
                            error: QueryError::Unknown(m),
                        });
                    }
                }
            }
            if not_implied.is_empty() {
                // fixed poined reached
                println!("Fixed point reached");
                break;
            }
            invs = invs
                .into_iter()
                .filter(|q| !not_implied.contains(q))
                .collect();
            println!("Candidate invariants are:");
            for &p in &invs {
                println!("    {p}")
            }
            println!("");
        }
        if invs.is_empty() || invs[0] != &assert.inv {
            return Err(AssertionFailure {
                loc: pf.assert.span,
                reason: FailureType::NotInductive,
                error: QueryError::Unknown("assertion not in fixed point".to_string()), // TODO(oded): better error reporting
            });
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
                    let res = if houdini {
                        run_houdini(&pf, &assert)
                    } else {
                        check_invariant(&pf, &assert)
                    };
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
        solver::backends::{GenericBackend, SolverType},
    };

    use super::{verify_module, SolveError, SolverConf};

    fn z3_verify(m: &Module) -> Result<(), SolveError> {
        // optionally override Z3 command
        let z3_cmd = env::var_os("Z3_BIN")
            .map(|val| val.to_string_lossy().to_string())
            .unwrap_or("z3".to_string());
        let conf = SolverConf {
            backend: GenericBackend::new(SolverType::Z3, &z3_cmd),
            tee: None,
        };
        verify_module(&conf, m, false)
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

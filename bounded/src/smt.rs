// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A bounded model checker for flyvy programs using an SMT solver.
//! This is useful, even though it's slow, because it doesn't require sort bounds.

use fly::semantics::Model;
use fly::{syntax::*, term::prime::Next, transitions::*};
use solver::{conf::SolverConf, SatResp};
use std::collections::HashMap;
use thiserror::Error;

#[allow(missing_docs)]
#[derive(Error, Debug)]
pub enum CheckerError {
    #[error("{0}")]
    ExtractionError(ExtractionError),
    #[error("{0}")]
    SolverError(String),
}

/// The result of a successful run of the bounded model checker
#[derive(Debug, PartialEq)]
pub enum CheckerAnswer {
    /// The checker found a counterexample
    Counterexample(Vec<Model>),
    /// The checker did not find a counterexample
    Unknown,
}

/// Check a given Module out to some depth.
/// The checker ignores proof blocks.
pub fn check(
    module: &Module,
    conf: &SolverConf,
    depth: usize,
    print_timing: bool,
) -> Result<CheckerAnswer, CheckerError> {
    if !module.defs.is_empty() {
        panic!("definitions are not supported yet");
    }

    let d = extract(module).map_err(CheckerError::ExtractionError)?;
    let inits = d.inits.iter().chain(&d.axioms).cloned();
    let transitions = d
        .transitions
        .iter()
        .chain(d.mutable_axioms(&module.signature.relations))
        .cloned();
    let safeties = d.proofs.iter().map(|proof| proof.safety.x.clone());

    let next = Next::new(&module.signature);

    let init = Term::and(inits);
    let mut tr = Term::and(transitions);
    let mut not_safe = Term::negate(Term::and(safeties));

    let mut program = vec![init];
    for _ in 0..depth {
        program.push(tr.clone());
        not_safe = next.prime(&not_safe);
        tr = next.prime(&tr);
    }
    program.push(not_safe);

    println!("starting search...");
    let search = std::time::Instant::now();

    let mut solver = conf.solver(&module.signature, depth + 1);
    solver.assert(&Term::and(program));
    let answer = match solver.check_sat(HashMap::new()).expect("error in solver") {
        SatResp::Sat { .. } => {
            let states = solver
                .get_minimal_model()
                .expect("solver error while minimizing");
            CheckerAnswer::Counterexample(states)
        }
        SatResp::Unsat => CheckerAnswer::Unknown,
        SatResp::Unknown(m) => return Err(CheckerError::SolverError(m)),
    };

    if print_timing {
        println!("search finished in {:0.1}s", search.elapsed().as_secs_f64());
    }

    Ok(answer)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fly::sorts::sort_check_and_infer;
    use solver::backends::{GenericBackend, SolverType};
    use solver::solver_path;

    fn conf() -> SolverConf {
        SolverConf {
            backend: GenericBackend::new(SolverType::Z3, &solver_path("z3")),
            tee: None,
        }
    }

    #[test]
    fn checker_smt_basic() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/tests/examples/basic2.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();

        assert_eq!(CheckerAnswer::Unknown, check(&module, &conf(), 0, false)?);
        assert!(matches!(
            check(&module, &conf(), 1, false)?,
            CheckerAnswer::Counterexample(..),
        ));

        Ok(())
    }

    #[test]
    fn checker_smt_lockserver() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/examples/lockserver.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();

        assert_eq!(CheckerAnswer::Unknown, check(&module, &conf(), 10, false)?);

        Ok(())
    }

    #[ignore]
    #[test]
    fn checker_smt_lockserver_buggy() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/tests/examples/lockserver_buggy.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();

        let bug = check(&module, &conf(), 12, false)?;
        assert!(matches!(bug, CheckerAnswer::Counterexample(..)));

        let too_short = check(&module, &conf(), 11, false)?;
        assert_eq!(CheckerAnswer::Unknown, too_short);

        Ok(())
    }

    #[test]
    fn checker_smt_consensus() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/examples/consensus.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();

        assert_eq!(CheckerAnswer::Unknown, check(&module, &conf(), 5, false)?);

        Ok(())
    }

    #[test]
    fn checker_smt_immutability() -> Result<(), CheckerError> {
        let source =
            include_str!("../../temporal-verifier/tests/examples/success/immutability.fly");
        let mut module = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();

        assert_eq!(CheckerAnswer::Unknown, check(&module, &conf(), 10, false)?);
        Ok(())
    }
}

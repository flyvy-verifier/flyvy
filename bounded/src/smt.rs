// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A bounded model checker for flyvy programs using the [CaDiCaL][cadical] SAT solver.
//!
//! [cadical]: https://fmv.jku.at/cadical/

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
        todo!("definitions are not supported yet");
    }

    let DestructuredModule {
        inits,
        transitions,
        axioms,
        proofs,
    } = extract(module).map_err(CheckerError::ExtractionError)?;

    let inits: Vec<_> = inits.into_iter().chain(axioms.clone()).collect();
    let transitions: Vec<_> = transitions.into_iter().chain(axioms).collect();
    let safeties: Vec<_> = proofs.into_iter().map(|proof| proof.safety.x).collect();

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

    if let CheckerAnswer::Counterexample(ref models) = answer {
        for (i, model) in models.iter().enumerate() {
            println!("state {}:", i);
            println!("{}", model.fmt());
        }
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
        let source = "
mutable x: bool

assume x

assume always (x -> !x')

assert always x
        ";

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

        assert_eq!(CheckerAnswer::Unknown, check(&module, &conf(), 10, false)?);

        Ok(())
    }

    #[ignore] // too slow
    #[test]
    fn checker_smt_lockserver_buggy() -> Result<(), CheckerError> {
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
            (((unlock_msg(N))') <-> unlock_msg(N)) &
            ((server_holds_lock)')) &
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) &
        (forall x0:node. ((grant_msg(x0))') = grant_msg(x0)) &
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0)))

# safety:
assert always (forall N1:node, N2:node. holds_lock(N1) & holds_lock(N2) -> N1 = N2)
        ";

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
        let source = "
sort node
sort quorum
sort value

# relations:
immutable member(node, quorum): bool
mutable vote_request_msg(node, node): bool
mutable voted(node): bool
mutable vote_msg(node, node): bool
mutable votes(node, node): bool
mutable leader(node): bool
mutable decided(node, value): bool

# init:
assume (forall N1:node, N2:node. !vote_request_msg(N1, N2)) & (forall N:node. !voted(N)) &
    (forall N1:node, N2:node. !vote_msg(N1, N2)) & (forall N1:node, N2:node. !votes(N1, N2)) &
    (forall N1:node. !leader(N1)) & (forall N:node, V:value. !decided(N, V))

# transitions:
assume always (exists src:node, dst:node. (forall N1:node, N2:node. (vote_request_msg(N1, N2))' <->
    vote_request_msg(N1, N2) | N1 = src & N2 = dst) & (forall x0:node. (voted(x0))' = voted(x0)) &
    (forall x0:node, x1:node. (vote_msg(x0, x1))' = vote_msg(x0, x1)) & (forall x0:node, x1:node.
    (votes(x0, x1))' = votes(x0, x1)) & (forall x0:node. (leader(x0))' = leader(x0)) &
    (forall x0:node, x1:value. (decided(x0, x1))' = decided(x0, x1))) | (exists src:node, dst:node.
    (forall N1:node, N2:node, N:node. !voted(src) & vote_request_msg(dst, src) & ((vote_msg(N1, N2))' <->
    vote_msg(N1, N2) | N1 = src & N2 = dst) & ((voted(N))' <-> voted(N) | N = src) & (!(N1 = dst &
    N2 = src) -> ((vote_request_msg(N1, N2))' <-> vote_request_msg(N1, N2)))) & (forall x0:node, x1:node.
    (votes(x0, x1))' = votes(x0, x1)) & (forall x0:node. (leader(x0))' = leader(x0)) & (forall x0:node,
    x1:value. (decided(x0, x1))' = decided(x0, x1))) | (exists n:node, sender:node. (forall N1:node, N2:node.
    vote_msg(sender, n) & ((votes(N1, N2))' <-> votes(N1, N2) | N1 = n & N2 = sender)) & (forall x0:node,
    x1:node. (vote_request_msg(x0, x1))' = vote_request_msg(x0, x1)) & (forall x0:node. (voted(x0))' = voted(x0))
    & (forall x0:node, x1:node. (vote_msg(x0, x1))' = vote_msg(x0, x1)) & (forall x0:node. (leader(x0))' =
    leader(x0)) & (forall x0:node, x1:value. (decided(x0, x1))' = decided(x0, x1))) | (exists n:node, q:quorum.
    (forall N:node. (member(N, q) -> votes(n, N)) & ((leader(N))' <-> leader(N) | N = n)) & (forall x0:node,
    x1:node. (vote_request_msg(x0, x1))' = vote_request_msg(x0, x1)) & (forall x0:node. (voted(x0))' = voted(x0))
    & (forall x0:node, x1:node. (vote_msg(x0, x1))' = vote_msg(x0, x1)) & (forall x0:node, x1:node.
    (votes(x0, x1))' = votes(x0, x1)) & (forall x0:node, x1:value. (decided(x0, x1))' = decided(x0, x1))) |
    (exists n:node, v:value. (forall V:value, N:node. leader(n) & !decided(n, V) & ((decided(N, V))' <->
    decided(N, V) | N = n & V = v)) & (forall x0:node, x1:node. (vote_request_msg(x0, x1))' =
    vote_request_msg(x0, x1)) & (forall x0:node. (voted(x0))' = voted(x0)) & (forall x0:node, x1:node.
    (vote_msg(x0, x1))' = vote_msg(x0, x1)) & (forall x0:node, x1:node. (votes(x0, x1))' = votes(x0, x1)) &
    (forall x0:node. (leader(x0))' = leader(x0)))

# added by hand
# axiom
assume always (forall Q1:quorum, Q2:quorum. exists N:node. member(N, Q1) & member(N, Q2))

# safety:
assert always (forall N1:node, V1:value, N2:node, V2:value. decided(N1, V1) & decided(N2, V2) -> V1 = V2)
        ";

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();

        assert_eq!(CheckerAnswer::Unknown, check(&module, &conf(), 5, false)?);

        Ok(())
    }

    #[test]
    fn checker_smt_immutability() -> Result<(), CheckerError> {
        let source = "
immutable r: bool
assume r
assert always r
        ";
        let mut module = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();

        assert_eq!(CheckerAnswer::Unknown, check(&module, &conf(), 10, false)?);
        Ok(())
    }
}

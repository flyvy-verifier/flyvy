// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, fs};

    use rayon::prelude::*;

    use crate::{
        fly::{
            self,
            syntax::{Proof, Term, ThmStmt},
        },
        smtlib::proc::SatResp,
        solver::{
            backends::{GenericBackend, SolverType},
            solver_path,
        },
        term::Next,
        verify::{safety::InvariantAssertion, SolverConf},
    };

    #[test]
    fn test_concurrent_verify() {
        let file =
            fs::read_to_string("examples/consensus_epr.fly").expect("could not find test file");
        let m = fly::parse(&file).expect("could not parse test file");

        let assumes: Vec<&Term> = m
            .statements
            .iter()
            .filter_map(|s| match s {
                ThmStmt::Assume(t) => Some(t),
                _ => None,
            })
            .collect();
        let pf: &Proof = m
            .statements
            .iter()
            .filter_map(|s| match s {
                ThmStmt::Assert(pf) => Some(pf),
                _ => None,
            })
            .next()
            .expect("should have one assertion");
        let pf_invs = pf.invariants.iter().map(|inv| &inv.x).collect::<Vec<_>>();
        let inv_assert = InvariantAssertion::for_assert(&assumes, &pf.assert.x, &pf_invs)
            .expect("should be an invariant assertion");

        let backend = GenericBackend::new(SolverType::Z3, &solver_path("z3"));
        let conf = SolverConf { backend, tee: None };

        // we'll assume proof_inv (all the invariants) in the pre state and try
        // to prove Next::prime(inv) in the post state for each proof invariant
        // separately
        let proof_inv = Term::and(inv_assert.proof_invs);
        // rayon provides .par_iter(), which performs the invariant checks in
        // parallel; then we gather up a Vec of all the results due to the
        // `.collect()`.
        let results = pf_invs
            .par_iter()
            .map(|inv| {
                // not bothering to check initiation
                let mut solver = conf.solver(&m.signature, 2);
                solver.assert(&inv_assert.next);
                solver.assert(&inv_assert.assumed_inv);
                solver.assert(&Next::prime(&inv_assert.assumed_inv));
                solver.assert(&proof_inv);
                solver.assert(&Term::negate(Next::prime(inv)));
                return solver.check_sat(HashMap::new());
            })
            .collect::<Vec<_>>();
        for r in results {
            match r {
                Ok(resp) => assert!(resp == SatResp::Unsat, "invariant is not inductive"),
                Err(err) => panic!("something went wrong in solver: {err}"),
            }
        }
    }
}

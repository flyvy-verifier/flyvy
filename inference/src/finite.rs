// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Infer an inductive invariant from the set of reachable states
//! with small sort bounds.

use bounded::bdd::*;
use fly::syntax::*;
use std::collections::HashMap;

pub fn invariant(module: &Module) -> Result<Option<Term>, CheckerError> {
    let mut universe = HashMap::new();
    for sort in &module.signature.sorts {
        universe.insert(sort.clone(), 2);
    }

    let _bdd = match check(module, &universe, None, false) {
        Ok(CheckerAnswer::Convergence(bdd)) => bdd,
        Ok(CheckerAnswer::Counterexample(_)) => return Ok(None),
        Ok(CheckerAnswer::Unknown) => unreachable!(),
        Err(e) => return Err(e),
    };

    todo!()
}

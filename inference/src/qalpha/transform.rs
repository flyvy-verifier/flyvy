// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Define transformations of predicates during qalpha

use itertools::Itertools;
use std::sync::Arc;

use crate::qalpha::{
    quant::{QuantifierConfig, QuantifierPrefix},
    subsume::{Clause, Element},
    weaken::{LemmaQf, LemmaSet},
};

fn has_opposing_literals(clause: &<Clause as Element>::Base) -> bool {
    clause
        .iter()
        .any(|literal| clause.contains(&literal.negate()))
}

pub fn into_equivalent_clause<E: Element, L: LemmaQf<Body = E>>(
    prefix: Arc<QuantifierPrefix>,
    body: E,
    config: &QuantifierConfig,
    lemma_set: &LemmaSet<E>,
) -> Option<(Arc<QuantifierPrefix>, E)> {
    let clauses = body.to_cnf().0;
    let universal_prefix = config.as_universal();
    let bodies = clauses
        .into_iter()
        .filter(|clause| !has_opposing_literals(&clause.to_base(true)))
        .map(|clause| L::body_from_clause(clause));

    let not_subsumed = bodies
        .filter(|body| !lemma_set.subsumes(&universal_prefix.restrict(body.ids()), body))
        .collect_vec();

    match not_subsumed.len() {
        0 => None,
        1 => {
            let new_body = not_subsumed.into_iter().next().unwrap();
            let new_prefix = Arc::new(prefix.restrict(new_body.ids()));
            Some((new_prefix, new_body))
        }
        _ => Some((prefix, body)),
    }
}

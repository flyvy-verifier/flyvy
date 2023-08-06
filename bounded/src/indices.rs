// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A structure that can map between (relation name, arguments) pairs and indices.

use crate::quantenum::*;
use fly::{ouritertools::OurItertools, semantics::*, syntax::*};
use std::collections::HashMap;

/// Holds a map from (relation name, arguments) pairs to a number. The number is used
/// for different purposes depending on the checker, but this is common functionality
/// among most of the bounded model checkers. This map also keeps track of the number
/// of primes on mutable relations, and also supports creating unique indices that
/// don't correspond to relations. It also remembers the signature and universe that
/// were used to create it, because functions that need this object frequently also
/// need the signature or the universe, and this means that they don't need to accept
/// them separately.
pub struct Indices<'a> {
    /// The signature used to create this object
    pub signature: &'a Signature,
    /// The universe used to create this object
    pub universe: &'a UniverseBounds,
    /// The number of copies of mutable relations that this object holds
    pub num_mutable_copies: usize,
    /// The number of indices in one copy of the mutable relations
    pub num_mutables: usize,
    /// The total number of indices that are tracked
    pub num_vars: usize,
    /// The map that this object is wrapping
    indices: HashMap<&'a str, HashMap<Vec<Element>, (usize, bool)>>,
}

impl Indices<'_> {
    /// Create a new `Indices` object from a signature, universe bounds, and the number
    /// of mutable copies to include.
    pub fn new<'a>(
        signature: &'a Signature,
        universe: &'a UniverseBounds,
        num_mutable_copies: usize,
    ) -> Indices<'a> {
        let (mutable, immutable): (Vec<_>, Vec<_>) = signature
            .relations
            .iter()
            .partition(|relation| relation.mutable);
        let elements = |relation: &&'a RelationDecl| {
            relation
                .args
                .iter()
                .map(|sort| cardinality(universe, sort))
                .map(|card| (0..card).collect::<Vec<usize>>())
                .multi_cartesian_product_fixed()
                .map(|element| (relation.name.as_str(), element))
                .collect::<Vec<_>>()
        };

        let mut indices: HashMap<_, HashMap<_, _>> = HashMap::new();

        let mut num_mutables = 0;
        for (i, (r, e)) in mutable.iter().flat_map(elements).enumerate() {
            num_mutables += 1;
            indices.entry(r).or_default().insert(e, (i, true));
        }
        let mut num_immutables = 0;
        for (i, (r, e)) in immutable.iter().flat_map(elements).enumerate() {
            num_immutables += 1;
            indices
                .entry(r)
                .or_default()
                .insert(e, (num_mutables * num_mutable_copies + i, false));
        }

        Indices {
            signature,
            universe,
            indices,
            num_mutable_copies,
            num_mutables,
            num_vars: num_mutables * num_mutable_copies + num_immutables,
        }
    }

    /// Get an index from the information contained in a `Term::App`.
    pub fn get(&self, relation: &str, primes: usize, elements: &[usize]) -> usize {
        assert!(primes < self.num_mutable_copies);
        let (mut i, mutable) = self.indices[relation][elements];
        if mutable {
            i += primes * self.num_mutables;
        }
        i
    }

    /// Create a new unique index that doesn't correspond to a relation.
    pub fn var(&mut self) -> usize {
        self.num_vars += 1;
        self.num_vars - 1
    }

    /// Returns an iterator over one copy of the mutable and immutable indices
    pub fn iter(&self) -> impl Iterator<Item = (&&str, &HashMap<Vec<Element>, (usize, bool)>)> {
        self.indices.iter()
    }
}

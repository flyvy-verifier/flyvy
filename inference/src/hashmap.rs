// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Aliases for HashMap and HashSet with deterministic iteration order.

use fxhash::FxBuildHasher;
use std::hash::Hash;

/// HashMap with deterministic iteration order
pub type HashMap<K, V> = indexmap::IndexMap<K, V, FxBuildHasher>;
/// HashSet with deterministic iteration order
pub type HashSet<K> = indexmap::IndexSet<K, FxBuildHasher>;

// pub type HashMap<K, V> = std::collections::HashMap<K, V>;
// pub type HashSet<K> = std::collections::HashSet<K>;

/// Construct a deterministic HashSet from a `std::collections::HashSet`.
pub fn set_from_std<K: Eq + Hash>(s: std::collections::HashSet<K>) -> HashSet<K> {
    s.into_iter().collect()
}

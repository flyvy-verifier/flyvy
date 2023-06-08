use fxhash::FxBuildHasher;
use std::hash::Hash;

pub type HashMap<K, V> = indexmap::IndexMap<K, V, FxBuildHasher>;
pub type HashSet<K> = indexmap::IndexSet<K, FxBuildHasher>;

// pub type HashMap<K, V> = std::collections::HashMap<K, V>;
// pub type HashSet<K> = std::collections::HashSet<K>;

pub fn set_from_std<K: Eq + Hash>(s: std::collections::HashSet<K>) -> HashSet<K> {
    s.into_iter().collect()
}

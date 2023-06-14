// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Define the abstract notion of subsumption, and provide efficient data structures
//! for the handling of elements implementing subsumption.

use std::{cmp::Ordering, fmt::Debug, hash::Hash};

use itertools::Itertools;

use crate::inference::atoms::Literal;
use crate::inference::hashmap::{HashMap, HashSet};

pub trait OrderSubsumption: Clone + Eq + Hash + Ord + Send + Sync {
    type Base: Hash + Debug;
    type Map<V: Clone + Send + Sync>: SubsumptionMap<Key = Self, Value = V>;

    fn leq(&self, other: &Self) -> bool;

    fn subsumes(&self, other: &Self) -> bool;

    fn to_base(&self) -> Self::Base;

    fn from_base(base: Self::Base) -> Self;

    fn leq_cmp(&self, other: &Self) -> Ordering {
        if self == other {
            Ordering::Equal
        } else if self.leq(other) {
            Ordering::Less
        } else {
            Ordering::Greater
        }
    }
}

pub trait SubsumptionMap: Clone + Send + Sync {
    type Key: OrderSubsumption;
    type Value: Clone + Send + Sync;

    fn new() -> Self;

    fn is_empty(&self) -> bool;

    fn len(&self) -> usize;

    fn keys(&self) -> Vec<Self::Key>;

    fn insert(&mut self, key: Self::Key, value: Self::Value);

    fn remove(&mut self, key: &Self::Key) -> Self::Value;

    fn get(&self, key: &Self::Key) -> Option<&Self::Value>;

    fn get_mut(&mut self, key: &Self::Key) -> Option<&mut Self::Value>;

    fn get_subsuming(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)>;

    fn get_subsumed(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)>;
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Reversed<O: OrderSubsumption>(O);

impl<O: OrderSubsumption> PartialOrd for Reversed<O> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.leq_cmp(other))
    }
}

impl<O: OrderSubsumption> Ord for Reversed<O> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.leq_cmp(other)
    }
}

impl<O: OrderSubsumption> OrderSubsumption for Reversed<O> {
    type Base = O::Base;
    type Map<V: Clone + Send + Sync> = ReversedSubsumptionMap<O::Map<V>>;

    fn leq(&self, other: &Self) -> bool {
        other.0.leq(&self.0)
    }

    fn subsumes(&self, other: &Self) -> bool {
        other.0.subsumes(&self.0)
    }

    fn to_base(&self) -> Self::Base {
        self.0.to_base()
    }

    fn from_base(base: Self::Base) -> Self {
        Reversed(O::from_base(base))
    }
}

impl<O: OrderSubsumption> Reversed<O> {
    fn vec_cloned(v: &[O]) -> Vec<Self> {
        Self::vec(v.into_iter().cloned())
    }

    fn vec<I: DoubleEndedIterator<Item = O>>(iter: I) -> Vec<Self> {
        iter.rev().map(|o| Reversed(o)).collect_vec()
    }
}

#[derive(Clone)]
pub struct ReversedSubsumptionMap<M: SubsumptionMap>(M);

impl<M: SubsumptionMap> SubsumptionMap for ReversedSubsumptionMap<M> {
    type Key = Reversed<M::Key>;
    type Value = M::Value;

    fn new() -> Self {
        Self(M::new())
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn keys(&self) -> Vec<Self::Key> {
        self.0.keys().into_iter().map(|k| Reversed(k)).collect_vec()
    }

    fn insert(&mut self, key: Self::Key, value: Self::Value) {
        self.0.insert(key.0, value)
    }

    fn remove(&mut self, key: &Self::Key) -> Self::Value {
        self.0.remove(&key.0)
    }

    fn get(&self, key: &Self::Key) -> Option<&Self::Value> {
        self.0.get(&key.0)
    }

    fn get_mut(&mut self, key: &Self::Key) -> Option<&mut Self::Value> {
        self.0.get_mut(&key.0)
    }

    fn get_subsuming(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)> {
        self.0
            .get_subsumed(&key.0)
            .into_iter()
            .map(|(k, v)| (Reversed(k), v))
            .collect_vec()
    }

    fn get_subsumed(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)> {
        self.0
            .get_subsuming(&key.0)
            .into_iter()
            .map(|(k, v)| (Reversed(k), v))
            .collect_vec()
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct AndLike<O: OrderSubsumption>(Vec<O>);

pub type OrLike<O> = Reversed<AndLike<Reversed<O>>>;

impl<O: OrderSubsumption> AndLike<O> {
    fn leq_slices(and1: &[O], and2: &[O]) -> bool {
        if and2.is_empty() {
            return true;
        } else if and1.is_empty() {
            return false;
        }

        let (first1, rest1) = and1.split_first().unwrap();
        let (first2, rest2) = and2.split_first().unwrap();

        if first1 == first2 {
            Self::leq_slices(rest1, rest2)
        } else {
            first1.leq(first2)
        }
    }
}

impl<O: OrderSubsumption> PartialOrd for AndLike<O> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.leq_cmp(other))
    }
}

impl<O: OrderSubsumption> Ord for AndLike<O> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.leq_cmp(other)
    }
}

impl<O: OrderSubsumption> OrderSubsumption for AndLike<O> {
    type Base = Vec<O::Base>;
    type Map<V: Clone + Send + Sync> = AndSubsumptionMap<O, V>;

    fn leq(&self, other: &Self) -> bool {
        Self::leq_slices(&self.0, &other.0)
    }

    fn subsumes(&self, other: &Self) -> bool {
        other.0.iter().all(|elem2| {
            for elem1 in &self.0 {
                if !elem1.leq(elem2) {
                    break;
                } else if elem1.subsumes(elem2) {
                    return true;
                }
            }

            false
        })
    }

    fn to_base(&self) -> Self::Base {
        self.0.iter().map(|o| o.to_base()).collect_vec()
    }

    fn from_base(base: Self::Base) -> Self {
        let mut seq = vec![];

        for o in base.into_iter().map(|b| O::from_base(b)).sorted() {
            if seq.iter().all(|pre_o: &O| !pre_o.subsumes(&o)) {
                seq.push(o);
            }
        }

        AndLike(seq)
    }
}

struct TrieMap<O: OrderSubsumption, V: Clone + Send + Sync> {
    value: Option<V>,
    edges: Box<O::Map<Self>>,
}

impl<O: OrderSubsumption, V: Clone + Send + Sync> Clone for TrieMap<O, V> {
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            edges: self.edges.clone(),
        }
    }
}

impl<O: OrderSubsumption, V: Clone + Send + Sync> TrieMap<O, V> {
    fn new() -> Self {
        Self {
            value: None,
            edges: Box::new(O::Map::new()),
        }
    }

    fn insert(&mut self, key: &[O], value: V) {
        if key.is_empty() {
            assert!(self.value.is_none());
            self.value = Some(value);
        } else {
            let (elem, rest) = key.split_first().unwrap();

            if let Some(trie) = self.edges.get_mut(elem) {
                trie.insert(rest, value);
            } else {
                let mut trie = Self::new();
                trie.insert(rest, value);
                self.edges.insert(elem.clone(), trie);
            }
        }
    }

    fn mutate<F>(&mut self, key: &[O], f: F)
    where
        F: Fn(V) -> Option<V>,
    {
        if key.is_empty() {
            self.value = f(self.value.take().unwrap());
        } else {
            let (elem, rest) = key.split_first().unwrap();

            let trie = self.edges.get_mut(elem).unwrap();
            trie.mutate(rest, f);

            if trie.value.is_none() && trie.edges.is_empty() {
                self.edges.remove(elem);
            }
        }
    }

    fn remove(&mut self, key: &[O]) -> V {
        if key.is_empty() {
            self.value.take().unwrap()
        } else {
            let (elem, rest) = key.split_first().unwrap();

            let trie = self.edges.get_mut(elem).unwrap();
            let res = trie.remove(rest);

            if trie.value.is_none() && trie.edges.is_empty() {
                self.edges.remove(elem);
            }

            res
        }
    }

    fn get(&self, key: &[O]) -> Option<&V> {
        if key.is_empty() {
            return self.value.as_ref();
        }

        let (elem, rest) = key.split_first().unwrap();

        match self.edges.get(elem) {
            Some(trie) => trie.get(rest),
            None => None,
        }
    }

    /// assume and
    fn get_subsuming_and(&self, key: &[O], path: Vec<O>) -> Vec<(Vec<O>, &V)> {
        if key.is_empty() {
            return Vec::from_iter(self.value.as_ref().map(|v| (path, v)));
        }

        let first = key.first().unwrap();

        key.iter()
            .flat_map(|o| self.edges.get_subsuming(o))
            .filter(|(o, _)| o.leq(first))
            .flat_map(|(o, trie)| {
                let new_key = key.iter().filter(|k| !o.subsumes(k)).cloned().collect_vec();
                let mut new_path = path.clone();
                new_path.push(o.clone());

                trie.get_subsuming_and(&new_key, new_path)
            })
            .collect()
    }

    /// assume or
    fn get_subsuming_or(&self, key: &[O], path: Vec<O>) -> Vec<(Vec<O>, &V)> {
        let mut subsumed = key
            .iter()
            .flat_map(|o| self.edges.get_subsuming(o))
            .flat_map(|(o, trie)| {
                let new_key = key.iter().filter(|&k| !k.leq(&o)).cloned().collect_vec();
                let mut new_path = path.clone();
                new_path.push(o.clone());

                trie.get_subsuming_or(&new_key, new_path)
            })
            .collect_vec();

        subsumed.extend(self.value.as_ref().map(|v| (path, v)));

        subsumed
    }
}

#[derive(Clone)]
pub struct AndSubsumptionMap<O: OrderSubsumption, V: Clone> {
    keys: HashMap<usize, AndLike<O>>,
    values: HashMap<usize, V>,
    trie: TrieMap<Reversed<O>, usize>,
    subsets: TrieMap<O, HashSet<usize>>,
    next: usize,
}

impl<O: OrderSubsumption, V: Clone + Send + Sync> SubsumptionMap for AndSubsumptionMap<O, V> {
    type Key = AndLike<O>;
    type Value = V;

    fn new() -> Self {
        Self {
            keys: HashMap::default(),
            values: HashMap::default(),
            trie: TrieMap::new(),
            subsets: TrieMap::new(),
            next: 0,
        }
    }

    fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    fn len(&self) -> usize {
        self.keys.len()
    }

    fn keys(&self) -> Vec<Self::Key> {
        self.keys.values().cloned().collect_vec()
    }

    fn insert(&mut self, key: Self::Key, value: Self::Value) {
        let id = self.next;
        self.next += 1;

        let key_rev = Reversed::vec_cloned(&key.0);
        self.trie.insert(&key_rev, id);

        for subset in key.0.iter().cloned().powerset() {
            if self.subsets.get(&subset).is_none() {
                self.subsets.insert(&subset, HashSet::from_iter([id]));
            } else {
                self.subsets.mutate(&subset, |mut hs| {
                    hs.insert(id);
                    Some(hs)
                });
            }
        }

        self.keys.insert(id, key);
        self.values.insert(id, value);
    }

    fn remove(&mut self, key: &Self::Key) -> Self::Value {
        let key_rev = Reversed::vec_cloned(&key.0);
        let id = self.trie.remove(&key_rev);

        for subset in key.0.iter().cloned().powerset() {
            self.subsets.mutate(&subset, |mut hs| {
                hs.remove(&id);

                if hs.is_empty() {
                    None
                } else {
                    Some(hs)
                }
            });
        }

        self.keys.remove(&id);

        self.values.remove(&id).unwrap()
    }

    fn get(&self, key: &Self::Key) -> Option<&Self::Value> {
        let key_rev = Reversed::vec_cloned(&key.0);

        match self.trie.get(&key_rev) {
            Some(i) => self.values.get(i),
            None => None,
        }
    }

    fn get_mut(&mut self, key: &Self::Key) -> Option<&mut Self::Value> {
        let key_rev = Reversed::vec_cloned(&key.0);

        match self.trie.get(&key_rev) {
            Some(i) => self.values.get_mut(i),
            None => None,
        }
    }

    fn get_subsuming(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)> {
        self.subsets
            .get_subsuming_and(&key.0, vec![])
            .into_iter()
            .flat_map(|(_, is)| is.iter().map(|i| (self.keys[i].clone(), &self.values[i])))
            .collect_vec()
    }

    fn get_subsumed(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)> {
        let key_rev = Reversed::vec_cloned(&key.0);

        self.trie
            .get_subsuming_or(&key_rev, vec![])
            .into_iter()
            .map(|(k, i)| {
                (
                    AndLike(k.into_iter().rev().map(|r| r.0).collect_vec()),
                    &self.values[i],
                )
            })
            .collect_vec()
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Pair<O1: OrderSubsumption, O2: OrderSubsumption>(O1, O2);

impl<O1: OrderSubsumption, O2: OrderSubsumption> PartialOrd for Pair<O1, O2> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.leq_cmp(other))
    }
}

impl<O1: OrderSubsumption, O2: OrderSubsumption> Ord for Pair<O1, O2> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.leq_cmp(other)
    }
}

impl<O1: OrderSubsumption, O2: OrderSubsumption> OrderSubsumption for Pair<O1, O2> {
    type Base = (O1::Base, O2::Base);

    type Map<V: Clone + Send + Sync> = PairSubsumptionMap<O1, O2, V>;

    fn leq(&self, other: &Self) -> bool {
        if self.0 == other.0 {
            self.1.leq(&other.1)
        } else {
            self.0.leq(&other.0)
        }
    }

    fn subsumes(&self, other: &Self) -> bool {
        self.0.subsumes(&other.0) && self.1.subsumes(&other.1)
    }

    fn to_base(&self) -> Self::Base {
        (self.0.to_base(), self.1.to_base())
    }

    fn from_base(base: Self::Base) -> Self {
        Pair(O1::from_base(base.0), O2::from_base(base.1))
    }
}

#[derive(Clone)]
pub struct PairSubsumptionMap<O1: OrderSubsumption, O2: OrderSubsumption, V: Clone + Send + Sync>(
    O1::Map<O2::Map<V>>,
);

impl<O1: OrderSubsumption, O2: OrderSubsumption, V: Clone + Send + Sync> SubsumptionMap
    for PairSubsumptionMap<O1, O2, V>
{
    type Key = Pair<O1, O2>;

    type Value = V;

    fn new() -> Self {
        Self(O1::Map::new())
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn len(&self) -> usize {
        self.0
            .keys()
            .iter()
            .map(|k: &O1| self.0.get(k).unwrap().len())
            .sum()
    }

    fn keys(&self) -> Vec<Self::Key> {
        self.0
            .keys()
            .iter()
            .flat_map(|k1: &O1| {
                self.0
                    .get(k1)
                    .unwrap()
                    .keys()
                    .into_iter()
                    .map(|k2: O2| Pair(k1.clone(), k2))
            })
            .collect_vec()
    }

    fn insert(&mut self, key: Self::Key, value: Self::Value) {
        if let Some(map) = self.0.get_mut(&key.0) {
            map.insert(key.1, value);
        } else {
            let mut map = O2::Map::<V>::new();
            map.insert(key.1, value);
            self.0.insert(key.0, map);
        }
    }

    fn remove(&mut self, key: &Self::Key) -> Self::Value {
        let map = self.0.get_mut(&key.0).unwrap();
        let value = map.remove(&key.1);
        if map.is_empty() {
            self.0.remove(&key.0);
        }

        value
    }

    fn get(&self, key: &Self::Key) -> Option<&Self::Value> {
        if let Some(map) = self.0.get(&key.0) {
            map.get(&key.1)
        } else {
            None
        }
    }

    fn get_mut(&mut self, key: &Self::Key) -> Option<&mut Self::Value> {
        if let Some(map) = self.0.get_mut(&key.0) {
            map.get_mut(&key.1)
        } else {
            None
        }
    }

    fn get_subsuming(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)> {
        self.0
            .get_subsuming(&key.0)
            .into_iter()
            .flat_map(|(k1, map)| {
                map.get_subsuming(&key.1)
                    .into_iter()
                    .map(move |(k2, value)| (Pair(k1.clone(), k2), value))
            })
            .collect_vec()
    }

    fn get_subsumed(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)> {
        self.0
            .get_subsumed(&key.0)
            .into_iter()
            .flat_map(|(k1, map)| {
                map.get_subsumed(&key.1)
                    .into_iter()
                    .map(move |(k2, value)| (Pair(k1.clone(), k2), value))
            })
            .collect_vec()
    }
}

pub type Clause<L> = OrLike<L>;
pub type Cube<L> = AndLike<L>;
pub type Cnf<L> = AndLike<Clause<L>>;
pub type Dnf<L> = OrLike<Cube<L>>;
pub type PDnf<L> = Pair<Clause<L>, Dnf<L>>;

#[derive(Clone)]
pub struct EqSubsumptionMap<T: OrderSubsumption, V: Clone + Send + Sync>(HashMap<T, V>);

impl<T: OrderSubsumption, V: Clone + Send + Sync> SubsumptionMap for EqSubsumptionMap<T, V> {
    type Key = T;
    type Value = V;

    fn new() -> Self {
        Self(HashMap::default())
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn keys(&self) -> Vec<Self::Key> {
        self.0.keys().cloned().collect_vec()
    }

    fn insert(&mut self, key: Self::Key, value: Self::Value) {
        assert!(self.0.insert(key, value).is_none());
    }

    fn remove(&mut self, key: &Self::Key) -> Self::Value {
        self.0.remove(key).unwrap()
    }

    fn get(&self, key: &Self::Key) -> Option<&Self::Value> {
        self.0.get(key)
    }

    fn get_mut(&mut self, key: &Self::Key) -> Option<&mut Self::Value> {
        self.0.get_mut(key)
    }

    fn get_subsuming(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)> {
        self.0
            .get(key)
            .into_iter()
            .map(|v| (key.clone(), v))
            .collect_vec()
    }

    fn get_subsumed(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)> {
        self.0
            .get(key)
            .into_iter()
            .map(|v| (key.clone(), v))
            .collect_vec()
    }
}

impl OrderSubsumption for usize {
    type Base = Self;
    type Map<V: Clone + Send + Sync> = EqSubsumptionMap<Self, V>;

    fn leq(&self, other: &Self) -> bool {
        self <= other
    }

    fn subsumes(&self, other: &Self) -> bool {
        self == other
    }

    fn to_base(&self) -> Self::Base {
        *self
    }

    fn from_base(base: Self::Base) -> Self {
        base
    }
}

impl OrderSubsumption for Literal {
    type Base = Self;
    type Map<V: Clone + Send + Sync> = EqSubsumptionMap<Self, V>;

    fn leq(&self, other: &Self) -> bool {
        self <= other
    }

    fn subsumes(&self, other: &Self) -> bool {
        self == other
    }

    fn to_base(&self) -> Self::Base {
        *self
    }

    fn from_base(base: Self::Base) -> Self {
        base
    }
}

#[derive(Clone)]
pub struct LiteralSubsumptionMap<V>(HashMap<usize, V>);

#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use super::{Clause, Cnf, Cube, OrderSubsumption, SubsumptionMap};

    pub type ClauseMap<L, V> = <Clause<L> as OrderSubsumption>::Map<V>;
    pub type CubeMap<L, V> = <Cube<L> as OrderSubsumption>::Map<V>;
    pub type CnfMap<L, V> = <Cnf<L> as OrderSubsumption>::Map<V>;
    // pub type DnfMap<L, V> = <Dnf<L> as OrderSubsumption>::Map<V>;

    #[test]
    fn test_clause() {
        let literal_count: usize = 20;
        let clause_size = 3;
        let mut map: ClauseMap<usize, usize> = ClauseMap::new();
        let mut next = 0;

        // Add all clauses.
        for cl in (0..literal_count).combinations(clause_size) {
            let clause = Clause::from_base(cl);
            assert!(map.get_subsuming(&clause).is_empty());
            assert!(map.get_subsumed(&clause).is_empty());
            map.insert(clause, next);
            next += 1;
        }

        // Check that they're in the set.
        next = 0;
        for cl in (0..literal_count).combinations(clause_size) {
            let clause = Clause::from_base(cl);
            assert_eq!(map.get(&clause), Some(&next));
            assert_eq!(map.get_subsuming(&clause).len(), 1);
            assert_eq!(map.get_subsumed(&clause).len(), 1);
            next += 1;
        }

        // Check subsumption for sub-clauses
        for cl in (0..literal_count).combinations(clause_size - 1) {
            let clause = Clause::from_base(cl);
            assert_eq!(map.get(&clause), None);
            assert_eq!(map.get_subsuming(&clause).len(), 0);
            assert_eq!(
                map.get_subsumed(&clause).len(),
                literal_count - (clause_size - 1)
            );
        }

        // Check subsumption for super-clauses.
        for cl in (0..literal_count).combinations(clause_size + 1) {
            let clause = Clause::from_base(cl);
            assert_eq!(map.get(&clause), None);
            assert_eq!(map.get_subsuming(&clause).len(), clause_size + 1);
            assert_eq!(map.get_subsumed(&clause).len(), 0);
        }

        // Remove clauses.
        next = 0;
        for cl in (0..literal_count).combinations(clause_size) {
            let clause = Clause::from_base(cl);
            assert_eq!(map.remove(&clause), next);
            next += 1;
        }

        assert!(map.is_empty());
        assert!(map.0.values.is_empty());
        assert!(map.0.trie.edges.is_empty());
        assert!(map.0.trie.value.is_none());
        assert!(map.0.subsets.edges.is_empty());
        assert!(map.0.subsets.value.is_none());
    }

    #[test]
    fn test_cube() {
        let literal_count: usize = 20;
        let cube_size = 3;
        let mut map: CubeMap<usize, usize> = CubeMap::new();
        let mut next = 0;

        // Add all cubes.
        for cb in (0..literal_count).combinations(cube_size) {
            let cube = Cube::from_base(cb);
            assert!(map.get_subsuming(&cube).is_empty());
            assert!(map.get_subsumed(&cube).is_empty());
            map.insert(cube, next);
            next += 1;
        }

        // Check that they're in the set.
        next = 0;
        for cb in (0..literal_count).combinations(cube_size) {
            let cube = Cube::from_base(cb);
            assert_eq!(map.get(&cube), Some(&next));
            assert_eq!(map.get_subsuming(&cube).len(), 1);
            assert_eq!(map.get_subsumed(&cube).len(), 1);
            next += 1;
        }

        // Check subsumption for sub-clauses
        for cb in (0..literal_count).combinations(cube_size - 1) {
            let cube = Cube::from_base(cb);
            assert_eq!(map.get(&cube), None);
            assert_eq!(
                map.get_subsuming(&cube).len(),
                literal_count - (cube_size - 1)
            );
            assert_eq!(map.get_subsumed(&cube).len(), 0);
        }

        // Check subsumption for super-clauses.
        for cb in (0..literal_count).combinations(cube_size + 1) {
            let cube = Cube::from_base(cb);
            assert_eq!(map.get(&cube), None);
            assert_eq!(map.get_subsuming(&cube).len(), 0);
            assert_eq!(map.get_subsumed(&cube).len(), cube_size + 1);
        }

        // Remove clauses.
        next = 0;
        for cb in (0..literal_count).combinations(cube_size) {
            let cube = Cube::from_base(cb);
            assert_eq!(map.remove(&cube), next);
            next += 1;
        }

        assert!(map.is_empty());
        assert!(map.values.is_empty());
        assert!(map.trie.edges.is_empty());
        assert!(map.trie.value.is_none());
        assert!(map.subsets.edges.is_empty());
        assert!(map.subsets.value.is_none());
    }

    #[test]
    fn test_cnf() {
        let literal_count: usize = 20;
        let clause_size = 2;
        let clause_count = 2;
        let mut map: CnfMap<usize, usize> = CnfMap::new();
        let mut next = 0;

        let clauses = (0..literal_count).combinations(clause_size).collect_vec();

        for cl in clauses.iter().cloned().combinations(clause_count) {
            let cnf = Cnf::from_base(cl);
            assert!(map.get_subsuming(&cnf).is_empty());
            assert!(map.get_subsumed(&cnf).is_empty());
            map.insert(cnf, next);
            next += 1;
        }
    }
}

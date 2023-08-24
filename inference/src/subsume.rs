// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Define the abstract notion of subsumption, and provide efficient data structures
//! for the handling of elements implementing subsumption.

use std::fmt::Debug;
use std::sync::Arc;
use std::{cmp::Ordering, hash::Hash};

use fly::ouritertools::OurItertools;
use fly::term::subst::Substitution;
use itertools::Itertools;

use crate::atoms::{Literal, Literals};
use crate::hashmap::{HashMap, HashSet};
use crate::trie::TrieMap;
use fly::syntax::Term;

pub type Structure = HashSet<Literal>;

pub trait Element: Clone + Eq + Hash + Ord + Send + Sync + Debug {
    type Config;
    type Base;
    type Map<V: Clone + Send + Sync>: SubsumptionMap<Key = Self, Value = V>;

    fn subsumes(&self, other: &Self) -> bool;

    fn bottom() -> Self;

    fn top() -> Self;

    fn satisfied_by(&self, m: &Structure) -> bool;

    fn weaken(&self, cfg: &Self::Config, m: &Structure) -> Vec<Self>;

    fn strengthen(&self, cfg: &Self::Config, m: &Structure) -> Vec<Self>;

    fn to_term(&self, positive: bool) -> Term;

    fn substitute(&self, substitution: &Substitution) -> Self;

    fn ids(&self) -> HashSet<String>;

    fn to_base(&self, positive: bool) -> Self::Base;

    fn from_base(base: Self::Base, positive: bool) -> Self;
}

pub trait SubsumptionMap: Clone + Send + Sync {
    type Key: Element;
    type Value: Clone + Send + Sync;

    fn new() -> Self;

    fn is_empty(&self) -> bool;

    fn len(&self) -> usize;

    fn items(&self) -> Vec<(Self::Key, &Self::Value)>;

    fn insert(&mut self, key: Self::Key, value: Self::Value);

    fn remove(&mut self, key: &Self::Key) -> Self::Value;

    fn get(&self, key: &Self::Key) -> Option<&Self::Value>;

    fn get_mut(&mut self, key: &Self::Key) -> Option<&mut Self::Value>;

    fn get_subsuming(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)>;

    fn get_subsumed(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)>;

    fn get_satisfied_by(&self, m: &Structure) -> Vec<(Self::Key, &Self::Value)>;

    fn get_unsatisfied_by(&self, m: &Structure) -> Vec<(Self::Key, &Self::Value)>;
}

fn rev<T: Clone>(seq: &[T]) -> Vec<T> {
    seq.into_iter().cloned().rev().collect_vec()
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Neg<E: Element>(E);

impl<E: Element> Ord for Neg<E> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0).reverse()
    }
}

impl<E: Element> PartialOrd for Neg<E> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<E: Element> Element for Neg<E> {
    type Config = E::Config;
    type Base = E::Base;
    type Map<V: Clone + Send + Sync> = NegMap<E::Map<V>>;

    fn subsumes(&self, other: &Self) -> bool {
        other.0.subsumes(&self.0)
    }

    fn bottom() -> Self {
        Neg(E::top())
    }

    fn top() -> Self {
        Neg(E::bottom())
    }

    fn satisfied_by(&self, m: &Structure) -> bool {
        !self.0.satisfied_by(m)
    }

    fn weaken(&self, cfg: &Self::Config, m: &Structure) -> Vec<Self> {
        self.0
            .strengthen(cfg, m)
            .into_iter()
            .map(|e| Neg(e))
            .collect_vec()
    }

    fn strengthen(&self, cfg: &Self::Config, m: &Structure) -> Vec<Self> {
        self.0
            .weaken(cfg, m)
            .into_iter()
            .map(|e| Neg(e))
            .collect_vec()
    }

    fn to_term(&self, positive: bool) -> Term {
        self.0.to_term(!positive)
    }

    fn substitute(&self, substitution: &Substitution) -> Self {
        Neg(self.0.substitute(substitution))
    }

    fn ids(&self) -> HashSet<String> {
        self.0.ids()
    }

    fn to_base(&self, positive: bool) -> Self::Base {
        self.0.to_base(!positive)
    }

    fn from_base(base: Self::Base, positive: bool) -> Self {
        Neg(E::from_base(base, !positive))
    }
}

#[derive(Clone)]
pub struct NegMap<M: SubsumptionMap>(M);

impl<M: SubsumptionMap> SubsumptionMap for NegMap<M> {
    type Key = Neg<M::Key>;
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

    fn items(&self) -> Vec<(Self::Key, &Self::Value)> {
        self.0
            .items()
            .into_iter()
            .map(|(k, v)| (Neg(k), v))
            .collect_vec()
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
            .map(|(k, v)| (Neg(k), v))
            .collect_vec()
    }

    fn get_subsumed(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)> {
        self.0
            .get_subsuming(&key.0)
            .into_iter()
            .map(|(k, v)| (Neg(k), v))
            .collect_vec()
    }

    fn get_satisfied_by(&self, m: &Structure) -> Vec<(Self::Key, &Self::Value)> {
        self.0
            .get_unsatisfied_by(m)
            .into_iter()
            .map(|(k, v)| (Neg(k), v))
            .collect_vec()
    }

    fn get_unsatisfied_by(&self, m: &Structure) -> Vec<(Self::Key, &Self::Value)> {
        self.0
            .get_satisfied_by(m)
            .into_iter()
            .map(|(k, v)| (Neg(k), v))
            .collect_vec()
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct And<E: Element>(Vec<E>);

pub type Or<E> = Neg<And<Neg<E>>>;

impl<E: Element> From<Vec<E>> for And<E> {
    fn from(value: Vec<E>) -> Self {
        let mut elements = vec![];
        let top = E::top();
        for new_e in value {
            if new_e != top && !elements.iter().any(|e: &E| e.subsumes(&new_e)) {
                elements.retain(|e: &E| !new_e.subsumes(e));
                elements.push(new_e);
            }
        }
        elements.sort();
        Self(elements)
    }
}

impl<E: Element> PartialOrd for And<E> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<E: Element> Ord for And<E> {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut i = 0;
        loop {
            // A shorter and-sequence is greater.
            match (self.0.len() <= i, other.0.len() <= i) {
                (true, true) => return Ordering::Equal,
                (true, false) => return Ordering::Greater,
                (false, true) => return Ordering::Less,
                (false, false) => (),
            }
            let elem_cmp = self.0[i].cmp(&other.0[i]);
            if !elem_cmp.is_eq() {
                return elem_cmp;
            }

            i += 1;
        }
    }
}

impl<E: Element> Element for And<E> {
    type Config = (usize, E::Config);
    type Base = Vec<E::Base>;
    type Map<V: Clone + Send + Sync> = AndMap<E, V>;

    fn subsumes(&self, other: &Self) -> bool {
        other.0.iter().all(|elem2| {
            for elem1 in &self.0 {
                if elem1 > elem2 {
                    break;
                } else if elem1.subsumes(elem2) {
                    return true;
                }
            }

            false
        })
    }

    fn bottom() -> Self {
        Self(vec![E::bottom()])
    }

    fn top() -> Self {
        Self(vec![])
    }

    fn satisfied_by(&self, m: &Structure) -> bool {
        self.0.iter().all(|e| e.satisfied_by(m))
    }

    fn weaken(&self, cfg: &Self::Config, m: &Structure) -> Vec<Self> {
        if self.satisfied_by(m) {
            vec![self.clone()]
        } else if self.0 == vec![E::bottom()] {
            self.0[0]
                .weaken(&cfg.1, m)
                .into_iter()
                .combinations(cfg.0)
                .map(|elements| elements.into())
                .collect_vec()
        } else {
            self.0
                .iter()
                .map(|element| element.weaken(&cfg.1, m))
                .multi_cartesian_product_fixed()
                .map(|elements| elements.into())
                .collect_vec()
        }
    }

    fn strengthen(&self, cfg: &Self::Config, m: &Structure) -> Vec<Self> {
        if !self.satisfied_by(m) {
            vec![self.clone()]
        } else if self.0.len() < cfg.0 {
            E::top()
                .strengthen(&cfg.1, m)
                .into_iter()
                .map(|new_e| {
                    let mut new_elements = self.0.clone();
                    new_elements.push(new_e);
                    new_elements.into()
                })
                .collect_vec()
        } else {
            self.0
                .iter()
                .enumerate()
                .flat_map(|(i, e)| {
                    e.strengthen(&cfg.1, m).into_iter().map(move |new_e| {
                        let mut new_elements = vec![new_e];
                        new_elements.extend(self.0[..i].iter().cloned());
                        new_elements.extend(self.0[(i + 1)..].iter().cloned());
                        new_elements.into()
                    })
                })
                .collect_vec()
        }
    }

    fn to_term(&self, positive: bool) -> Term {
        if positive {
            Term::and(self.0.iter().map(|e| e.to_term(true)))
        } else {
            Term::or(self.0.iter().map(|e| e.to_term(false)))
        }
    }

    fn substitute(&self, substitution: &Substitution) -> Self {
        self.0
            .iter()
            .map(|e| e.substitute(substitution))
            .collect_vec()
            .into()
    }

    fn ids(&self) -> HashSet<String> {
        self.0.iter().flat_map(|e| e.ids()).collect()
    }

    fn to_base(&self, positive: bool) -> Self::Base {
        self.0.iter().map(|e| e.to_base(positive)).collect()
    }

    fn from_base(base: Self::Base, positive: bool) -> Self {
        base.into_iter()
            .map(|b| E::from_base(b, positive))
            .collect_vec()
            .into()
    }
}

#[derive(Clone)]
pub struct AndMap<E: Element, V: Clone> {
    keys: HashMap<usize, Vec<E>>,
    values: HashMap<usize, V>,
    trie: TrieMap<E, usize>,
    subsets: TrieMap<E, HashSet<usize>>,
    next: usize,
}

impl<E: Element, V: Clone + Send + Sync> AndMap<E, V> {
    fn key_value_pairs(
        &self,
        ids: &HashSet<usize>,
    ) -> Vec<(
        <Self as SubsumptionMap>::Key,
        &<Self as SubsumptionMap>::Value,
    )> {
        ids.into_iter()
            .map(|i| (self.keys[i].clone().into(), &self.values[i]))
            .collect_vec()
    }
}

impl<E: Element, V: Clone + Send + Sync> SubsumptionMap for AndMap<E, V> {
    type Key = And<E>;
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

    fn items(&self) -> Vec<(Self::Key, &Self::Value)> {
        self.keys
            .iter()
            .map(|(id, k)| (k.clone().into(), &self.values[id]))
            .collect_vec()
    }

    fn insert(&mut self, key: Self::Key, value: Self::Value) {
        let id = self.next;
        self.next += 1;

        self.trie.insert(&rev(&key.0), id);
        self.subsets.mutate_subsets(&key.0, |v| {
            let mut hs = v.unwrap_or_default();
            hs.insert(id);
            Some(hs)
        });

        self.keys.insert(id, key.0);
        self.values.insert(id, value);
    }

    fn remove(&mut self, key: &Self::Key) -> Self::Value {
        let id = self.trie.remove(&rev(&key.0));

        self.subsets.mutate_subsets(&key.0, |v| {
            let mut hs = v.unwrap();
            assert!(hs.remove(&id));
            if hs.is_empty() {
                None
            } else {
                Some(hs)
            }
        });

        self.keys.remove(&id);
        self.values.remove(&id).unwrap()
    }

    fn get(&self, key: &Self::Key) -> Option<&Self::Value> {
        match self.trie.get(&rev(&key.0)) {
            Some(i) => self.values.get(i),
            None => None,
        }
    }

    fn get_mut(&mut self, key: &Self::Key) -> Option<&mut Self::Value> {
        match self.trie.get(&rev(&key.0)) {
            Some(i) => self.values.get_mut(i),
            None => None,
        }
    }

    fn get_subsuming(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)> {
        self.key_value_pairs(
            &self
                .subsets
                .get_subsuming(&key.0)
                .into_iter()
                .flat_map(|(_, v)| v.iter().cloned())
                .collect(),
        )
    }

    fn get_subsumed(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)> {
        self.key_value_pairs(
            &self
                .trie
                .get_subsumed(&rev(&key.0))
                .into_iter()
                .map(|(_, v)| *v)
                .collect(),
        )
    }

    fn get_satisfied_by(&self, m: &Structure) -> Vec<(Self::Key, &Self::Value)> {
        self.key_value_pairs(
            &self
                .trie
                .get_satisfied_by(m)
                .into_iter()
                .map(|(_, v)| *v)
                .collect(),
        )
    }

    fn get_unsatisfied_by(&self, m: &Structure) -> Vec<(Self::Key, &Self::Value)> {
        self.key_value_pairs(
            &self
                .subsets
                .get_unsatisfied_by(m)
                .into_iter()
                .flat_map(|(_, v)| v.iter().cloned())
                .collect(),
        )
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Pair<E1: Element, E2: Element>(E1, E2);

impl<E1: Element, E2: Element> From<(E1, E2)> for Pair<E1, E2> {
    fn from(value: (E1, E2)) -> Self {
        if value.0 == E1::top() || value.1 == E2::top() {
            return Pair(E1::top(), E2::top());
        }
        Pair(value.0, value.1)
    }
}

impl<E1: Element, E2: Element> PartialOrd for Pair<E1, E2> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<E1: Element, E2: Element> Ord for Pair<E1, E2> {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.0.cmp(&other.0) {
            Ordering::Equal => self.1.cmp(&other.1),
            ord => ord,
        }
    }
}

impl<E1, E2> Element for Pair<E1, E2>
where
    E1: Element,
    E2: Element,
{
    type Config = (E1::Config, E2::Config);
    type Base = (E1::Base, E2::Base);
    type Map<V: Clone + Send + Sync> = PairMap<E1, E2, V>;

    fn subsumes(&self, other: &Self) -> bool {
        self.0.subsumes(&other.0) && self.1.subsumes(&other.1)
    }

    fn satisfied_by(&self, m: &Structure) -> bool {
        self.0.satisfied_by(m) || self.1.satisfied_by(m)
    }

    fn bottom() -> Self {
        Pair(E1::bottom(), E2::bottom())
    }

    fn top() -> Self {
        Pair(E1::top(), E2::top())
    }

    fn weaken(&self, cfg: &Self::Config, m: &Structure) -> Vec<Self> {
        if self.satisfied_by(m) {
            return vec![self.clone()];
        }

        self.0
            .weaken(&cfg.0, m)
            .into_iter()
            .map(|e1| (e1, self.1.clone()).into())
            .chain(
                self.1
                    .weaken(&cfg.1, m)
                    .into_iter()
                    .map(|e2| (self.0.clone(), e2).into()),
            )
            .collect_vec()
    }

    fn strengthen(&self, cfg: &Self::Config, m: &Structure) -> Vec<Self> {
        if !self.satisfied_by(m) {
            return vec![self.clone()];
        }

        let str_0 = self.0.strengthen(&cfg.0, m);
        let str_1 = self.1.strengthen(&cfg.1, m);
        [0..str_0.len(), 0..str_1.len()]
            .into_iter()
            .multi_cartesian_product_fixed()
            .map(|i| (str_0[i[0]].clone(), str_1[i[1]].clone()).into())
            .collect_vec()
    }

    fn to_term(&self, positive: bool) -> Term {
        if self == &Self::top() {
            return Term::true_();
        }

        let mut terms = vec![];
        if self.0 != E1::bottom() {
            terms.push(self.0.to_term(positive));
        }
        if self.1 != E2::bottom() {
            terms.push(self.1.to_term(positive));
        }

        if positive {
            Term::or(terms)
        } else {
            Term::and(terms)
        }
    }

    fn substitute(&self, substitution: &Substitution) -> Self {
        (
            self.0.substitute(substitution),
            self.1.substitute(substitution),
        )
            .into()
    }

    fn ids(&self) -> HashSet<String> {
        let mut ids = self.0.ids();
        ids.extend(self.1.ids());
        ids
    }

    fn to_base(&self, positive: bool) -> Self::Base {
        (self.0.to_base(positive), self.1.to_base(positive))
    }

    fn from_base(base: Self::Base, positive: bool) -> Self {
        (
            E1::from_base(base.0, positive),
            E2::from_base(base.1, positive),
        )
            .into()
    }
}

#[derive(Clone)]
pub struct PairMap<E1: Element, E2: Element, V: Clone + Send + Sync> {
    map: E1::Map<E2::Map<usize>>,
    reverse_map: E2::Map<E1::Map<usize>>,
    values: HashMap<usize, V>,
    next: usize,
}

impl<E1: Element, E2: Element, V: Clone + Send + Sync> SubsumptionMap for PairMap<E1, E2, V> {
    type Key = Pair<E1, E2>;
    type Value = V;

    fn new() -> Self {
        Self {
            map: E1::Map::new(),
            reverse_map: E2::Map::new(),
            values: HashMap::default(),
            next: 0,
        }
    }

    fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    fn len(&self) -> usize {
        self.values.len()
    }

    fn items(&self) -> Vec<(Self::Key, &Self::Value)> {
        self.map
            .items()
            .into_iter()
            .flat_map(|(e1, map)| {
                map.items()
                    .into_iter()
                    .map(move |(e2, i): (_, &usize)| ((e1.clone(), e2).into(), &self.values[i]))
            })
            .collect_vec()
    }

    fn insert(&mut self, key: Self::Key, value: Self::Value) {
        let id = self.next;
        self.next += 1;

        if let Some(map) = self.map.get_mut(&key.0) {
            map.insert(key.1.clone(), id);
        } else {
            let mut map = E2::Map::<usize>::new();
            map.insert(key.1.clone(), id);
            self.map.insert(key.0.clone(), map);
        }

        if let Some(map) = self.reverse_map.get_mut(&key.1) {
            map.insert(key.0, id);
        } else {
            let mut map = E1::Map::<usize>::new();
            map.insert(key.0, id);
            self.reverse_map.insert(key.1, map);
        }

        self.values.insert(id, value);
    }

    fn remove(&mut self, key: &Self::Key) -> Self::Value {
        let map = self.map.get_mut(&key.0).unwrap();
        let id = map.remove(&key.1);
        if map.is_empty() {
            self.map.remove(&key.0);
        }

        let rev_map = self.reverse_map.get_mut(&key.1).unwrap();
        let rev_id = rev_map.remove(&key.0);
        if rev_map.is_empty() {
            self.reverse_map.remove(&key.1);
        }

        assert_eq!(id, rev_id);

        self.values.remove(&id).unwrap()
    }

    fn get(&self, key: &Self::Key) -> Option<&Self::Value> {
        self.values.get(self.map.get(&key.0)?.get(&key.1)?)
    }

    fn get_mut(&mut self, key: &Self::Key) -> Option<&mut Self::Value> {
        self.values.get_mut(self.map.get(&key.0)?.get(&key.1)?)
    }

    fn get_subsuming(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)> {
        self.map
            .get_subsuming(&key.0)
            .into_iter()
            .flat_map(|(e1, map)| {
                map.get_subsuming(&key.1)
                    .into_iter()
                    .map(move |(e2, id): (_, &usize)| ((e1.clone(), e2).into(), &self.values[id]))
            })
            .collect_vec()
    }

    fn get_subsumed(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)> {
        self.map
            .get_subsumed(&key.0)
            .into_iter()
            .flat_map(|(e1, map)| {
                map.get_subsumed(&key.1)
                    .into_iter()
                    .map(move |(e2, id): (_, &usize)| ((e1.clone(), e2).into(), &self.values[id]))
            })
            .collect_vec()
    }

    fn get_satisfied_by(&self, m: &Structure) -> Vec<(Self::Key, &Self::Value)> {
        let satisfied: HashSet<_> = self
            .map
            .get_satisfied_by(m)
            .into_iter()
            .flat_map(|(e1, map)| {
                map.items()
                    .into_iter()
                    .map(move |(e2, id): (_, &usize)| ((e1.clone(), e2), *id))
            })
            .chain(
                self.reverse_map
                    .get_satisfied_by(m)
                    .into_iter()
                    .flat_map(|(e2, map)| {
                        map.items()
                            .into_iter()
                            .map(move |(e1, id): (_, &usize)| ((e1, e2.clone()), *id))
                    }),
            )
            .collect();

        satisfied
            .into_iter()
            .map(|(tup, id)| (tup.into(), &self.values[&id]))
            .collect_vec()
    }

    fn get_unsatisfied_by(&self, m: &Structure) -> Vec<(Self::Key, &Self::Value)> {
        self.map
            .get_unsatisfied_by(m)
            .into_iter()
            .flat_map(|(e1, map)| {
                map.get_unsatisfied_by(m)
                    .into_iter()
                    .map(move |(e2, id): (_, &usize)| ((e1.clone(), e2).into(), &self.values[id]))
            })
            .collect_vec()
    }
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub enum Bounded<E: PartialEq + Eq + PartialOrd + Ord + Hash + Clone> {
    Bottom,
    Element(E),
    Top,
}

impl<E: PartialEq + Eq + PartialOrd + Ord + Hash + Clone> From<E> for Bounded<E> {
    fn from(value: E) -> Self {
        Self::Element(value)
    }
}

impl<E: PartialEq + Eq + PartialOrd + Ord + Hash + Clone> Ord for Bounded<E> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Bounded::Bottom, Bounded::Bottom) | (Bounded::Top, Bounded::Top) => Ordering::Equal,
            (Bounded::Bottom, _) | (_, Bounded::Top) => Ordering::Less,
            (_, Bounded::Bottom) | (Bounded::Top, _) => Ordering::Greater,
            (Bounded::Element(e1), Bounded::Element(e2)) => e1.cmp(e2),
        }
    }
}

impl<E: PartialEq + Eq + PartialOrd + Ord + Hash + Clone> PartialOrd for Bounded<E> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(&other))
    }
}

#[derive(Clone)]
pub struct BoundedLiteralMap<V>(HashMap<Bounded<Literal>, V>)
where
    V: Clone + Send + Sync;

impl<V> SubsumptionMap for BoundedLiteralMap<V>
where
    V: Clone + Send + Sync,
{
    type Key = Bounded<Literal>;
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

    fn items(&self) -> Vec<(Self::Key, &Self::Value)> {
        self.0.iter().map(|(k, v)| (k.clone(), v)).collect_vec()
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
        let mut subsuming = vec![];

        if let Some(v) = self.0.get(key) {
            subsuming.push((key.clone(), v))
        }

        if let Some(v) = self.0.get(&Self::Key::Bottom) {
            subsuming.push((Self::Key::Bottom, v))
        }

        subsuming
    }

    fn get_subsumed(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)> {
        let mut subsumed = vec![];

        if let Some(v) = self.0.get(key) {
            subsumed.push((key.clone(), v))
        }

        if let Some(v) = self.0.get(&Self::Key::Top) {
            subsumed.push((Self::Key::Top, v))
        }

        subsumed
    }

    fn get_satisfied_by(&self, m: &Structure) -> Vec<(Self::Key, &Self::Value)> {
        let mut satisfied = m
            .into_iter()
            .filter_map(|literal| {
                let key = Bounded::Element(literal.clone());
                self.0.get(&key).map(|v| (key, v))
            })
            .collect_vec();

        if let Some(v) = self.0.get(&Self::Key::Top) {
            satisfied.push((Self::Key::Top, v))
        }

        satisfied
    }

    fn get_unsatisfied_by(&self, m: &Structure) -> Vec<(Self::Key, &Self::Value)> {
        let mut unsatisfied = m
            .into_iter()
            .filter_map(|literal| {
                let key = Bounded::Element(literal.negate());
                self.0.get(&key).map(|v| (key, v))
            })
            .collect_vec();

        if let Some(v) = self.0.get(&Self::Key::Bottom) {
            unsatisfied.push((Self::Key::Bottom, v))
        }

        unsatisfied
    }
}

impl Element for Bounded<Literal> {
    type Config = Arc<Literals>;
    type Base = Self;
    type Map<V: Clone + Send + Sync> = BoundedLiteralMap<V>;

    fn subsumes(&self, other: &Self) -> bool {
        match (self, other) {
            (Bounded::Bottom, _) | (_, Bounded::Top) => true,
            (Bounded::Element(lit1), Bounded::Element(lit2)) => lit1 == lit2,
            _ => false,
        }
    }

    fn bottom() -> Self {
        Bounded::Bottom
    }

    fn top() -> Self {
        Bounded::Top
    }

    fn satisfied_by(&self, m: &Structure) -> bool {
        match self {
            Bounded::Bottom => false,
            Bounded::Element(literal) => m.contains(literal),
            Bounded::Top => true,
        }
    }

    fn weaken(&self, cfg: &Self::Config, m: &Structure) -> Vec<Self> {
        if self.satisfied_by(m) {
            return vec![self.clone()];
        }
        if matches!(self, Bounded::Bottom) {
            let weakenings: Vec<Self> = m
                .iter()
                .filter(|lit| cfg.contains(*lit))
                .map(|lit| Bounded::Element(lit.clone()))
                .collect();
            if !weakenings.is_empty() {
                return weakenings;
            }
        }

        vec![Bounded::Top]
    }

    fn strengthen(&self, cfg: &Self::Config, m: &Structure) -> Vec<Self> {
        if !self.satisfied_by(m) {
            return vec![self.clone()];
        }
        if matches!(self, Bounded::Top) {
            let strengthenings: Vec<Self> = m
                .iter()
                .map(|lit| lit.negate())
                .filter(|lit| cfg.contains(lit))
                .map(Bounded::Element)
                .collect();
            if !strengthenings.is_empty() {
                return strengthenings;
            }
        }

        vec![Bounded::Bottom]
    }

    fn to_term(&self, positive: bool) -> Term {
        match &self.to_base(positive) {
            Bounded::Bottom => Term::false_(),
            Bounded::Element(literal) => literal.into(),
            Bounded::Top => Term::true_(),
        }
    }

    fn substitute(&self, substitution: &Substitution) -> Self {
        match self {
            Bounded::Element(literal) => Bounded::Element(literal.substitute(substitution)),
            _ => self.clone(),
        }
    }

    fn ids(&self) -> HashSet<String> {
        match self {
            Bounded::Element(literal) => literal.ids(),
            _ => HashSet::default(),
        }
    }

    fn to_base(&self, positive: bool) -> Self::Base {
        Self::from_base(self.clone(), positive)
    }

    fn from_base(base: Self::Base, positive: bool) -> Self {
        match (base, positive) {
            (Bounded::Bottom, true) | (Bounded::Top, false) => Bounded::Bottom,
            (Bounded::Bottom, false) | (Bounded::Top, true) => Bounded::Top,
            (Bounded::Element(literal), true) => literal.into(),
            (Bounded::Element(literal), false) => literal.negate().into(),
        }
    }
}

pub type Clause = Or<Bounded<Literal>>;
pub type Cube = And<Bounded<Literal>>;
pub type Cnf = And<Clause>;
pub type Dnf = Or<Cube>;
pub type PDnf = Pair<Clause, Dnf>;

#[cfg(test)]
mod tests {
    use crate::atoms::Literal;
    use crate::hashmap::HashSet;
    use fly::syntax::Term;
    use std::sync::Arc;

    use super::{Clause, Cnf, Cube, Element, SubsumptionMap};

    fn lit(name: &str, positive: bool) -> Literal {
        Literal(Term::id(name), positive)
    }

    #[test]
    fn test_clause() {
        let literals = Arc::new(HashSet::from_iter([
            lit("a", true),
            lit("a", false),
            lit("b", true),
            lit("b", false),
            lit("c", true),
            lit("c", false),
        ]));

        let cfg = (2, literals.clone());
        let cl = Clause::bottom();
        let mut map = <Clause as Element>::Map::<()>::new();

        let m110 = HashSet::from_iter([lit("a", true), lit("b", true), lit("c", false)]);
        let m000 = HashSet::from_iter([lit("a", false), lit("b", false), lit("c", false)]);

        let weakenings: HashSet<_> = cl.weaken(&cfg, &m110).into_iter().collect();
        assert_eq!(
            weakenings,
            HashSet::from_iter([
                Clause::from_base(vec![lit("a", true).into(),], true),
                Clause::from_base(vec![lit("b", true).into(),], true),
                Clause::from_base(vec![lit("c", false).into(),], true)
            ])
        );

        for w in weakenings {
            assert!(map.get_subsuming(&w).is_empty());
            assert!(map.get_subsumed(&w).is_empty());
            map.insert(w, ());
        }

        assert_eq!(map.len(), 3);
        assert_eq!(map.get_satisfied_by(&m110).len(), 3);
        assert!(map.get_unsatisfied_by(&m110).is_empty());

        let unsat: HashSet<_> = map
            .get_unsatisfied_by(&m000)
            .into_iter()
            .map(|(c, _)| c)
            .collect();
        for u in &unsat {
            map.remove(u);
        }
        assert_eq!(unsat.len(), 2);
        assert_eq!(map.len(), 1);

        let weakenings: HashSet<_> = unsat
            .into_iter()
            .flat_map(|c| c.weaken(&cfg, &m000))
            .collect();
        assert_eq!(
            weakenings,
            HashSet::from_iter([
                Clause::from_base(vec![lit("a", true).into(), lit("a", false).into()], true),
                Clause::from_base(vec![lit("a", true).into(), lit("b", false).into()], true),
                Clause::from_base(vec![lit("a", true).into(), lit("c", false).into()], true),
                Clause::from_base(vec![lit("b", true).into(), lit("a", false).into()], true),
                Clause::from_base(vec![lit("b", true).into(), lit("b", false).into()], true),
                Clause::from_base(vec![lit("b", true).into(), lit("c", false).into()], true),
            ])
        );

        for w in weakenings {
            if map.get_subsuming(&w).is_empty() {
                assert!(map.get_subsumed(&w).is_empty());
                map.insert(w, ());
            }
        }
        assert_eq!(map.len(), 5);
    }

    #[test]
    fn test_cube() {
        let literals = Arc::new(HashSet::from_iter([
            lit("a", true),
            lit("a", false),
            lit("b", true),
            lit("b", false),
            lit("c", true),
            lit("c", false),
        ]));

        let cfg = (2, literals.clone());
        let cb = Cube::bottom();
        let mut map = <Cube as Element>::Map::<()>::new();

        let m110 = HashSet::from_iter([lit("a", true), lit("b", true), lit("c", false)]);
        let m000 = HashSet::from_iter([lit("a", false), lit("b", false), lit("c", false)]);

        let weakenings: HashSet<_> = cb.weaken(&cfg, &m110).into_iter().collect();
        assert_eq!(
            weakenings,
            HashSet::from_iter([
                Cube::from_base(vec![lit("a", true).into(), lit("b", true).into(),], true),
                Cube::from_base(vec![lit("a", true).into(), lit("c", false).into()], true),
                Cube::from_base(vec![lit("b", true).into(), lit("c", false).into(),], true)
            ])
        );

        for w in weakenings {
            assert!(map.get_subsuming(&w).is_empty());
            assert!(map.get_subsumed(&w).is_empty());
            map.insert(w, ());
        }

        assert_eq!(map.len(), 3);
        assert_eq!(map.get_satisfied_by(&m110).len(), 3);
        assert!(map.get_unsatisfied_by(&m110).is_empty());

        let unsat: HashSet<_> = map
            .get_unsatisfied_by(&m000)
            .into_iter()
            .map(|(c, _)| c)
            .collect();
        for u in &unsat {
            map.remove(u);
        }
        assert_eq!(unsat.len(), 3);
        assert_eq!(map.len(), 0);

        let weakenings: HashSet<_> = unsat
            .into_iter()
            .flat_map(|c| c.weaken(&cfg, &m000))
            .collect();
        assert_eq!(
            weakenings,
            HashSet::from_iter([
                Cube::top(),
                Cube::from_base(vec![lit("c", false).into()], true),
            ])
        );

        for w in weakenings {
            if map.get_subsuming(&w).is_empty() {
                let subsumed: Vec<_> = map.get_subsumed(&w).into_iter().map(|(e, _)| e).collect();
                for e in subsumed {
                    map.remove(&e)
                }
                map.insert(w, ());
            }
        }
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn test_cnf() {
        let literals = Arc::new(HashSet::from_iter([
            lit("a", true),
            lit("a", false),
            lit("b", true),
            lit("b", false),
            lit("c", true),
            lit("c", false),
        ]));

        let cfg = (2, (2, literals.clone()));
        let cnf = Cnf::bottom();
        let mut map = <Cnf as Element>::Map::<()>::new();

        let m110 = HashSet::from_iter([lit("a", true), lit("b", true), lit("c", false)]);
        let m100 = HashSet::from_iter([lit("a", true), lit("b", false), lit("c", false)]);

        let weakenings: HashSet<_> = cnf.weaken(&cfg, &m110).into_iter().collect();
        assert_eq!(
            weakenings,
            HashSet::from_iter([
                Cnf::from_base(
                    vec![vec![lit("a", true).into(),], vec![lit("b", true).into(),],],
                    true
                ),
                Cnf::from_base(
                    vec![vec![lit("a", true).into(),], vec![lit("c", false).into(),],],
                    true
                ),
                Cnf::from_base(
                    vec![vec![lit("b", true).into(),], vec![lit("c", false).into(),],],
                    true
                ),
            ])
        );

        for w in weakenings {
            assert!(map.get_subsuming(&w).is_empty());
            assert!(map.get_subsumed(&w).is_empty());
            map.insert(w, ());
        }

        assert_eq!(map.len(), 3);
        assert_eq!(map.get_satisfied_by(&m110).len(), 3);
        assert!(map.get_unsatisfied_by(&m110).is_empty());

        let unsat: HashSet<_> = map
            .get_unsatisfied_by(&m100)
            .into_iter()
            .map(|(c, _)| c)
            .collect();
        for u in &unsat {
            map.remove(u);
        }
        assert_eq!(unsat.len(), 2);
        assert_eq!(map.len(), 1);

        let weakenings: HashSet<_> = unsat
            .into_iter()
            .flat_map(|c| c.weaken(&cfg, &m100))
            .collect();
        assert_eq!(
            weakenings,
            HashSet::from_iter([
                Cnf::from_base(vec![vec![lit("a", true).into(),],], true),
                Cnf::from_base(vec![vec![lit("c", false).into(),],], true),
                Cnf::from_base(
                    vec![
                        vec![lit("a", true).into(),],
                        vec![lit("b", true).into(), lit("b", false).into(),],
                    ],
                    true
                ),
                Cnf::from_base(
                    vec![
                        vec![lit("a", true).into(),],
                        vec![lit("b", true).into(), lit("c", false).into(),],
                    ],
                    true
                ),
                Cnf::from_base(
                    vec![
                        vec![lit("c", false).into(),],
                        vec![lit("b", true).into(), lit("a", true).into(),],
                    ],
                    true
                ),
                Cnf::from_base(
                    vec![
                        vec![lit("c", false).into(),],
                        vec![lit("b", true).into(), lit("b", false).into(),],
                    ],
                    true
                ),
            ])
        );

        for w in weakenings {
            if map.get_subsuming(&w).is_empty() {
                assert!(map.get_subsumed(&w).is_empty());
                map.insert(w, ());
            }
        }
        assert_eq!(map.len(), 3);
    }

    #[test]
    fn test_clause_map() {
        let mut map = <Clause as Element>::Map::<()>::new();

        let a = Clause::from_base(vec![lit("a", true).into()], true);
        let b = Clause::from_base(vec![lit("b", true).into()], true);
        let ab = Clause::from_base(vec![lit("a", true).into(), lit("b", true).into()], true);

        map.insert(a.clone(), ());

        assert!(map.get(&a).is_some());
        assert!(map.get(&b).is_none());
        assert!(map.get(&ab).is_none());

        assert_eq!(map.get_subsuming(&a).len(), 1);
        assert_eq!(map.get_subsuming(&b).len(), 0);
        assert_eq!(map.get_subsuming(&ab).len(), 1);

        assert_eq!(map.get_subsumed(&a).len(), 1);
        assert_eq!(map.get_subsumed(&b).len(), 0);
        assert_eq!(map.get_subsumed(&ab).len(), 0);

        map.insert(ab.clone(), ());

        assert!(map.get(&a).is_some());
        assert!(map.get(&b).is_none());
        assert!(map.get(&ab).is_some());

        assert_eq!(map.get_subsuming(&a).len(), 1);
        assert_eq!(map.get_subsuming(&b).len(), 0);
        assert_eq!(map.get_subsuming(&ab).len(), 2);

        assert_eq!(map.get_subsumed(&a).len(), 2);
        assert_eq!(map.get_subsumed(&b).len(), 1);
        assert_eq!(map.get_subsumed(&ab).len(), 1);
    }

    #[test]
    fn test_cube_map() {
        let mut map = <Cube as Element>::Map::<()>::new();

        let a = Cube::from_base(vec![lit("a", true).into()], true);
        let b = Cube::from_base(vec![lit("b", true).into()], true);
        let ab = Cube::from_base(vec![lit("a", true).into(), lit("b", true).into()], true);

        map.insert(a.clone(), ());

        assert!(map.get(&a).is_some());
        assert!(map.get(&b).is_none());
        assert!(map.get(&ab).is_none());

        assert_eq!(map.get_subsuming(&a).len(), 1);
        assert_eq!(map.get_subsuming(&b).len(), 0);
        assert_eq!(map.get_subsuming(&ab).len(), 0);

        assert_eq!(map.get_subsumed(&a).len(), 1);
        assert_eq!(map.get_subsumed(&b).len(), 0);
        assert_eq!(map.get_subsumed(&ab).len(), 1);

        map.insert(ab.clone(), ());

        assert!(map.get(&a).is_some());
        assert!(map.get(&b).is_none());
        assert!(map.get(&ab).is_some());

        assert_eq!(map.get_subsuming(&a).len(), 2);
        assert_eq!(map.get_subsuming(&b).len(), 1);
        assert_eq!(map.get_subsuming(&ab).len(), 1);

        assert_eq!(map.get_subsumed(&a).len(), 1);
        assert_eq!(map.get_subsumed(&b).len(), 0);
        assert_eq!(map.get_subsumed(&ab).len(), 2);
    }

    #[test]
    fn test_cnf_map() {
        let mut map = <Cnf as Element>::Map::<()>::new();

        let a_b = Cnf::from_base(
            vec![vec![lit("a", true).into()], vec![lit("b", true).into()]],
            true,
        );
        let ac_b = Cnf::from_base(
            vec![
                vec![lit("a", true).into(), lit("c", true).into()],
                vec![lit("b", true).into()],
            ],
            true,
        );

        assert!(a_b < ac_b);

        map.insert(a_b.clone(), ());

        assert!(map.get(&a_b).is_some());
        assert!(map.get(&ac_b).is_none());

        assert_eq!(map.get_subsuming(&a_b).len(), 1);
        assert_eq!(map.get_subsuming(&ac_b).len(), 1);

        assert_eq!(map.get_subsumed(&a_b).len(), 1);
        assert_eq!(map.get_subsumed(&ac_b).len(), 0);

        map.remove(&a_b);
        assert!(map.is_empty());
        map.insert(ac_b.clone(), ());
        assert!(!map.is_empty());
        assert_eq!(map.len(), 1);

        assert!(map.get(&a_b).is_none());
        assert!(map.get(&ac_b).is_some());

        assert_eq!(map.get_subsuming(&a_b).len(), 0);
        assert_eq!(map.get_subsuming(&ac_b).len(), 1);

        assert_eq!(map.get_subsumed(&a_b).len(), 1);
        assert_eq!(map.get_subsumed(&ac_b).len(), 1);
    }
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Trie-based data structures for efficient handling of ordered sequences

use itertools::Itertools;

use crate::qalpha::subsume::{Element, Structure, SubsumptionMap};

pub struct TrieMap<E: Element, V: Clone + Send + Sync> {
    value: Option<V>,
    edges: Box<E::Map<Self>>,
}

impl<E: Element, V: Clone + Send + Sync> Clone for TrieMap<E, V> {
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            edges: self.edges.clone(),
        }
    }
}

impl<E: Element, V: Clone + Send + Sync> TrieMap<E, V> {
    pub fn new() -> Self {
        Self {
            value: None,
            edges: Box::new(E::Map::new()),
        }
    }

    pub fn insert(&mut self, key: &[E], value: V) {
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

    pub fn mutate<F, R>(&mut self, key: &[E], f: F) -> R
    where
        F: Fn(V) -> (Option<V>, R),
    {
        if key.is_empty() {
            let (val, res) = f(self.value.take().unwrap());
            self.value = val;
            res
        } else {
            let (elem, rest) = key.split_first().unwrap();

            let trie = self.edges.get_mut(elem).unwrap();
            let res = trie.mutate(rest, f);

            if trie.value.is_none() && trie.edges.is_empty() {
                self.edges.remove(elem);
            }

            res
        }
    }

    pub fn remove(&mut self, key: &[E]) -> V {
        self.mutate(key, |v| (None, v))
    }

    pub fn get(&self, key: &[E]) -> Option<&V> {
        if key.is_empty() {
            return self.value.as_ref();
        }

        let (elem, rest) = key.split_first().unwrap();

        match self.edges.get(elem) {
            Some(trie) => trie.get(rest),
            None => None,
        }
    }

    pub fn mutate_subsets<F>(&mut self, key: &[E], f: F)
    where
        F: Fn(Option<V>) -> Option<V>,
    {
        for subset in key.iter().cloned().powerset() {
            if self.get(&subset).is_none() {
                let v = f(None);
                if let Some(value) = v {
                    self.insert(&subset, value);
                }
            } else {
                self.mutate(&subset, |value| (f(Some(value)), ()));
            }
        }
    }

    // elements in ascending order
    pub fn get_subsuming(&self, key: &[E]) -> Vec<(Vec<E>, &V)> {
        if key.is_empty() {
            self.value.iter().map(|v| (vec![], v)).collect()
        } else {
            let first = key.first().unwrap();
            key.iter()
                .flat_map(|k| self.edges.get_subsuming(k))
                .filter(|(e, _)| e <= first)
                .flat_map(|(e, trie)| {
                    let new_key = key.iter().filter(|k| !e.subsumes(k)).cloned().collect_vec();
                    let mut subsuming = trie.get_subsuming(&new_key);
                    for (k, _) in &mut subsuming {
                        k.insert(0, e.clone());
                    }

                    subsuming
                })
                .collect()
        }
    }

    // elements in decending order
    pub fn get_subsumed(&self, key: &[E]) -> Vec<(Vec<E>, &V)> {
        let mut subsumed: Vec<_> = self.value.iter().map(|v| (vec![], v)).collect();
        subsumed.extend(
            key.iter()
                .flat_map(|k| self.edges.get_subsumed(k))
                .flat_map(|(e, trie)| {
                    let fst_idx = key.iter().position(|k| k < &e).unwrap_or(key.len());
                    let mut local_subsumed = trie.get_subsumed(&key[fst_idx..]);
                    for (k, _) in &mut local_subsumed {
                        k.insert(0, e.clone());
                    }

                    local_subsumed
                }),
        );

        subsumed
    }

    // paths where all elements are satisfied
    pub fn get_satisfied_by(&self, m: &Structure) -> Vec<(Vec<E>, &V)> {
        let mut satisfied: Vec<_> = self.value.iter().map(|v| (vec![], v)).collect();
        satisfied.extend(
            self.edges
                .get_satisfied_by(m)
                .into_iter()
                .flat_map(|(e, v)| {
                    let mut local_satisfied = v.get_satisfied_by(m);
                    for (k, _) in &mut local_satisfied {
                        k.insert(0, e.clone());
                    }
                    local_satisfied
                }),
        );

        satisfied
    }

    // paths of length 1 where the first element is not satisfied
    pub fn get_unsatisfied_by(&self, m: &Structure) -> Vec<(Vec<E>, &V)> {
        self.edges
            .get_unsatisfied_by(m)
            .into_iter()
            .filter_map(|(e, trie)| trie.value.as_ref().map(|v| (vec![e], v)))
            .collect()
    }
}

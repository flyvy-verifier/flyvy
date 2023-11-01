// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A straightforward implementation of subsumption maps which serves as a baseline to the one
//! implemented in `subsume.rs`.

use crate::qalpha::subsume::*;
use fly::term::subst::Substitution;
use std::collections::HashMap;

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Baseline<E: Element>(pub E);
#[derive(Clone)]
pub struct BaselineMap<E: Element, V: Clone>(HashMap<Baseline<E>, V>);

impl<E: Element> Element for Baseline<E> {
    type Config = E::Config;
    type Base = E::Base;
    type Map<V: Clone + Send + Sync> = BaselineMap<E, V>;

    fn subsumes(&self, other: &Self) -> bool {
        self.0.subsumes(&other.0)
    }

    fn bottom() -> Self {
        Self(E::bottom())
    }

    fn top() -> Self {
        Self(E::top())
    }

    fn satisfied_by(&self, m: &Structure) -> bool {
        self.0.satisfied_by(m)
    }

    fn weaken(&self, cfg: &Self::Config, m: &Structure) -> Vec<Self> {
        self.0.weaken(cfg, m).into_iter().map(Self).collect()
    }

    fn strengthen(&self, cfg: &Self::Config, m: &Structure) -> Vec<Self> {
        self.0.strengthen(cfg, m).into_iter().map(Self).collect()
    }

    fn to_term(&self, positive: bool) -> fly::syntax::Term {
        self.0.to_term(positive)
    }

    fn substitute(&self, substitution: &Substitution) -> Self {
        Self(self.0.substitute(substitution))
    }

    fn ids(&self) -> crate::hashmap::HashSet<String> {
        self.0.ids()
    }

    fn to_base(&self, positive: bool) -> Self::Base {
        self.0.to_base(positive)
    }

    fn from_base(base: Self::Base, positive: bool) -> Self {
        Self(E::from_base(base, positive))
    }

    fn to_cnf(&self) -> Cnf {
        self.0.to_cnf()
    }

    fn to_dnf(&self) -> Dnf {
        self.0.to_dnf()
    }

    fn size(&self) -> usize {
        self.0.size()
    }
}

impl<E: Element, V: Clone + Send + Sync> SubsumptionMap for BaselineMap<E, V> {
    type Key = Baseline<E>;
    type Value = V;

    fn new() -> Self {
        Self(HashMap::new())
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn items(&self) -> Vec<(Self::Key, &Self::Value)> {
        self.0.iter().map(|(k, v)| (k.clone(), v)).collect()
    }

    fn insert(&mut self, key: Self::Key, value: Self::Value) {
        self.0.insert(key, value);
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
            .iter()
            .filter(|(other, _)| other.subsumes(key))
            .map(|(k, v)| (k.clone(), v))
            .collect()
    }

    fn get_subsumed(&self, key: &Self::Key) -> Vec<(Self::Key, &Self::Value)> {
        self.0
            .iter()
            .filter(|(other, _)| key.subsumes(other))
            .map(|(k, v)| (k.clone(), v))
            .collect()
    }

    fn get_satisfied_by(&self, m: &Structure) -> Vec<(Self::Key, &Self::Value)> {
        self.0
            .iter()
            .filter(|(k, _)| k.satisfied_by(m))
            .map(|(k, v)| (k.clone(), v))
            .collect()
    }

    fn get_unsatisfied_by(&self, m: &Structure) -> Vec<(Self::Key, &Self::Value)> {
        self.0
            .iter()
            .filter(|(k, _)| !k.satisfied_by(m))
            .map(|(k, v)| (k.clone(), v))
            .collect()
    }
}

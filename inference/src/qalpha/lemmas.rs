// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Manage sets of quantified lemmas used in inference, and provide foundational algorithms
//! for handling them, e.g. checking subsumption, weakening, etc.

use std::collections::BTreeMap;
use std::fmt::Debug;
use std::iter::empty;
use std::ops::AddAssign;
use std::sync::Arc;
use std::time::Instant;

use crate::{
    hashmap::HashMap,
    qalpha::{fixpoint::ForwardCti, language::BoundedFormula},
};

use itertools::Itertools;
use rayon::prelude::*;

use crate::{
    basics::OrderedTerms,
    qalpha::language::{BoundedLanguage, FormulaId, FormulaSet},
};
use fly::{
    semantics::{Assignment, Model},
    syntax::{Quantifier, Term},
};

macro_rules! timed {
    ($blk:block) => {{
        let start = Instant::now();
        $blk
        start.elapsed()
    }};
}

/// A compound key that uniquely identifies a formula across multiple WeakenLemmaSet instances.
/// Contains the index of the set and the LemmaKey within that set.
#[derive(Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct CompoundKey {
    pub set_idx: usize,
    pub key: LemmaKey,
}

impl CompoundKey {
    pub fn new(set_idx: usize, key: LemmaKey) -> Self {
        CompoundKey { set_idx, key }
    }

    pub fn is_universal(&self) -> bool {
        self.key.is_universal()
    }
}

/// Manages lemmas from a [`BoundedLanguage`] and allows weakening them simultaneously.
pub struct WeakenLemmaSet<L: BoundedLanguage> {
    lang: Arc<L>,
    set: L::Set,
    sorted: BTreeMap<LemmaKey, Term>,
    rev_sorted: HashMap<Term, (LemmaKey, FormulaId)>,
    total: FormulaId,
    pub max_size: usize,
}

/// Manages multiple WeakenLemmaSet instances for the same BoundedLanguage type.
/// Provides a unified view with CompoundKeys that track which set each formula belongs to.
pub struct MultiWeakenLemmaSet<L: BoundedLanguage> {
    /// The individual lemma sets
    sets: Vec<WeakenLemmaSet<L>>,
    /// A sorted map of all compound keys to terms across all sets
    pub sorted: BTreeMap<CompoundKey, Term>,
    /// Maximum size across all sets
    pub max_size: usize,
}

pub struct WeakenHypotheses<'a, L: BoundedLanguage> {
    set: &'a WeakenLemmaSet<L>,
    permanent: Vec<(LemmaKey, Term)>,
    before: Option<LemmaKey>,
    try_first: Vec<LemmaKey>,
}

pub struct MultiWeakenHypotheses<'a, L: BoundedLanguage> {
    multi_set: &'a MultiWeakenLemmaSet<L>,
    permanent: Vec<(CompoundKey, Term)>,
    before: Option<CompoundKey>,
    try_first: Vec<CompoundKey>,
}

impl<'a, L: BoundedLanguage> OrderedTerms for &WeakenHypotheses<'a, L> {
    type Key = LemmaKey;

    fn permanent(&self) -> Vec<(&Self::Key, &Term)> {
        self.permanent.iter().map(|(k, t)| (k, t)).collect()
    }

    fn first_unsat(self, model: &Model) -> Option<(Self::Key, Term)> {
        self.try_first
            .iter()
            .map(|k| (k, &self.set.sorted[k]))
            .find(|(_, t)| model.eval(t) == 0)
            .or_else(|| {
                let is_after = |k| self.before.as_ref().is_some_and(|b| k >= b);
                self.set
                    .sorted
                    .iter()
                    .find(|(key, term)| is_after(*key) || model.eval(term) == 0)
                    .filter(|(key, _)| !is_after(*key))
            })
            .map(|(key, term)| (*key, term.clone()))
    }

    fn all_terms(self) -> BTreeMap<Self::Key, Term> {
        if let Some(before) = self.before {
            self.set
                .sorted
                .range(..before)
                .map(|(key, term)| (*key, term.clone()))
                .collect()
        } else {
            self.set.sorted.clone()
        }
    }
}

impl<'a, L: BoundedLanguage> OrderedTerms for &MultiWeakenHypotheses<'a, L> {
    type Key = CompoundKey;

    fn permanent(&self) -> Vec<(&Self::Key, &Term)> {
        self.permanent.iter().map(|(k, t)| (k, t)).collect()
    }

    fn first_unsat(self, model: &Model) -> Option<(Self::Key, Term)> {
        // First check try_first formulas
        for compound_key in &self.try_first {
            let term = &self.multi_set.sorted[compound_key];
            if model.eval(term) == 0 {
                return Some((*compound_key, term.clone()));
            }
        }

        // Then check formulas in order, respecting the `before` boundary
        // CompoundKey ordering naturally respects set indices first, then LemmaKey within each set
        let is_after = |k: &CompoundKey| self.before.as_ref().is_some_and(|b| k >= b);

        self.multi_set
            .sorted
            .iter()
            .find(|(key, term)| is_after(key) || model.eval(term) == 0)
            .filter(|(key, _)| !is_after(key))
            .map(|(key, term)| (*key, term.clone()))
    }

    fn all_terms(self) -> BTreeMap<Self::Key, Term> {
        if let Some(before) = self.before {
            // Use range to get all terms before the `before` key
            // CompoundKey's Ord implementation ensures proper ordering across sets
            self.multi_set
                .sorted
                .range(..before)
                .map(|(key, term)| (*key, term.clone()))
                .collect()
        } else {
            self.multi_set.sorted.clone()
        }
    }
}

impl<L: BoundedLanguage> WeakenLemmaSet<L> {
    pub fn new(lang: Arc<L>) -> Self {
        Self {
            lang,
            set: L::Set::default(),
            sorted: BTreeMap::new(),
            rev_sorted: HashMap::default(),
            total: 0,
            max_size: 0,
        }
    }

    pub fn simplified_len(&self) -> usize {
        self.sorted.len()
    }

    pub fn len(&self) -> usize {
        self.set.len()
    }

    pub fn hypotheses(
        &self,
        permanent: Vec<LemmaKey>,
        before: Option<LemmaKey>,
        try_first: Vec<LemmaKey>,
    ) -> WeakenHypotheses<'_, L> {
        WeakenHypotheses {
            set: self,
            permanent: permanent
                .into_iter()
                .map(|k| (k, self.sorted[&k].clone()))
                .collect(),
            before,
            try_first,
        }
    }

    pub fn init(&mut self) {
        self.insert(self.lang.bottom());
        self.max_size = self.max_size.max(self.len());
    }

    fn insert(&mut self, f: L::Formula) -> Vec<LemmaKey> {
        let simplified = self.lang.simplify(&f);
        self.set.insert(f);

        simplified
            .into_iter()
            .filter_map(|term| {
                if let Some((_, count)) = self.rev_sorted.get_mut(&term) {
                    *count += 1;
                    None
                } else {
                    let key = LemmaKey::key(&term, self.total);
                    self.total += 1;
                    assert!(self.sorted.insert(key, term.clone()).is_none());
                    assert!(self.rev_sorted.insert(term, (key, 1)).is_none());
                    Some(key)
                }
            })
            .collect()
    }

    fn remove(&mut self, f: &L::Formula) -> Vec<LemmaKey> {
        self.lang
            .simplify(f)
            .iter()
            .filter_map(|term| {
                let (_, count) = self.rev_sorted.get_mut(term).unwrap();
                assert!(*count > 0);
                *count -= 1;
                if *count == 0 {
                    let (key, _) = self.rev_sorted.remove(term).unwrap();
                    assert!(self.sorted.remove(&key).is_some());
                    Some(key)
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn unsat_cti(&self, cti: &ForwardCti) -> bool {
        let empty_asgn = Assignment::new();
        let unsat = self.set.get_unsat(&cti.post, &empty_asgn);
        match &cti.pre {
            Some(model) => unsat
                .iter()
                .any(|id| self.set.get_f(id).unwrap().eval(model, &empty_asgn)),
            None => !unsat.is_empty(),
        }
    }

    pub fn unsat(&self, model: &Model) -> bool {
        !self.set.get_unsat(model, &Assignment::new()).is_empty()
    }

    pub fn weaken(&mut self, cti: &ForwardCti) -> (Vec<LemmaKey>, Vec<LemmaKey>) {
        let start_time = Instant::now();
        let empty_assigment = Assignment::new();

        let unsat;
        let mut removed: Vec<LemmaKey> = vec![];
        let mut added: Vec<LemmaKey> = vec![];
        let mut total_added = 0_usize;

        let unsat_time = timed!({
            unsat = self.set.remove_unsat_cti(cti);
        });
        for f in &unsat {
            removed.append(&mut self.remove(f));
        }

        let ignore = |f: &L::Formula| !self.set.get_subsuming(f).is_empty();

        let mut weakenings: Vec<_>;
        let weaken_time = timed!({
            weakenings = unsat
                .par_iter()
                .flat_map_iter(|f| self.lang.weaken(f, &cti.post, &empty_assigment, ignore))
                .collect::<Vec<_>>();
        });

        let minimization_time = timed!({ weakenings = L::minimize(empty(), weakenings) });

        let insertion_time = timed!({
            for f in weakenings.into_iter().sorted() {
                total_added += 1;
                added.append(&mut self.insert(f));
            }
        });

        self.max_size = self.max_size.max(self.len());

        if !unsat.is_empty() {
            log::info!(
                "[{} ~> {} | {}] Weakened: removed={}({}), added={}({}), total_time={}ms (unsat={}ms, weaken={}ms, min={}ms, insertion={}ms)",
                self.len(),
                self.simplified_len(),
                self.max_size,
                unsat.len(),
                removed.len(),
                total_added,
                added.len(),
                start_time.elapsed().as_millis(),
                unsat_time.as_millis(),
                weaken_time.as_millis(),
                minimization_time.as_millis(),
                insertion_time.as_millis(),
            );
        }

        (removed, added)
    }

    pub fn remove_unsat(&mut self, cti: &ForwardCti) -> Vec<LemmaKey> {
        let start_time = Instant::now();

        let unsat = self.set.remove_unsat_cti(cti);
        let mut removed: Vec<LemmaKey> = vec![];

        for f in &unsat {
            removed.append(&mut self.remove(f));
        }

        if !removed.is_empty() {
            log::info!(
                "[{}] Removed UNSAT: removed={}, total_time={}ms",
                self.len(),
                unsat.len(),
                start_time.elapsed().as_millis(),
            );
        }

        removed
    }

    pub fn key_to_idx(&self) -> HashMap<LemmaKey, usize> {
        self.sorted
            .keys()
            .cloned()
            .enumerate()
            .map(|(i, k)| (k, i))
            .collect()
    }

    pub fn keys(&self) -> impl Iterator<Item = &LemmaKey> {
        self.sorted.keys()
    }

    pub fn to_terms_keys(&self) -> impl Iterator<Item = (&Term, &LemmaKey)> {
        self.rev_sorted.iter().map(|(t, (k, _))| (t, k))
    }

    pub fn to_terms(&self) -> Vec<Term> {
        self.sorted.values().cloned().collect()
    }

    pub fn key_to_term(&self, key: &LemmaKey) -> Term {
        self.sorted[key].clone()
    }
}

impl<L: BoundedLanguage> MultiWeakenLemmaSet<L> {
    pub fn new(langs: Vec<Arc<L>>) -> Self {
        let sets: Vec<WeakenLemmaSet<L>> = langs
            .into_iter()
            .map(|lang| WeakenLemmaSet::new(lang))
            .collect();

        Self {
            sets,
            sorted: BTreeMap::new(),
            max_size: 0,
        }
    }

    pub fn simplified_len(&self) -> usize {
        self.sorted.len()
    }

    pub fn len(&self) -> usize {
        self.sets.iter().map(|set| set.len()).sum()
    }

    pub fn to_terms(&self) -> Vec<Term> {
        self.sorted.values().cloned().collect()
    }

    pub fn to_terms_keys(&self) -> impl Iterator<Item = (&Term, &CompoundKey)> + '_ {
        self.sorted.iter().map(|(k, t)| (t, k))
    }

    pub fn keys(&self) -> impl Iterator<Item = &CompoundKey> {
        self.sorted.keys()
    }

    pub fn key_to_idx(&self) -> HashMap<CompoundKey, usize> {
        self.sorted
            .keys()
            .cloned()
            .enumerate()
            .map(|(i, k)| (k, i))
            .collect()
    }

    pub fn key_to_term(&self, key: &CompoundKey) -> Term {
        self.sorted[key].clone()
    }

    pub fn init(&mut self) {
        for (set_idx, set) in self.sets.iter_mut().enumerate() {
            set.init();
            // Populate sorted with compound keys
            for (key, term) in &set.sorted {
                self.sorted
                    .insert(CompoundKey::new(set_idx, *key), term.clone());
            }
        }
        // max_size is the sum of all sets' lengths
        let total_len = self.len();
        self.max_size = self.max_size.max(total_len);
    }

    pub fn hypotheses(
        &self,
        permanent: Vec<CompoundKey>,
        before: Option<CompoundKey>,
        try_first: Vec<CompoundKey>,
    ) -> MultiWeakenHypotheses<'_, L> {
        MultiWeakenHypotheses {
            multi_set: self,
            permanent: permanent
                .into_iter()
                .map(|k| (k, self.sorted[&k].clone()))
                .collect(),
            before,
            try_first,
        }
    }

    pub fn weaken(&mut self, cti: &ForwardCti) -> (Vec<CompoundKey>, Vec<CompoundKey>) {
        // Weaken each set in parallel and collect results
        let results: Vec<(usize, Vec<LemmaKey>, Vec<LemmaKey>)> = self
            .sets
            .par_iter_mut()
            .enumerate()
            .map(|(set_idx, set)| {
                let (removed, added) = set.weaken(cti);
                (set_idx, removed, added)
            })
            .collect();

        let mut all_removed = Vec::new();
        let mut all_added = Vec::new();

        // Process results sequentially to update the sorted map
        for (set_idx, removed, added) in results {
            // Remove compound keys from sorted map
            for key in &removed {
                let compound_key = CompoundKey::new(set_idx, *key);
                self.sorted.remove(&compound_key);
                all_removed.push(compound_key);
            }

            // Add compound keys to sorted map
            for key in &added {
                let compound_key = CompoundKey::new(set_idx, *key);
                let term = self.sets[set_idx].sorted[key].clone();
                self.sorted.insert(compound_key, term);
                all_added.push(compound_key);
            }
        }

        // Update max_size with the current total length
        let total_len = self.len();
        self.max_size = self.max_size.max(total_len);

        (all_removed, all_added)
    }

    pub fn remove_unsat(&mut self, cti: &ForwardCti) -> Vec<CompoundKey> {
        // Remove unsat from each set in parallel
        let results: Vec<(usize, Vec<LemmaKey>)> = self
            .sets
            .par_iter_mut()
            .enumerate()
            .map(|(set_idx, set)| {
                let removed = set.remove_unsat(cti);
                (set_idx, removed)
            })
            .collect();

        let mut all_removed = Vec::new();

        // Process results sequentially to update the sorted map
        for (set_idx, removed) in results {
            // Remove compound keys from sorted map
            for key in &removed {
                let compound_key = CompoundKey::new(set_idx, *key);
                self.sorted.remove(&compound_key);
                all_removed.push(compound_key);
            }
        }

        all_removed
    }

    pub fn unsat(&self, model: &Model) -> bool {
        // Return true if any set has an unsat formula
        self.sets.iter().any(|set| set.unsat(model))
    }
}

/// Lemma complexity consists of
/// - the number of existentials,
/// - the number of literals,
/// - the number of quantified variables
#[derive(Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct LemmaComplexity(usize, usize, usize);

#[derive(Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct LemmaKey(LemmaComplexity, FormulaId);

impl LemmaKey {
    fn key(term: &Term, id: FormulaId) -> Self {
        LemmaKey(LemmaComplexity::complexity(term), id)
    }

    pub fn is_universal(&self) -> bool {
        self.0 .0 == 0
    }
}

impl AddAssign for LemmaComplexity {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
        self.1 += rhs.1;
        self.2 += rhs.2;
    }
}

impl LemmaComplexity {
    /// Return the complexity of this lemma, assuming it contains only quantifiers and boolean connectives, and is in NNF.
    fn complexity(term: &Term) -> Self {
        let mut comp = LemmaComplexity(0, 0, 0);
        match term {
            Term::Quantified {
                quantifier,
                binders: _,
                body,
            } => {
                comp += LemmaComplexity::complexity(body);
                if matches!(quantifier, Quantifier::Exists) {
                    comp.0 += 1
                }
                comp.2 += 1;
            }
            Term::NAryOp(_, args) => {
                for a in args {
                    comp += LemmaComplexity::complexity(a);
                }
            }
            _ => comp.1 += 1,
        }

        comp
    }
}

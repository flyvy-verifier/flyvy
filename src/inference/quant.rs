// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Manage quantifiers used in inference.

use crate::inference::hashmap::HashSet;
use itertools::Itertools;
use std::fmt::Debug;
use std::sync::Arc;

use crate::{
    fly::syntax::{Binder, Quantifier, Signature, Sort, Term},
    inference::InferenceConfig,
    term::subst::Substitution,
};

pub fn count_exists(qs: &[Quantifier]) -> usize {
    qs.iter().filter(|q| **q == Quantifier::Exists).count()
}

/// Generate the variable names for this [`QuantifierSequence`]. The names are grouped
/// and ordered based on their position in the sequence.
pub fn vars(signature: &Signature, sorts: &[usize], counts: &[usize]) -> Vec<Vec<String>> {
    let mut vars = vec![vec![]; sorts.len()];
    let mut sorted_counts: Vec<usize> = vec![0; signature.sorts.len()];
    for i in 0..sorts.len() {
        vars[i].extend((0..counts[i]).map(|_| {
            sorted_counts[sorts[i]] += 1;
            format!("{}_{}", signature.sorts[sorts[i]], sorted_counts[sorts[i]])
        }));
    }

    vars
}

fn distribute(amount: usize, boxes: &[usize]) -> Vec<Vec<usize>> {
    assert!(!boxes.is_empty());
    if boxes.len() == 1 {
        if amount <= boxes[0] {
            vec![vec![amount]]
        } else {
            vec![]
        }
    } else {
        (0..=amount.min(boxes[0]))
            .flat_map(|c| {
                distribute(amount - c, &boxes[1..])
                    .into_iter()
                    .map(|mut v| {
                        v.insert(0, c);
                        v
                    })
                    .collect_vec()
            })
            .collect_vec()
    }
}

/// A [`QuantifierSequence`] is a sequence where each position represents a sorted
/// quantifier with a certain number of quantified variables.
/// Note that this is a generic structure with a generic quantifier.
#[derive(Clone, PartialEq, Eq)]
pub struct QuantifierSequence<Q: Clone> {
    pub signature: Arc<Signature>,
    pub quantifiers: Vec<Q>,
    pub sorts: Vec<usize>,
    pub names: Vec<Vec<String>>,
}

/// A [`QuantifierSequence`] where each quantifier is either [`None`], [`Some(Quantifier::Forall)`],
/// or [`Some(Quantifier::Exists)`], where [`None`] represents a wildcard configuration which allows
/// both classical quantifiers.
pub type QuantifierConfig = QuantifierSequence<Option<Quantifier>>;
/// A [`QuantifierSequence`] where each quantifier is either [`Quantifier::Forall`] or [`Quantifier::Exists`],
/// i.e. a classical quantifier prefix.
pub type QuantifierPrefix = QuantifierSequence<Quantifier>;

impl<Q: Clone> QuantifierSequence<Q> {
    pub fn new(
        signature: Arc<Signature>,
        quantifiers: Vec<Q>,
        sorts: Vec<usize>,
        counts: &[usize],
    ) -> Self {
        let names = vars(&signature, &sorts, counts);

        QuantifierSequence {
            signature,
            quantifiers,
            sorts,
            names,
        }
    }

    /// Get the length of the [`QuantifierSequence`].
    pub fn len(&self) -> usize {
        self.quantifiers.len()
    }

    pub fn num_vars(&self) -> usize {
        self.names.iter().map(|n| n.len()).sum()
    }

    pub fn all_vars(&self) -> HashSet<String> {
        self.names.iter().flat_map(|n| n.iter().cloned()).collect()
    }

    /// Generate all atoms in a given signature with this [`QuantifierSequence`].
    pub fn atoms(&self, nesting: Option<usize>, include_eq: bool) -> Vec<Term> {
        let mut sorted_vars = vec![vec![]; self.signature.sorts.len()];
        for (i, mut v) in self.names.iter().cloned().enumerate() {
            sorted_vars[self.sorts[i]].append(&mut v);
        }

        self.signature
            .terms_by_sort(&sorted_vars, nesting, include_eq)
            .pop()
            .unwrap()
    }

    /// Generate all permutations of grouped variables in the [`QuantifierSequence`],
    /// starting at position `start_at`. Include only the variables in `only` in the
    /// resulting permutations.
    pub fn permutations(
        &self,
        start_at: usize,
        only: Option<&HashSet<String>>,
    ) -> Vec<Substitution> {
        if start_at >= self.len() {
            return vec![Substitution::new()];
        }

        let vars = &self.names[start_at..];
        let only_vars = if let Some(only_set) = only {
            vars.iter()
                .map(|vs| {
                    vs.iter()
                        .filter(|&v| only_set.contains(v))
                        .cloned()
                        .collect_vec()
                })
                .collect_vec()
        } else {
            Vec::from(vars)
        };
        vars.iter()
            .enumerate()
            .map(|(i, vs)| vs.iter().permutations(only_vars[i].len()))
            .multi_cartesian_product()
            .map(|perm| {
                only_vars
                    .iter()
                    .flatten()
                    .cloned()
                    .zip(perm.into_iter().flatten().map(|s| Term::Id(s.clone())))
                    .collect()
            })
            .collect_vec()
    }
}

impl QuantifierConfig {
    pub fn all_prefixes(&self, infer_cfg: &InferenceConfig) -> Vec<QuantifierPrefix> {
        let mut res = vec![];

        for e in 0..=infer_cfg.max_existentials.unwrap_or(self.len()) {
            for s in 0..=infer_cfg.max_size.unwrap_or(self.num_vars()) {
                res.append(&mut self.exact_prefixes(e, e, s));
            }
        }

        res
    }

    pub fn exact_prefixes(
        &self,
        min_existentials: usize,
        max_existentials: usize,
        size: usize,
    ) -> Vec<QuantifierPrefix> {
        if self.len() == 0 {
            return vec![QuantifierPrefix {
                signature: self.signature.clone(),
                quantifiers: vec![],
                sorts: vec![],
                names: vec![],
            }];
        }

        let counts = self.names.iter().map(|n| n.len()).collect_vec();
        let sum = counts.iter().sum();

        distribute(size.min(sum), &counts)
            .iter()
            .flat_map(|dist| {
                self.quantifiers
                    .iter()
                    .enumerate()
                    .map(|(i, q)| match q {
                        None => {
                            if dist[i] != 0 {
                                vec![Quantifier::Forall, Quantifier::Exists]
                            } else {
                                vec![Quantifier::Forall]
                            }
                        }
                        Some(q) => vec![*q],
                    })
                    .multi_cartesian_product()
                    .filter(|qs| {
                        let e = count_exists(qs);
                        e >= min_existentials && e <= max_existentials
                    })
                    .map(|quantifiers| QuantifierPrefix {
                        signature: self.signature.clone(),
                        quantifiers,
                        sorts: self.sorts.clone(),
                        names: self
                            .names
                            .iter()
                            .enumerate()
                            .map(|(i, n)| n[..dist[i]].to_vec())
                            .collect_vec(),
                    })
            })
            .collect_vec()
    }

    pub fn non_universal_vars(&self) -> HashSet<String> {
        match (0..self.len()).find(|i| !matches!(self.quantifiers[*i], Some(Quantifier::Forall))) {
            Some(first_exists) => self.names[first_exists..]
                .iter()
                .flat_map(|ns| ns.iter().cloned())
                .collect(),
            None => HashSet::default(),
        }
    }
}

impl Debug for QuantifierConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts = vec![];
        for i in 0..self.len() {
            if !self.names[i].is_empty() {
                let q_vec = vec![
                    match self.quantifiers[i] {
                        None => "******".to_string(),
                        Some(Quantifier::Exists) => "exists".to_string(),
                        Some(Quantifier::Forall) => "forall".to_string(),
                    },
                    self.names[i].iter().join(", "),
                ];

                parts.push(q_vec.into_iter().join(" "));
            }
        }

        write!(f, "{}", parts.iter().join(" . "))
    }
}

impl QuantifierPrefix {
    /// Quantify the given term according to this [`QuantifierPrefix`].
    pub fn quantify(&self, mut term: Term) -> Term {
        let present_ids = term.ids();
        for (i, v) in self.names.iter().enumerate().rev() {
            let binders = v
                .iter()
                .filter_map(|name| {
                    if present_ids.contains(name) {
                        Some(Binder {
                            name: name.clone(),
                            sort: Sort::Id(self.signature.sorts[self.sorts[i]].clone()),
                        })
                    } else {
                        None
                    }
                })
                .collect_vec();

            if !binders.is_empty() {
                term = Term::Quantified {
                    quantifier: self.quantifiers[i],
                    binders,
                    body: Box::new(term),
                }
            }
        }

        term
    }

    /// Check whether one [`QuantifierPrefix`] subsumes another. A prefix Q1 is said to subsume Q2
    /// if Q2 can be gotten from Q1 by only flipping universal quantifiers to existential ones.
    pub fn subsumes(&self, other: &Self) -> bool {
        assert_eq!(self.len(), other.len());
        (0..self.len()).all(|i| {
            self.names[i].is_empty()
                || other.names[i].is_empty()
                || self.quantifiers[i] == Quantifier::Forall
                || other.quantifiers[i] == Quantifier::Exists
        })
    }

    /// Check whether one [`QuantifierPrefix`] contains another.
    pub fn contains(&self, other: &Self) -> bool {
        assert_eq!(self.len(), other.len());
        (0..self.len()).all(|i| {
            self.quantifiers[i] == other.quantifiers[i]
                && self.names[i].len() >= other.names[i].len()
        })
    }

    pub fn existentials(&self) -> usize {
        count_exists(&self.quantifiers)
    }

    pub fn non_universal_vars(&self) -> HashSet<String> {
        match (0..self.len()).find(|i| matches!(self.quantifiers[*i], Quantifier::Exists)) {
            Some(first_exists) => self.names[first_exists..]
                .iter()
                .flat_map(|ns| ns.iter().cloned())
                .collect(),
            None => HashSet::default(),
        }
    }
}

impl Debug for QuantifierPrefix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts = vec![];
        for i in 0..self.len() {
            if !self.names[i].is_empty() {
                let q_vec = vec![
                    match self.quantifiers[i] {
                        Quantifier::Exists => "exists".to_string(),
                        Quantifier::Forall => "forall".to_string(),
                    },
                    self.names[i].iter().join(", "),
                ];

                parts.push(q_vec.into_iter().join(" "));
            }
        }

        write!(f, "{}", parts.iter().join(". "))
    }
}

#[cfg(test)]
mod tests {
    use crate::inference::hashmap::HashSet;

    use super::QuantifierConfig;
    use crate::fly::syntax::Term;
    use crate::{fly::parser, term::subst::Substitution};
    use std::collections::HashMap;
    use std::sync::Arc;

    #[test]
    fn test_permutations() {
        let signature = parser::parse_signature(
            r#"
sort A
sort B
sort C
"#
            .trim(),
        );

        let config = QuantifierConfig::new(
            Arc::new(signature),
            vec![None, None, None],
            vec![0, 1, 2],
            &[2, 1, 2],
        );
        let a = |i: usize| format!("A_{}", i);
        let b = |i: usize| format!("B_{}", i);
        let c = |i: usize| format!("C_{}", i);
        let ta = |i: usize| Term::Id(a(i));
        let tb = |i: usize| Term::Id(b(i));
        let tc = |i: usize| Term::Id(c(i));

        let same = |perms1: &[Substitution], perms2: &[Substitution]| -> bool {
            perms1.iter().all(|p| perms2.contains(p)) && perms2.iter().all(|p| perms1.contains(p))
        };

        assert!(same(
            &config.permutations(0, None),
            &[
                HashMap::from_iter([
                    (a(1), ta(1)),
                    (a(2), ta(2)),
                    (b(1), tb(1)),
                    (c(1), tc(1)),
                    (c(2), tc(2)),
                ]),
                HashMap::from_iter([
                    (a(1), ta(2)),
                    (a(2), ta(1)),
                    (b(1), tb(1)),
                    (c(1), tc(1)),
                    (c(2), tc(2)),
                ]),
                HashMap::from_iter([
                    (a(1), ta(1)),
                    (a(2), ta(2)),
                    (b(1), tb(1)),
                    (c(1), tc(2)),
                    (c(2), tc(1)),
                ]),
                HashMap::from_iter([
                    (a(1), ta(2)),
                    (a(2), ta(1)),
                    (b(1), tb(1)),
                    (c(1), tc(2)),
                    (c(2), tc(1)),
                ])
            ]
        ));

        assert!(same(
            &config.permutations(1, None),
            &[
                HashMap::from_iter([(b(1), tb(1)), (c(1), tc(1)), (c(2), tc(2)),]),
                HashMap::from_iter([(b(1), tb(1)), (c(1), tc(2)), (c(2), tc(1))]),
            ]
        ));

        assert!(same(
            &config.permutations(0, Some(&HashSet::from_iter([a(1), c(2)]))),
            &[
                HashMap::from_iter([(a(1), ta(1)), (c(2), tc(1)),]),
                HashMap::from_iter([(a(1), ta(2)), (c(2), tc(1)),]),
                HashMap::from_iter([(a(1), ta(1)), (c(2), tc(2)),]),
                HashMap::from_iter([(a(1), ta(2)), (c(2), tc(2)),]),
            ]
        ));
    }
}

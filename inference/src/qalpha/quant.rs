// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Manage quantifiers used in inference.

use std::{cmp::Ordering, hash::Hash};

use crate::hashmap::HashSet;
use fly::ouritertools::OurItertools;
use itertools::Itertools;
use std::fmt::Debug;
use std::sync::Arc;

use crate::qalpha::frame;
use fly::syntax::{Binder, Quantifier, Signature, Sort, Term};
use fly::term::subst::Substitution;

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

fn push_front<T>(mut v: Vec<T>, t: T) -> Vec<T> {
    v.insert(0, t);
    v
}

/// Returns all possible distributions of `amount` into `boxes` of the specified sizes.
fn distribute(amount: usize, boxes: &[usize]) -> Vec<Vec<usize>> {
    if boxes.is_empty() {
        match amount {
            0 => vec![vec![]],
            _ => vec![],
        }
    } else {
        (0..=amount.min(boxes[0]))
            .flat_map(|c| {
                distribute(amount - c, &boxes[1..])
                    .into_iter()
                    .map(|v| push_front(v, c))
                    .collect_vec()
            })
            .collect_vec()
    }
}

/// Return a vector whose position `i` is `boxes[i][..sizes[i]]`.
fn sub_boxes<T: Clone>(sizes: &[usize], boxes: &[Vec<T>]) -> Vec<Vec<T>> {
    assert_eq!(sizes.len(), boxes.len());
    sizes
        .iter()
        .enumerate()
        .map(|(i, size)| boxes[i][..*size].to_vec())
        .collect()
}

/// Find the first location `i` such that the sum of `boxes[i..]` is less than or equal to `max`.
fn select_last(max: usize, boxes: &[usize]) -> usize {
    (1..=boxes.len())
        .rev()
        .find(|i| boxes[(i - 1)..].iter().sum::<usize>() > max)
        .unwrap_or(0)
}

fn parse_quantifier(sig: &Signature, s: &str) -> Result<(Option<Quantifier>, Sort, usize), String> {
    let mut parts = s.split_whitespace();

    let quantifier = match parts.next().unwrap() {
        "*" => None,
        "F" => Some(Quantifier::Forall),
        "E" => Some(Quantifier::Exists),
        _ => return Err("invalid quantifier (choose F/E/*)".to_string()),
    };

    let sort_id = parts.next().unwrap().to_string();
    let sort = if sig.sorts.contains(&sort_id) {
        Sort::Uninterpreted(sort_id)
    } else {
        return Err(format!("invalid sort {sort_id}"));
    };

    let count = parts.next().unwrap().parse::<usize>().unwrap();
    Ok((quantifier, sort, count))
}

pub fn parse_quantifiers(quant_strings: &[String], sig: &Signature) -> QuantifierConfig {
    let mut quantifiers = vec![];
    let mut sorts = vec![];
    let mut counts = vec![];
    for quantifier_spec in quant_strings {
        match parse_quantifier(sig, quantifier_spec) {
            Ok((q, sort, count)) => {
                quantifiers.push(q);
                sorts.push(sort);
                counts.push(count);
            }
            Err(err) => panic!("{err}"),
        }
    }

    QuantifierConfig::new(Arc::new(sig.clone()), quantifiers, sorts, &counts)
}

/// A [`QuantifierSequence`] is a sequence where each position represents a sorted
/// quantifier with a certain number of quantified variables.
/// Note that this is a generic structure with a generic quantifier.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct QuantifierSequence<Q: Clone + Hash + Eq> {
    pub quantifiers: Vec<Q>,
    pub sorts: Arc<Vec<Sort>>,
    pub names: Arc<Vec<Vec<String>>>,
}

/// A [`QuantifierSequence`] where each quantifier is either [`None`], [`Some(Quantifier::Forall)`],
/// or [`Some(Quantifier::Exists)`], where [`None`] represents a wildcard configuration which allows
/// both classical quantifiers.
pub type QuantifierConfig = QuantifierSequence<Option<Quantifier>>;
/// A [`QuantifierSequence`] where each quantifier is either [`Quantifier::Forall`] or [`Quantifier::Exists`],
/// i.e. a classical quantifier prefix.
pub type QuantifierPrefix = QuantifierSequence<Quantifier>;

impl<Q: Clone + Hash + Eq> QuantifierSequence<Q> {
    pub fn new(
        signature: Arc<Signature>,
        quantifiers: Vec<Q>,
        sorts: Vec<Sort>,
        counts: &[usize],
    ) -> Self {
        let sort_indices: Vec<usize> = sorts.iter().map(|sort| signature.sort_idx(sort)).collect();
        let names = vars(&signature, &sort_indices, counts);

        QuantifierSequence {
            quantifiers,
            sorts: Arc::new(sorts),
            names: Arc::new(names),
        }
    }

    /// Get the length of the [`QuantifierSequence`].
    pub fn len(&self) -> usize {
        self.quantifiers.len()
    }

    pub fn counts(&self) -> Vec<usize> {
        self.names.iter().map(|n| n.len()).collect()
    }

    /// Return whether the sequence is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Restrict the sequence to variables in the given ID set.
    pub fn restrict(&self, ids: HashSet<String>) -> Self {
        Self {
            quantifiers: self.quantifiers.clone(),
            sorts: self.sorts.clone(),
            names: Arc::new(
                self.names
                    .iter()
                    .map(|n| n.iter().filter(|id| ids.contains(*id)).cloned().collect())
                    .collect(),
            ),
        }
    }

    /// Return the number of quantified variables.
    pub fn num_vars(&self) -> usize {
        self.names.iter().map(|n| n.len()).sum()
    }

    /// Return the names of all quantified variables in this sequence.
    pub fn all_vars(&self) -> HashSet<String> {
        self.names.iter().flat_map(|n| n.iter().cloned()).collect()
    }

    /// Generate all atoms in a given signature with this [`QuantifierSequence`].
    pub fn atoms(
        &self,
        signature: &Signature,
        nesting: Option<usize>,
        constants: Option<Vec<Vec<String>>>,
        include_eq: bool,
    ) -> Vec<Term> {
        let mut sorted_terms = vec![vec![]; signature.sorts.len()];
        for (i, v) in self.names.iter().enumerate() {
            sorted_terms[signature.sort_idx(&self.sorts[i])].extend(v.iter().cloned());
        }
        if let Some(consts) = constants {
            for (i, c) in consts.iter().enumerate() {
                sorted_terms[i].extend(c.iter().cloned());
            }
        } else {
            for r in &signature.relations {
                if r.args.is_empty() && !matches!(r.sort, Sort::Bool) {
                    sorted_terms[signature.sort_idx(&r.sort)].push(r.name.clone());
                }
            }
        }

        signature
            .terms_from_basis(&sorted_terms, nesting, include_eq)
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
            .multi_cartesian_product_fixed()
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

    pub fn substitutions_for(&self, other: &Self) -> Vec<Substitution> {
        assert_eq!(self.len(), other.len());

        (0..self.len())
            .map(|i| {
                other.names[i]
                    .iter()
                    .cloned()
                    .permutations(self.names[i].len())
            })
            .multi_cartesian_product_fixed()
            .map(|asgn| {
                self.names
                    .iter()
                    .flatten()
                    .cloned()
                    .zip(asgn.into_iter().flatten().map(Term::Id))
                    .collect()
            })
            .collect()
    }

    pub fn as_universal(&self) -> QuantifierPrefix {
        QuantifierPrefix {
            quantifiers: vec![Quantifier::Forall; self.len()],
            sorts: self.sorts.clone(),
            names: self.names.clone(),
        }
    }

    pub fn subsequences(&self, size: usize) -> Vec<Self> {
        distribute(size, &self.counts())
            .iter()
            .map(|size_dist| Self {
                quantifiers: self.quantifiers.clone(),
                sorts: self.sorts.clone(),
                names: Arc::new(sub_boxes(size_dist, &self.names)),
            })
            .collect()
    }
}

impl QuantifierConfig {
    /// Return all prefixes of the given configuration without any redundancy in terms of containment.
    pub fn prefixes(&self, max_size: usize, last_exist: usize) -> Vec<QuantifierPrefix> {
        let mut res = vec![];

        // Go over all prefix of exact size and existential count, from largest to smallest, and add
        // those that aren't contained by previously added prefixes. Since we go from largest to smallest
        // we will not have any containment between any two prefixes in the result.
        for size in (0..=max_size).rev() {
            for prefix in self.exact_prefixes(size, last_exist) {
                if !res.iter().any(|p: &QuantifierPrefix| p.contains(&prefix)) {
                    res.push(prefix);
                }
            }
        }

        res
    }

    /// Returns all sub-prefixes of exactly length `size` and `exist` existentials
    pub fn exact_prefixes(&self, size: usize, last_exist: usize) -> Vec<QuantifierPrefix> {
        distribute(size, &self.counts())
            .iter()
            .flat_map(|size_dist| {
                let exist_limit = select_last(last_exist, size_dist);
                (0..size_dist.len())
                    .map(|i| {
                        if i >= exist_limit && size_dist[i] > 0 {
                            vec![false, true]
                        } else {
                            vec![false]
                        }
                    })
                    .multi_cartesian_product_fixed()
                    .filter(|exist_select| {
                        exist_select.iter().enumerate().all(|(i, e)| {
                            // Existential selection must conform with configuration in non-zero places.
                            match (self.quantifiers[i], size_dist[i]) {
                                (None, _) | (_, 0) => true,
                                (Some(Quantifier::Forall), _) => !e,
                                (Some(Quantifier::Exists), _) => *e,
                            }
                        })
                    })
                    .map(|exist_select| QuantifierPrefix {
                        quantifiers: exist_select
                            .iter()
                            .map(|e| match e {
                                true => Quantifier::Exists,
                                false => Quantifier::Forall,
                            })
                            .collect(),
                        sorts: self.sorts.clone(),
                        names: Arc::new(sub_boxes(size_dist, &self.names)),
                    })
                    .collect_vec()
            })
            .collect()
    }

    pub fn strictly_universal_vars(&self) -> HashSet<String> {
        self.quantifiers
            .iter()
            .zip(self.names.iter())
            .filter_map(|(q, ns)| match q {
                Some(Quantifier::Forall) => Some(ns.iter().cloned()),
                _ => None,
            })
            .flatten()
            .collect()
    }

    pub fn vars_after_first_exist(&self) -> HashSet<String> {
        match (0..self.len()).find(|i| !matches!(self.quantifiers[*i], Some(Quantifier::Forall))) {
            Some(first_exists) => self.names[first_exists..]
                .iter()
                .flat_map(|ns| ns.iter().cloned())
                .collect(),
            None => HashSet::default(),
        }
    }

    pub fn is_universal(&self) -> bool {
        self.names
            .iter()
            .zip(self.quantifiers.iter())
            .all(|(ns, q)| ns.is_empty() || matches!(q, Some(Quantifier::Forall)))
    }
}

impl Debug for QuantifierConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts = vec![];
        for i in 0..self.len() {
            let q_vec = vec![
                match self.quantifiers[i] {
                    None => "***".to_string(),
                    Some(Quantifier::Exists) => "exists".to_string(),
                    Some(Quantifier::Forall) => "forall".to_string(),
                },
                self.names[i].iter().join(", "),
            ];

            parts.push(q_vec.into_iter().join(" "));
        }

        write!(f, "{}", parts.iter().join(" . "))
    }
}

impl QuantifierPrefix {
    /// Quantify the given term according to this [`QuantifierPrefix`].
    pub fn quantify(&self, mut term: Term) -> Term {
        let present_ids = frame::ids(&term);
        for (i, v) in self.names.iter().enumerate().rev() {
            let binders = v
                .iter()
                .filter_map(|name| {
                    if present_ids.contains(name) {
                        Some(Binder {
                            name: name.clone(),
                            sort: self.sorts[i].clone(),
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
    /// if Q2 can be gotten from Q1 by only flipping universal quantifiers to existential ones
    /// and dropping quantified variables.
    ///
    /// This subsumption behaves in the following way with the [`Ord`] defined for [`QuantifierPrefix`]:
    /// If Q1 subsumes Q2, then Q1 <= Q2.
    pub fn subsumes(&self, other: &Self) -> bool {
        assert_eq!(self.len(), other.len());

        (0..self.len()).all(|i| {
            self.names.is_empty()
                || other.names.is_empty()
                || self.quantifiers[i] == Quantifier::Forall
                || other.quantifiers[i] == Quantifier::Exists
        })
    }

    /// Check whether one [`QuantifierPrefix`] contains another.
    pub fn contains(&self, other: &Self) -> bool {
        assert_eq!(self.len(), other.len());
        (0..self.len()).all(|i| {
            other.names[i].is_empty()
                || (self.quantifiers[i] == other.quantifiers[i]
                    && self.names[i].len() >= other.names[i].len())
        })
    }

    pub fn existentials(&self) -> usize {
        (0..self.len())
            .map(|i| match self.quantifiers[i] {
                Quantifier::Exists => self.names[i].len(),
                Quantifier::Forall => 0,
            })
            .sum()
    }

    pub fn vars_after_first_exist(&self) -> HashSet<String> {
        match (0..self.len()).find(|i| matches!(self.quantifiers[*i], Quantifier::Exists)) {
            Some(first_exists) => self.names[first_exists..]
                .iter()
                .flat_map(|ns| ns.iter().cloned())
                .collect(),
            None => HashSet::default(),
        }
    }

    pub fn is_universal(&self) -> bool {
        self.names
            .iter()
            .zip(self.quantifiers.iter())
            .all(|(ns, q)| ns.is_empty() || matches!(q, Quantifier::Forall))
    }

    /// Convert this [`QuantifierPrefix`] to a [`QuantifierConfig`] by wrapping each
    /// concrete quantifier in `Some()`.
    pub fn to_config(&self) -> QuantifierConfig {
        QuantifierConfig {
            quantifiers: self.quantifiers.iter().map(|q| Some(*q)).collect(),
            sorts: self.sorts.clone(),
            names: self.names.clone(),
        }
    }
}

impl Debug for QuantifierPrefix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts = vec![];
        for i in 0..self.len() {
            let q_vec = vec![
                match self.quantifiers[i] {
                    Quantifier::Exists => "exists".to_string(),
                    Quantifier::Forall => "forall".to_string(),
                },
                self.names[i].iter().join(", "),
            ];

            parts.push(q_vec.into_iter().join(" "));
        }

        write!(f, "{}", parts.iter().join(". "))
    }
}

impl PartialOrd for QuantifierPrefix {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for QuantifierPrefix {
    fn cmp(&self, other: &Self) -> Ordering {
        assert_eq!(self.len(), other.len());
        assert_eq!(self.sorts, other.sorts);

        for i in 0..self.len() {
            match (self.names[i].is_empty(), other.names[i].is_empty()) {
                (true, true) => continue,
                (true, false) => return Ordering::Greater,
                (false, true) => return Ordering::Less,
                (false, false) => (),
            }

            match (self.quantifiers[i], other.quantifiers[i]) {
                (Quantifier::Forall, Quantifier::Exists) => return Ordering::Less,
                (Quantifier::Exists, Quantifier::Forall) => return Ordering::Greater,
                _ => (),
            }

            match self.names[i].len().cmp(&other.names[i].len()) {
                Ordering::Greater => return Ordering::Less,
                Ordering::Less => return Ordering::Greater,
                _ => (),
            }
        }

        Ordering::Equal
    }
}

/// Generate all [`QuantifierPrefix`]es of a given length that respect the specified sort ordering.
///
/// # Arguments
/// * `signature` - The signature containing sort information
/// * `sort_order` - The ordered sequence of sorts (variables will follow this order). Must not contain duplicates.
/// * `prefix_length` - The total number of quantified variables in the prefix
/// * `max_per_sort` - Optional per-sort limits on the number of variables. If `None`, no limit is imposed.
///                     If provided, must have the same length as `sort_order`.
///
/// # Returns
/// A vector of all valid [`QuantifierPrefix`]es where:
/// - The total number of variables equals `prefix_length`
/// - Variables are ordered according to `sort_order` (earlier sorts come before later sorts)
/// - Each position can be either universally or existentially quantified
/// - No sort exceeds its corresponding limit in `max_per_sort` (if specified)
pub fn ordered_prefixes(
    signature: Arc<Signature>,
    sort_order: &[Sort],
    prefix_length: usize,
    max_per_sort: Option<&[usize]>,
) -> Vec<QuantifierPrefix> {
    // Check that sort_order has no duplicates
    assert!(
        sort_order.iter().all_unique(),
        "sort_order must not contain duplicate sorts"
    );

    if prefix_length == 0 {
        return vec![QuantifierPrefix::new(signature, vec![], vec![], &[])];
    }

    // Distribute prefix_length variables across the sorts in sort_order
    let max_limits = max_per_sort
        .map(|limits| {
            assert_eq!(limits.len(), sort_order.len());
            limits.to_vec()
        })
        .unwrap_or_else(|| vec![prefix_length; sort_order.len()]);
    let distributions = distribute(prefix_length, &max_limits);

    distributions
        .into_iter()
        .flat_map(|counts| {
            // For each distribution, generate all combinations of quantifiers
            // Filter out positions with 0 variables and their corresponding quantifiers
            let non_zero_positions: Vec<usize> = counts
                .iter()
                .enumerate()
                .filter_map(|(i, &count)| if count > 0 { Some(i) } else { None })
                .collect();

            if non_zero_positions.is_empty() {
                return vec![];
            }

            // Generate all possible quantifier assignments (Forall or Exists) for non-zero positions
            (0..non_zero_positions.len())
                .map(|_| vec![Quantifier::Forall, Quantifier::Exists])
                .multi_cartesian_product_fixed()
                .map(|quantifiers| {
                    let filtered_sorts: Vec<Sort> = non_zero_positions
                        .iter()
                        .map(|&i| sort_order[i].clone())
                        .collect();
                    let filtered_counts: Vec<usize> =
                        non_zero_positions.iter().map(|&i| counts[i]).collect();

                    QuantifierPrefix::new(
                        signature.clone(),
                        quantifiers,
                        filtered_sorts,
                        &filtered_counts,
                    )
                })
                .collect_vec()
        })
        .collect()
}

/// Generate all [`QuantifierPrefix`]es of a given length that follow the exists* forall* pattern
/// and respect the specified sort ordering.
///
/// This function generates prefixes where all existential quantifiers come before all universal
/// quantifiers. For a prefix with N quantifier positions, it generates N+1 prefixes of the form
/// exists^i forall^(N-i) for i in 0..=N.
///
/// # Arguments
/// * `signature` - The signature containing sort information
/// * `sort_order` - The ordered sequence of sorts (variables will follow this order). Must not contain duplicates.
/// * `prefix_length` - The total number of quantified variables in the prefix
/// * `max_per_sort` - Optional per-sort limits on the number of variables. If `None`, no limit is imposed.
///                     If provided, must have the same length as `sort_order`.
///
/// # Returns
/// A vector of all valid [`QuantifierPrefix`]es where:
/// - The total number of variables equals `prefix_length`
/// - All existential quantifiers come before all universal quantifiers
/// - Variables are ordered according to `sort_order`
/// - No sort exceeds its corresponding limit in `max_per_sort` (if specified)
pub fn ordered_prefixes_exists_forall(
    signature: Arc<Signature>,
    sort_order: &[Sort],
    prefix_length: usize,
    max_per_sort: Option<&[usize]>,
) -> Vec<QuantifierPrefix> {
    // Check that sort_order has no duplicates
    assert!(
        sort_order.iter().all_unique(),
        "sort_order must not contain duplicate sorts"
    );

    if prefix_length == 0 {
        return vec![QuantifierPrefix::new(signature, vec![], vec![], &[])];
    }

    // Distribute prefix_length variables across the sorts in sort_order
    let max_limits = max_per_sort
        .map(|limits| {
            assert_eq!(limits.len(), sort_order.len());
            limits.to_vec()
        })
        .unwrap_or_else(|| vec![prefix_length; sort_order.len()]);
    let distributions = distribute(prefix_length, &max_limits);

    distributions
        .into_iter()
        .flat_map(|counts| {
            // Filter out positions with 0 variables
            let non_zero_positions: Vec<usize> = counts
                .iter()
                .enumerate()
                .filter_map(|(i, &count)| if count > 0 { Some(i) } else { None })
                .collect();

            if non_zero_positions.is_empty() {
                return vec![];
            }

            let num_positions = non_zero_positions.len();

            // For i in 0..=num_positions, create exists^i forall^(num_positions - i)
            (0..=num_positions)
                .map(|num_exists_positions| {
                    let quantifiers: Vec<Quantifier> = (0..num_positions)
                        .map(|i| {
                            if i < num_exists_positions {
                                Quantifier::Exists
                            } else {
                                Quantifier::Forall
                            }
                        })
                        .collect();

                    let filtered_sorts: Vec<Sort> = non_zero_positions
                        .iter()
                        .map(|&i| sort_order[i].clone())
                        .collect();
                    let filtered_counts: Vec<usize> =
                        non_zero_positions.iter().map(|&i| counts[i]).collect();

                    QuantifierPrefix::new(
                        signature.clone(),
                        quantifiers,
                        filtered_sorts,
                        &filtered_counts,
                    )
                })
                .collect_vec()
        })
        .collect()
}

/// Generate all combinations of [`QuantifierPrefix`]es with their maximal constant sets,
/// filtered to include only saturated pairs.
///
/// This function generates prefix+constant pairs by:
/// 1. Generating all possible prefix structures with 0 to `prefix_length` variables
/// 2. For each prefix, generating ALL combinations of maximal constant sets
/// 3. Filtering to keep only pairs where all sorts are saturated
///
/// A constant set is "maximal" for a prefix if, for each sort, it contains exactly
/// `min(total_per_sort[i] - vars_used[i], available_constants[i])` constants.
///
/// A sort S is "saturated" in a (prefix, constants) pair if either:
/// - The prefix has `prefix_length` variables (at maximum length), OR
/// - `vars_of_sort_S + constants_of_sort_S == total_per_sort[S]` (sort is at its limit)
///
/// The saturation filter eliminates redundant pairs: if a sort is not saturated, we could
/// extend the prefix with another variable of that sort, which we will do exhaustively.
/// Therefore, we only keep pairs where all sorts are saturated.
///
/// # Arguments
/// * `signature` - The signature containing sort and relation information
/// * `sort_order` - The ordered sequence of sorts (variables will follow this order). Must not contain duplicates.
/// * `prefix_length` - The maximum number of quantified variables in any prefix
/// * `constant_limit` - The maximum total number of constants across all sorts
/// * `total_per_sort` - The total number of terms (variables + constants) for each sort.
///                      Must have the same length as `sort_order`.
/// * `exists_forall_only` - If true, only generate prefixes following the exists* forall* pattern.
///
/// # Returns
/// A vector of tuples, where each tuple contains:
/// - A [`QuantifierPrefix`] with quantified variables (from 0 to `prefix_length` variables)
/// - A `Vec<Vec<String>>` with a maximal constant set for each sort in `signature.sorts` order.
///   Constants within each sort are ordered according to their appearance in `signature.sorts`.
///
/// Only pairs where all sorts are saturated are included.
pub fn ordered_prefixes_with_constants(
    signature: Arc<Signature>,
    sort_order: &[Sort],
    prefix_length: usize,
    constant_limit: Option<usize>,
    total_per_sort: &[usize],
    exists_forall_only: bool,
) -> Vec<(QuantifierPrefix, Vec<Vec<String>>)> {
    assert_eq!(sort_order.len(), total_per_sort.len());

    // Check that sort_order has no duplicates
    assert!(
        sort_order.iter().all_unique(),
        "sort_order must not contain duplicate sorts"
    );

    // Get all constants from the signature, grouped by sort and ordered by signature.sorts
    let mut constants_by_sort: Vec<Vec<String>> = vec![vec![]; signature.sorts.len()];
    for r in &signature.relations {
        if r.args.is_empty() && !matches!(r.sort, Sort::Bool) {
            let sort_idx = signature.sort_idx(&r.sort);
            constants_by_sort[sort_idx].push(r.name.clone());
        }
    }

    // Generate all possible prefix structures with 0 to prefix_length variables
    let all_prefixes: Vec<QuantifierPrefix> = (0..=prefix_length)
        .flat_map(|num_vars| {
            if exists_forall_only {
                ordered_prefixes_exists_forall(
                    signature.clone(),
                    sort_order,
                    num_vars,
                    Some(total_per_sort), // Respect total_per_sort as max constraint
                )
            } else {
                ordered_prefixes(
                    signature.clone(),
                    sort_order,
                    num_vars,
                    Some(total_per_sort), // Respect total_per_sort as max constraint
                )
            }
        })
        .collect();

    // For each prefix, compute all maximal constant sets
    all_prefixes
        .into_iter()
        .flat_map(|prefix| {
            // Count how many variables this prefix uses per sort (in sort_order indexing)
            let mut vars_per_sort_order = vec![0; sort_order.len()];
            for (i, names) in prefix.names.iter().enumerate() {
                let sort_idx = sort_order
                    .iter()
                    .position(|s| s == &prefix.sorts[i])
                    .expect("Prefix sort should be in sort_order");
                vars_per_sort_order[sort_idx] += names.len();
            }

            // Calculate maximal constants per sort (in sort_order indexing)
            let max_constants_per_sort_order: Vec<usize> = total_per_sort
                .iter()
                .zip(vars_per_sort_order.iter())
                .enumerate()
                .map(|(i, (total, vars))| {
                    let available = total.saturating_sub(*vars);
                    let sort_idx = signature.sort_idx(&sort_order[i]);
                    available.min(constants_by_sort[sort_idx].len())
                })
                .collect();

            // Calculate the maximum total constants we can have for this prefix
            // It's the minimum of: sum of per-sort maximums, and constant_limit (if specified)
            let total_max_constants: usize = max_constants_per_sort_order.iter().sum();
            let max_constants_to_distribute = match constant_limit {
                Some(limit) => total_max_constants.min(limit),
                None => total_max_constants, // No limit - use all available constants
            };

            // Use distribute to find all ways to distribute exactly max_constants_to_distribute constants
            // across the sorts, respecting the per-sort maximal limits
            let constant_distributions =
                distribute(max_constants_to_distribute, &max_constants_per_sort_order);

            // For each distribution, generate all combinations of constants
            constant_distributions
                .into_iter()
                .flat_map(|distribution| {
                    // For each sort, generate all ways to select distribution[i] constants
                    let constant_combinations: Vec<Vec<Vec<String>>> = sort_order
                        .iter()
                        .enumerate()
                        .map(|(i, sort)| {
                            let sort_idx = signature.sort_idx(sort);
                            let num_to_select = distribution[i];
                            if num_to_select == 0 {
                                vec![vec![]]
                            } else {
                                constants_by_sort[sort_idx]
                                    .iter()
                                    .cloned()
                                    .combinations(num_to_select)
                                    .collect()
                            }
                        })
                        .collect();

                    // Generate all combinations across sorts for this distribution
                    constant_combinations
                        .into_iter()
                        .multi_cartesian_product_fixed()
                        .collect_vec()
                })
                .filter_map(|selected_constants_by_order| {
                    // Check saturation: a sort is saturated if either:
                    // 1. The prefix is at max length (prefix_length), OR
                    // 2. vars_in_sort + constants_in_sort == total_per_sort[sort]
                    let is_prefix_at_max = prefix.num_vars() == prefix_length;

                    let all_sorts_saturated = (0..sort_order.len()).all(|i| {
                        let total_for_sort =
                            vars_per_sort_order[i] + selected_constants_by_order[i].len();
                        is_prefix_at_max || total_for_sort == total_per_sort[i]
                    });

                    // Only keep this combination if all sorts are saturated
                    if !all_sorts_saturated {
                        return None;
                    }

                    // Convert from sort_order indexing to signature.sorts indexing
                    let mut selected_constants = vec![vec![]; signature.sorts.len()];
                    for (i, sort) in sort_order.iter().enumerate() {
                        let sort_idx = signature.sort_idx(sort);
                        selected_constants[sort_idx] = selected_constants_by_order[i].clone();
                    }
                    Some((prefix.clone(), selected_constants))
                })
                .collect_vec()
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use fly::{parser, term::subst::Substitution};
    use std::collections::HashMap;

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

        let sort = Sort::uninterpreted;
        let config = QuantifierConfig::new(
            Arc::new(signature),
            vec![None, None, None],
            vec![sort("A"), sort("B"), sort("C")],
            &[2, 1, 2],
        );
        let a = |i: usize| format!("A_{i}");
        let b = |i: usize| format!("B_{i}");
        let c = |i: usize| format!("C_{i}");
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

    #[test]
    fn test_ordered_prefixes() {
        let signature = Arc::new(parser::parse_signature(
            r#"
sort A
sort B
sort C
"#
            .trim(),
        ));

        let sort = Sort::uninterpreted;
        let sort_order = vec![sort("A"), sort("B"), sort("C")];

        // Test with prefix_length = 0
        let prefixes = ordered_prefixes(signature.clone(), &sort_order, 0, None);
        assert_eq!(prefixes.len(), 1);
        assert_eq!(prefixes[0].num_vars(), 0);

        // Test with prefix_length = 1
        let prefixes = ordered_prefixes(signature.clone(), &sort_order, 1, None);
        // Should have 3 sorts * 2 quantifiers = 6 prefixes
        assert_eq!(prefixes.len(), 6);
        assert!(prefixes.iter().all(|p| p.num_vars() == 1));

        // Test with prefix_length = 2
        let prefixes = ordered_prefixes(signature.clone(), &sort_order, 2, None);
        // Should have multiple distributions: (2,0,0), (1,1,0), (1,0,1), (0,2,0), (0,1,1), (0,0,2)
        // Each with 2 quantifier choices (Forall/Exists) or 4 for two positions
        assert!(prefixes.len() > 0);
        assert!(prefixes.iter().all(|p| p.num_vars() == 2));

        // Verify ordering is preserved - earlier sorts should come before later sorts
        for prefix in &prefixes {
            let mut seen_sorts = vec![];
            for (i, names) in prefix.names.iter().enumerate() {
                if !names.is_empty() {
                    seen_sorts.push(&prefix.sorts[i]);
                }
            }
            // Check that seen_sorts maintains the order from sort_order
            for i in 0..seen_sorts.len() - 1 {
                let idx1 = sort_order.iter().position(|s| s == seen_sorts[i]).unwrap();
                let idx2 = sort_order
                    .iter()
                    .position(|s| s == seen_sorts[i + 1])
                    .unwrap();
                assert!(idx1 < idx2, "Sort ordering not preserved in prefix");
            }
        }

        // Test with max_per_sort constraint
        let prefixes = ordered_prefixes(signature.clone(), &sort_order, 3, Some(&[1, 1, 1]));
        // With max 1 variable per sort and 3 total variables, we need all 3 sorts
        // Each distribution should be (1,1,1), giving 2^3 = 8 quantifier combinations
        assert_eq!(prefixes.len(), 8);
        assert!(prefixes.iter().all(|p| p.num_vars() == 3));
        // Verify no sort has more than 1 variable
        for prefix in &prefixes {
            for names in prefix.names.iter() {
                assert!(
                    names.len() <= 1,
                    "Sort has more than max_per_sort variables"
                );
            }
        }

        // Test max_per_sort = [2, 2, 2] with prefix_length = 4
        let prefixes = ordered_prefixes(signature.clone(), &sort_order, 4, Some(&[2, 2, 2]));
        assert!(prefixes.len() > 0);
        assert!(prefixes.iter().all(|p| p.num_vars() == 4));
        // Verify no sort has more than 2 variables
        for prefix in &prefixes {
            for names in prefix.names.iter() {
                assert!(
                    names.len() <= 2,
                    "Sort has more than max_per_sort variables"
                );
            }
        }
    }

    #[test]
    fn test_ordered_prefixes_with_constants() {
        let signature = Arc::new(parser::parse_signature(
            r#"
sort A
sort B
sort C

mutable c1: A
mutable c2: A
mutable c3: B
"#
            .trim(),
        ));

        let sort = Sort::uninterpreted;
        let sort_order = vec![sort("A"), sort("B"), sort("C")];

        // Test with total_per_sort = [2, 1, 0] and prefix_length = 3
        // New behavior: generates all prefixes with 0-3 variables, each with maximal constants
        // For each prefix, constants are maximal: min(total_per_sort[i] - vars[i], available_constants[i])
        let total_per_sort = vec![2, 1, 0];
        let results = ordered_prefixes_with_constants(
            signature.clone(),
            &sort_order,
            3,
            None, // constant_limit: unlimited for this test
            &total_per_sort,
            false,
        );

        assert!(results.len() > 0);

        // Verify that for each result, variables + constants per sort does not exceed total_per_sort
        // and that constants are maximal given the variable distribution
        for (prefix, constants) in &results {
            // Count variables per sort from the prefix
            let mut vars_per_sort = vec![0; sort_order.len()];
            for (i, names) in prefix.names.iter().enumerate() {
                let sort_idx = sort_order
                    .iter()
                    .position(|s| s == &prefix.sorts[i])
                    .unwrap();
                vars_per_sort[sort_idx] += names.len();
            }

            // Verify constraints
            for i in 0..sort_order.len() {
                let total = vars_per_sort[i] + constants[i].len();
                // Total should not exceed total_per_sort
                assert!(
                    total <= total_per_sort[i],
                    "Sort {:?}: total {} exceeds limit {}",
                    sort_order[i],
                    total,
                    total_per_sort[i]
                );

                // Constants should be maximal: min(total_per_sort[i] - vars[i], available)
                let sort_idx = signature.sort_idx(&sort_order[i]);
                let available_constants = if sort_idx == signature.sort_idx(&sort("A")) {
                    2 // c1, c2
                } else if sort_idx == signature.sort_idx(&sort("B")) {
                    1 // c3
                } else {
                    0 // C has no constants
                };
                let max_possible = (total_per_sort[i] - vars_per_sort[i]).min(available_constants);
                assert_eq!(
                    constants[sort_idx].len(),
                    max_possible,
                    "Sort {:?}: expected {} constants (maximal), got {}",
                    sort_order[i],
                    max_possible,
                    constants[sort_idx].len()
                );
            }
        }

        // Verify that we're generating prefixes with different variable counts (0 to prefix_length)
        let var_counts: std::collections::HashSet<usize> = results
            .iter()
            .map(|(prefix, _)| prefix.num_vars())
            .collect();
        assert!(
            var_counts.len() > 1,
            "Should generate prefixes with varying numbers of variables"
        );

        // Test with uniform total_per_sort = [1, 1, 1]
        let results = ordered_prefixes_with_constants(
            signature.clone(),
            &sort_order,
            3,
            None,
            &[1, 1, 1],
            false,
        );
        assert!(results.len() > 0);

        // Verify all results respect the constraints
        for (prefix, constants) in &results {
            // Total vars + constants should not exceed 3 (sum of total_per_sort)
            let total = prefix.num_vars() + constants.iter().map(|c| c.len()).sum::<usize>();
            assert!(total <= 3, "Total atomic terms {} exceeds limit 3", total);

            // Verify per-sort constraints
            let mut vars_per_sort = vec![0; sort_order.len()];
            for (i, names) in prefix.names.iter().enumerate() {
                let sort_idx = sort_order
                    .iter()
                    .position(|s| s == &prefix.sorts[i])
                    .unwrap();
                vars_per_sort[sort_idx] += names.len();
            }

            for i in 0..sort_order.len() {
                let sort_idx = signature.sort_idx(&sort_order[i]);
                let total_for_sort = vars_per_sort[i] + constants[sort_idx].len();
                assert!(
                    total_for_sort <= 1,
                    "Sort {:?}: total {} exceeds per-sort limit 1",
                    sort_order[i],
                    total_for_sort
                );
            }
        }
    }

    #[test]
    fn test_prefix_to_config() {
        let signature = Arc::new(parser::parse_signature(
            r#"
sort A
sort B
"#
            .trim(),
        ));

        let sort = Sort::uninterpreted;
        let prefix = QuantifierPrefix::new(
            signature.clone(),
            vec![Quantifier::Forall, Quantifier::Exists],
            vec![sort("A"), sort("B")],
            &[2, 1],
        );

        let config = prefix.to_config();

        // Verify the config has the same structure
        assert_eq!(config.len(), prefix.len());
        assert_eq!(config.sorts, prefix.sorts);
        assert_eq!(config.names, prefix.names);

        // Verify quantifiers are wrapped in Some()
        assert_eq!(config.quantifiers[0], Some(Quantifier::Forall));
        assert_eq!(config.quantifiers[1], Some(Quantifier::Exists));

        // Verify the config has the same number of variables
        assert_eq!(config.num_vars(), prefix.num_vars());
    }

    #[test]
    fn test_saturation_filter() {
        // Test that the saturation filter correctly eliminates redundant pairs.
        //
        // Key insight: A (prefix, constants) pair is redundant if we can add more variables
        // to the prefix while respecting total_per_sort limits. The saturation filter ensures
        // that for each pair, either:
        // 1. The prefix is at max length (can't add more variables), OR
        // 2. Every sort is "saturated" - has reached its total_per_sort limit
        //
        // This way, any unsaturated pair with a shorter prefix will be dominated by
        // a pair with a longer prefix that we generate exhaustively.

        let signature = Arc::new(parser::parse_signature(
            r#"
sort A
sort B

mutable c1_A: A
mutable c2_A: A
mutable c1_B: B
mutable c2_B: B
"#
            .trim(),
        ));

        let sort = Sort::uninterpreted;
        let sort_order = vec![sort("A"), sort("B")];

        // Test with prefix_length=3, total_per_sort=[2, 2]
        // This means:
        // - Prefixes can have 0-3 variables total
        // - Each sort can have at most 2 total terms (vars + constants)
        // - We have 2 constants available per sort
        let results =
            ordered_prefixes_with_constants(signature.clone(), &sort_order, 3, None, &[2, 2], false);

        // Helper to check if a result matches a description
        let has_prefix_with = |num_a_vars: usize,
                               num_b_vars: usize,
                               num_a_consts: usize,
                               num_b_consts: usize|
         -> bool {
            results.iter().any(|(prefix, constants)| {
                let mut vars_per_sort = vec![0; 2];
                for (i, names) in prefix.names.iter().enumerate() {
                    let sort_idx = sort_order
                        .iter()
                        .position(|s| s == &prefix.sorts[i])
                        .unwrap();
                    vars_per_sort[sort_idx] += names.len();
                }
                let a_sort_idx = signature.sort_idx(&sort("A"));
                let b_sort_idx = signature.sort_idx(&sort("B"));

                vars_per_sort[0] == num_a_vars
                    && vars_per_sort[1] == num_b_vars
                    && constants[a_sort_idx].len() == num_a_consts
                    && constants[b_sort_idx].len() == num_b_consts
            })
        };

        // SHOULD BE INCLUDED (saturated cases):

        // Case 1: Prefix at max length (3 vars) - must include maximal constants
        // Note: Even at max length, we must use maximal constants (can't have "room" to add more).
        // For "2 A-vars, 1 B-var": A has 2 terms (at limit), B has 1 var so needs 1 const for 2 total
        assert!(
            has_prefix_with(2, 1, 0, 1),
            "Should include: 2 A-vars, 1 B-var, 1 B-const (prefix at max, maximal constants)"
        );
        // For "1 A-var, 2 B-vars": A has 1 var so needs 1 const, B has 2 terms (at limit)
        assert!(
            has_prefix_with(1, 2, 1, 0),
            "Should include: 1 A-var, 2 B-vars, 1 A-const (prefix at max, maximal constants)"
        );

        // Case 2: All sorts saturated at their limits (regardless of prefix length)
        assert!(
            has_prefix_with(0, 0, 2, 2),
            "Should include: 0 vars, 2 A-consts, 2 B-consts (all sorts saturated)"
        );
        assert!(
            has_prefix_with(1, 0, 1, 2),
            "Should include: 1 A-var, 1 A-const, 2 B-consts (all sorts saturated)"
        );
        assert!(
            has_prefix_with(0, 1, 2, 1),
            "Should include: 1 B-var, 2 A-consts, 1 B-const (all sorts saturated)"
        );
        assert!(
            has_prefix_with(1, 1, 1, 1),
            "Should include: 1 A-var, 1 B-var, 1 A-const, 1 B-const (all sorts saturated)"
        );

        // SHOULD BE FILTERED OUT (not saturated):
        // These pairs have prefix not at max AND at least one sort not at its limit,
        // meaning we could extend the prefix with another variable.

        assert!(
            !has_prefix_with(1, 0, 0, 0),
            "Should filter: 1 A-var only (B not saturated, not at max)"
        );
        assert!(
            !has_prefix_with(0, 1, 0, 0),
            "Should filter: 1 B-var only (A not saturated, not at max)"
        );
        assert!(
            !has_prefix_with(1, 0, 1, 0),
            "Should filter: 1 A-var, 1 A-const (B not saturated, not at max)"
        );
        assert!(
            !has_prefix_with(2, 0, 0, 1),
            "Should filter: 2 A-vars, 1 B-const (B has 1 term < 2, not at max)"
        );

        // Verify that ALL included results satisfy the saturation property
        for (prefix, constants) in &results {
            let mut vars_per_sort = vec![0; 2];
            for (i, names) in prefix.names.iter().enumerate() {
                let sort_idx = sort_order
                    .iter()
                    .position(|s| s == &prefix.sorts[i])
                    .unwrap();
                vars_per_sort[sort_idx] += names.len();
            }

            let is_at_max = prefix.num_vars() == 3;
            let a_sort_idx = signature.sort_idx(&sort("A"));
            let b_sort_idx = signature.sort_idx(&sort("B"));

            let a_saturated = vars_per_sort[0] + constants[a_sort_idx].len() == 2;
            let b_saturated = vars_per_sort[1] + constants[b_sort_idx].len() == 2;
            let all_saturated = a_saturated && b_saturated;

            assert!(
                is_at_max || all_saturated,
                "Found non-saturated pair: {} A-vars, {} B-vars, {} A-consts, {} B-consts (at_max={}, all_sat={})",
                vars_per_sort[0],
                vars_per_sort[1],
                constants[a_sort_idx].len(),
                constants[b_sort_idx].len(),
                is_at_max,
                all_saturated
            );
        }
    }
}

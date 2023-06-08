// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Trie-based data structures employed in inference algorithms.

use crate::inference::hashmap::{HashMap, HashSet};
use itertools::Itertools;
use std::hash::Hash;
use std::rc::Rc;

use crate::fly::semantics::{Assignment, Model};
use crate::fly::syntax::{BinOp, Quantifier, Term};
use crate::term::subst::{substitute_qf, Substitution};

use crate::inference::lemma::{Literal, Qcnf};
use crate::inference::quant::{QuantifierConfig, QuantifierPrefix};

use super::lemma::{LemmaQf, WeakenQf};

/// Extend an assignment by all possible assignments to the given variables
/// over a domain containing the given number of elements.
fn extend_assignment(
    assignment: &Assignment,
    vars: &[String],
    elem_count: usize,
) -> Vec<Assignment> {
    assert!(!vars.is_empty());

    vars.iter()
        .map(|_| 0..elem_count)
        .multi_cartesian_product()
        .map(|asgn| {
            let mut new_assignment = assignment.clone();
            for i in 0..vars.len() {
                new_assignment.insert(vars[i].clone(), asgn[i]);
            }

            new_assignment
        })
        .collect_vec()
}

/// A [`Trie`] is a prefix-tree of ordered sequences, where each sequence
/// has an ID attached to it.
#[derive(Clone)]
struct Trie<T: Clone + Hash + Ord> {
    /// The ID of the sequence on the path to this sub-trie.
    id: Option<usize>,
    /// Labeled edges to existing sub-tries.
    next: HashMap<T, Trie<T>>,
}

impl<T: Clone + Hash + Ord> Trie<T> {
    /// Create an empty [`Trie`].
    fn new() -> Self {
        Self {
            id: None,
            next: HashMap::new(),
        }
    }

    /// Find the ID of a sequence in the [`Trie`], if it exists.
    fn find(&self, seq: &[T]) -> Option<usize> {
        if seq.is_empty() {
            self.id
        } else if let Some(trie) = self.next.get(&seq[0]) {
            trie.find(&seq[1..])
        } else {
            None
        }
    }

    /// Add a sequence to the [`Trie`] with the specified ID.
    fn add(&mut self, seq: &[T], id: usize) {
        if seq.is_empty() {
            assert_eq!(self.id, None);
            self.id = Some(id);
        } else if let Some(next_trie) = self.next.get_mut(&seq[0]) {
            next_trie.add(&seq[1..], id);
        } else {
            let mut next_trie = Trie::new();
            next_trie.add(&seq[1..], id);
            self.next.insert(seq[0].clone(), next_trie);
        }
    }

    /// Remove a sequence from the [`Trie`] and return its ID.
    fn remove(&mut self, seq: &[T]) -> usize {
        if seq.is_empty() {
            let id = self.id.expect("Sequence not in trie.");
            self.id = None;
            id
        } else {
            let next_trie = self.next.get_mut(&seq[0]).expect("Sequence not in trie.");
            let id = next_trie.remove(&seq[1..]);
            if next_trie.id.is_none() && next_trie.next.is_empty() {
                self.next.remove(&seq[0]);
            }
            id
        }
    }

    /// Find all subsets of a sequence in the [`Trie`] and return their ID's.
    fn subsets(&self, seq: &[T]) -> HashSet<usize> {
        let mut subsets = HashSet::from_iter(self.id);
        if !seq.is_empty() {
            subsets.extend(
                (0..seq.len())
                    .filter(|&i| self.next.contains_key(&seq[i]))
                    .flat_map(|i| self.next[&seq[i]].subsets(&seq[(i + 1)..])),
            )
        }

        subsets
    }
}

/// A [`PowerTrie`] represents a collection of sets of ordered sequences.
#[derive(Clone)]
struct PowerTrie<T: Clone + Hash + Ord> {
    /// Holds all ordered sequences from all sets.
    trie: Trie<T>,
    /// Maps sequence ids to actual sequences.
    seqs: HashMap<usize, Vec<T>>,
    /// Maps sets to the sequences they contain.
    sets_to_seqs: HashMap<usize, Vec<usize>>,
    /// Maps sequences to the sets that contain them.
    seqs_to_sets: HashMap<usize, HashSet<usize>>,
    /// The ID of the next inserted sequence.
    next_seq: usize,
    /// The ID of the next created set.
    next_set: usize,
}

impl<T: Clone + Hash + Ord> PowerTrie<T> {
    fn _health_check(&self) {
        for id in self.seqs.keys() {
            assert!(id < &self.next_seq);
            assert!(self.seqs_to_sets.contains_key(id));
        }

        for (id, sets) in &self.seqs_to_sets {
            assert!(self.seqs.contains_key(id));
            for set_id in sets {
                assert!(self.sets_to_seqs[set_id].contains(id));
            }
        }

        for (id, seqs) in &self.sets_to_seqs {
            assert!(id < &self.next_set);
            for seq_id in seqs {
                assert!(self.seqs_to_sets[seq_id].contains(id));
            }
        }
    }

    /// Create an empty [`PowerTrie`].
    fn new() -> Self {
        Self {
            trie: Trie::new(),
            seqs: HashMap::new(),
            sets_to_seqs: HashMap::new(),
            seqs_to_sets: HashMap::new(),
            next_seq: 0,
            next_set: 0,
        }
    }

    /// Return all sets containing at least one of the given sequences.
    fn containing_sets<'a, I: IntoIterator<Item = &'a usize>>(&self, seq_ids: I) -> HashSet<usize> {
        seq_ids
            .into_iter()
            .flat_map(|seq_id| &self.seqs_to_sets[seq_id])
            .cloned()
            .collect()
    }

    /// Return all ID's of sets subsuming the given set of sequences,
    /// which also satify the provided filter.
    ///
    /// A set `s1` subsumes a set `s2` iff for every sequence in `s2`,
    /// there exists a subset of it in `s1`.
    fn subsuming<F: Fn(&usize) -> bool>(&self, seqs: &[&[T]], filter: F) -> HashSet<usize> {
        let mut i = 0;
        let mut set_ids: HashSet<usize> = self.containing_sets(&self.trie.subsets(seqs[i]));
        set_ids.retain(filter);

        while i < seqs.len() && !set_ids.is_empty() {
            set_ids = set_ids
                .intersection(&self.containing_sets(&self.trie.subsets(seqs[i])))
                .cloned()
                .collect();
            i += 1;
        }

        set_ids
    }

    /// Add the sequence to the [`PowerTrie`].
    fn add_seq(&mut self, seq: &[T]) -> usize {
        match self.trie.find(seq) {
            Some(id) => id,
            None => {
                let id = self.next_seq;
                self.next_seq += 1;

                self.trie.add(seq, id);
                self.seqs.insert(id, Vec::from(seq));
                self.seqs_to_sets.insert(id, HashSet::new());

                id
            }
        }
    }

    /// Add the set containing the given sequence IDs to the [`PowerTrie`].
    fn add_set(&mut self, seq_ids: &[usize]) -> usize {
        let id = self.next_set;
        self.next_set += 1;

        self.sets_to_seqs.insert(id, Vec::from(seq_ids));
        for seq_id in seq_ids {
            self.seqs_to_sets.get_mut(seq_id).unwrap().insert(id);
        }

        id
    }

    fn remove_set(&mut self, set_id: &usize) {
        let seq_ids: HashSet<usize> = HashSet::from_iter(self.sets_to_seqs.remove(set_id).unwrap());
        for seq_id in &seq_ids {
            self.seqs_to_sets.get_mut(seq_id).unwrap().remove(set_id);
            if self.seqs_to_sets[seq_id].is_empty() {
                self.seqs_to_sets.remove(seq_id);
                let seq = self.seqs.remove(seq_id).unwrap();
                assert_eq!(self.trie.remove(&seq), *seq_id);
            }
        }
    }
}

/// A [`QCNFSet`] is a set of quantified CNF formulas with a shared [`QuantifierConfig`], a common
/// set of atoms, and some bound on the number of clauses and the number of literals in each clause.
#[derive(Clone)]
pub struct QcnfSet<B: LemmaQf, W: WeakenQf<B>> {
    /// The shared [`QuantifierConfig`] of the quantified CNF formulas.
    config: Rc<QuantifierConfig>,
    /// The weaken configuration for the quantifier-free bodies.
    weaken: Rc<W>,
    /// The common atoms of the quantified CNF formulas.
    atoms: Rc<Vec<Term>>,
    /// A reverse mapping from each atom to its index.
    atom_to_index: Rc<HashMap<Term, usize>>,
    /// A [`PowerTrie`] holding the CNF bodies.
    power_trie: PowerTrie<Literal>,
    /// The mapping from the ID of each quantified CNF formula to its [`QuantifierPrefix`].
    pub prefixes: HashMap<usize, QuantifierPrefix>,
    /// The quantifier-free body of lemmas.
    pub bodies: HashMap<usize, B>,
}

impl<L: LemmaQf, W: WeakenQf<L>> QcnfSet<L, W> {
    /// Create an empty [`QCNFSet`].
    pub fn new(config: Rc<QuantifierConfig>, weaken: Rc<W>, atoms: Rc<Vec<Term>>) -> Self {
        let atom_to_index = Rc::new(
            atoms
                .iter()
                .enumerate()
                .map(|(index, term)| (term.clone(), index))
                .collect(),
        );
        Self {
            config,
            weaken,
            atoms,
            atom_to_index,
            power_trie: PowerTrie::new(),
            prefixes: HashMap::new(),
            bodies: HashMap::new(),
        }
    }

    /// Add a the strongest possible formula to the [`QCNFSet`].
    pub fn add_strongest(&mut self) {
        let prefix = self.config.strongest_prefix();
        for body in self.weaken.strongest() {
            self.add(prefix.clone(), body);
        }
    }

    /// Create an empty [`QCNFSet`] with the same configuration.
    pub fn clone_empty(&self) -> Self {
        Self {
            config: self.config.clone(),
            weaken: self.weaken.clone(),
            atoms: self.atoms.clone(),
            atom_to_index: self.atom_to_index.clone(),
            power_trie: PowerTrie::new(),
            prefixes: HashMap::new(),
            bodies: HashMap::new(),
        }
    }

    /// Return the number of quantified CNF formulas in the set.
    pub fn len(&self) -> usize {
        self.prefixes.len()
    }

    /// Return the number of distinct clauses in the set.
    pub fn len_clauses(&self) -> usize {
        self.power_trie.seqs.len()
    }

    /// Return the [`Literal`] corresponding to the application of the given [`Substitution`]
    /// to the given [`Literal`].
    fn substitute_literal(&self, literal: &Literal, substitution: &Substitution) -> Literal {
        match &self.atoms[literal.0] {
            Term::BinOp(BinOp::Equals, t1, t2) => {
                let t1_sub = Box::new(substitute_qf(t1, substitution));
                let t2_sub = Box::new(substitute_qf(t2, substitution));

                if let Some(&index) = self.atom_to_index.get(&Term::BinOp(
                    BinOp::Equals,
                    t1_sub.clone(),
                    t2_sub.clone(),
                )) {
                    (index, literal.1)
                } else if let Some(&index) =
                    self.atom_to_index
                        .get(&Term::BinOp(BinOp::Equals, t2_sub, t1_sub))
                {
                    (index, literal.1)
                } else {
                    panic!("Atom after substitution does not exist!");
                }
            }
            _ => (
                self.atom_to_index[&substitute_qf(&self.atoms[literal.0], substitution)],
                literal.1,
            ),
        }
    }

    /// Find all quantified CNF formulas which subsume the given quantifier prefix and clauses.
    ///
    /// A quantified CNF subsumes another iff subsumption holds both for the prefix and for the sets of clauses.
    /// See [`Trie::subsets`](Trie) for a definition of clause set subsumption, and [`QuantifierPrefix::subsumes`](QuantifierPrefix)
    /// for a defintion of quantifier-prefix subsumption.
    fn subsuming_exact(&self, prefix: &QuantifierPrefix, clauses: &[&[Literal]]) -> HashSet<usize> {
        self.power_trie
            .subsuming(clauses, |id| self.prefixes[id].subsumes(prefix))
    }

    /// Find all quantified CNF formulas which subsume the given quantifier prefix and clauses,
    /// allowing for permutations in same-quantifier variables, as defined in [`QuantifierConfig`].
    /// The considered permutations are only over variables at indices >= `start_at` in the [`QuantifierConfig`].
    ///
    /// If `max_count` is `Some(k)`, return up to the first `k` quantified CNF formulas found.
    pub fn subsuming(
        &self,
        prefix: &QuantifierPrefix,
        clauses: &[&[Literal]],
        start_at: usize,
        max_count: Option<usize>,
    ) -> HashSet<usize> {
        let mut subsuming = HashSet::new();

        // Find relevant Term::Id's that can be substituted.
        let ids: HashSet<String> = clauses
            .iter()
            .flat_map(|cl| cl.iter().flat_map(|lit| self.atoms[lit.0].ids()))
            .collect();
        // Go over all subsutitutions which permute the relevant variables.
        for perm in &self.config.permutations(start_at, Some(&ids)) {
            // Compute the clauses after the permutation.
            let perm_clauses = clauses
                .iter()
                .map(|clause| {
                    clause
                        .iter()
                        .map(|literal| self.substitute_literal(literal, perm))
                        .collect_vec()
                })
                .collect_vec();

            // Find those subsuming the permuted clauses and add the to the return set.
            for &id in &self.subsuming_exact(
                prefix,
                &perm_clauses
                    .iter()
                    .map(|clause| clause.as_slice())
                    .collect_vec(),
            ) {
                subsuming.insert(id);
                if max_count.is_some() && subsuming.len() >= max_count.unwrap() {
                    return subsuming;
                }
            }
        }

        subsuming
    }

    /// Check whether the [`QCNFSet`] subsumes the given quantifier prefix and clauses,
    /// allowing for permutations in same-quantifier variables, as defined in the set's [`QuantifierConfig`].
    ///
    /// A [`QCNFSet`] subsumes a quantified CNF formula if it contains another which subsumes it.
    pub fn subsumes(
        &self,
        prefix: &QuantifierPrefix,
        clauses: &[&[Literal]],
        start_at: usize,
    ) -> bool {
        !self
            .subsuming(prefix, clauses, start_at, Some(1))
            .is_empty()
    }

    /// Add the given quantified CNF formula to the [`QCNFSet`].
    pub fn add(&mut self, prefix: QuantifierPrefix, body: L) -> usize {
        let seq_ids = body
            .to_cnf()
            .iter()
            .map(|cl| self.power_trie.add_seq(cl))
            .collect_vec();
        let id = self.power_trie.add_set(&seq_ids);
        self.prefixes.insert(id, prefix.clone());
        self.bodies.insert(id, body);

        id
    }

    /// Remove the quantified CNF formula associated with the given ID from the [`QCNFSet`].
    pub fn remove(&mut self, id: &usize) {
        self.power_trie.remove_set(id);
        self.prefixes.remove(id);
        self.bodies.remove(id);
    }

    /// Minimize the [`QCNFSet`] with respect to subsumption with permutations over indices >= `start_at`.
    fn minimize(&mut self, start_at: usize) {
        for id in &self.prefixes.keys().copied().collect_vec() {
            if self
                .subsuming(
                    &self.prefixes[id],
                    &self.qcnf_clauses(id),
                    start_at,
                    Some(2),
                )
                .len()
                > 1
            {
                self.remove(id);
            }
        }
    }

    /// Return the clauses of the formula associated with the given ID.
    pub fn qcnf_clauses(&self, id: &usize) -> Vec<&[Literal]> {
        self.power_trie.sets_to_seqs[id]
            .iter()
            .map(|cl_id| self.power_trie.seqs[cl_id].as_slice())
            .collect_vec()
    }

    /// Merge two [`QCNFSet`]'s, dropping subsumed formulas.
    fn merge(&mut self, mut other: QcnfSet<L, W>, start_at: usize) {
        // Drop formulas in `other` subsumed by `self`.
        for id in &other.prefixes.keys().cloned().collect_vec() {
            if self.subsumes(&other.prefixes[id], &other.qcnf_clauses(id), start_at) {
                other.remove(id);
            }
        }

        // Drop formulas in `self` subsumed by `other`.
        for id in &self.prefixes.keys().cloned().collect_vec() {
            if other.subsumes(&self.prefixes[id], &self.qcnf_clauses(id), start_at) {
                self.remove(id);
            }
        }

        // Add the remaining formulas in `other` to `self`.
        for (id, prefix) in other.prefixes.into_iter() {
            self.add(prefix, other.bodies.remove(&id).unwrap());
        }
    }

    fn weaken_qcnfs(
        &self,
        prefix: &QuantifierPrefix,
        qcnf_ids: &HashSet<usize>,
        cube: &[Literal],
    ) -> (HashSet<usize>, QcnfSet<L, W>) {
        // Compute the negation of the cube, i.e. a clause which is equivalent to its negation.
        let neg_cube = cube.iter().map(|&(i, b)| (i, !b)).collect_vec();
        let to_weaken = self
            .power_trie
            .subsuming(&[&neg_cube], |id| qcnf_ids.contains(id));

        let mut new_qcnf_set = self.clone_empty();
        for id in &to_weaken {
            for body in self.weaken.weaken(&self.bodies[id], cube, &self.atoms) {
                new_qcnf_set.add(prefix.clone(), body);
            }
        }

        (to_weaken, new_qcnf_set)
    }

    fn weaken_rec(
        &self,
        qcnf_ids: &HashSet<usize>,
        model: &Model,
        vars: &Vec<Vec<String>>,
        assignment: &Assignment,
        index: usize,
        perm_index: usize,
        prefix: &QuantifierPrefix,
    ) -> (HashSet<usize>, QcnfSet<L, W>) {
        if index >= self.config.len() {
            let cube = self
                .atoms
                .iter()
                .enumerate()
                .map(|(i, a)| (i, model.eval_assign(a, assignment.clone()) == 1))
                .collect_vec();

            let mut weakened = self.weaken_qcnfs(prefix, qcnf_ids, &cube);
            weakened.1.minimize(perm_index);

            return weakened;
        }

        let quantifier = self.config.quantifiers[index];
        let mut modified: HashSet<usize> = HashSet::new();
        let mut qset = self.clone_empty();
        let extended_assignments = extend_assignment(
            assignment,
            &vars[index],
            model.universe[self.config.sorts[index]],
        );

        let mut new_prefix = prefix.clone();
        new_prefix.quantifiers.push(Quantifier::Forall);
        new_prefix.sorts.push(self.config.sorts[index]);
        new_prefix.counts.push(self.config.counts[index]);

        if quantifier.is_none() || quantifier == Some(Quantifier::Forall) {
            let new_perm_index = if prefix.quantifiers.last() == Some(&Quantifier::Exists) {
                index
            } else {
                perm_index
            };

            let mut self_ids: HashSet<usize> = qcnf_ids
                .iter()
                .cloned()
                .filter(|id| self.prefixes[id].quantifiers[index] == Quantifier::Forall)
                .collect();

            for asgn in &extended_assignments {
                if !self_ids.is_empty() {
                    let (new_modified, new_qset) = self.weaken_rec(
                        &self_ids,
                        model,
                        vars,
                        asgn,
                        index + 1,
                        new_perm_index,
                        &new_prefix,
                    );
                    for id in &new_modified {
                        modified.insert(*id);
                        self_ids.remove(id);
                    }
                    qset.merge(new_qset, new_perm_index);
                }

                let qset_ids: HashSet<usize> = qset.prefixes.keys().cloned().collect();
                if !qset_ids.is_empty() {
                    let (new_modified, new_qset) = qset.weaken_rec(
                        &qset_ids,
                        model,
                        vars,
                        asgn,
                        index + 1,
                        new_perm_index,
                        &new_prefix,
                    );
                    for id in &new_modified {
                        qset.remove(id)
                    }
                    qset.merge(new_qset, new_perm_index);
                }
            }

            if new_perm_index != perm_index {
                qset.minimize(perm_index);
            }
        }

        new_prefix.quantifiers[index] = Quantifier::Exists;

        if quantifier.is_none() && !modified.is_empty() {
            let mut alter_qset = self.clone_empty();
            for id in &modified {
                let mut alter_prefix = self.prefixes[id].clone();
                alter_prefix.quantifiers[index] = Quantifier::Exists;
                alter_qset.add(alter_prefix.clone(), self.bodies[id].clone());
            }

            let mut alter_ids: HashSet<usize> = alter_qset.prefixes.keys().cloned().collect();
            for asgn in &extended_assignments {
                if alter_ids.is_empty() {
                    break;
                }
                let (new_modified, new_trie) = alter_qset.weaken_rec(
                    &alter_ids,
                    model,
                    vars,
                    asgn,
                    index + 1,
                    perm_index,
                    &new_prefix,
                );
                qset.merge(new_trie, perm_index);
                alter_ids = new_modified;
            }

            for id in &alter_ids {
                alter_qset.remove(id);
            }

            qset.merge(alter_qset, perm_index)
        }

        if quantifier.is_none() || quantifier == Some(Quantifier::Exists) {
            let mut self_ids: HashSet<usize> = qcnf_ids
                .iter()
                .cloned()
                .filter(|id| self.prefixes[id].quantifiers[index] == Quantifier::Exists)
                .collect();
            for asgn in &extended_assignments {
                if self_ids.is_empty() {
                    break;
                }
                let (new_modified, new_qset) = self.weaken_rec(
                    &self_ids,
                    model,
                    vars,
                    asgn,
                    index + 1,
                    perm_index,
                    &new_prefix,
                );
                qset.merge(new_qset, perm_index);
                self_ids = new_modified;
            }
            modified.extend(self_ids);
        }

        (modified, qset)
    }

    pub fn weaken(&mut self, model: &Model) {
        let (modified, trie) = self.weaken_rec(
            &self.prefixes.keys().cloned().collect(),
            model,
            &self.config.vars(0),
            &Assignment::new(),
            0,
            0,
            &QuantifierPrefix {
                signature: self.config.signature.clone(),
                quantifiers: vec![],
                sorts: vec![],
                counts: vec![],
            },
        );

        for id in &modified {
            self.remove(id);
        }

        self.merge(trie, 0);
    }

    /// Return the quantified CNF formula associated with the given ID.
    pub fn qcnf(&self, id: &usize) -> Qcnf {
        Qcnf {
            prefix: Box::new(self.prefixes[id].clone()),
            body: Term::and(self.power_trie.sets_to_seqs[id].iter().map(|cl_id| {
                Term::or(
                    self.power_trie.seqs[cl_id]
                        .iter()
                        .map(|literal| match literal.1 {
                            true => self.atoms[literal.0].clone(),
                            false => Term::negate(self.atoms[literal.0].clone()),
                        }),
                )
            })),
        }
    }

    /// Return all quantified CNF formulas in the set.
    pub fn qcnfs(&self) -> Vec<Qcnf> {
        self.prefixes.keys().map(|id| self.qcnf(id)).collect_vec()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::*;

    #[test]
    fn test_trie() {
        let mut trie: Trie<usize> = Trie::new();

        trie.add(&[1, 2, 3], 0);
        trie.add(&[1, 2, 4], 1);
        trie.add(&[1, 4], 2);
        trie.add(&[1, 2], 3);
        trie.add(&[1, 3], 4);
        assert_eq!(trie.remove(&[1, 2]), 3);

        for (cl, id) in [vec![1, 2, 3], vec![1, 2, 4], vec![1, 4], vec![1, 3]]
            .iter()
            .zip([0, 1, 2, 4])
        {
            assert_eq!(trie.find(cl), Some(id));
        }

        for cl in [vec![1, 3, 4], vec![1], vec![1, 2], vec![4]] {
            assert_eq!(trie.find(&cl), None);
        }

        assert_eq!(trie.subsets(&[1, 2]), HashSet::from_iter([]));
        assert_eq!(trie.subsets(&[1, 2, 4]), HashSet::from_iter([1, 2]));
        assert_eq!(trie.subsets(&[1, 3, 4]), HashSet::from_iter([2, 4]));
    }

    #[test]
    fn test_power_trie() {
        let mut ptrie: PowerTrie<usize> = PowerTrie::new();

        assert_eq!(ptrie.add_seq(&[1, 2, 3]), 0);
        assert_eq!(ptrie.add_seq(&[1, 2, 4]), 1);
        assert_eq!(ptrie.add_seq(&[1, 4]), 2);
        assert_eq!(ptrie.add_seq(&[1, 2]), 3);
        assert_eq!(ptrie.add_seq(&[1, 3]), 4);

        assert_eq!(ptrie.add_set(&[0, 2]), 0);
        assert_eq!(ptrie.add_set(&[1, 4]), 1);
        assert_eq!(ptrie.add_set(&[3, 4]), 2);

        assert_eq!(
            &ptrie.seqs,
            &HashMap::from_iter([
                (0, vec![1, 2, 3]),
                (1, vec![1, 2, 4]),
                (2, vec![1, 4]),
                (3, vec![1, 2]),
                (4, vec![1, 3])
            ])
        );
        assert_eq!(
            &ptrie.seqs_to_sets,
            &HashMap::from_iter([
                (0, HashSet::from_iter([0])),
                (1, HashSet::from_iter([1])),
                (2, HashSet::from_iter([0])),
                (3, HashSet::from_iter([2])),
                (4, HashSet::from_iter([1, 2]))
            ])
        );
        assert_eq!(
            &ptrie.sets_to_seqs,
            &HashMap::from_iter([(0, vec![0, 2]), (1, vec![1, 4]), (2, vec![3, 4]),])
        );

        assert_eq!(
            ptrie.subsuming(&[&[1, 2, 3], &[1, 2, 4]], |_| true),
            HashSet::from_iter([0, 1, 2])
        );
        assert_eq!(
            ptrie.subsuming(&[&[1, 2, 3], &[1, 2, 4]], |&id| id != 2),
            HashSet::from_iter([0, 1])
        );
        assert_eq!(
            ptrie.subsuming(&[&[1, 3, 5], &[1, 2, 4]], |_| true),
            HashSet::from_iter([1, 2])
        );

        ptrie.remove_set(&1);
        assert_eq!(
            &ptrie.seqs,
            &HashMap::from_iter([
                (0, vec![1, 2, 3]),
                (2, vec![1, 4]),
                (3, vec![1, 2]),
                (4, vec![1, 3])
            ])
        );
        assert_eq!(
            &ptrie.seqs_to_sets,
            &HashMap::from_iter([
                (0, HashSet::from_iter([0])),
                (2, HashSet::from_iter([0])),
                (3, HashSet::from_iter([2])),
                (4, HashSet::from_iter([2]))
            ])
        );
        assert_eq!(
            &ptrie.sets_to_seqs,
            &HashMap::from_iter([(0, vec![0, 2]), (2, vec![3, 4]),])
        );
    }
}

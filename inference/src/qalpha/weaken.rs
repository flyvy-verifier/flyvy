// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Manage sets of quantified lemmas used in inference, and provide foundational algorithms
//! for handling them, e.g. checking subsumption, weakening, etc.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::sync::Arc;

use crate::hashmap::{HashMap, HashSet};

use fly::ouritertools::OurItertools;
use itertools::Itertools;
use rayon::prelude::*;

use crate::{
    basics::{OrderedTerms, QuantifierFreeConfig},
    qalpha::{
        atoms::{sat_literals, Literal, Literals},
        quant::QuantifierPrefix,
        subsume::{self, Clause, Element, Structure, SubsumptionMap},
    },
};
use fly::{
    semantics::{Assignment, Model},
    syntax::{Quantifier, Signature, Term},
};

pub type Domain<L> = (Arc<QuantifierPrefix>, Arc<L>, Arc<Literals>);

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
        .multi_cartesian_product_fixed()
        .map(|asgn| {
            let mut new_assignment = assignment.clone();
            for i in 0..vars.len() {
                new_assignment.insert(vars[i].clone(), asgn[i]);
            }

            new_assignment
        })
        .collect_vec()
}

/// Defines a general configuation for quantifier-free bodies of lemmas,
/// namely the attributes that do not depend on the atoms themselves.
pub trait LemmaQfConfig: Clone + Sync + Send + Debug {
    fn new(cfg: &QuantifierFreeConfig) -> Self;

    fn is_universal(&self) -> bool;

    fn as_universal(&self) -> Self;

    fn sub_spaces(&self) -> Vec<Self>;
}

/// Defines how quantifier-free bodies of lemmas are handled.
pub trait LemmaQf: Clone + Sync + Send + Debug {
    /// The type of the quantifier-free bodies which are weakened.
    type Body: subsume::Element;
    /// The basic configuration of the quantifier-free bodies.
    type Config: LemmaQfConfig;

    /// Create a new instance given the following configuration.
    fn new(
        cfg: Arc<Self::Config>,
        literals: Arc<Literals>,
        non_universal_vars: &HashSet<String>,
    ) -> Self;

    /// Return weakenings of the given [`Self::Body`] which satisfy the given cube.
    fn weaken<I>(&self, body: Self::Body, structure: &Structure, ignore: I) -> HashSet<Self::Body>
    where
        I: Fn(&Self::Body) -> bool + Sync;

    fn approx_space_size(&self) -> usize;

    fn contains(&self, other: &Self) -> bool;

    fn body_from_clause(clause: Clause) -> Self::Body;
}

/// Manages lemmas with a shared quantifier-prefix.
#[derive(Clone)]
pub struct PrefixLemmaSet<E, L>
where
    E: Element,
    L: LemmaQf<Body = E>,
{
    prefix: Arc<QuantifierPrefix>,
    lemma_qf: Arc<L>,
    literals: Arc<Literals>,
    bodies: Box<E::Map<usize>>,
    by_id: HashMap<usize, E>,
    next: usize,
}

#[derive(Clone)]
enum Ignore<'a, T> {
    Contained(&'a HashMap<usize, T>),
    NotContained(&'a HashMap<usize, T>),
}

impl<'a, T> Ignore<'a, T> {
    fn ignore(&self, i: &usize) -> bool {
        match self {
            Ignore::Contained(hm) => hm.contains_key(i),
            Ignore::NotContained(hm) => !hm.contains_key(i),
        }
    }
}

impl<E, L> PrefixLemmaSet<E, L>
where
    E: Element,
    L: LemmaQf<Body = E>,
{
    fn new(prefix: Arc<QuantifierPrefix>, lemma_qf: Arc<L>, literals: Arc<Literals>) -> Self {
        Self {
            prefix,
            lemma_qf,
            literals,
            bodies: Box::new(E::Map::new()),
            by_id: HashMap::default(),
            next: 0,
        }
    }

    fn init(&mut self) -> Vec<usize> {
        assert!(self.is_empty());
        vec![self.insert(E::bottom())]
    }

    pub fn is_empty(&self) -> bool {
        self.by_id.is_empty()
    }

    fn clone_empty(&self) -> Self {
        Self {
            prefix: self.prefix.clone(),
            lemma_qf: self.lemma_qf.clone(),
            literals: self.literals.clone(),
            bodies: Box::new(E::Map::new()),
            by_id: HashMap::default(),
            next: 0,
        }
    }

    fn insert(&mut self, body: E) -> usize {
        let id = self.next;
        self.next += 1;
        self.by_id.insert(id, body.clone());
        self.bodies.insert(body, id);
        id
    }

    fn remove(&mut self, id: &usize) -> E {
        let body = self.by_id.remove(id).unwrap();
        self.bodies.remove(&body);
        body
    }

    fn get_subsuming(&self, body: &E, perm_index: usize) -> HashSet<usize> {
        let mut subsuming: HashSet<usize> = HashSet::default();

        for perm in self.prefix.permutations(perm_index, Some(&body.ids())) {
            let perm_body = body.substitute(&perm);
            subsuming.extend(
                self.bodies
                    .get_subsuming(&perm_body)
                    .into_iter()
                    .map(|(_, id)| *id),
            );
        }

        subsuming
    }

    fn get_subsumed(&self, body: &E, perm_index: usize) -> HashSet<usize> {
        let mut subsumed: HashSet<usize> = HashSet::default();

        for perm in self.prefix.permutations(perm_index, Some(&body.ids())) {
            let perm_body = body.substitute(&perm);
            subsumed.extend(
                self.bodies
                    .get_subsumed(&perm_body)
                    .into_iter()
                    .map(|(_, id)| *id),
            );
        }

        subsumed
    }

    fn subsumes(&self, body: &E, perm_index: usize) -> bool {
        for perm in self.prefix.permutations(perm_index, Some(&body.ids())) {
            let perm_body = body.substitute(&perm);
            if self
                .bodies
                .get_subsuming(&perm_body)
                .into_iter()
                .next()
                .is_some()
            {
                return true;
            }
        }

        false
    }

    fn insert_minimized(&mut self, body: E, perm_index: usize) {
        if !Self::subsumes(self, &body, perm_index) {
            for subs_id in &self.get_subsumed(&body, perm_index) {
                self.remove(subs_id);
            }
            self.insert(body);
        }
    }

    fn unsat(
        &self,
        model: &Model,
        assignment: &Assignment,
        index: usize,
        ignore: &[Ignore<'_, HashSet<im::HashSet<Literal>>>],
    ) -> HashMap<usize, HashSet<im::HashSet<Literal>>> {
        if index >= self.prefix.len() {
            let structure = sat_literals(&self.literals, model, assignment);
            let im_structure: im::HashSet<_> = structure.iter().cloned().collect();

            return self
                .bodies
                .get_unsatisfied_by(&structure)
                .into_iter()
                .filter(|(_, i)| !ignore.iter().any(|ig| ig.ignore(i)))
                .map(|(_, i)| (*i, HashSet::from_iter([im_structure.clone()])))
                .collect();
        }

        if self.prefix.names[index].is_empty() {
            return self.unsat(model, assignment, index + 1, ignore);
        }

        let extended_assignments = extend_assignment(
            assignment,
            &self.prefix.names[index],
            model.universe[self.prefix.sorts[index]],
        );

        if self.prefix.quantifiers[index] == Quantifier::Forall {
            let mut unsat: HashMap<usize, HashSet<im::HashSet<Literal>>> = HashMap::default();
            for asgn in &extended_assignments {
                let mut new_ignore = ignore.to_vec();
                new_ignore.push(Ignore::Contained(&unsat));

                let new_unsat = self.unsat(model, asgn, index + 1, &new_ignore);
                for (i, structures) in new_unsat {
                    unsat.insert(i, structures);
                }
            }

            unsat
        } else {
            let mut unsat: Option<HashMap<usize, HashSet<im::HashSet<Literal>>>> = None;
            for asgn in &extended_assignments {
                let mut new_ignore = ignore.to_vec();
                if let Some(unsat_ref) = &unsat {
                    new_ignore.push(Ignore::NotContained(unsat_ref));
                }

                let mut new_unsat = self.unsat(model, asgn, index + 1, &new_ignore);
                if let Some(prev_unsat) = unsat {
                    for (i, structures) in &mut new_unsat {
                        structures.extend(prev_unsat[i].iter().cloned());
                    }
                }

                unsat = Some(new_unsat);
            }

            unsat.unwrap()
        }
    }

    /// Weakens and returns (IDs of removed lemmas, IDs of added lemmas).
    pub fn weaken(&mut self, model: &Model) -> (Vec<usize>, Vec<usize>) {
        let get_to_weaken =
            |set: &mut Self, unsat: HashMap<usize, HashSet<im::HashSet<Literal>>>| {
                unsat
                    .into_iter()
                    .flat_map(|(i, structures)| {
                        let body = set.remove(&i);
                        structures
                            .into_iter()
                            .map(move |st| (body.clone(), HashSet::from_iter(st)))
                    })
                    .collect_vec()
            };

        let mut unsat = self.unsat(model, &Assignment::new(), 0, &[]);
        let removed = unsat.keys().cloned().collect();
        let mut added = vec![];
        let mut to_weaken = get_to_weaken(self, unsat);
        while !to_weaken.is_empty() {
            let weakened: HashSet<E> = to_weaken
                .into_par_iter()
                .flat_map_iter(|(body, structure)| {
                    self.lemma_qf
                        .weaken(body, &structure, |b| self.subsumes(b, 0))
                })
                .collect();
            let mut weakened_min = self.clone_empty();
            for new_body in weakened {
                weakened_min.insert_minimized(new_body, 0);
            }

            unsat = weakened_min.unsat(model, &Assignment::new(), 0, &[]);
            to_weaken = get_to_weaken(&mut weakened_min, unsat);
            for (_, body) in weakened_min.by_id {
                added.push(self.insert(body));
            }
        }

        (removed, added)
    }
}

fn has_opposing_literals(clause: &<Clause as Element>::Base) -> bool {
    clause
        .iter()
        .any(|literal| clause.contains(&literal.negate()))
}

#[derive(Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct LemmaId(usize, usize);

/// Manages multiple instances of [`PrefixLemmaSet`] and allows weakening them all simultaneously.
pub struct WeakenLemmaSet<E, L>
where
    E: Element,
    L: LemmaQf<Body = E>,
{
    signature: Arc<Signature>,
    sets: Vec<PrefixLemmaSet<E, L>>,
    id_to_key: HashMap<LemmaId, LemmaKey>,
    key_to_term: BTreeMap<LemmaKey, Term>,
}
pub struct WeakenHypotheses<'a, E, L>
where
    E: Element,
    L: LemmaQf<Body = E>,
{
    set: &'a WeakenLemmaSet<E, L>,
    before: Option<LemmaKey>,
    try_first: Vec<LemmaKey>,
}

impl<'a, E, L> OrderedTerms for &WeakenHypotheses<'a, E, L>
where
    E: Element,
    L: LemmaQf<Body = E>,
{
    type Key = LemmaKey;

    fn first_unsat(self, model: &Model) -> Option<(Self::Key, Term)> {
        let unsat = self.set.unsat(model);

        if let Some(key) = self.try_first.iter().find(|key| unsat.contains(key)) {
            return Some((*key, self.set.key_to_term(key)));
        }

        if let Some(key) = unsat.first() {
            if !self.before.as_ref().is_some_and(|before| key >= before) {
                return Some((*key, self.set.key_to_term(key)));
            }
        }

        None
    }

    fn all_terms(self) -> BTreeMap<Self::Key, Term> {
        if let Some(before) = self.before {
            self.set
                .key_to_term
                .range(..before)
                .map(|(key, term)| (*key, term.clone()))
                .collect()
        } else {
            self.set.key_to_term.clone()
        }
    }
}

impl<E, L> WeakenLemmaSet<E, L>
where
    E: Element,
    L: LemmaQf<Body = E>,
{
    pub fn new(
        signature: Arc<Signature>,
        domains: Vec<(Arc<QuantifierPrefix>, Arc<L>, Arc<Literals>)>,
    ) -> Self {
        let sets: Vec<PrefixLemmaSet<E, L>> = domains
            .into_iter()
            .sorted_by_key(|(prefix, _, _)| prefix.clone())
            .map(|(prefix, lemma_qf, atoms)| PrefixLemmaSet::new(prefix, lemma_qf, atoms))
            .collect_vec();

        Self {
            signature,
            sets,
            id_to_key: HashMap::default(),
            key_to_term: BTreeMap::new(),
        }
    }

    pub fn hypotheses(
        &self,
        before: Option<LemmaKey>,
        try_first: Vec<LemmaKey>,
    ) -> WeakenHypotheses<'_, E, L> {
        WeakenHypotheses {
            set: self,
            before,
            try_first,
        }
    }

    pub fn init(&mut self) {
        let added = self
            .sets
            .iter_mut()
            .enumerate()
            .flat_map(|(i, set)| set.init().into_iter().map(move |j| LemmaId(i, j)))
            .collect_vec();

        for id in &added {
            if !self.redundant(id) {
                let key = self.lemma_key(*id);
                self.id_to_key.insert(*id, key);
                self.key_to_term.insert(key, self.id_to_term(id));
            }
        }
    }

    pub fn weaken(&mut self, model: &Model) -> (Vec<LemmaKey>, Vec<LemmaKey>) {
        let results: Vec<_> = self
            .sets
            .par_iter_mut()
            .enumerate()
            .map(|(i, set)| {
                let (removed, added) = set.weaken(model);
                (i, removed, added)
            })
            .collect();

        let mut removed = vec![];
        let mut added = vec![];
        for (i, r, a) in &results {
            removed.extend(r.iter().filter_map(|j| {
                let key = self.id_to_key.remove(&LemmaId(*i, *j));
                if let Some(k) = &key {
                    self.key_to_term.remove(k);
                }
                key
            }));
            added.extend(a.iter().filter_map(|j| {
                let id = LemmaId(*i, *j);
                if !self.redundant(&id) {
                    let key = self.lemma_key(id);
                    self.id_to_key.insert(id, key);
                    self.key_to_term.insert(key, self.id_to_term(&id));
                    Some(key)
                } else {
                    None
                }
            }));
        }

        (removed, added)
    }

    pub fn full_len(&self) -> usize {
        self.sets.iter().map(|set| set.by_id.len()).sum()
    }

    pub fn len(&self) -> usize {
        self.id_to_key.len()
    }

    fn redundant(&self, id: &LemmaId) -> bool {
        let prefix = self.sets[id.0]
            .prefix
            .restrict(self.sets[id.0].by_id[&id.1].ids());
        self.sets[..id.0].iter().any(|s| s.prefix.contains(&prefix))
    }

    pub fn first_subsuming(
        &self,
        prefix: &QuantifierPrefix,
        body: &E,
        before: Option<&LemmaKey>,
    ) -> Option<LemmaKey> {
        let res = self
            .sets
            .iter()
            .enumerate()
            .filter(|(_, set_i)| set_i.prefix.subsumes(prefix))
            .flat_map(|(i, set_i)| {
                set_i
                    .get_subsuming(body, 0)
                    .into_iter()
                    .filter_map(move |j| self.id_to_key.get(&LemmaId(i, j)).cloned())
            })
            .min();

        if res.is_some_and(|res_key| !before.is_some_and(|bound| &res_key >= bound)) {
            res
        } else {
            None
        }
    }

    pub fn get_implying(&self, key: &LemmaKey) -> Option<HashSet<LemmaKey>> {
        let id: LemmaId = key.into();
        let set = &self.sets[id.0];
        let body = &set.by_id[&id.1];
        let prefix = set.prefix.restrict(body.ids());

        if let Some(k) = self.first_subsuming(&prefix, body, Some(key)) {
            return Some(HashSet::from_iter([k]));
        }

        let clauses = body
            .to_cnf()
            .0
            .into_iter()
            .filter(|cl| !has_opposing_literals(&cl.to_base(true)))
            .collect_vec();
        let multi_clause = clauses.len() > 1;

        if multi_clause {
            // Universal multi-clause formulas are always redundant.
            if prefix.existentials() == 0 {
                return Some(HashSet::default());
            }

            let universal_prefix = prefix.as_universal();
            let subsuming = clauses
                .iter()
                .map(|clause| {
                    let body = L::body_from_clause(clause.clone());
                    self.first_subsuming(&universal_prefix.restrict(body.ids()), &body, Some(key))
                })
                .collect_vec();
            let not_subsumed = subsuming
                .iter()
                .enumerate()
                .filter_map(|(i, s)| match s {
                    None => Some(i),
                    Some(_) => None,
                })
                .collect_vec();

            let filtered_subsuming = subsuming.into_iter().flatten();
            match not_subsumed.len() {
                0 => Some(filtered_subsuming.collect()),
                1 => {
                    let reduced_body = L::body_from_clause(clauses[not_subsumed[0]].clone());
                    let reduced_prefix = prefix.restrict(reduced_body.ids());
                    self.first_subsuming(&reduced_prefix, &reduced_body, Some(key))
                        .map(|s| filtered_subsuming.chain([s]).collect())
                }
                _ => None,
            }
        } else {
            None
        }
    }

    fn lemma_key(&self, id: LemmaId) -> LemmaKey {
        let set = &self.sets[id.0];
        let body = &set.by_id[&id.1];
        LemmaKey::key(&set.prefix.restrict(body.ids()), body, id)
    }

    pub fn keys(&self) -> impl Iterator<Item = &LemmaKey> + '_ {
        self.key_to_term.keys()
    }

    pub fn unsat(&self, model: &Model) -> BTreeSet<LemmaKey> {
        self.sets
            .iter()
            .enumerate()
            .flat_map(|(i, set)| {
                set.unsat(model, &Assignment::new(), 0, &[])
                    .keys()
                    .filter_map(move |j| self.id_to_key.get(&LemmaId(i, *j)).cloned())
                    .collect_vec()
            })
            .collect()
    }

    pub fn to_terms_keys(&self) -> impl Iterator<Item = (Term, LemmaKey)> + '_ {
        self.key_to_term
            .iter()
            .map(|(key, term)| (term.clone(), *key))
    }

    pub fn to_terms(&self) -> Vec<Term> {
        self.to_terms_keys().map(|(t, _)| t).collect()
    }

    pub fn id_to_term(&self, id: &LemmaId) -> Term {
        let set = &self.sets[id.0];
        let body = &set.by_id[&id.1];
        set.prefix
            .restrict(body.ids())
            .quantify(&self.signature, body.to_term(true))
    }

    pub fn key_to_term(&self, key: &LemmaKey) -> Term {
        self.key_to_term[key].clone()
    }

    pub fn key_to_idx(&self) -> HashMap<LemmaKey, usize> {
        self.key_to_term
            .keys()
            .enumerate()
            .map(|(i, key)| (*key, i))
            .collect()
    }

    pub fn remove_unsat(&mut self, model: &Model) -> Vec<LemmaKey> {
        let removed_ids: Vec<_> = self
            .sets
            .par_iter_mut()
            .enumerate()
            .flat_map_iter(|(i, set)| {
                set.unsat(model, &Assignment::new(), 0, &[])
                    .iter()
                    .map(|(j, _)| {
                        set.remove(j);
                        LemmaId(i, *j)
                    })
                    .collect_vec()
            })
            .collect();

        removed_ids
            .iter()
            .filter_map(|id| {
                let key = self.id_to_key.remove(id);
                if let Some(k) = &key {
                    self.key_to_term.remove(k);
                }
                key
            })
            .collect()
    }
}

#[derive(Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct LemmaKey(usize, usize, usize, LemmaId);

impl LemmaKey {
    fn key<E: Element>(prefix: &QuantifierPrefix, body: &E, id: LemmaId) -> Self {
        Self(prefix.existentials(), body.size(), prefix.num_vars(), id)
    }
}

impl From<&LemmaKey> for LemmaId {
    fn from(value: &LemmaKey) -> Self {
        value.3
    }
}

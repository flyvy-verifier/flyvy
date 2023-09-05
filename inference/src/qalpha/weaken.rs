// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Manage sets of quantified lemmas used in inference, and provide foundational algorithms
//! for handling them, e.g. checking subsumption, weakening, etc.

use std::fmt::Debug;
use std::sync::Arc;

use crate::hashmap::{HashMap, HashSet};
use crate::parallel::DequeWorker;

use fly::ouritertools::OurItertools;
use itertools::FoldWhile::{Continue, Done};
use itertools::Itertools;

use crate::{
    basics::InferenceConfig,
    qalpha::{
        atoms::{sat_literals, Literals},
        quant::{QuantifierConfig, QuantifierPrefix},
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

/// [`LemmaQf`] defines how quantifier-free bodies of lemmas are handled.
pub trait LemmaQf: Clone + Sync + Send + Debug {
    /// The type of the quantifier-free bodies which are weakened.
    type Body: subsume::Element;

    /// Create a new instance given the following configuration.
    fn new(
        cfg: &InferenceConfig,
        literals: Arc<Literals>,
        non_universal_vars: &HashSet<String>,
    ) -> Self;

    /// Return weakenings of the given [`Self::Body`] which satisfy the given cube.
    fn weaken<I>(&self, body: Self::Body, structure: &Structure, ignore: I) -> Vec<Self::Body>
    where
        I: Fn(&Self::Body) -> bool + Sync;

    fn approx_space_size(&self) -> usize;

    fn sub_spaces(&self) -> Vec<Self>;

    fn contains(&self, other: &Self) -> bool;

    fn body_from_clause(clause: Clause) -> Self::Body;
}

/// Specifies that all lemmas subsumed by the given set and permutations over variables should be ignored.
#[derive(Clone)]
struct IgnoreSubsumed<'a, E, L>
where
    E: Element,
    L: LemmaQf<Body = E>,
{
    set: &'a PrefixLemmaSet<E, L>,
    perm_index: usize,
}

impl<'a, E, L> IgnoreSubsumed<'a, E, L>
where
    E: Element,
    L: LemmaQf<Body = E>,
{
    fn subsumes(&self, e: &E) -> bool {
        self.set.subsumes(e, self.perm_index)
    }
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

    fn init(&mut self) {
        assert!(self.is_empty());
        self.insert(E::bottom());
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

    fn insert(&mut self, body: E) {
        self.by_id.insert(self.next, body.clone());
        self.bodies.insert(body, self.next);
        self.next += 1;
    }

    pub fn remove(&mut self, body: &E) {
        let id = self.bodies.remove(body);
        self.by_id.remove(&id).unwrap();
    }

    fn remove_by_id(&mut self, id: &usize) -> E {
        let body = self.by_id.remove(id).unwrap();
        self.bodies.remove(&body);

        body
    }

    #[allow(dead_code)]
    fn get_subsuming(&self, body: &E, perm_index: usize) -> HashSet<E> {
        let mut subsuming: HashSet<E> = HashSet::default();

        for perm in self.prefix.permutations(perm_index, Some(&body.ids())) {
            let perm_body = body.substitute(&perm);
            subsuming.extend(
                self.bodies
                    .get_subsuming(&perm_body)
                    .into_iter()
                    .map(|(o, _)| o),
            );
        }

        subsuming
    }

    fn get_subsumed(&self, body: &E, perm_index: usize) -> HashSet<E> {
        let mut subsumed: HashSet<E> = HashSet::default();

        for perm in self.prefix.permutations(perm_index, Some(&body.ids())) {
            let perm_body = body.substitute(&perm);
            subsumed.extend(
                self.bodies
                    .get_subsumed(&perm_body)
                    .into_iter()
                    .map(|(o, _)| o),
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
            for subs_body in self.get_subsumed(&body, perm_index) {
                self.remove(&subs_body);
            }
            self.insert(body);
        }
    }

    fn unsat(&self, model: &Model, assignment: &Assignment, index: usize) -> HashSet<usize> {
        if index >= self.prefix.len() {
            let structure = sat_literals(&self.literals, model, assignment);

            return self
                .bodies
                .get_unsatisfied_by(&structure)
                .into_iter()
                .map(|(_, i)| *i)
                .collect();
        }

        if self.prefix.names[index].is_empty() {
            return self.unsat(model, assignment, index + 1);
        }

        let extended_assignments = extend_assignment(
            assignment,
            &self.prefix.names[index],
            model.universe[self.prefix.sorts[index]],
        );

        if self.prefix.quantifiers[index] == Quantifier::Forall {
            extended_assignments
                .iter()
                .flat_map(|asgn| self.unsat(model, asgn, index + 1))
                .collect()
        } else {
            extended_assignments
                .iter()
                .map(|asgn| self.unsat(model, asgn, index + 1))
                .fold_while(None, |res, new_hs| match res {
                    None => Continue(Some(new_hs)),
                    Some(hs) => {
                        let intersected: HashSet<_> = hs.intersection(&new_hs).cloned().collect();
                        if intersected.is_empty() {
                            Done(Some(intersected))
                        } else {
                            Continue(Some(intersected))
                        }
                    }
                })
                .into_inner()
                .unwrap()
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn weaken_add(
        &mut self,
        mut to_weaken: Self,
        model: &Model,
        assignment: &Assignment,
        index: usize,
        perm_index: usize,
        prev_exists: bool,
        ignore: &Vec<IgnoreSubsumed<'_, E, L>>,
    ) {
        if to_weaken.is_empty() {
            return;
        }

        if index >= self.prefix.len() {
            let mut new_ignore = ignore.clone();
            new_ignore.push(IgnoreSubsumed {
                set: self,
                perm_index,
            });

            let structure = sat_literals(&self.literals, model, assignment);

            let weakenings = DequeWorker::run(to_weaken.bodies(), |body| {
                (
                    self.lemma_qf.weaken(body.clone(), &structure, |b| {
                        new_ignore.iter().any(|ig| ig.subsumes(b))
                    }),
                    vec![],
                    vec![],
                    false,
                )
            });

            let mut weakened_min = to_weaken.clone_empty();
            for new_body in weakenings.into_iter().filter_map(|(_, w)| w).flatten() {
                weakened_min.insert_minimized(new_body, perm_index);
            }

            if prev_exists && !self.is_empty() {
                for new_body in weakened_min.by_id.values() {
                    for subs_body in self.get_subsumed(new_body, perm_index) {
                        self.remove(&subs_body);
                    }
                }
            }

            for new_body in weakened_min.by_id.values() {
                self.insert(new_body.clone());
            }

            return;
        }

        // Skip sorts with no quantified variables
        if self.prefix.names[index].is_empty() {
            return self.weaken_add(
                to_weaken,
                model,
                assignment,
                index + 1,
                perm_index,
                prev_exists,
                ignore,
            );
        }

        let extended_assignments = extend_assignment(
            assignment,
            &self.prefix.names[index],
            model.universe[self.prefix.sorts[index]],
        );

        if self.prefix.quantifiers[index] == Quantifier::Forall {
            let mut new_ignore = ignore.clone();
            new_ignore.push(IgnoreSubsumed {
                set: self,
                perm_index,
            });

            let new_perm_index = if prev_exists { index } else { perm_index };
            for new_asgn in &extended_assignments {
                let unsat = to_weaken.unsat(model, new_asgn, index + 1);
                let mut new_to_weaken = to_weaken.clone_empty();
                for i in &unsat {
                    new_to_weaken.insert(to_weaken.remove_by_id(i));
                }
                to_weaken.weaken_add(
                    new_to_weaken,
                    model,
                    new_asgn,
                    index + 1,
                    new_perm_index,
                    false,
                    &new_ignore,
                );
            }

            if prev_exists {
                let mut minimized = to_weaken.clone_empty();
                for (body, _) in to_weaken.bodies.items() {
                    minimized.insert_minimized(body, perm_index);
                }
                to_weaken = minimized;

                for body in to_weaken.by_id.values() {
                    for subs_body in self.get_subsumed(body, perm_index) {
                        self.remove(&subs_body);
                    }
                }
            }

            for body in to_weaken.by_id.values() {
                self.insert(body.clone());
            }
        } else {
            for new_asgn in &extended_assignments {
                self.weaken_add(
                    to_weaken.clone(),
                    model,
                    new_asgn,
                    index + 1,
                    perm_index,
                    true,
                    ignore,
                );
            }
        }
    }

    pub fn weaken(&mut self, model: &Model) -> bool {
        let unsat = self.unsat(model, &Assignment::new(), 0);

        if unsat.is_empty() {
            return false;
        }

        let mut to_weaken = self.clone_empty();
        for i in &unsat {
            to_weaken.insert(self.remove_by_id(i));
        }

        self.weaken_add(to_weaken, model, &Assignment::new(), 0, 0, false, &vec![]);

        true
    }

    fn bodies(&self) -> Vec<E> {
        self.by_id.values().cloned().collect_vec()
    }

    pub fn as_iter(&self) -> impl Iterator<Item = (Arc<QuantifierPrefix>, E)> + '_ {
        self.by_id
            .values()
            .map(|body| (Arc::new(self.prefix.restrict(body.ids())), body.clone()))
    }
}

/// Manages multiple instances of [`PrefixLemmaSet`] and allows weakening them all simultaneously.
pub struct WeakenLemmaSet<E, L>
where
    E: Element,
    L: LemmaQf<Body = E>,
{
    sets: Vec<PrefixLemmaSet<E, L>>,
}

impl<E, L> WeakenLemmaSet<E, L>
where
    E: Element,
    L: LemmaQf<Body = E>,
{
    pub fn new(domains: Vec<(Arc<QuantifierPrefix>, Arc<L>, Arc<Literals>)>) -> Self {
        let sets: Vec<PrefixLemmaSet<E, L>> = domains
            .into_iter()
            .map(|(prefix, lemma_qf, atoms)| PrefixLemmaSet::new(prefix, lemma_qf, atoms))
            .collect_vec();

        Self { sets }
    }

    pub fn init(&mut self) {
        for set in &mut self.sets {
            set.init();
        }
    }

    pub fn weaken(&mut self, model: &Model) -> bool {
        std::thread::scope(|s| {
            self.sets
                .iter_mut()
                .map(|set| s.spawn(|| set.weaken(model)))
                .collect_vec()
                .into_iter()
                .any(|h| h.join().unwrap())
        })
    }

    pub fn len(&self) -> usize {
        self.sets.iter().map(|set| set.by_id.len()).sum()
    }

    pub fn as_iter(&self) -> impl Iterator<Item = (Arc<QuantifierPrefix>, E)> + '_ {
        self.sets.iter().flat_map(|set| set.as_iter())
    }

    pub fn unsat(&self, model: &Model) -> bool {
        self.sets
            .iter()
            .any(|set| !set.unsat(model, &Assignment::new(), 0).is_empty())
    }
}

/// Manages lemmas of several quantifier prefixes together, which all share some [`QuantifierConfig`].
#[derive(Clone)]
pub struct LemmaSet<E: Element> {
    signature: Arc<Signature>,
    pub config: Arc<QuantifierConfig>,
    to_prefixes: HashMap<usize, Arc<QuantifierPrefix>>,
    to_bodies: HashMap<usize, E>,
    bodies: E::Map<HashSet<usize>>,
    next: usize,
}

fn lemma_key<E: Element>(prefix: &QuantifierPrefix, body: &E) -> impl Ord {
    (prefix.existentials(), body.size(), prefix.num_vars())
}

impl<E: Element> LemmaSet<E> {
    pub fn new(signature: Arc<Signature>, config: Arc<QuantifierConfig>) -> Self {
        Self {
            signature,
            config,
            to_prefixes: HashMap::default(),
            to_bodies: HashMap::default(),
            bodies: E::Map::new(),
            next: 0,
        }
    }

    pub fn init(&mut self) {
        self.insert(
            Arc::new(self.config.as_universal().restrict(HashSet::default())),
            E::bottom(),
        );
    }

    pub fn len(&self) -> usize {
        self.to_prefixes.len()
    }

    pub fn id_to_lemma(&self, id: &usize) -> (Arc<QuantifierPrefix>, E) {
        (self.to_prefixes[id].clone(), self.to_bodies[id].clone())
    }

    pub fn to_terms_ids(&self) -> impl Iterator<Item = (usize, Term)> + '_ {
        self.as_iter()
            .map(|((prefix, body), id)| (id, prefix.quantify(&self.signature, body.to_term(true))))
    }

    pub fn to_terms(&self) -> Vec<Term> {
        self.to_terms_ids().map(|(_, t)| t).collect()
    }

    pub fn as_iter(&self) -> impl Iterator<Item = ((Arc<QuantifierPrefix>, E), usize)> {
        self.to_prefixes
            .keys()
            .copied()
            .map(|id| (self.id_to_lemma(&id), id))
            .sorted_by_key(|((prefix, body), id)| (lemma_key(prefix, body), *id))
    }

    pub fn as_vec(&self) -> Vec<((Arc<QuantifierPrefix>, E), usize)> {
        self.as_iter().collect()
    }

    pub fn subsumes(&self, prefix: &QuantifierPrefix, body: &E) -> bool {
        for perm in self.config.permutations(0, Some(&body.ids())) {
            let perm_body = body.substitute(&perm);

            if self
                .bodies
                .get_subsuming(&perm_body)
                .into_iter()
                .flat_map(|(_, is)| is)
                .any(|i| self.to_prefixes[i].subsumes(prefix))
            {
                return true;
            }
        }

        false
    }

    pub fn get_subsumed(&self, prefix: &QuantifierPrefix, body: &E) -> HashSet<usize> {
        let mut subsumed: HashSet<usize> = HashSet::default();

        for perm in self.config.permutations(0, Some(&body.ids())) {
            let perm_body = body.substitute(&perm);
            subsumed.extend(
                self.bodies
                    .get_subsumed(&perm_body)
                    .into_iter()
                    .flat_map(|(_, is)| is)
                    .copied()
                    .filter(|i| prefix.subsumes(&self.to_prefixes[i])),
            );
        }

        subsumed
    }

    pub fn insert(&mut self, prefix: Arc<QuantifierPrefix>, body: E) -> usize {
        let id = self.next;
        self.next += 1;

        self.to_prefixes.insert(id, prefix);
        self.to_bodies.insert(id, body.clone());
        if let Some(hs) = self.bodies.get_mut(&body) {
            hs.insert(id);
        } else {
            self.bodies.insert(body.clone(), HashSet::from_iter([id]));
        }

        id
    }

    pub fn insert_minimized(&mut self, prefix: Arc<QuantifierPrefix>, body: E) -> Option<usize> {
        if !LemmaSet::subsumes(self, &prefix, &body) {
            for id in &self.get_subsumed(&prefix, &body) {
                self.remove(id);
            }

            Some(self.insert(prefix, body))
        } else {
            None
        }
    }

    pub fn remove(&mut self, id: &usize) -> (Arc<QuantifierPrefix>, E) {
        let prefix = self.to_prefixes.remove(id).unwrap();
        let body = self.to_bodies.remove(id).unwrap();
        let hs = self.bodies.get_mut(&body).unwrap();
        hs.remove(id);
        if hs.is_empty() {
            self.bodies.remove(&body);
        }

        (prefix, body)
    }
}

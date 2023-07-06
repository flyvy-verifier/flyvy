// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Manage sets of quantified lemmas used in inference, and provide foundational algorithms
//! for handling them, e.g. checking subsumption, weakening, etc.

use std::fmt::Debug;
use std::sync::Arc;

use crate::hashmap::{HashMap, HashSet};

use itertools::FoldWhile::{Continue, Done};
use itertools::Itertools;

use crate::{
    atoms::{Literal, RestrictedAtoms},
    basics::InferenceConfig,
    quant::{QuantifierConfig, QuantifierPrefix},
    subsume::{OrderSubsumption, SubsumptionMap},
};
use fly::term::subst::Substitution;
use fly::{
    semantics::{Assignment, Model},
    syntax::{Quantifier, Term},
};

use rayon::prelude::*;

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

/// [`LemmaQf`] defines how quantifier-free bodies of lemmas are handled.
pub trait LemmaQf: Clone + Sync + Send {
    /// The type of the quantifier-free bodies which are weakened.
    type Base: Clone + Debug;

    /// Convert a given clause to a quantifier-free body.
    fn base_from_clause(&self, clause: &[Literal]) -> Self::Base;

    /// Perform a substitution.
    fn substitute(&self, base: &Self::Base, substitution: &Substitution) -> Option<Self::Base>;

    /// Get all [`Term::Id`]'s in the body.
    fn ids(&self, base: &Self::Base) -> HashSet<String>;

    /// Convert body to a [`Term`].
    fn base_to_term(&self, base: &Self::Base) -> Term;

    /// Create a new instance given the following configuration.
    fn new(
        cfg: &InferenceConfig,
        atoms: Arc<RestrictedAtoms>,
        non_universal_vars: HashSet<String>,
    ) -> Self;

    /// Return the strongest instances of the associated [`Self::Base`]
    fn strongest(&self) -> Vec<Self::Base>;

    /// Return weakenings of the given [`Self::Base`] which satisfy the given cube.
    fn weaken<I>(&self, base: Self::Base, cube: &[Literal], ignore: I) -> Vec<Self::Base>
    where
        I: Fn(&Self::Base) -> bool;

    fn approx_space_size(&self) -> usize;

    fn sub_spaces(&self) -> Vec<Self>;

    fn contains(&self, other: &Self) -> bool;
}

/// Specifies that all lemmas subsumed by the given set and permutations over variables should be ignored.
#[derive(Clone)]
struct IgnoreSubsumed<'a, O, L, B>
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
{
    set: &'a PrefixLemmaSet<O, L, B>,
    perm_index: usize,
}

impl<'a, O, L, B> IgnoreSubsumed<'a, O, L, B>
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
{
    fn subsumes(&self, o: &O) -> bool {
        self.set.subsumes(o, self.perm_index)
    }
}

/// Manages lemmas with a shared quantifier-prefix.
#[derive(Clone)]
pub struct PrefixLemmaSet<O, L, B>
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
{
    prefix: Arc<QuantifierPrefix>,
    lemma_qf: Arc<L>,
    atoms: Arc<RestrictedAtoms>,
    bodies: Box<O::Map<usize>>,
    by_id: HashMap<usize, O>,
    next: usize,
}

impl<O, L, B> PrefixLemmaSet<O, L, B>
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
{
    fn new(prefix: Arc<QuantifierPrefix>, lemma_qf: Arc<L>, atoms: Arc<RestrictedAtoms>) -> Self {
        Self {
            prefix,
            lemma_qf,
            atoms,
            bodies: Box::new(O::Map::new()),
            by_id: HashMap::default(),
            next: 0,
        }
    }

    fn init(&mut self) {
        assert!(self.is_empty());
        for base in self.lemma_qf.strongest() {
            self.insert(O::from_base(base));
        }
    }

    pub fn is_empty(&self) -> bool {
        self.by_id.is_empty()
    }

    fn clone_empty(&self) -> Self {
        Self {
            prefix: self.prefix.clone(),
            lemma_qf: self.lemma_qf.clone(),
            atoms: self.atoms.clone(),
            bodies: Box::new(O::Map::new()),
            by_id: HashMap::default(),
            next: 0,
        }
    }

    fn insert(&mut self, body: O) {
        self.by_id.insert(self.next, body.clone());
        self.bodies.insert(body, self.next);
        self.next += 1;
    }

    pub fn remove(&mut self, body: &O) {
        let id = self.bodies.remove(body);
        self.by_id.remove(&id).unwrap();
    }

    fn remove_by_id(&mut self, id: &usize) -> O {
        let body = self.by_id.remove(id).unwrap();
        self.bodies.remove(&body);

        body
    }

    #[allow(dead_code)]
    fn get_subsuming(&self, body: &O, perm_index: usize) -> HashSet<O> {
        let mut subsuming: HashSet<O> = HashSet::default();
        let base = body.to_base();

        for perm in self
            .prefix
            .permutations(perm_index, Some(&self.lemma_qf.ids(&base)))
        {
            let perm_base = self.lemma_qf.substitute(&base, &perm);
            let perm_body = O::from_base(perm_base.expect("Substitution couldn't be performed."));
            subsuming.extend(
                self.bodies
                    .get_subsuming(&perm_body)
                    .into_iter()
                    .map(|(o, _)| o),
            );
        }

        subsuming
    }

    fn get_subsumed(&self, body: &O, perm_index: usize) -> HashSet<O> {
        let mut subsumed: HashSet<O> = HashSet::default();
        let base = body.to_base();

        for perm in self
            .prefix
            .permutations(perm_index, Some(&self.lemma_qf.ids(&base)))
        {
            let perm_base = self.lemma_qf.substitute(&base, &perm);
            let perm_body = O::from_base(perm_base.expect("Substitution couldn't be performed."));
            subsumed.extend(
                self.bodies
                    .get_subsumed(&perm_body)
                    .into_iter()
                    .map(|(o, _)| o),
            );
        }

        subsumed
    }

    fn subsumes(&self, body: &O, perm_index: usize) -> bool {
        let base = body.to_base();

        for perm in self
            .prefix
            .permutations(perm_index, Some(&self.lemma_qf.ids(&base)))
        {
            let perm_base = self.lemma_qf.substitute(&base, &perm);
            let perm_body = O::from_base(perm_base.expect("Substitution couldn't be performed."));
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

    fn insert_minimized(&mut self, body: O, perm_index: usize) {
        if !Self::subsumes(self, &body, perm_index) {
            for subs_body in self.get_subsumed(&body, perm_index) {
                self.remove(&subs_body);
            }
            self.insert(body);
        }
    }

    fn unsat(&self, model: &Model, assignment: &Assignment, index: usize) -> HashSet<usize> {
        if index >= self.prefix.len() {
            let neg_cube = self.atoms.neg_cube(model, assignment);

            let neg_cube_as_o = O::from_base(self.lemma_qf.base_from_clause(&neg_cube));

            return self
                .bodies
                .get_subsuming(&neg_cube_as_o)
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
        ignore: &Vec<IgnoreSubsumed<'_, O, L, B>>,
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

            let cube = self.atoms.cube(model, assignment);
            let weakened: HashSet<O> = to_weaken
                .bases()
                .into_par_iter()
                .flat_map_iter(|base| {
                    self.lemma_qf.weaken(base, &cube, |b| {
                        let body: O = O::from_base(b.clone());
                        new_ignore.iter().any(|ig| ig.subsumes(&body))
                    })
                })
                .map(|new_base| O::from_base(new_base))
                .collect();

            let mut weakened_min = to_weaken.clone_empty();
            for new_body in weakened {
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
                for body in to_weaken.bodies.keys() {
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

    pub fn weaken_cti(&mut self, prestate: &Model, poststate: &Model) -> bool {
        let non_inductive: HashSet<usize> = self
            .unsat(poststate, &Assignment::new(), 0)
            .difference(&self.unsat(prestate, &Assignment::new(), 0))
            .cloned()
            .collect();

        if non_inductive.is_empty() {
            return false;
        }

        let mut to_weaken = self.clone_empty();
        for i in &non_inductive {
            to_weaken.insert(self.remove_by_id(i));
        }

        self.weaken_add(
            to_weaken,
            poststate,
            &Assignment::new(),
            0,
            0,
            false,
            &vec![],
        );

        true
    }

    fn bases(&self) -> Vec<B> {
        self.by_id.values().map(|o| o.to_base()).collect_vec()
    }

    pub fn as_iter(&self) -> impl Iterator<Item = (Arc<QuantifierPrefix>, &O)> {
        self.by_id.values().map(|body| (self.prefix.clone(), body))
    }
}

/// Manages multiple instances of [`PrefixLemmaSet`] and allows weakening them all simultaneously.
pub struct WeakenLemmaSet<O, L, B>
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
{
    config: Arc<QuantifierConfig>,
    infer_cfg: Arc<InferenceConfig>,
    atoms: Arc<RestrictedAtoms>,
    sets: Vec<PrefixLemmaSet<O, L, B>>,
}

impl<O, L, B> WeakenLemmaSet<O, L, B>
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
{
    pub fn new(
        config: Arc<QuantifierConfig>,
        infer_cfg: Arc<InferenceConfig>,
        atoms: Arc<RestrictedAtoms>,
        domains: Vec<(Arc<QuantifierPrefix>, Arc<L>, Arc<RestrictedAtoms>)>,
    ) -> Self {
        let sets: Vec<PrefixLemmaSet<O, L, B>> = domains
            .into_iter()
            .map(|(prefix, lemma_qf, atoms)| PrefixLemmaSet::new(prefix, lemma_qf, atoms))
            .collect_vec();

        Self {
            config,
            infer_cfg,
            atoms,
            sets,
        }
    }

    pub fn init(&mut self) {
        for set in &mut self.sets {
            set.init();
        }
    }

    pub fn weaken(&mut self, model: &Model) -> bool {
        let weakened: Vec<bool> = self
            .sets
            .par_iter_mut()
            .map(|set| set.weaken(model))
            .collect();

        weakened.iter().any(|b| *b)
    }

    pub fn weaken_cti(&mut self, prestate: &Model, poststate: &Model) -> bool {
        let weakened: Vec<bool> = self
            .sets
            .par_iter_mut()
            .map(|set| set.weaken_cti(prestate, poststate))
            .collect();

        weakened.iter().any(|b| *b)
    }

    pub fn len(&self) -> usize {
        self.sets.iter().map(|set| set.by_id.len()).sum()
    }

    pub fn as_iter(&self) -> impl Iterator<Item = (Arc<QuantifierPrefix>, &O)> {
        self.sets
            .iter()
            .sorted_by_key(|set| set.prefix.existentials())
            .flat_map(|set| set.as_iter())
    }

    pub fn as_vec(&self) -> Vec<(Arc<QuantifierPrefix>, &O)> {
        self.as_iter().collect_vec()
    }

    pub fn unsat(&self, model: &Model) -> bool {
        self.sets
            .par_iter()
            .any(|set| !set.unsat(model, &Assignment::new(), 0).is_empty())
    }

    pub fn minimized(&self) -> LemmaSet<O, L, B> {
        let mut lemmas: LemmaSet<O, L, B> =
            LemmaSet::new(self.config.clone(), &self.infer_cfg, self.atoms.clone());
        for (prefix, body) in self.as_vec() {
            lemmas.insert_minimized(prefix.clone(), body.clone());
        }

        lemmas
    }

    pub fn contains(&self, prefix: &QuantifierPrefix, body: &O) -> bool {
        self.sets
            .iter()
            .any(|set| set.prefix.as_ref() == prefix && set.bodies.get(body).is_some())
    }
}

/// Manages lemmas of several quantifier prefixes together, which all share some [`QuantifierConfig`].
#[derive(Clone)]
pub struct LemmaSet<O, L, B>
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug,
{
    config: Arc<QuantifierConfig>,
    pub lemma_qf: Arc<L>,
    pub to_prefixes: HashMap<usize, Arc<QuantifierPrefix>>,
    pub to_bodies: HashMap<usize, O>,
    bodies: O::Map<HashSet<usize>>,
    next: usize,
}

impl<O, L, B> LemmaSet<O, L, B>
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug,
{
    pub fn new(
        config: Arc<QuantifierConfig>,
        infer_cfg: &InferenceConfig,
        atoms: Arc<RestrictedAtoms>,
    ) -> Self {
        let non_universal_vars = config.non_universal_vars();

        Self {
            config,
            lemma_qf: Arc::new(L::new(infer_cfg, atoms, non_universal_vars)),
            to_prefixes: HashMap::default(),
            to_bodies: HashMap::default(),
            bodies: O::Map::new(),
            next: 0,
        }
    }

    pub fn clone_empty(&self) -> Self {
        Self {
            config: self.config.clone(),
            lemma_qf: self.lemma_qf.clone(),
            to_prefixes: HashMap::default(),
            to_bodies: HashMap::default(),
            bodies: O::Map::new(),
            next: 0,
        }
    }

    pub fn len(&self) -> usize {
        self.to_prefixes.len()
    }

    pub fn to_terms_ids(&self) -> Vec<(usize, Term)> {
        self.to_prefixes
            .iter()
            .sorted_by_key(|(_, prefix)| prefix.existentials())
            .map(|(id, prefix)| {
                (
                    *id,
                    prefix.quantify(self.lemma_qf.base_to_term(&self.to_bodies[id].to_base())),
                )
            })
            .collect_vec()
    }

    pub fn to_terms(&self) -> Vec<Term> {
        self.to_terms_ids().into_iter().map(|(_, t)| t).collect()
    }

    pub fn as_vec(&self) -> Vec<(Arc<QuantifierPrefix>, O)> {
        self.to_prefixes
            .iter()
            .map(|(id, prefix)| (prefix.clone(), self.to_bodies[id].clone()))
            .collect_vec()
    }

    pub fn subsumes(&self, prefix: &QuantifierPrefix, body: &O) -> bool {
        let base = body.to_base();

        for perm in self.config.permutations(0, Some(&self.lemma_qf.ids(&base))) {
            let perm_body = O::from_base(self.lemma_qf.substitute(&base, &perm).unwrap());

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

    pub fn get_subsuming(&self, prefix: &QuantifierPrefix, body: &O) -> HashSet<usize> {
        let mut subsuming: HashSet<usize> = HashSet::default();
        let base = body.to_base();

        for perm in self.config.permutations(0, Some(&self.lemma_qf.ids(&base))) {
            let perm_body = O::from_base(self.lemma_qf.substitute(&base, &perm).unwrap());
            subsuming.extend(
                self.bodies
                    .get_subsuming(&perm_body)
                    .into_iter()
                    .flat_map(|(_, is)| is)
                    .copied()
                    .filter(|i| self.to_prefixes[i].subsumes(prefix)),
            );
        }

        subsuming
    }

    pub fn get_subsumed(&self, prefix: &QuantifierPrefix, body: &O) -> HashSet<usize> {
        let mut subsumed: HashSet<usize> = HashSet::default();
        let base = body.to_base();

        for perm in self.config.permutations(0, Some(&self.lemma_qf.ids(&base))) {
            let perm_body = O::from_base(self.lemma_qf.substitute(&base, &perm).unwrap());
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

    pub fn insert(&mut self, prefix: Arc<QuantifierPrefix>, body: O) -> usize {
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

    pub fn insert_minimized(&mut self, prefix: Arc<QuantifierPrefix>, body: O) -> Option<usize> {
        if !LemmaSet::subsumes(self, &prefix, &body) {
            for id in &self.get_subsumed(&prefix, &body) {
                self.remove(id);
            }

            Some(self.insert(prefix, body))
        } else {
            None
        }
    }

    pub fn remove(&mut self, id: &usize) {
        self.to_prefixes.remove(id).unwrap();
        let body = self.to_bodies.remove(id).unwrap();
        let hs = self.bodies.get_mut(&body).unwrap();
        hs.remove(id);
        if hs.is_empty() {
            self.bodies.remove(&body);
        }
    }
}

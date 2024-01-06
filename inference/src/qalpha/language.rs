// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Defines constructors for bounded languages along with their subsumption relation,
//! and implements useful operations over them such as weakening a formula, retrieving
//! all unsatified formulas in a set, and retrieving all formulas subsuming a given formula.
//!
//! Current assumptions:
//! - No shadowing of variables
//! - All formulas created externally (e.g., using `from_term`) are canonical

use crate::{
    hashmap::{HashMap, HashSet},
    qalpha::{
        atoms::Literal,
        quant::{QuantifierConfig, QuantifierPrefix},
    },
};
use fly::{
    ouritertools::OurItertools,
    semantics::{Assignment, Element, Model},
    syntax::{NOp, Quantifier, Sort, Term, UOp},
    term::subst::Substitution,
};

use itertools::Itertools;
use rayon::prelude::*;
use std::{cmp::Ordering, fmt::Debug, hash::Hash, iter::empty, marker::PhantomData, sync::Arc};

// ========== Utilities ==========

macro_rules! fmap_type {
    ($f:ty) => {
        Arc<dyn Fn($f) -> Option<$f> + Send + Sync>
    };
}

macro_rules! simplify_type {
    ($lang:ty, $f:ty) => {
        Option<Arc<dyn Fn(&$lang, &$f) -> Vec<Term> + Send + Sync>>
    };
}

fn par_intersect<T, I>(it: I) -> HashSet<T>
where
    T: Hash + Eq + Send + Sync,
    I: ParallelIterator<Item = HashSet<T>>,
{
    it.map(Some)
        .reduce(
            || None,
            |set1, set2| match (set1, set2) {
                (None, None) => None,
                (Some(set), None) | (None, Some(set)) => Some(set),
                (Some(mut set1), Some(mut set2)) => {
                    if set1.len() > set2.len() {
                        (set1, set2) = (set2, set1);
                    }
                    set1.retain(|e| set2.contains(e));
                    Some(set1)
                }
            },
        )
        .unwrap()
}

// ========== Basic Definitions ==========

fn permutations(from: &[Vec<String>], to: &[Vec<String>]) -> Vec<Substitution> {
    assert_eq!(from.len(), to.len());
    from.iter()
        .zip(to)
        .map(|(f, t)| {
            let terms = f.iter().chain(t).unique().map(|v| Term::id(v));
            terms.permutations(f.len()).map(move |perm| {
                f.iter()
                    .zip(perm)
                    .map(|(x, t)| (x.clone(), t))
                    .collect_vec()
            })
        })
        .multi_cartesian_product_fixed()
        .map(|substs| substs.into_iter().flatten().collect())
        .collect()
}

fn extend_assignment(
    assignment: &Assignment,
    vars: &[String],
    sort: &Sort,
    model: &Model,
) -> Vec<Assignment> {
    vars.iter()
        .map(|_| 0..model.cardinality(sort))
        .multi_cartesian_product_fixed()
        .map(|asgn| {
            let mut new_assignment = assignment.clone();
            for i in 0..vars.len() {
                new_assignment.insert(vars[i].clone(), asgn[i]);
            }

            new_assignment
        })
        .collect()
}

pub trait BoundedLanguage: Sync + Send {
    type SubLanguages;
    type Formula: BoundedFormula;
    type Set: FormulaSet<Formula = Self::Formula>;
    type Config;

    /// Create a new ordered language, with formulas ordered in a way that respects their subsumption relation,
    /// and an efficient implementation of [`FormulaSet`] for these formulas.
    fn new(
        sub: Self::SubLanguages,
        cfg: Self::Config,
        fmap: fmap_type!(Self::Formula),
        simplify: simplify_type!(Self, Self::Formula),
    ) -> Arc<Self>;

    /// The least element in the language w.r.t subsumption.
    fn bottom(&self) -> Self::Formula;

    /// Weaken the formula `f`. We assume that the given `model` and `assignment` do not satify `f`.
    /// The returned set is an antichain w.r.t subsumption, and has the property that for any `f1` subsumed by `f`
    /// which is satisfied by `model` and `assignment`, there exists `f2` in the set that subsumes `f1`.
    fn weaken_unfiltered(
        &self,
        f: &Self::Formula,
        model: &Model,
        assignment: &Assignment,
    ) -> HashSet<Self::Formula>;

    fn filter_map(&self, f: Self::Formula) -> Option<Self::Formula>;

    fn simplify(&self, f: &Self::Formula) -> Vec<Term>;

    fn weaken(
        &self,
        f: &Self::Formula,
        model: &Model,
        assignment: &Assignment,
    ) -> Vec<Self::Formula> {
        self.weaken_unfiltered(f, model, assignment)
            .into_iter()
            .filter_map(|w| self.filter_map(w))
            .collect()
    }

    fn weaken_set(&self, set: &mut Self::Set, model: &Model, assignment: &Assignment) {
        let unsat = set.get_unsat(model, assignment);
        for f in &unsat {
            set.remove(f);
        }

        let weakenings: Vec<_> = unsat
            .par_iter()
            .flat_map_iter(|f| self.weaken(f, model, assignment))
            .collect();
        set.extend_min(weakenings);
    }

    fn minimize<I1, I2>(min_it: I1, it: I2) -> HashSet<Self::Formula>
    where
        I1: IntoIterator<Item = Self::Formula>,
        I2: IntoIterator<Item = Self::Formula>,
    {
        Self::Set::minimize(min_it, it)
    }

    fn log_size(&self) -> f64;
}

pub trait BoundedFormula: Ord + Hash + Clone + Sync + Send + Debug {
    fn subsumes(&self, other: &Self) -> bool;

    fn eval(&self, model: &Model, assignment: &Assignment) -> bool;

    fn substitute(&self, substitution: &Substitution) -> Self;

    fn free_ids(&self) -> HashSet<String>;

    fn from_term(term: &Term) -> Self;

    fn to_term(&self) -> Term;
}

pub trait FormulaSet:
    Clone + Default + Sync + Send + Into<HashSet<Self::Formula>> + AsRef<HashSet<Self::Formula>>
{
    type Formula: BoundedFormula;

    fn contains(&self, f: &Self::Formula) -> bool {
        self.as_ref().contains(f)
    }

    fn insert(&mut self, f: Self::Formula);

    fn remove(&mut self, f: &Self::Formula);

    fn get_subsuming(&self, f: &Self::Formula) -> HashSet<Self::Formula>;

    fn get_unsat(&self, model: &Model, assignment: &Assignment) -> HashSet<Self::Formula>;

    fn len(&self) -> usize;

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn extend<I: IntoIterator<Item = Self::Formula>>(&mut self, it: I) {
        for f in it.into_iter().sorted() {
            self.insert(f);
        }
    }

    fn extend_min<I: IntoIterator<Item = Self::Formula>>(&mut self, it: I) {
        for f in it.into_iter().sorted() {
            if !self.contains(&f) && self.get_subsuming(&f).is_empty() {
                self.insert(f);
            }
        }
    }

    fn minimize<I1, I2>(min_it: I1, it: I2) -> HashSet<Self::Formula>
    where
        I1: IntoIterator<Item = Self::Formula>,
        I2: IntoIterator<Item = Self::Formula>,
    {
        let mut set = Self::default();
        set.extend(min_it);
        set.extend_min(it);
        set.into()
    }
}

// ========== EqLanguage (Basis) ==========
pub struct EqLanguage<L: Hash + Ord + Clone, S>(
    Vec<Bounded<L>>,
    fmap_type!(Bounded<L>),
    simplify_type!(Self, Bounded<L>),
    PhantomData<S>,
);

#[derive(Hash, Clone, PartialEq, Eq, Debug)]
pub enum Bounded<L> {
    Bottom,
    Some(L),
}

#[derive(Clone)]
pub struct EqSet<L>(HashSet<Bounded<L>>);

impl<S: FormulaSet<Formula = Bounded<Literal>>> BoundedLanguage for EqLanguage<Literal, S> {
    type SubLanguages = ();
    type Formula = Bounded<Literal>;
    type Set = S;
    type Config = Vec<Literal>;

    fn new(
        _: Self::SubLanguages,
        cfg: Self::Config,
        fmap: fmap_type!(Self::Formula),
        simplify: simplify_type!(Self, Self::Formula),
    ) -> Arc<Self> {
        Arc::new(Self(
            cfg.into_iter().map(Bounded::Some).collect(),
            fmap,
            simplify,
            PhantomData,
        ))
    }

    fn bottom(&self) -> Self::Formula {
        Bounded::Bottom
    }

    fn weaken_unfiltered(
        &self,
        f: &Self::Formula,
        model: &Model,
        assignment: &Assignment,
    ) -> HashSet<Self::Formula> {
        assert!(!f.eval(model, assignment));
        match f {
            Bounded::Bottom => self
                .0
                .iter()
                .filter(|literal| literal.eval(model, assignment))
                .cloned()
                .collect(),
            _ => HashSet::default(),
        }
    }

    fn filter_map(&self, f: Self::Formula) -> Option<Self::Formula> {
        (self.1)(f)
    }

    fn simplify(&self, f: &Self::Formula) -> Vec<Term> {
        match self.2.as_ref() {
            Some(simplify) => (simplify)(self, f),
            None => vec![f.to_term()],
        }
    }

    fn log_size(&self) -> f64 {
        ((self.0.len() + 1) as f64).log10()
    }
}

impl<L: Ord> PartialOrd for Bounded<L> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<L: Ord> Ord for Bounded<L> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Bounded::Bottom, Bounded::Bottom) => Ordering::Equal,
            (Bounded::Bottom, Bounded::Some(_)) => Ordering::Less,
            (Bounded::Some(_), Bounded::Bottom) => Ordering::Greater,
            (Bounded::Some(s), Bounded::Some(o)) => s.cmp(o),
        }
    }
}

impl BoundedFormula for Bounded<Literal> {
    fn subsumes(&self, other: &Self) -> bool {
        matches!(self, Bounded::Bottom) || self == other
    }

    fn eval(&self, model: &Model, assignment: &Assignment) -> bool {
        match self {
            Bounded::Bottom => false,
            Bounded::Some(l) => model.eval_assign(&l.0, assignment) == l.1 as Element,
        }
    }

    fn substitute(&self, substitution: &Substitution) -> Self {
        match self {
            Bounded::Bottom => Bounded::Bottom,
            Bounded::Some(literal) => Bounded::Some(literal.substitute(substitution)),
        }
    }

    fn free_ids(&self) -> HashSet<String> {
        match self {
            Bounded::Bottom => HashSet::default(),
            Bounded::Some(literal) => literal.ids(),
        }
    }

    fn from_term(term: &Term) -> Self {
        match term {
            Term::Literal(false) => Bounded::Bottom,
            Term::UnaryOp(UOp::Not, t) => {
                Bounded::Some(Literal(Arc::new(t.as_ref().clone()), false))
            }
            _ => Bounded::Some(Literal(Arc::new(term.clone()), true)),
        }
    }

    fn to_term(&self) -> Term {
        match self {
            Bounded::Bottom => Term::Literal(false),
            Bounded::Some(literal) => literal.into(),
        }
    }
}

impl<L> Default for EqSet<L> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl AsRef<HashSet<Bounded<Literal>>> for EqSet<Literal> {
    fn as_ref(&self) -> &HashSet<Bounded<Literal>> {
        &self.0
    }
}

impl From<EqSet<Literal>> for HashSet<Bounded<Literal>> {
    fn from(value: EqSet<Literal>) -> Self {
        value.0
    }
}

impl FormulaSet for EqSet<Literal> {
    type Formula = Bounded<Literal>;

    fn insert(&mut self, f: Self::Formula) {
        assert!(self.0.insert(f));
    }

    fn remove(&mut self, f: &Self::Formula) {
        assert!(self.0.remove(f));
    }

    fn get_subsuming(&self, f: &Self::Formula) -> HashSet<Self::Formula> {
        let mut res = HashSet::default();
        let bottom = Bounded::Bottom;
        if self.0.contains(&bottom) {
            res.insert(bottom);
        }
        if self.0.contains(f) {
            res.insert(f.clone());
        }
        res
    }

    fn get_unsat(&self, model: &Model, assignment: &Assignment) -> HashSet<Self::Formula> {
        self.0
            .iter()
            .filter(|lit| !lit.eval(model, assignment))
            .cloned()
            .collect()
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}

// ========== Binary OR ==========
pub struct BinOrLanguage<L1: BoundedLanguage, L2: BoundedLanguage, S>(
    Arc<L1>,
    Arc<L2>,
    fmap_type!(BinOr<L1::Formula, L2::Formula>),
    simplify_type!(Self, BinOr<L1::Formula, L2::Formula>),
    PhantomData<S>,
);

#[derive(Hash, Clone, PartialEq, Eq, Debug)]
pub struct BinOr<F1: BoundedFormula, F2: BoundedFormula>(F1, F2);

#[derive(Clone)]
pub struct BinOrSet<S1: FormulaSet, S2: FormulaSet> {
    hash_set: HashSet<BinOr<S1::Formula, S2::Formula>>,
    set1: S1,
    proj1: HashMap<S1::Formula, S2>,
}

impl<L1, L2, S> BoundedLanguage for BinOrLanguage<L1, L2, S>
where
    L1: BoundedLanguage,
    L2: BoundedLanguage,
    S: FormulaSet<Formula = BinOr<L1::Formula, L2::Formula>>,
{
    type SubLanguages = (Arc<L1>, Arc<L2>);
    type Formula = BinOr<L1::Formula, L2::Formula>;
    type Set = S;
    type Config = ();

    fn new(
        sub: Self::SubLanguages,
        _: Self::Config,
        fmap: fmap_type!(Self::Formula),
        simplify: simplify_type!(Self, Self::Formula),
    ) -> Arc<Self> {
        Arc::new(Self(sub.0, sub.1, fmap, simplify, PhantomData))
    }

    fn bottom(&self) -> Self::Formula {
        BinOr(self.0.bottom(), self.1.bottom())
    }

    fn weaken_unfiltered(
        &self,
        f: &Self::Formula,
        model: &Model,
        assignment: &Assignment,
    ) -> HashSet<Self::Formula> {
        assert!(!f.eval(model, assignment));
        let (w0, w1) = rayon::join(
            || self.0.weaken(&f.0, model, assignment),
            || self.1.weaken(&f.1, model, assignment),
        );

        w0.into_iter()
            .map(|f0| BinOr(f0, f.1.clone()))
            .chain(w1.into_iter().map(|f1| BinOr(f.0.clone(), f1)))
            .collect()
    }

    fn filter_map(&self, f: Self::Formula) -> Option<Self::Formula> {
        (self.2)(f)
    }

    fn simplify(&self, f: &Self::Formula) -> Vec<Term> {
        match self.3.as_ref() {
            Some(simplify) => (simplify)(self, f),
            None => vec![f.to_term()],
        }
    }

    fn log_size(&self) -> f64 {
        self.0.log_size() + self.1.log_size()
    }
}

impl<F1: BoundedFormula, F2: BoundedFormula> PartialOrd for BinOr<F1, F2> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<F1: BoundedFormula, F2: BoundedFormula> Ord for BinOr<F1, F2> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.0.cmp(&other.0) {
            Ordering::Equal => self.1.cmp(&other.1),
            ord => ord,
        }
    }
}

impl<F1: BoundedFormula, F2: BoundedFormula> BoundedFormula for BinOr<F1, F2> {
    fn subsumes(&self, other: &Self) -> bool {
        self.0.subsumes(&other.0) && self.1.subsumes(&other.1)
    }

    fn eval(&self, model: &Model, assignment: &Assignment) -> bool {
        self.0.eval(model, assignment) || self.1.eval(model, assignment)
    }

    fn substitute(&self, substitution: &Substitution) -> Self {
        Self(
            self.0.substitute(substitution),
            self.1.substitute(substitution),
        )
    }

    fn free_ids(&self) -> HashSet<String> {
        let mut ids = self.0.free_ids();
        ids.extend(self.1.free_ids());
        ids
    }

    fn from_term(term: &Term) -> Self {
        match term {
            Term::NAryOp(NOp::Or, args) if args.len() == 2 => {
                BinOr(F1::from_term(&args[0]), F2::from_term(&args[0]))
            }
            _ => panic!("cannot convert term into a formula in the language"),
        }
    }

    fn to_term(&self) -> Term {
        Term::or([self.0.to_term(), self.1.to_term()])
    }
}

impl<S1: FormulaSet, S2: FormulaSet> Default for BinOrSet<S1, S2> {
    fn default() -> Self {
        Self {
            hash_set: Default::default(),
            set1: Default::default(),
            proj1: Default::default(),
        }
    }
}

impl<S1: FormulaSet, S2: FormulaSet> AsRef<HashSet<BinOr<S1::Formula, S2::Formula>>>
    for BinOrSet<S1, S2>
{
    fn as_ref(&self) -> &HashSet<BinOr<S1::Formula, S2::Formula>> {
        &self.hash_set
    }
}

impl<S1: FormulaSet, S2: FormulaSet> From<BinOrSet<S1, S2>>
    for HashSet<BinOr<S1::Formula, S2::Formula>>
{
    fn from(value: BinOrSet<S1, S2>) -> Self {
        value.hash_set
    }
}

impl<S1: FormulaSet, S2: FormulaSet> FormulaSet for BinOrSet<S1, S2> {
    type Formula = BinOr<S1::Formula, S2::Formula>;

    fn insert(&mut self, f: Self::Formula) {
        assert!(self.hash_set.insert(f.clone()));
        let BinOr(f1, f2) = f;
        if let Some(set2) = self.proj1.get_mut(&f1) {
            set2.insert(f2);
        } else {
            let mut set2 = S2::default();
            set2.insert(f2);
            self.proj1.insert(f1.clone(), set2);
            self.set1.insert(f1);
        }
    }

    fn remove(&mut self, f: &Self::Formula) {
        assert!(self.hash_set.remove(f));
        let BinOr(f1, f2) = f;
        let set2 = self.proj1.get_mut(f1).unwrap();
        set2.remove(f2);
        if set2.is_empty() {
            self.proj1.remove(f1);
            self.set1.remove(f1);
        }
    }

    fn get_subsuming(&self, f: &Self::Formula) -> HashSet<Self::Formula> {
        self.set1
            .get_subsuming(&f.0)
            .par_iter()
            .flat_map(|h1| {
                self.proj1[h1]
                    .get_subsuming(&f.1)
                    .into_par_iter()
                    .map(|h2| BinOr(h1.clone(), h2))
            })
            .collect()
    }

    fn get_unsat(&self, model: &Model, assignment: &Assignment) -> HashSet<Self::Formula> {
        self.set1
            .get_unsat(model, assignment)
            .par_iter()
            .flat_map(|h1| {
                self.proj1[h1]
                    .get_unsat(model, assignment)
                    .into_par_iter()
                    .map(|h2| BinOr(h1.clone(), h2))
            })
            .collect()
    }

    fn len(&self) -> usize {
        self.hash_set.len()
    }
}

// ========== N-ary OR ==========

pub struct OrLanugage<L: BoundedLanguage, S>(
    usize,
    Arc<L>,
    fmap_type!(Or<L::Formula>),
    simplify_type!(Self, Or<L::Formula>),
    PhantomData<S>,
);

#[derive(Hash, Clone, PartialEq, Eq, Debug)]
pub struct Or<F: BoundedFormula>(Arc<Vec<F>>);

pub struct Trie<S: FormulaSet> {
    present: bool,
    next: S,
    edges: HashMap<S::Formula, Trie<S>>,
}

#[derive(Clone)]
pub struct OrSet<S: FormulaSet> {
    hash_set: HashSet<Or<S::Formula>>,
    trie: Trie<S>,
}

impl<L, S> BoundedLanguage for OrLanugage<L, S>
where
    L: BoundedLanguage,
    S: FormulaSet<Formula = Or<L::Formula>>,
{
    type SubLanguages = Arc<L>;
    type Formula = Or<L::Formula>;
    type Set = S;
    type Config = usize;

    fn new(
        sub: Self::SubLanguages,
        cfg: Self::Config,
        fmap: fmap_type!(Self::Formula),
        simplify: simplify_type!(Self, Self::Formula),
    ) -> Arc<Self> {
        Arc::new(Self(cfg, sub, fmap, simplify, PhantomData))
    }

    fn bottom(&self) -> Self::Formula {
        Or(Arc::new(vec![]))
    }

    fn weaken_unfiltered(
        &self,
        f: &Self::Formula,
        model: &Model,
        assignment: &Assignment,
    ) -> HashSet<Self::Formula> {
        assert!(!f.eval(model, assignment));

        // If possible, add a weakening of bottom to the disjunction.
        let bottom_weakenings: HashSet<Self::Formula> = if f.0.len() < self.0 {
            self.1
                .weaken(&self.1.bottom(), model, assignment)
                .into_iter()
                .map(|bot_w| {
                    let mut w = f.clone();
                    let disjuncts = Arc::make_mut(&mut w.0);
                    disjuncts.push(bot_w);
                    disjuncts.sort();
                    w
                })
                .collect()
        } else {
            HashSet::default()
        };

        // Always also try to weaken one of the disjuncts.
        let disj_weakenings: HashSet<Self::Formula> =
            f.0.par_iter()
                .enumerate()
                .flat_map_iter(|(i, disj)| {
                    let mut f_removed = f.clone();
                    Arc::make_mut(&mut f_removed.0).remove(i);
                    self.1
                        .weaken(disj, model, assignment)
                        .into_iter()
                        .map(move |disj_w| (f_removed.clone(), disj_w))
                })
                .map(|(f_removed, disj_w)| {
                    let mut w = f_removed.clone();
                    let disjuncts = Arc::make_mut(&mut w.0);
                    disjuncts.push(disj_w);
                    disjuncts.sort();
                    w
                })
                .collect();

        // Keep minimal weakenings only.
        Self::minimize(
            empty(),
            bottom_weakenings.into_iter().chain(disj_weakenings),
        )
    }

    fn filter_map(&self, f: Self::Formula) -> Option<Self::Formula> {
        (self.2)(f)
    }

    fn simplify(&self, f: &Self::Formula) -> Vec<Term> {
        match self.3.as_ref() {
            Some(simplify) => (simplify)(self, f),
            None => vec![f.to_term()],
        }
    }

    fn log_size(&self) -> f64 {
        // The size is approximated as n^k, where n is the sub-language size and k is the length of the disjunction.
        // With this, log10(n^k) = k * log10(n).
        (self.0 as f64) * self.1.log_size()
    }
}

impl<F: BoundedFormula> PartialOrd for Or<F> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.0.cmp(&other.0))
    }
}

impl<F: BoundedFormula> Ord for Or<F> {
    fn cmp(&self, other: &Self) -> Ordering {
        // Compare the sequences in reverse order. If at some point the two compared elements aren't equal,
        // then they determine the order.
        for (s, o) in self.0.iter().rev().zip(other.0.iter().rev()) {
            match s.cmp(o) {
                Ordering::Equal => (),
                ord => return ord,
            }
        }
        // Otherwise, the shorter or-sequence is lesser.
        self.0.len().cmp(&other.0.len())
    }
}

impl<F: BoundedFormula> BoundedFormula for Or<F> {
    fn subsumes(&self, other: &Self) -> bool {
        self.0.is_empty()
            || (0..other.0.len())
                .filter(|i| self.0[0].subsumes(&other.0[*i]))
                .any(|i| {
                    let mut new_self = self.clone();
                    let mut new_other = other.clone();
                    Arc::make_mut(&mut new_self.0).remove(0);
                    Arc::make_mut(&mut new_other.0).remove(i);
                    new_self.subsumes(&new_other)
                })
    }

    fn eval(&self, model: &Model, assignment: &Assignment) -> bool {
        self.0.iter().any(|f| f.eval(model, assignment))
    }

    fn substitute(&self, substitution: &Substitution) -> Self {
        Or(Arc::new(
            self.0
                .iter()
                .map(|f| f.substitute(substitution))
                .sorted()
                .collect(),
        ))
    }

    fn free_ids(&self) -> HashSet<String> {
        self.0.iter().flat_map(|f| f.free_ids()).collect()
    }

    fn from_term(term: &Term) -> Self {
        match term {
            Term::NAryOp(NOp::Or, args) => Or(Arc::new(args.iter().map(F::from_term).collect())),
            _ => panic!("cannot convert term into a formula in the language"),
        }
    }

    fn to_term(&self) -> Term {
        Term::or(self.0.iter().map(|t| t.to_term()))
    }
}

impl<S: FormulaSet> Clone for Trie<S> {
    fn clone(&self) -> Self {
        Self {
            present: self.present,
            next: self.next.clone(),
            edges: self.edges.clone(),
        }
    }
}

impl<S: FormulaSet> Default for Trie<S> {
    fn default() -> Self {
        Self {
            present: false,
            next: Default::default(),
            edges: Default::default(),
        }
    }
}

impl<S: FormulaSet> Trie<S> {
    fn insert<I: Iterator<Item = S::Formula>>(&mut self, mut seq: I) {
        match seq.next() {
            None => {
                assert!(!self.present);
                self.present = true;
            }
            Some(first) => {
                if let Some(next_trie) = self.edges.get_mut(&first) {
                    next_trie.insert(seq);
                } else {
                    let mut next_trie = Trie::default();
                    next_trie.insert(seq);
                    self.next.insert(first.clone());
                    self.edges.insert(first, next_trie);
                }
            }
        }
    }

    fn remove(&mut self, seq: &[S::Formula]) {
        match seq.split_first() {
            None => {
                assert!(self.present);
                self.present = false;
            }
            Some((first, rest)) => {
                let next_trie = self.edges.get_mut(first).unwrap();
                next_trie.remove(rest);
                if next_trie.is_empty() {
                    self.next.remove(first);
                    self.edges.remove(first);
                }
            }
        }
    }

    fn get_subsuming(&self, seq: &[&S::Formula]) -> HashSet<Vec<S::Formula>> {
        let mut subsuming: HashSet<_> = seq
            .par_iter()
            .enumerate()
            .flat_map(|(i, f)| {
                // Get all those subsuming position i in seq
                let subsuming_i = self.next.get_subsuming(f);
                // Remove position i from seq
                let mut shortened_seq = seq.to_vec();
                shortened_seq.remove(i);
                subsuming_i.into_par_iter().flat_map_iter(move |sub| {
                    // Maintain only elements greater than sub, since anything smaller or equal is also smaller than
                    // the following formulas in the trie, and therefore cannot be subsumed by them.
                    let new_seq = match shortened_seq.iter().position(|x| *x > &sub) {
                        None => &[],
                        Some(i) => &shortened_seq[i..],
                    };

                    self.edges[&sub]
                        .get_subsuming(new_seq)
                        .into_iter()
                        .map(move |mut v| {
                            v.insert(0, sub.clone());
                            v
                        })
                })
            })
            .collect();
        if self.present {
            subsuming.insert(vec![]);
        }
        subsuming
    }

    fn get_unsat(&self, model: &Model, assignment: &Assignment) -> Vec<Vec<S::Formula>> {
        let mut res: Vec<Vec<S::Formula>> = self
            .next
            .get_unsat(model, assignment)
            .par_iter()
            .flat_map_iter(|f| {
                self.edges[f]
                    .get_unsat(model, assignment)
                    .into_iter()
                    .map(|mut v| {
                        v.insert(0, f.clone());
                        v
                    })
            })
            .collect();
        if self.present {
            res.push(vec![]);
        }
        res
    }

    fn is_empty(&self) -> bool {
        !self.present && self.edges.is_empty()
    }
}

impl<S: FormulaSet> Default for OrSet<S> {
    fn default() -> Self {
        Self {
            hash_set: Default::default(),
            trie: Default::default(),
        }
    }
}

impl<S: FormulaSet> AsRef<HashSet<Or<S::Formula>>> for OrSet<S> {
    fn as_ref(&self) -> &HashSet<Or<S::Formula>> {
        &self.hash_set
    }
}

impl<S: FormulaSet> From<OrSet<S>> for HashSet<Or<S::Formula>> {
    fn from(value: OrSet<S>) -> Self {
        value.hash_set
    }
}

impl<S: FormulaSet> FormulaSet for OrSet<S> {
    type Formula = Or<S::Formula>;

    fn insert(&mut self, f: Self::Formula) {
        self.trie.insert(f.0.iter().cloned());
        assert!(self.hash_set.insert(f));
    }

    fn remove(&mut self, f: &Self::Formula) {
        self.trie.remove(&f.0);
        assert!(self.hash_set.remove(f));
    }

    fn get_subsuming(&self, f: &Self::Formula) -> HashSet<Self::Formula> {
        self.trie
            .get_subsuming(&f.0.iter().collect_vec())
            .into_iter()
            .map(|v| Or(Arc::new(v)))
            .collect()
    }

    fn get_unsat(&self, model: &Model, assignment: &Assignment) -> HashSet<Self::Formula> {
        self.trie
            .get_unsat(model, assignment)
            .into_iter()
            .map(|v| Or(Arc::new(v)))
            .collect()
    }

    fn len(&self) -> usize {
        self.hash_set.len()
    }
}

// ========== N-ary AND ==========

pub struct AndLanugage<L: BoundedLanguage, S>(
    Arc<L>,
    fmap_type!(And<L::Formula>),
    simplify_type!(Self, And<L::Formula>),
    PhantomData<S>,
);

/// A conjunction. Assumed to be ordered, redundancy-free and non-empty.
#[derive(Hash, Clone, PartialEq, Eq, Debug)]
pub struct And<F: BoundedFormula>(Arc<Vec<F>>);

#[derive(Clone)]
pub struct AndSet<S: FormulaSet> {
    hash_set: HashSet<And<S::Formula>>,
    all_present: S,
    to_containing: HashMap<S::Formula, HashSet<And<S::Formula>>>,
}

impl<L, S> BoundedLanguage for AndLanugage<L, S>
where
    L: BoundedLanguage,
    S: FormulaSet<Formula = And<L::Formula>>,
{
    type SubLanguages = Arc<L>;
    type Formula = And<L::Formula>;
    type Set = S;
    type Config = ();

    fn new(
        sub: Self::SubLanguages,
        _: Self::Config,
        fmap: fmap_type!(Self::Formula),
        simplify: simplify_type!(Self, Self::Formula),
    ) -> Arc<Self> {
        Arc::new(Self(sub, fmap, simplify, PhantomData))
    }

    fn bottom(&self) -> Self::Formula {
        And(Arc::new(vec![self.0.bottom()]))
    }

    fn weaken_unfiltered(
        &self,
        f: &Self::Formula,
        model: &Model,
        assignment: &Assignment,
    ) -> HashSet<Self::Formula> {
        assert!(!f.eval(model, assignment));
        let (sat, unsat): (Vec<_>, Vec<_>) =
            f.0.iter().partition(|conj| conj.eval(model, assignment));
        let conj_weakenings: HashSet<_> = unsat
            .par_iter()
            .flat_map_iter(|conj| self.0.weaken(conj, model, assignment))
            .collect();

        let and = L::minimize(sat.into_iter().cloned(), conj_weakenings);
        if and.is_empty() {
            HashSet::default()
        } else {
            HashSet::from_iter([And(Arc::new(and.into_iter().sorted().collect()))])
        }
    }

    fn filter_map(&self, f: Self::Formula) -> Option<Self::Formula> {
        (self.1)(f)
    }

    fn simplify(&self, f: &Self::Formula) -> Vec<Term> {
        match self.2.as_ref() {
            Some(simplify) => (simplify)(self, f),
            None => vec![f.to_term()],
        }
    }

    fn log_size(&self) -> f64 {
        // The size is equal to 2^n, where n is the sub-language size.
        // With this, log10(2^n) = n * log10(2)
        10_f64.powf(self.0.log_size()) * 2_f64.log10()
    }
}

impl<F: BoundedFormula> PartialOrd for And<F> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: BoundedFormula> Ord for And<F> {
    fn cmp(&self, other: &Self) -> Ordering {
        // Compare the sequences in order. If at some point the two compared elements aren't equal,
        // then they determine the order.
        for (s, o) in self.0.iter().zip(other.0.iter()) {
            match s.cmp(o) {
                Ordering::Equal => (),
                ord => return ord,
            }
        }
        // Otherwise, the longer or-sequence is lesser.
        self.0.len().cmp(&other.0.len()).reverse()
    }
}

impl<F: BoundedFormula> BoundedFormula for And<F> {
    fn subsumes(&self, other: &Self) -> bool {
        other.0.iter().all(|o| self.0.iter().any(|s| s.subsumes(o)))
    }

    fn eval(&self, model: &Model, assignment: &Assignment) -> bool {
        self.0.iter().all(|f| f.eval(model, assignment))
    }

    fn substitute(&self, substitution: &Substitution) -> Self {
        And(Arc::new(
            self.0
                .iter()
                .map(|f| f.substitute(substitution))
                .sorted()
                .collect(),
        ))
    }

    fn free_ids(&self) -> HashSet<String> {
        self.0.iter().flat_map(|f| f.free_ids()).collect()
    }

    fn from_term(term: &Term) -> Self {
        match term {
            Term::NAryOp(NOp::And, args) => And(Arc::new(args.iter().map(F::from_term).collect())),
            _ => panic!("cannot convert term into a formula in the language"),
        }
    }

    fn to_term(&self) -> Term {
        Term::and(self.0.iter().map(|t| t.to_term()))
    }
}

impl<S: FormulaSet> Default for AndSet<S> {
    fn default() -> Self {
        Self {
            hash_set: Default::default(),
            all_present: Default::default(),
            to_containing: Default::default(),
        }
    }
}

impl<S: FormulaSet> AsRef<HashSet<And<S::Formula>>> for AndSet<S> {
    fn as_ref(&self) -> &HashSet<And<S::Formula>> {
        &self.hash_set
    }
}

impl<S: FormulaSet> From<AndSet<S>> for HashSet<And<S::Formula>> {
    fn from(value: AndSet<S>) -> Self {
        value.hash_set
    }
}

impl<S: FormulaSet> FormulaSet for AndSet<S> {
    type Formula = And<S::Formula>;

    fn insert(&mut self, f: Self::Formula) {
        for conj in f.0.as_ref() {
            if let Some(containing) = self.to_containing.get_mut(conj) {
                assert!(containing.insert(f.clone()));
            } else {
                self.all_present.insert(conj.clone());
                let mut containing = HashSet::default();
                assert!(containing.insert(f.clone()));
                self.to_containing.insert(conj.clone(), containing);
            }
        }
        assert!(self.hash_set.insert(f));
    }

    fn remove(&mut self, f: &Self::Formula) {
        for conj in f.0.as_ref() {
            let containing = self.to_containing.get_mut(conj).unwrap();
            containing.remove(f);
            if containing.is_empty() {
                self.all_present.remove(conj);
                self.to_containing.remove(conj);
            }
        }
        assert!(self.hash_set.remove(f));
    }

    fn get_subsuming(&self, f: &Self::Formula) -> HashSet<Self::Formula> {
        par_intersect(
            f.0.par_iter()
                // Get all formulas containing a conjunct subsuming a specific conjunct in `f`
                .map(|conj| {
                    self.all_present
                        .get_subsuming(conj)
                        .iter()
                        .flat_map(|o| self.to_containing[o].iter().cloned())
                        .collect::<HashSet<_>>()
                }),
        )
    }

    fn get_unsat(&self, model: &Model, assignment: &Assignment) -> HashSet<Self::Formula> {
        self.all_present
            .get_unsat(model, assignment)
            .par_iter()
            .flat_map_iter(|f| self.to_containing[f].iter().cloned())
            .collect()
    }

    fn len(&self) -> usize {
        self.hash_set.len()
    }
}

// ========== Quantification ==========

pub struct QuantLanguage<L: BoundedLanguage, S> {
    cfg: Arc<QuantifierConfig>,
    language: Arc<L>,
    fmap: fmap_type!(Quant<L::Formula>),
    simplify: simplify_type!(Self, Quant<L::Formula>),
    set_type: PhantomData<S>,
}

#[derive(Hash, Clone, PartialEq, Eq, Debug)]
pub struct Quant<F: BoundedFormula> {
    prefix: QuantifierPrefix,
    body: F,
}

#[derive(Clone)]
pub struct QuantSet<S: FormulaSet> {
    hash_set: HashSet<Quant<S::Formula>>,
    variable_counts: Vec<HashMap<String, usize>>,
    variables: Vec<Vec<String>>,
    sorts: Vec<Sort>,
    /// Maps a specific prefix to the [`FormulaSet`] holding the bodies with this prefix,
    /// and a mapping from each such body to its [`QuantifierPrefix`].
    sets: HashMap<Vec<Quantifier>, (S, HashMap<S::Formula, QuantifierPrefix>)>,
}

impl<L, S> QuantLanguage<L, S>
where
    L: BoundedLanguage,
    S: FormulaSet<Formula = Quant<L::Formula>>,
{
    fn canonicalize(&self, f: Quant<L::Formula>) -> <Self as BoundedLanguage>::Formula {
        let (perm, perm_body) = permutations(&f.prefix.names, &self.cfg.names)
            .into_iter()
            .map(|perm| {
                let perm_body = f.body.substitute(&perm);
                (perm, perm_body)
            })
            .min_by(|x, y| x.1.cmp(&y.1))
            .unwrap();
        let perm_vars: Vec<Vec<String>> = f
            .prefix
            .names
            .iter()
            .map(|v| {
                v.iter()
                    .map(|n| match &perm[n] {
                        Term::Id(name) => name.clone(),
                        _ => unreachable!(),
                    })
                    .collect()
            })
            .collect();

        Quant {
            prefix: QuantifierPrefix {
                quantifiers: f.prefix.quantifiers,
                sorts: f.prefix.sorts,
                names: Arc::new(perm_vars),
            },
            body: perm_body,
        }
    }

    fn add_prefix(&self, body: L::Formula, prefix: &Vec<Quantifier>) -> Quant<L::Formula> {
        assert_eq!(prefix.len(), self.cfg.len());

        let free_ids = body.free_ids();
        let names = self
            .cfg
            .names
            .iter()
            .map(|vs| {
                vs.iter()
                    .filter(|id| free_ids.contains(*id))
                    .cloned()
                    .collect()
            })
            .collect();

        self.canonicalize(Quant {
            prefix: QuantifierPrefix {
                quantifiers: prefix.clone(),
                sorts: self.cfg.sorts.clone(),
                names: Arc::new(names),
            },
            body,
        })
    }

    fn weaken_rec(
        &self,
        index: usize,
        mut bodies: L::Set,
        prefix: &Vec<Quantifier>,
        model: &Model,
        assignment: &Assignment,
    ) -> L::Set {
        assert!(index <= self.cfg.len());

        if index == self.cfg.len() {
            let unsat = bodies.get_unsat(model, assignment);
            for u in &unsat {
                bodies.remove(u);
            }
            bodies.extend_min(
                unsat
                    .iter()
                    .flat_map(|u| self.language.weaken(u, model, assignment)),
            );
            return bodies;
        }

        let assignments = extend_assignment(
            assignment,
            &self.cfg.names[index],
            &self.cfg.sorts[index],
            model,
        );
        match prefix[index] {
            Quantifier::Forall => {
                for asgn in &assignments {
                    bodies = self.weaken_rec(index + 1, bodies, prefix, model, asgn);
                }
                bodies
            }
            Quantifier::Exists => {
                let mut weakenings = L::Set::default();
                weakenings.extend_min(
                    assignments
                        .par_iter()
                        .flat_map_iter(|asgn| {
                            self.weaken_rec(index + 1, bodies.clone(), prefix, model, asgn)
                                .into()
                        })
                        .collect::<Vec<_>>(),
                );
                weakenings
            }
        }
    }
}

impl<L, S> BoundedLanguage for QuantLanguage<L, S>
where
    L: BoundedLanguage,
    S: FormulaSet<Formula = Quant<L::Formula>>,
{
    type SubLanguages = Arc<L>;
    type Formula = Quant<L::Formula>;
    type Set = S;
    type Config = Arc<QuantifierConfig>;

    fn new(
        sub: Self::SubLanguages,
        cfg: Self::Config,
        fmap: fmap_type!(Self::Formula),
        simplify: simplify_type!(Self, Self::Formula),
    ) -> Arc<Self> {
        Arc::new(Self {
            cfg,
            language: sub,
            fmap,
            simplify,
            set_type: PhantomData,
        })
    }

    fn bottom(&self) -> Self::Formula {
        let length = self.cfg.len();
        // We assume bottom does not contain any variable symbols
        Quant {
            prefix: QuantifierPrefix {
                quantifiers: self
                    .cfg
                    .quantifiers
                    .iter()
                    .map(|q| q.unwrap_or(Quantifier::Forall))
                    .collect(),
                sorts: self.cfg.sorts.clone(),
                names: Arc::new(vec![vec![]; length]),
            },
            body: self.language.bottom(),
        }
    }

    fn weaken_unfiltered(
        &self,
        f: &Self::Formula,
        model: &Model,
        assignment: &Assignment,
    ) -> HashSet<Self::Formula> {
        let mut bodies = L::Set::default();
        bodies.insert(f.body.clone());

        let prefixes: Vec<_> = f
            .prefix
            .quantifiers
            .iter()
            .zip(self.cfg.quantifiers.iter())
            .map(|q| match q {
                (Quantifier::Exists, _) => vec![Quantifier::Exists],
                (_, None) => vec![Quantifier::Forall, Quantifier::Exists],
                _ => vec![Quantifier::Forall],
            })
            .multi_cartesian_product_fixed()
            .collect();

        let weakenings: Vec<Self::Formula> = prefixes
            .par_iter()
            .flat_map_iter(|prefix| {
                self.weaken_rec(0, bodies.clone(), prefix, model, assignment)
                    .into()
                    .into_iter()
                    .map(move |body| self.add_prefix(body, prefix))
            })
            .collect();

        Self::minimize(empty(), weakenings)
    }

    fn filter_map(&self, f: Self::Formula) -> Option<Self::Formula> {
        (self.fmap)(f)
    }

    fn simplify(&self, f: &Self::Formula) -> Vec<Term> {
        match self.simplify.as_ref() {
            Some(simplify) => (simplify)(self, f),
            None => vec![f.to_term()],
        }
    }

    fn log_size(&self) -> f64 {
        self.language.log_size()
            + self
                .cfg
                .quantifiers
                .iter()
                .map(|q| match q {
                    None => 2_f64.log10(),
                    _ => 0_f64,
                })
                .sum::<f64>()
    }
}

impl<F: BoundedFormula> PartialOrd for Quant<F> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: BoundedFormula> Ord for Quant<F> {
    fn cmp(&self, other: &Self) -> Ordering {
        assert_eq!(self.prefix.len(), other.prefix.len());
        for i in 0..self.prefix.len() {
            match (self.prefix.quantifiers[i], other.prefix.quantifiers[i]) {
                (Quantifier::Forall, Quantifier::Exists) => return Ordering::Less,
                (Quantifier::Exists, Quantifier::Forall) => return Ordering::Greater,
                _ => (),
            }
        }
        self.body.cmp(&other.body)
    }
}

impl<F: BoundedFormula> Quant<F> {
    fn eval_rec(&self, index: usize, model: &Model, assignment: &Assignment) -> bool {
        if index == self.prefix.len() {
            self.body.eval(model, assignment)
        } else {
            let assignments = extend_assignment(
                assignment,
                &self.prefix.names[index],
                &self.prefix.sorts[index],
                model,
            );
            match self.prefix.quantifiers[index] {
                Quantifier::Forall => assignments
                    .iter()
                    .all(|asgn| self.eval_rec(index + 1, model, asgn)),
                Quantifier::Exists => assignments
                    .iter()
                    .any(|asgn| self.eval_rec(index + 1, model, asgn)),
            }
        }
    }

    fn from_term_rec(
        term: &Term,
        mut quantifiers: Vec<Quantifier>,
        mut sorts: Vec<Sort>,
        mut names: Vec<Vec<String>>,
    ) -> Self {
        match term {
            Term::Quantified {
                quantifier,
                binders,
                body,
            } => {
                assert!(!binders.is_empty());
                let sort = binders[0].sort.clone();
                assert!(binders.iter().all(|b| b.sort == sort));
                quantifiers.push(*quantifier);
                sorts.push(sort);
                names.push(binders.iter().map(|b| b.name.clone()).collect());
                Self::from_term_rec(body, quantifiers, sorts, names)
            }
            _ => Quant {
                prefix: QuantifierPrefix {
                    quantifiers,
                    sorts: Arc::new(sorts),
                    names: Arc::new(names),
                },
                body: F::from_term(term),
            },
        }
    }
}

impl<F: BoundedFormula> BoundedFormula for Quant<F> {
    fn subsumes(&self, other: &Self) -> bool {
        assert_eq!(self.prefix.len(), other.prefix.len());
        self.prefix
            .quantifiers
            .iter()
            .zip(&other.prefix.quantifiers)
            .all(|(sq, oq)| {
                matches!(
                    (sq, oq),
                    (Quantifier::Forall, _) | (Quantifier::Exists, Quantifier::Exists)
                )
            })
            && permutations(&self.prefix.names, &other.prefix.names)
                .iter()
                .any(|perm| self.body.substitute(perm).subsumes(&other.body))
    }

    fn eval(&self, model: &Model, assignment: &Assignment) -> bool {
        self.eval_rec(0, model, assignment)
    }

    fn substitute(&self, substitution: &Substitution) -> Self {
        // We assume the substitution does not refer to quantified variables.
        Self {
            prefix: self.prefix.clone(),
            body: self.body.substitute(substitution),
        }
    }

    fn free_ids(&self) -> HashSet<String> {
        let mut ids = self.body.free_ids();
        for v in self.prefix.names.iter().flatten() {
            ids.remove(v);
        }
        ids
    }

    fn from_term(term: &Term) -> Self {
        Self::from_term_rec(term, vec![], vec![], vec![])
    }

    fn to_term(&self) -> Term {
        self.prefix.quantify(self.body.to_term())
    }
}

impl<S: FormulaSet> Default for QuantSet<S> {
    fn default() -> Self {
        Self {
            hash_set: Default::default(),
            variable_counts: Default::default(),
            variables: vec![],
            sorts: vec![],
            sets: HashMap::default(),
        }
    }
}

impl<S: FormulaSet> AsRef<HashSet<Quant<S::Formula>>> for QuantSet<S> {
    fn as_ref(&self) -> &HashSet<Quant<S::Formula>> {
        &self.hash_set
    }
}

impl<S: FormulaSet> From<QuantSet<S>> for HashSet<Quant<S::Formula>> {
    fn from(value: QuantSet<S>) -> Self {
        value.hash_set
    }
}

impl<S: FormulaSet> QuantSet<S> {
    fn get_unsat_rec(
        &self,
        qs: &Vec<Quantifier>,
        model: &Model,
        assignment: &Assignment,
    ) -> HashSet<Quant<S::Formula>> {
        let index = qs.len();
        if index == self.sorts.len() {
            if let Some((set, map)) = self.sets.get(qs) {
                return set
                    .get_unsat(model, assignment)
                    .into_iter()
                    .map(|body| Quant {
                        prefix: map[&body].clone(),
                        body,
                    })
                    .collect();
            } else {
                return HashSet::default();
            }
        }

        let assignments = extend_assignment(
            assignment,
            &self.variables[index],
            &self.sorts[index],
            model,
        );

        let (unsat_forall, mut unsat_exists) = rayon::join(
            || {
                let mut qs_forall = qs.clone();
                qs_forall.push(Quantifier::Forall);
                assignments
                    .par_iter()
                    .flat_map_iter(|asgn| self.get_unsat_rec(&qs_forall, model, asgn))
                    .collect::<HashSet<_>>()
            },
            || {
                let mut qs_exists = qs.clone();
                qs_exists.push(Quantifier::Exists);
                par_intersect(
                    assignments
                        .par_iter()
                        .map(|asgn| self.get_unsat_rec(&qs_exists, model, asgn)),
                )
            },
        );
        unsat_exists.extend(unsat_forall);
        unsat_exists
    }
}

impl<S: FormulaSet> FormulaSet for QuantSet<S> {
    type Formula = Quant<S::Formula>;

    fn insert(&mut self, f: Self::Formula) {
        let length = f.prefix.len();
        // The length of the prefixes this set can hold are determined upon the first insertion, and remain fixed.
        if self.hash_set.is_empty() {
            assert!(self.sets.is_empty());
            self.variable_counts = vec![HashMap::default(); length];
            self.variables = vec![vec![]; length];
            self.sorts = f.prefix.sorts.as_ref().clone();
        } else {
            assert_eq!(self.variable_counts.len(), length);
            assert_eq!(self.variables.len(), length);
            assert_eq!(&self.sorts, f.prefix.sorts.as_ref());
        }

        self.hash_set.insert(f.clone());
        let Quant { prefix, body } = f;

        // Update present variables.
        for i in 0..length {
            for name in &prefix.names[i] {
                if let Some(c) = self.variable_counts[i].get_mut(name) {
                    *c += 1;
                } else {
                    self.variable_counts[i].insert(name.clone(), 1);
                    self.variables[i].push(name.clone());
                }
            }
        }

        // Insert formula into the proper subset.
        let qs = &prefix.quantifiers;
        if let Some((set, map)) = self.sets.get_mut(qs) {
            set.insert(body.clone());
            assert!(map.insert(body, prefix).is_none());
        } else {
            let mut set = S::default();
            let mut map = HashMap::default();
            let qs = qs.clone();
            set.insert(body.clone());
            map.insert(body, prefix);
            self.sets.insert(qs, (set, map));
        }
    }

    fn remove(&mut self, f: &Self::Formula) {
        let length = f.prefix.len();
        assert_eq!(self.variable_counts.len(), length);
        assert_eq!(self.variables.len(), length);
        assert_eq!(&self.sorts, f.prefix.sorts.as_ref());

        assert!(self.hash_set.remove(f));
        let Quant { prefix, body } = f;

        // Update present variables.
        for i in 0..length {
            for name in &f.prefix.names[i] {
                let c = self.variable_counts[i].get_mut(name).unwrap();
                *c -= 1;
                if *c == 0 {
                    self.variable_counts[i].remove(name);
                    self.variables[i].retain(|x| x != name);
                }
            }
        }

        // Remove formula from the proper subset.
        let qs = &prefix.quantifiers;
        let (set, map) = self.sets.get_mut(qs).unwrap();
        set.remove(body);
        assert!(map.remove(body).is_some());
        if map.is_empty() {
            self.sets.remove(qs);
        }
    }

    fn get_subsuming(&self, f: &Self::Formula) -> HashSet<Self::Formula> {
        if self.is_empty() {
            return HashSet::default();
        }

        // The prefixes of formulas which might subsume this one.
        let relevant: Vec<Vec<Quantifier>> = f
            .prefix
            .quantifiers
            .iter()
            .map(|q| match q {
                Quantifier::Exists => vec![Quantifier::Forall, Quantifier::Exists],
                Quantifier::Forall => vec![Quantifier::Forall],
            })
            .multi_cartesian_product_fixed()
            .collect();

        permutations(&f.prefix.names, &self.variables)
            .par_iter()
            .flat_map(|perm| {
                let perm_body = f.body.substitute(perm);
                relevant
                    .par_iter()
                    .filter_map(|qs| self.sets.get(qs))
                    .flat_map(move |(set, map)| {
                        set.get_subsuming(&perm_body)
                            .into_par_iter()
                            .map(|body| Quant {
                                prefix: map[&body].clone(),
                                body,
                            })
                    })
            })
            .collect()
    }

    fn get_unsat(&self, model: &Model, assignment: &Assignment) -> HashSet<Self::Formula> {
        if self.is_empty() {
            HashSet::default()
        } else {
            self.get_unsat_rec(&vec![], model, assignment)
        }
    }

    fn len(&self) -> usize {
        self.hash_set.len()
    }
}

// ========== Baseline Set ==========

#[derive(Clone)]
pub struct BaselineSet<F: BoundedFormula>(HashSet<F>);

impl<F: BoundedFormula> Default for BaselineSet<F> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<F: BoundedFormula> From<BaselineSet<F>> for HashSet<F> {
    fn from(value: BaselineSet<F>) -> Self {
        value.0
    }
}

impl<F: BoundedFormula> AsRef<HashSet<F>> for BaselineSet<F> {
    fn as_ref(&self) -> &HashSet<F> {
        &self.0
    }
}

impl<F: BoundedFormula> FormulaSet for BaselineSet<F> {
    type Formula = F;

    fn insert(&mut self, f: Self::Formula) {
        assert!(self.0.insert(f))
    }

    fn remove(&mut self, f: &Self::Formula) {
        assert!(self.0.remove(f))
    }

    fn get_subsuming(&self, f: &Self::Formula) -> HashSet<Self::Formula> {
        self.0
            .par_iter()
            .filter(|x| x.subsumes(f))
            .cloned()
            .collect()
    }

    fn get_unsat(&self, model: &Model, assignment: &Assignment) -> HashSet<Self::Formula> {
        self.0
            .par_iter()
            .filter(|x| !x.eval(model, assignment))
            .cloned()
            .collect()
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}

// ========== Useful Types and Functions ==========

type Clause = Or<Bounded<Literal>>;
type Cube = And<Bounded<Literal>>;
type Cnf = And<Clause>;
type Dnf = Or<Cube>;
type PDnf = BinOr<Clause, Dnf>;

fn trivial_fmap<T>() -> fmap_type!(T) {
    Arc::new(|f| Some(f))
}

fn clause_fmap() -> fmap_type!(Clause) {
    Arc::new(|f| {
        // Disallow a literal and its negation in the same clause, and disallow inequalities.
        if f.0.iter().all(|l| match l {
            Bounded::Bottom => true,
            Bounded::Some(l) => !l.is_neq() && !f.0.contains(&Bounded::Some(l.negate())),
        }) {
            Some(f)
        } else {
            None
        }
    })
}

fn pdnf_fmap() -> fmap_type!(PDnf) {
    Arc::new(|mut f| {
        // Remove all negations of clause literals from cubes.
        let neg_literals: HashSet<_> =
            f.0 .0
                .iter()
                .filter_map(|lit| match lit {
                    Bounded::Bottom => None,
                    Bounded::Some(l) => Some(Bounded::Some(l.negate())),
                })
                .collect();
        let mut new_cubes = HashSet::default();
        for cube in f.1 .0.iter() {
            let mut new_cube = cube.clone();
            let cube_literals = Arc::make_mut(&mut new_cube.0);
            cube_literals.retain(|l| !neg_literals.contains(l));
            if cube_literals.is_empty() {
                return None;
            }
            new_cubes.insert(new_cube);
        }
        f.1 .0 = Arc::new(new_cubes.into_iter().sorted().collect());
        Some(f)
    })
}

pub mod baseline {
    use super::*;

    pub type LiteralLanguage = EqLanguage<Literal, BaselineSet<Bounded<Literal>>>;
    pub type ClauseLanguage = OrLanugage<LiteralLanguage, BaselineSet<Clause>>;
    pub type CubeLanguage = AndLanugage<LiteralLanguage, BaselineSet<Cube>>;
    pub type CnfLanguage = AndLanugage<ClauseLanguage, BaselineSet<Cnf>>;
    pub type DnfLanguage = OrLanugage<CubeLanguage, BaselineSet<Dnf>>;
    pub type PDnfLanguage = BinOrLanguage<ClauseLanguage, DnfLanguage, BaselineSet<PDnf>>;
    pub type QuantPDnfLanguage = QuantLanguage<PDnfLanguage, BaselineSet<Quant<PDnf>>>;

    pub fn literal_language(literals: Vec<Literal>) -> Arc<LiteralLanguage> {
        LiteralLanguage::new((), literals, trivial_fmap(), None)
    }

    pub fn clause_language(clause_size: usize, literals: Vec<Literal>) -> Arc<ClauseLanguage> {
        ClauseLanguage::new(literal_language(literals), clause_size, clause_fmap(), None)
    }

    pub fn cube_language(literals: Vec<Literal>) -> Arc<CubeLanguage> {
        CubeLanguage::new(literal_language(literals), (), trivial_fmap(), None)
    }

    pub fn cnf_language(clause_size: usize, literals: Vec<Literal>) -> Arc<CnfLanguage> {
        CnfLanguage::new(
            clause_language(clause_size, literals),
            (),
            trivial_fmap(),
            None,
        )
    }

    pub fn dnf_language(cube_count: usize, literals: Vec<Literal>) -> Arc<DnfLanguage> {
        DnfLanguage::new(cube_language(literals), cube_count, trivial_fmap(), None)
    }

    pub fn pdnf_language(
        clause_size: usize,
        cube_count: usize,
        clause_literals: Vec<Literal>,
        cube_literals: Vec<Literal>,
    ) -> Arc<PDnfLanguage> {
        PDnfLanguage::new(
            (
                clause_language(clause_size, clause_literals),
                dnf_language(cube_count, cube_literals),
            ),
            (),
            pdnf_fmap(),
            None,
        )
    }

    pub fn quant_pdnf_language(
        cfg: Arc<QuantifierConfig>,
        clause_size: usize,
        cube_count: usize,
        clause_literals: Vec<Literal>,
        cube_literals: Vec<Literal>,
    ) -> Arc<QuantPDnfLanguage> {
        QuantLanguage::new(
            pdnf_language(clause_size, cube_count, clause_literals, cube_literals),
            cfg,
            trivial_fmap(),
            None,
        )
    }
}

pub mod advanced {
    use super::*;

    pub type LiteralSet = EqSet<Literal>;
    pub type ClauseSet = OrSet<LiteralSet>;
    pub type CubeSet = AndSet<LiteralSet>;
    pub type CnfSet = AndSet<ClauseSet>;
    pub type DnfSet = OrSet<CubeSet>;
    pub type PDnfSet = BinOrSet<ClauseSet, DnfSet>;
    pub type QuantPDnfSet = QuantSet<PDnfSet>;

    pub type LiteralLanguage = EqLanguage<Literal, LiteralSet>;
    pub type ClauseLanguage = OrLanugage<LiteralLanguage, ClauseSet>;
    pub type CubeLanguage = AndLanugage<LiteralLanguage, CubeSet>;
    pub type CnfLanguage = AndLanugage<ClauseLanguage, CnfSet>;
    pub type DnfLanguage = OrLanugage<CubeLanguage, DnfSet>;
    pub type PDnfLanguage = BinOrLanguage<ClauseLanguage, DnfLanguage, PDnfSet>;
    pub type QuantPDnfLanguage = QuantLanguage<PDnfLanguage, QuantPDnfSet>;

    pub fn literal_language(literals: Vec<Literal>) -> Arc<LiteralLanguage> {
        LiteralLanguage::new((), literals, trivial_fmap(), None)
    }

    pub fn clause_language(clause_size: usize, literals: Vec<Literal>) -> Arc<ClauseLanguage> {
        ClauseLanguage::new(literal_language(literals), clause_size, clause_fmap(), None)
    }

    pub fn cube_language(literals: Vec<Literal>) -> Arc<CubeLanguage> {
        CubeLanguage::new(literal_language(literals), (), trivial_fmap(), None)
    }

    pub fn cnf_language(clause_size: usize, literals: Vec<Literal>) -> Arc<CnfLanguage> {
        CnfLanguage::new(
            clause_language(clause_size, literals),
            (),
            trivial_fmap(),
            None,
        )
    }

    pub fn dnf_language(cube_count: usize, literals: Vec<Literal>) -> Arc<DnfLanguage> {
        DnfLanguage::new(cube_language(literals), cube_count, trivial_fmap(), None)
    }

    pub fn pdnf_language(
        clause_size: usize,
        cube_count: usize,
        clause_literals: Vec<Literal>,
        cube_literals: Vec<Literal>,
    ) -> Arc<PDnfLanguage> {
        PDnfLanguage::new(
            (
                clause_language(clause_size, clause_literals),
                dnf_language(cube_count, cube_literals),
            ),
            (),
            pdnf_fmap(),
            None,
        )
    }

    pub fn quant_pdnf_language(
        cfg: Arc<QuantifierConfig>,
        clause_size: usize,
        cube_count: usize,
        clause_literals: Vec<Literal>,
        cube_literals: Vec<Literal>,
    ) -> Arc<QuantPDnfLanguage> {
        QuantLanguage::new(
            pdnf_language(clause_size, cube_count, clause_literals, cube_literals),
            cfg,
            trivial_fmap(),
            None,
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fly::{
        parser::term,
        semantics::{Assignment, Interpretation},
        syntax::{RelationDecl, Signature, Term},
    };
    use std::collections::HashMap;

    fn lit(name: &str, positive: bool) -> Literal {
        Literal(Arc::new(Term::id(name)), positive)
    }

    fn sort(name: &str) -> Sort {
        Sort::Uninterpreted(name.to_string())
    }

    #[test]
    fn test_permutations() {
        let name = |s: &str| s.to_string();
        let term = |s: &str| Term::id(s);

        let from = [vec![name("x1"), name("x2")]];
        let to = [vec![name("x1"), name("x2")]];
        let perms = permutations(&from, &to);
        assert_eq!(
            perms,
            Vec::from_iter([
                HashMap::from_iter([(name("x1"), term("x1")), (name("x2"), term("x2"))]),
                HashMap::from_iter([(name("x1"), term("x2")), (name("x2"), term("x1"))])
            ])
        );

        let from = [vec![name("x")], vec![name("y1"), name("y2")]];
        let to = [vec![name("x1"), name("x2")], vec![name("y2")]];
        let perms = permutations(&from, &to);
        assert_eq!(
            perms,
            Vec::from_iter([
                HashMap::from_iter([
                    (name("x"), term("x")),
                    (name("y1"), term("y1")),
                    (name("y2"), term("y2"))
                ]),
                HashMap::from_iter([
                    (name("x"), term("x")),
                    (name("y1"), term("y2")),
                    (name("y2"), term("y1"))
                ]),
                HashMap::from_iter([
                    (name("x"), term("x1")),
                    (name("y1"), term("y1")),
                    (name("y2"), term("y2"))
                ]),
                HashMap::from_iter([
                    (name("x"), term("x1")),
                    (name("y1"), term("y2")),
                    (name("y2"), term("y1"))
                ]),
                HashMap::from_iter([
                    (name("x"), term("x2")),
                    (name("y1"), term("y1")),
                    (name("y2"), term("y2"))
                ]),
                HashMap::from_iter([
                    (name("x"), term("x2")),
                    (name("y1"), term("y2")),
                    (name("y2"), term("y1"))
                ]),
            ])
        );

        let from = [vec![name("x")], vec![name("a1"), name("a2")]];
        let to = [vec![], vec![name("a2")]];
        let perms = permutations(&from, &to);
        assert_eq!(
            perms,
            Vec::from_iter([
                HashMap::from_iter([
                    (name("x"), term("x")),
                    (name("a1"), term("a1")),
                    (name("a2"), term("a2")),
                ]),
                HashMap::from_iter([
                    (name("x"), term("x")),
                    (name("a1"), term("a2")),
                    (name("a2"), term("a1")),
                ]),
            ])
        );
    }

    #[test]
    fn test_clause() {
        let sig = Signature {
            sorts: vec![],
            relations: vec![
                RelationDecl {
                    mutable: true,
                    name: "a".to_string(),
                    args: vec![],
                    sort: Sort::Bool,
                },
                RelationDecl {
                    mutable: true,
                    name: "b".to_string(),
                    args: vec![],
                    sort: Sort::Bool,
                },
                RelationDecl {
                    mutable: true,
                    name: "c".to_string(),
                    args: vec![],
                    sort: Sort::Bool,
                },
            ],
        };

        let model = |a, b, c| Model {
            signature: sig.clone(),
            universe: vec![],
            interp: vec![
                Interpretation {
                    shape: vec![2],
                    data: vec![a],
                },
                Interpretation {
                    shape: vec![2],
                    data: vec![b],
                },
                Interpretation {
                    shape: vec![2],
                    data: vec![c],
                },
            ],
        };

        let clause = |disj: Vec<Literal>| {
            Or::<Bounded<Literal>>(Arc::new(
                disj.into_iter().map(Bounded::Some).sorted().collect(),
            ))
        };

        let literals = vec![
            lit("a", true),
            lit("a", false),
            lit("b", true),
            lit("b", false),
            lit("c", true),
            lit("c", false),
        ];

        let cl_lang = advanced::clause_language(2, literals);

        let cl = cl_lang.bottom();
        let mut set = advanced::ClauseSet::default();

        let m110 = model(1, 1, 0);
        let m000 = model(0, 0, 0);

        let weakenings: HashSet<_> = cl_lang.weaken_unfiltered(&cl, &m110, &Assignment::new());
        assert_eq!(
            weakenings,
            HashSet::from_iter([
                clause(vec![lit("a", true),]),
                clause(vec![lit("b", true),]),
                clause(vec![lit("c", false),])
            ])
        );

        for w in weakenings {
            assert!(set.get_subsuming(&w).is_empty());
            set.insert(w);
        }

        assert_eq!(set.len(), 3);
        assert!(set.get_unsat(&m110, &Assignment::new()).is_empty());

        let unsat: HashSet<_> = set.get_unsat(&m000, &Assignment::new());
        for u in &unsat {
            set.remove(u);
        }
        assert_eq!(unsat.len(), 2);
        assert_eq!(set.len(), 1);

        let weakenings: HashSet<_> = unsat
            .iter()
            .flat_map(|c| cl_lang.weaken_unfiltered(c, &m000, &Assignment::new()))
            .collect();
        assert_eq!(
            weakenings,
            HashSet::from_iter([
                clause(vec![lit("a", true).into(), lit("a", false)]),
                clause(vec![lit("a", true).into(), lit("b", false)]),
                clause(vec![lit("a", true).into(), lit("c", false)]),
                clause(vec![lit("b", true).into(), lit("a", false)]),
                clause(vec![lit("b", true).into(), lit("b", false)]),
                clause(vec![lit("b", true).into(), lit("c", false)]),
            ])
        );

        let weakenings: HashSet<_> = unsat
            .iter()
            .flat_map(|c| cl_lang.weaken(c, &m000, &Assignment::new()))
            .collect();
        assert_eq!(
            weakenings,
            HashSet::from_iter([
                clause(vec![lit("a", true).into(), lit("b", false)]),
                clause(vec![lit("a", true).into(), lit("c", false)]),
                clause(vec![lit("b", true).into(), lit("a", false)]),
                clause(vec![lit("b", true).into(), lit("c", false)]),
            ])
        );

        set.extend_min(weakenings);
        assert_eq!(set.len(), 3);
    }

    #[test]
    fn test_cube() {
        let sig = Signature {
            sorts: vec![],
            relations: vec![
                RelationDecl {
                    mutable: true,
                    name: "a".to_string(),
                    args: vec![],
                    sort: Sort::Bool,
                },
                RelationDecl {
                    mutable: true,
                    name: "b".to_string(),
                    args: vec![],
                    sort: Sort::Bool,
                },
                RelationDecl {
                    mutable: true,
                    name: "c".to_string(),
                    args: vec![],
                    sort: Sort::Bool,
                },
            ],
        };

        let model = |a, b, c| Model {
            signature: sig.clone(),
            universe: vec![],
            interp: vec![
                Interpretation {
                    shape: vec![2],
                    data: vec![a],
                },
                Interpretation {
                    shape: vec![2],
                    data: vec![b],
                },
                Interpretation {
                    shape: vec![2],
                    data: vec![c],
                },
            ],
        };

        let cube = |conj: Vec<Literal>| {
            And::<Bounded<Literal>>(Arc::new(
                conj.into_iter().map(Bounded::Some).sorted().collect(),
            ))
        };

        let literals = vec![
            lit("a", true),
            lit("a", false),
            lit("b", true),
            lit("b", false),
            lit("c", true),
            lit("c", false),
        ];

        let cb_lang = advanced::cube_language(literals);

        let cb = cb_lang.bottom();
        let mut set = advanced::CubeSet::default();

        let m110 = model(1, 1, 0);
        let m000 = model(0, 0, 0);

        let weakenings: HashSet<_> = cb_lang.weaken_unfiltered(&cb, &m110, &Assignment::new());
        assert_eq!(
            weakenings,
            HashSet::from_iter([cube(vec![lit("a", true), lit("b", true), lit("c", false)])])
        );

        for w in weakenings {
            assert!(set.get_subsuming(&w).is_empty());
            set.insert(w);
        }

        assert_eq!(set.len(), 1);
        assert!(set.get_unsat(&m110, &Assignment::new()).is_empty());

        cb_lang.weaken_set(&mut set, &m000, &Assignment::new());
        assert_eq!(
            set.as_ref(),
            &HashSet::from_iter([cube(vec![lit("c", false)]),])
        );
    }

    #[test]
    fn test_quant_pdnf() {
        let sig = Arc::new(Signature {
            sorts: vec!["T".to_string(), "S".to_string()],
            relations: vec![
                RelationDecl {
                    mutable: true,
                    name: "p".to_string(),
                    args: vec![sort("T")],
                    sort: Sort::Bool,
                },
                RelationDecl {
                    mutable: true,
                    name: "q".to_string(),
                    args: vec![sort("S")],
                    sort: Sort::Bool,
                },
            ],
        });

        let cfg = Arc::new(QuantifierConfig::new(
            sig.clone(),
            vec![Some(Quantifier::Forall), None],
            vec![sort("S"), sort("T")],
            &[2, 2],
        ));

        let model = |t_count: usize, s_count: usize, in_p: Vec<usize>, in_q: Vec<usize>| Model {
            signature: sig.as_ref().clone(),
            universe: vec![t_count, s_count],
            interp: vec![
                Interpretation::new(&vec![t_count, 2], |e| in_p.contains(&e[0]) as usize),
                Interpretation::new(&vec![s_count, 2], |e| in_q.contains(&e[0]) as usize),
            ],
        };

        let literals = ["p(T_1)", "p(T_2)", "q(S_1)", "q(S_2)"]
            .into_iter()
            .flat_map(|a| {
                let t = Arc::new(term(a));
                [Literal(t.clone(), true), Literal(t.clone(), false)]
            })
            .collect_vec();

        let q_lang = advanced::quant_pdnf_language(cfg, 3, 2, literals.clone(), literals);
        let f = q_lang.bottom();

        let m = model(2, 2, vec![1], vec![0, 1]);
        let weakenings = q_lang.weaken(&f, &m, &Assignment::new());
        for w in weakenings.iter().permutations(2) {
            assert!(w[0].eval(&m, &Assignment::new()));
            assert!(!w[0].subsumes(&w[1]) || w[0] == w[1]);
        }
    }
}

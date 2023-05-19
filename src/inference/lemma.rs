// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Handle lemmas used in inference.

use itertools::Itertools;
use std::collections::{HashMap, HashSet};

use crate::{
    fly::semantics::Model,
    fly::syntax::{BinOp, Term},
    inference::{basics::FOModule, quant::QuantifierPrefix, trie::QcnfSet},
    verify::SolverConf,
};

/// An [`Atom`] is referred to via a certain index.
pub type Atom = usize;
/// A [`Literal`] represents an atom, either positive or negated.
/// E.g. atom `i` negated is represented by (i, false).
pub type Literal = (Atom, bool);

// Convert a literal to its corresponding term.
fn literal_as_term(literal: &Literal, atoms: &[Term]) -> Term {
    match literal.1 {
        true => atoms[literal.0].clone(),
        false => Term::negate(atoms[literal.0].clone()),
    }
}

/// Check whether the given [`Literal`] refers to an equality,
/// either negated or unnegated.
fn is_eq(literal: Literal, unnegated: bool, atoms: &[Term]) -> bool {
    literal.1 == unnegated && matches!(atoms[literal.0], Term::BinOp(BinOp::Equals, _, _))
}

/// Check whether the first ordered sequence is a subset of the second.
fn subset<T: Ord>(seq1: &[T], seq2: &[T]) -> bool {
    let mut i2 = 0;
    for t1 in seq1 {
        while i2 < seq2.len() && t1 < &seq2[i2] {
            i2 += 1;
        }

        if i2 >= seq2.len() || t1 > &seq2[i2] {
            return false;
        }
    }

    true
}

/// [`LemmaQf`] defines the basic behavior of the quantifier-free part of lemmas.
pub trait LemmaQf: Clone {
    /// Convert into a CNF structure.
    fn to_cnf(&self) -> Vec<Vec<Literal>>;

    /// Convert into a [`Term`].
    fn to_term(&self, atoms: &[Term]) -> Term;
}

/// [`WeakenQf`] defines how instances of the associated [`LemmaQf`] are weakened.
pub trait WeakenQf<L: LemmaQf>: Clone {
    /// Return the strongest instances of the associated [`LemmaQf`].
    fn strongest(&self) -> Vec<L>;

    /// Return weakenings of the given [`LemmaQf`] which satisfy the given cube.
    ///
    /// For any [`LemmaQf`] satisfying the cube and subsumed by the given [`LemmaQf`],
    /// there should be some [`LemmaQf`] in the returned vector which subsumes it.
    /// All subsumptions here refer to CNF subsumption.
    fn weaken(&self, lemma: &L, cube: &[Literal], atoms: &[Term]) -> Vec<L>;
}

#[derive(Clone, PartialEq, Eq)]
pub struct Cnf(Vec<Vec<Literal>>);

#[derive(Clone)]
pub struct CnfWeaken {
    /// The maximal number of clauses in a CNF formula.
    pub max_clauses: usize,
    /// The maximal number of literals in each clause.
    pub max_literals: usize,
}

impl LemmaQf for Cnf {
    fn to_cnf(&self) -> Vec<Vec<Literal>> {
        self.0.clone()
    }

    fn to_term(&self, atoms: &[Term]) -> Term {
        Term::and(
            self.0
                .iter()
                .map(|cl| Term::or(cl.iter().map(|lit| literal_as_term(lit, atoms)))),
        )
    }
}

impl WeakenQf<Cnf> for CnfWeaken {
    fn strongest(&self) -> Vec<Cnf> {
        vec![Cnf(vec![vec![]])]
    }

    fn weaken(&self, lemma: &Cnf, cube: &[Literal], atoms: &[Term]) -> Vec<Cnf> {
        assert!(!lemma.0.is_empty());

        // If one of the clauses is of maximal size, or is a unit clause of a negated equality,
        // there are no weakenings possible.
        if lemma.0.iter().any(|cl| {
            cl.len() >= self.max_literals || (cl.len() == 1 && is_eq(cl[0], false, atoms))
        }) {
            return vec![];
        }

        // Handle the special case where the lemma is the empty clause.
        if lemma == &Cnf(vec![vec![]]) {
            return cube
                .iter()
                .cloned()
                .combinations(self.max_clauses.min(cube.len()))
                .map(|lits| Cnf(lits.into_iter().map(|lit| vec![lit]).collect_vec()))
                .collect_vec();
        }

        // Weaken each clause by adding a literal from `cube`.
        let weakened_clauses = lemma.0.iter().map(|cl| {
            let mut new_clauses = vec![];
            for i in 0..=cl.len() {
                let lower = if i > 0 { cl[i - 1].0 + 1 } else { 0 };
                let upper = if i < cl.len() { cl[i].0 } else { atoms.len() };

                for atom in lower..upper {
                    // Do not add inequalities to non-empty clauses.
                    if cl.is_empty() || !is_eq(cube[atom], false, atoms) {
                        let mut new_clause = cl.to_vec();
                        new_clause.insert(i, cube[atom]);
                        assert!((1..new_clause.len()).all(|i| new_clause[i - 1] < new_clause[i]));
                        new_clauses.push(new_clause);
                    }
                }
            }

            new_clauses
        });

        // Return all combinations of weakened clauses.
        weakened_clauses
            .into_iter()
            .multi_cartesian_product()
            .map(|mut cls| {
                minimize_subsumed(&mut cls, |cl1, cl2| subset(cl1, cl2));
                Cnf(cls)
            })
            .collect_vec()
    }
}

impl Term {
    /// Compute the names of [`Term::Id`]'s present in the given term.
    ///
    /// Supports only quantifier-free terms.
    pub fn ids(&self) -> HashSet<String> {
        match self {
            Term::Id(name) => HashSet::from([name.clone()]),
            Term::App(_, _, vt) => vt.iter().flat_map(|t| t.ids()).collect(),
            Term::UnaryOp(_, t) => t.ids(),
            Term::BinOp(_, t1, t2) => [t1, t2].iter().flat_map(|t| t.ids()).collect(),
            Term::NAryOp(_, vt) => vt.iter().flat_map(|t| t.ids()).collect(),
            Term::Ite { cond, then, else_ } => {
                [cond, then, else_].iter().flat_map(|t| t.ids()).collect()
            }
            _ => HashSet::new(),
        }
    }
}

/// Minimize a vector of elements using the given subsumption predicate.
pub fn minimize_subsumed<T, S: Fn(&T, &T) -> bool>(v: &mut Vec<T>, subsumes: S) {
    let mut v_new: Vec<T> = vec![];
    for t in v.drain(..) {
        if !v_new.iter().any(|old_t| subsumes(old_t, &t)) {
            v_new.retain(|old_t| !subsumes(&t, old_t));
            v_new.push(t);
        }
    }

    v.append(&mut v_new);
}

/// A quantified CNF formula.
#[derive(Clone, Debug)]
pub struct Qcnf {
    pub prefix: Box<QuantifierPrefix>,
    pub body: Term,
}

impl Qcnf {
    pub fn to_term(&self) -> Term {
        self.prefix.quantify(self.body.clone())
    }
}

/// A [`Frontier`] maintains quantified CNF formulas during invariant inference.
pub struct Frontier<L: LemmaQf, W: WeakenQf<L>> {
    /// The set of lemmas used to sample pre-states when sampling from a transition.
    /// This is referred to as the _frontier_.
    lemmas: QcnfSet<L, W>,
    /// A set of lemmas blocked by the current frontier. That is, any post-state of
    /// a transition from the frontier satisfies `blocked`.
    blocked: QcnfSet<L, W>,
    /// A mapping between each blocked lemma and a core in the frontier that blocks it.
    blocking_cores: HashMap<usize, HashSet<usize>>,
}

impl<L: LemmaQf, W: WeakenQf<L>> Frontier<L, W> {
    /// Create a new frontier from the given set of lemmas.
    pub fn new(qcnf_set: &QcnfSet<L, W>) -> Self {
        Frontier {
            lemmas: qcnf_set.clone(),
            blocked: qcnf_set.clone_empty(),
            blocking_cores: HashMap::new(),
        }
    }

    /// Get the length of the frontier.
    pub fn len(&self) -> usize {
        self.lemmas.len()
    }

    /// Convert the frontier into a vector of terms.    
    pub fn to_terms(&self) -> Vec<Term> {
        self.lemmas
            .qcnfs()
            .iter()
            .map(|q| q.to_term())
            .collect_vec()
    }

    /// Get an initial state which violates one of the given lemmas.
    /// This doesn't use the frontier, only previously blocked lemmas.
    pub fn init_cex(
        &mut self,
        fo: &FOModule,
        conf: &SolverConf,
        lemmas: &QcnfSet<L, W>,
    ) -> Option<Model> {
        for (id, prefix) in &lemmas.prefixes {
            if !self.blocked.subsumes(prefix, &lemmas.qcnf_clauses(id), 0) {
                let term = lemmas.qcnf(id).to_term();
                if let Some(model) = fo.init_cex(conf, &term) {
                    return Some(model);
                } else {
                    let new_id = self.blocked.add(prefix.clone(), lemmas.bodies[id].clone());
                    self.blocking_cores
                        .insert(new_id, self.lemmas.prefixes.keys().copied().collect());
                }
            }
        }

        None
    }

    /// Get an post-state of the frontier which violates one of the given lemmas.
    pub fn trans_cex(
        &mut self,
        fo: &FOModule,
        conf: &SolverConf,
        lemmas: &QcnfSet<L, W>,
    ) -> Option<Model> {
        let pre_terms = self.to_terms();
        for (id, prefix) in &lemmas.prefixes {
            if !self.blocked.subsumes(prefix, &lemmas.qcnf_clauses(id), 0) {
                let term = lemmas.qcnf(id).to_term();
                if let Some((_, model)) = fo.trans_cex(conf, &pre_terms, &term) {
                    return Some(model);
                } else {
                    let new_id = self.blocked.add(prefix.clone(), lemmas.bodies[id].clone());
                    self.blocking_cores
                        .insert(new_id, self.lemmas.prefixes.keys().copied().collect());
                }
            }
        }

        None
    }

    /// Advance the fontier using the new lemmas.
    ///
    /// Advancing a lemma involves replacing it with the new lemmas subsumed by it.
    /// If there are none, the lemma is dropped. If there is only one, the original lemma is substituted.
    /// When advancing the entire frontier, we always do these zero-cost replacements,
    /// and if `grow` is enabled, and there are no such substitions available, we advance
    /// the lemma that would cause the least growth in the length of the frontier.
    ///
    /// Return whether such an advancement was possible.
    pub fn advance(&mut self, new_lemmas: &QcnfSet<L, W>, mut grow: bool) -> bool {
        // If there are no lemmas in the frontier, it cannot be advanced.
        if self.lemmas.len() == 0 {
            return false;
        }

        // Find all lemmas in the frontier (parents) which have been weakened in the new lemmas.
        // These are precisely the lemmas in the fontier which are not subsumed by new lemmas.
        let weakened_parents: HashSet<usize> = self
            .lemmas
            .prefixes
            .keys()
            .filter(|id| {
                !new_lemmas.subsumes(&self.lemmas.prefixes[id], &self.lemmas.qcnf_clauses(id), 0)
            })
            .cloned()
            .collect();

        // Initialize the mapping from parents to their weakenings (children).
        let mut children: HashMap<usize, HashSet<usize>> = weakened_parents
            .iter()
            .map(|id| (*id, HashSet::new()))
            .collect();

        // Compute the mapping from children to parents.
        let mut parents: HashMap<usize, HashSet<usize>> = new_lemmas
            .prefixes
            .iter()
            .map(|(&id, prefix)| {
                let p = self
                    .lemmas
                    .subsuming(prefix, &new_lemmas.qcnf_clauses(&id), 0, None);

                (id, p)
            })
            .collect();

        // Compute the `children` mapping.
        for (id, ps) in &parents {
            for parent in ps {
                if let Some(ch) = children.get_mut(parent) {
                    ch.insert(*id);
                }
            }
        }

        let mut advanced = false;
        // Given a children and parents mapping, compute the parent with the least unique children,
        // i.e. the least number of children which are uniquely theirs.
        let min_unique = |children_local: &HashMap<usize, HashSet<usize>>,
                          parents_local: &HashMap<usize, HashSet<usize>>|
         -> Option<(usize, HashSet<usize>)> {
            let mut unique_children = children_local.clone();
            for (_, ch) in unique_children.iter_mut() {
                ch.retain(|id| parents_local[id].len() == 1);
            }

            unique_children
                .into_iter()
                .min_by_key(|(id, ch)| (ch.len(), *id))
        };

        let mut min = min_unique(&children, &parents);
        while min.is_some() && (grow || min.as_ref().unwrap().1.is_empty()) {
            // This is the replaced lemma.
            let (id, ch) = &min.unwrap();

            // The frontier is advanced.
            advanced = true;
            // Never grow twice.
            grow = false;

            // Remove the lemma from the frontier.
            self.lemmas.remove(id);
            // Remove blocking cores that contain the replaced lemma.
            let removed: Vec<usize> = self
                .blocking_cores
                .keys()
                .cloned()
                .filter(|i| self.blocking_cores[i].contains(id))
                .collect();
            for r in &removed {
                self.blocked.remove(r);
                self.blocking_cores.remove(r);
            }

            // Add the lemma's unique children to the frontier.
            for new_id in ch {
                self.lemmas.add(
                    new_lemmas.prefixes[new_id].clone(),
                    new_lemmas.bodies[new_id].clone(),
                );
                for p in &parents.remove(new_id).unwrap() {
                    children.get_mut(p).unwrap().remove(new_id);
                }
            }
            children.remove(id);

            min = min_unique(&children, &parents);
        }

        advanced
    }
}

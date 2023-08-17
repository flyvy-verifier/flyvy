// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use fly::{
    semantics::{Assignment, Model},
    syntax::{BinOp, Term},
    term::subst::{substitute_qf, Substitution},
};
use itertools::Itertools;

use crate::{
    basics::{FOModule, InferenceConfig},
    hashmap::HashSet,
    lemma::ids,
    quant::{QuantifierConfig, QuantifierPrefix},
};
use solver::basics::BasicSolver;

use rayon::prelude::*;

/// An [`Atom`] is referred to via a certain index.
pub type Atom = Term;
/// A [`Literal`] represents an atom, either positive or negated.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Literal(Atom, bool);

pub struct Atoms(HashSet<Atom>);

fn substitute(atom: &Atom, substitution: &Substitution) -> Atom {
    match &atom {
        Term::BinOp(BinOp::Equals, t1, t2) => {
            let t1_sub = substitute_qf(t1, substitution);
            let t2_sub = substitute_qf(t2, substitution);
            if t1_sub <= t2_sub {
                Term::equals(t1_sub, t2_sub)
            } else {
                Term::equals(t2_sub, t1_sub)
            }
        }
        _ => substitute_qf(atom, substitution),
    }
}

impl Literal {
    pub fn ids(&self) -> HashSet<String> {
        ids(&self.0)
    }

    pub fn negate(&self) -> Self {
        Self(self.0.clone(), !self.1)
    }

    pub fn substitute(&self, substitution: &Substitution) -> Self {
        Self(substitute(&self.0, substitution), self.1)
    }

    pub fn is_neq(&self) -> bool {
        matches!(self.0, Term::BinOp(BinOp::Equals, _, _)) && !self.1
    }
}

impl From<&Literal> for Term {
    fn from(value: &Literal) -> Self {
        match value.1 {
            true => value.0.clone(),
            false => Term::not(&value.0),
        }
    }
}

impl Atoms {
    pub fn new<B: BasicSolver>(infer_cfg: &InferenceConfig, solver: &B, fo: &FOModule) -> Self {
        let univ_prefix = infer_cfg.cfg.as_universal();
        let atoms: HashSet<Term> = infer_cfg
            .cfg
            .atoms(infer_cfg.nesting, infer_cfg.include_eq)
            .into_par_iter()
            .filter(|t| {
                let univ_t = univ_prefix.quantify(t.clone());
                let univ_not_t = univ_prefix.quantify(Term::negate(t.clone()));

                fo.implication_cex(solver, &[], &univ_t).is_cex()
                    && fo.implication_cex(solver, &[], &univ_not_t).is_cex()
            })
            // Make sure all equality atoms "t1 = t2" satisfy t1 <= t2.
            // This is done to allow substitutions without creating equivalent equalities.
            .map(|a| match a {
                Term::BinOp(BinOp::Equals, t1, t2) => {
                    if t1 <= t2 {
                        Term::BinOp(BinOp::Equals, t1, t2)
                    } else {
                        Term::BinOp(BinOp::Equals, t2, t1)
                    }
                }
                _ => a,
            })
            .collect();

        Self(atoms)
    }

    pub fn contains(&self, atom: &Atom) -> bool {
        self.0.contains(atom)
    }

    pub fn contains_literal(&self, literal: &Literal) -> bool {
        self.0.contains(&literal.0)
    }

    pub fn restrict<R>(&self, r: R) -> Self
    where
        R: Fn(&Term) -> bool,
    {
        Self(self.0.iter().filter(|a| r(a)).cloned().collect())
    }

    pub fn restrict_by_prefix(&self, config: &QuantifierConfig, prefix: &QuantifierPrefix) -> Self {
        let config_vars = config.all_vars();
        let prefix_vars = prefix.all_vars();
        let difference: HashSet<String> = config_vars.difference(&prefix_vars).cloned().collect();

        self.restrict(|a| ids(a).is_disjoint(&difference))
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.len() == 0
    }

    pub fn cube(&self, model: &Model, assignment: &Assignment) -> Vec<Literal> {
        self.0
            .iter()
            .map(|a| Literal(a.clone(), model.eval_assign(a, assignment.clone()) == 1))
            .collect_vec()
    }

    pub fn neg_cube(&self, model: &Model, assignment: &Assignment) -> Vec<Literal> {
        self.0
            .iter()
            .map(|a| Literal(a.clone(), model.eval_assign(a, assignment.clone()) == 0))
            .collect_vec()
    }

    pub fn atoms_containing_vars(&self, vars: &HashSet<String>) -> usize {
        self.0.iter().filter(|a| !ids(a).is_disjoint(vars)).count()
    }
}

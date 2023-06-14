// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use crate::{
    fly::{
        semantics::{Assignment, Model},
        syntax::{BinOp, Term},
    },
    inference::hashmap::{HashMap, HashSet},
    term::subst::{substitute_qf, Substitution},
};
use itertools::Itertools;
use std::sync::Arc;

use super::quant::{QuantifierConfig, QuantifierPrefix};

/// An [`Atom`] is referred to via a certain index.
pub type Atom = usize;
/// A [`Literal`] represents an atom, either positive or negated.
/// E.g. atom `i` negated is represented by (i, false).
pub type Literal = (Atom, bool);

pub fn restrict_by_prefix(
    atoms: &Arc<Atoms>,
    config: &QuantifierConfig,
    prefix: &QuantifierPrefix,
) -> RestrictedAtoms {
    let config_vars = config.all_vars();
    let prefix_vars = prefix.all_vars();
    let difference: HashSet<String> = config_vars.difference(&prefix_vars).cloned().collect();

    restrict(atoms, |a| a.ids().is_disjoint(&difference))
}

pub fn restrict<R>(atoms: &Arc<Atoms>, r: R) -> RestrictedAtoms
where
    R: Fn(&Term) -> bool,
{
    RestrictedAtoms {
        atoms: atoms.clone(),
        allowed: atoms
            .to_term
            .iter()
            .enumerate()
            .filter(|(_, a)| r(a))
            .map(|(i, _)| i)
            .collect(),
    }
}

pub struct Atoms {
    pub to_term: Vec<Term>,
    pub to_index: HashMap<Term, usize>,
}

impl Atoms {
    pub fn new(to_term: Vec<Term>) -> Self {
        let to_index = to_term
            .iter()
            .enumerate()
            .map(|(index, term)| (term.clone(), index))
            .collect();

        Self { to_term, to_index }
    }
}

#[derive(Clone)]
pub struct RestrictedAtoms {
    pub atoms: Arc<Atoms>,
    pub allowed: HashSet<usize>,
}

impl RestrictedAtoms {
    pub fn len(&self) -> usize {
        self.allowed.len()
    }

    pub fn is_eq(&self, atom: usize) -> bool {
        matches!(self.atoms.to_term[atom], Term::BinOp(BinOp::Equals, _, _))
    }

    pub fn substitute(&self, atom: usize, substitution: &Substitution) -> Option<usize> {
        match &self.atoms.to_term[atom] {
            Term::BinOp(BinOp::Equals, t1, t2) => {
                let t1_sub = substitute_qf(t1, substitution);
                let t2_sub = substitute_qf(t2, substitution);

                let eq12 = Term::equals(t1_sub.clone(), t2_sub.clone());
                let eq21 = Term::equals(t2_sub, t1_sub);

                let mut res = None;

                if let Some(i) = self.atoms.to_index.get(&eq12) {
                    if self.allowed.contains(i) {
                        res = Some(*i);
                    }
                }

                if let Some(i) = self.atoms.to_index.get(&eq21) {
                    if self.allowed.contains(i) {
                        res = Some(*i);
                    }
                }

                res
            }
            _ => self
                .atoms
                .to_index
                .get(&substitute_qf(&self.atoms.to_term[atom], substitution))
                .filter(|&i| self.allowed.contains(i))
                .copied(),
        }
    }

    pub fn cube(&self, model: &Model, assignment: &Assignment) -> Vec<Literal> {
        self.allowed
            .iter()
            .map(|&a| {
                (
                    a,
                    model.eval_assign(&self.atoms.to_term[a], assignment.clone()) == 1,
                )
            })
            .collect_vec()
    }

    pub fn neg_cube(&self, model: &Model, assignment: &Assignment) -> Vec<Literal> {
        self.allowed
            .iter()
            .map(|&a| {
                (
                    a,
                    model.eval_assign(&self.atoms.to_term[a], assignment.clone()) == 0,
                )
            })
            .collect_vec()
    }

    pub fn to_term(&self, literal: &Literal) -> Option<Term> {
        if self.allowed.contains(&literal.0) {
            let a = self.atoms.to_term[literal.0].clone();

            Some(match literal.1 {
                true => a,
                false => Term::negate(a),
            })
        } else {
            None
        }
    }
}

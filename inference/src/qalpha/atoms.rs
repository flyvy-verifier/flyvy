// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use fly::{
    semantics::{Assignment, Model},
    syntax::{BinOp, Signature, Term},
    term::subst::{substitute_qf, Substitution},
};

use crate::{
    basics::{FOModule, QalphaConfig},
    hashmap::HashSet,
    qalpha::{
        lemma::ids,
        quant::{QuantifierConfig, QuantifierPrefix},
    },
};
use solver::basics::BasicSolver;

use rayon::prelude::*;
use std::sync::Arc;

/// An [`Atom`] is referred to via a certain index.
pub type Atom = Arc<Term>;
/// A [`Literal`] represents an atom, either positive or negated.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Literal(pub Atom, pub bool);
pub type Literals = HashSet<Literal>;

fn substitute(atom: &Atom, substitution: &Substitution) -> Atom {
    Arc::new(match atom.as_ref() {
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
    })
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
        matches!(self.0.as_ref(), Term::BinOp(BinOp::Equals, _, _)) && !self.1
    }
}

impl From<&Literal> for Term {
    fn from(value: &Literal) -> Self {
        match value.1 {
            true => value.0.as_ref().clone(),
            false => Term::not(value.0.as_ref()),
        }
    }
}

pub fn generate_literals<B: BasicSolver>(
    infer_cfg: &QalphaConfig,
    signature: &Signature,
    solver: &B,
    fo: &FOModule,
) -> Literals {
    let univ_prefix = infer_cfg.cfg.as_universal();
    infer_cfg
        .cfg
        .atoms(signature, infer_cfg.nesting, infer_cfg.include_eq)
        .into_par_iter()
        .filter(|t| {
            let univ_t = univ_prefix.quantify(signature, t.clone());
            let univ_not_t = univ_prefix.quantify(signature, Term::negate(t.clone()));

            fo.implication_cex(solver, &[], &univ_t, None, false)
                .is_cex()
                && fo
                    .implication_cex(solver, &[], &univ_not_t, None, false)
                    .is_cex()
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
        .flat_map(|a| {
            let lit_pos = Literal(Arc::new(a), true);
            let lit_neg = lit_pos.negate();
            [lit_pos, lit_neg]
        })
        .collect()
}

pub fn sat_literals(literals: &Literals, model: &Model, assignment: &Assignment) -> Literals {
    literals
        .iter()
        .filter(|lit| (model.eval_assign(&lit.0, assignment.clone()) == 1) == lit.1)
        .cloned()
        .collect()
}

pub fn restrict_by_prefix(
    literals: &Literals,
    config: &QuantifierConfig,
    prefix: &QuantifierPrefix,
) -> Literals {
    let config_vars = config.all_vars();
    let prefix_vars = prefix.all_vars();
    let difference: HashSet<String> = config_vars.difference(&prefix_vars).cloned().collect();

    literals
        .iter()
        .filter(|lit| lit.ids().is_disjoint(&difference))
        .cloned()
        .collect()
}

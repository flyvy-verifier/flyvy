// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use crate::{
    fly::syntax::{BinOp, NOp, Term, UOp},
    inference::lemma::LemmaQF,
    term::subst::{substitute_qf, Substitution},
};

/// A pDNF is a disjunction of literals and cubes, with some limit on the number
/// of cubes. An optional limit for the number of literals can also be provided.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(clippy::upper_case_acronyms)]
pub struct PDNF {
    n_cubes: usize,
    n_literals: Option<usize>,
    literals: Vec<Term>,
    cubes: Vec<Vec<Term>>,
}

impl PDNF {
    /// Get a pDNF formula which is equivalent to false.
    pub fn get_false(n_cubes: usize, n_literals: Option<usize>) -> Self {
        PDNF {
            n_cubes,
            n_literals,
            literals: vec![],
            cubes: vec![],
        }
    }

    /// Add a literal to the pDNF, if limit not reached.
    fn add_literal(&self, literal: Term) -> Option<PDNF> {
        if let Term::UnaryOp(UOp::Not, arg) = &literal {
            if let Term::BinOp(BinOp::Equals, _, _) = **arg {
                return None;
            }
        }

        let mut literals = vec![literal];
        let mut pdnf = self.clone();

        while let Some(literal) = literals.pop() {
            if pdnf.literals.contains(&literal) {
                continue;
            }

            let neg_lit = literal.flip();
            if pdnf.literals.contains(&neg_lit)
                || (pdnf.n_literals.is_some() && pdnf.literals.len() >= pdnf.n_literals.unwrap())
            {
                return None;
            }

            pdnf.cubes.retain(|c| !c.contains(&literal));
            for c in pdnf.cubes.iter_mut() {
                c.retain(|t| *t != neg_lit);
            }

            let new_lits;
            (new_lits, pdnf.cubes) = pdnf.cubes.into_iter().partition(|c| c.len() == 1);
            pdnf.literals.push(literal);

            for mut v in new_lits.into_iter() {
                literals.push(v.pop().unwrap());
            }
        }

        Some(pdnf)
    }

    /// Add a cube to the pDNF. (Ignores cube limit -- see [`PDNF::weaken`].)
    fn add_cube(&self, mut cube: Vec<Term>) -> Option<PDNF> {
        if cube.iter().any(|t| self.literals.contains(t)) {
            return Some(self.clone());
        }

        cube.retain(|t| !self.literals.contains(&t.flip()));

        if self
            .cubes
            .iter()
            .any(|c| c.iter().all(|t| cube.contains(t)))
        {
            return Some(self.clone());
        }

        match cube.len() {
            0 => None,
            1 => self.add_literal(cube.pop().unwrap()),
            _ => {
                let mut pdnf = self.clone();
                pdnf.cubes.retain(|c| !cube.iter().all(|t| c.contains(t)));
                pdnf.cubes.push(cube);
                Some(pdnf)
            }
        }
    }

    // For testing. No correctness checks are performed.
    #[allow(dead_code)]
    fn from_dnf(n_cubes: usize, n_literals: Option<usize>, t: &Term) -> Self {
        let mut pdnf = PDNF {
            n_cubes,
            n_literals,
            literals: vec![],
            cubes: vec![],
        };
        if let Term::NAryOp(NOp::Or, v_or) = t {
            for c in v_or {
                if let Term::NAryOp(NOp::And, v_and) = c {
                    pdnf.cubes.push(v_and.to_vec());
                } else {
                    pdnf.literals.push(c.clone());
                }
            }
        } else if let Term::NAryOp(NOp::And, v_and) = t {
            pdnf.cubes.push(v_and.to_vec());
        } else {
            pdnf.literals.push(t.clone());
        }

        assert!(pdnf.cubes.len() <= n_cubes);

        pdnf
    }

    /// Return whether the pDNF is subsumption-equivalent to another.
    #[allow(dead_code)]
    fn equiv(&self, other: &Self) -> bool {
        self.subsumes(other) && other.subsumes(self)
    }
}

impl LemmaQF for PDNF {
    // X subsumes Y iff for all c in X, there exists c' in Y,
    // such that c is a superset of c'.
    fn subsumes(&self, other: &Self) -> bool {
        assert_eq!(self.n_cubes, other.n_cubes);
        self.literals.iter().all(|t| other.literals.contains(t))
            && self.cubes.iter().all(|c| {
                c.iter().any(|t| other.literals.contains(t))
                    || other
                        .cubes
                        .iter()
                        .any(|c_other| c_other.iter().all(|t| c.contains(t)))
            })
    }

    fn weaken(&self, cube: Vec<Term>) -> Vec<Self> {
        // Add the new cube.
        let pdnf = match self.add_cube(cube.into_iter().collect()) {
            Some(p) => p,
            None => return vec![],
        };

        if pdnf.cubes.len() <= self.n_cubes {
            return vec![pdnf];
        }

        assert_eq!(pdnf.cubes.len(), self.n_cubes + 1);

        let mut weakened = vec![];
        // Try to reduce number of cubes.
        for i in 0..=self.n_cubes {
            // Weaken by turning a cube into a literal.
            for lit in pdnf.cubes[i].iter().cloned() {
                if let Some(p) = pdnf.add_literal(lit) {
                    weakened.push(p);
                }
            }

            // Weaken by intersecting a cube.
            for j in i + 1..=self.n_cubes {
                let intersection = pdnf.cubes[i]
                    .iter()
                    .filter(|&t| pdnf.cubes[j].contains(t))
                    .cloned()
                    .collect();
                if let Some(p) = pdnf.add_cube(intersection) {
                    weakened.push(p);
                }
            }
        }

        weakened
    }

    fn substitute(&self, substitution: &Substitution) -> Self {
        PDNF {
            n_cubes: self.n_cubes,
            n_literals: self.n_literals,
            literals: self
                .literals
                .iter()
                .map(|t| substitute_qf(t, substitution))
                .collect(),
            cubes: self
                .cubes
                .iter()
                .map(|c| c.iter().map(|t| substitute_qf(t, substitution)).collect())
                .collect(),
        }
    }

    fn to_term(&self) -> Term {
        let mut or_terms: Vec<Term> = self.literals.to_vec();
        or_terms.append(
            &mut self
                .cubes
                .iter()
                .map(|c| {
                    if c.is_empty() {
                        Term::Literal(true)
                    } else {
                        Term::NAryOp(NOp::And, c.to_vec())
                    }
                })
                .collect(),
        );

        if or_terms.is_empty() {
            Term::Literal(false)
        } else {
            Term::NAryOp(NOp::Or, or_terms)
        }
    }
}

#[cfg(test)]
#[allow(clippy::redundant_clone)]
mod tests {
    use super::*;
    use crate::fly::parser::term;

    #[test]
    fn test_add_literal_add_cube() {
        let p1 = PDNF::from_dnf(2, None, &term("a | !b | (c & d) | (!d & e & !f & g)"));
        let p1_add_nc = PDNF::from_dnf(2, None, &term("a | !b | !c | d | (e & !f & g)"));
        let p1_add_nd = PDNF::from_dnf(2, None, &term("a | !b | c | !d"));
        let p1_add_e_nf = PDNF::from_dnf(2, None, &term("a | !b | (c & d) | (e & !f)"));

        let p2 = PDNF::from_dnf(3, None, &term("a | !b | (c & d) | (!d & c)"));
        let p2_add_nd_ne =
            PDNF::from_dnf(3, None, &term("a | !b | (c & d) | (!d & c) | (!d & !e)"));
        let p3 = PDNF::from_dnf(3, None, &term("a | !b | (c & d) | (!d & e) | (!d & !e)"));

        let a = term("a");
        let b = term("b");
        let c = term("c");
        let d = term("d");
        let e = term("e");
        let f = term("f");

        assert!(p1.add_literal(a.clone()).unwrap().equiv(&p1));
        assert_eq!(p1.add_literal(a.flip()), None);
        assert_eq!(p1.add_literal(b.clone()), None);
        assert!(p1.add_literal(b.flip()).unwrap().equiv(&p1));

        assert!(p1.add_literal(c.flip()).unwrap().equiv(&p1_add_nc));
        assert!(p1.add_literal(d.flip()).unwrap().equiv(&p1_add_nd));

        assert!(p1
            .add_cube(vec![b.flip(), c.clone(), d.clone()].into_iter().collect())
            .unwrap()
            .equiv(&p1));
        assert!(p1
            .add_cube(vec![a.flip(), c.clone(), d.clone()].into_iter().collect())
            .unwrap()
            .equiv(&p1));

        assert!(p1
            .add_cube(vec![b.clone(), c.flip(), a.flip()].into_iter().collect())
            .unwrap()
            .equiv(&p1_add_nc));
        assert!(p1
            .add_cube(vec![b.clone(), e.clone(), f.flip()].into_iter().collect())
            .unwrap()
            .equiv(&p1_add_e_nf));

        assert_eq!(
            p2.add_cube(vec![a.flip(), b.clone(), c.flip()].into_iter().collect()),
            None
        );
        assert_eq!(
            p3.add_cube(vec![a.flip(), b.clone(), c.flip()].into_iter().collect()),
            None
        );

        assert!(p2
            .add_cube(vec![a.flip(), d.flip(), e.flip()].into_iter().collect())
            .unwrap()
            .equiv(&p2_add_nd_ne));
    }

    #[test]
    fn test_subsumes_weaken() {
        let p1 = PDNF::from_dnf(2, None, &term("a | b | (c & d) | (e & f & g)"));
        let p2 = PDNF::from_dnf(2, None, &term("a | b | d | (!e & f) | (f & g)"));

        let c1 = vec![
            term("!a"),
            term("!b"),
            term("!c"),
            term("d"),
            term("e"),
            term("f"),
            term("!g"),
        ];
        let mut p_c1 = PDNF::get_false(2, None);
        p_c1.cubes.push(c1.to_vec());

        assert!(p1.subsumes(&p2));
        assert!(!p2.subsumes(&p1));
        assert!(!p_c1.subsumes(&p1));
        assert!(p_c1.subsumes(&p2));

        // Subsumption is reflexive
        assert!(p1.subsumes(&p1));
        assert!(p2.subsumes(&p2));

        // Simple cases
        assert!(p1.subsumes(&p2));
        assert!(!p2.subsumes(&p1));

        let p1_w = p1.weaken(c1.clone());
        let p2_w = p2.weaken(c1);

        // Check if weakened
        for p in p1_w.iter() {
            assert!(p_c1.subsumes(p));
        }

        assert!(p2_w.len() == 1 && p2_w[0] == p2);
        assert!(p1_w.iter().any(|p| p.subsumes(&p2)));
    }
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Implement simple components, lemma domains and data structures for use in inference.

use itertools::Itertools;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::sync::{Arc, Mutex, RwLock};

use crate::{
    fly::semantics::Model,
    fly::syntax::Term,
    inference::{
        atoms::{Literal, RestrictedAtoms},
        basics::{FOModule, InferenceConfig},
        hashmap::{HashMap, HashSet},
        subsume::OrderSubsumption,
        weaken::{LemmaQf, LemmaSet, WeakenLemmaSet},
    },
    solver::SolverConf,
    term::subst::Substitution,
};

use rayon::prelude::*;

use super::basics::TransCexResult;
use super::hashmap;
use super::quant::{count_exists, QuantifierPrefix};

fn clauses_cubes_count(atoms: usize, len: usize) -> usize {
    ((atoms - len + 1)..=atoms).product::<usize>() * 2_usize.pow(len as u32)
}

#[derive(Clone)]
pub struct LemmaCnf {
    /// The maximal number of clauses in a CNF formula.
    pub clauses: usize,
    /// The maximal number of literals in each clause.
    pub clause_size: usize,
    atoms: Arc<RestrictedAtoms>,
}

impl LemmaQf for LemmaCnf {
    type Base = Vec<Vec<Literal>>;

    fn base_from_clause(&self, clause: &[Literal]) -> Self::Base {
        vec![Vec::from(clause)]
    }

    fn substitute(&self, base: &Self::Base, substitution: &Substitution) -> Option<Self::Base> {
        let mut new_base = vec![];
        for clause in base {
            let mut new_clause = vec![];
            for literal in clause {
                if let Some(a) = self.atoms.substitute(literal.0, substitution) {
                    new_clause.push((a, literal.1));
                } else {
                    return None;
                }
            }
            new_base.push(new_clause);
        }

        Some(new_base)
    }

    fn ids(&self, base: &Self::Base) -> HashSet<String> {
        base.iter()
            .flat_map(|clause| {
                clause
                    .iter()
                    .flat_map(|literal| self.atoms.to_term(literal).unwrap().ids())
            })
            .collect()
    }

    fn base_to_term(&self, base: &Self::Base) -> Term {
        Term::and(base.iter().map(|clause| {
            Term::or(
                clause
                    .iter()
                    .map(|literal| self.atoms.to_term(literal).unwrap()),
            )
        }))
    }

    fn new(
        cfg: &InferenceConfig,
        atoms: Arc<RestrictedAtoms>,
        non_universal_vars: HashSet<String>,
    ) -> Self {
        Self {
            clauses: if non_universal_vars.is_empty() {
                1
            } else {
                cfg.clauses
                    .expect("Maximum number of clauses not provided.")
            },
            clause_size: cfg
                .clause_size
                .expect("Maximum number of literals per clause not provided."),
            atoms,
        }
    }

    fn strongest(&self) -> Vec<Self::Base> {
        vec![vec![vec![]]]
    }

    fn weaken<I>(&self, base: Self::Base, cube: &[Literal], ignore: I) -> Vec<Self::Base>
    where
        I: Fn(&Self::Base) -> bool,
    {
        assert!(!base.is_empty());

        // Handle the special case where the lemma is the empty clause.
        if base == vec![vec![]] {
            return cube
                .iter()
                .cloned()
                .combinations(self.clauses.min(cube.len()))
                .map(|lits| lits.into_iter().map(|lit| vec![lit]).collect_vec())
                .collect_vec();
        }

        // Weaken each clause by adding a literal from `cube`.
        let weakened_clauses = base.into_iter().map(|cl| {
            assert!(!cl.is_empty());

            let cl_lits: HashSet<(usize, bool)> = cl.iter().cloned().collect();
            if cube.iter().any(|lit| cl_lits.contains(lit)) {
                vec![cl]
            } else if cl.len() >= self.clause_size {
                vec![]
            } else {
                let mut new_clauses = vec![];

                for lit in cube
                    .iter()
                    .filter(|lit| !cl_lits.contains(&(lit.0, !lit.1)))
                {
                    // Do not add inequalities to non-empty clauses.
                    if !self.atoms.is_eq(lit.0) || lit.1 {
                        let mut new_clause = cl.to_vec();
                        new_clause.push(*lit);
                        new_clauses.push(new_clause);
                    }
                }

                new_clauses
            }
        });

        // Return all combinations of weakened clauses.
        weakened_clauses
            .into_iter()
            .multi_cartesian_product()
            .filter(|b| !ignore(b))
            .collect_vec()
    }

    fn approx_space_size(&self) -> usize {
        let atoms = self.atoms.len();
        let clauses: usize = (0..=self.clause_size)
            .map(|len| clauses_cubes_count(atoms, len))
            .sum();

        ((clauses - self.clauses + 1)..=clauses).product()
    }

    fn sub_spaces(&self) -> Vec<Self> {
        (1..=self.clauses)
            .map(|clauses| Self {
                clauses,
                clause_size: self.clause_size,
                atoms: self.atoms.clone(),
            })
            .collect_vec()
    }

    fn contains(&self, other: &Self) -> bool {
        self.clauses >= other.clauses && self.clause_size >= other.clause_size
    }
}

#[derive(Clone)]
pub struct LemmaPDnfNaive {
    pub cubes: usize,
    pub cube_size: usize,
    pub non_unit: usize,
    atoms: Arc<RestrictedAtoms>,
}

impl LemmaPDnfNaive {
    fn unit_normalize(
        &self,
        mut base: <Self as LemmaQf>::Base,
        literal: Literal,
    ) -> Option<<Self as LemmaQf>::Base> {
        base = base
            .into_iter()
            .filter_map(|mut cb| {
                if cb.contains(&literal) {
                    None
                } else {
                    cb.retain(|lit| (lit.0, !lit.1) != literal);
                    Some(cb)
                }
            })
            .collect_vec();

        if base.iter().any(|cb| cb.is_empty()) {
            None
        } else {
            Some(base)
        }
    }

    fn add_unit(
        &self,
        mut base: <Self as LemmaQf>::Base,
        mut literal: Literal,
    ) -> Option<<Self as LemmaQf>::Base> {
        let mut literals = HashSet::default();

        loop {
            if self.atoms.is_eq(literal.0) && !literal.1 {
                return None;
            }

            match self.unit_normalize(base, literal) {
                Some(new_base) => {
                    base = new_base;
                    literals.insert(literal);
                }
                None => return None,
            }

            match base.iter().find_position(|v| v.len() == 1) {
                Some((i, _)) => literal = base.remove(i).pop().unwrap(),
                None => break,
            }
        }

        if literals.len() + base.len() <= self.cubes {
            for lit in literals {
                base.push(vec![lit]);
            }

            Some(base)
        } else {
            None
        }
    }

    fn add_combinations(
        &self,
        base: <Self as LemmaQf>::Base,
        cube: &[Literal],
    ) -> Vec<<Self as LemmaQf>::Base> {
        let units: HashSet<Literal> = base
            .iter()
            .filter(|cb| cb.len() == 1)
            .map(|cb| cb[0])
            .collect();

        if cube.iter().any(|lit| units.contains(lit)) {
            return vec![base];
        }

        let cube = cube
            .iter()
            .filter(|lit| !units.contains(&(lit.0, !lit.1)))
            .cloned()
            .collect_vec();
        let cube_len = cube.len();

        match cube_len {
            0 => vec![],
            1 => Vec::from_iter(self.add_unit(base, cube[0])),
            _ => {
                if base.len() < self.cubes {
                    cube.into_iter()
                        .combinations(self.cube_size.min(cube_len))
                        .map(|cb| {
                            let mut new_base = base.clone();
                            new_base.push(cb);
                            new_base
                        })
                        .collect_vec()
                } else {
                    vec![]
                }
            }
        }
    }

    fn intersect_cubes(
        &self,
        base: <Self as LemmaQf>::Base,
        cube: &[Literal],
    ) -> Vec<<Self as LemmaQf>::Base> {
        let mut cube: HashSet<Literal> = HashSet::from_iter(cube.iter().cloned());
        let mut non_units = vec![];
        for (i, cb) in base.iter().enumerate() {
            match cb.len() {
                1 => {
                    if cube.contains(&cb[0]) {
                        return vec![base];
                    } else {
                        cube.remove(&(cb[0].0, !cb[0].1));
                    }
                }
                _ => non_units.push(i),
            }
        }

        let mut intersected = vec![];
        for i in non_units {
            let intersection = base[i]
                .iter()
                .filter(|&lit| cube.contains(lit))
                .cloned()
                .collect_vec();
            match intersection.len() {
                0 | 1 => (),
                _ => {
                    let mut new_base = base.clone();
                    new_base[i] = intersection;
                    intersected.push(new_base);
                }
            }
        }

        intersected
    }
}

impl LemmaQf for LemmaPDnfNaive {
    type Base = Vec<Vec<Literal>>;

    fn base_from_clause(&self, clause: &[Literal]) -> Self::Base {
        clause.iter().map(|lit| vec![*lit]).collect_vec()
    }

    fn substitute(&self, base: &Self::Base, substitution: &Substitution) -> Option<Self::Base> {
        let mut new_base = vec![];
        for cube in base {
            let mut new_cube = vec![];
            for literal in cube {
                if let Some(a) = self.atoms.substitute(literal.0, substitution) {
                    new_cube.push((a, literal.1));
                } else {
                    return None;
                }
            }
            new_base.push(new_cube);
        }

        Some(new_base)
    }

    fn ids(&self, base: &Self::Base) -> HashSet<String> {
        base.iter()
            .flat_map(|cube| {
                cube.iter()
                    .flat_map(|literal| self.atoms.to_term(literal).unwrap().ids())
            })
            .collect()
    }

    fn base_to_term(&self, base: &Self::Base) -> Term {
        Term::or(base.iter().map(|cube| {
            Term::and(
                cube.iter()
                    .map(|literal| self.atoms.to_term(literal).unwrap()),
            )
        }))
    }

    fn new(
        cfg: &InferenceConfig,
        atoms: Arc<RestrictedAtoms>,
        non_universal_vars: HashSet<String>,
    ) -> Self {
        let cubes = cfg.cubes.expect("Maximum number of cubes not provided.");
        let mut non_unit = cfg
            .non_unit
            .expect("Number of pDNF non-unit cubes not provided.");
        let mut cube_size = cfg
            .cube_size
            .expect("Maximum size of non-unit cubes not provided.");

        if non_universal_vars.is_empty() {
            non_unit = 0;
        }

        if non_unit == 0 {
            cube_size = 1;
        }

        assert!(cubes >= non_unit && cube_size > 0);

        Self {
            cubes,
            non_unit,
            cube_size,
            atoms,
        }
    }

    fn strongest(&self) -> Vec<Self::Base> {
        vec![vec![]]
    }

    fn weaken<I>(&self, base: Self::Base, cube: &[Literal], ignore: I) -> Vec<Self::Base>
    where
        I: Fn(&Self::Base) -> bool,
    {
        // Currently unimplemented for for than one non-unit cube.
        // For this we'd need to consider intersections of existing cubes.
        assert!(self.non_unit <= 1);

        let mut weakened = vec![];

        let non_unit = base.iter().filter(|cb| cb.len() > 1).count();
        assert!(non_unit <= self.non_unit);

        if non_unit < self.non_unit {
            weakened.extend(self.add_combinations(base, cube));
        } else {
            // Add literal from cube.
            weakened.extend(
                cube.iter()
                    .filter_map(|lit| self.add_unit(base.clone(), *lit))
                    .filter(|b| b.len() <= self.cubes && !ignore(b)),
            );
            // Reduce old cube to a literal, and add combinations of new cube.
            let non_unit_literals: HashSet<Literal> = base
                .iter()
                .filter(|cb| cb.len() > 1)
                .flatten()
                .cloned()
                .collect();
            weakened.extend(
                non_unit_literals
                    .into_iter()
                    .filter_map(|lit| self.add_unit(base.clone(), lit))
                    .filter(|b| !ignore(b))
                    .flat_map(|base| self.add_combinations(base, cube))
                    .filter(|b| !ignore(b)),
            );
            // Intersect old cube with new cube.
            weakened.extend(
                self.intersect_cubes(base, cube)
                    .into_iter()
                    .filter(|b| !ignore(b)),
            );
        }

        weakened
    }

    fn approx_space_size(&self) -> usize {
        let atoms = self.atoms.len();
        let cubes: usize = (0..=self.cube_size)
            .map(|len| clauses_cubes_count(atoms, len))
            .sum();

        let mut total = 0;
        for non_unit in 0..=self.non_unit {
            let literals: usize = (0..=(self.cubes - non_unit))
                .map(|len| clauses_cubes_count(atoms, len))
                .sum();
            total += literals * ((cubes - non_unit + 1)..=cubes).product::<usize>();
        }

        total
    }

    fn sub_spaces(&self) -> Vec<Self> {
        (0..=self.non_unit)
            .flat_map(move |non_unit| {
                let max_cube_size = match non_unit {
                    0 => 1,
                    _ => self.cube_size,
                };

                (1..=max_cube_size).map(move |cube_size| Self {
                    cubes: self.cubes,
                    cube_size,
                    non_unit,
                    atoms: self.atoms.clone(),
                })
            })
            .collect_vec()
    }

    fn contains(&self, other: &Self) -> bool {
        self.cubes >= other.cubes
            && self.non_unit >= other.non_unit
            && self.cube_size >= other.cube_size
    }
}

#[derive(Clone)]
pub struct LemmaPDnf {
    pub cubes: usize,
    pub cube_size: usize,
    pub non_unit: usize,
    atoms: Arc<RestrictedAtoms>,
    non_universal_vars: HashSet<String>,
}

impl LemmaQf for LemmaPDnf {
    type Base = (Vec<Literal>, Vec<Vec<Literal>>);

    fn base_from_clause(&self, clause: &[Literal]) -> Self::Base {
        (
            clause.to_vec(),
            clause.iter().map(|lit| vec![*lit]).collect(),
        )
    }

    fn substitute(&self, base: &Self::Base, substitution: &Substitution) -> Option<Self::Base> {
        let mut new_base = (vec![], vec![]);

        for literal in &base.0 {
            if let Some(a) = self.atoms.substitute(literal.0, substitution) {
                new_base.0.push((a, literal.1));
            } else {
                return None;
            }
        }

        for cube in &base.1 {
            let mut new_cube = vec![];
            for literal in cube {
                if let Some(a) = self.atoms.substitute(literal.0, substitution) {
                    new_cube.push((a, literal.1));
                } else {
                    return None;
                }
            }
            new_base.1.push(new_cube);
        }

        Some(new_base)
    }

    fn ids(&self, base: &Self::Base) -> HashSet<String> {
        base.1
            .iter()
            .chain([&base.0])
            .flat_map(|cube| {
                cube.iter()
                    .flat_map(|literal| self.atoms.to_term(literal).unwrap().ids())
            })
            .collect()
    }

    fn base_to_term(&self, base: &Self::Base) -> Term {
        Term::or(
            base.0
                .iter()
                .map(|literal| self.atoms.to_term(literal).unwrap())
                .chain(base.1.iter().map(|cube| {
                    Term::and(
                        cube.iter()
                            .map(|literal| self.atoms.to_term(literal).unwrap()),
                    )
                })),
        )
    }

    fn new(
        cfg: &InferenceConfig,
        atoms: Arc<RestrictedAtoms>,
        non_universal_vars: HashSet<String>,
    ) -> Self {
        let cubes = cfg.cubes.expect("Maximum number of cubes not provided.");
        let mut cube_size = cfg
            .cube_size
            .expect("Maximum size of non-unit cubes not provided.");
        let mut non_unit = cfg
            .non_unit
            .expect("Number of pDNF non-unit cubes not provided.");

        if non_universal_vars.is_empty() {
            non_unit = 0;
        }

        if non_unit == 0 {
            cube_size = 1;
        }

        assert!(cubes >= non_unit && cube_size > 0);

        Self {
            cubes,
            non_unit,
            cube_size,
            atoms,
            non_universal_vars,
        }
    }

    fn strongest(&self) -> Vec<Self::Base> {
        vec![(vec![], vec![])]
    }

    fn weaken<I>(&self, base: Self::Base, cube: &[Literal], ignore: I) -> Vec<Self::Base>
    where
        I: Fn(&Self::Base) -> bool,
    {
        let mut weakened = vec![];
        let (units, non_units) = base;

        // Weaken by adding a new literal
        if units.len() + non_units.len() < self.cubes {
            for literal in cube.iter().filter(|lit| !self.atoms.is_eq(lit.0) || lit.1) {
                let neg_literal = (literal.0, !literal.1);
                if !units.contains(&neg_literal) {
                    let new_non_units = non_units
                        .iter()
                        .filter(|cb| !cb.contains(literal))
                        .map(|cb| {
                            cb.iter()
                                .copied()
                                .filter(|lit| *lit != neg_literal)
                                .collect_vec()
                        })
                        .collect_vec();
                    if new_non_units.iter().all(|cb| cb.len() > 1) {
                        let mut new_base = (units.clone(), new_non_units);
                        new_base.0.push(*literal);
                        if !ignore(&new_base) {
                            weakened.push(new_base);
                        }
                    }
                }
            }
        }

        // Weaken by intersecting a cube
        for i in 0..non_units.len() {
            let cube_map: HashMap<usize, bool> = cube.iter().cloned().collect();
            let intersection = non_units[i]
                .iter()
                .copied()
                .filter(|lit| cube_map[&lit.0] == lit.1)
                .collect_vec();
            if intersection.len() > 1 {
                let mut new_non_units = vec![];
                new_non_units.extend(non_units[0..i].iter().cloned());
                new_non_units.push(intersection);
                new_non_units.extend(non_units[(i + 1)..].iter().cloned());
                let new_base = (units.clone(), new_non_units);
                if !ignore(&new_base) {
                    weakened.push(new_base);
                }
            }
        }

        // Weaken by adding a cube
        if units.len() + non_units.len() < self.cubes
            && non_units.len() < self.non_unit
            && self.cube_size > 1
        {
            let mut cube = cube
                .iter()
                .filter(|lit| !units.contains(&(lit.0, !lit.1)))
                .copied()
                .collect_vec();
            cube = self.atoms.containing_vars(cube, &self.non_universal_vars);

            let comb_len = self.cube_size.min(cube.len());
            if comb_len > 1 {
                for comb in cube.into_iter().combinations(self.cube_size.min(comb_len)) {
                    let mut new_non_units = non_units.clone();
                    new_non_units.push(comb);
                    let new_base = (units.clone(), new_non_units);
                    if !ignore(&new_base) {
                        weakened.push(new_base);
                    }
                }
            }
        }

        weakened
    }

    fn approx_space_size(&self) -> usize {
        let cubes: usize = (0..=self.cube_size)
            .map(|len| {
                clauses_cubes_count(
                    self.atoms.atoms_containing_vars(&self.non_universal_vars),
                    len,
                )
            })
            .sum();

        let mut total = 0;
        for non_unit in 0..=self.non_unit {
            let literals: usize = (0..=(self.cubes - non_unit))
                .map(|len| clauses_cubes_count(self.atoms.len(), len))
                .sum();
            total += literals * ((cubes - non_unit + 1)..=cubes).product::<usize>();
        }

        total
    }

    fn sub_spaces(&self) -> Vec<Self> {
        (0..=self.non_unit)
            .flat_map(move |non_unit| {
                let max_cube_size = match non_unit {
                    0 => 1,
                    _ => self.cube_size,
                };

                (1..=max_cube_size).map(move |cube_size| Self {
                    cubes: self.cubes,
                    cube_size,
                    non_unit,
                    atoms: self.atoms.clone(),
                    non_universal_vars: self.non_universal_vars.clone(),
                })
            })
            .collect_vec()
    }

    fn contains(&self, other: &Self) -> bool {
        self.cubes >= other.cubes
            && self.non_unit >= other.non_unit
            && self.cube_size >= other.cube_size
    }
}

impl Term {
    /// Compute the names of [`Term::Id`]'s present in the given term.
    ///
    /// Supports only quantifier-free terms.
    pub fn ids(&self) -> HashSet<String> {
        match self {
            Term::Id(name) => HashSet::from_iter([name.clone()]),
            Term::App(_, _, vt) => vt.iter().flat_map(|t| t.ids()).collect(),
            Term::UnaryOp(_, t) => t.ids(),
            Term::BinOp(_, t1, t2) => [t1, t2].iter().flat_map(|t| t.ids()).collect(),
            Term::NAryOp(_, vt) => vt.iter().flat_map(|t| t.ids()).collect(),
            Term::Ite { cond, then, else_ } => {
                [cond, then, else_].iter().flat_map(|t| t.ids()).collect()
            }
            _ => HashSet::default(),
        }
    }
}

/// A [`Frontier`] maintains quantified formulas during invariant inference.
pub struct Frontier<O, L, B>
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug,
{
    /// The set of lemmas used to sample pre-states when sampling from a transition.
    /// This is referred to as the _frontier_.
    pub lemmas: LemmaSet<O, L, B>,
    /// A set of lemmas blocked by the current frontier. That is, any post-state of
    /// a transition from the frontier satisfies `blocked`.
    blocked: LemmaSet<O, L, B>,
    /// A mapping between each blocked lemma and a core in the frontier that blocks it.
    blocked_to_core: HashMap<usize, HashSet<usize>>,
    /// A mapping between frontier elements and the blocked lemmas they block.
    core_to_blocked: HashMap<usize, HashSet<usize>>,
    /// Whether to extend CTI traces, and how much.
    extend: Option<(usize, usize)>,
    /// A set of CTI's to extend.
    ctis: VecDeque<Model>,
}

impl<O, L, B> Frontier<O, L, B>
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
{
    /// Create a new frontier from the given set of lemmas.
    pub fn new(lemmas_init: LemmaSet<O, L, B>, extend: Option<(usize, usize)>) -> Self {
        let blocked = lemmas_init.clone_empty();

        Frontier {
            lemmas: lemmas_init,
            blocked,
            blocked_to_core: HashMap::default(),
            core_to_blocked: HashMap::default(),
            extend,
            ctis: VecDeque::new(),
        }
    }

    /// Get the length of the frontier.
    pub fn len(&self) -> usize {
        self.lemmas.len()
    }

    /// Get an initial state which violates one of the given lemmas.
    /// This doesn't use the frontier, only previously blocked lemmas.
    pub fn init_cex(
        &mut self,
        fo: &FOModule,
        conf: &SolverConf,
        lemmas: &WeakenLemmaSet<O, L, B>,
    ) -> Option<Model> {
        let new_cores: Mutex<Vec<(Arc<QuantifierPrefix>, O, HashSet<usize>)>> = Mutex::new(vec![]);

        let res = lemmas
            .iter()
            .into_par_iter()
            .filter(|(prefix, body)| !self.blocked.subsumes(prefix, body))
            .find_map_any(|(prefix, body)| {
                let term = prefix.quantify(self.lemmas.lemma_qf.base_to_term(&body.to_base()));
                if let Some(model) = fo.init_cex(conf, &term) {
                    return Some(model);
                } else {
                    let core = self.lemmas.to_prefixes.keys().copied().collect();
                    let mut new_cores_vec = new_cores.lock().unwrap();
                    new_cores_vec.push((prefix, body.clone(), core))
                }

                None
            });

        for (prefix, body, core) in new_cores.into_inner().unwrap() {
            let blocked_id = self.blocked.insert(prefix, body);
            for i in &core {
                if let Some(hs) = self.core_to_blocked.get_mut(i) {
                    hs.insert(blocked_id);
                } else {
                    self.core_to_blocked
                        .insert(*i, HashSet::from_iter([blocked_id]));
                }
            }
            self.blocked_to_core.insert(blocked_id, core);
        }

        if self.extend.is_some() {
            self.ctis.extend(res.iter().cloned());
        }

        res
    }

    /// Extend CTI traces and weaken the given lemmas accordingly,
    /// until no more states can be sampled.
    pub fn extend(
        &mut self,
        fo: &FOModule,
        conf: &SolverConf,
        lemmas: &mut WeakenLemmaSet<O, L, B>,
    ) {
        let (width, depth) = self.extend.unwrap();
        while let Some(state) = self.ctis.pop_front() {
            log::info!(
                "[{}] Extending CTI trace... (remaining CTI's = {})",
                lemmas.len(),
                self.ctis.len()
            );
            let samples = fo.simulate_from(conf, &state, width, depth);
            log::info!(
                "[{}] Weakening with {} samples...",
                lemmas.len(),
                samples.len()
            );
            for sample in samples {
                if lemmas.weaken(&sample) {
                    log::info!("[{}] Weakened.", lemmas.len());
                    self.ctis.push_back(sample);
                }
            }
        }
    }

    /// Get an post-state of the frontier which violates one of the given lemmas.
    pub fn trans_cex(
        &mut self,
        fo: &FOModule,
        conf: &SolverConf,
        lemmas: &WeakenLemmaSet<O, L, B>,
    ) -> Option<Model> {
        let (pre_ids, pre_terms): (Vec<usize>, Vec<Term>) =
            self.lemmas.to_terms_ids().into_iter().unzip();

        let new_cores: Mutex<Vec<(Arc<QuantifierPrefix>, O, HashSet<usize>)>> = Mutex::new(vec![]);
        let cancel = Arc::new(RwLock::new(false));

        let res = lemmas
            .iter()
            .into_par_iter()
            .filter(|(prefix, body)| !self.blocked.subsumes(prefix, body))
            .find_map_any(|(prefix, body)| {
                let term = prefix.quantify(self.lemmas.lemma_qf.base_to_term(&body.to_base()));
                match fo.trans_cex(conf, &pre_terms, &term, false, false, Some(cancel.clone())) {
                    TransCexResult::CTI(_, model) => {
                        let mut lock = cancel.write().unwrap();
                        *lock = true;
                        return Some(model);
                    }
                    TransCexResult::UnsatCore(core) => {
                        let mut new_cores_vec = new_cores.lock().unwrap();
                        new_cores_vec.push((prefix, body.clone(), hashmap::set_from_std(core)));
                    }
                    TransCexResult::Cancelled => (),
                }

                None
            });

        for (prefix, body, core) in new_cores.into_inner().unwrap() {
            let core = core.into_iter().map(|i| pre_ids[i]).collect();
            let blocked_id = self.blocked.insert(prefix, body);
            for i in &core {
                if let Some(hs) = self.core_to_blocked.get_mut(i) {
                    hs.insert(blocked_id);
                } else {
                    self.core_to_blocked
                        .insert(*i, HashSet::from_iter([blocked_id]));
                }
            }
            self.blocked_to_core.insert(blocked_id, core);
        }

        if self.extend.is_some() {
            self.ctis.extend(res.iter().cloned());
        }

        res
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
    pub fn advance(&mut self, new_lemmas: &LemmaSet<O, L, B>, mut grow: bool) -> bool {
        // If there are no lemmas in the frontier, it cannot be advanced.
        if self.lemmas.len() == 0 {
            return false;
        }

        // Find all lemmas in the frontier (parents) which have been weakened in the new lemmas.
        // These are precisely the lemmas in the fontier which are not part of the new lemmas.
        let weakened_parents: HashSet<usize> = self
            .lemmas
            .to_prefixes
            .keys()
            .filter(|&id| {
                !new_lemmas.subsumes(&self.lemmas.to_prefixes[id], &self.lemmas.to_bodies[id])
            })
            .cloned()
            .collect();

        // Compute the mapping from parents to their weakenings (children).
        let mut to_children: HashMap<usize, HashSet<usize>> = weakened_parents
            .par_iter()
            .map(|&id| {
                (
                    id,
                    new_lemmas
                        .get_subsumed(&self.lemmas.to_prefixes[&id], &self.lemmas.to_bodies[&id]),
                )
            })
            .collect();

        // Compute the mapping from children to parents.
        let mut to_parents: HashMap<usize, HashSet<usize>> = new_lemmas
            .to_prefixes
            .par_iter()
            .map(|(id, prefix)| {
                (
                    *id,
                    self.lemmas
                        .get_subsuming(prefix, &new_lemmas.to_bodies[id])
                        .intersection(&weakened_parents)
                        .cloned()
                        .collect(),
                )
            })
            .collect();

        assert!(to_children
            .iter()
            .all(|(p, ch)| ch.iter().all(|c| to_parents[c].contains(p))));
        assert!(to_parents
            .iter()
            .all(|(c, pr)| pr.iter().all(|p| to_children[p].contains(c))));

        let mut advanced = false;
        loop {
            // Given a children and parents mapping, compute the parent with the least unique children,
            // i.e. the least number of children which are uniquely theirs.
            let min_unique = |to_children_local: &HashMap<usize, HashSet<usize>>,
                              to_parents_local: &HashMap<usize, HashSet<usize>>|
             -> Option<(usize, Vec<usize>)> {
                to_children_local
                    .iter()
                    .map(|(id, ch)| {
                        let unique_ch: Vec<usize> = ch
                            .iter()
                            .cloned()
                            .filter(|ch_id| to_parents_local[ch_id].len() == 1)
                            .collect();

                        (*id, unique_ch)
                    })
                    .min_by_key(|(id, ch)| {
                        (
                            ch.iter()
                                .map(|i| count_exists(&new_lemmas.to_prefixes[i].quantifiers))
                                .sum::<usize>(),
                            ch.len(),
                            *id,
                        )
                    })
            };

            let min = min_unique(&to_children, &to_parents);
            #[allow(clippy::unnecessary_unwrap)]
            if min.is_some() && (grow || min.as_ref().unwrap().1.len() <= 1) {
                // This is the replaced lemma.
                let (id, ch) = &min.unwrap();

                // The frontier is advanced.
                advanced = true;
                // Never grow twice.
                grow = false;

                // Remove the lemma from the frontier.
                self.lemmas.remove(id);
                // Remove blocking cores that contain the replaced lemma.
                if let Some(unblocked) = self.core_to_blocked.remove(id) {
                    for lemma in &unblocked {
                        // Signal that the lemma isn't blocked anymore.
                        self.blocked.remove(lemma);
                        // For any other frontier element in the core, signal that it doesn't block the lemma anymore.
                        for in_core in &self.blocked_to_core.remove(lemma).unwrap() {
                            if in_core != id {
                                let blocked_by_in_core =
                                    self.core_to_blocked.get_mut(in_core).unwrap();
                                blocked_by_in_core.remove(lemma);
                                if blocked_by_in_core.is_empty() {
                                    self.core_to_blocked.remove(in_core);
                                }
                            }
                        }
                    }
                }

                // Remove the parent lemma and disconnect it from its children.
                for ch_id in to_children.remove(id).unwrap() {
                    assert!(to_parents.get_mut(&ch_id).unwrap().remove(id));
                }
                // Add each unique child to the frontier.
                for new_id in ch {
                    self.lemmas.insert(
                        new_lemmas.to_prefixes[new_id].clone(),
                        new_lemmas.to_bodies[new_id].clone(),
                    );
                    // Remove the parents entry of this child (it should be empty because its only parent
                    // was already removed.)
                    assert!(to_parents.remove(new_id).unwrap().is_empty());
                }
            } else {
                break;
            }
        }

        advanced
    }
}

/// An [`IndividualLemmaSearch`] manages the search for individually inductive lemmas.
pub struct IndividualLemmaSearch<O, L, B>
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
{
    /// The set of lemmas that might still need to be weakened.
    pub weaken_set: WeakenLemmaSet<O, L, B>,
    // The set of lemmas already cover initial states.
    pub initial: LemmaSet<O, L, B>,
    /// The set of inductive lemmas found so far.
    pub inductive: LemmaSet<O, L, B>,
    /// Whether to extend CTI traces, and how much.
    pub extend: Option<(usize, usize)>,
    /// A set of CTI's to extend.
    pub ctis: VecDeque<Model>,
}

impl<O, L, B> IndividualLemmaSearch<O, L, B>
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
{
    /// Get the length of the frontier.
    pub fn len(&self) -> (usize, usize) {
        (self.weaken_set.len(), self.inductive.len())
    }

    pub fn init_cycle(&mut self, fo: &FOModule, conf: &SolverConf) -> bool {
        let new_initial: Mutex<Vec<_>> = Mutex::new(vec![]);
        log::info!("Getting weakest lemmas...");
        let weakest = self.weaken_set.iter();
        log::info!("Finding CTI...");
        let cti = weakest
            .into_par_iter()
            .filter(|(prefix, body)| !self.initial.subsumes(prefix, body))
            .find_map_any(|(prefix, body)| {
                let term = prefix.quantify(self.initial.lemma_qf.base_to_term(&body.to_base()));
                if let Some(model) = fo.init_cex(conf, &term) {
                    return Some(model);
                } else {
                    let mut new_initial_vec = new_initial.lock().unwrap();
                    new_initial_vec.push((prefix, body));

                    None
                }
            });

        log::info!("Saving initially implied lemmas...");
        for (prefix, body) in new_initial.into_inner().unwrap() {
            self.initial.insert_minimized(prefix, body.clone());
        }

        if let Some(model) = cti {
            log::info!("Weakening...");
            self.weaken_set.weaken(&model);
            if self.extend.is_some() {
                self.ctis.push_back(model);
            }
            true
        } else {
            false
        }
    }

    /// Extend CTI traces and weaken the given lemmas accordingly,
    /// until no more states can be sampled.
    pub fn extend(&mut self, fo: &FOModule, conf: &SolverConf) {
        let (width, depth) = self.extend.unwrap();

        while let Some(state) = self.ctis.pop_front() {
            let mut levels = vec![vec![(0, state)]];
            log::info!(
                "[{}] Extending CTI trace... (remaining CTI's = {})",
                self.weaken_set.len(),
                self.ctis.len()
            );
            for i in 0..depth {
                let mut new_level = vec![];
                for (j, state) in &levels[i] {
                    new_level.extend(
                        fo.simulate_from(conf, state, width, 1)
                            .into_iter()
                            .map(|model| (*j, model)),
                    );
                }
                levels.push(new_level);
            }
            log::info!(
                "[{}] Weakening with {} samples...",
                self.weaken_set.len(),
                levels[1..].iter().map(|l| l.len()).sum::<usize>()
            );
            for i in 1..=depth {
                for (j, poststate) in &levels[i] {
                    if self.weaken_set.weaken_cti(&levels[i - 1][*j].1, poststate) {
                        log::info!("[{}] Weakened.", self.weaken_set.len());
                        self.ctis.push_back(poststate.clone());
                    }
                }
            }
        }
    }

    pub fn trans_cycle(&mut self, fo: &FOModule, conf: &SolverConf) -> bool {
        let new_inductive: Mutex<Vec<_>> = Mutex::new(vec![]);
        let cancel = Arc::new(RwLock::new(false));
        log::info!("Getting weakest lemmas...");
        let weakest = self.weaken_set.iter();
        log::info!("Finding CTI...");
        let cti = weakest
            .into_par_iter()
            .filter(|(prefix, body)| !self.inductive.subsumes(prefix, body))
            .find_map_any(|(prefix, body)| {
                let term = [prefix.quantify(self.inductive.lemma_qf.base_to_term(&body.to_base()))];
                match fo.trans_cex(conf, &term, &term[0], false, false, Some(cancel.clone())) {
                    TransCexResult::CTI(pre, post) => {
                        let mut lock = cancel.write().unwrap();
                        *lock = true;
                        return Some((pre, post));
                    }
                    TransCexResult::UnsatCore(_) => {
                        let mut new_inductive_vec = new_inductive.lock().unwrap();
                        new_inductive_vec.push((prefix, body));
                    }
                    TransCexResult::Cancelled => (),
                }

                None
            });

        log::info!("Saving inductive lemmas...");
        for (prefix, body) in new_inductive.into_inner().unwrap() {
            self.inductive.insert_minimized(prefix, body.clone());
        }

        if let Some((prestate, poststate)) = cti {
            log::info!("Weakening...");
            self.weaken_set.weaken_cti(&prestate, &poststate);
            if self.extend.is_some() {
                self.ctis.push_back(poststate);
            }
            true
        } else {
            false
        }
    }
}

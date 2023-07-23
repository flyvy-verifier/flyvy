// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Implement simple components, lemma domains and data structures for use in inference.

use fly::ouritertools::OurItertools;
use itertools::Itertools;
use std::collections::VecDeque;
use std::fmt::Debug;
use std::sync::{Arc, Mutex, RwLock};
use std::time::Instant;

use fly::semantics::Model;
use fly::syntax::Term;
use fly::term::subst::Substitution;
use solver::conf::SolverConf;

use crate::{
    atoms::{Literal, RestrictedAtoms},
    basics::{FOModule, InferenceConfig, SolverPids, TransCexResult},
    hashmap::{HashMap, HashSet},
    subsume::OrderSubsumption,
    weaken::{LemmaQf, LemmaSet, WeakenLemmaSet},
};

use rayon::prelude::*;

/// The minimal number of disjuncts a lemma is allowed to have.
/// This corresponds to number of cubes in DNF, or the clause size in CNF.
const MIN_DISJUNCTS: usize = 3;

fn clauses_cubes_count(atoms: usize, len: usize) -> usize {
    if len > atoms {
        0
    } else {
        ((atoms - len + 1)..=atoms).product::<usize>() / (1..=len).product::<usize>()
            * 2_usize.pow(len as u32)
    }
}

#[derive(Clone)]
pub struct LemmaCnf {
    /// The maximal number of clauses in a CNF formula.
    pub clauses: usize,
    /// The maximal number of literals in each clause.
    pub clause_size: usize,
    atoms: Arc<RestrictedAtoms>,
}

impl Debug for LemmaCnf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CNF")
            .field("clauses", &self.clauses)
            .field("clause_size", &self.clause_size)
            .finish()
    }
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
                    .flat_map(|literal| ids(&self.atoms.to_term(literal).unwrap()))
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
            .multi_cartesian_product_fixed()
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
            .flat_map(|clauses| {
                (MIN_DISJUNCTS..=self.clause_size).map(move |clause_size| Self {
                    clauses,
                    clause_size,
                    atoms: self.atoms.clone(),
                })
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

impl Debug for LemmaPDnfNaive {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("pDNF (naive)")
            .field("cubes", &self.cubes)
            .field("cube_size", &self.cube_size)
            .field("non_unit", &self.non_unit)
            .finish()
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
                    .flat_map(|literal| ids(&self.atoms.to_term(literal).unwrap()))
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
        (MIN_DISJUNCTS..=self.cubes)
            .flat_map(|cubes| {
                (0..=self.non_unit.min(cubes)).flat_map(move |non_unit| {
                    let cube_sizes = match non_unit {
                        0 => 0..=0,
                        _ => 2..=self.cube_size,
                    };

                    cube_sizes.map(move |cube_size| Self {
                        cubes,
                        cube_size,
                        non_unit,
                        atoms: self.atoms.clone(),
                    })
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

impl Debug for LemmaPDnf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("pDNF")
            .field("cubes", &self.cubes)
            .field("cube_size", &self.cube_size)
            .field("non_unit", &self.non_unit)
            .finish()
    }
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
                    .flat_map(|literal| ids(&self.atoms.to_term(literal).unwrap()))
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
        let atoms = self.atoms.len();
        let cube_atoms = self.atoms.atoms_containing_vars(&self.non_universal_vars);
        (MIN_DISJUNCTS..=self.cubes.min(atoms))
            .flat_map(|cubes| {
                (0..=self.non_unit.min(cubes)).flat_map(move |non_unit| {
                    let cube_sizes = match non_unit {
                        0 => 0..=0,
                        _ => 2..=self.cube_size.min(cube_atoms),
                    };

                    cube_sizes.map(move |cube_size| Self {
                        cubes,
                        cube_size,
                        non_unit,
                        atoms: self.atoms.clone(),
                        non_universal_vars: self.non_universal_vars.clone(),
                    })
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

/// Compute the names of [`Term::Id`]'s present in the given term.
///
/// Supports only quantifier-free terms.
pub fn ids(term: &Term) -> HashSet<String> {
    match term {
        Term::Id(name) => HashSet::from_iter([name.clone()]),
        Term::App(_, _, vt) => vt.iter().flat_map(ids).collect(),
        Term::UnaryOp(_, t) => ids(t),
        Term::BinOp(_, t1, t2) => [t1, t2].iter().flat_map(|t| ids(t)).collect(),
        Term::NAryOp(_, vt) => vt.iter().flat_map(ids).collect(),
        Term::Ite { cond, then, else_ } => {
            [cond, then, else_].iter().flat_map(|t| ids(t)).collect()
        }
        _ => HashSet::default(),
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

    /// Check if the frontier is empty
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get an initial state which violates one of the given lemmas.
    /// This doesn't use the frontier, only previously blocked lemmas.
    pub fn init_cex(
        &mut self,
        fo: &FOModule,
        conf: &SolverConf,
        lemmas: &WeakenLemmaSet<O, L, B>,
    ) -> Option<Model> {
        let blocked_lock = RwLock::new((
            &mut self.blocked,
            &mut self.blocked_to_core,
            &mut self.core_to_blocked,
        ));

        let res = lemmas
            .as_vec()
            .into_par_iter()
            .filter(|(prefix, body)| {
                let blocked_read = blocked_lock.read().unwrap();
                !blocked_read.0.subsumes(prefix, body)
            })
            .find_map_any(|(prefix, body)| {
                let term = prefix.quantify(self.lemmas.body_to_term(body));
                if let Some(model) = fo.init_cex(conf, &term) {
                    return Some(model);
                } else {
                    let mut blocked_write = blocked_lock.write().unwrap();
                    let core = self.lemmas.ids().collect();
                    let blocked_id = blocked_write.0.insert(prefix, body.clone());
                    for i in &core {
                        if let Some(hs) = blocked_write.2.get_mut(i) {
                            hs.insert(blocked_id);
                        } else {
                            blocked_write.2.insert(*i, HashSet::from_iter([blocked_id]));
                        }
                    }
                    blocked_write.1.insert(blocked_id, core);
                }

                None
            });

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
        while !self.ctis.is_empty() {
            let mut new_ctis = VecDeque::new();
            log::debug!(
                "[{}] Extending traces from {} CTI's...",
                lemmas.len(),
                self.ctis.len()
            );
            let samples: Vec<Model> = self
                .ctis
                .par_iter()
                .enumerate()
                .flat_map_iter(|(id, state)| {
                    log::debug!("[{}] Extending CTI trace #{id}...", lemmas.len());
                    let samples = fo.simulate_from(conf, state, width, depth);
                    log::debug!(
                        "[{}] Found {} simulated samples from CTI #{id}...",
                        lemmas.len(),
                        samples.len(),
                    );

                    samples
                })
                .collect();

            let samples_len = samples.len();
            log::debug!(
                "[{}] Found a total of {samples_len} simulated samples from {} CTI's...",
                lemmas.len(),
                self.ctis.len(),
            );
            let mut idx = 0;
            while let Some(i) = (idx..samples.len())
                .into_par_iter()
                .find_first(|i| lemmas.unsat(&samples[*i]))
            {
                assert!(lemmas.weaken(&samples[i]));
                log::debug!("[{}] Weakened ({} / {samples_len}).", lemmas.len(), i + 1);
                new_ctis.push_back(samples[i].clone());
                idx = i + 1;
            }

            self.ctis = new_ctis;
        }
    }

    /// Get an post-state of the frontier which violates one of the given lemmas.
    pub fn trans_cex(
        &mut self,
        fo: &FOModule,
        conf: &SolverConf,
        lemmas: &WeakenLemmaSet<O, L, B>,
    ) -> Option<Model> {
        let (pre_ids, pre_terms): (Vec<usize>, Vec<Term>) = self.lemmas.to_terms_ids().unzip();

        let solver_pids = SolverPids::new();
        let unknown = Mutex::new(false);
        let first_sat = Mutex::new(None);
        let total_sat = Mutex::new(0_usize);
        let total_unsat = Mutex::new(0_usize);
        let blocked_lock = RwLock::new((
            &mut self.blocked,
            &mut self.blocked_to_core,
            &mut self.core_to_blocked,
        ));

        let start_time = Instant::now();
        let res = lemmas
            .as_vec()
            .into_par_iter()
            .filter(|(prefix, body)| {
                let blocked_read = blocked_lock.read().unwrap();
                !blocked_read.0.subsumes(prefix, body)
            })
            .find_map_any(|(prefix, body)| {
                let term = prefix.quantify(self.lemmas.body_to_term(body));
                match fo.trans_cex(conf, &pre_terms, &term, false, false, Some(&solver_pids)) {
                    TransCexResult::CTI(_, model) => {
                        solver_pids.cancel();
                        {
                            let mut first_sat_lock = first_sat.lock().unwrap();
                            if first_sat_lock.is_none() {
                                *first_sat_lock = Some(Instant::now());
                            }
                        }
                        {
                            let mut total_sat_lock = total_sat.lock().unwrap();
                            *total_sat_lock += 1;
                        }
                        return Some(model);
                    }
                    TransCexResult::UnsatCore(core) => {
                        {
                            let mut total_unsat_lock = total_unsat.lock().unwrap();
                            *total_unsat_lock += 1;
                        }

                        {
                            let mut blocked_write = blocked_lock.write().unwrap();
                            let core = core.into_iter().map(|i| pre_ids[i]).collect();
                            let blocked_id = blocked_write.0.insert(prefix, body.clone());
                            for i in &core {
                                if let Some(hs) = blocked_write.2.get_mut(i) {
                                    hs.insert(blocked_id);
                                } else {
                                    blocked_write.2.insert(*i, HashSet::from_iter([blocked_id]));
                                }
                            }
                            blocked_write.1.insert(blocked_id, core);
                        }
                    }
                    TransCexResult::Cancelled => (),
                    TransCexResult::Unknown => *unknown.lock().unwrap() = true,
                }

                None
            });

        if res.is_none() && unknown.into_inner().unwrap() {
            panic!("SMT queries got 'unknown' and no SAT results.")
        }

        log::info!(
            "    SMT STATS: total_time={:.5}s, until_sat={:.5}s, sat_found={}, unsat_found={}",
            (Instant::now() - start_time).as_secs_f64(),
            (first_sat.into_inner().unwrap().unwrap_or(start_time) - start_time).as_secs_f64(),
            total_sat.into_inner().unwrap(),
            total_unsat.into_inner().unwrap(),
        );

        if self.extend.is_some() {
            self.ctis.extend(res.iter().cloned());
        }

        res
    }

    fn remove_lemma(&mut self, id: &usize) {
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
                        let blocked_by_in_core = self.core_to_blocked.get_mut(in_core).unwrap();
                        blocked_by_in_core.remove(lemma);
                        if blocked_by_in_core.is_empty() {
                            self.core_to_blocked.remove(in_core);
                        }
                    }
                }
            }
        }
    }

    /// Advance the fontier using the new lemmas. That is, remove each lemma in the frontier
    /// which isn't in the new lemmas, and add all weakenings of it (lemmas subsumed by it)
    /// to the frontier. However, to keep the frontier minimized, do not add lemmas
    /// that are subsumed by existing, unweakened lemmas.
    ///
    /// Return whether the advancement caused any change in the frontier.
    pub fn advance(&mut self, new_lemmas: &WeakenLemmaSet<O, L, B>) -> bool {
        // If there are no lemmas in the frontier, it cannot be advanced.
        if self.lemmas.is_empty() {
            return false;
        }

        // Find all lemmas in the frontier (parents) which have been weakened in the new lemmas.
        // These are precisely the lemmas in the fontier which are not part of the new lemmas.
        let weakened_parents: HashSet<usize> = self
            .lemmas
            .as_iter()
            .filter_map(|(prefix, body, id)| {
                if !new_lemmas.contains(&prefix, body) {
                    Some(id)
                } else {
                    None
                }
            })
            .collect();

        let advanced = !weakened_parents.is_empty();
        for id in &weakened_parents {
            self.remove_lemma(id)
        }

        let mut added_lemmas = self.lemmas.clone_empty();
        for (prefix, body) in new_lemmas.as_iter() {
            if !self.lemmas.subsumes(prefix.as_ref(), body) {
                added_lemmas.insert_minimized(prefix, body.clone());
            }
        }

        for (prefix, body, _) in added_lemmas.as_iter() {
            self.lemmas.insert(prefix, body.clone());
        }

        advanced
    }
}

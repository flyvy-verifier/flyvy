use core::panic;
use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

use fly::{
    syntax::{BinOp, NOp, NumRel, Term, UOp},
    term::subst::{rename_symbols, NameSubstitution, Substitutable},
};
use itertools::Itertools;

use crate::chc::{Chc, Component, FunctionSort};

#[derive(Hash, Eq, PartialEq, Clone)]
pub enum Atomic {
    /// A less-than comparison between two terms.
    /// The boolean indicates whether the comparison is strict (true) or non-strict (false).
    LessThan(Term, Term, bool),
    /// An atomic formula represented by a term and an optional polarity.
    /// The polarity indicates whether the formula is positive (Some(true)) or negative (Some(false)).
    /// If the polarity is None, it indicates that the formula may be used both positively and negatively.
    Atom(Term, Option<bool>),
}

#[derive(Hash, PartialEq, Eq, Clone)]
pub enum Assignment {
    Int(String, Term),
    ArrayStore {
        array: String,
        old_array: String,
        index: Term,
        value: Term,
    },
}

impl Display for Assignment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Assignment::Int(name, term) => write!(f, "{name} := {term}"),
            Assignment::ArrayStore {
                array,
                old_array,
                index,
                value,
            } => write!(f, "{array}[{index}] := {value} (from {old_array}))"),
        }
    }
}

fn saturate_assignments(assignments: &mut HashSet<Assignment>) {
    for _ in 0..1000 {
        let mut new_assignments = HashSet::new();
        for (a1, a2) in assignments.iter().cartesian_product(assignments.iter()) {
            match (a1, a2) {
                (Assignment::Int(x1, v1), Assignment::Int(x2, v2)) if v1.ids().contains(x2) => {
                    let mut substitution = NameSubstitution::new();
                    substitution.insert((x2.clone(), 0), Substitutable::Term(v2.clone()));
                    new_assignments.insert(Assignment::Int(
                        x1.clone(),
                        rename_symbols(v1, &substitution),
                    ));
                }

                (
                    Assignment::ArrayStore {
                        array,
                        old_array,
                        index,
                        value,
                    },
                    Assignment::Int(i, v),
                ) if index.ids().contains(i) || value.ids().contains(i) => {
                    let mut substitution = NameSubstitution::new();
                    substitution.insert((i.clone(), 0), Substitutable::Term(v.clone()));
                    new_assignments.insert(Assignment::ArrayStore {
                        array: array.clone(),
                        old_array: old_array.clone(),
                        index: rename_symbols(index, &substitution),
                        value: rename_symbols(value, &substitution),
                    });
                }
                (
                    Assignment::ArrayStore {
                        array: a2,
                        old_array: a2_old,
                        index: _,
                        value: _,
                    },
                    Assignment::ArrayStore {
                        array: a1,
                        old_array: a1_old,
                        index,
                        value,
                    },
                ) if a2_old == a1 => {
                    new_assignments.insert(Assignment::ArrayStore {
                        array: a2.clone(),
                        old_array: a1_old.clone(),
                        index: index.clone(),
                        value: value.clone(),
                    });
                }
                _ => (),
            }
        }

        let old_len = assignments.len();
        assignments.extend(new_assignments);
        if assignments.len() == old_len {
            return;
        }
    }
    panic!("too many iterations!");
}

fn old_arrays(term: &Term) -> HashSet<String> {
    match term {
        Term::Id(s) => HashSet::from_iter([s.clone()]),
        Term::ArrayStore {
            array,
            index: _,
            value: _,
        } => old_arrays(array),
        Term::Ite {
            cond: _,
            then,
            else_,
        } => {
            let mut arrays = old_arrays(then);
            arrays.extend(old_arrays(else_));
            arrays
        }
        _ => panic!("found no arrays"),
    }
}

impl Assignment {
    fn from_eq(dst: &String, src: &Term, fsort: &FunctionSort) -> Vec<Self> {
        if let Term::Ite {
            cond: _,
            then,
            else_,
        } = src
        {
            let mut asgns = Self::from_eq(dst, then, fsort);
            asgns.append(&mut Self::from_eq(dst, else_, fsort));
            return asgns;
        }

        if fsort.is_int() {
            vec![Self::Int(dst.clone(), src.clone())]
        } else if fsort.is_array_int_int() {
            if let Term::ArrayStore {
                array,
                index,
                value,
            } = src
            {
                let mut asgns = Assignment::from_eq(dst, array.as_ref(), fsort);
                let nested_arrays = old_arrays(array);
                for a in nested_arrays {
                    asgns.push(Assignment::ArrayStore {
                        array: dst.clone(),
                        old_array: a,
                        index: index.as_ref().clone(),
                        value: value.as_ref().clone(),
                    });
                }
                asgns
            } else {
                vec![]
            }
        } else {
            vec![]
        }
    }

    fn in_term(term: &Term, sorts: &HashMap<String, FunctionSort>) -> Vec<Self> {
        match term {
            Term::BinOp(BinOp::Equals, t1, t2) => {
                if let Term::Id(name) = t1.as_ref() {
                    if let Some(fsort) = sorts.get(name) {
                        return Self::from_eq(name, t2, fsort);
                    }
                } else if let Term::Id(name) = t2.as_ref() {
                    if let Some(fsort) = sorts.get(name) {
                        return Self::from_eq(name, t1, fsort);
                    }
                }
            }
            Term::NAryOp(NOp::And, ts) => {
                return ts.iter().flat_map(|t| Self::in_term(t, sorts)).collect()
            }
            _ => (),
        }

        vec![]
    }
}

impl Display for Atomic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LessThan(t1, t2, strict) => {
                write!(f, "{} {} {}", t1, if *strict { "<" } else { "<=" }, t2)
            }
            Self::Atom(term, polarity) => {
                if let Some(pos) = polarity {
                    write!(f, "{}{}", if *pos { "+" } else { "-" }, term)
                } else {
                    write!(f, "{}", term)
                }
            }
        }
    }
}

fn is_int(term: &Term, name_to_sort: &HashMap<String, FunctionSort>) -> bool {
    match term {
        Term::Literal(_)
        | Term::ArrayStore {
            array: _,
            index: _,
            value: _,
        } => false,
        Term::Int(_) | Term::NumOp(_, _) => true,
        Term::Id(name) => name_to_sort.get(name).unwrap().is_int(),
        // Currently, we only support integer arrays.
        Term::ArraySelect { array: _, index: _ } => true,
        _ => unimplemented!(),
    }
}

impl Atomic {
    fn from_term(
        term: &Term,
        pos: bool,
        name_to_sort: &HashMap<String, FunctionSort>,
    ) -> Vec<Self> {
        match term {
            Term::BinOp(bin_op, t1, t2)
                if matches!(bin_op, BinOp::Equals | BinOp::NotEquals)
                    && is_int(t1, name_to_sort)
                    && is_int(t2, name_to_sort) =>
            {
                let strict = matches!(
                    (bin_op, pos),
                    (BinOp::Equals, false) | (BinOp::NotEquals, true)
                );

                vec![
                    Self::LessThan(t1.as_ref().clone(), t2.as_ref().clone(), strict),
                    Self::LessThan(t2.as_ref().clone(), t1.as_ref().clone(), strict),
                ]
            }
            Term::NumRel(num_rel, t1, t2) => {
                let (left, right, flip_strict) = if pos {
                    (t1.as_ref().clone(), t2.as_ref().clone(), false)
                } else {
                    (t2.as_ref().clone(), t1.as_ref().clone(), true)
                };
                vec![match num_rel {
                    NumRel::Lt => Self::LessThan(left, right, !flip_strict),
                    NumRel::Leq => Self::LessThan(left, right, flip_strict),
                    NumRel::Gt => Self::LessThan(right, left, !flip_strict),
                    NumRel::Geq => Self::LessThan(right, left, flip_strict),
                }]
            }
            _ => {
                // All other terms are treated as atomic formulas.
                vec![Self::Atom(term.clone(), Some(pos))]
            }
        }
    }

    fn rename_symbols(&mut self, substitution: &NameSubstitution) {
        match self {
            Atomic::LessThan(t1, t2, _) => {
                *t1 = rename_symbols(t1, &substitution);
                *t2 = rename_symbols(t2, &substitution);
            }
            Atomic::Atom(term, _) => {
                *term = rename_symbols(term, &substitution);
            }
        }
    }

    fn ids(&self) -> HashSet<String> {
        match self {
            Atomic::LessThan(t1, t2, _) => {
                let mut ids = t1.ids();
                ids.extend(t2.ids());
                ids
            }
            Atomic::Atom(term, _) => term.ids(),
        }
    }
}

/// A structure to hold the atomic formulas and variables extracted from a CHC.
pub struct Atomics {
    pub terms: Vec<Atomic>,
    pub vars: Vec<(String, FunctionSort)>,
}

fn is_only_arith(term: &Term) -> bool {
    match term {
        Term::Int(_) | Term::Id(_) => true,
        Term::NumOp(_, ts) => ts.iter().all(is_only_arith),
        _ => false,
    }
}

impl Atomics {
    /// Create a new instance of `Atomics`.
    fn new() -> Self {
        Self {
            terms: vec![],
            vars: vec![],
        }
    }

    /// Load terms and variables from a single formula with the given polarity.
    fn load_from_formula(
        &mut self,
        term: &Term,
        pos: bool,
        name_to_sort: &HashMap<String, FunctionSort>,
    ) {
        match term {
            Term::Literal(_) => (),
            Term::BinOp(BinOp::Iff, _, _) => unimplemented!(),

            Term::UnaryOp(UOp::Not, t) => self.load_from_formula(t, !pos, name_to_sort),
            Term::BinOp(BinOp::Implies, t1, t2) => {
                self.load_from_formula(t1, !pos, name_to_sort);
                self.load_from_formula(t2, pos, name_to_sort);
            }
            Term::BinOp(BinOp::Equals, t1, t2) => {
                self.load_from_ite(t1, name_to_sort);
                self.load_from_ite(t2, name_to_sort);
            }
            Term::NAryOp(_, terms) => {
                for t in terms {
                    self.load_from_formula(t, pos, name_to_sort);
                }
            }
            Term::Ite { cond, then, else_ } => {
                self.load_from_formula(cond, pos, name_to_sort);
                self.load_from_formula(cond, !pos, name_to_sort);
                self.load_from_formula(then, pos, name_to_sort);
                self.load_from_formula(else_, pos, name_to_sort);
            }

            Term::Quantified {
                quantifier: _,
                binders,
                body,
            } => {
                let mut new_name_to_sort = name_to_sort.clone();
                new_name_to_sort.extend(
                    binders
                        .iter()
                        .map(|b| (b.name.clone(), FunctionSort::from_sort(&b.sort))),
                );
                self.vars.extend(
                    binders
                        .iter()
                        .cloned()
                        .map(|b| (b.name.clone(), FunctionSort::from_sort(&b.sort))),
                );
                self.load_from_formula(body, pos, &new_name_to_sort);
            }
            _ => self
                .terms
                .append(&mut Atomic::from_term(term, pos, name_to_sort)),
        };
    }

    fn load_from_ite(&mut self, term: &Term, name_to_sort: &HashMap<String, FunctionSort>) {
        if let Term::Ite {
            cond,
            then: _,
            else_: _,
        } = term
        {
            self.load_from_formula(cond, true, name_to_sort);
            self.load_from_formula(cond, false, name_to_sort);
        }
    }

    fn integer_bounds(&self) -> Vec<Term> {
        let mut bounds = vec![];
        for atomic in &self.terms {
            if let Atomic::LessThan(t1, t2, _) = atomic {
                if is_only_arith(t1) && is_only_arith(t2) {
                    bounds.push(t1.clone());
                    bounds.push(t2.clone());
                }
            }
        }

        bounds
    }
}

pub struct Fact {
    pub predicate: String,
    pub args: Vec<String>,
    pub atomics: Vec<Atomic>,
}

pub struct Update {
    pub predicate: String,
    pub args: Vec<String>,
    pub vars: Vec<(String, FunctionSort)>,
    pub atomics: Vec<Atomic>,
}

pub struct LinearQuery {
    pub predicate: String,
    pub args: Vec<String>,
    pub vars: Vec<(String, FunctionSort)>,
    pub atomics: Vec<Atomic>,
}

impl Display for LinearQuery {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Query:\n")?;
        write!(f, "  Predicate: {}\n", self.predicate)?;
        write!(f, "  Arguments: {:?}\n", self.args)?;
        write!(f, "  Variables:\n")?;
        for (name, sort) in &self.vars {
            write!(f, "    {}: {}\n", name, sort)?;
        }
        write!(f, "    Atomics:\n")?;
        for a in &self.atomics {
            write!(f, "      {}\n", a)?;
        }
        Ok(())
    }
}

fn default_arg_name(i: usize) -> String {
    format!("__miner_arg_{i}")
}

fn default_quant_name(i: usize) -> String {
    format!("__miner_quant_{i}")
}

fn retain_atomics(atomics: &mut Vec<Atomic>, args: &[String], vars: &[(String, FunctionSort)]) {
    atomics.retain(|t| {
        t.ids()
            .iter()
            .all(|id| args.contains(id) || vars.iter().any(|(v, _)| v == id))
    });
}

impl Fact {
    pub fn from_chc(chc: &Chc) -> Self {
        assert!(chc.is_fact(), "CHC must be a fact");

        let predicate = chc.head.predicate().expect("Fact head must be a predicate");
        let mut atomics = Atomics::new();
        let name_to_sort: HashMap<String, FunctionSort> = chc
            .variables
            .iter()
            .map(|v| (v.name.clone(), v.sort.clone()))
            .collect();
        for component in &chc.body {
            match component {
                Component::Predicate(name, args) => {
                    panic!(
                        "Fact body should not contain predicates, found: {} with args: {:?}",
                        name, args
                    );
                }
                Component::Formulas(terms) => {
                    for term in terms {
                        atomics.load_from_formula(term, true, &name_to_sort);
                    }
                }
            }
        }

        let mut args: Vec<String> = vec![];
        for (i, s) in predicate.1.iter().enumerate() {
            match s {
                Substitutable::Name(name) | Substitutable::Term(Term::Id(name)) => {
                    args.push(name.clone())
                }
                Substitutable::Term(t) => {
                    let name = default_arg_name(i);
                    atomics
                        .terms
                        .push(Atomic::LessThan(Term::id(&name), t.clone(), false));
                    atomics
                        .terms
                        .push(Atomic::LessThan(t.clone(), Term::id(&name), false));
                    args.push(name);
                }
            }
        }
        atomics
            .terms
            .retain(|t| t.ids().iter().all(|id| args.contains(id)));

        Self {
            predicate: predicate.0.clone(),
            args,
            atomics: atomics.terms,
        }
    }

    pub fn rename_args(&mut self, renames: &HashMap<String, String>) {
        self.args = self
            .args
            .iter()
            .map(|arg| renames.get(arg).cloned().unwrap_or_else(|| arg.clone()))
            .collect();
        let substitution: NameSubstitution = renames
            .iter()
            .map(|(k, v)| ((k.clone(), 0), Substitutable::name(v)))
            .collect();
        for atomic in &mut self.atomics {
            atomic.rename_symbols(&substitution);
        }
    }
}

impl Update {
    pub fn from_chc(chc: &Chc) -> Self {
        let predicate = chc
            .head
            .predicate()
            .map(|(name, args)| (name.clone(), args.iter().map(|s| s.to_name()).collect_vec()))
            .expect("Update head must be a predicate");
        let is_arg = |name: &String| predicate.1.contains(name);

        let old_predicates: Vec<_> = chc
            .body
            .iter()
            .filter_map(|p| match p {
                Component::Predicate(name, args) if name == &predicate.0 => {
                    Some((name.clone(), args.iter().map(|s| s.to_name()).collect_vec()))
                }
                _ => None,
            })
            .collect();

        let name_to_sort: HashMap<_, _> = chc
            .variables
            .iter()
            .map(|v| (v.name.clone(), v.sort.clone()))
            .collect();

        let mut atomics_for_bounds = Atomics::new();
        for t in chc.terms().iter() {
            atomics_for_bounds.load_from_formula(t, true, &name_to_sort);
        }
        let bounds = atomics_for_bounds.integer_bounds();

        if old_predicates.len() == 1 && old_predicates[0].0 == predicate.0 {
            let old_predicate = &old_predicates[0];
            assert_eq!(predicate.1.len(), old_predicate.1.len());
            let is_old_arg = |name: &String| old_predicate.1.contains(name);
            let arg_subst: NameSubstitution = predicate
                .1
                .iter()
                .zip(old_predicate.1.iter())
                .map(|(new, old)| ((old.clone(), 0), Substitutable::name(new)))
                .collect();

            let mut assignments: HashSet<_> = chc
                .terms()
                .iter()
                .flat_map(|t| Assignment::in_term(t, &name_to_sort))
                .collect();
            saturate_assignments(&mut assignments);

            let mut atomics = vec![];
            for a in assignments {
                match &a {
                    Assignment::Int(_, _) => (),
                    Assignment::ArrayStore {
                        array,
                        old_array,
                        index,
                        value,
                    } => {
                        if is_arg(array)
                            && is_old_arg(old_array)
                            && index.ids().iter().all(is_old_arg)
                            && value.ids().iter().all(is_old_arg)
                        {
                            let new_index = rename_symbols(index, &arg_subst);
                            let new_value = rename_symbols(value, &arg_subst);
                            if new_value.ids().is_empty() {
                                let quant_index = Term::id(&default_quant_name(0));
                                let quant_select =
                                    Term::array_select(Term::id(array), &quant_index);

                                println!("Adding assignment: {array}[{quant_index}] := {new_value} (from {old_array})");
                                // Add index bounds
                                atomics.push(Atomic::LessThan(
                                    quant_index.clone(),
                                    new_index.clone(),
                                    false,
                                ));
                                atomics.push(Atomic::LessThan(new_index, quant_index, false));

                                // Add array value atomics
                                atomics.push(Atomic::LessThan(
                                    quant_select.clone(),
                                    new_value.clone(),
                                    false,
                                ));
                                atomics.push(Atomic::LessThan(new_value, quant_select, false));
                            } else {
                                for index_id in new_index.ids() {
                                    if name_to_sort.get(&index_id).is_some_and(|s| s.is_int()) {
                                        let index_id_subst = NameSubstitution::from_iter([(
                                            (index_id.clone(), 0),
                                            Substitutable::name(default_quant_name(0)),
                                        )]);
                                        let quant_index =
                                            rename_symbols(&new_index, &index_id_subst);
                                        let quant_value =
                                            rename_symbols(&new_value, &index_id_subst);
                                        println!("Adding assignment: {array}[{quant_index}] := {quant_value} (from {old_array})");
                                        let quant_select =
                                            Term::array_select(Term::id(array), quant_index);
                                        atomics.push(Atomic::LessThan(
                                            quant_select.clone(),
                                            quant_value.clone(),
                                            false,
                                        ));
                                        atomics.push(Atomic::LessThan(
                                            quant_value.clone(),
                                            quant_select,
                                            false,
                                        ));
                                    }
                                }
                            }
                        }
                    }
                }
            }

            let args = predicate.1;
            let vars = if atomics.is_empty() {
                vec![]
            } else {
                vec![(default_quant_name(0), FunctionSort::int())]
            };

            for (v, s) in &vars {
                if s.is_int() {
                    for bound in &bounds {
                        println!("Adding bound for {v}: {bound}");
                        let new_bound = rename_symbols(bound, &arg_subst);
                        if new_bound.ids().len() <= 1 {
                            atomics.push(Atomic::LessThan(Term::id(v), new_bound.clone(), false));
                            atomics.push(Atomic::LessThan(new_bound.clone(), Term::id(v), false));
                            atomics.push(Atomic::LessThan(Term::id(v), new_bound.clone(), true));
                            atomics.push(Atomic::LessThan(new_bound, Term::id(v), true));
                        }
                    }
                }
            }

            retain_atomics(&mut atomics, &args, &vars);

            Self {
                predicate: predicate.0,
                args,
                vars,
                atomics,
            }
        } else {
            unimplemented!(
                "Unimplemented for updates with multiple old predicates or different names: new={}, old={}",
                predicate.0,
                old_predicates.iter().map(|(n, _)| n).join(", ")
            );
        }
    }

    pub fn rename_args_and_vars(&mut self, renames: &HashMap<String, String>) {
        self.args = self
            .args
            .iter()
            .map(|arg| renames.get(arg).cloned().unwrap_or_else(|| arg.clone()))
            .collect();
        self.vars = self
            .vars
            .iter()
            .map(|(name, sort)| {
                (
                    renames.get(name).cloned().unwrap_or_else(|| name.clone()),
                    sort.clone(),
                )
            })
            .collect();
        let substitution: NameSubstitution = renames
            .iter()
            .map(|(k, v)| ((k.clone(), 0), Substitutable::name(v)))
            .collect();
        for atomic in &mut self.atomics {
            atomic.rename_symbols(&substitution);
        }
    }
}

impl LinearQuery {
    pub fn from_chc(chc: &Chc) -> Self {
        assert!(
            chc.is_linear() && chc.is_query(),
            "CHC must be a linear query"
        );

        let mut predicate = None;
        let mut arguments: Option<Vec<String>> = None;
        let mut atomics = Atomics::new();
        let name_to_sort: HashMap<String, FunctionSort> = chc
            .variables
            .iter()
            .map(|v| (v.name.clone(), v.sort.clone()))
            .collect();
        for component in &chc.body {
            match component {
                Component::Predicate(name, args) => {
                    assert!(
                        predicate.is_none() && arguments.is_none(),
                        "Linear CHC query must have exactly one predicate"
                    );
                    predicate = Some(name.clone());
                    arguments = Some(args.iter().map(|a| a.to_name()).collect());
                }
                Component::Formulas(terms) => {
                    for term in terms {
                        atomics.load_from_formula(term, false, &name_to_sort);
                    }
                }
            }
        }

        if let Component::Formulas(terms) = &chc.head {
            for term in terms {
                atomics.load_from_formula(term, true, &name_to_sort);
            }
        }

        let predicate = predicate.expect("Linear CHC query must have at least one predicate");
        let args = arguments.expect("Linear CHC query must have at least one predicate");
        let vars: Vec<(String, FunctionSort)> = chc
            .variables
            .iter()
            .map(|v| (v.name.clone(), v.sort.clone()))
            .chain(
                atomics
                    .vars
                    .iter()
                    .map(|(name, sort)| (name.clone(), sort.clone())),
            )
            .filter(|(name, sort)| !args.contains(&name) && sort.is_int())
            .collect();

        retain_atomics(&mut atomics.terms, &args, &vars);

        Self {
            predicate,
            args,
            vars,
            atomics: atomics.terms,
        }
    }

    pub fn rename_args_and_vars(&mut self, renames: &HashMap<String, String>) {
        self.args = self
            .args
            .iter()
            .map(|arg| renames.get(arg).cloned().unwrap_or_else(|| arg.clone()))
            .collect();
        self.vars = self
            .vars
            .iter()
            .map(|(name, sort)| {
                (
                    renames.get(name).cloned().unwrap_or_else(|| name.clone()),
                    sort.clone(),
                )
            })
            .collect();
        let substitution: NameSubstitution = renames
            .iter()
            .map(|(k, v)| ((k.clone(), 0), Substitutable::name(v)))
            .collect();
        for atomic in &mut self.atomics {
            atomic.rename_symbols(&substitution);
        }
    }
}

use core::panic;
use std::{collections::HashMap, fmt::Display};

use fly::{
    syntax::{BinOp, NumRel, Term, UOp},
    term::subst::{rename_symbols, NameSubstitution, Substitutable},
};

use crate::chc::{Chc, Component, FunctionSort};

pub enum Atomic {
    /// A less-than comparison between two terms.
    /// The boolean indicates whether the comparison is strict (true) or non-strict (false).
    LessThan(Term, Term, bool),
    /// An atomic formula represented by a term and an optional polarity.
    /// The polarity indicates whether the formula is positive (Some(true)) or negative (Some(false)).
    /// If the polarity is None, it indicates that the formula may be used both positively and negatively.
    Atom(Term, Option<bool>),
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
}

/// A structure to hold the atomic formulas and variables extracted from a CHC.
pub struct Atomics {
    pub terms: Vec<Atomic>,
    pub vars: Vec<(String, FunctionSort)>,
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
            Term::NAryOp(_, terms) => {
                for t in terms {
                    self.load_from_formula(t, pos, name_to_sort);
                }
            }
            Term::Ite { cond, then, else_ } => {
                self.load_from_formula(cond, pos, name_to_sort);
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
}

pub struct Fact {
    pub predicate: String,
    pub args: Vec<String>,
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

        Self {
            predicate: predicate.0.clone(),
            args: predicate.1.iter().map(|a| a.to_name()).collect(),
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

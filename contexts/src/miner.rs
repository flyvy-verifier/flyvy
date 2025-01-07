use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

use fly::{
    syntax::{BinOp, NOp, Term, UOp},
    term::subst::{rename_symbols, NameSubstitution, Substitutable},
};
use formats::chc::{Chc, ChcSystem};
use itertools::Itertools;

use crate::{
    alg::PredicateConfig,
    arith::{ArithExpr, IneqTemplates},
};

// TODO: Make sure the substitution only uses fresh names
// TODO: Flatten constant expressions

/// A type of term mined for language construction.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TermType {
    /// Invalid type (cannot be used to construct atoms)
    Invalid,
    /// Unknown type
    Unknown,
    /// Quantifier integer variable
    QuantifiedIntVar,
    /// Array index type
    ArrayIndex,
    /// Array entry type
    ArrayEntry,
    /// Type used both as array index and array entry
    ArrayIndexEntry,
}

#[derive(Default)]
pub struct MinedTerms {
    array_index_ids: HashSet<String>,
    quant_int_var: HashSet<Term>,
    array_indices: HashSet<Term>,
    array_entries: HashSet<Term>,
    int_atomics: HashSet<Term>,
}

impl TermType {
    fn unify(self, other: Self) -> Self {
        if self == other {
            return self;
        }
        match (self, other) {
            (Self::Unknown, _) => other,
            (_, Self::Unknown) => self,
            (
                Self::ArrayIndex | Self::ArrayIndexEntry,
                Self::ArrayEntry | Self::ArrayIndexEntry,
            )
            | (
                Self::ArrayEntry | Self::ArrayIndexEntry,
                Self::ArrayIndex | Self::ArrayIndexEntry,
            ) => Self::ArrayIndexEntry,
            _ => panic!("conflicting term types: {self:?}, {other:?}"),
        }
    }
}

impl MinedTerms {
    fn add(&mut self, term: Term, ttype: TermType) {
        self.add_int_atomics(&term, ttype);
        match ttype {
            TermType::Unknown | TermType::Invalid => (),
            TermType::QuantifiedIntVar => {
                self.quant_int_var.insert(term);
            }
            TermType::ArrayIndex => {
                self.array_indices.insert(term);
            }
            TermType::ArrayEntry => {
                self.array_entries.insert(term);
            }
            TermType::ArrayIndexEntry => {
                self.array_indices.insert(term.clone());
                self.array_entries.insert(term);
            }
        }
    }

    fn add_int_atomics(&mut self, term: &Term, ttype: TermType) {
        match (term, ttype) {
            (
                Term::Id(_),
                TermType::QuantifiedIntVar | TermType::ArrayIndex | TermType::ArrayIndexEntry,
            )
            | (
                Term::ArraySelect { array: _, index: _ },
                TermType::ArrayEntry | TermType::ArrayIndexEntry,
            ) => {
                self.int_atomics.insert(term.clone());
            }
            (Term::NumOp(_, ts), _) => {
                for t in ts {
                    self.add_int_atomics(t, ttype);
                }
            }
            _ => (),
        }
    }

    fn mine(
        &mut self,
        term: &Term,
        known: &HashMap<Term, TermType>,
        assumed_ttype: TermType,
    ) -> TermType {
        let ttype = assumed_ttype.unify(*known.get(term).unwrap_or(&TermType::Unknown));
        ttype.unify(match term {
            Term::Literal(_) => TermType::Invalid,
            Term::Int(_) => TermType::Unknown,
            Term::Id(name) => {
                if self.array_index_ids.contains(name) {
                    TermType::ArrayIndex
                } else {
                    TermType::Unknown
                }
            }
            Term::App(_, _, _) => TermType::Invalid,
            Term::UnaryOp(UOp::Not, term) => self.mine(term, known, TermType::Invalid),
            Term::BinOp(BinOp::Equals | BinOp::NotEquals, t1, t2) | Term::NumRel(_, t1, t2) => {
                let tt1 = self.mine(t1, known, TermType::Unknown);
                let tt2 = self.mine(t2, known, TermType::Unknown);
                let tt = tt1.unify(tt2);
                self.add(t1.as_ref().clone(), tt);
                self.add(t2.as_ref().clone(), tt);
                TermType::Invalid
            }
            Term::BinOp(BinOp::Iff | BinOp::Implies, t1, t2) => {
                self.mine(t1, known, TermType::Invalid);
                self.mine(t2, known, TermType::Invalid);
                TermType::Invalid
            }
            Term::NAryOp(NOp::And | NOp::Or, ts) => {
                for t in ts {
                    self.mine(t, known, TermType::Invalid);
                }
                TermType::Invalid
            }
            Term::ArrayStore {
                array,
                index,
                value,
            } => {
                self.mine(array, known, TermType::Invalid);
                self.mine(index, known, TermType::ArrayIndex);
                self.mine(value, known, TermType::ArrayEntry);
                self.add(index.as_ref().clone(), TermType::ArrayIndex);
                TermType::Invalid
            }
            Term::ArraySelect { array, index } => {
                self.mine(array, known, TermType::Invalid);
                self.mine(index, known, TermType::ArrayIndex);
                self.add(index.as_ref().clone(), TermType::ArrayIndex);
                TermType::ArrayEntry
            }
            Term::NumOp(_, ts) => {
                let mut tt = ttype;
                for t in ts {
                    tt = tt.unify(self.mine(t, known, ttype));
                }
                tt
            }
            Term::Ite { cond, then, else_ } => {
                self.mine(cond, known, TermType::Invalid);
                let then_tt = self.mine(then, known, TermType::Unknown);
                let else_tt = self.mine(else_, known, TermType::Unknown);
                then_tt.unify(else_tt)
            }
            _ => unimplemented!("{term}"),
        })
    }

    fn add_quant_int_var(&mut self, name: &str) {
        self.array_index_ids.insert(name.to_string());

        self.add(Term::id(name), TermType::QuantifiedIntVar);

        let replace_index_id = |t: &Term| -> Vec<Term> {
            t.ids()
                .intersection(&self.array_index_ids)
                .map(|id| {
                    let mut substitution = NameSubstitution::new();
                    substitution.insert((id.clone(), 0), Substitutable::name(name));
                    rename_symbols(t, &substitution)
                })
                .collect()
        };

        let entries = self
            .array_entries
            .iter()
            .flat_map(|entry| replace_index_id(entry))
            .collect_vec();

        for term in entries {
            self.add(term, TermType::ArrayEntry);
        }
    }

    fn retain_ids(&mut self, ids: &HashSet<String>) {
        self.int_atomics.retain(|t| t.ids().is_subset(&ids));
        self.array_index_ids.retain(|t| ids.contains(t));
        self.array_indices.retain(|t| t.ids().is_subset(&ids));
        self.array_entries.retain(|t| t.ids().is_subset(&ids));
    }

    pub fn inequalities(&self) -> (Vec<Term>, IneqTemplates) {
        let int_atomics: Vec<Term> = self.int_atomics.iter().cloned().collect();
        let atomic_to_index =
            |term: &Term| -> usize { int_atomics.iter().position(|t| t == term).unwrap() };
        let mut ineqs = IneqTemplates::new(false);

        for (qi, ind) in self
            .quant_int_var
            .iter()
            .cartesian_product(&self.array_indices)
        {
            let e1 = ArithExpr::<usize>::from_term(qi, atomic_to_index);
            let e2 = ArithExpr::<usize>::from_term(ind, atomic_to_index);

            for expr in [&e1 - &e2, &e2 - &e1] {
                if !expr.is_constant() {
                    ineqs.add_range(expr, (-1, 0));
                }
            }
        }

        for entries in self.array_entries.iter().combinations(2) {
            let e1 = ArithExpr::<usize>::from_term(entries[0], atomic_to_index);
            let e2 = ArithExpr::<usize>::from_term(entries[1], atomic_to_index);

            for expr in [&e1 - &e2, &e2 - &e1] {
                if !expr.is_constant() {
                    ineqs.add_range(expr, (-1, 0));
                }
            }
        }

        (int_atomics, ineqs)
    }
}

impl Display for MinedTerms {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "quantified integer variables:")?;
        for t in &self.quant_int_var {
            writeln!(f, "    {t}")?;
        }
        writeln!(f, "array indices:")?;
        for t in &self.array_indices {
            writeln!(f, "    {t}")?;
        }
        writeln!(f, "array entries:")?;
        for t in &self.array_entries {
            writeln!(f, "    {t}")?;
        }
        Ok(())
    }
}

#[derive(Default)]
pub struct ChcMiner {
    pub miners: HashMap<String, MinedTerms>,
}

impl ChcMiner {
    fn mine_chc(&mut self, chc: &Chc) {
        let chc_terms = chc.terms();
        let mut chc_predicates = chc.predicates();
        if let Some((name, args)) = chc.head.predicate() {
            chc_predicates.push((name.clone(), args.clone()));
        }

        for (pred, args) in &chc_predicates {
            let substitution: NameSubstitution = args
                .iter()
                .enumerate()
                .filter_map(|(i, a)| match a {
                    Substitutable::Name(name) | Substitutable::Term(Term::Id(name)) => Some((
                        (name.clone(), 0),
                        Substitutable::Name(PredicateConfig::arg_name(i)),
                    )),
                    _ => None,
                })
                .collect();
            let miner = self.miners.entry(pred.clone()).or_default();

            let mut known = HashMap::new();
            let mut index_ids = vec![];
            for v in &chc.variables {
                if v.sort.is_int() {
                    let name = match substitution.get(&(v.name.clone(), 0)) {
                        Some(Substitutable::Name(n)) => n.clone(),
                        _ => v.name.clone(),
                    };
                    known.insert(Term::id(&name), TermType::ArrayIndex);
                    index_ids.push(name);
                }
            }
            miner.array_index_ids.extend(index_ids.iter().cloned());
            for t in chc_terms.iter().map(|t| rename_symbols(t, &substitution)) {
                miner.mine(&t, &known, TermType::Invalid);
            }
        }
    }

    pub fn mine_chcs(&mut self, chc_sys: &ChcSystem, quantified_indices: usize) {
        // Mine terms
        for chc in &chc_sys.chcs {
            self.mine_chc(chc);
        }

        for (name, terms) in &mut self.miners {
            let pred = chc_sys.predicates.iter().find(|p| &p.name == name).unwrap();
            let mut ids: HashSet<String> = (0..pred.args.len())
                .map(PredicateConfig::arg_name)
                .collect();
            // Add quantified index
            if pred.args.iter().any(|arg| arg.is_array_int_int()) {
                for i in 0..quantified_indices {
                    terms.add_quant_int_var(&PredicateConfig::quant_name(i));
                    ids.insert(PredicateConfig::quant_name(i));
                }
            }
            // Remove terms containing non-argument identifiers
            terms.retain_ids(&ids);
        }
    }
}

impl Display for ChcMiner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (name, miner) in &self.miners {
            writeln!(f, "---------- {name} ----------")?;
            writeln!(f, "{miner}")?;
        }
        Ok(())
    }
}

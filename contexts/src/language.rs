//! Tools to determine the language used in inferece, e.g. for unknown predicates in CHC solving.

use std::collections::{HashMap, HashSet};

use crate::{alg::PredicateConfig, arith::ArithExpr, logic::Literal};
use fly::syntax::{BinOp, NOp, NumRel, Sort, Term, UOp};
use formats::chc::{Chc, ChcSystem, Component, FunctionSort};
use itertools::Itertools;

/// A collection of atomic literals.
pub struct Atomics {
    /// Boolean atoms.
    pub bools: Vec<Term>,
    /// Atomic integer expressions.
    pub ints: Vec<Term>,
    /// Atomic array expression.
    pub arrays: Vec<Term>,
    /// The set of literals.
    pub literals: HashSet<Literal>,
}

impl Atomics {
    /// Create a new atomics set.
    pub fn new(bools: Vec<Term>, ints: Vec<Term>, arrays: Vec<Term>) -> Self {
        Self {
            bools,
            ints,
            arrays,
            literals: HashSet::new(),
        }
    }

    fn get_int(&mut self, term: &Term) -> usize {
        if let Some(index) = (0..self.ints.len()).find(|i| &self.ints[*i] == term) {
            index
        } else {
            self.ints.push(term.clone());
            self.ints.len() - 1
        }
    }

    fn add_from_aggr(&mut self, aggr: &AggregatedTerms) {
        for expr in &aggr.exprs_leq_0 {
            let ints = expr.ints();
            let arrays = expr.arrays();

            let get_asgn = |from: &[usize], to: Vec<Term>| -> HashMap<_, _> {
                assert_eq!(from.len(), to.len());
                from.iter().cloned().zip(to.into_iter()).collect()
            };

            for (ints_vals, arrays_vals) in self
                .ints
                .clone()
                .into_iter()
                .permutations(ints.len())
                .cartesian_product(self.arrays.clone().into_iter().permutations(arrays.len()))
            {
                let ints_asgn = get_asgn(&ints, ints_vals);
                let arrays_asgn = get_asgn(&arrays, arrays_vals);
                let mut new_expr = ArithExpr::from_expr(expr, |temp| {
                    self.get_int(&match temp {
                        AtomicTemplate::Int(i) => ints_asgn[i].clone(),
                        AtomicTemplate::Select(a, i) => Term::ArraySelect {
                            array: Box::new(arrays_asgn[a].clone()),
                            index: Box::new(ints_asgn[i].clone()),
                        },
                    })
                });
                let bound = -new_expr.constant;
                new_expr.constant = 0;
                self.literals.insert(Literal::Leq(new_expr, bound));
            }
        }
    }
}

/// Something parameterized by argument names and quantified variables.
#[derive(Default)]
pub struct Parameterized<T> {
    /// The arguments.
    pub args: Vec<(String, FunctionSort)>,
    /// Universally quantified integer variables
    pub univ_ints: Vec<String>,
    /// The parameterized content.
    pub content: T,
}

/// A template for atoms in arithmetic expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AtomicTemplate {
    /// An atomic integer term, identified using a [`usize`].
    Int(usize),
    /// An atomic selection term, identifier using [`usize`] identifiers for the array and index terms.
    Select(usize, usize),
}

struct AggregatedTerms {
    exprs_leq_0: HashSet<ArithExpr<AtomicTemplate>>,
}

type PredicateToTerms = HashMap<String, Parameterized<AggregatedTerms>>;
type PredicatesToAtomics = HashMap<String, Parameterized<Atomics>>;

impl AggregatedTerms {
    fn new() -> Self {
        Self {
            exprs_leq_0: HashSet::new(),
        }
    }

    fn len(&self) -> usize {
        self.exprs_leq_0.len()
    }

    fn add_from_lt(&mut self, left: &Term, right: &Term, strict: bool) {
        let (mut expr, _, _) = match ArithExpr::from_terms(&[left, right]) {
            Some((exprs, ints, arrays)) => (exprs[0].clone() - exprs[1].clone(), ints, arrays),
            _ => return,
        };

        if expr.summands.is_empty() {
            return;
        }

        if strict {
            expr.constant += 1;
        }

        expr.normalize_leq_0();
        self.exprs_leq_0.insert(expr);
    }

    fn add_literals_from_term(&mut self, term: &Term, sign: bool) {
        match (term, sign) {
            // t1 = t2 ---> t1 <= t2, t2 <= t1
            (Term::BinOp(BinOp::Equals, t1, t2), true)
            | (Term::BinOp(BinOp::NotEquals, t1, t2), false) => {
                self.add_from_lt(t1, t2, false);
                self.add_from_lt(t2, t1, false);
            }
            // t1 != t2 ---> t1 < t2, t2 < t1
            (Term::BinOp(BinOp::Equals, t1, t2), false)
            | (Term::BinOp(BinOp::NotEquals, t1, t2), true) => {
                self.add_from_lt(t1, t2, true);
                self.add_from_lt(t2, t1, true);
            }
            // t1 <= t2 ---> t1 <= t2
            (Term::NumRel(NumRel::Leq, t1, t2), true)
            | (Term::NumRel(NumRel::Gt, t1, t2), false) => {
                self.add_from_lt(t1, t2, false);
            }
            // t1 > t2 ---> t2 < t1
            (Term::NumRel(NumRel::Leq, t1, t2), false)
            | (Term::NumRel(NumRel::Gt, t1, t2), true) => {
                self.add_from_lt(t2, t1, true);
            }
            // t1 >= t2 ---> t2 <= t1
            (Term::NumRel(NumRel::Geq, t1, t2), true)
            | (Term::NumRel(NumRel::Lt, t1, t2), false) => {
                self.add_from_lt(t2, t1, false);
            }
            // t1 < t2 ---> t1 < t2
            (Term::NumRel(NumRel::Geq, t1, t2), false)
            | (Term::NumRel(NumRel::Lt, t1, t2), true) => {
                self.add_from_lt(t1, t2, true);
            }
            _ => (),
        }
    }

    fn mine_from_term(&mut self, term: &Term, sign: bool) {
        match term {
            // There are no literals to add
            Term::Literal(_) | Term::Id(_) | Term::App(_, _, _) => (),
            // The term itself is a literal that should be added
            Term::BinOp(BinOp::Equals | BinOp::NotEquals, _, _) | Term::NumRel(_, _, _) => {
                self.add_literals_from_term(term, sign);
            }
            // Push negation inwards
            Term::UnaryOp(UOp::Not, t) => self.mine_from_term(t, !sign),
            // Handle other logical connectives
            Term::BinOp(BinOp::Implies, t1, t2) => {
                self.mine_from_term(t1, !sign);
                self.mine_from_term(t2, sign);
            }
            Term::BinOp(BinOp::Iff, t1, t2) => {
                self.mine_from_term(t1, sign);
                self.mine_from_term(t1, !sign);
                self.mine_from_term(t2, sign);
                self.mine_from_term(t2, !sign);
            }
            Term::NAryOp(NOp::Or | NOp::And, ts) => {
                for t in ts {
                    self.mine_from_term(t, sign);
                }
            }
            _ => unimplemented!(),
        }
    }

    fn mine_from_other(&mut self, other: &Self, sign: bool) {
        for mut expr in other.exprs_leq_0.iter().cloned() {
            if !sign {
                expr.negate_leq_0();
            }
            self.exprs_leq_0.insert(expr);
        }
    }

    fn mine_from_component(
        &mut self,
        component: &Component,
        to_terms: &PredicateToTerms,
        sign: bool,
    ) {
        match component {
            Component::Predicate(name, args) => {
                let terms = &to_terms[name];
                assert_eq!(args.len(), terms.args.len());
                self.mine_from_other(&terms.content, sign);
            }
            Component::Formulas(ts) => {
                for t in ts {
                    self.mine_from_term(t, sign);
                }
            }
        }
    }

    fn mine_from_chc(&mut self, chc: &Chc, to_terms: &PredicateToTerms, for_component: usize) {
        let for_head = for_component == chc.body.len();

        for (i, component) in chc.body.iter().enumerate() {
            if i != for_component && matches!(component, Component::Formulas(_)) {
                self.mine_from_component(component, to_terms, for_head);
            }
        }

        if !for_head {
            self.mine_from_component(&chc.head, to_terms, true);
        }
    }
}

impl Parameterized<AggregatedTerms> {
    fn mine_from_aggr(&mut self, aggr: &AggregatedTerms) {
        self.content
            .exprs_leq_0
            .extend(aggr.exprs_leq_0.iter().cloned());
    }
}

/// Analyse the given CHC system and return a set of literals for each of its predicates.
pub fn atomics_in_chc_sys(chc_sys: &ChcSystem, univ_indices: usize) -> PredicatesToAtomics {
    let univ_ints = (0..univ_indices)
        .map(PredicateConfig::quant_name)
        .collect_vec();
    let mut to_terms: PredicateToTerms = chc_sys
        .predicates
        .iter()
        .map(|p| {
            (
                p.name.clone(),
                Parameterized {
                    args: p
                        .args
                        .iter()
                        .enumerate()
                        .map(|(i, s)| (PredicateConfig::arg_name(i), s.clone()))
                        .collect(),
                    univ_ints: univ_ints.clone(),
                    content: AggregatedTerms::new(),
                },
            )
        })
        .collect();

    let mut analyze_component = |chc: &Chc, i: usize, name: &String| -> bool {
        let mut agg = AggregatedTerms::new();
        agg.mine_from_chc(chc, &to_terms, i);

        let par_terms = to_terms.get_mut(name).unwrap();

        let old_len = par_terms.content.len();
        par_terms.mine_from_aggr(&agg);
        old_len != par_terms.content.len()
    };

    let mut any_changed = true;
    while any_changed {
        any_changed = false;

        for chc in &chc_sys.chcs {
            for (i, c) in chc.body.iter().enumerate() {
                if let Component::Predicate(name, _) = c {
                    any_changed |= analyze_component(chc, i, name);
                }
            }

            if let Component::Predicate(name, _) = &chc.head {
                any_changed |= analyze_component(chc, chc.body.len(), name);
            }
        }
    }

    let int_sort = FunctionSort(vec![], Sort::Int);
    let array_sort = FunctionSort(vec![], Sort::array(Sort::Int, Sort::Int));
    let to_lits = to_terms
        .into_iter()
        .map(|(name, terms)| {
            let mut ints = terms
                .args
                .iter()
                .filter(|(_, sort)| sort == &int_sort)
                .map(|(name, _)| Term::id(name))
                .collect_vec();
            let arrays = terms
                .args
                .iter()
                .filter(|(_, sort)| sort == &array_sort)
                .map(|(name, _)| Term::id(name))
                .collect_vec();
            if !arrays.is_empty() {
                ints.extend(terms.univ_ints.iter().map(|name| Term::id(name)));
            }
            let mut lits = Parameterized {
                args: terms.args.clone(),
                univ_ints: terms.univ_ints.clone(),
                content: Atomics::new(vec![], ints, arrays),
            };

            lits.content.add_from_aggr(&terms.content);

            (name, lits)
        })
        .collect();

    to_lits
}

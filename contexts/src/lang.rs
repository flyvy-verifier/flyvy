use std::collections::HashMap;

use fly::syntax::{IntType, Term};
use formats::{
    chc::{ChcSystem, FunctionSort, HoPredicateDecl},
    miner::{Atomic, Fact, LinearQuery},
};

use crate::{alg::PredicateConfig, arith::ArithExpr};

pub struct PredicateSynth {
    args: Vec<FunctionSort>,
    facts: Vec<Fact>,
    linear_queries: Vec<LinearQuery>,
    quantified: usize,
    bools: Vec<Term>,
    ints: Vec<Term>,
    leqs: Vec<(ArithExpr<usize>, (IntType, IntType))>,
}

pub struct LanguageSynth {
    predicates: HashMap<String, PredicateSynth>,
}

pub fn position_or_push(terms: &mut Vec<Term>, term: &Term) -> usize {
    if let Some(i) = terms.iter().position(|t| t == term) {
        i
    } else {
        terms.push(term.clone());
        terms.len() - 1
    }
}

impl PredicateSynth {
    pub fn new(pred: &HoPredicateDecl) -> Self {
        Self {
            args: pred.args.clone(),
            facts: vec![],
            linear_queries: vec![],
            quantified: 0,
            bools: vec![],
            ints: vec![],
            leqs: vec![],
        }
    }

    pub fn add_fact(&mut self, fact: Fact) {
        let renames = fact
            .args
            .iter()
            .enumerate()
            .map(|(i, arg)| (arg.clone(), PredicateConfig::arg_name(i)))
            .collect();
        let mut fact = fact;
        fact.rename_args(&renames);
        self.facts.push(fact);
    }

    pub fn add_linear_query(&mut self, mut query: LinearQuery) {
        let renames = query
            .args
            .iter()
            .enumerate()
            .map(|(i, arg)| (arg.clone(), PredicateConfig::arg_name(i)))
            .chain(
                query
                    .vars
                    .iter()
                    .enumerate()
                    .map(|(i, (name, _))| (name.clone(), PredicateConfig::quant_name(i))),
            )
            .collect();
        query.rename_args_and_vars(&renames);
        self.linear_queries.push(query);
    }

    pub fn extend_with_bounds(&mut self) {
        for i in 0..self.quantified {
            let quant =
                ArithExpr::<usize>::from_term(&Term::Id(PredicateConfig::quant_name(i)), |t| {
                    position_or_push(&mut self.ints, t)
                })
                .unwrap();
            for (j, fsort) in self.args.iter().enumerate() {
                if fsort.is_int() {
                    let arg = ArithExpr::<usize>::from_term(
                        &Term::Id(PredicateConfig::arg_name(j)),
                        |t| position_or_push(&mut self.ints, t),
                    )
                    .unwrap();
                    self.leqs.push((&arg - &quant, (-1, 0)));
                    self.leqs.push((&quant - &arg, (-1, 0)));
                }
            }
            self.leqs.push((quant, (-1, -1)));
            // for query in &self.linear_queries {
            //     for atomic in &query.atomics.terms {
            //         if let Atomic::LessThan(t1, t2, _) = atomic {
            //             if is_only_arith(t1) {
            //                 let x = ArithExpr::<usize>::from_term(t1, |t| {
            //                     position_or_push(&mut self.ints, t)
            //                 })
            //                 .unwrap();
            //                 self.leqs.push((&x - &quant, (-1, 0)));
            //                 self.leqs.push((&quant - &x, (-1, 0)));
            //             }
            //             if is_only_arith(t2) {
            //                 let x = ArithExpr::<usize>::from_term(t2, |t| {
            //                     position_or_push(&mut self.ints, t)
            //                 })
            //                 .unwrap();
            //                 self.leqs.push((&x - &quant, (-1, 0)));
            //                 self.leqs.push((&quant - &x, (-1, 0)));
            //             }
            //         }
            //     }
            // }
        }
    }

    pub fn extend_from_facts(&mut self) {
        for fact in &self.facts {
            for atomic in &fact.atomics {
                match atomic {
                    Atomic::LessThan(t1, t2, strict) => {
                        let x1 = ArithExpr::<usize>::from_term(t1, |t| {
                            position_or_push(&mut self.ints, t)
                        })
                        .unwrap();
                        let x2 = ArithExpr::<usize>::from_term(t2, |t| {
                            position_or_push(&mut self.ints, t)
                        })
                        .unwrap();
                        self.leqs
                            .push((&x1 - &x2, if *strict { (-1, -1) } else { (0, 0) }));
                    }
                    Atomic::Atom(t, _) if !self.bools.contains(t) => self.bools.push(t.clone()),
                    _ => (),
                }
            }
        }
    }

    pub fn extend_from_queries(&mut self) {
        for query in &self.linear_queries {
            self.quantified = self.quantified.max(query.vars.len());
            for atomic in &query.atomics {
                match atomic {
                    Atomic::LessThan(t1, t2, strict) => {
                        println!(
                            "Adding leq from query: {t1:?} <{} {t2:?}",
                            if !strict { "=" } else { "" }
                        );
                        let x1 = ArithExpr::<usize>::from_term(t1, |t| {
                            position_or_push(&mut self.ints, t)
                        })
                        .unwrap();
                        let x2 = ArithExpr::<usize>::from_term(t2, |t| {
                            position_or_push(&mut self.ints, t)
                        })
                        .unwrap();
                        self.leqs
                            .push((&x1 - &x2, if *strict { (-1, -1) } else { (0, 0) }));
                    }
                    Atomic::Atom(t, _) if !self.bools.contains(t) => self.bools.push(t.clone()),
                    _ => (),
                }
            }
        }
    }
}

impl LanguageSynth {
    pub fn new(chc_sys: &ChcSystem) -> Self {
        let mut predicates: HashMap<String, PredicateSynth> = chc_sys
            .predicates
            .iter()
            .map(|p| (p.name.clone(), PredicateSynth::new(p)))
            .collect();
        for chc in &chc_sys.chcs {
            if chc.is_linear() && chc.is_query() {
                let query = LinearQuery::from_chc(chc);
                predicates
                    .get_mut(&query.predicate)
                    .unwrap()
                    .add_linear_query(query);
            }
        }

        Self { predicates }
    }

    pub fn leqs_for(
        &mut self,
        predicate: &str,
    ) -> (
        usize,
        Vec<Term>,
        Vec<Term>,
        Vec<(ArithExpr<usize>, (IntType, IntType))>,
    ) {
        let synth = self.predicates.get_mut(predicate).unwrap();
        synth.extend_from_queries();
        synth.extend_from_facts();
        synth.extend_with_bounds();
        (
            synth.quantified,
            synth.bools.clone(),
            synth.ints.clone(),
            synth.leqs.clone(),
        )
    }
}

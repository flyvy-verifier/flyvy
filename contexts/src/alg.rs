//! Various algorithmic building blocks for using contexts in logical reasoning.

use std::collections::HashMap;

use crate::{
    context::{AttributeSet, Context, MultiAttribute, MultiContext, MultiObject},
    logic::*,
    sets::MultiAttributeSet,
};
use fly::{
    syntax::{NOp, RelationDecl, Signature, Sort, Term},
    term::subst::{rename_symbols, NameSubstitution},
};
use formats::chc::{Chc, ChcSystem, Component, SymbolicAssignment, SymbolicPredicate};
use itertools::Itertools;
use smtlib::sexp::InterpretedValue;
use solver::basics::{BasicSolver, BasicSolverResp, ModelOption, QueryConf};

fn prop_var(outer_index: usize, inner_index: usize) -> String {
    format!("__prop_{outer_index}_{inner_index}")
}

/// A sequence of propositional variables
pub struct PropVars {
    bools: Vec<String>,
}

fn prop_model_not_satisfies(f: &PropFormula, outer_index: usize) -> Term {
    match f {
        PropFormula::Bottom => Term::true_(),
        PropFormula::Atom(inner_index, false) => Term::Id(prop_var(outer_index, *inner_index)),
        PropFormula::Atom(inner_index, true) => {
            Term::not(Term::Id(prop_var(outer_index, *inner_index)))
        }
        PropFormula::Binary(Op::Or, f1, f2) => Term::and([
            prop_model_not_satisfies(f1, outer_index),
            prop_model_not_satisfies(f2, outer_index),
        ]),
        PropFormula::Binary(Op::And, f1, f2) => Term::or([
            prop_model_not_satisfies(f1, outer_index),
            prop_model_not_satisfies(f2, outer_index),
        ]),
        PropFormula::Nary(Op::Or, fs) => Term::and(
            fs.iter()
                .map(|ff| prop_model_not_satisfies(ff, outer_index)),
        ),
        PropFormula::Nary(Op::And, fs) => Term::or(
            fs.iter()
                .map(|ff| prop_model_not_satisfies(ff, outer_index)),
        ),
    }
}

/// A contruction for extracting a [`QuantifiedType`] from an SMT query.
pub struct Extractor {
    type_count: usize,
    type_length: usize,
    term: Term,
    vars: Vec<PropVars>,
}

impl Extractor {
    fn extract(&self, values: &HashMap<Term, InterpretedValue>) -> QuantifiedType {
        QuantifiedType(
            (0..self.type_count)
                .map(|outer_index| PropModel {
                    bools: (0..self.type_length)
                        .map(|inner_index| {
                            match &values[&Term::Id(prop_var(outer_index, inner_index))] {
                                InterpretedValue::B(b) => *b,
                                InterpretedValue::I(_) => unimplemented!(),
                            }
                        })
                        .collect(),
                })
                .collect(),
        )
    }

    fn extend_signature(&self, sig: &Signature) -> Signature {
        let mut extended_sig = sig.clone();
        for vs in &self.vars {
            for v in &vs.bools {
                extended_sig.relations.push(RelationDecl {
                    mutable: false,
                    name: v.clone(),
                    args: vec![],
                    sort: Sort::Bool,
                })
            }
        }

        extended_sig
    }

    fn not_satisfies(&self, f: &PropFormula) -> Term {
        Term::and((0..self.type_count).map(|outer_index| prop_model_not_satisfies(f, outer_index)))
    }
}

impl QuantifiedContext {
    fn to_term(&self, f: &PropFormula) -> Term {
        self.prefix.quantify(self.to_term_prop(f))
    }

    fn to_term_prop(&self, f: &PropFormula) -> Term {
        match f {
            PropFormula::Bottom => Term::false_(),
            PropFormula::Atom(i, b) => {
                if *b {
                    self.atoms[*i].clone()
                } else {
                    Term::not(&self.atoms[*i])
                }
            }
            PropFormula::Binary(Op::Or, f1, f2) => {
                Term::NAryOp(NOp::Or, vec![self.to_term_prop(f1), self.to_term_prop(f2)])
            }
            PropFormula::Binary(Op::And, f1, f2) => {
                Term::NAryOp(NOp::And, vec![self.to_term_prop(f1), self.to_term_prop(f2)])
            }
            PropFormula::Nary(Op::Or, fs) => {
                Term::NAryOp(NOp::Or, fs.iter().map(|ff| self.to_term_prop(ff)).collect())
            }
            PropFormula::Nary(Op::And, fs) => Term::NAryOp(
                NOp::And,
                fs.iter().map(|ff| self.to_term_prop(ff)).collect(),
            ),
        }
    }

    /// Create an extractor for extracting a [`QuantifiedType`] of the given size.
    /// The substitution is used to rename functions and relations in the atoms of the [`QuantifiedContext`]
    /// to those used by the extractor.
    pub fn extractor(&self, size: usize, substitution: &NameSubstitution) -> Extractor {
        assert!(size >= 1);

        let vars = (0..size)
            .map(|i| PropVars {
                bools: (0..self.atoms.len()).map(|j| prop_var(i, j)).collect(),
            })
            .collect_vec();

        let cubes = (0..size)
            .map(|i| {
                Term::and(
                    self.atoms
                        .iter()
                        .enumerate()
                        .map(|(j, a): (usize, &Term)| Term::iff(Term::id(&vars[i].bools[j]), a)),
                )
            })
            .collect_vec();

        let t = Term::not(self.prefix.quantify(Term::not(Term::or(cubes))));

        Extractor {
            type_count: size,
            type_length: self.atoms.len(),
            term: rename_symbols(&t, substitution),
            vars,
        }
    }
}

impl MultiContext<QuantifiedContext> {
    fn to_term(&self, f: &MultiAttribute<PropFormula>) -> Term {
        self.contexts[f.0].to_term(&f.1)
    }
}

struct PredicateSolution<S>
where
    S: AttributeSet<Object = QuantifiedType, Attribute = PropFormula>,
{
    arguments: Vec<String>,
    context: MultiContext<QuantifiedContext>,
    solution: MultiAttributeSet<S>,
}

/// A solution to a [`ChcSystem`].
pub struct ChcSolution<S>
where
    S: AttributeSet<Object = QuantifiedType, Attribute = PropFormula, Cont = QuantifiedContext>,
{
    solutions: HashMap<String, PredicateSolution<S>>,
}

impl<S> ChcSolution<S>
where
    S: AttributeSet<Object = QuantifiedType, Attribute = PropFormula, Cont = QuantifiedContext>,
{
    fn get_positive_cex<B: BasicSolver>(
        &self,
        solver: &B,
        chc_sys: &ChcSystem,
        size_limit: usize,
    ) -> Option<(String, MultiObject<QuantifiedType>)> {
        for size in 1..=size_limit {
            for chc in &chc_sys.chcs {
                if let Some(res) = self.get_positive_chc_cex(solver, chc, size) {
                    return Some(res);
                }
            }
        }

        None
    }

    fn get_positive_chc_cex<B: BasicSolver>(
        &self,
        solver: &B,
        chc: &Chc,
        size: usize,
    ) -> Option<(String, MultiObject<QuantifiedType>)> {
        let head_predicate = match chc.head {
            Component::Predicate(ref name, ref args) => (name, args),
            Component::Formulas(_) => return None,
        };

        let mut assignment = SymbolicAssignment::new();
        for (name, p) in &self.solutions {
            assignment.insert(
                name.clone(),
                SymbolicPredicate {
                    args: p.arguments.clone(),
                    formulas: p.solution.iter().map(|f| p.context.to_term(&f)).collect(),
                },
            );
        }

        // The hypothesis of the CHC
        let hyp = chc.instantiate_body(&assignment);
        // The solution for the predicate in the head
        let head_sol = &self.solutions[head_predicate.0];
        // The multiple contexts for formulas in the head
        let head_contexts = &head_sol.context.contexts;
        // The multiple sets of formulas of the head (matching the multiple contexts)
        let head_sets = &head_sol.solution.sets;
        // The substitution from the solution's arguments to the head's arguments
        assert_eq!(head_sol.arguments.len(), head_predicate.1.len());
        let head_subst = self.solutions[head_predicate.0]
            .arguments
            .iter()
            .zip(head_predicate.1)
            .map(|(old_v, new_v)| ((old_v.clone(), 0), (new_v.clone(), 0)))
            .collect();

        assert_eq!(head_contexts.len(), head_sets.len());
        for i in 0..head_contexts.len() {
            let extractor = head_contexts[i].extractor(size, &head_subst);
            let extended_sig = extractor.extend_signature(&chc.signature);
            let query_conf = QueryConf {
                sig: &extended_sig,
                n_states: 1,
                cancelers: None,
                model_option: ModelOption::None,
                evaluate: extractor
                    .vars
                    .iter()
                    .flat_map(|v| &v.bools)
                    .map(|name| Term::id(name))
                    .collect(),
                save_tee: false,
            };

            let f_count = head_sets[i].len();
            for (j, f) in head_sets[i].iter().enumerate() {
                log::info!("Querying context #{i}, formula {j} / {f_count}");
                let mut assertions = hyp.clone();
                assertions.push(extractor.term.clone());
                assertions.push(extractor.not_satisfies(&f));
                let resp = solver.check_sat(&query_conf, &assertions, &HashMap::new());

                match resp {
                    Ok(BasicSolverResp::Sat(_, vals)) => {
                        return Some((
                            head_predicate.0.clone(),
                            MultiObject(i, extractor.extract(&vals)),
                        ))
                    }
                    Ok(BasicSolverResp::Unsat(_)) => (),
                    _ => panic!("solver error {resp:?}"),
                }
            }
        }

        None
    }
}

impl<S> ToString for ChcSolution<S>
where
    S: AttributeSet<Object = QuantifiedType, Attribute = PropFormula, Cont = QuantifiedContext>,
{
    fn to_string(&self) -> String {
        let mut lines: Vec<String> = vec![];
        for (k, v) in &self.solutions {
            let args = v.arguments.iter().join(", ");
            lines.push(format!("predicate {k}({args}):"));
            for ref f in v.solution.iter() {
                let t = v.context.to_term(f);
                lines.push(format!("    {t}"));
            }
            lines.push("".to_string());
        }

        lines.iter().join("\n")
    }
}

/// A configuation for an unknown predicate in a CHC.
pub struct PredicateConfig {
    /// The name of the predicate.
    pub name: String,
    /// The names of arguments of the predicate.
    pub arguments: Vec<String>,
    /// The context the predicate ranges over.
    pub context: MultiContext<QuantifiedContext>,
}

/// Find the least-fixpoint solution of a [`ChcSystem`] with the given predicate configurations.
pub fn find_lfp<B, S>(solver: &B, chc_sys: &ChcSystem, cfg: Vec<PredicateConfig>) -> ChcSolution<S>
where
    B: BasicSolver,
    S: AttributeSet<Object = QuantifiedType, Attribute = PropFormula, Cont = QuantifiedContext>,
{
    let solutions = cfg
        .into_iter()
        .map(|p| {
            let solution = MultiAttributeSet::<S>::from_(&p.context, p.context.bottom());
            (
                p.name,
                PredicateSolution::<S> {
                    arguments: p.arguments,
                    context: p.context,
                    solution,
                },
            )
        })
        .collect();
    let mut chc_sol = ChcSolution { solutions };

    // TODO: handle increasing sizes

    while let Some((name, cex)) = chc_sol.get_positive_cex(solver, chc_sys, 1) {
        log::info!("Found CEX: {cex:?}");
        let pred_sol = chc_sol.solutions.get_mut(&name).unwrap();
        pred_sol.solution.weaken(&pred_sol.context, &cex);
    }

    chc_sol
}

#[cfg(test)]
mod tests {
    use crate::sets::{BaselinePropSet, QFormulaSet};

    use super::*;
    use fly::syntax::{Quantifier, Sort};
    use fly::{parser, quant::QuantifierSequence};
    use formats::chc::*;
    use solver::{backends::SolverType, basics::SingleSolver, conf::SolverConf};
    use std::sync::Arc;

    #[test]
    fn test_chc_cex() {
        let sort_a = Sort::uninterpreted("A");
        let sig = Arc::new(Signature {
            sorts: vec!["A".to_string()],
            relations: vec![],
        });

        // Define a CHC system with the single CHC:
        //
        // I(p1, q1) & forall x:A. (p1(x) <-> q2(x)) & (p2(x) <-> q1(x))
        // =>
        // I(p2,q2)
        //
        // where p1,p2,q1,q2 are predicates over an argument of uninterpreted sort A

        let mut chc_sys = ChcSystem::new(
            sig.as_ref().clone(),
            vec![HoPredicateDecl {
                name: "I".to_string(),
                args: vec![
                    FunctionSort(vec![sort_a.clone()], Sort::Bool),
                    FunctionSort(vec![sort_a.clone()], Sort::Bool),
                ],
            }],
        );

        chc_sys.add_chc(
            vec![
                HoVariable {
                    name: "p1".to_string(),
                    sort: FunctionSort(vec![sort_a.clone()], Sort::Bool),
                },
                HoVariable {
                    name: "p2".to_string(),
                    sort: FunctionSort(vec![sort_a.clone()], Sort::Bool),
                },
                HoVariable {
                    name: "q1".to_string(),
                    sort: FunctionSort(vec![sort_a.clone()], Sort::Bool),
                },
                HoVariable {
                    name: "q2".to_string(),
                    sort: FunctionSort(vec![sort_a.clone()], Sort::Bool),
                },
            ],
            vec![
                Component::Predicate("I".to_string(), vec!["p1".to_string(), "q1".to_string()]),
                Component::Formulas(vec![parser::term(
                    "forall x:A. (p1(x) <-> q2(x)) & (p2(x) <-> q1(x))",
                )]),
            ],
            Component::Predicate("I".to_string(), vec!["p2".to_string(), "q2".to_string()]),
        );

        let prefix = QuantifierSequence::new(
            sig.clone(),
            vec![Quantifier::Forall],
            vec![sort_a.clone()],
            &[1],
        );
        let v_name = prefix.all_vars().iter().next().unwrap().clone();
        let atoms = vec![
            Term::app("p", 0, [Term::id(&v_name)]),
            Term::app("q", 0, [Term::id(&v_name)]),
        ];
        let prop_cont =
            PropContext::Nary(Op::Or, Some(2), Box::new(PropContext::Bools(atoms.len())));

        let cont = MultiContext::new(vec![QuantifiedContext {
            prefix,
            atoms,
            prop_cont,
        }]);

        // Get a counterexample for the candidate I(p,q) = forall x:A. p(x),
        // where the atoms considered are p(x) and q(x). The only possible counterexample
        // (given as a quantified type) is { (false, true) }.

        let mut formulas_1 = MultiAttributeSet::<QFormulaSet<BaselinePropSet>>::new(&cont);
        formulas_1.insert(MultiAttribute(
            0,
            PropFormula::Nary(Op::Or, vec![PropFormula::Atom(0, true)]),
        ));
        let pred_sol_1 = PredicateSolution {
            arguments: vec!["p".to_string(), "q".to_string()],
            context: cont.clone(),
            solution: formulas_1,
        };

        let mut sol_1 = ChcSolution {
            solutions: HashMap::new(),
        };
        sol_1.solutions.insert("I".to_string(), pred_sol_1);

        let solver = SingleSolver::new(SolverConf::new(
            SolverType::Z3,
            false,
            &"".to_string(),
            0,
            None,
        ));

        let cex = sol_1.get_positive_cex(&solver, &chc_sys, 1);
        assert_eq!(
            cex,
            Some((
                "I".to_string(),
                MultiObject(
                    0,
                    QuantifiedType(vec![PropModel {
                        bools: vec![false, true]
                    }])
                )
            ))
        );
    }
}

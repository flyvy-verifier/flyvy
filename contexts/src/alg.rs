//! Various algorithmic building blocks for using contexts in logical reasoning.

use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::sync::Arc;

use crate::arith::{ArithExpr, IneqTemplates};
use crate::language::{Atomics, Parameterized};
use crate::sets::MultiId;
use crate::{
    context::{AttributeSet, Context, MultiAttribute, MultiContext, MultiObject},
    logic::*,
    sets::MultiAttributeSet,
};
use fly::quant::QuantifierPrefix;
use fly::syntax::{NumRel, Quantifier};
use fly::{
    syntax::{NOp, RelationDecl, Signature, Sort, Term},
    term::subst::{rename_symbols, NameSubstitution},
};
use formats::chc::{
    ChcSystem, FunctionSort, HoPredicateDecl, SymbolicAssignment, SymbolicPredicate,
};
use itertools::Itertools;
use smtlib::sexp::InterpretedValue;
use solver::basics::{BasicSolver, BasicSolverResp, ModelOption, QueryConf};

fn prop_var(outer_index: usize, inner_index: usize) -> String {
    format!("__prop_{outer_index}_{inner_index}")
}

fn int_var(outer_index: usize, inner_index: usize) -> String {
    format!("__int_{outer_index}_{inner_index}")
}

/// A sequence of propositional variables
#[derive(Clone)]
pub struct PropVars {
    bools: Vec<String>,
    ints: Vec<String>,
}

fn arith_term_with_vars(expr: &ArithExpr<usize>, outer_index: usize) -> Term {
    expr.to_term(|inner_index| Term::Id(int_var(outer_index, *inner_index)))
}

fn prop_model_not_satisfies(f: &PropFormula, outer_index: usize) -> Term {
    match f {
        PropFormula::Bottom => Term::true_(),
        PropFormula::Literal(Literal::Leq(expr, i)) => {
            let e = arith_term_with_vars(expr, outer_index);
            Term::NumRel(NumRel::Gt, Box::new(e), Box::new(Term::Int(*i)))
        }
        PropFormula::Literal(Literal::Bool(inner_index, false)) => {
            Term::Id(prop_var(outer_index, *inner_index))
        }
        PropFormula::Literal(Literal::Bool(inner_index, true)) => {
            Term::not(Term::Id(prop_var(outer_index, *inner_index)))
        }
        PropFormula::Binary(LogicOp::Or, f1, f2) => Term::and([
            prop_model_not_satisfies(f1, outer_index),
            prop_model_not_satisfies(f2, outer_index),
        ]),
        PropFormula::Binary(LogicOp::And, f1, f2) => Term::or([
            prop_model_not_satisfies(f1, outer_index),
            prop_model_not_satisfies(f2, outer_index),
        ]),
        PropFormula::Nary(LogicOp::Or, fs) => Term::and(
            fs.iter()
                .map(|ff| prop_model_not_satisfies(ff, outer_index)),
        ),
        PropFormula::Nary(LogicOp::And, fs) => Term::or(
            fs.iter()
                .map(|ff| prop_model_not_satisfies(ff, outer_index)),
        ),
    }
}

/// A contruction for extracting a [`QuantifiedType`] from an SMT query.
#[derive(Clone)]
pub struct Extractor {
    type_count: usize,
    bool_count: usize,
    int_count: usize,
    term: Term,
    vars: Vec<PropVars>,
}

impl Extractor {
    fn extract(&self, values: &HashMap<Term, InterpretedValue>) -> QuantifiedType {
        QuantifiedType(
            (0..self.type_count)
                .map(|outer_index| PropModel {
                    bools: (0..self.bool_count)
                        .map(|inner_index| {
                            values[&Term::Id(prop_var(outer_index, inner_index))]
                                .bool()
                                .unwrap()
                        })
                        .collect(),
                    ints: (0..self.int_count)
                        .map(|inner_index| {
                            values[&Term::Id(int_var(outer_index, inner_index))]
                                .int()
                                .unwrap()
                        })
                        .collect(),
                })
                .collect(),
        )
    }

    fn to_evaluate(&self) -> Vec<Term> {
        self.vars
            .iter()
            .flat_map(|v| v.bools.iter().chain(&v.ints))
            .map(|name| Term::id(name))
            .collect()
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
            for v in &vs.ints {
                extended_sig.relations.push(RelationDecl {
                    mutable: false,
                    name: v.clone(),
                    args: vec![],
                    sort: Sort::Int,
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
            PropFormula::Literal(Literal::Bool(i, b)) => {
                if *b {
                    self.bool_terms[*i].clone()
                } else {
                    Term::not(&self.bool_terms[*i])
                }
            }
            PropFormula::Literal(Literal::Leq(expr, i)) => {
                let expr_term = self.to_term_int(expr);
                Term::NumRel(NumRel::Leq, Box::new(expr_term), Box::new(Term::Int(*i)))
            }
            PropFormula::Binary(LogicOp::Or, f1, f2) => {
                Term::NAryOp(NOp::Or, vec![self.to_term_prop(f1), self.to_term_prop(f2)])
            }
            PropFormula::Binary(LogicOp::And, f1, f2) => {
                Term::NAryOp(NOp::And, vec![self.to_term_prop(f1), self.to_term_prop(f2)])
            }
            PropFormula::Nary(LogicOp::Or, fs) => {
                Term::or(fs.iter().map(|ff| self.to_term_prop(ff)))
            }
            PropFormula::Nary(LogicOp::And, fs) => {
                Term::and(fs.iter().map(|ff| self.to_term_prop(ff)))
            }
        }
    }

    fn to_term_int(&self, expr: &ArithExpr<usize>) -> Term {
        Term::int_add(
            [Term::Int(expr.constant)]
                .into_iter()
                .chain(expr.summands.iter().map(|(c, p)| {
                    Term::int_mul(
                        [Term::Int(*c)]
                            .into_iter()
                            .chain(p.iter().map(|index| self.int_terms[*index].clone())),
                    )
                })),
        )
    }

    /// Create an extractor for extracting a [`QuantifiedType`] of the given size.
    /// The substitution is used to rename functions and relations in the atoms of the [`QuantifiedContext`]
    /// to those used by the extractor.
    pub fn extractor(&self, size: usize, substitution: &NameSubstitution) -> Extractor {
        assert!(size >= 1);

        let vars = (0..size)
            .map(|i| PropVars {
                bools: (0..self.bool_terms.len()).map(|j| prop_var(i, j)).collect(),
                ints: (0..self.int_terms.len()).map(|j| int_var(i, j)).collect(),
            })
            .collect_vec();

        let cubes =
            (0..size)
                .map(|i| {
                    Term::and(
                        self.bool_terms
                            .iter()
                            .enumerate()
                            .map(|(j, t): (usize, &Term)| Term::iff(Term::id(&vars[i].bools[j]), t))
                            .chain(self.int_terms.iter().enumerate().map(
                                |(j, t): (usize, &Term)| {
                                    Term::equals(Term::id(&vars[i].ints[j]), t)
                                },
                            )),
                    )
                })
                .collect_vec();

        let t = Term::not(self.prefix.quantify(Term::not(Term::or(cubes))));

        Extractor {
            type_count: size,
            bool_count: self.bool_terms.len(),
            int_count: self.int_terms.len(),
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
    partial: PartialSolution<MultiId<S::AttributeId>>,
}

struct PartialSolution<K: Hash + Eq + Clone> {
    /// The identifiers of formulas left to check, for each CHC (as indexed by the [`ChcSystem`])
    to_check: Vec<HashSet<K>>,
    /// For each CHC, a mapping from a formula identifier to an UNSAT-core consisting of elements `(predicate_name, formula_identifier)`
    formula_to_core: Vec<HashMap<K, HashSet<(String, K)>>>,
    /// A mapping from `(predicate_name, formula_identifier)` to formulas in the heads of CHCs that have it in their UNSAT-core,
    /// given as `(chc_index, formula_identifier)`
    in_core_of: HashMap<(String, K), HashSet<(usize, K)>>,
}

impl<K: Hash + Eq + Clone + Debug> PartialSolution<K> {
    fn checks_left(&self) -> usize {
        self.to_check.iter().map(|s| s.len()).sum()
    }

    fn add_core(&mut self, id: (usize, K), core: HashSet<(String, K)>) {
        for e in &core {
            self.in_core_of
                .entry(e.clone())
                .or_default()
                .insert(id.clone());
        }
        assert!(self.formula_to_core[id.0].insert(id.1, core).is_none());
    }

    fn remove_core(&mut self, formula: &(usize, K)) -> HashSet<(String, K)> {
        let core = self.formula_to_core[formula.0].remove(&formula.1).unwrap();
        for in_core in &core {
            let s = self.in_core_of.get_mut(in_core).unwrap();
            assert!(s.remove(formula));
            if s.is_empty() {
                self.in_core_of.remove(in_core);
            }
        }

        core
    }

    /// Remove all cores using weakened formulas, and add the formulas using them to future checks.
    fn remove_cores(&mut self, predicate_name: &str, updates: &HashMap<K, Vec<K>>) {
        for k in updates.keys() {
            let participant = (predicate_name.to_owned(), k.clone());
            if let Some(using) = self.in_core_of.get(&participant).cloned() {
                for formula in using {
                    self.remove_core(&formula);
                    self.to_check[formula.0].insert(formula.1);
                }
            }
        }
    }

    fn update_weakened(
        &mut self,
        predicate_name: &String,
        updates: &HashMap<K, Vec<K>>,
        chc_sys: &ChcSystem,
    ) {
        for (i, chc) in chc_sys.chcs.iter().enumerate() {
            if chc.head.has_predicate_name(predicate_name) {
                for (k, weakenings) in updates {
                    // Remove weakened formulas from checks and add weakenings in their place.
                    // If a weakened formula is already proven, its weakenings don't need to be added.
                    if self.to_check[i].remove(k) {
                        for wk in weakenings {
                            assert!(self.to_check[i].insert(wk.clone()));
                        }
                    } else {
                        // Update the cores for the weakenings.
                        let core = self.remove_core(&(i, k.clone()));
                        for wk in weakenings {
                            self.add_core((i, wk.clone()), core.clone());
                        }
                    }
                }
            }
        }
    }
}

impl<S> ChcSolution<S>
where
    S: AttributeSet<Object = QuantifiedType, Attribute = PropFormula, Cont = QuantifiedContext>,
{
    fn new(cfg: Vec<PredicateConfig>, chc_sys: &ChcSystem) -> Self {
        let head_predicates = chc_sys
            .chcs
            .iter()
            .map(|chc| chc.head.predicate())
            .collect_vec();
        let solutions: HashMap<String, PredicateSolution<S>> = cfg
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
        let partial = PartialSolution {
            to_check: head_predicates
                .iter()
                .map(|pred| match pred {
                    Some((name, _)) => solutions[*name].solution.iter().collect(),
                    None => HashSet::new(),
                })
                .collect(),
            formula_to_core: vec![HashMap::new(); head_predicates.len()],
            in_core_of: HashMap::new(),
        };

        Self { solutions, partial }
    }

    /// Get the symbolic assignment given by this solution.
    pub fn get_symbolic_assignment(&self) -> SymbolicAssignment<(String, MultiId<S::AttributeId>)> {
        self.solutions
            .iter()
            .map(|(name, p)| {
                (
                    name.clone(),
                    SymbolicPredicate {
                        args: p.arguments.clone(),
                        formulas: p
                            .solution
                            .iter()
                            .map(|id| {
                                let t = p.context.to_term(&p.solution.get(&id));
                                ((name.clone(), id), t)
                            })
                            .collect(),
                    },
                )
            })
            .collect()
    }

    fn get_positive_cex<B: BasicSolver>(
        &mut self,
        solver: &B,
        chc_sys: &ChcSystem,
        size: usize,
    ) -> Option<(String, MultiObject<QuantifiedType>)> {
        let assignment = self.get_symbolic_assignment();

        'chc_loop: for chc_index in 0..self.partial.to_check.len() {
            if self.partial.to_check[chc_index].is_empty() {
                continue 'chc_loop;
            }

            let chc = &chc_sys.chcs[chc_index];
            let head_predicate = chc.head.predicate().unwrap();

            println!("Checking CHC #{chc_index} with head {}", head_predicate.0);

            // Check whether one of the predicates in the body is equivalent to false (which implies a trivial implication)
            for comp in &chc.body {
                if let Some((comp_name, _)) = comp.predicate() {
                    if let Some(core) = self.solutions[comp_name].solution.get_false_subset() {
                        let named_core: HashSet<_> =
                            core.into_iter().map(|e| (comp_name.clone(), e)).collect();
                        let ids_to_check = std::mem::take(&mut self.partial.to_check[chc_index]);
                        for id in ids_to_check {
                            self.partial.add_core((chc_index, id), named_core.clone());
                        }
                        println!("Check trivially holds");
                        continue 'chc_loop;
                    }
                }
            }

            // The hypotheses of the CHC
            let mut hyp = vec![];
            let mut assume_keys = vec![];
            let mut assumptions = HashMap::new();
            for (k, t) in chc.instantiate_body(&assignment).into_iter() {
                match k {
                    Some(key) => {
                        assumptions.insert(assume_keys.len(), (t, true));
                        assume_keys.push(key);
                    }
                    None => hyp.push(t),
                }
            }

            // The solution for the predicate in the head
            let head_sol = &self.solutions[head_predicate.0];
            // The multiple contexts for formulas in the head
            let head_contexts = &head_sol.context.contexts;
            // The multiple sets of formulas of the head (matching the multiple contexts)
            let head_sets = &head_sol.solution.sets;
            // The substitution from the solution's arguments to the head's arguments
            assert_eq!(head_sol.arguments.len(), head_predicate.1.len());
            let head_subst: NameSubstitution = self.solutions[head_predicate.0]
                .arguments
                .iter()
                .zip(head_predicate.1)
                .map(|(old_v, new_v)| ((old_v.clone(), 0), new_v.clone()))
                .collect();

            assert_eq!(head_contexts.len(), head_sets.len());

            let mut extractors: Vec<Option<Extractor>> = vec![None; head_contexts.len()];
            let ids_to_check = self.partial.to_check[chc_index].clone();
            for id in ids_to_check {
                // A formula to check shouldn't already have a core
                assert!(
                    !self.partial.formula_to_core[chc_index].contains_key(&id),
                    "formula to check already had UNSAT-core"
                );

                if extractors[id.0].is_none() {
                    extractors[id.0] = Some(head_contexts[id.0].extractor(size, &head_subst));
                }
                let extractor = extractors[id.0].as_ref().unwrap();
                let extended_sig = extractor.extend_signature(&chc.signature);
                let query_conf = QueryConf {
                    sig: &extended_sig,
                    n_states: 1,
                    cancelers: None,
                    model_option: ModelOption::None,
                    evaluate: extractor.to_evaluate(),
                    save_tee: false,
                };

                let formula = head_sets[id.0].get(&id.1);
                println!(
                    "Querying {} ({} remaining): {}",
                    head_predicate.0,
                    self.partial.checks_left(),
                    head_contexts[id.0].to_term(&formula)
                );
                let mut assertions = hyp.clone();
                assertions.push(extractor.term.clone());
                assertions.push(extractor.not_satisfies(&formula));
                let resp = solver.check_sat(&query_conf, &assertions, &assumptions);

                match resp {
                    Ok(BasicSolverResp::Sat(_, vals)) => {
                        return Some((
                            head_predicate.0.clone(),
                            MultiObject(id.0, extractor.extract(&vals)),
                        ))
                    }
                    Ok(BasicSolverResp::Unsat(core)) => {
                        let named_core = core.iter().map(|i| assume_keys[*i].clone()).collect();
                        self.partial.to_check[chc_index].remove(&id);
                        self.partial.add_core((chc_index, id), named_core);
                    }
                    _ => panic!("solver error {resp:?}"),
                }
            }
        }

        None
    }
}

impl<S> Display for ChcSolution<S>
where
    S: AttributeSet<Object = QuantifiedType, Attribute = PropFormula, Cont = QuantifiedContext>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut lines: Vec<String> = vec![];
        for (k, v) in &self.solutions {
            let mut new_lines = vec![];
            let args = v.arguments.iter().join(", ");
            new_lines.push(format!("predicate {k}({args}):"));
            for ref id in v.solution.iter() {
                let t = v.context.to_term(&v.solution.get(id));
                new_lines.push(format!("    {t}"));
            }
            lines.push(new_lines.iter().join("\n"));
        }

        write!(f, "{}", lines.iter().join("\n"))
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

impl PredicateConfig {
    /// Create standard argument name for an argument of a predicate at the given position.
    pub fn arg_name(i: usize) -> String {
        format!("__pvar_{i}")
    }

    /// Create standard variable name for a quantified variable at a given position.
    pub fn quant_name(i: usize) -> String {
        format!("__qvar_{i}")
    }

    /// Create a default configuration for the given predicate in the given CHC system.
    pub fn default(decl: &HoPredicateDecl, literals: &Parameterized<Atomics>) -> Self {
        let arguments = (0..decl.args.len()).map(Self::arg_name).collect_vec();

        let bool_sort = FunctionSort(vec![], Sort::Bool);
        let bool_terms = decl
            .args
            .iter()
            .zip(&arguments)
            .filter(|(sort, _)| *sort == &bool_sort)
            .map(|(_, name)| Term::id(name))
            .collect_vec();

        let int_terms = literals.content.ints.clone();

        let mut int_templates = IneqTemplates::new(false);
        for literal in &literals.content.literals {
            int_templates.add_from_literal(literal);
        }
        println!("Integer templates ({}):", decl.name);
        for (e, t) in &int_templates.templates {
            println!("{} <= {t}", e.to_term(|i| int_terms[*i].clone()));
        }
        println!();

        let literal_context = PropContext::literals((0..bool_terms.len()).collect(), int_templates);
        let prop_cont = PropContext::Nary(LogicOp::Or, Some(3), Box::new(literal_context));

        let prefix = QuantifierPrefix {
            quantifiers: vec![Quantifier::Forall],
            sorts: Arc::new(vec![Sort::Int]),
            names: Arc::new(vec![literals.univ_ints.clone()]),
        };

        PredicateConfig {
            name: decl.name.clone(),
            arguments,
            context: MultiContext {
                contexts: vec![QuantifiedContext {
                    prefix,
                    bool_terms,
                    int_terms,
                    prop_cont,
                }],
            },
        }
    }
}

/// Find the least-fixpoint solution of a [`ChcSystem`] with the given predicate configurations.
pub fn find_lfp<B, S>(solver: &B, chc_sys: &ChcSystem, cfg: Vec<PredicateConfig>) -> ChcSolution<S>
where
    B: BasicSolver,
    S: AttributeSet<Object = QuantifiedType, Attribute = PropFormula, Cont = QuantifiedContext>,
{
    let mut chc_sol = ChcSolution::new(cfg, chc_sys);

    // TODO: handle increasing sizes

    while let Some((name, cex)) = chc_sol.get_positive_cex(solver, chc_sys, 1) {
        println!("Found CEX: {cex:?}");
        let pred_sol = chc_sol.solutions.get_mut(&name).unwrap();
        let updates = pred_sol.solution.weaken(&pred_sol.context, &cex);
        chc_sol.partial.remove_cores(&name, &updates);
        chc_sol.partial.update_weakened(&name, &updates, chc_sys);
    }

    // TODO: verify solution (also w.r.t queries)

    chc_sol
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sets::{BaselinePropSet, QFormulaSet};
    use fly::syntax::{Quantifier, Sort};
    use fly::term::subst::Substitutable;
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
                Component::Predicate(
                    "I".to_string(),
                    vec![Substitutable::name("p1"), Substitutable::name("q1")],
                ),
                Component::Formulas(vec![parser::term(
                    "forall x:A. (p1(x) <-> q2(x)) & (p2(x) <-> q1(x))",
                )]),
            ],
            Component::Predicate(
                "I".to_string(),
                vec![Substitutable::name("p2"), Substitutable::name("q2")],
            ),
        );

        let prefix = QuantifierSequence::new(
            sig.clone(),
            vec![Quantifier::Forall],
            vec![sort_a.clone()],
            &[1],
        );
        let v_name = prefix.all_vars().iter().next().unwrap().clone();
        let bool_terms = vec![
            Term::app("p", 0, [Term::id(&v_name)]),
            Term::app("q", 0, [Term::id(&v_name)]),
        ];
        let prop_cont = PropContext::Nary(
            LogicOp::Or,
            Some(2),
            Box::new(PropContext::literals(
                (0..bool_terms.len()).collect(),
                IneqTemplates::new(false),
            )),
        );

        let cont = MultiContext::new(vec![QuantifiedContext {
            prefix,
            bool_terms,
            int_terms: vec![],
            prop_cont,
        }]);

        // Get a counterexample for the candidate I(p,q) = forall x:A. p(x),
        // where the atoms considered are p(x) and q(x). The only possible counterexample
        // (given as a quantified type) is { (false, true) }.

        let mut formulas_1 = MultiAttributeSet::<QFormulaSet<BaselinePropSet>>::new(&cont);
        formulas_1.insert(MultiAttribute(
            0,
            PropFormula::Nary(LogicOp::Or, vec![PropFormula::bool_literal(0, true)]),
        ));
        let pred_sol_1 = PredicateSolution {
            arguments: vec!["p".to_string(), "q".to_string()],
            context: cont.clone(),
            solution: formulas_1,
        };

        let mut sol_1 = ChcSolution {
            solutions: HashMap::new(),
            partial: PartialSolution {
                to_check: vec![pred_sol_1.solution.iter().collect()],
                formula_to_core: vec![HashMap::new()],
                in_core_of: HashMap::new(),
            },
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
                        bools: vec![false, true],
                        ints: vec![],
                    }])
                )
            ))
        );
        assert_eq!(sol_1.partial.to_check.len(), 1);
    }
}

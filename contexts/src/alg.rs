//! Various algorithmic building blocks for using contexts in logical reasoning.

use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::Arc;

use crate::sets::MultiId;
use crate::{
    context::{AttributeSet, Context, MultiAttribute, MultiContext, MultiObject},
    logic::*,
    sets::MultiAttributeSet,
};
use fly::quant::QuantifierPrefix;
use fly::syntax::NumRel;
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

fn arith_term_with_vars(expr: &ArithExpr, outer_index: usize) -> Term {
    match expr {
        ArithExpr::Int(i) => Term::Int(*i),
        ArithExpr::Expr(inner_index) => Term::Id(int_var(outer_index, *inner_index)),
        ArithExpr::Binary(op, x, y) => Term::NumOp(
            *op,
            Box::new(arith_term_with_vars(x, outer_index)),
            Box::new(arith_term_with_vars(y, outer_index)),
        ),
    }
}

fn prop_model_not_satisfies(f: &PropFormula, outer_index: usize) -> Term {
    match f {
        PropFormula::Bottom => Term::true_(),
        PropFormula::Literal(Literal::IntBounds { expr, lower, upper }) => {
            let e = arith_term_with_vars(expr, outer_index);
            let mut ts = vec![];
            if let Some(l) = lower {
                ts.push(Term::NumRel(
                    NumRel::Gt,
                    Box::new(Term::Int(*l)),
                    Box::new(e.clone()),
                ));
            }
            if let Some(u) = upper {
                ts.push(Term::NumRel(
                    NumRel::Lt,
                    Box::new(Term::Int(*u)),
                    Box::new(e.clone()),
                ));
            }
            return Term::or(ts);
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
            PropFormula::Literal(Literal::IntBounds { expr, lower, upper }) => {
                let mut ts = vec![];
                let expr_term = self.to_term_int(expr);
                // lower bound <= expr
                if let Some(l) = lower {
                    ts.push(Term::NumRel(
                        NumRel::Leq,
                        Box::new(Term::Int(*l)),
                        Box::new(expr_term.clone()),
                    ));
                }
                // upper bound >= expr
                if let Some(u) = upper {
                    ts.push(Term::NumRel(
                        NumRel::Geq,
                        Box::new(Term::Int(*u)),
                        Box::new(expr_term.clone()),
                    ));
                }
                Term::and(ts)
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

    fn to_term_int(&self, expr: &ArithExpr) -> Term {
        match expr {
            ArithExpr::Int(i) => Term::Int(*i),
            ArithExpr::Expr(index) => self.int_terms[*index].clone(),
            ArithExpr::Binary(op, x, y) => Term::NumOp(
                *op,
                Box::new(self.to_term_int(x)),
                Box::new(self.to_term_int(y)),
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

    fn post_weaken_update(
        &mut self,
        predicate_name: &String,
        updates: &HashMap<K, Vec<K>>,
        chc_sys: &ChcSystem,
    ) {
        // Remove all cores using the weakened predicate.
        for k in updates.keys() {
            let participant = (predicate_name.clone(), k.clone());
            if let Some(using) = self.in_core_of.remove(&participant) {
                for u in using {
                    self.formula_to_core[u.0].remove(&u.1);
                }
            }
        }

        for (i, chc) in chc_sys.chcs.iter().enumerate() {
            if chc.head.has_predicate_name(predicate_name) {
                for (k, weakenings) in updates {
                    // Remove weakened formulas from checks and add weakenings in their place.
                    // If a weakened formula is already proven, its weakenings don't need to be added.
                    if self.to_check[i].remove(k) {
                        for wk in weakenings {
                            assert!(self.to_check[i].insert(wk.clone()));
                        }
                    }

                    // Update the cores for the weakenings.
                    if let Some(core) = self.formula_to_core[i].remove(k) {
                        for c in &core {
                            assert!(self.in_core_of.get_mut(c).unwrap().remove(&(i, k.clone())));
                        }
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

    fn get_symbolic_assignment(&self) -> SymbolicAssignment<(String, MultiId<S::AttributeId>)> {
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

            log::info!("Checking CHC #{chc_index} with head {}", head_predicate.0);

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
                        log::info!("Check trivially holds");
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
                log::info!(
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

impl<S> ToString for ChcSolution<S>
where
    S: AttributeSet<Object = QuantifiedType, Attribute = PropFormula, Cont = QuantifiedContext>,
{
    fn to_string(&self) -> String {
        let mut lines: Vec<String> = vec![];
        for (k, v) in &self.solutions {
            let args = v.arguments.iter().join(", ");
            lines.push(format!("predicate {k}({args}):"));
            for ref id in v.solution.iter() {
                let t = v.context.to_term(&v.solution.get(id));
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

impl PredicateConfig {
    /// Create a default configuration for the given predicate in the given CHC system.
    pub fn default(decl: &HoPredicateDecl, chc_sys: &ChcSystem) -> Self {
        let arguments = (1..=decl.args.len())
            .map(|i| format!("__pvar_{i}"))
            .collect_vec();

        let bool_sort = FunctionSort(vec![], Sort::Bool);
        let bool_terms = decl
            .args
            .iter()
            .zip(&arguments)
            .filter(|(sort, _)| *sort == &bool_sort)
            .map(|(_, name)| Term::id(name))
            .collect_vec();

        let int_sort = FunctionSort(vec![], Sort::Int);
        let int_terms = decl
            .args
            .iter()
            .zip(&arguments)
            .filter(|(sort, _)| *sort == &int_sort)
            .map(|(_, name)| Term::id(name))
            .collect_vec();

        // Create integer bounds for each integer argument.
        let max_int = chc_sys.max_int().map(|i| i + 1).or(Some(1));
        let bounds = IntBoundTemplate {
            with_upper: true,
            with_lower: true,
            with_both: false,
            upper_limit: max_int,
            lower_limit: max_int.map(|i| -i),
        };
        let int_exprs: HashSet<_> = (0..int_terms.len()).map(ArithExpr::Expr).collect();

        log::info!("Integer expressions used ({}):", int_exprs.len());
        let int_templates = int_exprs
            .into_iter()
            .map(|e| {
                log::info!("    {e}");
                (e, bounds.clone())
            })
            .collect();

        let literal_context = PropContext::literals((0..bool_terms.len()).collect(), int_templates);

        let prop_cont = PropContext::Nary(LogicOp::Or, Some(2), Box::new(literal_context));

        PredicateConfig {
            name: decl.name.clone(),
            arguments,
            context: MultiContext {
                contexts: vec![QuantifiedContext {
                    prefix: QuantifierPrefix {
                        quantifiers: vec![],
                        sorts: Arc::new(vec![]),
                        names: Arc::new(vec![]),
                    },
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
        log::info!("Found CEX: {cex:?}");
        let pred_sol = chc_sol.solutions.get_mut(&name).unwrap();
        let updates = pred_sol.solution.weaken(&pred_sol.context, &cex);
        chc_sol.partial.post_weaken_update(&name, &updates, chc_sys);
    }

    // TODO: verify solution (also w.r.t queries)

    chc_sol
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sets::{BaselinePropSet, QFormulaSet};
    use fly::quant::QuantifierPrefix;
    use fly::syntax::{NumOp, Quantifier, Sort};
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
                HashMap::new(),
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

    #[test]
    fn test_mccarthy() {
        let solver = SingleSolver::new(SolverConf::new(
            SolverType::Z3,
            false,
            &"".to_string(),
            0,
            None,
        ));

        let sig = Signature {
            sorts: vec![],
            relations: vec![],
        };

        let mut chc_sys = ChcSystem::new(
            sig.clone(),
            vec![HoPredicateDecl {
                name: "MC".to_string(),
                args: vec![FunctionSort(vec![Sort::Int, Sort::Int], Sort::Bool)],
            }],
        );

        chc_sys.add_chc(
            vec![
                HoVariable {
                    name: "n".to_string(),
                    sort: FunctionSort(vec![], Sort::Int),
                },
                HoVariable {
                    name: "r".to_string(),
                    sort: FunctionSort(vec![], Sort::Int),
                },
            ],
            vec![Component::Formulas(vec![parser::term(
                "(n > 100) & (r = n - 10)",
            )])],
            Component::Predicate(
                "MC".to_string(),
                vec![Substitutable::name("n"), Substitutable::name("r")],
            ),
        );

        chc_sys.add_chc(
            vec![
                HoVariable {
                    name: "n".to_string(),
                    sort: FunctionSort(vec![], Sort::Int),
                },
                HoVariable {
                    name: "r1".to_string(),
                    sort: FunctionSort(vec![], Sort::Int),
                },
                HoVariable {
                    name: "r2".to_string(),
                    sort: FunctionSort(vec![], Sort::Int),
                },
            ],
            vec![
                Component::Formulas(vec![parser::term("!(n > 100)")]),
                Component::Predicate(
                    "MC".to_string(),
                    vec![
                        Substitutable::Term(parser::term("n + 11")),
                        Substitutable::name("r1"),
                    ],
                ),
                Component::Predicate(
                    "MC".to_string(),
                    vec![Substitutable::name("r1"), Substitutable::name("r2")],
                ),
            ],
            Component::Predicate(
                "MC".to_string(),
                vec![Substitutable::name("n"), Substitutable::name("r2")],
            ),
        );

        let prefix = QuantifierPrefix::new(Arc::new(sig.clone()), vec![], vec![], &[]);

        let prop_cont = PropContext::Binary(
            LogicOp::Or,
            Box::new(PropContext::literals(
                vec![],
                [(
                    ArithExpr::Expr(1),
                    IntBoundTemplate {
                        with_upper: true,
                        with_lower: true,
                        with_both: true,
                        upper_limit: Some(0),
                        lower_limit: Some(200),
                    },
                )]
                .into_iter()
                .collect(),
            )),
            Box::new(PropContext::Binary(
                LogicOp::And,
                Box::new(PropContext::literals(
                    vec![],
                    [(
                        ArithExpr::Expr(0),
                        IntBoundTemplate {
                            with_upper: true,
                            with_lower: true,
                            with_both: true,
                            upper_limit: Some(0),
                            lower_limit: Some(200),
                        },
                    )]
                    .into_iter()
                    .collect(),
                )),
                Box::new(PropContext::literals(
                    vec![],
                    [((
                        ArithExpr::Binary(
                            NumOp::Sub,
                            Box::new(ArithExpr::Expr(0)),
                            Box::new(ArithExpr::Expr(1)),
                        ),
                        IntBoundTemplate {
                            with_upper: true,
                            with_lower: true,
                            with_both: true,
                            upper_limit: Some(0),
                            lower_limit: Some(200),
                        },
                    ))]
                    .into_iter()
                    .collect(),
                )),
            )),
        );

        let context = MultiContext::new(vec![QuantifiedContext {
            prefix,
            bool_terms: vec![],
            int_terms: vec![Term::id("n"), Term::id("r")],
            prop_cont,
        }]);

        let cfg = vec![PredicateConfig {
            name: "MC".to_string(),
            arguments: vec!["n".to_string(), "r".to_string()],
            context,
        }];

        let res = find_lfp::<_, QFormulaSet<BaselinePropSet>>(&solver, &chc_sys, cfg);
        // Verify that (91 <= r <= 91) | ((102 <= n) | (10 <= n - r <= 10)) is in the solution
        assert!(
            res.solutions[&"MC".to_string()].solution.sets[0].contains(&PropFormula::Binary(
                LogicOp::Or,
                Box::new(PropFormula::Literal(Literal::IntBounds {
                    expr: ArithExpr::Expr(1),
                    lower: Some(91),
                    upper: Some(91),
                })),
                Box::new(PropFormula::Binary(
                    LogicOp::And,
                    Box::new(PropFormula::Literal(Literal::IntBounds {
                        expr: ArithExpr::Expr(0),
                        lower: Some(102),
                        upper: None,
                    })),
                    Box::new(PropFormula::Literal(Literal::IntBounds {
                        expr: ArithExpr::Binary(
                            NumOp::Sub,
                            Box::new(ArithExpr::Expr(0)),
                            Box::new(ArithExpr::Expr(1)),
                        ),
                        lower: Some(10),
                        upper: Some(10),
                    })),
                )),
            ))
        );
    }
}

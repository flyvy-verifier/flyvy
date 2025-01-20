//! Various algorithmic building blocks for using contexts in logical reasoning.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::sync::Arc;
use std::time::Instant;

use crate::arith::{ArithExpr, IneqTemplates};
use crate::sets::MultiId;
use crate::{
    context::{AttributeSet, Context, MultiAttribute, MultiContext, MultiObject},
    logic::*,
    sets::MultiAttributeSet,
};
use fly::quant::QuantifierPrefix;
use fly::semantics::Evaluable;
use fly::syntax::{NumRel, Quantifier};
use fly::{
    syntax::{NOp, RelationDecl, Signature, Sort, Term},
    term::subst::{rename_symbols, NameSubstitution},
};
use formats::basics::{CexResult, OrderedTerms, SmtTactic};
use formats::chc::{ChcSystem, HoPredicateDecl, SymbolicAssignment, SymbolicPredicate};
use itertools::Itertools;
use smtlib::sexp::InterpretedValue;
use solver::basics::{
    BasicCanceler, BasicSolver, BasicSolverResp, ModelOption, MultiCanceler, QueryConf, RespModel,
};
use solver::parallel::{parallelism, ParallelWorker, Tasks};

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
                let expr_term = expr.to_term(|i| self.int_terms[*i].clone());
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

struct OrderedFormulas<K>
where
    K: Ord + Hash + Eq + Clone + Send + Sync,
{
    next_id: usize,
    formulas: BTreeMap<(usize, usize, K), Term>,
}

impl<K> OrderedTerms for &OrderedFormulas<K>
where
    K: Ord + Hash + Eq + Clone + Send + Sync,
{
    type Key = (usize, usize, K);
    type Eval = RespModel;

    fn permanent(&self) -> Vec<(&Self::Key, &Term)> {
        vec![]
    }

    fn first_unsat(self, model: &Self::Eval) -> Option<(Self::Key, Term)> {
        self.formulas
            .iter()
            .find(|(_, t)| !model.evaluate(t))
            .map(|(k, t)| (k.clone(), t.clone()))
    }

    fn all_terms(self) -> BTreeMap<Self::Key, Term> {
        self.formulas.clone()
    }
}

impl<K> OrderedFormulas<K>
where
    K: Ord + Hash + Eq + Clone + Send + Sync,
{
    fn new() -> Self {
        Self {
            next_id: 0,
            formulas: BTreeMap::new(),
        }
    }

    fn add(&mut self, key: K, term: Term) {
        let size = term.size();
        self.formulas.insert((size, self.next_id, key), term);
        self.next_id += 1;
    }
}

struct Cores<B, C>
where
    B: Hash + Eq + Clone,
    C: Hash + Eq + Clone,
{
    blocked_to_blocking: HashMap<B, HashSet<C>>,
    blocking_to_blocked: HashMap<C, HashSet<B>>,
}

impl<B, C> Cores<B, C>
where
    B: Hash + Eq + Clone,
    C: Hash + Eq + Clone,
{
    fn new() -> Self {
        Self {
            blocked_to_blocking: HashMap::new(),
            blocking_to_blocked: HashMap::new(),
        }
    }

    fn is_blocked(&self, b: &B) -> bool {
        self.blocked_to_blocking.contains_key(b)
    }

    fn block(&mut self, b: B, core: HashSet<C>) {
        for c in &core {
            let blocked = self.blocking_to_blocked.entry(c.clone()).or_default();
            blocked.insert(b.clone());
        }
        assert!(self.blocked_to_blocking.insert(b, core).is_none());
    }

    fn remove_blocked(&mut self, b: &B) {
        if let Some(blocking) = self.blocked_to_blocking.remove(b) {
            for c in &blocking {
                let blocked = self.blocking_to_blocked.get_mut(c).unwrap();
                assert!(blocked.remove(b));
                if blocked.is_empty() {
                    self.blocking_to_blocked.remove(c);
                }
            }
        }
    }

    fn remove_blocking(&mut self, c: &C) {
        if let Some(blocked) = self.blocking_to_blocked.get(c).cloned() {
            for b in &blocked {
                self.remove_blocked(b);
            }
            assert!(!self.blocking_to_blocked.contains_key(c));
        }
    }

    fn weaken(&mut self, b: &B, weakenings: &[B]) {
        if let Some(core) = self.blocked_to_blocking.get(b).cloned() {
            for w in weakenings {
                self.block(w.clone(), core.clone());
            }
        }
    }
}

struct PredicateSolution<S>
where
    S: AttributeSet<Object = QuantifiedType, Attribute = PropFormula, Cont = QuantifiedContext>,
{
    arguments: Vec<String>,
    context: MultiContext<QuantifiedContext>,
    solution: MultiAttributeSet<S>,
    signature: Signature,
    implication_cores: Cores<MultiId<S::AttributeId>, MultiId<S::AttributeId>>,
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
    /// Cores of formulas in CHC heads. A blocked formula is represented by `(chc_index, formula_identifier)`,
    /// and formulas in cores are represented by `(predicate_name, formula_identifier)`.
    formula_cores: Cores<(usize, K), (String, K)>,
}

impl<S> PredicateSolution<S>
where
    S: AttributeSet<Object = QuantifiedType, Attribute = PropFormula, Cont = QuantifiedContext>,
{
    pub fn new(
        chc_sys: &ChcSystem,
        p: &PredicateConfig,
        solution: Option<MultiAttributeSet<S>>,
    ) -> Self {
        let solution = solution
            .unwrap_or_else(|| MultiAttributeSet::<S>::from_(&p.context, p.context.bottom()));
        let decl = chc_sys
            .predicates
            .iter()
            .find(|d| d.name == p.name)
            .unwrap();
        let mut signature = chc_sys.signature.clone();

        assert_eq!(p.arguments.len(), decl.args.len());
        for (name, sort) in p.arguments.iter().zip(&decl.args) {
            signature.relations.push(RelationDecl {
                mutable: false,
                name: name.clone(),
                args: sort.0.clone(),
                sort: sort.1.clone(),
            });
        }

        Self {
            arguments: p.arguments.clone(),
            context: p.context.clone(),
            signature,
            solution,
            implication_cores: Cores::new(),
        }
    }

    pub fn minimize_by_implication<B: BasicSolver>(&mut self, solver: &B) {
        let query_conf = QueryConf {
            sig: &self.signature,
            n_states: 1,
            cancelers: None,
            model_option: ModelOption::None,
            evaluate: vec![],
            save_tee: false,
        };
        // Used for collecting previous formulas IDs.
        let mut prev_ids: Vec<MultiId<S::AttributeId>> = vec![];
        let mut assumptions = HashMap::new();
        for (i, id) in self.solution.iter().sorted().enumerate() {
            let formula_term = self.context.to_term(&self.solution.get(&id));
            if !self.implication_cores.is_blocked(&id) {
                let res = solver.check_sat(&query_conf, &[Term::not(&formula_term)], &assumptions);
                match res {
                    Ok(BasicSolverResp::Unsat(core)) => {
                        self.implication_cores.block(
                            id.clone(),
                            core.iter().map(|i| prev_ids[*i].clone()).collect(),
                        );
                    }
                    Ok(BasicSolverResp::Sat(_, _)) => {
                        assumptions.insert(i, (formula_term, true));
                    }
                    _ => panic!("solver error {res:?}"),
                }
            }
            prev_ids.push(id);
        }
    }

    pub fn update_weakened(
        &mut self,
        updates: &HashMap<MultiId<S::AttributeId>, Vec<MultiId<S::AttributeId>>>,
    ) {
        for (id, weakenings) in updates {
            self.implication_cores.weaken(id, weakenings);
            self.implication_cores.remove_blocked(id);
            self.implication_cores.remove_blocking(id);
        }
    }

    pub fn minimal_set(&self) -> impl Iterator<Item = MultiId<S::AttributeId>> + '_ {
        self.solution
            .iter()
            .filter(|id| !self.implication_cores.is_blocked(id))
    }
}

impl<K: Hash + Eq + Clone + Debug> PartialSolution<K> {
    fn add_core(&mut self, id: (usize, K), core: HashSet<(String, K)>) {
        self.formula_cores.block(id, core);
    }

    fn update_weakened(
        &mut self,
        predicate_name: &String,
        updates: &HashMap<K, Vec<K>>,
        chc_sys: &ChcSystem,
    ) {
        for (i, chc) in chc_sys.chcs.iter().enumerate() {
            if chc.head.has_predicate_name(predicate_name) {
                for (k, wk) in updates {
                    let formula = (i, k.clone());
                    let weakenings = wk.iter().map(|w| (i, w.clone())).collect_vec();
                    self.formula_cores.weaken(&formula, &weakenings);
                    self.formula_cores.remove_blocked(&(i, k.clone()));
                }
            }
        }

        for k in updates.keys() {
            self.formula_cores
                .remove_blocking(&(predicate_name.clone(), k.clone()));
        }
    }
}

enum TriResult<Y, N> {
    None,
    Yes(Y),
    No(N),
}

impl<S> ChcSolution<S>
where
    S: AttributeSet<Object = QuantifiedType, Attribute = PropFormula, Cont = QuantifiedContext>
        + Sync,
{
    fn new(cfg: Vec<PredicateConfig>, chc_sys: &ChcSystem) -> Self {
        let solutions: HashMap<String, PredicateSolution<S>> = cfg
            .iter()
            .map(|p| {
                (
                    p.name.clone(),
                    PredicateSolution::<S>::new(chc_sys, &p, None),
                )
            })
            .collect();

        let partial: PartialSolution<(usize, <S as AttributeSet>::AttributeId)> = PartialSolution {
            formula_cores: Cores::new(),
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
                            .minimal_set()
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

    fn find_cex<B: BasicSolver>(
        &mut self,
        solver: &B,
        chc_sys: &ChcSystem,
    ) -> TriResult<(String, MultiObject<QuantifiedType>), ()> {
        // TODO: add triviality check
        // TODO: cache the ID's to check

        let assignment = self.get_symbolic_assignment();
        let cancelers = MultiCanceler::new();
        let mut out = TriResult::No(());

        'chc_loop: for (chc_index, chc) in chc_sys.chcs.iter().enumerate() {
            let head_predicate = match chc.head.predicate() {
                Some(pred) => pred,
                None => continue 'chc_loop,
            };

            println!("Checking CHC #{chc_index} with head {}", head_predicate.0);

            // The hypotheses of the CHC
            let mut hyp = vec![];
            let mut full_assumptions = OrderedFormulas::new();
            for (k, t) in chc.instantiate_body(&assignment).into_iter() {
                match k {
                    Some(key) => {
                        full_assumptions.add(key, t);
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

            let ids_to_check = self.solutions[head_predicate.0]
                .minimal_set()
                .map(|id| (chc_index, id))
                .filter(|id| !self.partial.formula_cores.is_blocked(id))
                .map(|id| (id.clone(), id));

            let mut tasks = Tasks::from_iter(ids_to_check);
            let worker = ParallelWorker::new(&mut tasks, |_, (_, id)| {
                // A formula to check shouldn't already have a core
                assert!(
                    !self
                        .partial
                        .formula_cores
                        .is_blocked(&(chc_index, id.clone())),
                    "formula to check already had UNSAT-core"
                );

                let formula = head_sets[id.0].get(&id.1);
                let formula_term =
                    rename_symbols(&head_contexts[id.0].to_term(&formula), &head_subst);
                let universal = head_contexts[id.0].prefix.is_universal();
                println!("Querying {}: {}", head_predicate.0, formula_term);

                // ---------- CHC CONSEQUENCE CHECK ----------
                if !universal {
                    println!("Checking CHC consequence...");
                    let query_conf = QueryConf {
                        sig: &chc.signature,
                        n_states: 1,
                        cancelers: Some(cancelers.clone()),
                        model_option: ModelOption::None,
                        evaluate: vec![],
                        save_tee: false,
                    };
                    let mut assertions = hyp.clone();
                    assertions.push(Term::not(formula_term));
                    let instant = Instant::now();
                    let res = full_assumptions.find_cex(
                        solver,
                        &query_conf,
                        &assertions,
                        &SmtTactic::Full,
                        |m| m.clone(),
                    );
                    match res {
                        CexResult::Cex(_, _) => {
                            println!(
                                "    (took {}ms, found SAT(null))",
                                instant.elapsed().as_millis()
                            );
                        }
                        CexResult::UnsatCore(core) => {
                            println!(
                                "    (took {}ms, found UNSAT({}))",
                                instant.elapsed().as_millis(),
                                core.len()
                            );
                            let named_core = core.into_iter().map(|(_, _, id)| id).collect();
                            return (TriResult::No(named_core), vec![], false);
                        }
                        CexResult::Canceled => return (TriResult::None, vec![], false),
                        _ => panic!("solver error {res:?}"),
                    }
                }

                let mut size = 1;
                loop {
                    let extractor = head_contexts[id.0].extractor(size, &head_subst);
                    let extended_sig = extractor.extend_signature(&chc.signature);
                    let query_conf = QueryConf {
                        sig: &extended_sig,
                        n_states: 1,
                        cancelers: Some(cancelers.clone()),
                        model_option: ModelOption::None,
                        evaluate: extractor.to_evaluate(),
                        save_tee: false,
                    };

                    let mut assertions = hyp.clone();
                    assertions.push(extractor.term.clone());
                    assertions.push(extractor.not_satisfies(&formula));
                    let instant = Instant::now();
                    let res = full_assumptions.find_cex(
                        solver,
                        &query_conf,
                        &assertions,
                        &SmtTactic::Full,
                        |m| m.clone(),
                    );

                    match res {
                        CexResult::Cex(_, vals) => {
                            println!(
                                "    (took {}ms, found SAT({size}))",
                                instant.elapsed().as_millis()
                            );
                            cancelers.cancel();
                            return (
                                TriResult::Yes((
                                    head_predicate.0.clone(),
                                    MultiObject(id.0, extractor.extract(&vals)),
                                )),
                                vec![],
                                true,
                            );
                        }
                        CexResult::UnsatCore(core) => {
                            println!(
                                "    (took {}ms, found UNSAT({}) for size {size})",
                                instant.elapsed().as_millis(),
                                core.len()
                            );

                            if universal {
                                let named_core = core.into_iter().map(|(_, _, id)| id).collect();
                                return (TriResult::No(named_core), vec![], false);
                            }
                        }
                        _ => return (TriResult::None, vec![], false),
                        // _ => panic!("({size}) solver error {res:?}"),
                    }

                    size += 1;
                }
            });

            let results = worker.run(parallelism());
            for ((_, id), res) in results {
                match res {
                    TriResult::None => out = TriResult::None,
                    TriResult::Yes(m) => out = TriResult::Yes(m),
                    TriResult::No(named_core) => {
                        self.partial.add_core((chc_index, id), named_core);
                    }
                }
            }
            if matches!(out, TriResult::Yes(_)) {
                return out;
            }
        }

        out
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

    pub fn int_ineqs(
        decl: &HoPredicateDecl,
        int_terms: Vec<Term>,
        bool_terms: Vec<Term>,
        int_templates: IneqTemplates,
        univ_indices: usize,
        disj_length: Option<usize>,
    ) -> Self {
        let prefix = QuantifierPrefix {
            quantifiers: vec![Quantifier::Forall],
            sorts: Arc::new(vec![Sort::Int]),
            names: Arc::new(vec![(0..univ_indices).map(Self::quant_name).collect()]),
        };

        let literal_context = PropContext::literals((0..bool_terms.len()).collect(), int_templates);
        let prop_cont = PropContext::Nary(LogicOp::Or, disj_length, Box::new(literal_context));

        Self {
            name: decl.name.clone(),
            arguments: (0..decl.args.len()).map(Self::arg_name).collect(),
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
pub fn find_lfp<B, S>(
    solver: &B,
    chc_sys: &ChcSystem,
    cfg: Vec<PredicateConfig>,
    minimize: bool,
) -> ChcSolution<S>
where
    B: BasicSolver,
    S: AttributeSet<Object = QuantifiedType, Attribute = PropFormula, Cont = QuantifiedContext>
        + Sync,
{
    let mut chc_sol = ChcSolution::new(cfg, chc_sys);

    if minimize {
        for pred_sol in chc_sol.solutions.values_mut() {
            pred_sol.minimize_by_implication(solver);
        }
    }

    loop {
        match chc_sol.find_cex(solver, chc_sys) {
            TriResult::Yes((name, cex)) => {
                println!("Found CEX: {cex:?}");
                let pred_sol = chc_sol.solutions.get_mut(&name).unwrap();
                let updates = pred_sol.solution.weaken(&pred_sol.context, &cex);

                if minimize {
                    pred_sol.update_weakened(&updates);
                    pred_sol.minimize_by_implication(solver);
                }

                chc_sol.partial.update_weakened(&name, &updates, chc_sys);
            }
            TriResult::None => print!("cannot sample counter-example or verify proof!"),
            TriResult::No(()) => break,
        }
    }

    chc_sol
}

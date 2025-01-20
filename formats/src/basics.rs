//! Basic utilities used by different formats.

use itertools;
use itertools::Itertools;
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    hash::Hash,
    sync::{Arc, Mutex},
    thread,
};

use fly::syntax::Term::*;
use fly::syntax::*;
use fly::term::{prime::clear_next, prime::Next};
use fly::{ouritertools::OurItertools, semantics::Model, transitions::*};
use fly::{semantics::Evaluable, syntax::BinOp};
use smtlib::{
    proc::{SatResp, SolverError},
    sexp::InterpretedValue,
};
use solver::{
    basics::{
        BasicCanceler, BasicSolver, BasicSolverResp, ModelOption, MultiCanceler, QueryConf,
        RespModel,
    },
    conf::SolverConf,
};

#[derive(Debug)]
/// The result of an SMT query looking for a counterexample
pub enum CexResult<K: Eq + Hash> {
    /// The counterexample given as a trace of models
    Cex(RespModel, HashMap<Term, InterpretedValue>),
    /// An UNSAT-core sufficent for showing that the query has no counterexample
    UnsatCore(HashSet<K>),
    /// Indicates that the query has been canceled
    Canceled,
    /// An unknown query response
    Unknown(String),
}

impl<K: Eq + Hash> CexResult<K> {
    /// Convert into an [`Option`], which either contains a counterexample or [`None`].
    pub fn into_trace(self) -> Option<Vec<Model>> {
        match self {
            CexResult::Cex(RespModel::Trace(models), _) => Some(models),
            CexResult::UnsatCore(_) => None,
            _ => panic!("cex result is neither sat or unsat"),
        }
    }

    /// Return `true` if the [`CexResult`] contains a counterexample, or `false` if it contains an UNSAT-core.
    /// If the query is either `Canceled` or `Unknown`, this panics.
    pub fn is_cex(&self) -> bool {
        match self {
            CexResult::Cex(_, _) => true,
            CexResult::UnsatCore(_) => false,
            _ => panic!("cex result is neither sat or unsat"),
        }
    }
}

/// Manages a subset of formulas based on the counter-models they do not satisfy.
///
/// This is used to find a small UNSAT-core of some SMT query by iteratively adding negative
/// counterexamples to be blocked and growing the core in a minimal way to block all of them.
/// If `minimal` is set, the core is guaranteed to be minimal in the local sense that
/// no formula can be dropped from it while still blocking all the previous counterexamples.
struct Core<H: OrderedTerms> {
    formulas: H,
    participants: BTreeMap<H::Key, Term>,
    counter_models: Vec<H::Eval>,
    to_participants: HashMap<usize, HashSet<H::Key>>,
    to_counter_models: HashMap<H::Key, HashSet<usize>>,
    minimal: bool,
}

impl<H: OrderedTerms> Core<H> {
    /// Create a new core from the given formulas. `participants` specifies which formulas
    /// to intialize the core with, and `minimal` determines whether to minimize the core
    /// when adding future participants.
    fn new(formulas: H, participants: BTreeMap<H::Key, Term>, minimal: bool) -> Self {
        Core {
            formulas,
            participants,
            counter_models: vec![],
            to_participants: HashMap::new(),
            to_counter_models: HashMap::new(),
            minimal,
        }
    }

    /// Update the core so that it blocks the given model and all previously blocked models.
    /// This involves adding a blocking formula to the core and potentially minimizing it.
    /// We assume that the new model satisfies the current core (i.e. is not blocked by it).
    ///
    /// Returns `true` if the model has been successfully blocked or `false` if it couldn't be
    /// blocked because it satisfied all candidate formulas.
    fn add_counter_model(&mut self, counter_model: H::Eval) -> bool {
        match self.formulas.first_unsat(&counter_model) {
            Some((key, term)) => {
                let model_idx = self.counter_models.len();
                self.to_participants.insert(model_idx, HashSet::new());
                let mut counter_models: HashSet<usize> = (0..self.counter_models.len())
                    .filter(|i| !self.counter_models[*i].evaluate(&term))
                    .collect();
                counter_models.insert(model_idx);
                self.counter_models.push(counter_model);
                for m_idx in &counter_models {
                    self.to_participants
                        .get_mut(m_idx)
                        .unwrap()
                        .insert(key.clone());
                }
                self.to_counter_models.insert(key.clone(), counter_models);
                self.participants.insert(key.clone(), term);

                if self.minimal {
                    while self.reduce() {}

                    assert!(self.participants.keys().all(|key| {
                        self.to_counter_models[key].iter().any(|m_idx| {
                            self.to_participants[m_idx] == HashSet::from([key.clone()])
                        })
                    }));
                }

                true
            }
            None => false,
        }
    }

    /// Reduces the size of the core by one if possible, by trying to find a formula such that any model it blocks
    /// is also blocked by a different formula in the core. Formulas with a higher index are prioritized for removal.
    ///
    /// Returns `true` if the core has been reduced, or `false` otherwise.
    fn reduce(&mut self) -> bool {
        if let Some(key) = self.participants.keys().cloned().rev().find(|p_idx| {
            self.to_counter_models[p_idx]
                .iter()
                .all(|m_idx| self.to_participants[m_idx].len() > 1)
        }) {
            assert!(self.participants.remove(&key).is_some());
            for m_idx in self.to_counter_models.remove(&key).unwrap() {
                assert!(self.to_participants.get_mut(&m_idx).unwrap().remove(&key));
            }

            true
        } else {
            false
        }
    }

    /// Convert the current core to a set of assumption for use by the solver.
    /// This yields a map which maps each participant index to its [`Term`] and Boolean assumption,
    /// in this case always `true`.
    fn to_assumptions(&self) -> HashMap<usize, (Term, bool)> {
        self.present()
            .enumerate()
            .map(|(i, (_, t))| (i, (t.clone(), true)))
            .collect()
    }

    /// Convert a core returned by the solver to one of `H::Key` elements.
    fn convert_core<O>(&self, core: &HashSet<usize>) -> O
    where
        O: FromIterator<H::Key>,
    {
        self.present()
            .enumerate()
            .filter_map(|(i, (k, _))| {
                if core.contains(&i) {
                    Some(k.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    /// Get the keys and terms currently present in the core.
    fn present(&self) -> impl Iterator<Item = (&H::Key, &Term)> {
        let permanent = self.formulas.permanent();
        let seen: HashSet<H::Key> = permanent.iter().map(|(k, _)| (*k).clone()).collect();
        permanent
            .into_iter()
            .chain(
                self.participants
                    .iter()
                    .filter(move |(k, _)| !seen.contains(k)),
            )
            .unique()
    }
}

/// A term or a model
#[derive(Debug, Clone)]
pub enum TermOrModel {
    /// A model
    Model(Model),
    /// A term
    Term(Term),
}

/// A counterexample or an UNSAT-core
pub enum CexOrCore {
    /// A counterexample
    Cex((Term, Model)),
    /// An UNSAT-core
    Core(HashMap<Term, bool>),
}

/// An sequence of terms, ordered by keys associated with each term. This is used for incremental queries,
/// where some set of terms needs to be included in a query and we have some preference for which terms
/// to always include, which terms to include before others, etc.
pub trait OrderedTerms: Copy + Send + Sync {
    /// The type of keys the terms are ordered by
    type Key: Ord + Hash + Eq + Clone + Send + Sync;
    /// The type of model used to evaluate the terms.
    type Eval: Evaluable;

    /// The terms which should always be included
    fn permanent(&self) -> Vec<(&Self::Key, &Term)>;

    /// Get the first term in the order unsatisfied by the given model (if one exists)
    fn first_unsat(self, model: &Self::Eval) -> Option<(Self::Key, Term)>;

    /// Get all terms, ordered by keys
    fn all_terms(self) -> BTreeMap<Self::Key, Term>;

    /// Find a counterexample to the formulas in the core and the given assertions.
    fn find_cex<B, F>(
        self,
        solver: &B,
        query_conf: &QueryConf<B::Canceler>,
        assertions: &[Term],
        smt_tactic: &SmtTactic,
        counter_model: F,
    ) -> CexResult<Self::Key>
    where
        B: BasicSolver,
        F: Fn(&RespModel) -> Self::Eval,
    {
        let mut core = match smt_tactic {
            SmtTactic::Full => Core::new(self, self.all_terms(), false),
            SmtTactic::Gradual => Core::new(self, BTreeMap::new(), false),
            SmtTactic::Minimal => Core::new(self, BTreeMap::new(), true),
        };
        loop {
            let assumptions = core.to_assumptions();
            match solver.check_sat(query_conf, assertions, &assumptions) {
                Ok(BasicSolverResp::Sat(resp_model, values)) => {
                    if matches!(smt_tactic, SmtTactic::Full)
                        || !core.add_counter_model(counter_model(&resp_model))
                    {
                        // A counter-example was found, no need to search further.
                        return CexResult::Cex(resp_model, values);
                    }
                }
                Ok(BasicSolverResp::Unsat(c)) => {
                    return CexResult::UnsatCore(core.convert_core(&c));
                }
                Ok(BasicSolverResp::Unknown(reason)) => return CexResult::Unknown(reason),
                Err(SolverError::Killed) => return CexResult::Canceled,
                Err(e) => return CexResult::Unknown(format!("error in solver: {e}")),
            }
        }
    }
}

impl<V: AsRef<[Term]> + Copy + Send + Sync> OrderedTerms for V {
    type Key = usize;
    type Eval = Model;

    fn permanent(&self) -> Vec<(&Self::Key, &Term)> {
        vec![]
    }

    fn first_unsat(self, model: &Model) -> Option<(Self::Key, Term)> {
        self.as_ref().iter().enumerate().find_map(|(i, t)| {
            if model.eval(t) == 0 {
                Some((i, t.clone()))
            } else {
                None
            }
        })
    }

    fn all_terms(self) -> BTreeMap<Self::Key, Term> {
        self.as_ref().iter().cloned().enumerate().collect()
    }
}

/// A first-order module is represented using first-order formulas,
/// namely single-vocabulary axioms, initial assertions and safety assertions,
/// and double-vocabulary transition assertions.
/// `disj` denotes whether to split the transitions disjunctively, if possible.
pub struct FOModule {
    /// The signature of the single-state, first-order logical language used
    pub signature: Arc<Signature>,
    /// Containts the different parts of the module
    pub module: DestructuredModule,
    disj: bool,
    smt_tactic: SmtTactic,
}

impl FOModule {
    /// Create a new [`FOModule`] which either decomposes the transitions disjunctive or not, and uses the given [`SmtTactic`].
    pub fn new(m: &Module, disj: bool, smt_tactic: SmtTactic) -> Self {
        FOModule {
            signature: m.signature.clone(),
            module: extract(m).unwrap(),
            disj,
            smt_tactic,
        }
    }

    /// Get the transitions as a disjunction of conjuctions.
    pub fn disj_trans(&self) -> Vec<Vec<&Term>> {
        if self.disj {
            self.module
                .transitions
                .iter()
                .map(|t| match t {
                    Term::NAryOp(NOp::Or, args) => args.iter().collect_vec(),
                    _ => vec![t],
                })
                .multi_cartesian_product_fixed()
                .collect_vec()
        } else {
            vec![self.module.transitions.iter().collect_vec()]
        }
    }

    /// Get an initial counterexample for the given term.
    pub fn init_cex<B: BasicSolver>(&self, solver: &B, t: &Term) -> Option<Model> {
        self.implication_cex(solver, &self.module.inits, t, None, false)
            .into_trace()
            .map(|mut models| {
                assert_eq!(models.len(), 1);
                models.pop().unwrap()
            })
    }

    /// Get a transition counterexample for the given term in the post-state, when assuming the given hypotheses in the pre-state.
    pub fn trans_cex<H, B, C>(
        &self,
        solver: &B,
        hyp: H,
        t: &Term,
        with_safety: bool,
        cancelers: Option<MultiCanceler<MultiCanceler<C>>>,
        save_tee: bool,
    ) -> CexResult<H::Key>
    where
        H: OrderedTerms<Eval = Model>,
        C: BasicCanceler,
        B: BasicSolver<Canceler = C>,
    {
        let transitions = self.disj_trans();
        let local_cancelers: MultiCanceler<C> = MultiCanceler::new();

        if cancelers
            .as_ref()
            .is_some_and(|c| !c.add_canceler(local_cancelers.clone()))
        {
            return CexResult::Canceled;
        }

        let query_conf = QueryConf {
            sig: &self.signature,
            n_states: 2,
            cancelers: Some(local_cancelers.clone()),
            model_option: ModelOption::Minimal,
            evaluate: vec![],
            save_tee,
        };
        let next = Next::new(&self.signature);
        let mut assertions = self.module.axioms.clone();
        assertions.extend(self.module.axioms.iter().map(|a| next.prime(a)));
        if with_safety {
            assertions.extend(self.module.proofs.iter().map(|p| p.safety.x.clone()))
        }
        assertions.push(Term::not(next.prime(t)));

        let cex_results: Vec<CexResult<H::Key>> = thread::scope(|s| {
            transitions
                .into_iter()
                .map(|transition| {
                    s.spawn(|| {
                        let mut local_assertions = assertions.clone();
                        local_assertions.extend(transition.into_iter().cloned());

                        let res = hyp.find_cex(
                            solver,
                            &query_conf,
                            &local_assertions,
                            &self.smt_tactic,
                            |m| m.trace()[0].clone(),
                        );
                        if let CexResult::Cex(_, _) = res {
                            local_cancelers.cancel();
                        }
                        res
                    })
                })
                .collect_vec()
                .into_iter()
                .map(|h| h.join().unwrap())
                .collect_vec()
        });

        // Check whether any counterexample has been found
        if cex_results
            .iter()
            .any(|res| matches!(res, CexResult::Cex(_, _)))
        {
            return cex_results
                .into_iter()
                .find(|res| matches!(res, CexResult::Cex(_, _)))
                .unwrap();
        }

        // Check whether any query has been canceled
        if cex_results
            .iter()
            .any(|res| matches!(res, CexResult::Canceled))
        {
            return CexResult::Canceled;
        }

        // Check whether any query has returned 'unknown'
        if cex_results
            .iter()
            .any(|res| matches!(res, CexResult::Unknown(_)))
        {
            return CexResult::Unknown(
                cex_results
                    .into_iter()
                    .filter_map(|res| match res {
                        CexResult::Unknown(reason) => Some(reason),
                        _ => None,
                    })
                    .join("\n"),
            );
        }

        // Otherwise, all results must be UNSAT-cores
        let unsat_core = cex_results
            .into_iter()
            .flat_map(|res| match res {
                CexResult::UnsatCore(core) => core,
                _ => unreachable!(),
            })
            .collect();

        CexResult::UnsatCore(unsat_core)
    }

    /// Get a (single-state) implication counterexamaple for the given term, when assuming the given hypotheses
    pub fn implication_cex<H, B, C>(
        &self,
        solver: &B,
        hyp: H,
        t: &Term,
        cancelers: Option<MultiCanceler<MultiCanceler<C>>>,
        save_tee: bool,
    ) -> CexResult<H::Key>
    where
        H: OrderedTerms<Eval = Model>,
        C: BasicCanceler,
        B: BasicSolver<Canceler = C>,
    {
        let local_cancelers: MultiCanceler<C> = MultiCanceler::new();
        if cancelers
            .as_ref()
            .is_some_and(|c| !c.add_canceler(local_cancelers.clone()))
        {
            return CexResult::Canceled;
        }

        let query_conf = QueryConf {
            sig: &self.signature,
            n_states: 1,
            cancelers: Some(local_cancelers),
            model_option: ModelOption::Minimal,
            evaluate: vec![],
            save_tee,
        };
        let mut assertions = self.module.axioms.clone();
        assertions.push(Term::not(t));
        hyp.find_cex(solver, &query_conf, &assertions, &self.smt_tactic, |m| {
            m.trace()[0].clone()
        })
    }

    /// Return up to `width` simulated post-states from the given pre-state
    pub fn simulate_from<B, C>(&self, solver: &B, state: &Model, width: usize) -> Vec<Model>
    where
        C: BasicCanceler,
        B: BasicSolver<Canceler = C>,
    {
        let transitions = self.disj_trans();
        let cancelers = MultiCanceler::new();
        let empty_assumptions = HashMap::new();
        let next = Next::new(&self.signature);
        let query_conf = QueryConf {
            sig: &self.signature,
            n_states: 2,
            cancelers: Some(cancelers.clone()),
            model_option: ModelOption::Minimal,
            evaluate: vec![],
            save_tee: false,
        };

        let state_term = state.to_term();
        let samples = Mutex::new(vec![]);
        thread::scope(|s| {
            for transition in &transitions {
                s.spawn(|| {
                    let mut assertions = vec![state_term.clone()];
                    assertions.extend(self.module.axioms.iter().map(|a| next.prime(a)));
                    assertions.extend(transition.iter().copied().cloned());

                    'this_loop: loop {
                        let resp = solver.check_sat(&query_conf, &assertions, &empty_assumptions);
                        match resp {
                            Ok(BasicSolverResp::Sat(resp_model, _)) => {
                                let mut models = resp_model.trace().to_owned();
                                assert_eq!(models.len(), 2);
                                let new_sample = models.pop().unwrap();
                                assertions.push(Term::negate(next.prime(&new_sample.to_term())));
                                {
                                    let mut samples_lock = samples.lock().unwrap();
                                    if samples_lock.len() < width {
                                        samples_lock.push(new_sample);
                                    }
                                    if samples_lock.len() >= width {
                                        cancelers.cancel();
                                        break 'this_loop;
                                    }
                                }
                            }
                            _ => break 'this_loop,
                        }
                    }
                });
            }
        });

        samples.into_inner().unwrap()
    }

    #[allow(missing_docs)]
    pub fn get_pred(&self, conf: &SolverConf, hyp: &[Term], t: &TermOrModel) -> CexOrCore {
        let as_term: Term = match t {
            TermOrModel::Term(t) => t.clone(),
            TermOrModel::Model(m) => m.to_diagram(),
        };
        assert_eq!(self.module.transitions.len(), 1);
        if let NAryOp(NOp::Or, _) = self.module.transitions[0].clone() {
        } else {
            panic!("malformed transitions!")
        }
        let separate_trans = self
            .module
            .transitions
            .iter()
            .flat_map(|t| match t {
                NAryOp(NOp::Or, args) => args.iter().collect_vec(),
                _ => vec![t],
            })
            .collect_vec();

        let mut core = HashMap::new();
        for trans in separate_trans {
            let mut solver = conf.solver(&self.signature, 2);
            for a in self
                .module
                .axioms
                .iter()
                .chain(hyp.iter())
                .chain(vec![trans])
            {
                solver.assert(a).unwrap();
            }
            for a in self.module.axioms.iter() {
                solver.assert(&Next::new(&self.signature).prime(a)).unwrap();
            }
            let mut indicators = HashMap::new();
            let mut ind_to_term = HashMap::new();
            let mut new_terms = vec![];
            if let TermOrModel::Term(term) = t {
                // println!("got term, asserting with no core");
                solver
                    .assert(&Next::new(&self.signature).prime(term))
                    .unwrap();
            } else if let Quantified {
                quantifier: Quantifier::Exists,
                body,
                binders,
            } = Next::new(&self.signature).prime(&as_term)
            {
                if let NAryOp(NOp::And, terms) = *body {
                    for (i, clause) in terms.into_iter().enumerate() {
                        let ind = solver.get_indicator(&i.to_string());
                        new_terms.push(Term::BinOp(
                            BinOp::Equals,
                            Box::new(ind.clone()),
                            Box::new(clause.clone()),
                        ));
                        // println!("adding clause {}", &clause);
                        indicators.insert(ind.clone(), true);
                        ind_to_term.insert(ind, clause);
                    }
                    let new_term = Quantified {
                        quantifier: Quantifier::Exists,
                        body: Box::new(NAryOp(NOp::And, new_terms)),
                        binders,
                    };
                    solver.assert(&new_term).unwrap();
                } else {
                    panic!("bad term for pred!");
                }
            } else {
                panic!("bad term for pred!");
            }

            let resp = solver.check_sat(indicators).expect("error in solver");
            match resp {
                SatResp::Sat => {
                    let states = solver.get_minimal_model().expect("error in solver");
                    assert_eq!(states.len(), 2);
                    // println!("trans: {}", &trans);
                    return CexOrCore::Cex((trans.clone(), states[0].clone()));
                }
                SatResp::Unsat => {
                    // println!("adding group");
                    for (ind, b) in solver
                        .get_unsat_core()
                        .expect("could not get unsat assumptions")
                    {
                        assert!(b, "got false in core");
                        // println!("adding to core: {}", clear_next(ind_to_term[&ind].clone()));
                        core.insert(clear_next(ind_to_term[&ind].clone()), b);
                    }
                }
                SatResp::Unknown(error) => panic!("{}", error),
            }
            solver.save_tee();
        }
        return CexOrCore::Core(core);
    }

    #[allow(missing_docs)]
    pub fn implies_cex(&self, conf: &SolverConf, hyp: &[Term], t: &Term) -> Option<Model> {
        let mut solver = conf.solver(&self.signature, 1);
        for a in hyp {
            solver.assert(a).unwrap();
        }
        solver.assert(&Term::negate(t.clone())).unwrap();

        let resp = solver.check_sat(HashMap::new()).expect("error in solver");
        solver.save_tee();
        match resp {
            SatResp::Sat => {
                let states = solver.get_minimal_model().expect("error in solver");
                assert_eq!(states.len(), 1);
                return Some(states[0].clone());
            }
            SatResp::Unsat => None,
            SatResp::Unknown(_) => panic!(),
        }
    }

    /// Get a safety implication counterexample when assuming the given hypotheses.
    pub fn safe_implication_cex<H, B, C>(
        &self,
        solver: &B,
        hyp: H,
        cancelers: Option<MultiCanceler<MultiCanceler<C>>>,
    ) -> CexResult<H::Key>
    where
        H: OrderedTerms<Eval = Model>,
        C: BasicCanceler,
        B: BasicSolver<Canceler = C>,
    {
        let mut core = HashSet::new();
        for s in self.module.proofs.iter() {
            match self.implication_cex(solver, hyp, &s.safety.x, cancelers.clone(), false) {
                CexResult::UnsatCore(new_core) => core.extend(new_core),
                res => return res,
            }
        }

        CexResult::UnsatCore(core)
    }

    /// Get a safety counterexample in the post-state when assuming the given hypotheses in the pre-state.
    pub fn trans_safe_cex<H, C, B>(
        &self,
        solver: &B,
        hyp: H,
        cancelers: Option<MultiCanceler<MultiCanceler<C>>>,
    ) -> CexResult<H::Key>
    where
        H: OrderedTerms<Eval = Model>,
        C: BasicCanceler,
        B: BasicSolver<Canceler = C>,
    {
        let mut core = HashSet::new();
        for s in self.module.proofs.iter() {
            match self.trans_cex(solver, hyp, &s.safety.x, true, cancelers.clone(), false) {
                CexResult::UnsatCore(new_core) => core.extend(new_core),
                res => return res,
            }
        }

        CexResult::UnsatCore(core)
    }

    #[allow(missing_docs)]
    pub fn safe_cex(&self, conf: &SolverConf, hyp: &[Term]) -> Option<Model> {
        for s in self.module.proofs.iter() {
            if let Some(model) = self.implies_cex(conf, hyp, &s.safety.x) {
                return Some(model);
            }
        }

        None
    }
}

/// A tactic for gradual SMT calls
pub enum SmtTactic {
    /// Use all assertions in the first query.
    Full,
    /// Add assertions one by one when getting spurious counterexamples, each time adding the next assertion unsatisfied by the counterexample.
    Gradual,
    /// Add assertions one by one when getting spurious counterexamples, each time adding the next assertion unsatisfied by a counterexample,
    /// but maintain minimality by removing assertions unnecessary for blocking the spurious counterexamples seen so far.
    Minimal,
}

impl From<&str> for SmtTactic {
    fn from(value: &str) -> Self {
        match value {
            "gradual" => Self::Gradual,
            "minimal" => Self::Minimal,
            "full" => Self::Full,
            _ => panic!("invalid choice of SMT technique!"),
        }
    }
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Find a fixpoint invariant expressing reachable states in a given
//! lemma domain.

use fly::semantics::Model;
use solver::basics::{BasicCanceler, MultiCanceler};
use std::cmp::Ordering;
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use crate::qalpha::atoms::Literal;
use crate::{
    basics::{FOModule, QalphaConfig, QfBody, SimulationConfig},
    parallel::parallelism,
    parallel::Tasks,
    qalpha::{
        atoms::generate_literals,
        frame::{InductionFrame, OperationStats},
        language::{advanced, baseline, BoundedLanguage},
        quant::ordered_prefixes_with_constants,
    },
};
use fly::syntax::{BinOp, Module, Term, ThmStmt};
use solver::{
    backends::SolverType,
    basics::{BasicSolver, FallbackSolvers, ParallelSolvers},
    conf::SolverConf,
};

use rayon::prelude::*;

macro_rules! timed {
    ($blk:block) => {{
        let start = Instant::now();
        $blk
        start.elapsed()
    }};
}

pub mod defaults {
    pub const QUANT_SAME_SORT: usize = 3;
    pub const SIMULATION_SORT_SIZE: usize = 0;
    pub const MIN_DISJUNCTS: usize = 2;
    pub const MIN_NON_UNIT_SIZE: usize = 2;
}

#[derive(PartialEq, Eq, Clone)]
pub enum TraversalDepth {
    Bfs(usize),
    Dfs(usize),
}

use TraversalDepth::*;

impl TraversalDepth {
    pub fn depth(&self) -> usize {
        match self {
            TraversalDepth::Bfs(d) | TraversalDepth::Dfs(d) => *d,
        }
    }
}

impl PartialOrd for TraversalDepth {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TraversalDepth {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self, other) {
            (Bfs(x), Bfs(y)) => x.cmp(y),
            (Dfs(x), Dfs(y)) => x.cmp(y).reverse(),
            _ => panic!("cannot compare BFS and DFS depths!"),
        }
    }
}

/// (sum of universe sizes, simulation depth)
pub type SamplePriority = (usize, TraversalDepth);

pub fn sample_priority(
    cfg: &SimulationConfig,
    universe: &[usize],
    depth: usize,
) -> Option<SamplePriority> {
    let sum: usize = universe.iter().product();
    if !cfg.depth.is_some_and(|d| depth > d) {
        Some((sum, if cfg.dfs { Dfs(depth) } else { Bfs(depth) }))
    } else {
        None
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct ForwardCti {
    pub pre: Option<Model>,
    pub post: Model,
}

impl ForwardCti {
    pub fn new(pre: Option<Model>, post: Model) -> Self {
        Self { pre, post }
    }

    pub fn universe(&self) -> &[usize] {
        &self.post.universe
    }
}

#[derive(Clone, Copy)]
pub enum Strategy {
    None,
    Houdini,
    HoudiniPd,
    Weaken,
    WeakenPd,
}

impl From<&str> for Strategy {
    fn from(value: &str) -> Self {
        match value {
            "none" => Self::None,
            "houdini" => Self::Houdini,
            "houdini-pd" => Self::HoudiniPd,
            "weaken" => Self::Weaken,
            "weaken-pd" => Self::WeakenPd,
            _ => panic!("invalid CTI strategy option"),
        }
    }
}

impl Strategy {
    fn property_directed(&self) -> bool {
        matches!(self, Self::HoudiniPd | Self::WeakenPd)
    }

    fn is_weaken(&self) -> bool {
        matches!(self, Self::Weaken | Self::WeakenPd)
    }

    fn is_houdini(&self) -> bool {
        matches!(self, Self::Houdini | Self::HoudiniPd)
    }
}

/// Check how much of the handwritten invariant the given lemmas cover.
fn invariant_cover<S: BasicSolver>(
    m: &Module,
    solver: &S,
    fo: &FOModule,
    lemmas: &[Term],
) -> (usize, usize) {
    let proof = m
        .statements
        .iter()
        .filter_map(|s| match s {
            ThmStmt::Assert(p) => Some(p),
            _ => None,
        })
        .next()
        .unwrap();

    let covered = proof
        .invariants
        .par_iter()
        .filter(|inv| {
            !fo.implication_cex(solver, lemmas, &inv.x, None, false)
                .is_cex()
        })
        .count();

    (covered, proof.invariants.len())
}

/// An inductive fixpoint
pub struct FoundFixpoint {
    /// The last frame of the fixpoint computation.
    /// This is inductive iff `reduced_proof` is not `None`
    proof: Vec<Term>,
    /// The fixpoint term, semantically reduced.
    /// If `None`, the run has been terminated/aborted before reaching the fixpoint
    reduced_proof: Option<Vec<Term>>,
    /// A subset of the (reduced) fixpoint term which suffices to prove safety.
    /// If None, the last frame is unsafe
    safety_proof: Option<Vec<Term>>,
    /// Statistics for this execution
    stats: FixpointStats,
}

impl FoundFixpoint {
    #[allow(clippy::too_many_arguments)]
    fn new(
        time: Duration,
        success: bool,
        proof: Vec<Term>,
        full_size: usize,
        max_size: usize,
        reduced_proof: Option<Vec<Term>>,
        safety_proof: Option<Vec<Term>>,
        covering: Option<(usize, usize)>,
        processed_states: usize,
        generated_states: usize,
        weaken_stats: OperationStats,
        get_unsat_stats: OperationStats,
    ) -> Self {
        let stats = FixpointStats {
            time_sec: time.as_secs_f64(),
            success,
            simplified_size: proof.len(),
            full_size,
            max_size,
            reduced: reduced_proof.as_ref().map(|r| r.len()),
            safety: safety_proof.as_ref().map(|r| r.len()),
            covering,
            processed_states,
            generated_states,
            weaken_stats,
            get_unsat_stats,
        };
        FoundFixpoint {
            proof,
            reduced_proof,
            safety_proof,
            stats,
        }
    }

    pub fn report(&self, print_nondet: bool, json: bool) {
        let print_inv = |name: &str, size: usize, inv: &[Term]| {
            println!("{name} (size={size}) {{");
            for lemma in inv {
                println!("  invariant {lemma}");
            }
            println!("}} end of {name}");
        };

        if let Some(reduced_proof) = &self.reduced_proof {
            println!(
                "Fixpoint REACHED! frame_size={}, reduced_size={}",
                self.proof.len(),
                reduced_proof.len()
            );
        } else {
            println!("Fixpoint NOT reached! frame_size={}", self.proof.len());
        }

        if let Some(safety_proof) = &self.safety_proof {
            println!("Safety VERIFIED! proof_size={}", safety_proof.len());
        } else {
            println!("Safety NOT verified.");
        }

        if print_nondet {
            print_inv("frame", self.proof.len(), &self.proof);
            if let Some(reduced_proof) = &self.reduced_proof {
                print_inv("reduced", reduced_proof.len(), reduced_proof);
            }
            if let Some(safety_proof) = &self.safety_proof {
                print_inv("safety", safety_proof.len(), safety_proof);
            }

            if json {
                println!("=============== JSON ===============");
                println!("{}", serde_json::to_string(&self.stats).unwrap());
            }
        }
    }

    pub fn is_safe(&self) -> bool {
        self.safety_proof.is_some()
    }

    pub fn reduced(&self) -> Vec<Term> {
        self.reduced_proof.as_ref().unwrap().clone()
    }

    pub fn time_sec(&self) -> f64 {
        self.stats.time_sec
    }
}

#[derive(serde::Serialize, serde::Deserialize)]
pub struct FixpointStats {
    /// Total runtime
    time_sec: f64,
    /// Whether the task finished successfully
    success: bool,
    /// The number of formulas in the simplified final frame
    simplified_size: usize,
    /// The number of formulas in the final weaken frame, containing unsimplified formulas
    pub full_size: usize,
    /// The maximal number of formulas encountered in the weaken frame,
    pub max_size: usize,
    /// The number of formulas in reduced by implication checks (if available)
    pub reduced: Option<usize>,
    /// The number of formulas in the safety proof (if available)
    safety: Option<usize>,
    /// Number of lemmas in the handwritten invariant covered by the result
    /// and the total number of lemmas in the handwritten invariants
    covering: Option<(usize, usize)>,
    /// The number of states processed during the execution
    processed_states: usize,
    /// The number of states generated during the execution (some might not have been processed)
    generated_states: usize,
    /// Statistics regarding frame weaken operations
    pub weaken_stats: OperationStats,
    /// Statistics regarding frame get_unsat operations
    get_unsat_stats: OperationStats,
}

fn parallel_solver(cfg: &QalphaConfig, seeds: usize) -> impl BasicSolver {
    ParallelSolvers::new(
        (0..seeds)
            .flat_map(|_| {
                [
                    SolverConf::new(SolverType::Z3, true, &cfg.fname, 0, None),
                    SolverConf::new(SolverType::Cvc5, true, &cfg.fname, 0, None),
                ]
            })
            .collect(),
    )
}

#[allow(dead_code)]
fn fallback_solver(cfg: &QalphaConfig) -> impl BasicSolver {
    // For the solvers in fallback fashion we alternate between Z3 and CVC5
    // with increasing timeouts and varying seeds, ending with a Z3 solver with
    // no timeout. The idea is to try both Z3 and CVC5 with some timeout to see if any
    // of them solve the query, and gradually increase the timeout for both,
    // ending with no timeout at all. The seed changes are meant to add some
    // variation vis-a-vis previous attempts.
    FallbackSolvers::new(vec![
        SolverConf::new(SolverType::Z3, true, &cfg.fname, 3, Some(0)),
        SolverConf::new(SolverType::Cvc5, true, &cfg.fname, 3, Some(0)),
        SolverConf::new(SolverType::Z3, true, &cfg.fname, 60, Some(1)),
        SolverConf::new(SolverType::Cvc5, true, &cfg.fname, 60, Some(1)),
        SolverConf::new(SolverType::Z3, true, &cfg.fname, 600, Some(2)),
        SolverConf::new(SolverType::Cvc5, true, &cfg.fname, 600, Some(2)),
        SolverConf::new(SolverType::Z3, true, &cfg.fname, 0, Some(3)),
    ])
}

fn qalpha<L, S>(cfg: Arc<QalphaConfig>, langs: Vec<Arc<L>>, m: &Module, solver: &S) -> FoundFixpoint
where
    L: BoundedLanguage,
    S: BasicSolver,
{
    log::info!("Running qalpha algorithm...");

    // Calculate the total domain size as the sum of individual language sizes
    let total_size: f64 = langs.iter().map(|lang| 10_f64.powf(lang.log_size())).sum();
    let log_domain_size = total_size.log10();
    log::info!("Approximate total domain size: 10^{log_domain_size:.2}");

    run_qalpha::<L, S>(cfg.clone(), langs, solver, m, &cfg.fo)
}

pub fn qalpha_dynamic(
    cfg: Arc<QalphaConfig>,
    m: &Module,
    raw_literals: Option<Vec<Literal>>,
    print_nondet: bool,
) -> FoundFixpoint {
    // TODO: add fallback solver option or remove it from command arguments
    let solver = parallel_solver(&cfg, cfg.seeds);

    // TODO: make nesting and include_eq configurable or remove them from command arguments
    log::info!("Generating literals...");
    let mut literals: Vec<_>;
    let cube_literals: Vec<_>;
    let gen_time = timed!({
        literals = raw_literals.unwrap_or_else(|| {
            generate_literals(
                &m.signature,
                &cfg.quant_cfg,
                cfg.qf_cfg.nesting,
                true,
                None,
                &cfg.fo,
                &solver,
                cfg.remove_trivial_atoms,
            )
        });
        let non_universal_vars = cfg.quant_cfg.vars_after_first_exist();
        cube_literals = literals
            .iter()
            .filter(|literal| !literal.ids().is_disjoint(&non_universal_vars))
            .cloned()
            .collect();
        let universal_vars = cfg.quant_cfg.strictly_universal_vars();
        literals.retain(|lit| match (lit.0.as_ref(), lit.1) {
            (Term::BinOp(BinOp::Equals, t1, t2), false) => match (t1.as_ref(), t2.as_ref()) {
                (Term::Id(name1), Term::Id(name2)) => {
                    !universal_vars.contains(name1) && !universal_vars.contains(name2)
                }
                (Term::Id(name), _) | (_, Term::Id(name)) => !universal_vars.contains(name),
                _ => true,
            },
            _ => true,
        });
    });

    log::info!(
        "Generated {} literals in {}ms ({} containing variables after first existential)",
        literals.len(),
        if print_nondet {
            gen_time.as_millis()
        } else {
            0
        },
        cube_literals.len()
    );

    match (&cfg.qf_cfg.qf_body, cfg.baseline) {
        (QfBody::Cnf, true) => qalpha(
            cfg.clone(),
            vec![baseline::quant_cnf_language(
                cfg.quant_cfg.clone(),
                cfg.qf_cfg.clause_size.unwrap(),
                literals,
            )],
            m,
            &solver,
        ),
        (QfBody::Cnf, false) => qalpha(
            cfg.clone(),
            vec![advanced::quant_cnf_language(
                cfg.quant_cfg.clone(),
                cfg.qf_cfg.clause_size.unwrap(),
                literals,
            )],
            m,
            &solver,
        ),
        (QfBody::PDnf, true) => qalpha(
            cfg.clone(),
            vec![baseline::quant_pdnf_language(
                cfg.quant_cfg.clone(),
                cfg.qf_cfg.clause_size.unwrap(),
                cfg.qf_cfg.cubes.unwrap(),
                literals,
                cube_literals,
            )],
            m,
            &solver,
        ),
        (QfBody::PDnf, false) => qalpha(
            cfg.clone(),
            vec![advanced::quant_pdnf_language(
                cfg.quant_cfg.clone(),
                cfg.qf_cfg.clause_size.unwrap(),
                cfg.qf_cfg.cubes.unwrap(),
                literals,
                cube_literals,
            )],
            m,
            &solver,
        ),
        (QfBody::Dnf, true) => qalpha(
            cfg.clone(),
            vec![baseline::quant_dnf_language(
                cfg.quant_cfg.clone(),
                cfg.qf_cfg.cubes.unwrap(),
                literals,
            )],
            m,
            &solver,
        ),
        (QfBody::Dnf, false) => qalpha(
            cfg.clone(),
            vec![advanced::quant_dnf_language(
                cfg.quant_cfg.clone(),
                cfg.qf_cfg.cubes.unwrap(),
                literals,
            )],
            m,
            &solver,
        ),
    }
}

/// Run qalpha with multiple languages, one per (prefix, constants) combination.
///
/// This function generates multiple bounded languages by:
/// 1. Calling `ordered_prefixes_with_constants` to get all prefix+constant combinations
/// 2. For each combination, generating literals specific to those constants
/// 3. Creating a language from those literals
/// 4. Running qalpha with all generated languages together
///
/// # Arguments
/// * `cfg` - The qalpha configuration (must have baseline=false, qf_body=PDnf, and multi_* fields set)
/// * `m` - The module to verify
/// * `print_nondet` - Whether to print nondeterministic timing information
pub fn qalpha_multi_prefix(
    cfg: Arc<QalphaConfig>,
    m: &Module,
    print_nondet: bool,
) -> FoundFixpoint {
    assert!(
        !cfg.baseline,
        "qalpha_multi_prefix requires baseline=false (advanced language)"
    );
    assert!(
        matches!(cfg.qf_cfg.qf_body, QfBody::PDnf),
        "qalpha_multi_prefix currently only supports QfBody::PDnf"
    );

    let prefix_length = cfg
        .multi_prefix_length
        .expect("multi_prefix_length must be set");
    let constant_limit = cfg
        .multi_constant_limit
        .expect("multi_constant_limit must be set");
    let sort_order = cfg
        .multi_sort_order
        .as_ref()
        .expect("multi_sort_order must be set");
    let total_per_sort = cfg
        .multi_total_per_sort
        .as_ref()
        .expect("multi_total_per_sort must be set");

    let solver = parallel_solver(&cfg, cfg.seeds);

    log::info!("Generating prefixes with constants...");
    let prefix_combinations = ordered_prefixes_with_constants(
        m.signature.clone(),
        sort_order,
        prefix_length,
        constant_limit,
        total_per_sort,
        cfg.exists_forall_only,
    );
    log::info!(
        "Generated {} prefix+constant combinations",
        prefix_combinations.len()
    );

    // Log each combination
    for (i, (prefix, constants)) in prefix_combinations.iter().enumerate() {
        log::info!(
            "Combination {}: prefix = {:?}, constants = {:?}",
            i + 1,
            prefix,
            constants.iter().flatten().collect::<Vec<_>>()
        );
    }

    log::info!("Generating languages for each combination...");
    let languages: Vec<_>;
    let gen_time = timed!({
        languages = prefix_combinations
            .into_par_iter()
            .map(|(prefix, constants)| {
                // Convert prefix to config
                let quant_cfg = prefix.to_config();

                // Generate literals with the specific constants
                let literals: Vec<Literal> = generate_literals(
                    &m.signature,
                    &quant_cfg,
                    cfg.qf_cfg.nesting,
                    true,
                    Some(constants),
                    &cfg.fo,
                    &solver,
                    cfg.remove_trivial_atoms,
                );

                // Filter literals based on quantifier structure
                let non_universal_vars = quant_cfg.vars_after_first_exist();
                let cube_literals: Vec<_> = literals
                    .iter()
                    .filter(|literal| !literal.ids().is_disjoint(&non_universal_vars))
                    .cloned()
                    .collect();

                let mut filtered_literals = literals;
                let universal_vars = quant_cfg.strictly_universal_vars();
                filtered_literals.retain(|lit| match (lit.0.as_ref(), lit.1) {
                    (Term::BinOp(BinOp::Equals, t1, t2), false) => match (t1.as_ref(), t2.as_ref())
                    {
                        (Term::Id(name1), Term::Id(name2)) => {
                            !universal_vars.contains(name1) && !universal_vars.contains(name2)
                        }
                        (Term::Id(name), _) | (_, Term::Id(name)) => !universal_vars.contains(name),
                        _ => true,
                    },
                    _ => true,
                });

                // Create PDnf language
                advanced::quant_pdnf_language(
                    Arc::new(quant_cfg),
                    cfg.qf_cfg.clause_size.unwrap(),
                    cfg.qf_cfg.cubes.unwrap(),
                    filtered_literals,
                    cube_literals,
                )
            })
            .collect();
    });

    log::info!(
        "Generated {} languages in {}ms",
        languages.len(),
        if print_nondet {
            gen_time.as_millis()
        } else {
            0
        }
    );

    qalpha(cfg, languages, m, &solver)
}

/// Run the qalpha algorithm on the configured lemma domains.
fn run_qalpha<L, S>(
    cfg: Arc<QalphaConfig>,
    langs: Vec<Arc<L>>,
    solver: &S,
    m: &Module,
    fo: &FOModule,
) -> FoundFixpoint
where
    L: BoundedLanguage,
    S: BasicSolver,
{
    let start = std::time::Instant::now();

    let mut frame: InductionFrame<L> = InductionFrame::new(
        m,
        m.signature.clone(),
        langs,
        cfg.sim.clone(),
        cfg.strategy.property_directed(),
        parallelism() / (2 * cfg.seeds),
    );

    // Initialize simulations.
    let mut samples: Tasks<SamplePriority, ForwardCti> = frame.initial_samples();
    let mut full_houdini_frame: Option<Vec<Term>> = None;

    // Overapproximate initial states.
    if cfg.strategy.is_weaken() {
        loop {
            let ctis = frame.init_cex(fo, solver);
            if ctis.is_empty() {
                break;
            }
            frame.weaken(&ctis);
            for cti in ctis {
                frame.see(&cti.post);
                samples.insert(sample_priority(&cfg.sim, cti.universe(), 0).unwrap(), cti);
            }
        }

        frame.finish_initial();
    }

    // Handle transition CTI's.
    let mut run_sim = !samples.is_empty();
    let mut run_smt = cfg.strategy.is_weaken() || (cfg.strategy.is_houdini() && !run_sim);
    while run_sim || run_smt {
        let mut ctis: Vec<ForwardCti> = vec![];
        let canceler = MultiCanceler::new();
        // Get new samples and CTI's, and if enabled, check the safety of the frame.
        let not_safe = thread::scope(|s| {
            let smt_handle = s.spawn(|| {
                if run_smt {
                    qalpha_cti(&cfg, solver, fo, &frame, canceler.clone())
                } else {
                    Some(vec![])
                }
            });

            ctis = if run_sim {
                frame.extend(&mut samples, canceler.clone())
            } else {
                vec![]
            };

            let smt_cti = smt_handle.join().unwrap();
            // Abort
            if smt_cti.is_none() {
                return true;
            }

            let smt_cti = smt_cti.unwrap();
            for cti in &smt_cti {
                if !matches!(frame.see(&cti.post), Some(false)) {
                    samples.insert(
                        sample_priority(&cfg.sim, cti.universe(), 0).unwrap(),
                        cti.clone(),
                    );
                }
            }
            ctis.extend(smt_cti);

            false
        });

        if not_safe {
            return FoundFixpoint::new(
                start.elapsed(),
                false,
                frame.proof(),
                frame.weaken_lemmas.len(),
                frame.weaken_lemmas.max_size,
                None,
                None,
                None,
                samples.total() - samples.len(),
                samples.total(),
                frame.weaken_stats(),
                frame.get_unsat_stats(),
            );
        }

        if run_sim {
            frame.log_info(format!(
                "{} samples remaining (out of {})",
                samples.len(),
                samples.total()
            ));
        }

        if cfg.strategy.is_houdini() && run_smt {
            frame.remove_unsat(&ctis);
        } else {
            frame.weaken(&ctis);
        }

        run_sim = !ctis.is_empty() && !samples.is_empty();
        run_smt = if cfg.strategy.is_weaken() {
            !ctis.is_empty()
        } else if cfg.strategy.is_houdini() {
            if !run_smt && ctis.is_empty() {
                full_houdini_frame = Some(frame.proof());
            }

            (!run_smt && ctis.is_empty()) || (run_smt && !ctis.is_empty())
        } else {
            false
        }
    }

    if !matches!(cfg.strategy, Strategy::None) {
        frame.log_info("Checking safety...");
        frame.is_safe(fo, solver, None);
    }
    let time = start.elapsed();
    let proof = if cfg.strategy.is_houdini() {
        full_houdini_frame.unwrap()
    } else {
        frame.proof()
    };
    let reduced_proof = frame.reduced_proof();
    let safety_proof = frame.safety_proof();
    let covering = reduced_proof
        .as_ref()
        .map(|reduced| invariant_cover(m, solver, fo, reduced));
    let success = match cfg.strategy {
        Strategy::None => true,
        Strategy::Houdini => reduced_proof.is_some(),
        Strategy::HoudiniPd => safety_proof.is_some(),
        Strategy::Weaken => reduced_proof.is_some(),
        Strategy::WeakenPd => safety_proof.is_some(),
    };

    FoundFixpoint::new(
        time,
        success,
        proof,
        frame.weaken_lemmas.len(),
        frame.weaken_lemmas.max_size,
        reduced_proof,
        safety_proof,
        covering,
        samples.total() - samples.len(),
        samples.total(),
        frame.weaken_stats(),
        frame.get_unsat_stats(),
    )
}

/// Attempt to find a transition CTI for the current frame. If enabled by the configuration, this also checks
/// the safety of the frame and returns `None` if the execution should abort. Otherwise, `Some(_)` is returned
/// which contains a vector of counterexamples.
fn qalpha_cti<L, S>(
    cfg: &QalphaConfig,
    solver: &S,
    fo: &FOModule,
    frame: &InductionFrame<'_, L>,
    canceler: MultiCanceler<MultiCanceler<S::Canceler>>,
) -> Option<Vec<ForwardCti>>
where
    L: BoundedLanguage,
    S: BasicSolver,
{
    if canceler.is_canceled() {
        return Some(vec![]);
    }

    if cfg.strategy.property_directed() {
        frame.log_info("Checking safety...");
        match frame.is_safe(fo, solver, Some(canceler.clone())) {
            None => return Some(vec![]),
            Some(false) => {
                canceler.cancel();
                return None;
            }
            Some(true) => frame.log_info("Safety verified."),
        }
    }

    Some(frame.trans_cex(fo, solver, canceler, cfg.conj))
}

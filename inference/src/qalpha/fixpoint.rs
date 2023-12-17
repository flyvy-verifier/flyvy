// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Find a fixpoint invariant expressing reachable states in a given
//! lemma domain.

use fly::semantics::Model;
use itertools::Itertools;
use solver::basics::{BasicCanceler, MultiCanceler};
use std::cmp::Ordering;
use std::sync::Arc;
use std::thread;
use std::time::Duration;

use crate::basics::{QfBody, SimulationConfig};
use crate::parallel::Tasks;
use crate::{
    basics::{FOModule, QalphaConfig},
    qalpha::{
        atoms::restrict_by_prefix,
        baseline::Baseline,
        lemma::{self, InductionFrame},
        subsume::{self, Element},
        weaken::{Domain, LemmaQf, LemmaQfConfig},
    },
};
use fly::syntax::{Module, Term, ThmStmt};
use solver::{
    backends::SolverType,
    basics::{BasicSolver, FallbackSolvers, ParallelSolvers},
    conf::SolverConf,
};

use rayon::prelude::*;

pub mod defaults {
    pub const QUANT_SAME_SORT: usize = 3;
    pub const SIMULATION_SORT_SIZE: usize = 2;
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

pub enum Strategy {
    None,
    Houdini,
    HoudiniPd,
    Weaken,
    WeakenPd,
}

impl Default for Strategy {
    fn default() -> Self {
        Self::Weaken
    }
}

impl From<&String> for Strategy {
    fn from(value: &String) -> Self {
        match value.as_str() {
            "none" => Self::None,
            "houdini" => Self::Houdini,
            "houdini-pd" => Self::HoudiniPd,
            "weaken" => Self::Weaken,
            "weaken-pd" => Self::WeakenPd,
            _ => panic!("invalid CTI option"),
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
struct FoundFixpoint {
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
        reduced_proof: Option<Vec<Term>>,
        safety_proof: Option<Vec<Term>>,
        covering: Option<(usize, usize)>,
        processed_states: usize,
        generated_states: usize,
    ) -> Self {
        let stats = FixpointStats {
            time_sec: time.as_secs_f64(),
            success,
            size: proof.len(),
            reduced: reduced_proof.as_ref().map(|r| r.len()),
            safety: safety_proof.as_ref().map(|r| r.len()),
            covering,
            processed_states,
            generated_states,
        };
        FoundFixpoint {
            proof,
            reduced_proof,
            safety_proof,
            stats,
        }
    }

    fn report(&self, print_invariant: bool) {
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

        if print_invariant {
            print_inv("frame", self.proof.len(), &self.proof);
            if let Some(reduced_proof) = &self.reduced_proof {
                print_inv("reduced", reduced_proof.len(), reduced_proof);
            }
            if let Some(safety_proof) = &self.safety_proof {
                print_inv("safety", safety_proof.len(), safety_proof);
            }
        }

        println!("==============================");
        println!(
            "stats_json: {}",
            serde_json::to_string(&self.stats).unwrap()
        );
        println!("==============================");
    }
}

#[derive(serde::Serialize)]
struct FixpointStats {
    /// Total runtime
    time_sec: f64,
    /// Whether the task finished successfully
    success: bool,
    /// The number of formulas in the final frame
    size: usize,
    /// The number of formulas in reduced form (if available)
    reduced: Option<usize>,
    /// The number of formulas in the safety proof (if available)
    safety: Option<usize>,
    /// Number of lemmas in the handwritten invariant covered by the result
    /// and the total number of lemmas in the handwritten invariants
    covering: Option<(usize, usize)>,
    /// The number of states processed during the execution
    processed_states: usize,
    /// The number of states generated during the execution (some might not have been processed)
    generated_states: usize,
}

fn parallel_solver(infer_cfg: &QalphaConfig) -> impl BasicSolver {
    ParallelSolvers::new(vec![
        SolverConf::new(SolverType::Z3, true, &infer_cfg.fname, 0, 0),
        SolverConf::new(SolverType::Cvc5, true, &infer_cfg.fname, 0, 0),
    ])
}

fn fallback_solver(infer_cfg: &QalphaConfig) -> impl BasicSolver {
    // For the solvers in fallback fashion we alternate between Z3 and CVC5
    // with increasing timeouts and varying seeds, ending with a Z3 solver with
    // no timeout. The idea is to try both Z3 and CVC5 with some timeout to see if any
    // of them solve the query, and gradually increase the timeout for both,
    // ending with no timeout at all. The seed changes are meant to add some
    // variation vis-a-vis previous attempts.
    FallbackSolvers::new(vec![
        SolverConf::new(SolverType::Z3, true, &infer_cfg.fname, 3, 0),
        SolverConf::new(SolverType::Cvc5, true, &infer_cfg.fname, 3, 0),
        SolverConf::new(SolverType::Z3, true, &infer_cfg.fname, 60, 1),
        SolverConf::new(SolverType::Cvc5, true, &infer_cfg.fname, 60, 1),
        SolverConf::new(SolverType::Z3, true, &infer_cfg.fname, 600, 2),
        SolverConf::new(SolverType::Cvc5, true, &infer_cfg.fname, 600, 2),
        SolverConf::new(SolverType::Z3, true, &infer_cfg.fname, 0, 3),
    ])
}

pub fn qalpha<E, L, S>(cfg: Arc<QalphaConfig>, m: &Module, solver: &S, print_invariant: bool)
where
    E: Element,
    L: LemmaQf<Body = E>,
    S: BasicSolver,
{
    let domain_size_of = |doms: &[Domain<L>]| {
        doms.iter()
            .map(|(_, lemma_qf, _)| lemma_qf.approx_space_size())
            .sum::<usize>()
    };

    log::debug!("Computing predicate domains...");
    let lemma_qf_cfg = L::Config::new(&cfg.qf_cfg);
    let domain_configs: Vec<_> = cfg
        .vary
        // Get all requested prefix sizes
        .quant_sizes(&cfg)
        .into_iter()
        .flat_map(|quant| cfg.vary.quant_exists(&cfg, quant))
        .cartesian_product(cfg.vary.qf_configs(lemma_qf_cfg))
        .filter(|((_, exist), qf)| *exist > 0 || qf.is_universal())
        .collect();

    let domains: Vec<(_, Vec<Domain<_>>, usize)> = domain_configs
        .into_iter()
        .map(|((quant, exist), qf_cfg)| {
            let d: Vec<_> = quant
                .prefixes(quant.num_vars(), exist)
                .into_iter()
                .map(|prefix| {
                    let prefix = Arc::new(prefix);
                    let restricted =
                        Arc::new(restrict_by_prefix(&cfg.literals, &cfg.quant_cfg, &prefix));
                    let lemma_qf =
                        Arc::new(L::new(qf_cfg.clone(), restricted.clone(), prefix.clone()));
                    (prefix, lemma_qf, restricted)
                })
                .collect();
            let domain_size = domain_size_of(&d);

            ((quant, exist, qf_cfg), d, domain_size)
        })
        .sorted_by_key(|(_, _, domain_size)| *domain_size)
        .collect();

    println!("Number of individual domains: {}", domains.len());

    for (iteration, ((quant, e, qf), active_domains, domain_size)) in
        domains.into_iter().enumerate()
    {
        println!();
        println!("({iteration}) Running qalpha algorithm...");
        println!(
            "Approximate domain size: 10^{:.2} ({domain_size})",
            (domain_size as f64).log10()
        );
        println!("Prefixes: cfg = {quant:?}, last_exist = {e}, qf = {qf:?}):");
        for (prefix, lemma_qf, literals) in &active_domains {
            println!(
                "    {:?} --- {} literals --- {:?} ~ {}",
                prefix,
                literals.len(),
                lemma_qf,
                lemma_qf.approx_space_size()
            );
        }

        let fixpoint =
            run_qalpha::<E, L, S>(cfg.clone(), solver, m, &cfg.fo, active_domains.clone());

        fixpoint.report(print_invariant);

        if fixpoint.safety_proof.is_some() && cfg.until_safe {
            break;
        }
    }
}

pub fn qalpha_dynamic(cfg: Arc<QalphaConfig>, m: &Module, print_invariant: bool) {
    match (&cfg.qf_cfg.qf_body, cfg.fallback) {
        (QfBody::Cnf, false) => qalpha::<subsume::Cnf, lemma::LemmaCnf, _>(
            cfg.clone(),
            m,
            &parallel_solver(&cfg),
            print_invariant,
        ),
        (QfBody::PDnf, false) => qalpha::<subsume::PDnf, lemma::LemmaPDnf, _>(
            cfg.clone(),
            m,
            &parallel_solver(&cfg),
            print_invariant,
        ),
        (QfBody::Dnf, false) => qalpha::<subsume::Dnf, lemma::LemmaDnf, _>(
            cfg.clone(),
            m,
            &parallel_solver(&cfg),
            print_invariant,
        ),
        (QfBody::PDnfBaseline, false) => qalpha::<
            Baseline<subsume::PDnf>,
            lemma::LemmaPDnfBaseline,
            _,
        >(
            cfg.clone(), m, &parallel_solver(&cfg), print_invariant
        ),
        (QfBody::Cnf, true) => qalpha::<subsume::Cnf, lemma::LemmaCnf, _>(
            cfg.clone(),
            m,
            &fallback_solver(&cfg),
            print_invariant,
        ),
        (QfBody::PDnf, true) => qalpha::<subsume::PDnf, lemma::LemmaPDnf, _>(
            cfg.clone(),
            m,
            &fallback_solver(&cfg),
            print_invariant,
        ),
        (QfBody::Dnf, true) => qalpha::<subsume::Dnf, lemma::LemmaDnf, _>(
            cfg.clone(),
            m,
            &fallback_solver(&cfg),
            print_invariant,
        ),
        (QfBody::PDnfBaseline, true) => qalpha::<
            Baseline<subsume::PDnf>,
            lemma::LemmaPDnfBaseline,
            _,
        >(
            cfg.clone(), m, &fallback_solver(&cfg), print_invariant
        ),
    }
}

/// Run the qalpha algorithm on the configured lemma domains.
fn run_qalpha<E, L, S>(
    cfg: Arc<QalphaConfig>,
    solver: &S,
    m: &Module,
    fo: &FOModule,
    domains: Vec<Domain<L>>,
) -> FoundFixpoint
where
    E: Element,
    L: LemmaQf<Body = E>,
    S: BasicSolver,
{
    let start = std::time::Instant::now();

    let mut frame: InductionFrame<E, L> = InductionFrame::new(
        m,
        m.signature.clone(),
        domains,
        cfg.sim.clone(),
        cfg.strategy.property_directed(),
    );

    // Initialize simulations.
    let mut samples: Tasks<SamplePriority, Model> = frame.initial_samples();
    let mut full_houdini_frame: Option<Vec<Term>> = None;

    // Overapproximate initial states.
    loop {
        let mut ctis = frame.init_cex(fo, solver);
        if ctis.is_empty() {
            break;
        } else if !cfg.strategy.is_weaken() {
            panic!("overapproximation of initial states failed!")
        } else {
            ctis.retain(|cex| frame.see(cex));
            frame.weaken(&ctis);
            for cex in ctis {
                samples.insert(sample_priority(&cfg.sim, &cex.universe, 0).unwrap(), cex);
            }
        }
    }

    frame.finish_initial();

    // Handle transition CTI's.

    let mut run_sim = !samples.is_empty();
    let mut run_smt = cfg.strategy.is_weaken() || (cfg.strategy.is_houdini() && !run_sim);
    while run_sim || run_smt {
        let mut ctis: Vec<Model> = vec![];
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
            for cex in &smt_cti {
                if frame.see(cex) {
                    samples.insert(
                        sample_priority(&cfg.sim, &cex.universe, 0).unwrap(),
                        cex.clone(),
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
                None,
                None,
                None,
                samples.total() - samples.len(),
                samples.total(),
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

    frame.log_info("Checking safety...");
    frame.is_safe(fo, solver, None);
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
        reduced_proof,
        safety_proof,
        covering,
        samples.total() - samples.len(),
        samples.total(),
    )
}

/// Attempt to find a transition CTI for the current frame. If enabled by the configuration, this also checks
/// the safety of the frame and returns `None` if the execution should abort. Otherwise, `Some(_)` is returned
/// which contains a vector of counterexamples.
fn qalpha_cti<E, L, S>(
    cfg: &QalphaConfig,
    solver: &S,
    fo: &FOModule,
    frame: &InductionFrame<'_, E, L>,
    canceler: MultiCanceler<MultiCanceler<S::Canceler>>,
) -> Option<Vec<Model>>
where
    E: Element,
    L: LemmaQf<Body = E>,
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

    Some(frame.trans_cex(fo, solver, canceler))
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Find a fixpoint invariant expressing reachable states in a given
//! lemma domain.

use fly::semantics::Model;
use itertools::Itertools;
use solver::basics::{BasicCanceler, MultiCanceler};
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::sync::Arc;
use std::thread;
use std::time::Duration;

use crate::basics::QfBody;
use crate::{
    basics::{FOModule, QalphaConfig},
    qalpha::{
        atoms::{generate_literals, restrict_by_prefix},
        lemma::{self, InductionFrame},
        subsume::{self, Element},
        weaken::{Domain, LemmaQf},
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
    use super::QfBody;
    pub const MIN_DOMAIN_SIZE: usize = 100;
    pub const DOMAIN_GROWTH_FACTOR: usize = 5;
    pub const MAX_QUANT: usize = 6;
    pub const MAX_SAME_SORT: usize = 3;
    pub const QF_BODY: QfBody = QfBody::PDnf;
    pub const MAX_CLAUSES: Option<usize> = Some(4);
    pub const MAX_CLAUSE_SIZE: Option<usize> = Some(6);
    pub const MAX_CUBES: Option<usize> = Some(6);
    pub const MAX_CUBE_SIZE: Option<usize> = Some(4);
    pub const MAX_NON_UNIT: Option<usize> = Some(3);

    pub const MAX_MODEL_SIZE: usize = 8;
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

/// (ascending sort sizes, simulation depth, depth since weaken)
pub type SamplePriority = (usize, TraversalDepth, usize);

#[derive(Clone)]
pub struct SimulationOptions {
    pub max_size: Option<usize>,
    pub max_depth: Option<usize>,
    pub weaken_guided: bool,
    pub bfs: bool,
}

impl SimulationOptions {
    pub fn sample_priority(
        &self,
        universe: &[usize],
        depth: usize,
        since_weaken: usize,
    ) -> Option<SamplePriority> {
        if !self
            .max_depth
            .is_some_and(|d| depth > d && (!self.weaken_guided || since_weaken > d))
        {
            Some((
                universe.iter().copied().sum(),
                if self.bfs { Bfs(depth) } else { Dfs(depth) },
                since_weaken,
            ))
        } else {
            None
        }
    }
}

pub enum CtiOption {
    None,
    Houdini,
    HoudiniPd,
    Weaken,
    WeakenPd,
}

impl Default for CtiOption {
    fn default() -> Self {
        Self::Weaken
    }
}

impl From<&str> for CtiOption {
    fn from(value: &str) -> Self {
        match value {
            "none" => Self::None,
            "houdini" => Self::Houdini,
            "houdini-pd" => Self::HoudiniPd,
            "weaken" => Self::Weaken,
            "weaken-pd" => Self::WeakenPd,
            _ => panic!("invalid CTI option"),
        }
    }
}

impl CtiOption {
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
    /// Total time for fixpoint calculation
    time_taken: Duration,
    /// Number of terms of handwritten invariant covered by the (reduced) fixpoint result
    /// and total number of terms in the handwritten invariant
    covering: Option<(usize, usize)>,
}

impl FoundFixpoint {
    pub fn report(&self, print_invariant: bool) {
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
            let (covered_handwritten, size_handwritten) = self.covering.unwrap();
            println!("Covers {covered_handwritten} / {size_handwritten} of handwritten invariant.");
        } else {
            println!("Fixpoint NOT reached! frame_size={}", self.proof.len());
        }

        if let Some(safety_proof) = &self.safety_proof {
            println!("Safety VERIFIED! proof_size={}", safety_proof.len());
        } else {
            println!("Safety NOT verified.");
        }

        if print_invariant {
            println!("Runtime = {:.2}s", self.time_taken.as_secs_f64());
            print_inv("frame", self.proof.len(), &self.proof);
            if let Some(reduced_proof) = &self.reduced_proof {
                print_inv("reduced", reduced_proof.len(), reduced_proof);
            }
            if let Some(safety_proof) = &self.safety_proof {
                print_inv("safety", safety_proof.len(), safety_proof);
            }
        }
    }
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

pub fn qalpha<E, L, S>(infer_cfg: Arc<QalphaConfig>, m: &Module, solver: &S, print_invariant: bool)
where
    E: Element,
    L: LemmaQf<Body = E>,
    S: BasicSolver,
{
    let fo = FOModule::new(
        m,
        infer_cfg.disj,
        infer_cfg.gradual_smt,
        infer_cfg.minimal_smt,
    );
    log::debug!("Computing literals...");
    let literals = Arc::new(generate_literals(&infer_cfg, &m.signature, solver, &fo));

    let mut domains: VecDeque<Domain<L>>;
    let mut active_domains: Vec<Domain<L>>;

    let domain_size_of = |doms: &[Domain<L>]| {
        doms.iter()
            .map(|(_, lemma_qf, _)| lemma_qf.approx_space_size())
            .sum()
    };

    log::debug!("Computing predicate domains...");
    if infer_cfg.no_search {
        domains = VecDeque::new();
        active_domains = infer_cfg
            .cfg
            .exact_prefixes(
                0,
                infer_cfg
                    .max_existentials
                    .unwrap_or(infer_cfg.cfg.num_vars()),
                infer_cfg.max_size,
            )
            .into_iter()
            .map(|prefix| {
                let prefix = Arc::new(prefix);
                let restricted = Arc::new(restrict_by_prefix(&literals, &infer_cfg.cfg, &prefix));
                let lemma_qf = Arc::new(L::new(
                    &infer_cfg,
                    restricted.clone(),
                    &prefix.non_universal_vars(),
                ));
                (prefix, lemma_qf, restricted)
            })
            .collect();
    } else {
        domains = infer_cfg
            .cfg
            .all_prefixes(&infer_cfg)
            .into_iter()
            .flat_map(|prefix| {
                let prefix = Arc::new(prefix);
                let restricted = Arc::new(restrict_by_prefix(&literals, &infer_cfg.cfg, &prefix));
                let lemma_qf_full =
                    L::new(&infer_cfg, restricted.clone(), &prefix.non_universal_vars());
                lemma_qf_full
                    .sub_spaces()
                    .into_iter()
                    .map(move |lemma_qf| (prefix.clone(), Arc::new(lemma_qf), restricted.clone()))
            })
            .filter(|(_, lemma_qf, _)| lemma_qf.approx_space_size() > 1)
            .sorted_by_key(|(p, lemma_qf, _)| (lemma_qf.approx_space_size(), p.existentials()))
            .collect();
        active_domains = vec![];
    }

    println!(
        "Number of individual domains: {}",
        domains.len() + active_domains.len()
    );

    let mut domain_size: usize = domain_size_of(&active_domains);
    let mut next_domain_size = defaults::MIN_DOMAIN_SIZE;
    let mut iteration: usize = 1;
    loop {
        while !domains.is_empty() && domain_size < next_domain_size {
            let dom = domains.pop_front().unwrap();
            active_domains.retain(|d| !(dom.0.contains(&d.0) && dom.1.contains(&d.1)));
            active_domains.push(dom);
            domain_size = domain_size_of(&active_domains);
        }

        println!();
        println!("({iteration}) Running qalpha algorithm...");
        println!(
            "Approximate domain size: 10^{:.2} ({domain_size})",
            (domain_size as f64).log10()
        );
        println!("Prefixes:");
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
            run_qalpha::<E, L, S>(infer_cfg.clone(), solver, m, &fo, active_domains.clone());

        fixpoint.report(print_invariant);

        if (fixpoint.safety_proof.is_some() && infer_cfg.until_safe) || domains.is_empty() {
            break;
        }

        iteration += 1;
        next_domain_size = domain_size
            * infer_cfg
                .growth_factor
                .unwrap_or(defaults::DOMAIN_GROWTH_FACTOR);
    }
}

pub fn qalpha_dynamic(infer_cfg: Arc<QalphaConfig>, m: &Module, print_invariant: bool) {
    match (&infer_cfg.qf_body, infer_cfg.fallback) {
        (QfBody::CNF, false) => qalpha::<subsume::Cnf, lemma::LemmaCnf, _>(
            infer_cfg.clone(),
            m,
            &parallel_solver(&infer_cfg),
            print_invariant,
        ),
        (QfBody::PDnf, false) => qalpha::<subsume::PDnf, lemma::LemmaPDnf, _>(
            infer_cfg.clone(),
            m,
            &parallel_solver(&infer_cfg),
            print_invariant,
        ),
        (QfBody::Dnf, false) => qalpha::<subsume::Dnf, lemma::LemmaDnf, _>(
            infer_cfg.clone(),
            m,
            &parallel_solver(&infer_cfg),
            print_invariant,
        ),
        (QfBody::CNF, true) => qalpha::<subsume::Cnf, lemma::LemmaCnf, _>(
            infer_cfg.clone(),
            m,
            &fallback_solver(&infer_cfg),
            print_invariant,
        ),
        (QfBody::PDnf, true) => qalpha::<subsume::PDnf, lemma::LemmaPDnf, _>(
            infer_cfg.clone(),
            m,
            &fallback_solver(&infer_cfg),
            print_invariant,
        ),
        (QfBody::Dnf, true) => qalpha::<subsume::Dnf, lemma::LemmaDnf, _>(
            infer_cfg.clone(),
            m,
            &fallback_solver(&infer_cfg),
            print_invariant,
        ),
    }
}

/// Run the qalpha algorithm on the configured lemma domains.
fn run_qalpha<E, L, S>(
    infer_cfg: Arc<QalphaConfig>,
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
        infer_cfg.sim_options.clone(),
        infer_cfg.cti_option.property_directed(),
    );
    let cti_option = &infer_cfg.cti_option;
    let sim_options = &infer_cfg.sim_options;

    // Initialize simulations.
    let mut samples = frame.initial_samples();

    // Overapproximate initial states.
    loop {
        let mut ctis = frame.init_cex(fo, solver);
        if ctis.is_empty() {
            break;
        } else if !cti_option.is_weaken() {
            panic!("overapproximation of initial states failed!")
        } else {
            ctis.retain(|cex| frame.see(cex));
            frame.weaken(&ctis);
            for cex in ctis {
                samples.insert(
                    sim_options.sample_priority(&cex.universe, 0, 0).unwrap(),
                    cex,
                );
            }
        }
    }

    frame.finish_initial();

    // Handle transition CTI's.

    let mut run_sim = !samples.is_empty();
    let mut run_smt = cti_option.is_weaken() || (cti_option.is_houdini() && !run_sim);
    while run_sim || run_smt {
        let mut ctis: Vec<Model> = vec![];
        let canceler = MultiCanceler::new();
        // Get new samples and CTI's, and if enable, check the safety of the frame.
        let not_safe = thread::scope(|s| {
            let smt_handle = s.spawn(|| {
                if run_smt {
                    qalpha_cti(&infer_cfg, solver, fo, &frame, canceler.clone())
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
                        sim_options.sample_priority(&cex.universe, 0, 0).unwrap(),
                        cex.clone(),
                    );
                }
            }
            ctis.extend(smt_cti);

            false
        });

        if not_safe {
            return FoundFixpoint {
                proof: frame.proof(),
                reduced_proof: None,
                safety_proof: None,
                time_taken: start.elapsed(),
                covering: None,
            };
        }

        if run_sim {
            frame.log_info(format!(
                "{} samples remaining (out of {})",
                samples.len(),
                samples.total()
            ));
        }

        if infer_cfg.cti_option.is_houdini() && run_smt {
            frame.remove_unsat(&ctis);
        } else {
            frame.weaken(&ctis);
        }

        // There cannot be 0 CTI's but more samples to check.
        assert!(!ctis.is_empty() || samples.is_empty());
        run_sim = !samples.is_empty();
        run_smt = if cti_option.is_weaken() {
            !ctis.is_empty()
        } else if cti_option.is_houdini() {
            (!run_smt && ctis.is_empty()) || (run_smt && !ctis.is_empty())
        } else {
            false
        }
    }

    frame.log_info("Checking safety...");
    frame.is_safe(fo, solver);
    let time_taken = start.elapsed();
    let proof = frame.proof();
    let reduced_proof = frame.reduced_proof();
    let safety_proof = frame.safety_proof();
    let covering = reduced_proof
        .as_ref()
        .map(|reduced| invariant_cover(m, solver, fo, reduced));

    FoundFixpoint {
        proof,
        reduced_proof,
        safety_proof,
        time_taken,
        covering,
    }
}

/// Attempt to find a transition CTI for the current frame. If enabled by the configuration, this also checks
/// the safety of the frame and returns `None` if the execution should abort. Otherwise, `Some(_)` is returned
/// which contains a vector of counterexamples.
fn qalpha_cti<E, L, S>(
    infer_cfg: &QalphaConfig,
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

    if infer_cfg.cti_option.property_directed() {
        frame.log_info("Checking safety...");
        if !frame.is_safe(fo, solver) {
            return None;
        }
        frame.log_info("Safety verified.");
    }

    if !canceler.is_canceled() {
        Some(frame.trans_cex(fo, solver, canceler))
    } else {
        Some(vec![])
    }
}

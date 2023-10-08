// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Find a fixpoint invariant expressing reachable states in a given
//! lemma domain.

use itertools::Itertools;
use std::collections::VecDeque;
use std::sync::Arc;
use std::time::Duration;

use crate::basics::QfBody;
use crate::{
    basics::{FOModule, InferenceConfig},
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

fn parallel_solver(infer_cfg: &InferenceConfig) -> impl BasicSolver {
    ParallelSolvers::new(vec![
        SolverConf::new(SolverType::Z3, true, &infer_cfg.fname, 0, 0),
        SolverConf::new(SolverType::Cvc5, true, &infer_cfg.fname, 0, 0),
    ])
}

fn fallback_solver(infer_cfg: &InferenceConfig) -> impl BasicSolver {
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

pub fn qalpha<E, L, S1>(
    infer_cfg: Arc<InferenceConfig>,
    m: &Module,
    main_solver: &S1,
    print_invariant: bool,
) where
    E: Element,
    L: LemmaQf<Body = E>,
    S1: BasicSolver,
{
    let fo = FOModule::new(
        m,
        infer_cfg.disj,
        infer_cfg.gradual_smt,
        infer_cfg.minimal_smt,
    );
    log::debug!("Computing literals...");
    let literals = Arc::new(generate_literals(
        &infer_cfg,
        &m.signature,
        main_solver,
        &fo,
    ));
    let extend = match (infer_cfg.extend_width, infer_cfg.extend_depth) {
        (None, None) => None,
        (Some(width), Some(depth)) => Some((width, depth)),
        (_, _) => panic!("Only one of extend-width and extend-depth is specified."),
    };

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

        let fixpoint = run_qalpha::<E, L, S1>(
            infer_cfg.clone(),
            main_solver,
            m,
            &fo,
            active_domains.clone(),
            extend,
        );

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

pub fn qalpha_dynamic(infer_cfg: Arc<InferenceConfig>, m: &Module, print_invariant: bool) {
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
fn run_qalpha<E, L, S1>(
    infer_cfg: Arc<InferenceConfig>,
    main_solver: &S1,
    m: &Module,
    fo: &FOModule,
    domains: Vec<Domain<L>>,
    extend: Option<(usize, usize)>,
) -> FoundFixpoint
where
    E: Element,
    L: LemmaQf<Body = E>,
    S1: BasicSolver,
{
    let start = std::time::Instant::now();

    log::debug!("Axioms:");
    for a in fo.module.axioms.iter() {
        log::debug!("    {a}");
    }
    log::debug!("Initial states:");
    for a in fo.module.inits.iter() {
        log::debug!("    {a}");
    }
    log::debug!("Transitions:");
    for a in fo.module.transitions.iter() {
        log::debug!("    {a}");
    }

    let signature = Arc::new(m.signature.clone());
    let mut frame: InductionFrame<E, L> = InductionFrame::new(
        infer_cfg.clone(),
        signature,
        domains,
        extend,
        infer_cfg.property_directed,
    );

    // Begin by overapproximating the initial states.
    while frame.init_cycle(fo, main_solver) {}

    frame.clear_blocked();

    // Handle transition CTI's.
    loop {
        // If enabled, extend CTI traces using simulations.
        if extend.is_some() {
            frame.extend(m);
        }

        if infer_cfg.abort_unsafe {
            frame.log_info("Checking safety...");
            if !frame.is_safe(fo, main_solver) {
                return FoundFixpoint {
                    proof: frame.proof(),
                    reduced_proof: None,
                    safety_proof: None,
                    time_taken: start.elapsed(),
                    covering: None,
                };
            }
        }

        if !frame.trans_cycle(fo, main_solver) {
            break;
        }
    }

    frame.log_info("Checking safety...");
    frame.is_safe(fo, main_solver);
    let time_taken = start.elapsed();
    let proof = frame.proof();
    let reduced_proof = frame.reduced_proof();
    let safety_proof = frame.safety_proof();
    let covering = reduced_proof
        .as_ref()
        .map(|reduced| invariant_cover(m, main_solver, fo, reduced));

    FoundFixpoint {
        proof,
        reduced_proof,
        safety_proof,
        time_taken,
        covering,
    }
}

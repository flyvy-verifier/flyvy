// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Find a fixpoint invariant expressing reachable states in a given
//! lemma domain.

use fly::semantics::Model;
use itertools::Itertools;
use solver::basics::{BasicSolverCanceler, SolverCancelers};
use std::collections::VecDeque;
use std::sync::Arc;
use std::thread;
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

    pub const MAX_SORT_SIZE: usize = 3;
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

pub fn qalpha<E, L, S>(
    infer_cfg: Arc<InferenceConfig>,
    m: &Module,
    solver: &S,
    print_invariant: bool,
) where
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
fn run_qalpha<E, L, S>(
    infer_cfg: Arc<InferenceConfig>,
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
        infer_cfg.extend_depth,
        infer_cfg.property_directed,
    );

    let mut samples = VecDeque::new();

    // Begin by overapproximating the initial states.
    let mut initial_samples: VecDeque<Vec<(Model, usize)>> =
        frame.initial_samples(defaults::MAX_SORT_SIZE).collect();
    frame.log_info(format!("Sampled {} initial samples.", samples.len()));
    initial_samples
        .iter()
        .flatten()
        .for_each(|(model, _)| frame.weaken(model));
    frame.update();
    loop {
        frame.log_info("Finding initial CTI...");
        let ctis = frame.init_cex(fo, solver);
        if ctis.is_empty() {
            break;
        }
        frame.log_info(format!("{} initial CTI(s) found.", ctis.len()));
        for cex in ctis {
            frame.weaken(&cex);
            samples.insert(0, (cex, 0));
        }
        frame.update();
    }

    frame.log_info("No initial CTI found.");

    frame.clear_blocked();

    // Handle transition CTI's.
    loop {
        if infer_cfg.abort_unsafe || infer_cfg.property_directed {
            frame.log_info("Checking safety...");
            if !frame.is_safe(fo, solver) {
                return FoundFixpoint {
                    proof: frame.proof(),
                    reduced_proof: None,
                    safety_proof: None,
                    time_taken: start.elapsed(),
                    covering: None,
                };
            }
        }

        frame.log_info("Finding transition CTI...");
        let mut unsat: Vec<Model> = vec![];
        let canceler = SolverCancelers::new();
        thread::scope(|s| {
            let smt_handle = s.spawn(|| frame.trans_cex(fo, solver, canceler.clone()));
            let mut models;
            let mut remaining;
            loop {
                (models, remaining) = frame.extend(canceler.clone(), samples.drain(..));
                if canceler.is_canceled() || initial_samples.is_empty() {
                    break;
                }
                assert!(models.is_empty() && remaining.is_empty());
                samples.extend(initial_samples.pop_front().unwrap());
            }
            let smt_result: Vec<Model> = smt_handle.join().unwrap();

            unsat = smt_result.clone();
            unsat.append(&mut models);
            samples.extend(smt_result.into_iter().map(|model| (model, 0)));
            samples.append(&mut remaining);
        });

        frame.log_info(format!(
            "{} transition CTI(s) found, {} samples remaining",
            unsat.len(),
            samples.len()
        ));

        if unsat.is_empty() {
            break;
        }

        for model in &unsat {
            frame.weaken(model);
        }

        frame.update();
    }

    frame.log_info("No transition CTI found.");

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

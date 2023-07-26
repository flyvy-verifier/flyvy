// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Find a fixpoint invariant expressing reachable states in a given
//! lemma domain.

use itertools::Itertools;
use std::sync::Arc;
use std::time::Duration;
use std::{collections::VecDeque, fmt::Debug};

use crate::basics::QfBody;
use crate::{atoms, lemma, subsume};
use crate::{
    atoms::{restrict, restrict_by_prefix, Atoms, RestrictedAtoms},
    basics::{FOModule, InferenceConfig},
    lemma::InductionFrame,
    subsume::OrderSubsumption,
    weaken::{Domain, LemmaQf},
};
use fly::syntax::{Module, Term, ThmStmt};
use solver::conf::SolverConf;

use rayon::prelude::*;

pub mod defaults {
    use super::QfBody;
    pub const MIN_DOMAIN_SIZE: usize = 100;
    pub const DOMAIN_GROWTH_FACTOR: usize = 5;
    pub const MAX_QUANT: usize = 6;
    pub const MAX_SAME_SORT: usize = 3;
    pub const QF_BODY: QfBody = QfBody::PDnf;
    pub const MAX_CLAUSES: Option<usize> = None;
    pub const MAX_CLAUSE_SIZE: Option<usize> = None;
    pub const MAX_CUBES: Option<usize> = Some(6);
    pub const MAX_CUBE_SIZE: Option<usize> = Some(4);
    pub const MAX_NON_UNIT: Option<usize> = Some(3);
}

/// Check how much of the handwritten invariant the given lemmas cover.
fn invariant_cover(
    m: &Module,
    conf: &SolverConf,
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
        .filter(|inv| fo.implication_cex(conf, lemmas, &inv.x).is_none())
        .count();

    (covered, proof.invariants.len())
}

/// An inductive fixpoint
pub struct FoundFixpoint {
    /// The fixpoint term (the conjunction of these lemmas).
    /// If `None`, the run has been abort before reaching the fixpoint
    proof: Option<Vec<Term>>,
    /// A subset of the fixpoint term which suffices to prove safety
    minimized_proof: Option<Vec<Term>>,
    /// Whether the discovered fixpoint implies the safety predicates
    safe: bool,
    /// Total time for fixpoint calculation
    time_taken: Duration,
    /// Number of terms of handwritten invariant covered
    /// and total number of terms in the handwritten invariant
    covering: Option<(usize, usize)>,
}

impl FoundFixpoint {
    pub fn report(&self, print_invariant: bool) {
        let print_inv = |inv: &[Term]| {
            println!("proof {{");
            for lemma in inv {
                println!("  invariant {lemma}");
            }
            println!("}}");
        };

        if self.safe {
            println!("Fixpoint SAFE!");
        } else {
            println!("Fixpoint UNSAFE!");
        }

        if let Some(proof) = &self.proof {
            println!("Fixpoint size = {}", proof.len());
            if let Some((covered_handwritten, size_handwritten)) = self.covering {
                println!(
                    "Covers {covered_handwritten} / {size_handwritten} of handwritten invariant."
                );
            }

            if print_invariant {
                println!("Fixpoint runtime = {:.2}s", self.time_taken.as_secs_f64());
                print_inv(proof);
                if let Some(minimized_proof) = &self.minimized_proof {
                    println!("Safety invariant size = {}", minimized_proof.len());
                    print_inv(minimized_proof);
                }
            }
        }
    }
}

pub fn qalpha<O, L, B>(
    infer_cfg: InferenceConfig,
    conf: &SolverConf,
    m: &Module,
    print_invariant: bool,
) where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
{
    let fo = FOModule::new(
        m,
        infer_cfg.disj,
        infer_cfg.gradual_smt,
        infer_cfg.minimal_smt,
    );
    let atoms = Arc::new(Atoms::new(&infer_cfg, conf, &fo));
    let unrestricted = Arc::new(restrict(&atoms, |_| true));
    let infer_cfg = Arc::new(infer_cfg);
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
                let restricted = Arc::new(restrict_by_prefix(&atoms, &infer_cfg.cfg, &prefix));
                let lemma_qf = Arc::new(L::new(
                    &infer_cfg,
                    restricted.clone(),
                    prefix.non_universal_vars(),
                ));
                (prefix, lemma_qf, restricted)
            })
            .collect_vec();
    } else {
        domains = infer_cfg
            .cfg
            .all_prefixes(&infer_cfg)
            .into_iter()
            .flat_map(|prefix| {
                let prefix = Arc::new(prefix);
                let restricted = Arc::new(restrict_by_prefix(&atoms, &infer_cfg.cfg, &prefix));
                let lemma_qf_full =
                    L::new(&infer_cfg, restricted.clone(), prefix.non_universal_vars());
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
        for (prefix, lemma_qf, atoms) in &active_domains {
            println!(
                "    {:?} --- {} atoms --- {:?} ~ {}",
                prefix,
                atoms.len(),
                lemma_qf,
                lemma_qf.approx_space_size()
            );
        }

        let fixpoint = run_qalpha::<O, L, B>(
            infer_cfg.clone(),
            conf,
            m,
            &fo,
            unrestricted.clone(),
            active_domains.clone(),
            extend,
        );

        fixpoint.report(print_invariant);

        if (fixpoint.safe && infer_cfg.until_safe) || domains.is_empty() {
            break;
        }

        iteration += 1;
        next_domain_size = domain_size
            * infer_cfg
                .growth_factor
                .unwrap_or(defaults::DOMAIN_GROWTH_FACTOR);
    }
}

pub fn qalpha_by_qf_body(
    infer_cfg: InferenceConfig,
    conf: &SolverConf,
    m: &Module,
    print_invariant: bool,
) {
    match infer_cfg.qf_body {
        QfBody::CNF => qalpha::<
            subsume::Cnf<atoms::Literal>,
            lemma::LemmaCnf,
            Vec<Vec<atoms::Literal>>,
        >(infer_cfg, conf, m, print_invariant),
        QfBody::PDnf => qalpha::<
            subsume::PDnf<atoms::Literal>,
            lemma::LemmaPDnf,
            (Vec<atoms::Literal>, Vec<Vec<atoms::Literal>>),
        >(infer_cfg, conf, m, print_invariant),
        QfBody::PDnfNaive => qalpha::<
            subsume::Dnf<atoms::Literal>,
            lemma::LemmaPDnfNaive,
            Vec<Vec<atoms::Literal>>,
        >(infer_cfg, conf, m, print_invariant),
    }
}

/// Run the qalpha algorithm on the configured lemma domains.
fn run_qalpha<O, L, B>(
    infer_cfg: Arc<InferenceConfig>,
    conf: &SolverConf,
    m: &Module,
    fo: &FOModule,
    atoms: Arc<RestrictedAtoms>,
    domains: Vec<Domain<L>>,
    extend: Option<(usize, usize)>,
) -> FoundFixpoint
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
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

    let mut frame: InductionFrame<O, L, B> =
        InductionFrame::new(infer_cfg.clone(), atoms, domains, extend);

    // Begin by overapproximating the initial states.
    while frame.init_cycle(fo, conf) {}

    // Handle transition CTI's.
    loop {
        // If enabled, extend CTI traces using simulations.
        if extend.is_some() {
            frame.extend(fo, conf);
        }

        if infer_cfg.abort_unsafe {
            frame.log_info("Checking safety...");
            if !frame.is_safe(fo, conf) {
                return FoundFixpoint {
                    proof: None,
                    minimized_proof: None,
                    safe: false,
                    time_taken: start.elapsed(),
                    covering: None,
                };
            }
        }

        if !frame.trans_cycle(fo, conf) {
            break;
        }
    }

    frame.log_info("Checking safety...");
    let safe = frame.is_safe(fo, conf);
    let time_taken = start.elapsed();
    let proof: Vec<Term> = frame.proof();
    let minimized_proof = frame.minimized_proof();
    let covering = Some(invariant_cover(m, conf, fo, &proof));

    FoundFixpoint {
        proof: Some(proof),
        minimized_proof,
        safe,
        time_taken,
        covering,
    }
}

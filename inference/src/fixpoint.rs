// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Find a fixpoint invariant expressing reachable states in a given
//! lemma domain.

use std::sync::Arc;
use std::time::Duration;
use std::{collections::VecDeque, fmt::Debug};

use itertools::Itertools;

use crate::basics::QfBody;
use crate::{atoms, lemma, subsume};
use crate::{
    atoms::{restrict, restrict_by_prefix, Atoms, RestrictedAtoms},
    basics::{FOModule, InferenceConfig},
    lemma::{Frontier, IndividualLemmaSearch},
    quant::QuantifierPrefix,
    subsume::OrderSubsumption,
    weaken::{LemmaQf, LemmaSet, WeakenLemmaSet},
};
use fly::syntax::{Module, Term, ThmStmt};
use solver::conf::SolverConf;

use rayon::prelude::*;

type Domain<L> = (Arc<QuantifierPrefix>, Arc<L>, Arc<RestrictedAtoms>);

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
    /// The fixpoint term (the conjunction of these lemmas)
    pub proof: Vec<Term>,
    /// Whether the discovered fixpoint implies the safety predicates
    pub safe: bool,
    /// Total time for fixpoint calculation
    pub time_taken: Duration,
    /// Number of terms of handwritten invariant covered
    pub covered_handwritten: usize,
    /// Total number of terms in the handwritten invariant
    pub size_handwritten: usize,
}

pub fn fixpoint_single<O, L, B>(
    infer_cfg: InferenceConfig,
    conf: &SolverConf,
    m: &Module,
) -> FoundFixpoint
where
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
    let domains: Vec<Domain<L>> = infer_cfg
        .cfg
        .exact_prefixes(
            0,
            infer_cfg.max_existentials.unwrap_or(infer_cfg.cfg.len()),
            infer_cfg.max_size.unwrap_or(infer_cfg.cfg.num_vars()),
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
    let infer_cfg = Arc::new(infer_cfg);
    let extend = match (infer_cfg.extend_width, infer_cfg.extend_depth) {
        (None, None) => None,
        (Some(width), Some(depth)) => Some((width, depth)),
        (_, _) => panic!("Only one of extend-width and extend-depth is specified."),
    };

    log::info!("Running fixpoint algorithm...");
    let total_preds: usize = domains
        .iter()
        .map(|(_, lemma_qf, _)| lemma_qf.approx_space_size())
        .sum();
    log::info!("    Approximate domain size: {}", total_preds);
    log::info!("    Prefixes:");
    for (prefix, lemma_qf, _) in &domains {
        log::info!("        {:?} ~ {}", prefix, lemma_qf.approx_space_size());
    }

    let start = std::time::Instant::now();

    let fixpoint = if infer_cfg.indiv {
        run_individual::<O, L, B>(infer_cfg, conf, &fo, unrestricted, domains, extend).unwrap()
    } else {
        run_fixpoint::<O, L, B>(infer_cfg, conf, &fo, unrestricted, domains, extend).unwrap()
    };
    let time_taken = start.elapsed();
    let proof = fixpoint.to_terms();
    let safe = fo.trans_safe_cex(conf, &proof).is_none();
    let (covered, size) = invariant_cover(m, conf, &fo, &proof);

    FoundFixpoint {
        proof,
        safe,
        time_taken,
        covered_handwritten: covered,
        size_handwritten: size,
    }
}

pub fn fixpoint_single_qf_body(
    infer_cfg: InferenceConfig,
    conf: &SolverConf,
    m: &Module,
) -> FoundFixpoint {
    match infer_cfg.qf_body {
        QfBody::CNF => {
            fixpoint_single::<subsume::Cnf<atoms::Literal>, lemma::LemmaCnf, Vec<Vec<atoms::Literal>>>(
                infer_cfg, conf, m,
            )
        }
        QfBody::PDnf => fixpoint_single::<
            subsume::PDnf<atoms::Literal>,
            lemma::LemmaPDnf,
            (Vec<atoms::Literal>, Vec<Vec<atoms::Literal>>),
        >(infer_cfg, conf, m),
        QfBody::PDnfNaive => fixpoint_single::<
            subsume::Dnf<atoms::Literal>,
            lemma::LemmaPDnfNaive,
            Vec<Vec<atoms::Literal>>,
        >(infer_cfg, conf, m),
    }
}

impl FoundFixpoint {
    pub fn report(&self) {
        println!("proof {{");
        for lemma in &self.proof {
            println!("  invariant {lemma}");
        }
        println!("}}");

        if self.safe {
            println!("Fixpoint SAFE!");
        } else {
            println!("Fixpoint UNSAFE!");
        }

        println!("Fixpoint size = {}", self.proof.len());
        println!("Fixpoint runtime = {:.2}s", self.time_taken.as_secs_f64());
        println!(
            "Covers {} / {} of handwritten invariant.",
            self.covered_handwritten, self.size_handwritten
        );
    }

    pub fn test_report(&self) {
        if self.safe {
            println!("Fixpoint SAFE!");
        } else {
            println!("Fixpoint UNSAFE!");
        }

        println!("Fixpoint size = {}", self.proof.len());
        println!(
            "Covers {} / {} of handwritten invariant.",
            self.covered_handwritten, self.size_handwritten
        );
    }
}

pub fn fixpoint_multi<O, L, B>(infer_cfg: InferenceConfig, conf: &SolverConf, m: &Module)
where
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
    let domains: Vec<Domain<L>> = infer_cfg
        .cfg
        .all_prefixes(&infer_cfg)
        .into_iter()
        .flat_map(|prefix| {
            let prefix = Arc::new(prefix);
            let restricted = Arc::new(restrict_by_prefix(&atoms, &infer_cfg.cfg, &prefix));
            let lemma_qf_full = L::new(&infer_cfg, restricted.clone(), prefix.non_universal_vars());
            lemma_qf_full
                .sub_spaces()
                .into_iter()
                .map(move |lemma_qf| (prefix.clone(), Arc::new(lemma_qf), restricted.clone()))
        })
        .sorted_by_key(|(p, lemma_qf, _)| (p.existentials(), lemma_qf.approx_space_size()))
        .collect_vec();
    let infer_cfg = Arc::new(infer_cfg);
    let extend = match (infer_cfg.extend_width, infer_cfg.extend_depth) {
        (None, None) => None,
        (Some(width), Some(depth)) => Some((width, depth)),
        (_, _) => panic!("Only one of extend-width and extend-depth is specified."),
    };

    log::info!("Number of individual domains: {}", domains.len());

    let mut active_domains: Vec<Domain<L>> = vec![];
    for (i, dom) in domains.iter().enumerate() {
        active_domains.retain(|d| !(dom.0.contains(&d.0) && dom.1.contains(&d.1)));
        active_domains.push(dom.clone());

        log::info!("");
        log::info!("({}) Running fixpoint algorithm...", i + 1);
        let total_preds: usize = active_domains
            .iter()
            .map(|(_, lemma_qf, _)| lemma_qf.approx_space_size())
            .sum();
        log::info!("    Approximate domain size: {}", total_preds);
        log::info!("    Prefixes:");
        for (prefix, lemma_qf, _) in &active_domains {
            log::info!("        {:?} ~ {}", prefix, lemma_qf.approx_space_size());
        }

        let start = std::time::Instant::now();
        let fixpoint = run_fixpoint::<O, L, B>(
            infer_cfg.clone(),
            conf,
            &fo,
            unrestricted.clone(),
            active_domains.clone(),
            extend,
        )
        .unwrap();
        let total_time = start.elapsed().as_secs_f32();
        let proof = fixpoint.to_terms();
        if fo.trans_safe_cex(conf, &proof).is_none() {
            println!("({}) Fixpoint SAFE!", i + 1);
        } else {
            println!("({}) Fixpoint UNSAFE!", i + 1);
        }

        let (covered, size) = invariant_cover(m, conf, &fo, &proof);

        println!("    Fixpoint size = {}", proof.len());
        println!("    Fixpoint runtime = {:.2}s", total_time);
        println!("    Covers {covered} / {size} of handwritten invariant.");
    }

    println!();
}

pub fn fixpoint_multi_qf_body(infer_cfg: InferenceConfig, conf: &SolverConf, m: &Module) {
    match infer_cfg.qf_body {
        QfBody::CNF => {
            fixpoint_multi::<subsume::Cnf<atoms::Literal>, lemma::LemmaCnf, Vec<Vec<atoms::Literal>>>(
                infer_cfg, conf, m,
            )
        }
        QfBody::PDnf => fixpoint_multi::<
            subsume::PDnf<atoms::Literal>,
            lemma::LemmaPDnf,
            (Vec<atoms::Literal>, Vec<Vec<atoms::Literal>>),
        >(infer_cfg, conf, m),
        QfBody::PDnfNaive => fixpoint_multi::<
            subsume::Dnf<atoms::Literal>,
            lemma::LemmaPDnfNaive,
            Vec<Vec<atoms::Literal>>,
        >(infer_cfg, conf, m),
    }
}

/// Run a simple fixpoint algorithm on the configured lemma domains.
fn run_fixpoint<O, L, B>(
    infer_cfg: Arc<InferenceConfig>,
    conf: &SolverConf,
    fo: &FOModule,
    atoms: Arc<RestrictedAtoms>,
    domains: Vec<Domain<L>>,
    extend: Option<(usize, usize)>,
) -> Option<LemmaSet<O, L, B>>
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
{
    let start = std::time::Instant::now();

    log::debug!("Axioms:");
    for a in fo.axioms.iter() {
        log::debug!("    {a}");
    }
    log::debug!("Initial states:");
    for a in fo.inits.iter() {
        log::debug!("    {a}");
    }
    log::debug!("Transitions:");
    for a in fo.transitions.iter() {
        log::debug!("    {a}");
    }

    let print = |f: &Frontier<O, L, B>, wls: &WeakenLemmaSet<O, L, B>, s: String| {
        log::info!(
            "[{:.2}s] [{} | {}] {}",
            start.elapsed().as_secs_f32(),
            f.len(),
            wls.len(),
            s
        );
    };

    let mut weaken_set: WeakenLemmaSet<O, L, B> = WeakenLemmaSet::new(
        Arc::new(infer_cfg.cfg.clone()),
        infer_cfg.clone(),
        atoms,
        domains,
    );
    weaken_set.init();
    let mut frontier: Frontier<O, L, B> =
        Frontier::new(weaken_set.minimized(), infer_cfg.gradual_advance, extend);

    // Begin by overapproximating the initial states.
    print(&frontier, &weaken_set, "Finding CTI...".to_string());
    while let Some(cti) = frontier.init_cex(fo, conf, &weaken_set) {
        print(
            &frontier,
            &weaken_set,
            "CTI found, type=initial".to_string(),
        );

        print(&frontier, &weaken_set, "Weakening...".to_string());
        weaken_set.weaken(&cti);

        print(&frontier, &weaken_set, "Finding CTI...".to_string());
    }

    print(&frontier, &weaken_set, "Advancing...".to_string());
    while frontier.advance(&weaken_set, true) {
        // If enabled, extend CTI traces.
        if extend.is_some() {
            frontier.extend(fo, conf, &mut weaken_set);
            print(&frontier, &weaken_set, "Advancing...".to_string());
            frontier.advance(&weaken_set, false);
        }

        // Handle transition CTI's.
        print(&frontier, &weaken_set, "Finding CTI...".to_string());
        while let Some(cti) = frontier.trans_cex(fo, conf, &weaken_set) {
            print(
                &frontier,
                &weaken_set,
                "CTI found, type=transition".to_string(),
            );

            print(&frontier, &weaken_set, "Weakening...".to_string());
            weaken_set.weaken(&cti);

            // If enabled, extend CTI traces.
            if extend.is_some() {
                frontier.extend(fo, conf, &mut weaken_set);
            }

            print(&frontier, &weaken_set, "Advancing...".to_string());
            frontier.advance(&weaken_set, false);

            print(&frontier, &weaken_set, "Finding CTI...".to_string());
        }

        print(&frontier, &weaken_set, "Advancing...".to_string());
    }

    Some(weaken_set.minimized())
}

/// Run a simple fixpoint algorithm on the configured lemma domains.
fn run_individual<O, L, B>(
    infer_cfg: Arc<InferenceConfig>,
    conf: &SolverConf,
    fo: &FOModule,
    atoms: Arc<RestrictedAtoms>,
    domains: Vec<Domain<L>>,
    extend: Option<(usize, usize)>,
) -> Option<LemmaSet<O, L, B>>
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
{
    let start = std::time::Instant::now();

    log::debug!("Axioms:");
    for a in fo.axioms.iter() {
        log::debug!("    {a}");
    }
    log::debug!("Initial states:");
    for a in fo.inits.iter() {
        log::debug!("    {a}");
    }
    log::debug!("Transitions:");
    for a in fo.transitions.iter() {
        log::debug!("    {a}");
    }

    let print = |search: &IndividualLemmaSearch<O, L, B>, s: String| {
        let len = search.len();
        log::info!(
            "[{:.2}s] [{} | {}] {}",
            start.elapsed().as_secs_f32(),
            len.1,
            len.0,
            s
        );
    };

    let config = Arc::new(infer_cfg.cfg.clone());
    let mut weaken_set: WeakenLemmaSet<O, L, B> =
        WeakenLemmaSet::new(config.clone(), infer_cfg.clone(), atoms.clone(), domains);
    weaken_set.init();
    let empty: LemmaSet<O, L, B> = LemmaSet::new(config, &infer_cfg, atoms);
    let mut individual_search = IndividualLemmaSearch {
        weaken_set,
        initial: empty.clone(),
        inductive: empty,
        extend,
        ctis: VecDeque::new(),
    };

    // Begin by overapproximating the initial states.
    print(&individual_search, "Initiation cycle...".to_string());
    while individual_search.init_cycle(fo, conf) {
        print(&individual_search, "Initiation cycle...".to_string());
    }
    print(
        &individual_search,
        "Initiation cycles complete.".to_string(),
    );

    loop {
        print(&individual_search, "Extending CTI traces...".to_string());
        if extend.is_some() {
            individual_search.extend(fo, conf);
        }
        print(&individual_search, "Transition cycle...".to_string());
        if !individual_search.trans_cycle(fo, conf) {
            break;
        }
    }
    print(
        &individual_search,
        "Transition cycles complete.".to_string(),
    );

    Some(individual_search.inductive)
}

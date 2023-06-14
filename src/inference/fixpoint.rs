// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Find a fixpoint invariant expressing reachable states in a given
//! lemma domain.

use std::sync::Arc;
use std::{collections::VecDeque, fmt::Debug};

use itertools::Itertools;

use crate::{
    fly::syntax::{Module, Term, ThmStmt},
    inference::{
        atoms::{restrict, restrict_by_prefix, Atoms, RestrictedAtoms},
        basics::{FOModule, InferenceConfig},
        lemma::{Frontier, IndividualLemmaSearch},
        quant::QuantifierPrefix,
        subsume::OrderSubsumption,
        weaken::{LemmaQf, LemmaSet, WeakenLemmaSet},
    },
    verify::SolverConf,
};

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

/// Check how many of the given lemmas are trivial, i.e. valid given the axioms.
fn count_trivial(conf: &SolverConf, fo: &FOModule, lemmas: &[Term]) -> usize {
    lemmas
        .par_iter()
        .filter(|t| fo.implication_cex(conf, &[], t).is_none())
        .count()
}

pub fn fixpoint_single<O, L, B>(infer_cfg: InferenceConfig, conf: &SolverConf, m: &Module)
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
{
    let atoms = Arc::new(Atoms::new(
        infer_cfg.cfg.atoms(infer_cfg.nesting, infer_cfg.include_eq),
    ));
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
            let restricted = Arc::new(restrict_by_prefix(&atoms, &infer_cfg.cfg, &prefix));
            let lemma_qf = Arc::new(L::new(
                &infer_cfg,
                restricted.clone(),
                prefix.is_universal(),
            ));
            (Arc::new(prefix), lemma_qf, restricted.clone())
        })
        .collect_vec();
    let infer_cfg = Arc::new(infer_cfg);
    let fo = FOModule::new(m, infer_cfg.disj, infer_cfg.gradual);
    let extend = match (infer_cfg.extend_width, infer_cfg.extend_depth) {
        (None, None) => None,
        (Some(width), Some(depth)) => Some((width, depth)),
        (_, _) => panic!("Only one of extend-width and extend-depth is specified."),
    };

    let start = std::time::Instant::now();

    let fixpoint = if infer_cfg.indiv {
        run_individual::<O, L, B>(infer_cfg.clone(), conf, &fo, unrestricted, domains, extend)
            .unwrap()
    } else {
        run_fixpoint::<O, L, B>(infer_cfg.clone(), conf, &fo, unrestricted, domains, extend)
            .unwrap()
    };
    let total_time = start.elapsed().as_secs_f32();
    let proof = fixpoint.to_terms();

    println!("proof {{");
    for lemma in &proof {
        println!("  invariant {lemma}");
    }
    println!("}}");

    if fo.trans_safe_cex(conf, &proof).is_none() {
        println!("Fixpoint SAFE!");
    } else {
        println!("Fixpoint UNSAFE!");
    }

    let (covered, size) = invariant_cover(m, conf, &fo, &proof);
    let trivial = count_trivial(conf, &fo, &proof);

    println!("Fixpoint size = {}", proof.len());
    println!("Fixpoint runtime = {:.2}s", total_time);
    println!("Covers {covered} / {size} of handwritten invariant.");
    println!("{trivial} out of {} lemmas are trivial.", proof.len());
}

pub fn fixpoint_multi<O, L, B>(infer_cfg: InferenceConfig, conf: &SolverConf, m: &Module)
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
{
    let atoms = Arc::new(Atoms::new(
        infer_cfg.cfg.atoms(infer_cfg.nesting, infer_cfg.include_eq),
    ));
    let unrestricted = Arc::new(restrict(&atoms, |_| true));
    let domains: Vec<Domain<L>> = infer_cfg
        .cfg
        .all_prefixes(&infer_cfg)
        .into_iter()
        .flat_map(|prefix| {
            let prefix = Arc::new(prefix);
            let restricted = Arc::new(restrict_by_prefix(&atoms, &infer_cfg.cfg, &prefix));
            let lemma_qf_full = L::new(&infer_cfg, restricted.clone(), prefix.is_universal());
            lemma_qf_full
                .sub_spaces()
                .into_iter()
                .map(move |lemma_qf| (prefix.clone(), Arc::new(lemma_qf), restricted.clone()))
        })
        .sorted_by_key(|(p, w, a)| (p.existentials(), w.approx_space_size(a.len())))
        .collect_vec();
    let infer_cfg = Arc::new(infer_cfg);
    let fo = FOModule::new(m, infer_cfg.disj, infer_cfg.gradual);
    let extend = match (infer_cfg.extend_width, infer_cfg.extend_depth) {
        (None, None) => None,
        (Some(width), Some(depth)) => Some((width, depth)),
        (_, _) => panic!("Only one of extend-width and extend-depth is specified."),
    };

    println!("Number of individual domains: {}", domains.len());

    let mut active_domains: Vec<Domain<L>> = vec![];
    for i in 0..domains.len() {
        active_domains.retain(|d| !(domains[i].0.contains(&d.0) && domains[i].1.contains(&d.1)));
        active_domains.push(domains[i].clone());

        println!();
        println!("({}) Running fixpoint algorithm...", i + 1);
        let total_preds: usize = active_domains
            .iter()
            .map(|(_, w, a)| w.approx_space_size(a.len()))
            .sum();
        println!("    Approximate domain size: {}", total_preds);

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
            println!("    Fixpoint SAFE!");
        } else {
            println!("    Fixpoint UNSAFE!");
        }

        let (covered, size) = invariant_cover(m, conf, &fo, &proof);
        let trivial = count_trivial(conf, &fo, &proof);

        println!("    Fixpoint size = {}", proof.len());
        println!("    Fixpoint runtime = {:.2}s", total_time);
        println!("    Covers {covered} / {size} of handwritten invariant.");
        println!("    {trivial} out of {} lemmas are trivial.", proof.len());
    }

    println!();
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
    let mut weakest;
    let mut frontier: Frontier<O, L, B> = Frontier::new(weaken_set.minimized(), extend);

    // Begin by overapproximating the initial states.
    print(&frontier, &weaken_set, "Finding CTI...".to_string());
    while let Some(cti) = frontier.init_cex(&fo, conf, &weaken_set) {
        print(
            &frontier,
            &weaken_set,
            "CTI found, type=initial".to_string(),
        );

        print(&frontier, &weaken_set, "Weakening...".to_string());
        weaken_set.weaken(&cti);

        print(&frontier, &weaken_set, "Finding CTI...".to_string());
    }

    print(&frontier, &weaken_set, "Computing lemmas...".to_string());
    weakest = weaken_set.minimized();
    print(&frontier, &weaken_set, "Advancing...".to_string());
    while frontier.advance(&weakest, true) {
        // If enabled, extend CTI traces.
        if extend.is_some() {
            frontier.extend(fo, conf, &mut weaken_set);
            print(&frontier, &weaken_set, "Computing lemmas...".to_string());
            weakest = weaken_set.minimized();
            print(
                &frontier,
                &weaken_set,
                "Advancing (no growth)...".to_string(),
            );
            frontier.advance(&weakest, false);
        }

        // Handle transition CTI's.
        print(&frontier, &weaken_set, "Finding CTI...".to_string());
        while let Some(cti) = frontier.trans_cex(&fo, conf, &weaken_set) {
            print(
                &frontier,
                &weaken_set,
                "CTI found, type=transition".to_string(),
            );

            print(&frontier, &weaken_set, "Weakening...".to_string());
            weaken_set.weaken(&cti);

            if extend.is_some() {
                frontier.extend(fo, conf, &mut weaken_set);
            }

            print(&frontier, &weaken_set, "Computing lemmas...".to_string());
            weakest = weaken_set.minimized();
            print(
                &frontier,
                &weaken_set,
                "Advancing (no growth)...".to_string(),
            );
            frontier.advance(&weakest, false);

            print(&frontier, &weaken_set, "Finding CTI...".to_string());
        }

        print(&frontier, &weaken_set, "Computing lemmas...".to_string());
        weakest = weaken_set.minimized();
        print(&frontier, &weaken_set, "Advancing...".to_string());
    }

    Some(weakest)
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
        individual_search.extend(fo, conf);
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

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Find a fixpoint invariant expressing reachable states in a given
//! lemma domain.

use std::fmt::Debug;
use std::sync::Arc;

use itertools::Itertools;

use crate::{
    fly::syntax::{Module, Term, ThmStmt},
    inference::{
        basics::{FOModule, InferenceConfig},
        lemma::Frontier,
        quant::QuantifierPrefix,
        subsume::OrderSubsumption,
        weaken::{LemmaQf, LemmaSet, WeakenLemmaSet},
    },
    verify::SolverConf,
};

type Domain<L> = (QuantifierPrefix, L, Arc<Vec<Term>>);

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
        .iter()
        .filter(|inv| fo.implication_cex(conf, lemmas, &inv.x).is_none())
        .count();

    (covered, proof.invariants.len())
}

pub fn fixpoint_single<O, L, B>(
    infer_cfg: InferenceConfig,
    conf: &SolverConf,
    m: &Module,
    disj: bool,
) where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
{
    let domains = infer_cfg
        .cfg
        .exact_prefixes(
            0,
            infer_cfg.max_existentials.unwrap_or(infer_cfg.cfg.len()),
            infer_cfg.max_size.unwrap_or(infer_cfg.cfg.num_vars()),
        )
        .into_iter()
        .map(|prefix| {
            let atoms = Arc::new(prefix.atoms(infer_cfg.nesting, infer_cfg.include_eq));
            let weaken = L::new(&infer_cfg, atoms.clone(), prefix.is_universal());
            (prefix, weaken, atoms)
        })
        .collect_vec();
    let infer_cfg = Arc::new(infer_cfg);
    let fo = FOModule::new(m, disj);

    let start = std::time::Instant::now();
    let fixpoint =
        run_fixpoint::<O, L, B, _>(infer_cfg.clone(), conf, &fo, domains, |_| false).unwrap();
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

    println!("Fixpoint runtime = {:.2}s", total_time);
    println!("Covers {covered} / {size} of handwritten invariant.");
}

pub fn fixpoint_multi<O, L, B>(
    infer_cfg: InferenceConfig,
    conf: &SolverConf,
    m: &Module,
    disj: bool,
) where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
{
    let domains = infer_cfg
        .cfg
        .all_prefixes(&infer_cfg)
        .into_iter()
        .flat_map(|prefix| {
            let atoms = Arc::new(prefix.atoms(infer_cfg.nesting, infer_cfg.include_eq));
            let weaken_full = L::new(&infer_cfg, atoms.clone(), prefix.is_universal());
            weaken_full
                .sub_spaces()
                .into_iter()
                .map(move |weaken| (prefix.clone(), weaken, atoms.clone()))
        })
        .sorted_by_key(|(p, w, a)| (p.existentials(), w.approx_space_size(a.len())))
        .collect_vec();
    let infer_cfg = Arc::new(infer_cfg);
    let fo = FOModule::new(m, disj);

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
        let fixpoint = run_fixpoint::<O, L, B, _>(
            infer_cfg.clone(),
            conf,
            &fo,
            active_domains.clone(),
            |_| false,
        )
        .unwrap();
        let total_time = start.elapsed().as_secs_f32();
        let proof = fixpoint.to_terms();
        if fo.trans_safe_cex(conf, &proof).is_none() {
            println!("    Fixpoint SAFE!");
        } else {
            println!("    Fixpoint UNSAFE!");
        }
        println!("    Fixpoint size = {}", proof.len());
        println!("    Fixpoint runtime = {:.2}s", total_time);
        let (covered, size) = invariant_cover(m, conf, &fo, &proof);
        println!("    Covers {covered} / {size} of handwritten invariant.");
    }

    println!();
}

/// Run a simple fixpoint algorithm on the configured lemma domains.
fn run_fixpoint<O, L, B, F>(
    infer_cfg: Arc<InferenceConfig>,
    conf: &SolverConf,
    fo: &FOModule,
    domains: Vec<Domain<L>>,
    abort: F,
) -> Option<LemmaSet<O, L, B>>
where
    O: OrderSubsumption<Base = B>,
    L: LemmaQf<Base = B>,
    B: Clone + Debug + Send,
    F: Fn(&WeakenLemmaSet<O, L, B>) -> bool,
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

    let print = |f: &Frontier<O, L, B>, wls: &LemmaSet<O, L, B>, s: String| {
        log::info!(
            "[{:.2}s] [{} | {}] {}",
            start.elapsed().as_secs_f32(),
            f.len(),
            wls.len(),
            s
        );
    };

    let mut weaken_set: WeakenLemmaSet<O, L, B> =
        WeakenLemmaSet::new(Arc::new(infer_cfg.cfg.clone()), infer_cfg.clone(), domains);
    weaken_set.init();
    let mut weakest = weaken_set.to_set();
    let mut frontier: Frontier<O, L, B> = Frontier::new(weaken_set.to_set());

    // Begin by overapproximating the initial states.
    print(&frontier, &weakest, "Finding CTIs...".to_string());
    while let Some(cti) = frontier.init_cex(&fo, conf, &weakest) {
        print(&frontier, &weakest, "CTI found, type=initial".to_string());

        print(&frontier, &weakest, "Weakening...".to_string());
        weaken_set.weaken(&cti);
        if abort(&weaken_set) {
            return None;
        }
        print(&frontier, &weakest, "Computing lemmas...".to_string());
        weakest = weaken_set.to_set();

        print(&frontier, &weakest, "Finding CTIs...".to_string());
    }

    print(&frontier, &weakest, "Advancing...".to_string());
    while frontier.advance(&weakest, true, false) {
        // Handle transition CTI's.
        print(&frontier, &weakest, "Finding CTIs...".to_string());
        while let Some(cti) = frontier.trans_cex(&fo, conf, &weakest) {
            print(
                &frontier,
                &weakest,
                "CTI found, type=transition".to_string(),
            );

            print(&frontier, &weakest, "Weakening...".to_string());
            weaken_set.weaken(&cti);
            if abort(&weaken_set) {
                return None;
            }
            print(&frontier, &weakest, "Computing lemmas...".to_string());
            weakest = weaken_set.to_set();

            // "Zero-cost" advance is currently unused.
            // print(
            //     &frontier,
            //     &weaken_set,
            //     "Advancing (zero-cost)...".to_string(),
            // );
            // frontier.advance(&weaken_set.to_set(), false);

            print(&frontier, &weakest, "Finding CTIs...".to_string());
        }

        print(&frontier, &weakest, "Advancing...".to_string());
    }

    Some(weakest)
}

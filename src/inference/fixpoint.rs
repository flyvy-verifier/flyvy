// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Find a fixpoint invariant expressing reachable states in a given
//! lemma domain.

use std::rc::Rc;

use crate::{
    fly::syntax::Module,
    inference::{
        basics::{FOModule, InferenceConfig},
        lemma::{Cnf, CnfWeaken, Frontier},
        trie::QcnfSet,
    },
    verify::SolverConf,
};

/// Run a simple fixpoint algorithm on the configured lemma domain.
pub fn run_fixpoint(
    infer_cfg: InferenceConfig,
    conf: &SolverConf,
    m: &Module,
    _extend_models: bool,
    disj: bool,
) {
    let InferenceConfig {
        cfg,
        max_clauses,
        max_clause_len,
        nesting,
        include_eq,
    } = infer_cfg;

    let fo = FOModule::new(m, disj);

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

    let print = |f: &Frontier<Cnf, CnfWeaken>, qs: &QcnfSet<Cnf, CnfWeaken>, s: String| {
        log::info!("[{} | {} {}] {}", f.len(), qs.len(), qs.len_clauses(), s);
    };

    let atoms = cfg.atoms(nesting, include_eq);
    log::debug!("Atoms in configuration: {}", atoms.len());
    log::debug!("");

    let cfg = Rc::new(cfg);
    let weaken = CnfWeaken {
        max_clauses,
        max_literals: max_clause_len,
    };
    let mut qcnf_set: QcnfSet<Cnf, CnfWeaken> = QcnfSet::new(cfg, Rc::new(weaken), Rc::new(atoms));
    qcnf_set.add_strongest();
    let mut frontier: Frontier<Cnf, CnfWeaken> = Frontier::new(&qcnf_set);

    // Begin by overapproximating the initial states.
    print(&frontier, &qcnf_set, "Finding CTIs...".to_string());
    while let Some(cti) = frontier.init_cex(&fo, conf, &qcnf_set) {
        print(
            &frontier,
            &qcnf_set,
            "CTI found, type=transition".to_string(),
        );

        print(&frontier, &qcnf_set, "Weakening...".to_string());
        qcnf_set.weaken(&cti);

        print(&frontier, &qcnf_set, "Finding CTIs...".to_string());
    }

    print(&frontier, &qcnf_set, "Advancing...".to_string());
    while frontier.advance(&qcnf_set, true) {
        if fo.trans_safe_cex(conf, &frontier.to_terms()).is_some() {
            println!("Frontier unsafe!");
        }

        // Handle transition CTI's.
        print(&frontier, &qcnf_set, "Finding CTIs...".to_string());
        while let Some(cti) = frontier.trans_cex(&fo, conf, &qcnf_set) {
            print(
                &frontier,
                &qcnf_set,
                "CTI found, type=transition".to_string(),
            );

            print(&frontier, &qcnf_set, "Weakening...".to_string());
            qcnf_set.weaken(&cti);

            print(&frontier, &qcnf_set, "Advancing (zero-cost)...".to_string());
            frontier.advance(&qcnf_set, false);

            print(&frontier, &qcnf_set, "Finding CTIs...".to_string());
        }

        print(&frontier, &qcnf_set, "Advancing...".to_string());
    }

    let proof = frontier.to_terms();
    if fo.trans_safe_cex(conf, &proof).is_none() {
        println!("proof {{");
        for lemma in &frontier.to_terms() {
            println!("  invariant {lemma}");
        }
        println!("}}");
    } else {
        println!("Fixpoint unsafe!");
    }
}

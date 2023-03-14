// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Find a fixpoint for an invariant expressing the reachable states for a given
//! lemma domain.

use std::rc::Rc;

use crate::{
    fly::{semantics::Model, syntax::Module},
    inference::{
        basics::{FOModule, Frame, InferenceConfig},
        pdnf::PDNF,
    },
    verify::SolverConf,
};

/// Run a simple fixpoint algorithm on the configured lemma domain.
pub fn run_fixpoint(
    infer_cfg: InferenceConfig,
    conf: Rc<SolverConf>,
    m: &Module,
    extend_models: bool,
    disj: bool,
) {
    let InferenceConfig {
        cfg,
        kpdnf_cubes: kpdnf,
        kpdnf_lit,
    } = infer_cfg;
    let cfg = Rc::new(cfg);
    let fo = Rc::new(FOModule::new(m, disj));

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

    let mut frame = Frame::new(
        vec![cfg.quantify_false(PDNF::get_false(kpdnf, kpdnf_lit))],
        fo.clone(),
        cfg.clone(),
        conf.clone(),
    );
    let mut frame_t = frame.to_terms();
    let mut models: Vec<Model> = vec![];

    let print = |frame: &Frame<_>, s: &str| {
        log::info!("[{}, {}] {}", frame.len(), frame.len_weakened(), s);
    };

    let atoms = cfg.atoms(&m.signature);
    log::debug!("Atoms in configuration: {}", atoms.len());
    log::debug!("");

    // Begin by overapproximating the initial states.
    let mut i_init = (0, 0);
    while let Some(model) = frame.get_cex_init(Some(&mut i_init)) {
        print(&frame, "CTI found, type=initial");
        frame.weaken(&model, |_| true, &atoms, Some(i_init));
        if extend_models {
            models.push(model);
        }
        print(&frame, "Frame weakened");
    }

    loop {
        // Handle transition CTI's.
        let mut i_trans = (0, 0);
        loop {
            let mut i_extend = (0, 0);
            while !models.is_empty() {
                if let Some(model) = frame.get_cex_extend(&models[0], Some(&mut i_extend)) {
                    print(&frame, "CTI found, type=extended");
                    frame.weaken(&model, |_| true, &atoms, Some(i_extend));
                    models.push(model);
                    print(&frame, "Frame weakened");
                } else {
                    models.remove(0);
                    i_extend = (0, 0);
                }
            }

            if let Some((_, model)) = frame.get_cex_trans(&frame_t, Some(&mut i_trans)) {
                print(&frame, "CTI found, type=transition");
                frame.weaken(&model, |_| true, &atoms, Some(i_trans));
                if extend_models {
                    models.push(model);
                }
                print(&frame, "Frame weakened");
            } else {
                break;
            }
        }

        // Once CTI's are exhausted, update the frame to with weakened lemmas.
        if !frame.update(true) {
            break;
        }

        frame_t = frame.to_terms();

        print(&frame, "Frame updated");

        // Verify safety of updated frame.
        if fo.trans_safe_cex(&conf, &frame_t).is_some() {
            log::warn!("Frame is unsafe! Aborting.");
            return;
        }
    }

    println!("Fixpoint:");
    for lemma in &frame_t {
        println!("    {lemma}");
    }
}

use std::thread;

use crate::utils::{get_context_for_module, QalphaConfig};
use contexts::alg::{find_lfp, PredicateConfig};
use contexts::arith::{ArithExpr, IneqTemplates};
use contexts::miner::{position_or_push, ImperativeChc, MiningTactic};
use contexts::sets::{BaselinePropSet, QFormulaSet};
use fly::syntax::{Module, Term};
use formats::basics::SmtTactic;
use formats::chc::{chc_sys_from_fo_module, ChcSystem};
use itertools::Itertools;
use solver::backends::SolverType;
use solver::basics::{BasicCanceler, BasicSolver, MultiCanceler, ParallelSolvers};
use solver::conf::SolverConf;

fn parallel_z3(seeds: usize) -> ParallelSolvers {
    ParallelSolvers::new(
        (0..seeds)
            .map(|_| SolverConf::new(SolverType::Z3, false, "lfp", 2, None))
            .collect(),
    )
}

fn parallel_z3_cvc5(seeds: usize, fname: &str) -> ParallelSolvers {
    ParallelSolvers::new(
        (0..seeds)
            .flat_map(|_| {
                [
                    SolverConf::new(SolverType::Z3, false, fname, 0, None),
                    SolverConf::new(SolverType::Cvc5, false, fname, 0, None),
                ]
            })
            .collect(),
    )
}

pub fn qalpha_via_contexts(cfg: &QalphaConfig, m: &Module) {
    let solver = parallel_z3_cvc5(1, &cfg.fname);
    let (chc_sys, name, arguments) = chc_sys_from_fo_module(&cfg.fo);

    let inv_cfg = PredicateConfig {
        name,
        arguments,
        context: get_context_for_module(cfg, m, &solver),
    };

    let res = find_lfp::<_, QFormulaSet<BaselinePropSet>>(
        &solver,
        &chc_sys,
        vec![inv_cfg],
        true,
        None,
        &SmtTactic::Gradual,
    );
    if let Some(fp) = res {
        let assignment = fp.get_symbolic_assignment();

        println!();
        println!("{fp}");
        println!();
        if chc_sys.check_assignment(&solver, &assignment, true) {
            println!("Found LFP - Success!");
        } else {
            println!("Found LFP - Failure!");
        }
    } else {
        println!("Could not find LFP!")
    }
}

pub fn verify_via_lfp(chc_sys: &ChcSystem, minimize: bool, disj_lengths: &[usize]) -> bool {
    let multi_canceler = MultiCanceler::new();
    let results = thread::scope(|s| {
        let handles = MiningTactic::TACTICS
            .iter()
            .map(|mining_tactic| {
                let multi_canceler = multi_canceler.clone();
                s.spawn(move || {
                    for disj_length in disj_lengths {
                        log::info!(
                            "Running LFP algorithm with [{mining_tactic}], disj={disj_length}",
                        );
                        if let Some(res) = compute_lfp_single(
                            chc_sys,
                            minimize,
                            Some(*disj_length),
                            mining_tactic,
                            &multi_canceler,
                        ) {
                            if res.0 {
                                multi_canceler.cancel();
                                log::info!("    SUCCESS: [{mining_tactic}], disj={disj_length}");
                                return Some(res);
                            } else {
                                log::info!("    FAILURE: [{mining_tactic}], disj={disj_length}");
                            }
                        }

                        if multi_canceler.is_canceled() {
                            return None;
                        }
                    }

                    None
                })
            })
            .collect_vec();

        handles
            .into_iter()
            .filter_map(|h| h.join().unwrap())
            .collect_vec()
    });

    if !results.is_empty() {
        println!("{}", results[0].1);
        println!("Success!");
        true
    } else {
        println!("Failure!");
        false
    }
}

pub fn compute_lfp_single(
    chc_sys: &ChcSystem,
    minimize: bool,
    disj_length: Option<usize>,
    mining_tactic: &MiningTactic,
    multi_canceler: &MultiCanceler<MultiCanceler<<ParallelSolvers as BasicSolver>::Canceler>>,
) -> Option<(bool, String)> {
    // let solver = SingleSolver::new(SolverConf::new(SolverType::Z3, false, "lfp", 10, None));
    let solver: ParallelSolvers = parallel_z3(2);
    let univ_indices = 1;
    let quantified = (0..univ_indices)
        .map(PredicateConfig::quant_name)
        .collect_vec();

    let imp_chcs = chc_sys
        .chcs
        .iter()
        .filter_map(|chc| ImperativeChc::from_chc(chc, chc_sys))
        .collect_vec();

    for imp_chc in &imp_chcs {
        log::debug!("{imp_chc}")
    }

    let predicates = chc_sys
        .predicates
        .iter()
        .map(|decl| {
            let mut bool_terms = vec![];
            let mut int_terms = vec![];
            let mut int_templates = IneqTemplates::new(false);

            if !decl.args.is_empty() {
                let allowed_ids = (0..decl.args.len())
                    .map(PredicateConfig::arg_name)
                    .chain(quantified.iter().cloned())
                    .collect();

                for imp_chc in &imp_chcs {
                    let (bs, ls) = imp_chc.leqs(
                        &mining_tactic,
                        &allowed_ids,
                        &decl.args,
                        &quantified,
                        &mut int_terms,
                    );
                    for b in bs {
                        if !bool_terms.contains(&b) {
                            bool_terms.push(b)
                        }
                    }

                    if imp_chc.relevant_for(&decl.name) {
                        for (expr, r) in ls {
                            int_templates.add_range(expr, r);
                        }
                    }
                }

                for name in &quantified {
                    let expr = ArithExpr::<usize>::from_term(&Term::id(name), |t| {
                        position_or_push(&mut int_terms, t)
                    })
                    .unwrap();
                    int_templates.add_range(expr, (-1, 0));
                }

                /*
                for t in &int_terms {
                    println!("{t}");
                }
                println!("--- int exprs ----------");
                for (e, r) in &int_templates.templates {
                    println!("{e} <= {r}");
                }
                println!("--- bools --------------");
                for b in &bool_terms {
                    println!("{b}");
                }
                */
            }
            PredicateConfig::int_ineqs(
                decl,
                int_terms,
                bool_terms,
                int_templates,
                univ_indices,
                disj_length,
            )
        })
        .collect();

    let res = find_lfp::<_, QFormulaSet<BaselinePropSet>>(
        &solver,
        chc_sys,
        predicates,
        minimize,
        Some(multi_canceler),
        &SmtTactic::Full,
    );

    if let Some(fp) = res {
        let assignment = fp.get_symbolic_assignment();
        let solved = chc_sys.check_assignment(&solver, &assignment, true);
        Some((solved, fp.to_string()))
    } else {
        None
    }
}

use crate::utils::{get_context_for_module, QalphaConfig};
use contexts::alg::{find_lfp, PredicateConfig};
use contexts::arith::{ArithExpr, IneqTemplates};
use contexts::miner::{position_or_push, ImperativeChc};
use contexts::sets::{BaselinePropSet, QFormulaSet};
use fly::syntax::{Module, Term};
use formats::chc::{chc_sys_from_fo_module, ChcSystem};
use itertools::Itertools;
use solver::backends::SolverType;
use solver::basics::{BasicSolver, ParallelSolvers, SingleSolver};
use solver::conf::SolverConf;

fn parallel_z3(seeds: usize) -> impl BasicSolver {
    ParallelSolvers::new(
        (0..seeds)
            .map(|seed| SolverConf::new(SolverType::Z3, true, "lfp", 10, Some(seed)))
            .collect(),
    )
}

pub fn qalpha_via_contexts(cfg: &QalphaConfig, m: &Module) {
    let solver = SingleSolver::new(SolverConf::new(SolverType::Z3, true, &cfg.fname, 30, None));
    let (chc_sys, name, arguments) = chc_sys_from_fo_module(&cfg.fo);

    let inv_cfg = PredicateConfig {
        name,
        arguments,
        context: get_context_for_module(cfg, m),
    };

    let fp = find_lfp::<_, QFormulaSet<BaselinePropSet>>(&solver, &chc_sys, vec![inv_cfg], true);
    let assignment = fp.get_symbolic_assignment();

    println!();
    println!("{fp}");
    println!();
    if chc_sys.check_assignment(&solver, &assignment, true) {
        println!("Success!");
    } else {
        println!("Failure!");
    }
}

pub fn compute_lfp(chc_sys: &ChcSystem, minimize: bool, disj_length: Option<usize>) -> bool {
    // let solver = SingleSolver::new(SolverConf::new(SolverType::Z3, false, "lfp", 10, None));
    let solver = parallel_z3(2);
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
        println!("{imp_chc}")
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
                    let (bs, ls) = imp_chc.leqs(&allowed_ids, &quantified, &mut int_terms);
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

                println!("========== {} ==========", decl.name);
                println!("--- ints ---------------");
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

    let fp = find_lfp::<_, QFormulaSet<BaselinePropSet>>(&solver, chc_sys, predicates, minimize);
    let assignment = fp.get_symbolic_assignment();

    println!();
    println!("{fp}");

    println!();
    let solved = chc_sys.check_assignment(&solver, &assignment, true);
    if solved {
        println!("Success!");
    } else {
        println!("Failure!");
    }

    solved
}

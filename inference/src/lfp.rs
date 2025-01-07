use crate::utils::{get_context_for_module, QalphaConfig};
use contexts::alg::{find_lfp, PredicateConfig};
use contexts::miner::ChcMiner;
use contexts::sets::{BaselinePropSet, QFormulaSet};
use fly::syntax::Module;
use formats::chc::{chc_sys_from_fo_module, ChcSystem};
use solver::backends::SolverType;
use solver::basics::{BasicSolver, ParallelSolvers, SingleSolver};
use solver::conf::SolverConf;

fn parallel_z3(seeds: usize) -> impl BasicSolver {
    ParallelSolvers::new(
        (0..seeds)
            .map(|seed| SolverConf::new(SolverType::Z3, false, "lfp", 10, Some(seed)))
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
    if chc_sys.check_assignment(&solver, &assignment) {
        println!("Success!");
    } else {
        println!("Failure!");
    }
}

pub fn compute_lfp(chc_sys: &ChcSystem, minimize: bool) {
    let solver = parallel_z3(8);
    let univ_indices = 1;
    let disj_length = Some(3);

    let mut miners = ChcMiner::default();
    miners.mine_chcs(chc_sys, univ_indices);
    println!("{miners}");

    let predicates = chc_sys
        .predicates
        .iter()
        .map(|decl| {
            let terms = miners
                .miners
                .get(&decl.name)
                .expect("cannot mine terms for predicate");
            let (int_terms, int_templates) = terms.inequalities();
            println!("========== {} ==========", decl.name);
            for t in &int_terms {
                println!("{t}");
            }
            println!("------------------------");
            for e in int_templates.templates.keys() {
                println!("{e}");
            }
            PredicateConfig::int_ineqs(decl, int_terms, int_templates, univ_indices, disj_length)
        })
        .collect();

    let fp = find_lfp::<_, QFormulaSet<BaselinePropSet>>(&solver, chc_sys, predicates, minimize);
    let assignment = fp.get_symbolic_assignment();

    println!();
    println!("{fp}");

    println!();
    if chc_sys.check_assignment(&solver, &assignment) {
        println!("Success!");
    } else {
        println!("Failure!");
    }
}

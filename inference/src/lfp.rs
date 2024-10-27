use crate::utils::{get_multi_context, QalphaConfig};
use contexts::alg::{find_lfp, PredicateConfig};
use contexts::language::atomics_in_chc_sys;
use contexts::sets::{BaselinePropSet, QFormulaSet};
use fly::syntax::Module;
use formats::chc::{chc_sys_from_fo_module, ChcSystem};
use solver::backends::SolverType;
use solver::basics::SingleSolver;
use solver::conf::SolverConf;

pub fn qalpha_via_contexts(cfg: &QalphaConfig, m: &Module) {
    let solver = SingleSolver::new(SolverConf::new(SolverType::Z3, true, &cfg.fname, 0, None));
    let (chc_sys, name, arguments) = chc_sys_from_fo_module(&cfg.fo);

    let inv_cfg = PredicateConfig {
        name,
        arguments,
        context: get_multi_context(cfg, m),
    };

    let fp = find_lfp::<_, QFormulaSet<BaselinePropSet>>(&solver, &chc_sys, vec![inv_cfg]);

    println!("{fp}");
}

pub fn compute_lfp(chc_sys: &ChcSystem) {
    let solver = SingleSolver::new(SolverConf::new(SolverType::Z3, true, "lfp", 100, None));
    let pred_to_lits = atomics_in_chc_sys(chc_sys, 1);
    let predicates = chc_sys
        .predicates
        .iter()
        .map(|decl| PredicateConfig::default(decl, &pred_to_lits[&decl.name]))
        .collect();

    let fp = find_lfp::<_, QFormulaSet<BaselinePropSet>>(&solver, chc_sys, predicates);
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

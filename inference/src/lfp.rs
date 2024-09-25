use crate::utils::{get_multi_context, QalphaConfig};
use contexts::alg::{find_lfp, PredicateConfig};
use contexts::sets::{BaselinePropSet, QFormulaSet};
use fly::syntax::Module;
use formats::chc::{chc_sys_from_fo_module, ChcSystem};
use solver::backends::SolverType;
use solver::basics::SingleSolver;
use solver::conf::SolverConf;

pub fn qalpha_via_contexts(cfg: &QalphaConfig, m: &Module) {
    let solver = SingleSolver::new(SolverConf::new(SolverType::Z3, false, &cfg.fname, 0, None));
    let (chc_sys, name, arguments) = chc_sys_from_fo_module(&cfg.fo);

    let inv_cfg = PredicateConfig {
        name,
        arguments,
        context: get_multi_context(cfg, m),
    };

    let fp = find_lfp::<_, QFormulaSet<BaselinePropSet>>(&solver, &chc_sys, vec![inv_cfg]);

    println!("{}", fp.to_string());
}

pub fn compute_lfp(fname: &String, chc_sys: &ChcSystem) {
    let solver = SingleSolver::new(SolverConf::new(SolverType::Z3, false, fname, 0, None));
    let predicates = chc_sys
        .predicates
        .iter()
        .map(|decl| PredicateConfig::default(decl, chc_sys))
        .collect();

    let fp = find_lfp::<_, QFormulaSet<BaselinePropSet>>(&solver, &chc_sys, predicates);

    println!();
    println!("{}", fp.to_string());
}

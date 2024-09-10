use crate::utils::{get_multi_context, QalphaConfig};
use contexts::alg::{find_lfp, PredicateConfig};
use contexts::sets::{BaselinePropSet, QFormulaSet};
use fly::syntax::Module;
use formats::chc::chc_sys_from_fo_module;
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

use std::sync::Arc;

use fly::syntax::{Module, Term, ThmStmt};

use crate::{
    basics::{Direction, FOModule, QalphaConfig, SmtTactic},
    qalpha::fixpoint::{qalpha_dynamic, qalpha_multi_prefix},
};

pub fn qalpha_fbii(
    cfgs: Vec<(Direction, QalphaConfig)>,
    fwd_m: &Module,
    bwd_m: &Module,
    disj: bool,
    smt_tactic: SmtTactic,
    print_nondet: bool,
) {
    let mut additional_axioms = vec![];
    for (direction, mut cfg) in cfgs {
        cfg.fo.module.axioms.extend(additional_axioms.clone());

        let prefix_info = if cfg.multi_prefix_length.is_some() {
            format!(
                "multi-prefix (length={}, exists_forall={})",
                cfg.multi_prefix_length.unwrap(),
                cfg.exists_forall_only
            )
        } else {
            format!("{:?}", cfg.quant_cfg)
        };

        println!(
            "Running FBII({}) in {} direction with prefix: {}",
            additional_axioms.len(),
            direction,
            prefix_info
        );
        let mut m = match direction {
            Direction::Fwd => fwd_m,
            Direction::Bwd => bwd_m,
        }
        .clone();
        m.statements = additional_axioms
            .iter()
            .map(|a| ThmStmt::Assume(Term::always(a)))
            .chain(m.statements)
            .collect();
        cfg.fo = FOModule::new(&m, disj, smt_tactic);

        // Choose between multi-prefix and dynamic based on config
        let fixpoint = if cfg.multi_prefix_length.is_some() {
            qalpha_multi_prefix(Arc::new(cfg), &m, print_nondet)
        } else {
            qalpha_dynamic(Arc::new(cfg), &m, None, print_nondet)
        };

        let reduced = fixpoint.reduced();
        for t in &reduced {
            println!("    invariant {}", t);
        }
        println!(
            "========== Fixpoint found, reduced size={}, safe={}, time={} ==========",
            reduced.len(),
            fixpoint.is_safe(),
            fixpoint.time_sec()
        );
        additional_axioms.extend(reduced);
    }
}

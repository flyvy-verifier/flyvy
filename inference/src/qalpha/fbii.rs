use std::sync::Arc;

use fly::syntax::{Module, Term, ThmStmt};

use crate::{
    basics::{Direction, FOModule, QalphaConfig, SmtTactic},
    qalpha::fixpoint::qalpha_dynamic,
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
        println!(
            "Running FBII({}) in {} direction with prefix: {:?}",
            additional_axioms.len(),
            direction,
            cfg.quant_cfg
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
        let fixpoint = qalpha_dynamic(Arc::new(cfg), &m, print_nondet);
        let reduced = fixpoint.reduced();
        for t in &reduced {
            println!("    {}", t);
        }
        println!(
            "========== Fixpoint found, reduced size={}, safe={} ==========",
            reduced.len(),
            fixpoint.is_safe()
        );
        additional_axioms.extend(reduced);
    }
}

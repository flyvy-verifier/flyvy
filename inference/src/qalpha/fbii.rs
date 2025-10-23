use std::sync::Arc;
use std::time::Instant;

use fly::syntax::{Module, Term, ThmStmt};

use crate::{
    basics::{Direction, FOModule, QalphaConfig, SmtTactic},
    qalpha::fixpoint::{qalpha_dynamic, qalpha_multi_prefix},
};

/// Run FBII with automatic parameter tuning.
/// Iterates through parameter values from auto_min to auto_max, running the full FBII
/// sequence for each parameter value. Accumulates axioms across all iterations within
/// each parameter value. Stops when a safe fixpoint is found.
pub fn qalpha_fbii_auto(
    cfgs: &[(Direction, QalphaConfig)],
    fwd_m: &Module,
    bwd_m: &Module,
    disj: bool,
    smt_tactic: SmtTactic,
    print_nondet: bool,
    auto_min: usize,
    auto_max: usize,
) {
    let start_time = Instant::now();

    for param_value in auto_min..=auto_max {
        let elapsed = start_time.elapsed();
        println!(
            "\n========== Auto mode: trying parameter value {} (elapsed: {:.2}s) ==========",
            param_value,
            elapsed.as_secs_f64()
        );

        let mut additional_axioms = vec![];

        for (direction, cfg) in cfgs.iter() {
            let mut cfg = (*cfg).clone();
            cfg.fo.module.axioms.extend(additional_axioms.clone());

            // Auto mode always uses multi-prefix mode
            // Set unspecified parameters to current auto value
            // User-specified parameters remain fixed across all iterations
            if cfg.multi_prefix_length.is_none() {
                cfg.multi_prefix_length = Some(param_value);
            }
            if cfg.multi_constant_limit.is_none() {
                cfg.multi_constant_limit = Some(param_value);
            }
            // If multi_total_per_sort is None, initialize it with param_value for all sorts
            // If it's Some but contains zeros (indicating unspecified), set those to param_value
            if cfg.multi_total_per_sort.is_none() {
                if let Some(ref sort_order) = cfg.multi_sort_order {
                    cfg.multi_total_per_sort = Some(vec![param_value; sort_order.len()]);
                }
            }

            let prefix_info = format!(
                "multi-prefix (length={}, constant_limit={}, total_per_sort={:?}, exists_forall={})",
                cfg.multi_prefix_length.unwrap(),
                cfg.multi_constant_limit.unwrap(),
                cfg.multi_total_per_sort.as_ref().unwrap(),
                cfg.exists_forall_only
            );

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

            // Auto mode always uses multi-prefix
            let fixpoint = qalpha_multi_prefix(Arc::new(cfg), &m, print_nondet);

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

            if fixpoint.is_safe() {
                let elapsed = start_time.elapsed();
                println!(
                    "\n========== Auto mode: SUCCESS with parameter value {} ==========",
                    param_value
                );
                println!("Total auto mode time: {:.2}s", elapsed.as_secs_f64());
                return;
            }

            additional_axioms.extend(reduced);
        }
    }

    let elapsed = start_time.elapsed();
    println!("\n========== Auto mode: Failed to find safe fixpoint with parameters in range {}..={} ==========", auto_min, auto_max);
    println!("Total auto mode time: {:.2}s", elapsed.as_secs_f64());
}

pub fn qalpha_fbii(
    cfgs: Vec<(Direction, QalphaConfig)>,
    fwd_m: &Module,
    bwd_m: &Module,
    disj: bool,
    smt_tactic: SmtTactic,
    print_nondet: bool,
) {
    let start_time = Instant::now();
    let mut additional_axioms = vec![];
    for (direction, mut cfg) in cfgs {
        let elapsed = start_time.elapsed();
        cfg.fo.module.axioms.extend(additional_axioms.clone());

        let prefix_info = if cfg.multi_prefix_length.is_some() {
            format!(
                "multi-prefix (length={}, constant_limit={}, total_per_sort={:?}, exists_forall={})",
                cfg.multi_prefix_length.unwrap(),
                cfg.multi_constant_limit.unwrap(),
                cfg.multi_total_per_sort.as_ref().unwrap(),
                cfg.exists_forall_only
            )
        } else {
            format!("{:?}", cfg.quant_cfg)
        };

        println!(
            "Running FBII({}) in {} direction with prefix: {} (elapsed: {:.2}s)",
            additional_axioms.len(),
            direction,
            prefix_info,
            elapsed.as_secs_f64()
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

    let elapsed = start_time.elapsed();
    println!("\n========== FBII complete ==========");
    println!("Total FBII time: {:.2}s", elapsed.as_secs_f64());
}

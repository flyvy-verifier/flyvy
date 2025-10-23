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
/// 
/// For each parameter value, also iterates over all clause sizes (from min_clause_size to max_clause_size)
/// and all cube numbers (from min_cubes to max_cubes).
pub fn qalpha_fbii_auto(
    cfgs: &[(Direction, QalphaConfig)],
    fwd_m: &Module,
    bwd_m: &Module,
    disj: bool,
    smt_tactic: SmtTactic,
    print_nondet: bool,
    auto_min: usize,
    auto_max: usize,
    min_clause_size: usize,
    max_clause_size: Option<usize>,
    min_cubes: usize,
    max_cubes: Option<usize>,
) {
    let start_time = Instant::now();

    // Determine iteration ranges for clause_size and cubes
    // If max not specified, use the min value (no iteration on that dimension)
    let clause_size_max = max_clause_size.unwrap_or(min_clause_size);
    let cubes_max = max_cubes.unwrap_or(min_cubes);

    for param_value in auto_min..=auto_max {
        for current_clause_size in min_clause_size..=clause_size_max {
            for current_cubes in min_cubes..=cubes_max {
                let elapsed = start_time.elapsed();
                println!(
                    "\n========== Auto mode: param={}, clause_size={}, cubes={} (elapsed: {:.2}s) ==========",
                    param_value,
                    current_clause_size,
                    current_cubes,
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

                    // Update QF config with current clause_size and cubes
                    cfg.qf_cfg.clause_size = current_clause_size;
                    cfg.qf_cfg.cubes = current_cubes;

                    let prefix_info = format!(
                        "multi-prefix (length={}, constant_limit={}, total_per_sort={:?}, exists_forall={}, clause_size={}, cubes={})",
                        cfg.multi_prefix_length.unwrap(),
                        cfg.multi_constant_limit.unwrap(),
                        cfg.multi_total_per_sort.as_ref().unwrap(),
                        cfg.exists_forall_only,
                        current_clause_size,
                        current_cubes
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
                            "\n========== Auto mode: SUCCESS with param={}, clause_size={}, cubes={} ==========",
                            param_value,
                            current_clause_size,
                            current_cubes
                        );
                        println!("Total auto mode time: {:.2}s", elapsed.as_secs_f64());
                        return;
                    }

                    additional_axioms.extend(reduced);
                }
            }
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

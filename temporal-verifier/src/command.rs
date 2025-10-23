// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! The temporal-verifier binary's command-line interface.

use bounded::checker::CheckerAnswer;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use fly::term::prime::reverse_module;
use inference::qalpha::fbii::qalpha_fbii;
use inference::qalpha::fixpoint::defaults;
use path_slash::PathExt;
use solver::basics::SingleSolver;
use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;
use std::{fs, process};

use clap::Args;
use codespan_reporting::{
    files::SimpleFile,
    term::{
        self as terminal,
        termcolor::{ColorChoice, StandardStream},
    },
};
use fly::semantics::models_to_string;
use fly::syntax::{Module, Signature, Sort};
use fly::{self, parser::parse_error_diagnostic, printer, sorts, timing};
use inference::basics::{
    Direction, FOModule, QalphaConfig, QfBody, QuantifierFreeConfig, SimulationConfig, SmtTactic,
};
use inference::houdini;
use inference::qalpha::{
    fixpoint::{qalpha_dynamic, qalpha_multi_prefix, Strategy},
    quant::parse_quantifiers,
};
use inference::updr::Updr;
use solver::backends;
use solver::conf::SolverConf;
use verify::module::verify_module;

#[derive(clap::ValueEnum, Copy, Clone, Debug, PartialEq, Eq)]
enum SolverType {
    Z3,
    Cvc4,
    Cvc5,
}

#[derive(clap::ValueEnum, Copy, Clone, Debug, PartialEq, Eq)]
enum ColorOutput {
    Never,
    Auto,
    Always,
}

#[derive(clap::ValueEnum, Copy, Clone, Debug, PartialEq, Eq)]
enum Mode {
    Single,
    Multi,
    Auto,
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct SolverArgs {
    // --solver and --smt are global, meaning they are allowed even after
    // subcommands
    #[arg(value_enum, long, default_value_t = SolverType::Z3, global = true)]
    /// Solver to use
    solver: SolverType,

    #[arg(long, global = true)]
    /// Output smt2 file alongside input file
    smt: bool,

    #[arg(long, default_value_t = 600, global = true)]
    /// SMT solver timeout in seconds
    timeout: usize,

    #[arg(long, default_value_t = 0, global = true)]
    /// SMT solver random seed
    solver_seed: usize,
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct VerifyArgs {
    #[command(flatten)]
    solver: SolverArgs,

    #[arg(long)]
    /// Print timing statistics
    time: bool,

    /// File name for a .fly file
    file: String,
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct QuantifierConfigArgs {
    #[arg(short, long)]
    /// Quantifier of the form `<quantifier: F/E/*> <sort> <count>` which is appended to the
    /// quantifier structure of the first-order language; multiple quantifiers are permitted
    quantifier: Vec<String>,
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct QuantifierFreeConfigArgs {
    #[arg(long, default_value = "pdnf")]
    /// The quantifier-free body of formulas in the first-order language (pdnf/cnf/dnf)
    qf: String,

    #[arg(long)]
    /// The maximal size of the pDNF clause, or of each CNF clause, depending on --qf
    clause_size: Option<usize>,

    #[arg(long)]
    ///The maximal number of cubes in k-pDNF or DNF; for k-pDNF, this refers to non-unit cubes, i.e., k - 1
    cubes: Option<usize>,

    #[arg(long)]
    /// The maximal nesting depth of atoms / terms in the vocabulary (unbounded if not provided);
    /// non-Boolean constants are considered to have depth 1
    nesting: Option<usize>,

    #[arg(long, action)]
    /// Do not include equality terms in the vocabulary
    no_include_eq: bool,
}

impl QuantifierFreeConfigArgs {
    fn to_cfg(&self) -> QuantifierFreeConfig {
        QuantifierFreeConfig {
            qf_body: QfBody::from(self.qf.as_str()),
            clause_size: self.clause_size,
            cubes: self.cubes,
            nesting: self.nesting,
        }
    }
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct SimulationConfigArgs {
    /// The size bound to use for the given sort in simulations, given as SORT=N as in `--bound node=2`
    #[arg(long)]
    bound: Vec<String>,

    /// Instead of a bound for each sort, bound the sum of sort sizes
    #[arg(long)]
    bound_sum: Option<usize>,

    #[arg(long)]
    /// Run simulations up to this depth
    depth: Option<usize>,

    #[arg(long)]
    /// In simulations, consider the depth from the last counter-example found
    guided: bool,

    #[arg(long)]
    /// Run simulations in a DFS manner (default is BFS)
    dfs: bool,
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct SmtOptimizationArgs {
    #[arg(long, default_value = "1")]
    /// Number of different seeds to try the solvers with
    seeds: usize,

    #[arg(long)]
    /// Do not try to decompose the transition relation disjunctively
    no_disj: bool,

    #[arg(long, default_value = "gradual")]
    /// Determines the incrementality of SMT queries (full/gradual/minimal)
    smt_tactic: String,
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct QalphaArgs {
    #[command(flatten)]
    quant_cfg: QuantifierConfigArgs,

    #[arg(long)]
    /// Look for the strongest individually inductive lemmas rather than the strongest conjunction
    no_conj: bool,

    #[command(flatten)]
    qf_cfg: QuantifierFreeConfigArgs,

    #[arg(long)]
    /// Use the baseline implementation of the data-structure in qalpha instead of LSet
    baseline: bool,

    #[command(flatten)]
    sim_cfg: SimulationConfigArgs,

    #[arg(long, default_value = "weaken")]
    /// Determines the strategy that is used in the fixpoint search.
    /// Options are "weaken", "weaken-pd", "houdini", "houdini-pd", or "none".
    /// "pd" indicates a property-directed strategy. Only "weaken" guarantees finding
    /// the least-fixpoint.
    strategy: String,

    #[command(flatten)]
    smt_cfg: SmtOptimizationArgs,

    #[arg(value_enum, long, default_value_t = Mode::Single)]
    /// Mode for quantifier prefix generation (single/multi/auto)
    mode: Mode,

    #[arg(long)]
    /// Sort ordering for multi-prefix mode (repeatable)
    sort: Vec<String>,

    #[arg(long)]
    /// Prefix length for multi-prefix mode
    prefix_length: Option<usize>,

    #[arg(long)]
    /// Maximum total number of constants across all sorts for multi-prefix mode
    constant_limit: Option<usize>,

    #[arg(long)]
    /// Total atomic terms (vars + constants) per sort for multi-prefix mode (uniform across all sorts)
    total_per_sort: Option<usize>,

    #[arg(long, default_value_t = 1)]
    /// Minimum value for auto mode parameter iteration
    auto_min: usize,

    #[arg(long, default_value_t = 10)]
    /// Maximum value for auto mode parameter iteration
    auto_max: usize,

    #[arg(long)]
    /// Restrict prefixes to exists* forall* pattern in multi-prefix mode
    exists_forall: bool,

    #[arg(long)]
    /// Remove trivial atoms (that are always true or always false) using implication checks
    remove_trivial_atoms: bool,

    /// File name for a .fly file containing the program to analyse
    file: String,
}

impl QalphaArgs {
    fn to_cfg(&self, m: &Module, fname: String) -> QalphaConfig {
        let universe = if self.sim_cfg.bound.is_empty() || self.sim_cfg.bound_sum.is_some() {
            vec![defaults::SIMULATION_SORT_SIZE; m.signature.sorts.len()]
        } else {
            let universe_map = get_universe(&m.signature, &self.sim_cfg.bound);
            m.signature.sorts.iter().map(|s| universe_map[s]).collect()
        };

        // Parse sort order if in multi or auto mode
        let (multi_sort_order, multi_total_per_sort) = if self.mode == Mode::Multi || self.mode == Mode::Auto {
            let sort_order: Vec<Sort> = self
                .sort
                .iter()
                .map(|s| Sort::Uninterpreted(s.clone()))
                .collect();
            // For auto mode, total_per_sort is optional (will be set by auto-tuning if not specified)
            // For multi mode, it's required (validation handles this)
            let total_per_sort = self.total_per_sort.map(|val| vec![val; sort_order.len()]);
            (Some(sort_order), total_per_sort)
        } else {
            (None, None)
        };

        QalphaConfig {
            fname,
            fo: FOModule::new(
                m,
                !self.smt_cfg.no_disj,
                SmtTactic::from(self.smt_cfg.smt_tactic.as_str()),
            ),

            conj: !self.no_conj,

            quant_cfg: Arc::new(parse_quantifiers(&self.quant_cfg.quantifier, &m.signature)),

            qf_cfg: self.qf_cfg.to_cfg(),

            sim: SimulationConfig {
                universe,
                sum: self.sim_cfg.bound_sum,
                depth: self.sim_cfg.depth,
                guided: self.sim_cfg.guided,
                dfs: self.sim_cfg.dfs,
            },

            strategy: Strategy::from(self.strategy.as_str()),
            seeds: self.smt_cfg.seeds,
            baseline: self.baseline,
            exists_forall_only: self.exists_forall,
            remove_trivial_atoms: self.remove_trivial_atoms,
            multi_prefix_length: self.prefix_length,
            multi_constant_limit: self.constant_limit,
            multi_sort_order,
            multi_total_per_sort,
        }
    }
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct FbiiArgs {
    #[command(flatten)]
    qalpha_args: QalphaArgs,
    #[arg(short, long)]
    iter: Vec<String>,
}

impl FbiiArgs {
    fn to_cfgs(&self, m: &Module, fname: String) -> Vec<(Direction, QalphaConfig)> {
        let universe = if self.qalpha_args.sim_cfg.bound.is_empty()
            || self.qalpha_args.sim_cfg.bound_sum.is_some()
        {
            vec![defaults::SIMULATION_SORT_SIZE; m.signature.sorts.len()]
        } else {
            let universe_map = get_universe(&m.signature, &self.qalpha_args.sim_cfg.bound);
            m.signature.sorts.iter().map(|s| universe_map[s]).collect()
        };

        // Parse sort order if in multi or auto mode
        let (multi_sort_order, multi_total_per_sort) = if self.qalpha_args.mode == Mode::Multi || self.qalpha_args.mode == Mode::Auto {
            let sort_order: Vec<Sort> = self
                .qalpha_args
                .sort
                .iter()
                .map(|s| Sort::Uninterpreted(s.clone()))
                .collect();
            // For auto mode, total_per_sort is optional (will be set by auto-tuning if not specified)
            // For multi mode, it's required (validation handles this)
            let total_per_sort = self.qalpha_args.total_per_sort.map(|val| vec![val; sort_order.len()]);
            (Some(sort_order), total_per_sort)
        } else {
            (None, None)
        };

        let mut cfgs = vec![];
        let fo = FOModule::new(
            m,
            !self.qalpha_args.smt_cfg.no_disj,
            SmtTactic::from(self.qalpha_args.smt_cfg.smt_tactic.as_str()),
        );

        for it in &self.iter {
            let parts = it
                .split('|')
                .map(|s| s.to_string())
                .collect::<Vec<String>>();
            assert!(parts.len() > 0 && (parts[0] == "fwd" || parts[0] == "bwd"));
            let direction = if parts[0] == "fwd" {
                Direction::Fwd
            } else {
                Direction::Bwd
            };

            cfgs.push((
                direction,
                QalphaConfig {
                    fname: fname.clone(),

                    // will be overwritten by the direction later
                    fo: fo.clone(),

                    conj: !self.qalpha_args.no_conj,

                    quant_cfg: Arc::new(parse_quantifiers(&parts[1..], &m.signature)),

                    qf_cfg: self.qalpha_args.qf_cfg.to_cfg(),

                    sim: SimulationConfig {
                        universe: universe.clone(),
                        sum: self.qalpha_args.sim_cfg.bound_sum,
                        depth: self.qalpha_args.sim_cfg.depth,
                        guided: self.qalpha_args.sim_cfg.guided,
                        dfs: self.qalpha_args.sim_cfg.dfs,
                    },

                    strategy: Strategy::from(self.qalpha_args.strategy.as_str()),
                    seeds: self.qalpha_args.smt_cfg.seeds,
                    baseline: self.qalpha_args.baseline,
                    exists_forall_only: self.qalpha_args.exists_forall,
                    remove_trivial_atoms: self.qalpha_args.remove_trivial_atoms,
                    multi_prefix_length: self.qalpha_args.prefix_length,
                    multi_constant_limit: self.qalpha_args.constant_limit,
                    multi_sort_order: multi_sort_order.clone(),
                    multi_total_per_sort: multi_total_per_sort.clone(),
                },
            ));
        }

        cfgs
    }
}

#[derive(clap::Subcommand, Clone, Debug, PartialEq, Eq)]
enum InferCommand {
    /// Run Houdini
    Houdini {
        #[command(flatten)]
        solver: SolverArgs,

        /// File name for a .fly file
        file: String,
    },
    /// Run the qalpha algorithm, which computes the strongest inductive invariant expressible in
    /// a given first-order logical language. The language is mostly specified using a quantifier
    /// structure and a quantifier-free body restricting the formulas in the language.
    Qalpha(QalphaArgs),
    Fbii(FbiiArgs),
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct InferArgs {
    #[arg(long, global = true)]
    /// Print timing statistics
    time: bool,

    #[arg(long)]
    /// Don't print non-deterministic details about the run, e.g., the found invariant or timing information (for testing)
    no_print_nondet: bool,

    #[command(subcommand)]
    infer_cmd: InferCommand,
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct BoundedArgs {
    /// File name for a .fly file
    file: String,
    /// Maximum number of transitions to consider during model checking
    #[arg(long)]
    depth: Option<usize>,
    /// What size bound to use for the given sort, given as SORT=N as in --bound node=2
    #[arg(long)]
    bound: Vec<String>,
    /// Whether or not to print timing information (true by default)
    #[arg(long)]
    print_timing: Option<bool>,
}

/// Parses the arguments in `bound` into a universe size map.
///
/// Ensures that every sort in the given signature is given a bound.
fn get_universe(sig: &Signature, bound: &[String]) -> HashMap<String, usize> {
    let mut universe: HashMap<String, usize> = HashMap::new();
    for b in bound {
        if let [sort_name, bound_size] = b.split('=').collect::<Vec<&str>>()[..] {
            let sort_name = sort_name.to_string();
            if !sig.sorts.contains(&sort_name) {
                eprintln!("unknown sort name {sort_name} in bound {b}");
                process::exit(1);
            }
            if let Ok(bound_size) = bound_size.parse::<usize>() {
                universe.insert(sort_name, bound_size);
            } else {
                eprintln!("could not parse bound as integer in {b}");
                process::exit(1);
            }
        } else {
            eprintln!("expected exactly one '=' in bound {b}");
            process::exit(1);
        }
    }
    if let Some(unbounded_sort) = sig.sorts.iter().find(|&s| !universe.contains_key(s)) {
        eprintln!(
            "need a bound for sort {unbounded_sort} on the command line, as in --bound {unbounded_sort}=N"
        );
        process::exit(1);
    }
    universe
}

impl BoundedArgs {
    /// Parses the arguments in self.bound into a universe size map.
    ///
    /// Ensures that every sort in the given signature is given a bound.
    fn get_universe(&self, sig: &Signature) -> HashMap<String, usize> {
        get_universe(sig, &self.bound)
    }
}

#[derive(clap::Subcommand, Clone, Debug, PartialEq, Eq)]
enum Command {
    /// Verify all assertions using user-provided invariants.
    Verify(VerifyArgs),
    /// Verify assertions by inferring invariants with UPDR.
    UpdrVerify(VerifyArgs),
    /// Infer invariants using other invariant inference algorithms.
    Infer(InferArgs),
    /// Parse and re-print a fly file (for debugging)
    Print {
        /// File name for a .fly file
        file: String,
    },
    /// Parse a fly file, inline definitions, and print (for debugging)
    Inline {
        /// File name for a .fly file
        file: String,
    },
    /// Apply bounded model checking to each assertion using a set of states.
    SetCheck {
        #[command(flatten)]
        bounded: BoundedArgs,
        /// Whether to only keep track of the last state of the trace
        #[arg(long)]
        compress_traces: bool,
    },
    /// Apply bounded model checking to each assertion using a SAT solver.
    SatCheck(BoundedArgs),
    /// Apply bounded model checking to each assertion using binary decision
    /// diagrams (BDDs).
    BddCheck {
        #[command(flatten)]
        bounded: BoundedArgs,
        /// Whether to search from the unsafe states inward
        #[arg(long)]
        reversed: bool,
    },
    /// Apply bounded model checking to each assertion using an SMT solver.
    SmtCheck {
        #[command(flatten)]
        bounded: BoundedArgs, // universe bounds are unused
        #[command(flatten)]
        solver: SolverArgs,
    },
}

impl InferCommand {
    fn file(&self) -> &str {
        match self {
            InferCommand::Houdini { solver: _, file } => file,
            InferCommand::Qalpha(QalphaArgs { file, .. }) => file,
            InferCommand::Fbii(FbiiArgs {
                qalpha_args: QalphaArgs { file, .. },
                ..
            }) => file,
        }
    }
}

impl Command {
    fn file(&self) -> &str {
        match self {
            Command::Verify(VerifyArgs { file, .. }) => file,
            Command::Infer(InferArgs { infer_cmd, .. }) => infer_cmd.file(),
            Command::UpdrVerify(VerifyArgs { file, .. }) => file,
            Command::Print { file, .. } => file,
            Command::Inline { file, .. } => file,
            Command::SetCheck {
                bounded: BoundedArgs { file, .. },
                ..
            } => file,
            Command::SatCheck(BoundedArgs { file, .. }) => file,
            Command::BddCheck {
                bounded: BoundedArgs { file, .. },
                ..
            } => file,
            Command::SmtCheck {
                bounded: BoundedArgs { file, .. },
                ..
            } => file,
        }
    }
}

#[derive(clap::Parser, Debug)]
#[command(about, long_about=None)]
/// Entrypoint for the temporal-verifier binary, including all commands.
pub struct App {
    #[arg(value_enum, long, default_value_t = ColorOutput::Auto)]
    /// Control color output. Auto disables colors with TERM=dumb or
    /// NO_COLOR=true.
    color: ColorOutput,

    #[command(subcommand)]
    /// Command to run
    command: Command,
}

impl SolverArgs {
    fn get_solver_conf(&self, fname: &String) -> SolverConf {
        let backend_type = match &self.solver {
            SolverType::Z3 => backends::SolverType::Z3,
            SolverType::Cvc5 => backends::SolverType::Cvc5,
            SolverType::Cvc4 => backends::SolverType::Cvc4,
        };

        SolverConf::new(
            backend_type,
            self.smt,
            fname,
            self.timeout,
            Some(self.solver_seed),
        )
    }
}

impl VerifyArgs {
    fn get_solver_conf(&self) -> SolverConf {
        self.solver.get_solver_conf(&self.file)
    }
}

impl App {
    /// Run the application.
    pub fn exec(self) {
        let file = fs::read_to_string(self.command.file()).expect("could not read input file");
        // We make sure paths look like Unix paths on all platforms, otherwise test snapshots don't match.
        let standardized_filename = Path::new(self.command.file()).to_slash_lossy();
        let files = SimpleFile::new(standardized_filename, &file);

        let writer = StandardStream::stderr(match &self.color {
            ColorOutput::Never => ColorChoice::Never,
            ColorOutput::Always => ColorChoice::Always,
            ColorOutput::Auto => ColorChoice::Auto,
        });
        let config = codespan_reporting::term::Config {
            start_context_lines: 3,
            end_context_lines: 3,
            ..Default::default()
        };

        let mut m = match fly::parser::parse(&file) {
            Ok(v) => v,
            Err(err) => {
                let diagnostic = parse_error_diagnostic((), &err);
                terminal::emit(&mut writer.lock(), &config, &files, &diagnostic).unwrap();
                process::exit(1);
            }
        };

        let r = sorts::sort_check_module(&mut m);
        if let Err((err, span)) = r {
            eprintln!("sort checking error:");

            let mut diagnostic = Diagnostic::error().with_message(format!("{err}"));
            if let Some(span) = span {
                diagnostic = diagnostic.with_labels(vec![Label::primary((), span.start..span.end)]);
            }
            terminal::emit(&mut writer.lock(), &config, &files, &diagnostic).unwrap();

            process::exit(1);
        }

        match self.command {
            Command::Print { .. } => {
                // don't inline for printing
                println!("{}", printer::fmt(&m));
            }
            Command::Verify(ref args) => {
                let conf = args.get_solver_conf();
                m.inline_defs();
                let r = verify_module(&conf, &m);
                if args.time {
                    timing::report();
                }
                match r {
                    Ok(()) => println!("verifies!"),
                    Err(err) => {
                        eprintln!("verification errors:");

                        for fail in &err.fails {
                            let diagnostic = fail.diagnostic(());
                            terminal::emit(&mut writer.lock(), &config, &files, &diagnostic)
                                .unwrap();
                        }

                        process::exit(1);
                    }
                }
            }
            Command::Infer(
                ref args @ InferArgs {
                    infer_cmd:
                        InferCommand::Houdini {
                            ref solver,
                            ref file,
                        },
                    ..
                },
            ) => {
                let conf = solver.get_solver_conf(file);
                m.inline_defs();
                let r = houdini::infer_module(&conf, &m);
                if args.time {
                    timing::report();
                }
                match r {
                    Ok(()) => println!("verifies!"),
                    Err(err) => {
                        eprintln!("verification errors:");

                        for fail in &err.fails {
                            let diagnostic = fail.diagnostic(());
                            terminal::emit(&mut writer.lock(), &config, &files, &diagnostic)
                                .unwrap();
                        }

                        process::exit(1);
                    }
                }
            }
            Command::Infer(
                ref args @ InferArgs {
                    infer_cmd: InferCommand::Qalpha(ref qargs),
                    ..
                },
            ) => {
                m.inline_defs();

                // Validate mode-specific requirements
                if qargs.mode == Mode::Auto {
                    eprintln!("auto mode is only supported for fbii command, not qalpha");
                    process::exit(1);
                }

                let fixpoint = if qargs.mode == Mode::Multi {
                    // Validate multi-prefix arguments
                    if qargs.sort.is_empty() {
                        eprintln!("--mode multi requires --sort arguments");
                        process::exit(1);
                    }
                    if qargs.prefix_length.is_none() {
                        eprintln!("--mode multi requires --prefix-length argument");
                        process::exit(1);
                    }
                    if qargs.constant_limit.is_none() {
                        eprintln!("--mode multi requires --constant-limit argument");
                        process::exit(1);
                    }
                    if qargs.total_per_sort.is_none() {
                        eprintln!("--mode multi requires --total-per-sort argument");
                        process::exit(1);
                    }

                    // Validate sort names before creating config
                    for s in &qargs.sort {
                        if !m.signature.sorts.contains(s) {
                            eprintln!("unknown sort '{}' in --sort argument", s);
                            process::exit(1);
                        }
                    }

                    let infer_cfg = Arc::new(qargs.to_cfg(&m, args.infer_cmd.file().to_string()));

                    // Check that qf_body is PDnf
                    if !matches!(infer_cfg.qf_cfg.qf_body, QfBody::PDnf) {
                        eprintln!("--mode multi currently only supports --qf pdnf");
                        process::exit(1);
                    }

                    qalpha_multi_prefix(infer_cfg, &m, !args.no_print_nondet)
                } else {
                    let infer_cfg = Arc::new(qargs.to_cfg(&m, args.infer_cmd.file().to_string()));
                    qalpha_dynamic(infer_cfg, &m, None, !args.no_print_nondet)
                };

                fixpoint.report(!args.no_print_nondet, true);
                if args.time {
                    timing::report();
                }
            }
            Command::Infer(
                ref args @ InferArgs {
                    infer_cmd: InferCommand::Fbii(ref fbargs),
                    ..
                },
            ) => {
                m.inline_defs();
                let bwd_m = reverse_module(&m);
                let cfgs = fbargs.to_cfgs(&m, args.infer_cmd.file().to_string());
                
                if fbargs.qalpha_args.mode == Mode::Auto {
                    // Validate auto-mode arguments
                    if fbargs.qalpha_args.sort.is_empty() {
                        eprintln!("--mode auto requires --sort arguments");
                        process::exit(1);
                    }

                    // Validate sort names before creating config
                    for s in &fbargs.qalpha_args.sort {
                        if !m.signature.sorts.contains(s) {
                            eprintln!("unknown sort '{}' in --sort argument", s);
                            process::exit(1);
                        }
                    }

                    inference::qalpha::fbii::qalpha_fbii_auto(
                        &cfgs,
                        &m,
                        &bwd_m,
                        !fbargs.qalpha_args.smt_cfg.no_disj,
                        SmtTactic::from(fbargs.qalpha_args.smt_cfg.smt_tactic.as_str()),
                        !args.no_print_nondet,
                        fbargs.qalpha_args.auto_min,
                        fbargs.qalpha_args.auto_max,
                    );
                } else {
                    qalpha_fbii(
                        cfgs,
                        &m,
                        &bwd_m,
                        !fbargs.qalpha_args.smt_cfg.no_disj,
                        SmtTactic::from(fbargs.qalpha_args.smt_cfg.smt_tactic.as_str()),
                        !args.no_print_nondet,
                    );
                }
            }
            Command::Inline { .. } => {
                let mut m = m;
                m.inline_defs();
                println!("{}", printer::fmt(&m));
            }
            Command::UpdrVerify(ref args @ VerifyArgs { .. }) => {
                let conf = Arc::new(SingleSolver::new(args.get_solver_conf()));
                let mut updr = Updr::new(conf);
                let _result = updr.search(&m);
            }

            Command::SetCheck {
                bounded,
                compress_traces,
            } => {
                m.inline_defs();
                let back_convert_model = match m.convert_non_bool_relations() {
                    Ok(f) => f,
                    Err(e) => {
                        eprintln!("{e}");
                        process::exit(1)
                    }
                };
                let univ = bounded.get_universe(&m.signature);
                match bounded::set::check(
                    &m,
                    &univ,
                    bounded.depth,
                    compress_traces.into(),
                    bounded.print_timing.unwrap_or(true),
                ) {
                    Ok(CheckerAnswer::Counterexample(models)) => {
                        println!(
                            "found counterexample:\n{}",
                            models_to_string(models.iter().map(back_convert_model))
                        )
                    }
                    Ok(CheckerAnswer::Unknown) => {
                        println!(
                            "answer: safe up to {} for given sort bounds",
                            bounded
                                .depth
                                .map(|d| format!("depth {d}"))
                                .unwrap_or("any depth".to_string())
                        );
                    }
                    Ok(CheckerAnswer::Convergence(())) => {
                        println!("answer: safe forever with given sort bounds")
                    }
                    Err(error) => eprintln!("{error}"),
                }
            }
            Command::SatCheck(bounded) => {
                m.inline_defs();
                let back_convert_model = match m.convert_non_bool_relations() {
                    Ok(f) => f,
                    Err(e) => {
                        eprintln!("{e}");
                        process::exit(1)
                    }
                };
                let depth = match bounded.depth {
                    Some(depth) => depth,
                    None => {
                        eprintln!("sat checker does not support unbounded depth. please specify --depth N on the command line");
                        process::exit(1)
                    }
                };
                let univ = bounded.get_universe(&m.signature);
                match bounded::sat::check(&m, &univ, depth, bounded.print_timing.unwrap_or(true)) {
                    Ok(CheckerAnswer::Counterexample(models)) => {
                        println!(
                            "found counterexample:\n{}",
                            models_to_string(models.iter().map(back_convert_model))
                        )
                    }
                    Ok(CheckerAnswer::Unknown) => {
                        println!("answer: safe up to depth {depth} for given sort bounds")
                    }
                    Ok(CheckerAnswer::Convergence(())) => unreachable!(),
                    Err(error) => eprintln!("{error}"),
                }
            }
            Command::BddCheck { bounded, reversed } => {
                m.inline_defs();
                let back_convert_model = match m.convert_non_bool_relations() {
                    Ok(f) => f,
                    Err(e) => {
                        eprintln!("{e}");
                        process::exit(1)
                    }
                };
                let univ = bounded.get_universe(&m.signature);
                let check = match reversed {
                    false => bounded::bdd::check,
                    true => bounded::bdd::check_reversed,
                };
                match check(
                    &m,
                    &univ,
                    bounded.depth,
                    bounded.print_timing.unwrap_or(true),
                ) {
                    Ok(CheckerAnswer::Counterexample(models)) => {
                        println!(
                            "found counterexample:\n{}",
                            models_to_string(models.iter().map(back_convert_model))
                        )
                    }
                    Ok(CheckerAnswer::Unknown) => {
                        println!(
                            "answer: safe up to {} for given sort bounds",
                            bounded
                                .depth
                                .map(|d| format!("depth {d}"))
                                .unwrap_or("any depth".to_string())
                        );
                    }
                    Ok(CheckerAnswer::Convergence(..)) => {
                        println!("answer: safe forever with given sort bounds")
                    }
                    Err(error) => eprintln!("{error}"),
                }
            }
            Command::SmtCheck { bounded, solver } => {
                m.inline_defs();
                let depth = match bounded.depth {
                    Some(depth) => depth,
                    None => {
                        eprintln!("smt checker does not support unbounded depth. please specify --depth N on the command line");
                        process::exit(1)
                    }
                };
                match bounded::smt::check(
                    &m,
                    &solver.get_solver_conf(&file),
                    depth,
                    bounded.print_timing.unwrap_or(true),
                ) {
                    Ok(CheckerAnswer::Counterexample(models)) => {
                        println!("found counterexample:\n{}", models_to_string(models))
                    }
                    Ok(CheckerAnswer::Unknown) => {
                        println!("answer: safe up to depth {depth} for given sort bounds")
                    }
                    Ok(CheckerAnswer::Convergence(())) => unreachable!(),
                    Err(error) => eprintln!("{error}"),
                }
            }
        }
    }
}

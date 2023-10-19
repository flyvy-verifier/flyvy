// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! The temporal-verifier binary's command-line interface.

use bounded::checker::CheckerAnswer;
use codespan_reporting::diagnostic::{Diagnostic, Label};
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
use fly::syntax::{Signature, Sort};
use fly::{self, parser::parse_error_diagnostic, printer, sorts, timing};
use inference::basics::{parse_quantifier, InferenceConfig, QfBody};
use inference::houdini;
use inference::qalpha::fixpoint::{self, qalpha_dynamic};
use inference::qalpha::quant::QuantifierConfig;
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
    #[arg(long)]
    /// Use a custom prefix, given either by the sort ordering (via `--sort`) or by exact quantifiers (via `--quantifier`).
    /// Otherwise, use the sort ordering found in the loaded module
    custom_quant: bool,

    #[arg(short, long)]
    /// Sorts in the order they should appear in the quantifier prefix
    sort: Vec<String>,

    #[arg(short, long)]
    /// Quantifiers in the form `<quantifier: F/E/*> <sort> <var1> <var2> ...`
    quantifier: Vec<String>,
}

impl QuantifierConfigArgs {
    fn to_cfg(&self, sig: &Signature) -> QuantifierConfig {
        let mut quantifiers;
        let mut sorts: Vec<usize>;
        let mut counts: Vec<usize>;
        if !self.custom_quant {
            sorts = (0..sig.sorts.len()).collect();
            quantifiers = vec![None; sorts.len()];
            counts = vec![fixpoint::defaults::MAX_SAME_SORT; sorts.len()];
        } else if !self.sort.is_empty() {
            sorts = self
                .sort
                .iter()
                .map(|s| sig.sort_idx(&Sort::Uninterpreted(s.clone())))
                .collect();
            quantifiers = vec![None; sorts.len()];
            counts = vec![fixpoint::defaults::MAX_SAME_SORT; sorts.len()];
        } else {
            quantifiers = vec![];
            sorts = vec![];
            counts = vec![];
            for quantifier_spec in &self.quantifier {
                let r = parse_quantifier(sig, quantifier_spec);
                match r {
                    Ok((q, sort, count)) => {
                        quantifiers.push(q);
                        sorts.push(sig.sort_idx(&sort));
                        counts.push(count);
                    }
                    Err(err) => panic!("{err}"),
                }
            }
        }
        QuantifierConfig::new(Arc::new(sig.clone()), quantifiers, sorts, &counts)
    }
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct InferenceConfigArgs {
    #[command(flatten)]
    q_cfg_args: QuantifierConfigArgs,

    #[arg(long)]
    /// Instead on parallizing the solvers for each query, try them one by one
    /// in a sequential fallback fashion.
    fallback: bool,

    #[arg(long)]
    /// Defines the type of quantifier-free body (cnf/dnf/pdnf)
    qf_body: Option<String>,

    #[arg(long)]
    /// Whether the search should should only attempt to prove safety
    property_directed: bool,

    #[arg(long)]
    /// Do not search gradually for the quantified serach space needed to find an invariant,
    /// and instead begin with the maximal domain matching the specification.
    no_search: bool,

    #[arg(long)]
    /// Defines the maximal size of the quantifier prefix
    max_size: Option<usize>,

    #[arg(long)]
    /// Defines the maximal number of existential quantifiers
    max_exist: Option<usize>,

    #[arg(long)]
    /// For a quantifier-free body in CNF, determines the maximal number of clauses
    clauses: Option<usize>,

    #[arg(long)]
    /// For a quantifier-free body in CNF, determines the maximal size of each clause
    clause_size: Option<usize>,

    #[arg(long)]
    /// For a quantifier-free body in DNF, determines the maximal number of cubes
    cubes: Option<usize>,

    #[arg(long)]
    /// For a quantifier-free body in DNF, determines the maximal size of each cube
    cube_size: Option<usize>,

    #[arg(long)]
    /// For a quantifier-free body which supports unit clauses/cubes, like pDNF,
    /// this determines the maximal size of non-unit clauses/cubes
    non_unit: Option<usize>,

    #[arg(long)]
    /// The maximal nesting depth of terms in the vocabulary (unbounded if not provided)
    nesting: Option<usize>,

    #[arg(long, action)]
    /// Do not include equality terms in the vocabulary
    no_include_eq: bool,

    #[arg(long)]
    /// Do not try to decompose the transition relation disjunctively
    no_disj: bool,

    #[arg(long)]
    /// Perform SMT queries gradually
    gradual_smt: bool,

    #[arg(long)]
    /// Perform SMT queries gradually and minimally
    minimal_smt: bool,

    #[arg(long)]
    /// Try to extend model traces before looking for CEX in the frame
    extend_width: Option<usize>,

    #[arg(long)]
    /// Try to extend model traces before looking for CEX in the frame
    extend_depth: Option<usize>,

    #[arg(long)]
    /// Launch no new runs after safety has been proven
    until_safe: bool,

    #[arg(long)]
    /// Abort a run once it is evident that safety cannot be proven
    abort_unsafe: bool,

    #[arg(long)]
    /// Grow the domain of quantified lemmas by this factor each iteration (default: 5)
    growth_factor: Option<usize>,
}

impl InferenceConfigArgs {
    fn to_cfg(&self, sig: &Signature, fname: String) -> InferenceConfig {
        let qf_body = match &self.qf_body {
            None => fixpoint::defaults::QF_BODY,
            Some(qf_body_str) => {
                if qf_body_str.to_lowercase() == *"cnf" {
                    QfBody::CNF
                } else if qf_body_str.to_lowercase() == *"pdnf" {
                    QfBody::PDnf
                } else if qf_body_str.to_lowercase() == *"dnf" {
                    QfBody::Dnf
                } else {
                    panic!("Invalid choice of quantifier-free body!")
                }
            }
        };

        let mut cfg = InferenceConfig {
            fname,
            fallback: self.fallback,
            cfg: self.q_cfg_args.to_cfg(sig),
            qf_body,
            property_directed: self.property_directed,
            max_size: self.max_size.unwrap_or(fixpoint::defaults::MAX_QUANT),
            max_existentials: self.max_exist,
            clauses: self.clauses,
            clause_size: self.clause_size,
            cubes: self.cubes,
            cube_size: self.cube_size,
            non_unit: self.non_unit,
            nesting: self.nesting,
            include_eq: !self.no_include_eq,
            disj: !self.no_disj,
            gradual_smt: self.gradual_smt || self.minimal_smt,
            minimal_smt: self.minimal_smt,
            extend_depth: self.extend_depth,
            no_search: self.no_search,
            until_safe: self.until_safe,
            abort_unsafe: self.abort_unsafe,
            growth_factor: self.growth_factor,
        };

        cfg.clauses = cfg.clauses.or(fixpoint::defaults::MAX_CLAUSES);
        cfg.clause_size = cfg.clause_size.or(fixpoint::defaults::MAX_CLAUSE_SIZE);
        cfg.cubes = cfg.cubes.or(fixpoint::defaults::MAX_CUBES);
        cfg.cube_size = cfg.cube_size.or(fixpoint::defaults::MAX_CUBE_SIZE);
        cfg.non_unit = cfg.non_unit.or(fixpoint::defaults::MAX_NON_UNIT);

        cfg
    }
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct QalphaArgs {
    #[command(flatten)]
    infer_cfg: InferenceConfigArgs,

    /// File name for a .fly file
    file: String,
}

#[derive(clap::Subcommand, Clone, Debug, PartialEq, Eq)]
enum InferCommand {
    /// Run Houdini
    Houdini {
        /// File name for a .fly file
        file: String,
    },
    /// Run quantified-alpha-from-below
    Qalpha(QalphaArgs),
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct InferArgs {
    #[command(flatten)]
    solver: SolverArgs,

    #[arg(long, global = true)]
    /// Print timing statistics
    time: bool,

    #[arg(long)]
    /// Don't print the found invariant (for testing)
    no_print_invariant: bool,

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

impl BoundedArgs {
    /// Parses the arguments in self.bound into a universe size map.
    ///
    /// Ensures that every sort in the given signature is given a bound.
    fn get_universe(&self, sig: &Signature) -> HashMap<String, usize> {
        let mut universe: HashMap<String, usize> = HashMap::new();
        for b in &self.bound {
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
            InferCommand::Houdini { file } => file,
            InferCommand::Qalpha(QalphaArgs { file, .. }) => file,
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
            self.solver_seed,
        )
    }
}

impl VerifyArgs {
    fn get_solver_conf(&self) -> SolverConf {
        self.solver.get_solver_conf(&self.file)
    }
}

impl InferArgs {
    fn get_solver_conf(&self) -> SolverConf {
        self.solver
            .get_solver_conf(&self.infer_cmd.file().to_string())
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
                    infer_cmd: InferCommand::Houdini { .. },
                    ..
                },
            ) => {
                let conf = args.get_solver_conf();
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
                let infer_cfg = Arc::new(
                    qargs
                        .infer_cfg
                        .to_cfg(&m.signature, args.infer_cmd.file().to_string()),
                );
                qalpha_dynamic(infer_cfg, &m, !args.no_print_invariant);
                if args.time {
                    timing::report();
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

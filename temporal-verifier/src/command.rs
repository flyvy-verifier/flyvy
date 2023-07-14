// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! The temporal-verifier binary's command-line interface.

use codespan_reporting::diagnostic::{Diagnostic, Label};
use path_slash::PathExt;
use std::collections::HashMap;
use std::fs::create_dir_all;
use std::path::Path;
use std::sync::Arc;
use std::{fs, path::PathBuf, process};

use clap::Args;
use codespan_reporting::{
    files::SimpleFile,
    term::{
        self as terminal,
        termcolor::{ColorChoice, StandardStream},
    },
};
use fly::syntax::Signature;
use fly::{self, parser::parse_error_diagnostic, printer, sorts, timing};
use inference::basics::{parse_quantifier, InferenceConfig, QfBody};
use inference::fixpoint::{fixpoint_multi_qf_body, fixpoint_single_qf_body};
use inference::houdini;
use inference::quant::QuantifierConfig;
use inference::updr::Updr;
use solver::backends::{self, GenericBackend};
use solver::conf::SolverConf;
use solver::{log_dir, solver_path};
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
    #[arg(short, long)]
    /// Quantifier in the form `<quantifier: F/E/*> <sort> <var1> <var2> ...`.
    quantifier: Vec<String>,
}

impl QuantifierConfigArgs {
    fn to_cfg(&self, sig: &Signature) -> QuantifierConfig {
        let mut quantifiers = vec![];
        let mut sorts = vec![];
        let mut counts = vec![];
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
        QuantifierConfig::new(Arc::new(sig.clone()), quantifiers, sorts, &counts)
    }
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct InferenceConfigArgs {
    #[command(flatten)]
    q_cfg_args: QuantifierConfigArgs,

    #[arg(long)]
    qf_body: String,

    #[arg(long)]
    max_size: Option<usize>,

    #[arg(long)]
    max_exist: Option<usize>,

    #[arg(long)]
    clauses: Option<usize>,

    #[arg(long)]
    clause_size: Option<usize>,

    #[arg(long)]
    cubes: Option<usize>,

    #[arg(long)]
    cube_size: Option<usize>,

    #[arg(long)]
    non_unit: Option<usize>,

    #[arg(long)]
    nesting: Option<usize>,

    #[arg(long, action)]
    no_include_eq: bool,

    #[arg(long, action)]
    search: bool,

    #[arg(long)]
    /// Try to decompose the transition relation disjunctively
    disj: bool,

    #[arg(long)]
    /// Perform SMT queries gradually
    gradual_smt: bool,

    #[arg(long)]
    /// Perform SMT queries gradually and minimally
    minimal_smt: bool,

    #[arg(long)]
    /// Advance the prestate frontier gradually
    gradual_advance: bool,

    #[arg(long)]
    /// Try to find individually inductive lemmas
    indiv: bool,

    #[arg(long)]
    /// Try to extend model traces before looking for CEX in the frame
    extend_width: Option<usize>,

    #[arg(long)]
    /// Try to extend model traces before looking for CEX in the frame
    extend_depth: Option<usize>,
}

impl InferenceConfigArgs {
    fn to_cfg(&self, sig: &Signature) -> InferenceConfig {
        let qf_body = if self.qf_body.to_lowercase() == *"cnf" {
            QfBody::CNF
        } else if self.qf_body.to_lowercase() == *"pdnf" {
            QfBody::PDnf
        } else if self.qf_body.to_lowercase() == *"pdnf-naive" {
            QfBody::PDnfNaive
        } else {
            panic!("Invalid choice of quantifier-free body!")
        };

        InferenceConfig {
            cfg: self.q_cfg_args.to_cfg(sig),
            qf_body,
            max_size: self.max_size,
            max_existentials: self.max_exist,
            clauses: self.clauses,
            clause_size: self.clause_size,
            cubes: self.cubes,
            cube_size: self.cube_size,
            non_unit: self.non_unit,
            nesting: self.nesting,
            include_eq: !self.no_include_eq,
            disj: self.disj,
            gradual_smt: self.gradual_smt || self.minimal_smt,
            minimal_smt: self.minimal_smt,
            gradual_advance: self.gradual_advance,
            indiv: self.indiv,
            extend_width: self.extend_width,
            extend_depth: self.extend_depth,
        }
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
                    eprintln!("unknown sort name {} in bound {}", sort_name, b);
                    process::exit(1);
                }
                if let Ok(bound_size) = bound_size.parse::<usize>() {
                    universe.insert(sort_name, bound_size);
                } else {
                    eprintln!("could not parse bound as integer in {}", b);
                    process::exit(1);
                }
            } else {
                eprintln!("expected exactly one '=' in bound {}", b);
                process::exit(1);
            }
        }
        if let Some(unbounded_sort) = sig.sorts.iter().find(|&s| !universe.contains_key(s)) {
            eprintln!(
                "need a bound for sort {} on the command line, as in --bound {}=N",
                unbounded_sort, unbounded_sort
            );
            process::exit(1);
        }
        universe
    }
}

#[derive(clap::Subcommand, Clone, Debug, PartialEq, Eq)]
enum Command {
    Verify(VerifyArgs),
    UpdrVerify(VerifyArgs),
    Infer(InferArgs),
    Print {
        /// File name for a .fly file
        file: String,
    },
    Inline {
        /// File name for a .fly file
        file: String,
    },
    SetCheck {
        #[command(flatten)]
        bounded: BoundedArgs,
        /// Whether to only keep track of the last state of the trace
        #[arg(long)]
        compress_traces: bool,
    },
    SatCheck(BoundedArgs),
    BddCheck {
        #[command(flatten)]
        bounded: BoundedArgs,
        /// Whether to search from the unsafe states inward
        #[arg(long)]
        reversed: bool,
    },
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

fn solver_default_bin(t: SolverType) -> &'static str {
    match t {
        SolverType::Z3 => "z3",
        SolverType::Cvc5 => "cvc5",
        SolverType::Cvc4 => "cvc4",
    }
}

impl SolverArgs {
    fn get_solver_conf(&self, fname: &String) -> SolverConf {
        let backend_type = match &self.solver {
            SolverType::Z3 => backends::SolverType::Z3,
            SolverType::Cvc5 => backends::SolverType::Cvc5,
            SolverType::Cvc4 => backends::SolverType::Cvc4,
        };
        let solver_bin = solver_path(solver_default_bin(self.solver));
        let tee: Option<PathBuf> = if self.smt {
            let dir = log_dir(Path::new(fname));
            create_dir_all(&dir).expect("could not create log dir");
            if let Ok(rdir) = dir.read_dir() {
                for entry in rdir {
                    match entry {
                        Err(_) => {}
                        Ok(name) => {
                            _ = fs::remove_file(name.path());
                        }
                    }
                }
            }
            Some(dir)
        } else {
            None
        };
        let mut backend = GenericBackend::new(backend_type, &solver_bin);
        backend.timeout_ms(if self.timeout > 0 {
            Some(self.timeout * 1000)
        } else {
            None
        });
        backend.seed(self.solver_seed);
        SolverConf { backend, tee }
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

        let r = sorts::sort_check_and_infer(&mut m);
        if let Err((err, span)) = r {
            eprintln!("sort checking error:");

            let mut diagnostic = Diagnostic::error().with_message(format!("{}", err));
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
                let conf = args.get_solver_conf();
                m.inline_defs();
                let infer_cfg = qargs.infer_cfg.to_cfg(&m.signature);
                if qargs.infer_cfg.search {
                    fixpoint_multi_qf_body(infer_cfg, &conf, &m)
                } else {
                    let fixpoint = fixpoint_single_qf_body(infer_cfg, &conf, &m);
                    if args.no_print_invariant {
                        fixpoint.test_report();
                    } else {
                        fixpoint.report();
                    }
                }
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
                let conf = Arc::new(args.get_solver_conf());
                let mut updr = Updr::new(conf);
                let _result = updr.search(&m);
            }

            Command::SetCheck {
                bounded,
                compress_traces,
            } => {
                let univ = bounded.get_universe(&m.signature);
                bounded::set::check(
                    &m,
                    &univ,
                    bounded.depth,
                    compress_traces.into(),
                    bounded.print_timing.unwrap_or(true),
                );
            }
            Command::SatCheck(bounded) => {
                let depth = match bounded.depth {
                    Some(depth) => depth,
                    None => {
                        eprintln!("sat checker does not support unbounded depth. please specify --depth N on the command line");
                        process::exit(1)
                    }
                };
                let univ = bounded.get_universe(&m.signature);
                match bounded::sat::check(&m, &univ, depth, bounded.print_timing.unwrap_or(true)) {
                    Ok(bounded::sat::CheckerAnswer::Counterexample) => {}
                    Ok(bounded::sat::CheckerAnswer::Unknown) => {
                        println!("answer: safe up to depth {} for given sort bounds", depth)
                    }
                    Err(error) => eprintln!("{}", error),
                }
            }
            Command::BddCheck { bounded, reversed } => {
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
                    Ok(bounded::bdd::CheckerAnswer::Counterexample(..)) => {}
                    Ok(bounded::bdd::CheckerAnswer::Unknown) => {
                        println!(
                            "answer: safe up to {} for given sort bounds",
                            bounded
                                .depth
                                .map(|d| format!("depth {}", d))
                                .unwrap_or("any depth".to_string())
                        );
                    }
                    Ok(bounded::bdd::CheckerAnswer::Convergence(..)) => {
                        println!("answer: safe forever with given sort bounds")
                    }
                    Err(error) => eprintln!("{}", error),
                }
            }
            Command::SmtCheck { bounded, solver } => {
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
                    Ok(bounded::smt::CheckerAnswer::Counterexample(_)) => {}
                    Ok(bounded::smt::CheckerAnswer::Unknown) => {
                        println!("answer: safe up to depth {} for given sort bounds", depth)
                    }
                    Err(error) => eprintln!("{}", error),
                }
            }
        }
    }
}

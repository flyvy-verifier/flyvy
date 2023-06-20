// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use codespan_reporting::diagnostic::{Diagnostic, Label};
use path_slash::PathExt;
use std::collections::HashMap;
use std::fs::create_dir_all;
use std::io::BufRead;
use std::path::Path;
use std::sync::Arc;
use std::{fs, path::PathBuf, process};

use crate::fly::syntax::Signature;
use crate::inference::atoms;
use crate::inference::lemma;
use crate::inference::quant::QuantifierConfig;
use crate::inference::subsume;
use crate::inference::{houdini, parse_quantifier, InferenceConfig};
use crate::solver::bounded::{interpret, translate, InterpreterResult};
use crate::solver::{log_dir, solver_path, SolverConf};
use crate::timing;
use crate::{
    fly::{self, parser::parse_error_diagonistic, printer, sorts},
    inference::{fixpoint_multi, fixpoint_single, QfBody},
    solver::backends::{self, GenericBackend},
    verify::verify_module,
};
use clap::Args;
use codespan_reporting::{
    files::SimpleFile,
    term::{
        self as terminal,
        termcolor::{ColorChoice, StandardStream},
    },
};

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

#[derive(clap::Subcommand, Clone, Debug, PartialEq, Eq)]
enum Command {
    Verify(VerifyArgs),
    Infer(InferArgs),
    Print {
        /// File name for a .fly file
        file: String,
    },
    Inline {
        /// File name for a .fly file
        file: String,
    },
    BoundedCheck {
        /// File name for a .fly file
        file: String,
        /// Depth to run the checker to
        depth: usize,
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
            Command::Print { file, .. } => file,
            Command::Inline { file, .. } => file,
            Command::BoundedCheck { file, .. } => file,
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

        let mut m = match fly::parse(&file) {
            Ok(v) => v,
            Err(err) => {
                let diagnostic = parse_error_diagonistic((), &err);
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
                    match infer_cfg.qf_body {
                        QfBody::CNF => fixpoint_multi::<
                            subsume::Cnf<atoms::Literal>,
                            lemma::LemmaCnf,
                            Vec<Vec<atoms::Literal>>,
                        >(infer_cfg, &conf, &m),
                        QfBody::PDnf => fixpoint_multi::<
                            subsume::PDnf<atoms::Literal>,
                            lemma::LemmaPDnf,
                            (Vec<atoms::Literal>, Vec<Vec<atoms::Literal>>),
                        >(infer_cfg, &conf, &m),
                        QfBody::PDnfNaive => fixpoint_multi::<
                            subsume::Dnf<atoms::Literal>,
                            lemma::LemmaPDnfNaive,
                            Vec<Vec<atoms::Literal>>,
                        >(infer_cfg, &conf, &m),
                    }
                } else {
                    let fixpoint = match infer_cfg.qf_body {
                        QfBody::CNF => fixpoint_single::<
                            subsume::Cnf<atoms::Literal>,
                            lemma::LemmaCnf,
                            Vec<Vec<atoms::Literal>>,
                        >(infer_cfg, &conf, &m),
                        QfBody::PDnf => fixpoint_single::<
                            subsume::PDnf<atoms::Literal>,
                            lemma::LemmaPDnf,
                            (Vec<atoms::Literal>, Vec<Vec<atoms::Literal>>),
                        >(infer_cfg, &conf, &m),
                        QfBody::PDnfNaive => fixpoint_single::<
                            subsume::Dnf<atoms::Literal>,
                            lemma::LemmaPDnfNaive,
                            Vec<Vec<atoms::Literal>>,
                        >(infer_cfg, &conf, &m),
                    };
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
            Command::BoundedCheck { depth, .. } => {
                let mut universe = HashMap::new();
                let stdin = std::io::stdin();
                for sort in &m.signature.sorts {
                    println!("how large should {} be?", sort);
                    let input = stdin
                        .lock()
                        .lines()
                        .next()
                        .expect("no next line")
                        .expect("could not read next line")
                        .parse::<usize>();
                    match input {
                        Ok(input) => {
                            universe.insert(sort.clone(), input);
                        }
                        Err(_) => {
                            eprintln!("could not parse input as a number");
                            process::exit(1);
                        }
                    }
                }
                match translate(&mut m, &universe) {
                    Err(e) => eprintln!("{}", e),
                    Ok(program) => match interpret(&program, depth) {
                        InterpreterResult::Unknown => println!("no counterexample found"),
                        InterpreterResult::Counterexample(trace) => {
                            eprintln!("found counterexample: {:#?}", trace)
                        }
                    },
                }
            }
        }
    }
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use codespan_reporting::diagnostic::{Diagnostic, Label};
use path_slash::PathExt;
use std::path::Path;
use std::rc::Rc;
use std::{fs, path::PathBuf, process};

use crate::fly::syntax::Signature;
use crate::inference::lemma::QuantifierConfig;
use crate::inference::{houdini, parse_quantifier, InferenceConfig};
use crate::solver::solver_path;
use crate::timing;
use crate::{
    fly::{self, parser::parse_error_diagonistic, printer, sorts},
    inference::run_fixpoint,
    solver::backends::{self, GenericBackend},
    verify::{verify_module, SolverConf},
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
    Cvc,
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
    #[arg(value_enum, long, default_value_t = SolverType::Z3)]
    /// Solver to use (z3, cvc; or use cvc4 or cvc5 to force a particular solver)
    solver: SolverType,

    #[arg(long)]
    /// Full path to output SMT file to
    smt_file: Option<PathBuf>,

    #[arg(long)]
    /// Output smt2 file alongside input file
    smt: bool,
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
    depth: Option<usize>,

    #[arg(long, action)]
    no_include_eq: bool,

    #[arg(short, long)]
    /// Quantifier in the form `<quantifier: F/E/*> <sort> <var1> <var2> ...`.
    quantifier: Vec<String>,
}

impl QuantifierConfigArgs {
    fn to_cfg(&self, sig: &Signature) -> QuantifierConfig {
        let mut quantifiers = vec![];
        let mut sorts = vec![];
        let mut names = vec![];
        for quantifier_spec in &self.quantifier {
            let r = parse_quantifier(sig, quantifier_spec);
            match r {
                Ok((q, sort, q_names)) => {
                    quantifiers.push(q);
                    sorts.push(sort);
                    names.push(q_names);
                }
                Err(err) => panic!("{err}"),
            }
        }
        QuantifierConfig {
            quantifiers,
            sorts,
            names,
            depth: self.depth,
            include_eq: !self.no_include_eq,
        }
    }
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct InferenceConfigArgs {
    #[command(flatten)]
    q_cfg_args: QuantifierConfigArgs,

    #[arg(long, default_value_t = 0)]
    kpdnf_cubes: usize,

    #[arg(long)]
    kpdnf_lit: Option<usize>,
}

impl InferenceConfigArgs {
    fn to_cfg(&self, sig: &Signature) -> InferenceConfig {
        InferenceConfig {
            cfg: self.q_cfg_args.to_cfg(sig),
            kpdnf_cubes: self.kpdnf_cubes,
            kpdnf_lit: self.kpdnf_lit,
        }
    }
}

#[derive(Args, Clone, Debug, PartialEq, Eq)]
struct InferArgs {
    #[command(flatten)]
    solver: SolverArgs,

    #[arg(long)]
    /// Run the Houdini algorithm to infer invariants
    houdini: bool,

    #[command(flatten)]
    infer_cfg: InferenceConfigArgs,

    #[arg(long)]
    /// Print timing statistics
    time: bool,

    #[arg(long)]
    /// Try to extend model traces before looking for CEX in the frame
    extend_models: bool,

    #[arg(long)]
    /// Try to decompose the transition relation disjunctively
    disj: bool,

    /// File name for a .fly file
    file: String,
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
}

impl Command {
    fn file(&self) -> &str {
        match self {
            Command::Verify(VerifyArgs { file, .. }) => file,
            Command::Infer(InferArgs { file, .. }) => file,
            Command::Print { file, .. } => file,
            Command::Inline { file, .. } => file,
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
        SolverType::Cvc | SolverType::Cvc5 => "cvc5",
        SolverType::Cvc4 => "cvc4",
    }
}

impl SolverArgs {
    fn get_solver_conf(&self, fname: &String) -> SolverConf {
        let backend_type = match &self.solver {
            SolverType::Z3 => backends::SolverType::Z3,
            SolverType::Cvc | SolverType::Cvc5 => backends::SolverType::Cvc5,
            SolverType::Cvc4 => backends::SolverType::Cvc4,
        };
        let solver_bin = solver_path(solver_default_bin(self.solver));
        let tee: Option<PathBuf> = if let Some(path) = &self.smt_file {
            Some(path.to_path_buf())
        } else if self.smt {
            let path = PathBuf::from(fname).with_extension("smt2");
            Some(path)
        } else {
            None
        };
        SolverConf {
            backend: GenericBackend::new(backend_type, &solver_bin),
            tee,
        }
    }
}

impl VerifyArgs {
    fn get_solver_conf(&self) -> SolverConf {
        self.solver.get_solver_conf(&self.file)
    }
}

impl InferArgs {
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
                println!("{}", printer::fmt(&m));
            }
            Command::Verify(ref args) => {
                let conf = args.get_solver_conf();
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
            Command::Infer(ref args @ InferArgs { houdini, .. }) => {
                if houdini {
                    let conf = args.get_solver_conf();
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
                } else {
                    let conf = Rc::new(args.get_solver_conf());
                    let infer_cfg = args.infer_cfg.to_cfg(&m.signature);
                    run_fixpoint(infer_cfg, conf, &m, args.extend_models, args.disj);
                    if args.time {
                        timing::report();
                    }
                }
            }
            Command::Inline { .. } => {
                let mut m = m;
                m.inline_defs();
                println!("{}", printer::fmt(&m));
            }
        }
    }
}

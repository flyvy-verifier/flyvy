// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::{env, fs, path::PathBuf, process};

use crate::{
    fly::{
        printer,
        syntax::{self, parse_error_diagonistic},
    },
    solver::backends::{self, GenericBackend},
    verify::{verify_module, SolverConf},
};
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

#[derive(clap::Subcommand, Clone, Debug, PartialEq, Eq)]
enum Command {
    Verify {
        #[arg(long)]
        /// Run Houdini on supplied invariants
        houdini: bool,
        /// File name for a .fly file
        file: String,
    },
    Print {
        /// File name for a .fly file
        file: String,
    },
}

impl Command {
    fn file(&self) -> &str {
        match self {
            Command::Verify { houdini: _, file } => file,
            Command::Print { file } => file,
        }
    }
}

#[derive(clap::Parser, Debug)]
#[command(about, long_about=None)]
pub struct App {
    #[arg(value_enum, long, default_value_t = SolverType::Z3)]
    /// Solver to use (z3, cvc; or use cvc4 or cvc5 to force a particular solver)
    solver: SolverType,

    #[arg(long)]
    /// Full path to output SMT file to
    smt_file: Option<PathBuf>,

    #[arg(long)]
    /// Output smt2 file alongside input file
    smt: bool,

    #[arg(value_enum, long, default_value_t = ColorOutput::Auto)]
    /// Control color output. Auto disables colors with TERM=dumb or
    /// NO_COLOR=true.
    color: ColorOutput,

    #[command(subcommand)]
    /// Command to run
    command: Command,
}

fn env_path_fallback(path: &Option<String>, var: &str, fallback: &str) -> String {
    if let Some(path) = path {
        return path.into();
    }
    if let Some(val) = env::var_os(var) {
        return val.to_string_lossy().into();
    }
    fallback.into()
}

fn solver_env_var(t: SolverType) -> &'static str {
    match t {
        SolverType::Z3 => "Z3_BIN",
        SolverType::Cvc | SolverType::Cvc5 => "CVC5_BIN",
        SolverType::Cvc4 => "CVC4_BIN",
    }
}

fn solver_default_bin(t: SolverType) -> &'static str {
    match t {
        SolverType::Z3 => "z3",
        SolverType::Cvc | SolverType::Cvc5 => "cvc5",
        SolverType::Cvc4 => "cvc4",
    }
}

impl App {
    fn get_solver_conf(&self) -> SolverConf {
        let backend_type = match &self.solver {
            SolverType::Z3 => backends::SolverType::Z3,
            SolverType::Cvc | SolverType::Cvc5 => backends::SolverType::Cvc5,
            SolverType::Cvc4 => backends::SolverType::Cvc4,
        };
        let solver_bin = env_path_fallback(
            // TODO: allow command-line override, which would be Some here
            &None,
            solver_env_var(self.solver),
            solver_default_bin(self.solver),
        );
        let tee: Option<PathBuf> = if let Some(path) = &self.smt_file {
            Some(path.to_path_buf())
        } else if self.smt {
            let path = PathBuf::from(self.command.file()).with_extension("smt2");
            Some(path)
        } else {
            None
        };
        SolverConf {
            backend: GenericBackend::new(backend_type, &solver_bin),
            tee,
        }
    }

    pub fn exec(self) {
        let file = fs::read_to_string(self.command.file()).expect("could not read input file");
        let files = SimpleFile::new(self.command.file(), &file);

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

        let conf = self.get_solver_conf();

        let m = match syntax::parse(&file) {
            Ok(v) => v,
            Err(err) => {
                let diagnostic = parse_error_diagonistic((), &err);
                terminal::emit(&mut writer.lock(), &config, &files, &diagnostic).unwrap();
                process::exit(1);
            }
        };

        match self.command {
            Command::Print { .. } => {
                println!("{}", printer::fmt(&m));
            }
            Command::Verify { houdini, .. } => {
                let r = verify_module(&conf, &m, houdini);
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
        }
    }
}
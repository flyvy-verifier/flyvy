// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::{env, fs, path::PathBuf, process};

use clap::Parser;
use codespan_reporting::{
    files::SimpleFile,
    term::{
        self as terminal,
        termcolor::{ColorChoice, StandardStream},
    },
};
use temporal_verifier::{
    fly::{
        printer,
        syntax::{self, parse_error_diagonistic},
    },
    solver::backends::{self, GenericBackend},
    verify::{verify_module, SolverConf},
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

#[derive(clap::Parser, Debug)]
#[command(about, long_about=None)]
struct Args {
    #[arg(long)]
    /// Apply Houdini to supplied proof invariants
    houdini: bool,

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

    #[arg(long)]
    /// Parse and print the file back
    print: bool,

    /// File name for a .fly file
    file: String,
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

fn get_solver_conf(args: &Args) -> SolverConf {
    let backend_type = match args.solver {
        SolverType::Z3 => backends::SolverType::Z3,
        SolverType::Cvc | SolverType::Cvc5 => backends::SolverType::Cvc5,
        SolverType::Cvc4 => backends::SolverType::Cvc4,
    };
    let solver_bin = env_path_fallback(
        // TODO: allow command-line override, which would be Some here
        &None,
        solver_env_var(args.solver),
        solver_default_bin(args.solver),
    );
    let tee: Option<String> = if let Some(path) = &args.smt_file {
        Some(path.to_string_lossy().to_string())
    } else if args.smt {
        let path = PathBuf::from(&args.file).with_extension("smt2");
        Some(path.to_string_lossy().to_string())
    } else {
        None
    };
    SolverConf {
        backend: GenericBackend::new(backend_type, &solver_bin),
        tee,
    }
}

fn main() {
    let args = Args::parse();

    let file = fs::read_to_string(&args.file).expect("could not read input file");
    let files = SimpleFile::new(&args.file, &file);

    let writer = StandardStream::stderr(match args.color {
        ColorOutput::Never => ColorChoice::Never,
        ColorOutput::Always => ColorChoice::Always,
        ColorOutput::Auto => ColorChoice::Auto,
    });
    let config = codespan_reporting::term::Config {
        start_context_lines: 3,
        end_context_lines: 3,
        ..Default::default()
    };

    let conf = get_solver_conf(&args);

    let m = match syntax::parse(&file) {
        Ok(v) => v,
        Err(err) => {
            let diagnostic = parse_error_diagonistic((), &err);
            terminal::emit(&mut writer.lock(), &config, &files, &diagnostic).unwrap();
            process::exit(1);
        }
    };

    if args.print {
        println!("{}", printer::fmt(&m));
        return;
    }

    let r = verify_module(&conf, &m, args.houdini);
    match r {
        Ok(()) => println!("verifies!"),
        Err(err) => {
            eprintln!("verification errors:");

            for fail in &err.fails {
                let diagnostic = fail.diagnostic(());
                terminal::emit(&mut writer.lock(), &config, &files, &diagnostic).unwrap();
            }

            process::exit(1);
        }
    }
}

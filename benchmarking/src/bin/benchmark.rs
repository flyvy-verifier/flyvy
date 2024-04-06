// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Run all of the examples as benchmarks and report the results in a table.

use std::{fs, path::PathBuf, time::Duration};

use benchmarking::{
    qalpha::{qalpha_benchmarks, QalphaMeasurement},
    report::{load_results, ReportableMeasurement},
    run::{get_examples, BenchmarkConfig, BenchmarkMeasurement},
    time_bench::{compile_flyvy_bin, compile_time_bin, REPO_ROOT_PATH},
};
use clap::{Args, Parser};
use glob::Pattern;

#[derive(Args, Debug, Clone, PartialEq, Eq)]
struct QalphaParams {
    /// Glob pattern over benchmark names to run
    #[arg(short = 'F', long = "filter", default_value = "*")]
    name_glob: String,
    /// Directory to store results in / load results from
    #[arg(long)]
    dir: PathBuf,
    /// Time limit for running each experiment
    #[arg(long, default_value = "600s")]
    time_limit: humantime::Duration,
    /// Repeat each benchmark this number of times
    #[arg(short = 'R', long, default_value = "1")]
    repeat: usize,
    /// Whether to run the benchmarks or load the saved results
    #[arg(long)]
    load: bool,
    /// File to output the results in TSV format to
    #[arg(long)]
    tsv: Option<String>,
}

#[derive(clap::Subcommand, Clone, Debug, PartialEq, Eq)]
enum Command {
    /// Run verification benchmarks with user-supplied invariants.
    Verify {
        /// Time limit for verifying each file.
        #[arg(long, default_value = "60s")]
        time_limit: humantime::Duration,
        /// Solver to use
        #[arg(long, default_value = "z3")]
        solver: String,
        #[arg(long)]
        /// Output results in JSON format
        json: bool,
    },
    /// Run invariant inference benchmarks with qalpha.
    Qalpha(#[command(flatten)] QalphaParams),
}

#[derive(clap::Parser, Debug)]
struct App {
    /// Command to run
    #[command(subcommand)]
    command: Command,
}

fn benchmark_verify(time_limit: Duration, solver: &str) -> Vec<BenchmarkMeasurement> {
    get_examples()
        .into_iter()
        .map(|file| {
            eprintln!(
                "verify {}",
                file.strip_prefix(REPO_ROOT_PATH()).unwrap().display()
            );
            BenchmarkMeasurement::run(
                BenchmarkConfig {
                    command: vec![String::from("verify")],
                    params: vec![format!("--solver={solver}")],
                    file,
                    time_limit,
                },
                None, /* rust_log */
                None, /* output_dir */
            )
        })
        .collect()
}

fn run_qalpha(params: &QalphaParams) -> Vec<QalphaMeasurement> {
    let name_glob = Pattern::new(&params.name_glob).expect("could not parse pattern");
    qalpha_benchmarks(params.time_limit.into())
        .into_iter()
        .filter(|(name, _)| name_glob.matches_path(name))
        .map(|(file, config)| {
            eprintln!("qalpha {}", file.display());
            QalphaMeasurement::run(
                config.clone(),
                Some("info".to_string()),
                params.dir.join(&file),
                params.repeat,
            )
        })
        .collect()
}

impl App {
    fn exec(&self) {
        // make sure `time` is available
        compile_time_bin();
        // make sure `temporal-verifier` is available
        compile_flyvy_bin();
        match &self.command {
            Command::Verify {
                time_limit,
                solver,
                json,
            } => {
                let results = benchmark_verify((*time_limit).into(), solver);
                if *json {
                    println!("{}", BenchmarkMeasurement::to_json(&results));
                } else {
                    BenchmarkMeasurement::print_table(&results);
                }
            }
            Command::Qalpha(params) => {
                let results: Vec<QalphaMeasurement> = if params.load {
                    load_results(&params.name_glob, &params.dir)
                } else {
                    run_qalpha(params)
                };
                if let Some(fname) = &params.tsv {
                    let out = QalphaMeasurement::as_tsv(&results);
                    fs::write(fname, out).expect("could not write tsv to file");
                } else {
                    QalphaMeasurement::print_table(&results);
                }
            }
        }
    }
}

fn main() {
    let app = App::parse();
    app.exec();
}

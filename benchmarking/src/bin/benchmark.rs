// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Run all of the examples as benchmarks and report the results in a table.

use std::{fs, path::PathBuf, time::Duration};

use benchmarking::{
    qalpha::{qalpha_benchmarks, OverrideParams, QalphaMeasurement},
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
    /// Directory to store results in, or load results from
    #[arg(long)]
    dir: PathBuf,
    /// Time limit for running each experiment
    #[arg(long, default_value = "600s")]
    time_limit: humantime::Duration,
    /// Repeat each benchmark this number of times
    #[arg(short = 'R', long, default_value = "1")]
    repeat: usize,
    /// Whether to run the benchmarks or load saved results
    #[arg(long)]
    load: bool,
    /// File to output the results in TSV format to
    #[arg(long)]
    tsv: Option<String>,
    /// Whether to use the baseline datastructure instead of LSet
    #[arg(long)]
    baseline: bool,
    /// Whether to use an alternative context in inference
    #[arg(long)]
    use_contexts: bool,
    /// Overrides simulation depth in executions
    #[arg(long)]
    sim_depth: Option<usize>,
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
    /// Run or load invariant inference benchmarks with qalpha and report the results in a table.
    ///
    /// The table produced by this command has one row per benchmark, and contains the following columns:
    ///
    /// - example: the name of the file defining the first-order transition system;
    ///
    /// - #: the number of trials performed for this benchmark;
    ///
    /// - LSet: "✓" if an LSet data-structure was used, or "-" if a baseline data-structure was used instead;
    ///
    /// - outcome: "timeout" if all trials in the benchmark timed-out, empty otherwise;
    ///
    /// - time (s): the total runtime of the least-fixpoint computation;
    ///
    /// - quantifiers: the quantifier structure of formulas in the first-order language considered;
    ///
    /// - qf body: the quantifier-free body of formulas in the first-order language considered.
    ///   In our experiments we use k-pDNF as defined by P-FOL-IC3, with a restricted number of literals in the pDNF clause;
    ///
    /// - language: the approximate number of formulas in the first-order language considered, induced by the transition system and the language parameters;
    ///
    /// - % weaken: the percentage of time spent weakening formulas during the run (as opposed to searching for counter-exmaples to induction);
    ///
    /// - lfp: the number of formulas in the computed least-fixpoint;
    ///
    /// - reduced: the number of formulas in a subset of the least-fixpoint sufficient to semantically imply the rest;
    ///
    /// - max: the maximal number of formulas in the representation of an abstract element encountered throughout the run;
    ///
    /// - × cpu: the CPU utilization factor;
    ///
    /// - memory: the maximal amount of RAM used throughout the run.
    ///
    /// Since we often run multiple trials of the same least-fixpoint computation, we report each of the variable statistics
    /// (e.g., "time", "% weaken") as _median_ ± _deviation_. This is done by first computing the statistic for each individual trial,
    /// finding the median, and then computing the maximal distance from the median value to the value in any trial —
    /// which give us the deviation. This guarantees that the value of the statistic in all trials indeed falls within _median_ ± _deviation_.
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
    let override_params = OverrideParams {
        baseline: params.baseline,
        use_contexts: params.use_contexts,
        sim_depth: params.sim_depth,
    };
    qalpha_benchmarks(params.time_limit.into(), &override_params)
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

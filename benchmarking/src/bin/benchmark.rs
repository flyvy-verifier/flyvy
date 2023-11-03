// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Run all of the examples as benchmarks and report the results in a table.

use std::time::Duration;

use benchmarking::{
    run::{get_examples, BenchmarkMeasurement},
    time_bench::{compile_flyvy_bin, compile_time_bin, REPO_ROOT_PATH},
};
use clap::Parser;

#[derive(clap::Subcommand, Clone, Debug, PartialEq, Eq)]
enum Command {
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
                vec![String::from("verify")],
                vec![format!("--solver={solver}")],
                file,
                time_limit,
                None, /* output_dir */
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
                    BenchmarkMeasurement::print_table(results);
                }
            }
        }
    }
}

fn main() {
    let app = App::parse();
    app.exec();
}

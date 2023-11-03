// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Library for running and reporting benchmark measurements.

use std::{collections::HashMap, ffi::OsStr, path::PathBuf, time::Duration};

use crate::{
    measurement::RunMeasurement,
    time_bench::{Time, REPO_ROOT_PATH},
};

use tabled::settings::{
    object::{Columns, Object, Rows},
    width::MinWidth,
    Alignment, Color, Modify, Style, Width,
};
use walkdir::WalkDir;

/// A benchmark configuration and its resulting measurement.
#[derive(Debug, Clone)]
pub struct BenchmarkMeasurement {
    command: Vec<String>,
    params: String,
    file: PathBuf,
    measurement: RunMeasurement,
}

impl BenchmarkMeasurement {
    /// Run flyvy on a single benchmark, isolated to its own process.
    ///
    /// command + args form the arguments to temporal-verifier. These are split
    /// only for display purposes in the table; `command` is something like
    /// `infer qalpha` while `args` has other configuration and quantifiers for
    /// each sort, for example.
    ///
    /// file is added to the end of the argument list and also becomes a
    /// separate column in the results.
    ///
    /// time_limit is a maximum time to wait for the benchmark before killing
    /// it.
    pub fn run(
        command: Vec<String>,
        args: Vec<String>,
        file: PathBuf,
        time_limit: Duration,
        output_dir: Option<PathBuf>,
    ) -> Self {
        let mut timer = flyvy_timer();
        timer.timeout(time_limit);
        timer.args(&command);
        timer.args(&args);
        timer.arg(&file);
        if let Some(output_dir) = output_dir {
            timer.output_dir(output_dir);
        }
        let measurement = timer.run().expect("error getting timing");
        BenchmarkMeasurement {
            command,
            params: args.join(" "),
            file,
            measurement,
        }
    }

    /// Header used for printing table. Make sure this stays in sync with [`Self::row`].
    fn header() -> Vec<String> {
        [
            "command", "file", "outcome", "time s", "cpu util", "solver %", "mem", "params",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect()
    }

    fn success(&self) -> &'static str {
        if self.measurement.timed_out {
            "timeout"
        } else if self.measurement.success {
            ""
        } else {
            "fail"
        }
    }

    fn row(&self) -> Vec<String> {
        let file_name = self
            .file
            .strip_prefix(REPO_ROOT_PATH().join("temporal-verifier/examples"))
            .unwrap_or(self.file.strip_prefix(REPO_ROOT_PATH()).unwrap());
        let measure = &self.measurement;
        let real_time = measure.real_time.as_secs_f64();
        vec![
            format!("{}", self.command.join(" ")),
            format!("{}", file_name.display()),
            format!("{}", self.success()),
            format!("{real_time:0.1}"),
            format!("{:0.1}×", measure.cpu_utilization()),
            format!("{:0.0}%", measure.subprocess_utilization() * 100.0),
            format!("{}MB", measure.max_mem_mb()),
            format!("{}", self.params),
        ]
    }

    /// Print a nicely-formatting table from a list of results.
    pub fn print_table(results: Vec<Self>) {
        let mut success_counts = HashMap::<&str, usize>::new();
        for r in &results {
            let mut key = r.success();
            if key == "" {
                key = "ok";
            }
            *success_counts.entry(key).or_default() += 1;
        }
        let total = results.len();

        let mut rows = vec![Self::header()];
        rows.extend(results.iter().map(|r| r.row()));

        let mut table = tabled::builder::Builder::from(rows).build();
        let numerical_columns = Columns::new(3..=6);
        table
            .with(Style::rounded())
            .with(Modify::new(Columns::single(2).not(Rows::first())).with(Color::FG_RED))
            .with(Modify::new(numerical_columns).with(Alignment::right()))
            .with(MinWidth::new(150))
            .with(Width::truncate(300));
        println!("{table}");
        println!(
            "total:    {total}
ok:       {ok}
timeout:  {timeout}
fail:     {fail}",
            ok = success_counts.get("ok").unwrap_or(&0),
            timeout = success_counts.get("timeout").unwrap_or(&0),
            fail = success_counts.get("fail").unwrap_or(&0)
        );
    }
}

/// Create an instance of Time that runs temporal-verifier
fn flyvy_timer() -> Time {
    Time::new(REPO_ROOT_PATH().join("target/release/temporal-verifier"))
}

/// Get all the .fly examples from `temporal-verifier/examples`.
pub fn get_examples() -> Vec<PathBuf> {
    let root = REPO_ROOT_PATH();
    let examples_dir = root.join("temporal-verifier/examples");
    WalkDir::new(examples_dir)
        .sort_by_file_name()
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file() && e.path().extension() == Some(OsStr::new("fly")))
        .map(|e| e.into_path())
        .collect()
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Parse and report benchmarking measurement results.

use itertools::Itertools;
use std::fs;
use std::path::{Path, PathBuf};
use std::{collections::HashMap, fs::File};
use walkdir::{DirEntry, WalkDir};

use tabled::settings::{
    object::{Columns, Object, Rows},
    width::MinWidth,
    Alignment, Color, Modify, Style, Width,
};

use glob::Pattern;

use crate::qalpha::QalphaMeasurement;
use crate::run::{BenchmarkConfig, BenchmarkMeasurement};

use crate::{measurement::RunMeasurement, time_bench::REPO_ROOT_PATH};

/// Load all benchmark runs files in the given directory, recursively.
///
/// Loads a config.json and measurement.json from each subdirectory.
pub fn load_results<M: ReportableMeasurement>(name_glob: &str, dir: &Path) -> Vec<M> {
    let name_glob = Pattern::new(name_glob).expect("could not parse pattern");
    WalkDir::new(dir)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_dir() && name_glob.matches_path(e.path()))
        .filter_map(|entry| M::load(entry))
        .collect()
}

/// A runnbale measurement that can be reported in a table
pub trait ReportableMeasurement: Sized {
    /// Header used for printing table. Make sure this stays in sync with [`BenchmarkMeasurement::row`].
    fn header() -> Vec<String>;

    /// Load the measurement if the given ntry contains one
    fn load(entry: DirEntry) -> Option<Self>;

    /// The success status of the measurement
    fn success(&self) -> &'static str;

    /// The table row(s) representing the measurement
    fn rows(&self) -> Vec<Vec<String>>;
}

fn maybe_strip_prefix(prefix: &str, s: &Path) -> PathBuf {
    s.strip_prefix(prefix).unwrap_or(s).to_path_buf()
}

/// Print a nicely-formatting table from a list of results.
pub fn print_table<M: ReportableMeasurement>(results: Vec<M>) {
    let mut success_counts = HashMap::<&str, usize>::new();
    for r in &results {
        let mut key = r.success();
        if key == "" {
            key = "ok";
        }
        *success_counts.entry(key).or_default() += 1;
    }
    let total = results.len();

    let mut rows = vec![M::header()];
    rows.extend(results.iter().flat_map(|r| r.rows()));

    let mut table = tabled::builder::Builder::from(rows).build();
    let numerical_columns = Columns::new(3..=6);
    table
        .with(Style::rounded())
        .with(Modify::new(Columns::single(2).not(Rows::first())).with(Color::FG_RED))
        .with(Modify::new(numerical_columns).with(Alignment::right()))
        .with(MinWidth::new(150))
        .with(Width::truncate(500));
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

impl ReportableMeasurement for BenchmarkMeasurement {
    fn header() -> Vec<String> {
        [
            "command", "file", "outcome", "time s", "cpu util", "solver %", "mem", "params",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect()
    }

    fn load(entry: DirEntry) -> Option<Self> {
        // only process entries that contain measurements
        #[allow(clippy::nonminimal_bool)]
        if !fs::metadata(entry.path().join("measurement.json")).is_ok() {
            return None;
        }
        // for each entry, load its BenchmarkMeasurement from config.json and measurement.json
        let config: BenchmarkConfig =
            serde_json::from_reader(File::open(entry.path().join("config.json")).unwrap())
                .expect("could not parse config.json");
        let measurement: RunMeasurement =
            serde_json::from_reader(File::open(entry.path().join("measurement.json")).unwrap())
                .expect("could not parse measurement.json");
        Some(BenchmarkMeasurement {
            config,
            measurement,
        })
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

    fn rows(&self) -> Vec<Vec<String>> {
        let file_name = maybe_strip_prefix(
            "temporal-verifier/examples",
            &maybe_strip_prefix(REPO_ROOT_PATH().to_str().unwrap(), &self.config.file),
        );
        let measure = &self.measurement;
        let real_time = measure.real_time.as_secs_f64();
        vec![vec![
            format!("{}", self.config.command.join(" ")),
            format!("{}", file_name.display()),
            format!("{}", self.success()),
            format!("{real_time:0.1}"),
            format!("{:0.1}×", measure.cpu_utilization()),
            format!("{:0.0}%", measure.subprocess_utilization() * 100.0),
            format!("{}MB", measure.max_mem_mb()),
            format!("{}", self.config.params.join(" ")),
        ]]
    }
}

impl ReportableMeasurement for QalphaMeasurement {
    fn header() -> Vec<String> {
        [
            "command", "file", "outcome", "time s", "cpu util", "solver %", "mem", "params",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect()
    }

    fn load(entry: DirEntry) -> Option<Self> {
        // only process entries that contain a configuration
        if fs::metadata(entry.path().join("config.json")).is_err() {
            return None;
        }

        let sub_dirs: Vec<DirEntry> = WalkDir::new(entry.path())
            .min_depth(1)
            .max_depth(1)
            .into_iter()
            .filter_entry(|e| e.file_type().is_dir())
            .filter_map(|e| e.ok())
            .sorted_by_key(|e| e.file_name().to_os_string())
            .collect();
        // only process entries that contain properly arranged measurements
        if sub_dirs.iter().enumerate().any(|(i, e)| {
            e.file_name() != format!("{i}").as_str()
                || fs::metadata(e.path().join("measurement.json")).is_err()
        }) {
            return None;
        }

        let config: BenchmarkConfig =
            serde_json::from_reader(File::open(entry.path().join("config.json")).unwrap())
                .expect("could not parse config.json");
        let measurements = sub_dirs
            .iter()
            .map(|e| {
                serde_json::from_reader(File::open(e.path().join("measurement.json")).unwrap())
                    .expect("could not parse measurement.json")
            })
            .collect();

        Some(QalphaMeasurement {
            config,
            measurements,
        })
    }

    fn success(&self) -> &'static str {
        if self.measurements.iter().all(|m| m.timed_out) {
            "timeout"
        } else if self.measurements.iter().any(|m| m.success) {
            ""
        } else {
            "fail"
        }
    }

    fn rows(&self) -> Vec<Vec<String>> {
        let file_name = maybe_strip_prefix(
            "temporal-verifier/examples",
            &maybe_strip_prefix(REPO_ROOT_PATH().to_str().unwrap(), &self.config.file),
        );

        self.measurements
            .iter()
            .map(|measure| {
                let real_time = measure.real_time.as_secs_f64();
                vec![
                    format!("{}", self.config.command.join(" ")),
                    format!("{}", file_name.display()),
                    format!("{}", self.success()),
                    format!("{real_time:0.1}"),
                    format!("{:0.1}×", measure.cpu_utilization()),
                    format!("{:0.0}%", measure.subprocess_utilization() * 100.0),
                    format!("{}MB", measure.max_mem_mb()),
                    format!("{}", self.config.params.join(" ")),
                ]
            })
            .collect()
    }
}

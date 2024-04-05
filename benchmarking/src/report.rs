// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Parse and report benchmarking measurement results.

use itertools::Itertools;
use std::fs;
use std::ops::{Add, Div, Sub};
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
    /// Load the measurement if the given ntry contains one
    fn load(entry: DirEntry) -> Option<Self>;

    /// Print a nicely-formatting table from a list of results.
    fn print_table(results: Vec<Self>);
}

fn maybe_strip_prefix(prefix: &str, s: &Path) -> PathBuf {
    s.strip_prefix(prefix).unwrap_or(s).to_path_buf()
}

impl BenchmarkMeasurement {
    /// Header used for printing table. Make sure this stays in sync with [`BenchmarkMeasurement::row`].
    fn header() -> Vec<String> {
        [
            "command", "file", "outcome", "time s", "cpu util", "solver %", "mem", "params",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect()
    }

    /// The success status of the measurement
    fn success(&self) -> &'static str {
        if self.measurement.timed_out {
            "timeout"
        } else if self.measurement.success {
            ""
        } else {
            "fail"
        }
    }

    /// The table row(s) representing the measurement
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

impl ReportableMeasurement for BenchmarkMeasurement {
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

    fn print_table(results: Vec<Self>) {
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
}

fn median_and_range<V, I>(values: I) -> Option<(V, V)>
where
    V: Copy + PartialOrd + Add<Output = V> + Sub<Output = V> + Div<V, Output = V> + From<u8>,
    I: Iterator<Item = V>,
{
    let sorted: Vec<_> = values.sorted_by(|a, b| a.partial_cmp(b).unwrap()).collect();
    if sorted.is_empty() {
        return None;
    }

    let n = sorted.len();
    let median = if n % 2 == 0 {
        (sorted[n / 2] + sorted[n / 2 - 1]) / V::from(2)
    } else {
        sorted[n / 2]
    };

    let range = [median - sorted[0], sorted[n - 1] - median]
        .into_iter()
        .max_by(|a, b| a.partial_cmp(b).unwrap())
        .unwrap();

    Some((median, range))
}

impl QalphaMeasurement {
    fn header() -> Vec<String> {
        [
            "example",
            "LSet",
            "outcome",
            "time (s)",
            "quantifiers",
            "qf body",
            "lang size",
            "in weaken (s)",
            "in weaken (%)",
            "lfp size",
            "max size",
            "× cpu util",
            "mem",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect()
    }

    fn success(&self) -> &'static str {
        if self.measurements.iter().all(|m| m.run.timed_out) {
            "timeout"
        } else if self.measurements.iter().any(|m| m.run.success) {
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

        let lset = if self.config.params.contains(&"--baseline".to_string()) {
            "-"
        } else {
            "✓"
        }
        .to_string();
        let name = file_name.display().to_string();
        let outcome = self.success().to_string();

        let (time_med, time_rng) = median_and_range(
            self.measurements
                .iter()
                .map(|m| m.run.real_time.as_secs_f64()),
        )
        .unwrap();
        let real_time = format!("{time_med:0.1} ± {time_rng:>5.1}");

        // Quantifier structure
        let quants: String = self
            .config
            .params
            .iter()
            .enumerate()
            .filter(|(_, s)| *s == "--quantifier")
            .map(|(i, _)| {
                let parts: Vec<_> = self.config.params[i + 1].split(' ').collect();
                let quant = match parts[0].chars().nth(0).unwrap() {
                    '*' => "∃∀",
                    'F' => " ∀",
                    'E' => " ∃",
                    _ => unreachable!(),
                };

                format!("{quant}^{}", parts[2])
            })
            .join(" ");

        // Quantifier-free body
        let clause_size: usize = self
            .config
            .params
            .iter()
            .find_map(|s| s.strip_prefix("--clause-size=").map(|n| n.parse().unwrap()))
            .unwrap();
        let cubes: usize = self
            .config
            .params
            .iter()
            .find_map(|s| s.strip_prefix("--cubes=").map(|n| n.parse().unwrap()))
            .unwrap();

        let lang_size = self
            .measurements
            .iter()
            .find_map(|m| m.language_size.clone());
        if let Some(size) = &lang_size {
            assert!(self
                .measurements
                .iter()
                .all(|m| !m.language_size.as_ref().is_some_and(|s| s != size)))
        }

        let in_weaken_secs: Option<Vec<f64>> =
            self.measurements.iter().map(|m| m.in_weaken).collect();
        let in_weaken_s = in_weaken_secs.as_ref().map(|v| {
            let (med, rng) = median_and_range(v.iter().copied()).unwrap();
            format!("{med:0.1} ± {rng:>5.1}")
        });

        let in_weaken_per = in_weaken_secs.as_ref().map(|v| {
            let (med, rng) = median_and_range(
                v.iter()
                    .zip(&self.measurements)
                    .map(|(w, m)| *w / m.run.real_time.as_secs_f64() * 100.0),
            )
            .unwrap();
            format!("{med:0.0}% ± {rng:>2.0}%")
        });

        let lfp_size = self.measurements.iter().find_map(|m| m.lfp_size);
        if let Some(size) = lfp_size {
            assert!(self
                .measurements
                .iter()
                .all(|m| !m.lfp_size.is_some_and(|s| s != size)))
        }

        let max_size = median_and_range(self.measurements.iter().filter_map(|m| m.max_size))
            .map(|(med, rng)| format!("{med:0.1} ± {rng:>5.1}"));

        let (cpu_med, cpu_rng) =
            median_and_range(self.measurements.iter().map(|m| m.run.cpu_utilization())).unwrap();
        let cpu_util = format!("{cpu_med:0.0} ± {cpu_rng:>2.0}");

        let (mem_med, mem_rng) =
            median_and_range(self.measurements.iter().map(|m| m.run.max_mem_mb())).unwrap();
        let mem = format!("{mem_med:0.0} ± {mem_rng:>3.0} MB");

        vec![vec![
            name,
            lset,
            outcome,
            real_time,
            quants,
            format!("{}-pDNF, {clause_size}-clause", cubes + 1),
            lang_size.unwrap_or_default(),
            in_weaken_s.unwrap_or_default(),
            in_weaken_per.unwrap_or_default(),
            lfp_size.map(|size| format!("{size}")).unwrap_or_default(),
            max_size.unwrap_or_default(),
            cpu_util,
            mem,
        ]]
    }
}

impl ReportableMeasurement for QalphaMeasurement {
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

        Some(QalphaMeasurement::new(
            &entry.into_path(),
            config,
            measurements,
        ))
    }

    fn print_table(results: Vec<Self>) {
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
        rows.extend(results.iter().flat_map(|r| r.rows()));

        let mut table = tabled::builder::Builder::from(rows).build();
        table
            .with(Style::rounded())
            .with(Modify::new(Columns::single(1)).with(Alignment::center()))
            .with(Modify::new(Columns::single(2).not(Rows::first())).with(Color::FG_RED))
            .with(Modify::new(Columns::single(3)).with(Alignment::right()))
            .with(Modify::new(Columns::new(7..=12)).with(Alignment::right()))
            .with(Modify::new(Rows::single(0)).with(Alignment::center()))
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
}

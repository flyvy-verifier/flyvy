//! Define the qalpha experiments
use std::{
    collections::HashMap,
    path::{Path, PathBuf},
    time::Duration,
};

use crate::run::BenchmarkConfig;

fn example_path(file: &Path) -> PathBuf {
    PathBuf::from("temporal-verifier/examples").join(file)
}

/// Return a list of configured qalpha benchmarks for the examples.
///
/// Each benchmark is represented as a tuple of a name and a configuration. The
/// name is used as the output directory so it should be unique across
/// benchmarks.
pub fn qalpha_benchmarks() -> Vec<(PathBuf, BenchmarkConfig)> {
    let file = PathBuf::from("lockserver.fly");
    let config = BenchmarkConfig {
        command: ["infer", "qalpha"]
            .into_iter()
            .map(|s| s.to_string())
            .collect(),
        params: [
            "--custom-quant",
            "--until-safe",
            "--sort=node",
            "--bound",
            "node=3",
            "--cubes=3",
            "--cube-size=3",
            "--non-unit=3",
        ]
        .into_iter()
        .map(|s| s.to_string())
        .collect(),
        file: example_path(&file),
        time_limit: Duration::from_secs(60),
    };

    let benchmarks = vec![(file, config)];
    check_unique_benchmarks(&benchmarks);
    benchmarks
}

fn check_unique_benchmarks(benchmarks: &[(PathBuf, BenchmarkConfig)]) {
    let mut by_name: HashMap<&Path, Vec<BenchmarkConfig>> = HashMap::new();
    for (name, config) in benchmarks {
        by_name.entry(name).or_default().push(config.clone());
    }
    for (name, configs) in by_name {
        if configs.len() > 1 {
            panic!(
                "benchmark name {} is not unique: {configs:?}",
                name.display()
            );
        }
    }
}

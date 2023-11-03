//! Define the qalpha experiments
use std::{path::PathBuf, time::Duration};

use crate::run::BenchmarkConfig;

fn example_path(file: &str) -> PathBuf {
    PathBuf::from("temporal-verifier/examples").join(file)
}

/// Return a list of configured qalpha benchmarks for the examples
pub fn qalpha_benchmarks() -> Vec<(String, BenchmarkConfig)> {
    let file = "lockserver.fly";
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
        file: example_path(file),
        time_limit: Duration::from_secs(60),
    };
    vec![(file.to_string(), config)]
}

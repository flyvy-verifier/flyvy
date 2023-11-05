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

struct SortBound {
    sort: String,
    bound: usize,
}

struct QalphaConfig {
    file: PathBuf,
    bounds: Vec<SortBound>,
    cubes: usize,
    cube_size: usize,
    non_unit: usize,
    last_exist: usize,
    time_limit: Duration,
}

fn sort_bounds(spec: &str) -> Vec<SortBound> {
    spec.split(' ')
        .map(|s| {
            let mut parts = s.split('=');
            let sort = parts.next().unwrap();
            let bound = parts.next().unwrap().parse().unwrap();
            SortBound {
                sort: sort.to_string(),
                bound,
            }
        })
        .collect()
}

impl QalphaConfig {
    fn params(&self) -> Vec<String> {
        let mut args = vec!["--until-safe".to_string()];
        for SortBound { sort, bound } in &self.bounds {
            args.push(format!("--sort={sort}"));
            args.push(format!("--bound={sort}={bound}"));
        }
        args.push(format!("--cubes={}", self.cubes));
        args.push(format!("--cube-size={}", self.cube_size));
        args.push(format!("--non-unit={}", self.non_unit));
        args.push(format!("--last-exist={}", self.last_exist));
        args
    }

    pub fn benchmark(&self) -> BenchmarkConfig {
        BenchmarkConfig {
            command: vec!["infer".to_string(), "qalpha".to_string()],
            params: self.params(),
            file: example_path(&self.file),
            time_limit: self.time_limit,
        }
    }

    /// Give this benchmark a systematic path that includes enough information
    /// to (hopefully) make it unique.
    pub fn full_path(&self) -> PathBuf {
        let bound = self.bounds.iter().map(|b| b.bound).max().unwrap_or(0);
        PathBuf::from(format!(
            "{}/bound-{bound}-last-exist-{}",
            self.file.display(),
            self.last_exist,
        ))
    }
}

/// Convert a list of QalphaConfig to benchmarks with systematic names.
///
/// Automatically names multiple configurations for the same fly file using
/// [`QalphaConfig::full_path`].
fn named_benchmarks(config: Vec<QalphaConfig>) -> Vec<(PathBuf, BenchmarkConfig)> {
    let mut by_file: HashMap<PathBuf, Vec<_>> = HashMap::new();
    config
        .into_iter()
        .for_each(|config| by_file.entry(config.file.clone()).or_default().push(config));
    by_file
        .into_iter()
        .flat_map(|(_, configs)| {
            if configs.len() == 1 {
                let config = &configs[0];
                vec![(config.file.clone(), config.benchmark())]
            } else {
                configs
                    .into_iter()
                    .map(|config| (config.full_path(), config.benchmark()))
                    .collect()
            }
        })
        .collect()
}

/// Return a list of configured qalpha benchmarks for the examples.
///
/// Each benchmark is represented as a tuple of a name and a configuration. The
/// name is used as the output directory so it should be unique across
/// benchmarks.
pub fn qalpha_benchmarks() -> Vec<(PathBuf, BenchmarkConfig)> {
    let configs = vec![QalphaConfig {
        file: PathBuf::from("lockserver.fly"),
        bounds: sort_bounds("node=3"),
        cubes: 3,
        cube_size: 3,
        non_unit: 3,
        last_exist: 1,
        time_limit: Duration::from_secs(60),
    }];

    let benchmarks = named_benchmarks(configs);
    check_unique_benchmarks(&benchmarks);
    benchmarks
}

/// Check that the names for all the benchmarks are unique (to avoid results
/// from one benchmark overriding an earlier one).
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

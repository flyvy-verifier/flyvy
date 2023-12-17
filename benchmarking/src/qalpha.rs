// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Define the qalpha experiments
use std::{
    collections::HashMap,
    path::{Path, PathBuf},
    time::Duration,
};

use crate::run::BenchmarkConfig;

/// Return a list of configured qalpha benchmarks for the examples.
///
/// Each benchmark is represented as a tuple of a name and a configuration. The
/// name is used as the output directory so it should be unique across
/// benchmarks.
pub fn qalpha_benchmarks(
    safety_time_limit: Duration,
    fixpoint_time_limit: Duration,
) -> Vec<(PathBuf, BenchmarkConfig)> {
    let configs = vec![
        QalphaConfig {
            file: PathBuf::from("fol/lockserv.fly"),
            quantifiers: sort_counts("node=2"),
            cubes: 3,
            cube_size: 1,
            non_unit: 0,
            last_exist: 0,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/toy_consensus_forall.fly"),
            quantifiers: sort_counts("node=1 value=2"),
            cubes: 3,
            cube_size: 1,
            non_unit: 0,
            last_exist: 0,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/ring_id.fly"),
            quantifiers: sort_counts("node=3"),
            cubes: 3,
            cube_size: 1,
            non_unit: 0,
            last_exist: 0,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/sharded_kv.fly"),
            quantifiers: sort_counts("key=1 node=2 value=2"),
            cubes: 3,
            cube_size: 1,
            non_unit: 0,
            last_exist: 0,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/ticket.fly"),
            quantifiers: sort_counts("thread=2 ticket=2"),
            cubes: 5,
            cube_size: 1,
            non_unit: 0,
            last_exist: 0,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/learning_switch.fly"),
            quantifiers: sort_counts("node=4"),
            cubes: 4,
            cube_size: 1,
            non_unit: 0,
            last_exist: 0,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/consensus_wo_decide.fly"),
            quantifiers: sort_counts("node=3 value=1"),
            cubes: 3,
            cube_size: 1,
            non_unit: 0,
            last_exist: 0,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("consensus_forall.fly"),
            quantifiers: sort_counts("node=3 value=1"),
            cubes: 3,
            cube_size: 1,
            non_unit: 0,
            last_exist: 0,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/cache.fly"),
            quantifiers: sort_counts("address=2 core=2 value=2"),
            cubes: 5,
            cube_size: 1,
            non_unit: 0,
            last_exist: 0,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/sharded_kv_no_lost_keys.fly"),
            quantifiers: sort_counts("key=1 node=1 value=1"),
            cubes: 2,
            cube_size: 1,
            non_unit: 0,
            last_exist: 2,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/toy_consensus_epr.fly"),
            quantifiers: sort_counts("value=2 quorum=1 node=1"),
            cubes: 3,
            cube_size: 1,
            non_unit: 0,
            last_exist: 2,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/consensus_epr.fly"),
            quantifiers: sort_counts("quorum=1 node=3 value=1"),
            cubes: 3,
            cube_size: 1,
            non_unit: 0,
            last_exist: 3,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/client_server_ae.fly"),
            quantifiers: sort_counts("node=1 response=1 request=1"),
            cubes: 2,
            cube_size: 2,
            non_unit: 1,
            last_exist: 1,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/paxos_epr.fly"),
            quantifiers: sort_counts("round=2 value=2 quorum=1 node=1"),
            cubes: 4,
            cube_size: 3,
            non_unit: 1,
            last_exist: 2,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/flexible_paxos_epr.fly"),
            quantifiers: sort_counts("round=2 value=2 quorum_2=1 node=1"),
            cubes: 4,
            cube_size: 3,
            non_unit: 1,
            last_exist: 2,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/multi_paxos_epr.fly"),
            quantifiers: sort_counts("inst=1 round=2 value=2 quorum=1 node=2"),
            cubes: 4,
            cube_size: 3,
            non_unit: 1,
            last_exist: 3,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/stoppable_paxos_epr.fly"),
            quantifiers: sort_counts("inst=2 votemap=1 round=2 value=2 quorum=1 node=2"),
            cubes: 5,
            cube_size: 3,
            non_unit: 1,
            last_exist: 3,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/fast_paxos_epr.fly"),
            quantifiers: sort_counts("round=2 value=2 quorum_c=1 quorum_f=1 node=1"),
            cubes: 5,
            cube_size: 3,
            non_unit: 1,
            last_exist: 2,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/vertical_paxos_epr.fly"),
            quantifiers: sort_counts("round=2 value=2 config=1 quorum=1 node=1"),
            cubes: 6,
            cube_size: 3,
            non_unit: 2,
            last_exist: 3,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/bosco_3t_safety.fly"),
            quantifiers: sort_counts("value=1 value=2 quorum_b=1 node=2"),
            cubes: 5,
            cube_size: 5,
            non_unit: 2,
            last_exist: 4,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/firewall.fly"),
            quantifiers: sort_counts("node=1 node=1"),
            cubes: 2,
            cube_size: 2,
            non_unit: 1,
            last_exist: 1,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/ring_id_not_dead.fly"),
            quantifiers: sort_counts("node=2 node=1 id=1"),
            cubes: 3,
            cube_size: 3,
            non_unit: 1,
            last_exist: 3,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/client_server_db_ae.fly"),
            quantifiers: sort_counts("db_request_id=1 node=2 response=1 request=1 node=1"),
            cubes: 3,
            cube_size: 2,
            non_unit: 1,
            last_exist: 1,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/hybrid_reliable_broadcast_cisa.fly"),
            quantifiers: sort_counts("quorum_a=1 node=1 quorum_b=1 node=1"),
            cubes: 6,
            cube_size: 4,
            non_unit: 2,
            last_exist: 2,
            sim: Default::default(),
        },
        QalphaConfig {
            file: PathBuf::from("fol/block_cache_system_frozen_async.fly"),
            quantifiers: sort_counts("node=2 req_id=2 ref=1 location=2 ref=1"),
            cubes: 4,
            cube_size: 2,
            non_unit: 2,
            last_exist: 2,
            sim: Default::default(),
        },
    ];

    let benchmarks = named_benchmarks(configs, safety_time_limit, fixpoint_time_limit);
    check_unique_benchmarks(&benchmarks);
    benchmarks
}

fn example_path(file: &Path) -> PathBuf {
    PathBuf::from("temporal-verifier/examples").join(file)
}

struct SortCount {
    sort: String,
    count: usize,
}

#[allow(dead_code)]
enum SimulationBound {
    None,
    Sum(usize),
    Exact(Vec<SortCount>),
}

impl SimulationBound {
    fn params(&self) -> Vec<String> {
        match self {
            SimulationBound::None => vec![],
            SimulationBound::Sum(bound_sum) => vec![format!("--bound-sum={bound_sum}")],
            SimulationBound::Exact(bounds) => bounds
                .iter()
                .flat_map(|SortCount { sort, count }| {
                    ["--bound".to_string(), format!("{sort}={count}")]
                })
                .collect(),
        }
    }
}

struct SimulationConfig {
    bound: SimulationBound,
    depth: Option<usize>,
    guided: bool,
}

impl SimulationConfig {
    fn params(&self) -> Vec<String> {
        let mut params = self.bound.params();
        if let Some(d) = self.depth {
            params.push(format!("--depth={d}"));
        }
        if self.guided {
            params.push("--guided".to_string())
        }
        params
    }
}

impl Default for SimulationConfig {
    fn default() -> Self {
        Self {
            bound: SimulationBound::None,
            depth: Some(5),
            guided: true,
        }
    }
}

/// A configuration for a run of qalpha
struct QalphaConfig {
    file: PathBuf,
    quantifiers: Vec<SortCount>,
    cubes: usize,
    cube_size: usize,
    non_unit: usize,
    last_exist: usize,
    sim: SimulationConfig,
}

fn command() -> Vec<String> {
    vec!["infer".to_string(), "qalpha".to_string()]
}
fn sort_counts(spec: &str) -> Vec<SortCount> {
    spec.split(' ')
        .map(|s| {
            let mut parts = s.split('=');
            let sort = parts.next().unwrap();
            let count = parts.next().unwrap().parse().unwrap();
            SortCount {
                sort: sort.to_string(),
                count,
            }
        })
        .collect()
}

impl QalphaConfig {
    fn params(&self, sim: &SimulationConfig, strategy: &str) -> Vec<String> {
        let mut args = vec![];
        for SortCount { sort, count } in &self.quantifiers {
            args.extend(["--quantifier".to_string(), format!("* {sort} {count}")]);
        }
        args.push(format!("--cubes={}", self.cubes));
        args.push(format!("--cube-size={}", self.cube_size));
        args.push(format!("--non-unit={}", self.non_unit));
        args.push(format!("--last-exist={}", self.last_exist));
        args.extend(sim.params());
        args.push(format!("--strategy={strategy}"));
        args
    }

    pub fn benchmarks(
        &self,
        safety_time_limit: Duration,
        fixpoint_time_limit: Duration,
    ) -> Vec<(PathBuf, BenchmarkConfig)> {
        vec![
            // Safety benchmark (property directed)
            (
                self.full_path("safety"),
                BenchmarkConfig {
                    command: command(),
                    params: self.params(&self.sim, "weaken-pd"),
                    file: example_path(&self.file),
                    time_limit: safety_time_limit,
                },
            ),
            // Fixpoint benchmark
            (
                self.full_path("fixpoint"),
                BenchmarkConfig {
                    command: command(),
                    params: self.params(&self.sim, "weaken"),
                    file: example_path(&self.file),
                    time_limit: fixpoint_time_limit,
                },
            ),
        ]
    }

    /// Give this benchmark a systematic path that includes enough information
    /// to (hopefully) make it unique.
    fn full_path(&self, sub_name: &str) -> PathBuf {
        PathBuf::from(format!("{}/{sub_name}", self.file.display()))
    }
}

/// Convert a list of QalphaConfig to benchmarks with systematic names.
///
/// Automatically names multiple configurations for the same fly file using
/// [`QalphaConfig::full_path`].
fn named_benchmarks(
    configs: Vec<QalphaConfig>,
    safety_time_limit: Duration,
    fixpoint_time_limit: Duration,
) -> Vec<(PathBuf, BenchmarkConfig)> {
    configs
        .into_iter()
        .flat_map(|config| config.benchmarks(safety_time_limit, fixpoint_time_limit))
        .collect()
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

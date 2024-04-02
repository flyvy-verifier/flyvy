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
pub fn qalpha_benchmarks(time_limit: Duration) -> Vec<(PathBuf, BenchmarkConfig)> {
    let configs = vec![
        QalphaConfig {
            file: PathBuf::from("fol/lockserv.fly"),
            quantifiers: "F node 2",
            clause_size: 3,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/toy_consensus_forall.fly"),
            quantifiers: "F node 1; F value 2",
            clause_size: 3,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/ring_id.fly"),
            quantifiers: "F node 3",
            clause_size: 3,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/sharded_kv.fly"),
            quantifiers: "F key 1; F node 2; F value 2",
            clause_size: 3,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/ticket.fly"),
            quantifiers: "F thread 2; F ticket 2",
            clause_size: 5,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/learning_switch.fly"),
            quantifiers: "F node 4",
            clause_size: 4,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/consensus_wo_decide.fly"),
            quantifiers: "F node 3",
            clause_size: 3,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/consensus_forall.fly"),
            quantifiers: "F node 3; F value 1",
            clause_size: 3,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/cache.fly"),
            quantifiers: "F address 2; F core 2; F value 2",
            clause_size: 5,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/sharded_kv_no_lost_keys.fly"),
            quantifiers: "F key 1; * node 1; * value 1",
            clause_size: 2,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/toy_consensus_epr.fly"),
            quantifiers: "F value 2; * quorum 1; F node 1",
            clause_size: 3,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/consensus_epr.fly"),
            quantifiers: "* quorum 1; F node 3; F value 1",
            clause_size: 3,
            cubes: 0,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/client_server_ae.fly"),
            quantifiers: "F node 1; F response 1; * request 1",
            clause_size: 1,
            cubes: 1,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/paxos_epr.fly"),
            quantifiers: "F round 2; F value 2; * quorum 1; * node 1",
            clause_size: 3,
            cubes: 1,
            nesting: Some(1),
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/flexible_paxos_epr.fly"),
            quantifiers: "F round 2; F value 2; * quorum_2 1; * node 1",
            clause_size: 3,
            cubes: 1,
            nesting: Some(1),
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/multi_paxos_epr.fly"),
            quantifiers: "F inst 1; F round 2; F value 2; * quorum 1; * node 2",
            clause_size: 3,
            cubes: 1,
            nesting: Some(2),
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/fast_paxos_epr.fly"),
            quantifiers: "F round 2; F value 2; * quorum_c 1; * quorum_f 1; * node 1",
            clause_size: 4,
            cubes: 1,
            nesting: Some(1),
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/stoppable_paxos_epr.fly"),
            quantifiers: "F inst 2; F votemap 1; F round 2; F value 2; * quorum 1; * node 2",
            clause_size: 5,
            cubes: 1,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/vertical_paxos_epr.fly"),
            quantifiers: "F round 2; F value 2; * config 1; * quorum 1; * node 1",
            clause_size: 5,
            cubes: 2,
            nesting: Some(2),
            sim: Default::default(),
            fragment: Fragment::Epr,
        },
        QalphaConfig {
            file: PathBuf::from("fol/bosco_3t_safety.fly"),
            quantifiers: "F value 1; * value 2; * quorum_b 1; * node 2",
            clause_size: 5,
            cubes: 2,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::None,
        },
        QalphaConfig {
            file: PathBuf::from("fol/firewall.fly"),
            quantifiers: "F node 1; * node 1",
            clause_size: 1,
            cubes: 1,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::None,
        },
        QalphaConfig {
            file: PathBuf::from("fol/ring_id_not_dead.fly"),
            quantifiers: "* node 2; F node 1; * id 1",
            clause_size: 3,
            cubes: 3,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::None,
        },
        QalphaConfig {
            file: PathBuf::from("fol/client_server_db_ae.fly"),
            quantifiers: "F db_request_id 1; F node 2; F response 1; * request 1; * node 1",
            clause_size: 3,
            cubes: 1,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::None,
        },
        QalphaConfig {
            file: PathBuf::from("fol/hybrid_reliable_broadcast_cisa.fly"),
            quantifiers: "* quorum_a 1; F node 1; * quorum_b 1; * node 1",
            clause_size: 4,
            cubes: 2,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::None,
        },
        QalphaConfig {
            file: PathBuf::from("fol/block_cache_system_frozen_async.fly"),
            quantifiers: "F node 2; F req_id 2; F ref 1; F location 1; * ref 1; * location 1",
            clause_size: 4,
            cubes: 1,
            nesting: None,
            sim: Default::default(),
            fragment: Fragment::None,
        },
    ];

    let benchmarks = named_benchmarks(configs, time_limit);
    check_unique_benchmarks(&benchmarks);
    benchmarks
}

fn example_path(file: &Path) -> PathBuf {
    PathBuf::from("temporal-verifier/examples").join(file)
}

enum Fragment {
    Epr,
    None,
}

impl ToString for Fragment {
    fn to_string(&self) -> String {
        match self {
            Fragment::Epr => "epr".to_string(),
            Fragment::None => "none".to_string(),
        }
    }
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
            depth: None,
            guided: false,
        }
    }
}

/// A configuration for a run of qalpha
struct QalphaConfig<'a> {
    file: PathBuf,
    quantifiers: &'a str,
    clause_size: usize,
    cubes: usize,
    nesting: Option<usize>,
    sim: SimulationConfig,
    fragment: Fragment,
}

fn command() -> Vec<String> {
    vec!["infer".to_string(), "qalpha".to_string()]
}

#[allow(dead_code)]
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

fn quantifier_param(spec: &str) -> impl Iterator<Item = String> + '_ {
    spec.split("; ")
        .flat_map(|s| ["--quantifier".to_string(), s.to_string()])
}

impl<'a> QalphaConfig<'a> {
    fn params(&self, sim: &SimulationConfig, strategy: &str, baseline: bool) -> Vec<String> {
        let mut args = vec![];
        args.extend(quantifier_param(self.quantifiers));
        args.push(format!("--clause-size={}", self.clause_size));
        args.push(format!("--cubes={}", self.cubes));
        if let Some(n) = self.nesting {
            args.push(format!("--nesting={n}"));
        }
        args.extend(sim.params());
        args.push(format!("--strategy={strategy}"));
        if baseline {
            args.push("--baseline".to_string());
        }
        args
    }

    pub fn benchmarks(&self, time_limit: Duration) -> Vec<(PathBuf, BenchmarkConfig)> {
        [false, true]
            .into_iter()
            .flat_map(|baseline| {
                [
                    // Safety benchmark (property directed)
                    (
                        self.full_path("safety", baseline),
                        BenchmarkConfig {
                            command: command(),
                            params: self.params(&self.sim, "weaken-pd", false),
                            file: example_path(&self.file),
                            time_limit,
                        },
                    ),
                    // Fixpoint benchmark
                    (
                        self.full_path("fixpoint", baseline),
                        BenchmarkConfig {
                            command: command(),
                            params: self.params(&self.sim, "weaken", baseline),
                            file: example_path(&self.file),
                            time_limit,
                        },
                    ),
                ]
            })
            .collect()
    }

    /// Give this benchmark a systematic path that includes enough information
    /// to (hopefully) make it unique.
    fn full_path(&self, sub_name: &str, baseline: bool) -> PathBuf {
        let mut path_string = format!(
            "{}/{}-{sub_name}",
            self.file.display(),
            self.fragment.to_string(),
        );
        if baseline {
            path_string = format!("{path_string}-baseline");
        }
        PathBuf::from(path_string)
    }
}

/// Convert a list of QalphaConfig to benchmarks with systematic names.
///
/// Automatically names multiple configurations for the same fly file using
/// [`QalphaConfig::full_path`].
fn named_benchmarks(
    configs: Vec<QalphaConfig>,
    time_limit: Duration,
) -> Vec<(PathBuf, BenchmarkConfig)> {
    configs
        .into_iter()
        .flat_map(|config| config.benchmarks(time_limit))
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

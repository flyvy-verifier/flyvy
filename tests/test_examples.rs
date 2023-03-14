// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

#![allow(clippy::needless_return)]

use std::{
    collections::HashMap,
    env,
    ffi::OsStr,
    fmt::Display,
    fs::{self, File},
    io::{self, BufRead},
    path::{Path, PathBuf},
    process::Command,
};

use clap::Parser;
use lazy_static::lazy_static;
use regex::Regex;
use serde_derive::Deserialize;
use temporal_verifier::solver::solver_path;
use walkdir::WalkDir;

const SOLVERS_TO_TEST: [&str; 3] = ["z3", "cvc4", "cvc5"];

lazy_static! {
    static ref SOLVER_VERSION_VARS: HashMap<String, String> = {
        let mut versions = HashMap::new();
        let re = Regex::new(r#"(.*)_VERSION="(.*)""#).unwrap();
        for line in fs::read_to_string("tools/solver-versions.sh")
            .expect("could not find tools/solver-versions.sh")
            .lines()
        {
            if line.starts_with('#') || line.is_empty() {
                continue;
            }
            let m = re
                .captures(line)
                .expect("malformed line in solver-versions.sh");
            let solver = m.get(1).unwrap().as_str();
            let version = m.get(2).unwrap().as_str();
            versions.insert(solver.to_string(), version.to_string());
        }
        versions
    };
}

fn expected_version(solver: &str) -> String {
    let version = SOLVER_VERSION_VARS
        .get(&solver.to_uppercase())
        .expect("unexpected solver {solver} (not in tools/solver-versions.sh)");
    if solver == "z3" {
        format!("Z3 version {version}")
    } else if solver == "cvc4" {
        format!("CVC4 version {version}")
    } else if solver == "cvc5" {
        format!("cvc5 version {version}")
    } else {
        panic!("unexpected solver {solver}")
    }
}

fn get_version(solver: &str) -> String {
    let bin = solver_path(solver);
    let version_out = Command::new(bin).arg("--version").output();
    let version = match version_out {
        Ok(out) => String::from_utf8(out.stdout)
            .unwrap()
            .lines()
            .next()
            .expect("no output from --version")
            .to_string(),
        Err(_) => return format!("({solver} not found)"),
    };
    let version_re = Regex::new(r"(Z3|CVC4|cvc5) version [0-9.]*").unwrap();
    match version_re.captures(&version) {
        Some(capture) => capture.get(0).unwrap().as_str().to_string(),
        None => panic!("unexpected --version output"),
    }
}

/// Returns true if versions match. On version mismatch, prints the mismatch to
/// stderr for debugging.
fn check_version(solver: &str) -> bool {
    let expected = expected_version(solver);
    let actual = get_version(solver);
    if let Some(s) = env::var_os("TEST_STRICT_VERSIONS") {
        if s == OsStr::new("true") {
            // cause the test to fail
            assert_eq!(
                expected, actual,
                "installed {solver} version does not match"
            );
        }
    }
    if expected != actual {
        eprintln!("solver version mismatch:");
        eprintln!("  expected: {expected}");
        eprintln!("  actual: {actual}");
    }
    return expected == actual;
}

#[derive(Deserialize, Debug, Clone, clap::Parser)]
struct TestCfg {
    /// Assert that verification fails.
    #[arg(long)]
    #[serde(default)]
    expect_fail: bool,

    /// Automatically run this test with all SMT solvers.
    #[arg(long)]
    #[serde(default)]
    all_solvers: bool,

    /// Give this test a name (used in the snapshot file name)
    #[arg(long)]
    name: Option<String>,

    /// Arguments to be passed to the verifier.
    #[arg(last = true)]
    args: Vec<String>,
}

impl TestCfg {
    fn append_to_name(&mut self, s: &str) {
        self.name = match &self.name {
            Some(name) => Some(format!("{name}.{s}")),
            None => Some(s.to_string()),
        };
    }

    fn solver(&self) -> String {
        for arg in &self.args {
            if let Some(solver) = arg.strip_prefix("--solver=") {
                return solver.to_string();
            }
        }
        "z3".to_string()
    }
}

impl Display for TestCfg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.expect_fail {
            write!(f, "--expect-fail ")?;
        }
        if self.all_solvers {
            write!(f, "--all-solvers ")?;
        }
        if let Some(name) = &self.name {
            write!(f, "--name={name} ")?;
        }
        if !self.args.is_empty() {
            write!(f, "-- ")?;
            let args = self
                .args
                .iter()
                .map(|arg| shell_words::quote(arg))
                .collect::<Vec<_>>();
            write!(f, "{}", args.join(" "))?;
        }
        Ok(())
    }
}

#[derive(Deserialize, Debug, Clone)]
struct Tests {
    /// Tests to run for every fly file in the config file's directory.
    tests: Vec<TestCfg>,
}

#[derive(Debug, Clone)]
struct Test {
    path: PathBuf,
    cfg: TestCfg,
}

impl Display for Test {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", &self.cfg, self.path.display())
    }
}

/// Get tests specified as TEST lines
fn get_file_tests(path: &Path) -> Vec<Test> {
    let f = File::open(path).expect("could not open test file");
    let f = io::BufReader::new(f);
    f.lines()
        .flat_map(|l| {
            let l = l.unwrap();
            l.strip_prefix("# TEST ").map(|test_line| {
                let split_line = match shell_words::split(test_line) {
                    Ok(split) => split,
                    Err(err) => {
                        eprintln!("could not tokenize TEST line:");
                        eprintln!("# TEST {test_line}");
                        panic!("{err}");
                    }
                };
                let args = ["TEST".to_string()]
                    .into_iter()
                    .chain(split_line.into_iter());
                Test {
                    path: path.to_path_buf(),
                    cfg: TestCfg::try_parse_from(args).unwrap_or_else(|err| {
                        eprintln!("could not parse TEST line:");
                        eprintln!("# TEST {test_line}");
                        panic!("could not parse TEST line: {err}");
                    }),
                }
            })
        })
        .collect()
}

fn get_toml_tests(toml_file: &Path) -> Vec<Test> {
    let f = fs::read_to_string(toml_file).expect("could not open config file");
    let tests: Tests =
        toml::from_str(&f).unwrap_or_else(|err| panic!("could not parse toml file: {err}"));
    let dir = toml_file.parent().unwrap();
    dir.read_dir()
        .expect("could not read toml dir")
        .filter_map(|e| e.ok())
        .filter(|entry| entry.path().extension() == Some(OsStr::new("fly")))
        .flat_map(|entry| {
            tests
                .tests
                .iter()
                .map(|cfg| Test {
                    path: entry.path(),
                    cfg: cfg.clone(),
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Get tests recursively under a root directory, keyed by their file path.
fn get_tests(root_dir: &str) -> HashMap<PathBuf, Vec<Test>> {
    let root_dir = Path::new(root_dir);
    let tests = WalkDir::new(root_dir)
        .sort_by_file_name()
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|entry| entry.file_type().is_file())
        .flat_map(|entry| {
            if entry.path().ends_with("tests.toml") {
                get_toml_tests(entry.path())
            } else if entry.path().extension() == Some(OsStr::new("fly")) {
                get_file_tests(entry.path())
            } else {
                vec![]
            }
        });
    let mut path_tests = HashMap::new();
    for test in tests {
        path_tests
            .entry(test.path.clone())
            .or_insert_with(Vec::new)
            .push(test);
    }
    path_tests
}

fn verifier() -> Command {
    let mut cmd = Command::new("./target/debug/temporal-verifier");
    cmd.arg("--color=never");
    cmd
}

impl Test {
    fn test_name(&self) -> String {
        let path = self.path.file_name().unwrap().to_string_lossy();
        if let Some(name) = &self.cfg.name {
            format!("{path}.{name}")
        } else {
            path.to_string()
        }
    }

    /// Turn all_solvers=true into separate Test structs.
    fn normalize(&self) -> Vec<Self> {
        if self.cfg.all_solvers {
            SOLVERS_TO_TEST
                .map(|solver| {
                    let mut test = self.clone();
                    test.cfg.all_solvers = false;
                    test.cfg.args.push(format!("--solver={solver}"));
                    test.cfg.append_to_name(solver);
                    test
                })
                .to_vec()
        } else {
            vec![self.clone()]
        }
    }

    fn run(&self) {
        if self.cfg.all_solvers {
            for t in self.normalize() {
                t.run()
            }
        } else {
            let out = verifier()
                .args(&self.cfg.args)
                .arg(&self.path)
                .output()
                .expect("could not run verifier");
            let stdout = String::from_utf8(out.stdout).expect("non-utf8 output");
            let stderr = String::from_utf8(out.stderr).expect("non-utf8 output");
            let combined_stdout_stderr =
                format!("{stdout}\n======== STDERR: ===========\n{stderr}");

            if check_version(&self.cfg.solver()) {
                insta::assert_display_snapshot!(self.test_name(), combined_stdout_stderr);
            }

            if self.cfg.expect_fail {
                assert!(
                    !out.status.success(),
                    "verifier succeeded but expected failure"
                );
            } else if !out.status.success() {
                eprintln!("{stderr}");
                assert!(out.status.success(), "verifier should succeed");
            }
        }
    }
}

fn test_dir(root_dir: &str) {
    for (_, tests) in get_tests(root_dir) {
        for (n, mut test) in tests.into_iter().enumerate() {
            // ensure test names are unique by appending an index
            if n >= 1 {
                test.cfg.append_to_name(&format!("{n}"));
            }
            println!("# TEST {test}");
            let test_path = test.path.parent().unwrap().strip_prefix(root_dir).unwrap();
            insta::with_settings!(
                {
                    description => format!("{test}"),
                    prepend_module_to_snapshot => false,
                    // The initial .. is needed because this path is relative to
                    // where this test is
                    snapshot_path => Path::new("..").join(root_dir).join("snapshots").join(test_path),
                },
                { test.run(); }
            )
        }
    }
}

#[test]
fn test_solver_versions_match() {
    let mismatches = SOLVERS_TO_TEST
        .iter()
        .filter(|solver| !check_version(solver))
        .map(|s| s.to_string())
        .collect::<Vec<_>>();
    assert!(
        mismatches.is_empty(),
        "some solvers ({}) are at the wrong version (try running ./tools/download-solvers.sh)",
        mismatches.join(", ")
    );
}

#[test]
fn test_small_examples() {
    test_dir("tests/examples")
}

#[test]
fn test_larger_examples() {
    test_dir("examples")
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::{
    collections::HashMap,
    ffi::OsStr,
    fmt::Display,
    fs::{self, File},
    io::{self, BufRead},
    path::{Path, PathBuf},
    process::Command,
};

use clap::Parser;
use serde_derive::Deserialize;
use walkdir::WalkDir;

const SOLVERS_TO_TEST: [&str; 3] = ["z3", "cvc4", "cvc5"];

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
            write!(f, "{}", self.args.join(" "))?;
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
                let args = ["TEST"].iter().copied();
                let args = args.chain(test_line.split(' '));
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
            insta::assert_display_snapshot!(self.test_name(), combined_stdout_stderr);

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
fn test_small_examples() {
    test_dir("tests/examples")
}

#[test]
fn test_larger_examples() {
    test_dir("examples")
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::{
    ffi::OsStr,
    path::{Path, PathBuf},
    process::Command,
};

use walkdir::WalkDir;

const SOLVERS_TO_TEST: [&str; 3] = ["z3", "cvc4", "cvc5"];

fn get_tests(dir: &str) -> Vec<PathBuf> {
    WalkDir::new(format!("examples/{dir}"))
        .sort_by_file_name()
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|entry| {
            entry.file_type().is_file() && entry.path().extension() == Some(OsStr::new("fly"))
        })
        .map(|entry| entry.path().to_path_buf())
        .collect()
}

fn path_test_name(path: &Path) -> String {
    path.strip_prefix("examples")
        .unwrap()
        .to_string_lossy()
        .to_string()
}

#[test]
fn success() {
    for solver in SOLVERS_TO_TEST {
        for path in get_tests("success") {
            println!("Running {} with {solver}", path.display());
            let out = Command::new("./target/debug/temporal-verifier")
                .arg("--color=never")
                .arg(format!("--solver={solver}"))
                .arg(path.as_os_str())
                .output()
                .expect("could not run verifier");
            assert!(
                out.status.success(),
                "verification failed for {} with {solver}",
                path.display()
            );
        }
    }
}

#[test]
fn houdini_success() {
    for solver in SOLVERS_TO_TEST {
        for path in get_tests("success") {
            println!("Running Houdini on {} with {solver}", path.display());
            let out = Command::new("./target/debug/temporal-verifier")
                .arg("--color=never")
                .arg(format!("--solver={solver}"))
                .arg("--houdini")
                .arg(path.as_os_str())
                .output()
                .expect("could not run verifier");
            assert!(
                out.status.success(),
                "verification failed for {} with {solver}",
                path.display()
            );
        }
    }
}

#[test]
fn failing_snapshot() {
    for solver in SOLVERS_TO_TEST {
        for path in get_tests("fail") {
            println!("Running {} with {solver}", path.display());
            let out = Command::new("./target/debug/temporal-verifier")
                .arg("--color=never")
                .arg(format!("--solver={solver}"))
                .arg(path.as_os_str())
                .output()
                .expect("could not run verifier");
            let stderr = String::from_utf8(out.stderr).expect("non-utf8 output");
            insta::assert_display_snapshot!([&path_test_name(&path), solver].join("."), stderr);
        }
    }
}

#[test]
fn houdini_failing_snapshot() {
    for solver in SOLVERS_TO_TEST {
        for path in get_tests("fail") {
            println!("Running Houdini on {} with {solver}", path.display());
            let out = Command::new("./target/debug/temporal-verifier")
                .arg("--color=never")
                .arg(format!("--solver={solver}"))
                .arg("--houdini")
                .arg(path.as_os_str())
                .output()
                .expect("could not run verifier");
            let stderr = String::from_utf8(out.stderr).expect("non-utf8 output");
            insta::assert_display_snapshot!(
                [&path_test_name(&path), solver, "houdini"].join("."),
                stderr
            );
        }
    }
}

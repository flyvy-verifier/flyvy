// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::{
    ffi::OsStr,
    path::{Path, PathBuf},
    process::Command,
};

use walkdir::WalkDir;

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
    for path in get_tests("success") {
        let out = Command::new("./target/debug/temporal-verifier")
            .arg("--color=never")
            .arg(path.as_os_str())
            .output()
            .expect("could not run verifier");
        assert!(
            out.status.success(),
            "verification failed for {}",
            path.display()
        );
    }
}

#[test]
fn failing_snapshot() {
    for path in get_tests("fail") {
        println!("{}", path.display());
        let out = Command::new("./target/debug/temporal-verifier")
            .arg("--color=never")
            .arg(path.as_os_str())
            .output()
            .expect("could not run verifier");
        let stderr = String::from_utf8(out.stderr).expect("non-utf8 output");
        insta::assert_display_snapshot!(path_test_name(&path), stderr);
    }
}

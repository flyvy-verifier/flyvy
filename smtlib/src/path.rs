// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Utilities for finding SMT-related things in the filesystem.

use std::{
    env,
    path::{Path, PathBuf},
};

#[allow(non_snake_case)]
fn REPO_ROOT_PATH() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("could not get parent directory of smtlib package")
}

/// Get the right invocation of the solver with binary name bin.
///
/// First checks if the solver environment variable is set (eg, Z3_BIN), which
/// takes first priority. Then checks if the solver binary is in the compile
/// directory. Finally falls back to just using bin as-is (that is, relying on
/// $PATH).
pub fn solver_path(bin: &str) -> String {
    let var = bin.to_uppercase() + "_BIN";
    if let Some(val) = env::var_os(var) {
        return val.to_string_lossy().into();
    }
    let bin = if env::consts::OS == "windows" && !bin.ends_with(".exe") {
        bin.to_owned() + ".exe"
    } else {
        bin.to_owned()
    };
    let src_bin_path = REPO_ROOT_PATH().join("solvers").join(&bin);
    if src_bin_path.exists() {
        return src_bin_path.to_string_lossy().into();
    }
    bin
}

/// Get the log directory for a flyvy file
pub fn log_dir(fly_path: &Path) -> PathBuf {
    let log_base = REPO_ROOT_PATH().join(".flyvy-log");
    let Some(fname) = fly_path.file_name() else {
        return log_base;
    };
    log_base.join(Path::new(fname).with_extension(""))
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::process::Command;

fn temporal_verifier() -> Command {
    let mut cmd = Command::new("../target/debug/temporal-verifier");
    cmd.arg("--color=never");
    cmd
}

#[test]
fn updr_determinism() {
    let mut expected_output: Option<String> = None;
    let num_iters = 2; // ideally this would be higher, but it's too slow at ~6 seconds per iteration
    for i in 0..num_iters {
        println!("updr determinism iteration {}", i);
        let out = temporal_verifier()
            .arg("updr-verify")
            .arg("examples/lockserver.fly")
            .arg("--solver-seed=1")
            .output()
            .expect("could not run temporal-verifier");

        assert!(out.status.success(), "temporal-verifier should succeed");

        let stdout = String::from_utf8(out.stdout).expect("non-utf8 output");
        let stderr = String::from_utf8(out.stderr).expect("non-utf8 output");

        let combined_stdout_stderr = format!("{stdout}\n======== STDERR: ===========\n{stderr}");

        match expected_output {
            Some(ref expected) => {
                assert_eq!(expected, &combined_stdout_stderr);
            }
            None => {
                expected_output = Some(combined_stdout_stderr);
            }
        }
    }
}

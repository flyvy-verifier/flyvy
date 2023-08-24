// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Statistics from a single benchmark run, mostly gathered through `getrusage`.

use std::{error::Error, time::Duration};

use serde::{Deserialize, Serialize};

/// `RunMeasurement` holds the statistics captured from a single run. This includes
/// resource usage through `getrusage` (the same system call that powers
/// `time`), as well as basic info about whether the process exited with an
/// error or not.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RunMeasurement {
    /// Elapsed time of run.
    pub real_time: Duration,
    /// User time (including all child processes like solvers).
    pub user_time: Duration,
    /// System time (including all child processes like solvers).
    pub sys_time: Duration,
    /// User time (excluding child processes).
    pub self_user_time: Duration,
    /// Max memory usage (RSS) in bytes
    pub max_mem_bytes: usize,
    /// Whether the run was killed early due to a timeout.
    pub timed_out: bool,
    /// Whether the run was successful
    pub success: bool,
}

impl RunMeasurement {
    /// Maximum memory usage in MB.
    pub fn max_mem_mb(&self) -> usize {
        self.max_mem_bytes / 1024 / 1024
    }

    /// Time spent in subprocesses (eg, SMT solver).
    pub fn subprocess_time(&self) -> Duration {
        self.user_time.saturating_sub(self.self_user_time)
    }

    /// Percentage of time using CPU. This is simply the ratio of "CPU time" to
    /// wall clock time, so it can exceed 1 for a multi-threaded program.
    pub fn cpu_utilization(&self) -> f64 {
        self.user_time.as_secs_f64() / self.real_time.as_secs_f64()
    }

    /// Percentage of user time in subprocesses. This should be at most 1.
    pub fn subprocess_utilization(&self) -> f64 {
        self.subprocess_time().as_secs_f64() / self.user_time.as_secs_f64()
    }

    /// Print a human-readable version of these results.
    pub fn print(&self) {
        println!(
            "time: {:0.1}s{timed_out_msg}",
            &self.real_time.as_secs_f64(),
            timed_out_msg = if self.timed_out { " (timed out)" } else { "" }
        );
        println!("  user:   {:0.1}s", self.user_time.as_secs_f64());
        println!("  solver: {:0.1}s", self.subprocess_time().as_secs_f64());
        println!("  sys:    {:0.1}s", self.sys_time.as_secs_f64());
        println!("max mem: {}MB", self.max_mem_mb());
    }

    /// Convert these results to a compact JSON representation.
    pub fn to_json(&self) -> String {
        serde_json::to_string(self).expect("could not serialize `RunResult`")
    }

    /// Parse results serialized as JSON.
    pub fn from_json(s: &str) -> Result<Self, Box<dyn Error>> {
        let v = serde_json::from_str(s)?;
        Ok(v)
    }
}

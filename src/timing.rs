// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Track and report timing info across the whole pipeline.
//!
//! Focused on measuring time spent in calling the SMT solver.

use std::{
    sync::Mutex,
    time::{Duration, Instant},
};

use itertools::Itertools;
use lazy_static::lazy_static;

/// The category for a timing measurement.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum TimeType {
    /// A call to (check-sat)
    CheckSatCall {
        /// true if the result is sat (and false for unsat and unknown)
        sat: bool,
    },
    /// A call to (get-model)
    GetModel,
    /// The full process of getting a minimized model (incorporating several SMT
    /// queries)
    GetMinimalModel,
}

impl TimeType {
    fn name(&self) -> &'static str {
        match self {
            TimeType::CheckSatCall { sat: false } => "check-sat (unsat)",
            TimeType::CheckSatCall { sat: true } => "check-sat (sat)",
            TimeType::GetModel => "get-model",
            TimeType::GetMinimalModel => "get-minimal-model",
        }
    }
}

/// A single timing event.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
struct TimeInfo {
    typ: TimeType,
    dur: Duration,
}

/// A record of timing measurements.
///
/// `Sync` to support concurrent time recording.
pub struct Timings {
    /// List of timings gathered.
    times: Mutex<Vec<TimeInfo>>,
    /// The start time of the program (the exact time depends on how the
    /// `Timings` is initialized).
    start: Instant,
}

impl Timings {
    #[allow(clippy::new_without_default)]
    /// Create a new empty Timings struct, and set the start time.
    pub fn new() -> Self {
        Timings {
            times: Mutex::new(vec![]),
            start: Instant::now(),
        }
    }

    fn record_duration(&self, typ: TimeType, dur: Duration) {
        let mut times = self.times.lock().unwrap();
        times.push(TimeInfo { typ, dur })
    }

    /// Record a timing elapsed since `start`.
    pub fn elapsed(&self, typ: TimeType, start: Instant) {
        let dur = start.elapsed();
        self.record_duration(typ, dur);
    }

    /// Print a full timing report to stdout.
    pub fn report(&self) {
        if cfg!(debug_assertions) {
            eprintln!("warning: this is a debug build, non-solver time will be worse");
        }
        let total_time = self.start.elapsed().as_secs_f64();
        println!("{:<22}: {total_time:.1}s", "total");

        let times = {
            let times = self.times.lock().unwrap();
            times.clone()
        };
        let count = times.len();
        let solver_total = times
            .iter()
            .map(|info| info.dur)
            .sum::<Duration>()
            .as_secs_f64();
        println!("  {:<20}: {:.1}s", "non-solver", total_time - solver_total);
        println!(
            "  {:<20}: {solver_total:.1}s {count:>4} calls",
            "solver total",
        );

        let totals = times
            .iter()
            .into_grouping_map_by(|info| info.typ)
            .fold((Duration::ZERO, 0), |(dur, count), _key, t| {
                (dur + t.dur, count + 1)
            });
        for typ in [
            TimeType::CheckSatCall { sat: false },
            TimeType::CheckSatCall { sat: true },
            TimeType::GetModel,
            TimeType::GetMinimalModel,
        ] {
            let (time, count) = totals.get(&typ).unwrap_or(&(Duration::ZERO, 0));
            if *count > 0 {
                println!(
                    "    {:<18}: {:.1}s {count:>4} calls ",
                    typ.name(),
                    time.as_secs_f64()
                );
            }
        }
    }
}

lazy_static! {
    /// A global Timings struct for the whole program.
    static ref TIMES: Timings = Timings::new();
}

/// Set the start time of the program.
///
/// Does nothing if run multiple times.
pub fn init() {
    let _ = TIMES.start;
}

/// Get the start time of the program.
///
/// To make this mean anything the program must call [`init`] reasonably early.
pub fn start() -> Instant {
    Instant::now()
}

/// Record an elapsed time for a call of `typ` since `start`.
pub fn elapsed(typ: TimeType, start: Instant) {
    TIMES.elapsed(typ, start)
}

/// Print a timing report.
pub fn report() {
    TIMES.report()
}

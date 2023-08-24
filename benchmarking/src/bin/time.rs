// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Implementation of the `time` binary. Everything interesting is in
//! [`benchmarking::time_bench::Time`].

use std::{io, process::ExitCode};

use benchmarking::time_bench::Time;
use clap::Parser;

fn main() -> Result<ExitCode, io::Error> {
    let app = Time::parse();
    app.exec()
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use clap::Parser;
use fly::timing;
use temporal_verifier::App;

fn main() {
    pretty_env_logger::init();
    let app = App::parse();
    timing::init();
    app.exec();
}

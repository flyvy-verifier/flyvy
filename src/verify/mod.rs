// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Verify a fly module using an SMT solver.

mod error;
pub use error::*;
mod module;
pub use module::verify_module;
pub use module::SolverConf;
mod safety;

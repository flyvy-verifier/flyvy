// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! High-level interface to an SMT solver using [`Term`](crate::fly::syntax::Term).

pub mod backends;
mod imp;
mod models;
mod path;
mod sexp;
pub use imp::{Backend, FOModel, Solver};
pub use path::solver_path;

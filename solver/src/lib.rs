// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! High-level interface to an SMT solver using [`Term`](crate::fly::syntax::Term).

// configure clippy
#![allow(clippy::needless_return)]
#![allow(clippy::large_enum_variant)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::type_complexity)]
// documentation-related lints (only checked when running rustdoc)
#![warn(missing_docs)]
#![allow(rustdoc::private_intra_doc_links)]
#![deny(rustdoc::broken_intra_doc_links)]

pub mod backends;
pub mod conf;
pub mod imp;
pub mod models;
pub mod sexp;

pub use smtlib::path::{log_dir, solver_path};
pub use smtlib::proc::{SatResp, SmtPid};

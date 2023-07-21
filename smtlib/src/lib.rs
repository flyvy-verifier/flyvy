// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Low-level sexp-based interface to an SMT solver.
//!
//! This interface is implementing using pipes to communicate with an
//! SMT-LIB2-compatible solver process. The only solver-specific configuration
//! is the binary name and command-line arguments required to invoke the
//! solver.

// configure clippy
#![allow(clippy::needless_return)]
#![allow(clippy::large_enum_variant)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::type_complexity)]
#![deny(clippy::uninlined_format_args)]
// documentation-related lints (only checked when running rustdoc)
#![warn(missing_docs)]
#![allow(rustdoc::private_intra_doc_links)]
#![deny(rustdoc::broken_intra_doc_links)]

pub mod conf;
pub mod path;
pub mod proc;
pub mod sexp;
mod tee;

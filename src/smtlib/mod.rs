// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Low-level sexp-based interface to an SMT solver.
//!
//! This interface is implementing using pipes to communicate with an
//! SMT-LIB2-compatible solver process. The only solver-specific configuration
//! is the binary name and command-line arguments required to invoke the
//! solver.

pub mod proc;
pub mod sexp;

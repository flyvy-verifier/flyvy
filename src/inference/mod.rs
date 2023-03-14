// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Invariant inference
//!
//! Mostly consists of an implementation of the "q-alpha" algorithm, but also
//! provides an implementation of Houdini.

mod basics;
mod fixpoint;
pub mod houdini;
mod lemma;
mod pdnf;

pub use basics::input_cfg;
pub use fixpoint::run_fixpoint;

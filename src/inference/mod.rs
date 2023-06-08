// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Invariant inference
//!
//! Mostly consists of an implementation of the "q-alpha" algorithm, but also
//! provides an implementation of Houdini.

mod basics;
mod fixpoint;
mod hashmap;
pub mod houdini;
pub mod lemma;
pub mod quant;
pub mod subsume;
mod weaken;

pub use basics::{parse_quantifier, InferenceConfig, QfBody};
pub use fixpoint::{fixpoint_multi, fixpoint_single};

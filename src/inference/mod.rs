// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Invariant inference
//!
//! Mostly consists of an implementation of the "q-alpha" algorithm, but also
//! provides an implementation of Houdini.

pub mod atoms;
mod basics;
mod fixpoint;
mod hashmap;
pub mod houdini;
pub mod lemma;
mod marco;
pub mod quant;
pub mod subsume;
mod updr;
mod weaken;

pub use basics::{parse_quantifier, InferenceConfig, QfBody};
pub use fixpoint::{fixpoint_multi, fixpoint_single};
pub use updr::Updr;

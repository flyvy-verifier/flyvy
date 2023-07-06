// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Invariant inference
//!
//! Mostly consists of an implementation of the "q-alpha" algorithm, but also
//! provides an implementation of Houdini.

// configure clippy
#![allow(clippy::needless_return)]
#![allow(clippy::large_enum_variant)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::type_complexity)]
// documentation-related lints (only checked when running rustdoc)
#![warn(missing_docs)]
#![allow(rustdoc::private_intra_doc_links)]
#![deny(rustdoc::broken_intra_doc_links)]

pub mod atoms;
pub mod basics;
pub mod fixpoint;
pub mod hashmap;
pub mod houdini;
pub mod lemma;
pub mod marco;
pub mod quant;
pub mod subsume;
pub mod updr;
pub mod weaken;

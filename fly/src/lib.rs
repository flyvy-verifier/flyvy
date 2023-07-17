// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! The flyvy language

// configure clippy
#![allow(clippy::needless_return)]
#![allow(clippy::large_enum_variant)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::type_complexity)]
// documentation-related lints (only checked when running rustdoc)
#![warn(missing_docs)]
#![allow(rustdoc::private_intra_doc_links)]
#![deny(rustdoc::broken_intra_doc_links)]

pub mod defs;
pub mod ouritertools;
pub mod parser;
pub mod printer;
pub mod rets;
pub mod semantics;
pub mod sorts;
pub mod syntax;
pub mod term;
pub mod timing;
pub mod transitions;

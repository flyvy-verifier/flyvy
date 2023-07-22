// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! flyvy library
//!
//! The API is currently primarily available for testing purposes and not really
//! intended as a general-purpose library.

#![deny(missing_docs)]
// configure clippy
#![allow(clippy::needless_return)]
#![allow(clippy::large_enum_variant)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::type_complexity)]
#![deny(clippy::uninlined_format_args)]
// documentation-related lints (only checked when running rustdoc)
#![allow(rustdoc::private_intra_doc_links)]
#![deny(rustdoc::broken_intra_doc_links)]

pub mod command;
pub mod concurrent;

#[doc(hidden)]
pub use command::App;

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! flyvy library
//!
//! The API is currently primarily available for testing purposes and not really
//! intended as a general-purpose library.

#![allow(clippy::needless_return)]
#![warn(missing_docs)]

mod command;
mod fly;
mod inference;
pub mod smtlib;
pub mod solver;
mod term;
pub mod timing;
mod verify;

#[doc(hidden)]
pub use command::App;

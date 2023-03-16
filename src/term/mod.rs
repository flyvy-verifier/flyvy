// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Utilities for manipulating flyvy [`crate::fly::syntax::Term`]s.

mod cnf;
mod fo;
mod prime;
pub mod subst;
pub use cnf::Cnf;
pub use fo::FirstOrder;
pub use prime::Next;

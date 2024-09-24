//! Formats that `.fly` files can be parsed into and some utilities for using them.

// configure clippy
#![allow(clippy::needless_return)]
#![allow(clippy::large_enum_variant)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::type_complexity)]
#![deny(clippy::uninlined_format_args)]
#![warn(missing_docs)]

pub mod basics;
pub mod chc;
pub mod parser;

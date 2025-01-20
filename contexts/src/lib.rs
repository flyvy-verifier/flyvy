//! Defines contexts consisting of objects and attributes, and in particular logical contexts
//! meant to facillitate logical reasoning, e.g., in fixpoint computation for inference.

// configure clippy
#![allow(clippy::needless_return)]
#![allow(clippy::large_enum_variant)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::type_complexity)]
#![deny(clippy::uninlined_format_args)]
// TODO: #![warn(missing_docs)]

pub mod alg;
pub mod arith;
pub mod context;
pub mod logic;
pub mod miner;
pub mod sets;
pub mod subsume;

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! The flyvy language

// configure clippy
#![allow(clippy::needless_return)]
#![allow(clippy::large_enum_variant)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::type_complexity)]
#![allow(clippy::useless_format)]
#![deny(clippy::uninlined_format_args)]
// documentation-related lints (only checked when running rustdoc)
#![warn(missing_docs)]
#![allow(rustdoc::private_intra_doc_links)]
#![deny(rustdoc::broken_intra_doc_links)]

pub mod defs;
pub mod ouritertools;
pub mod parser;
pub mod printer;
pub mod quant;
pub mod rets;
pub mod semantics;
pub mod sorts;
pub mod syntax;
pub mod term;
pub mod timing;
pub mod transitions;

#[cfg(test)]
mod test_sorts_public {
    // these tests are here so that we are forced to use the public API to sort inference
    use crate::{
        parser::{self, parse_signature},
        sorts::Scope,
        syntax::{Binder, Quantifier, Sort, Term},
    };

    #[test]
    fn test_sorts_public() {
        let sig = parse_signature(
            "
            sort round
            immutable le(round, round): bool
            ",
        );
        let ctx = Scope::new(&sig).expect("could not create context");
        {
            // check that le(r,r) sort checks in context [r:round]
            let mut ctx = ctx.clone();
            ctx.add_variable("r", &Sort::Uninterpreted("round".to_owned()))
                .expect("could not add x to the scope");
            let sort = ctx
                .sort_check_term(&mut parser::term("le(r,r)"))
                .expect("unexpected sort checking error");
            assert_eq!(sort, Sort::Bool);
        }
        // check that le(r,r) does *not* sort check in the empty context
        assert!(ctx
            .sort_check_term(&mut crate::parser::term("le(r,r)"))
            .is_err());
        // check that sort inference can figure out r:round in this quantifier
        let mut t = parser::term("forall r. le(r,r)");
        let sort = ctx
            .sort_check_term(&mut t)
            .expect("unexpected sort checking error");
        assert_eq!(sort, Sort::Bool);
        match &t {
            Term::Quantified {
                quantifier: Quantifier::Forall,
                binders,
                body: _,
            } => match &binders[..] {
                // check that sort inference filled in the annotation correctly
                [Binder { name: _, sort }] => {
                    assert_eq!(sort, &Sort::Uninterpreted("round".to_owned()))
                }
                _ => panic!("wrong number of variables"),
            },
            _ => panic!("wrong AST node"),
        }
    }
}

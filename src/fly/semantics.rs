// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

#![allow(dead_code)]
use std::iter::zip;

use super::syntax::{Signature, Sort};

/// Element is an integer type for representing members of a universe within an
/// interpretation.
pub type Element = usize;

/// A universe maps each sort (in the order of the Signature) to its number of
/// elements in an interpretation.
pub type Universe = Vec<usize>;

/// An interpretation gives the complete value of a function for a
/// finite-cardinality universe.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Interpretation {
    /// The type of this function, given as the cardinality first of all the
    /// inputs and finally the cardinality of the output.
    pub shape: Vec<usize>,
    /// The value of the function at every possible input.
    pub data: Vec<Element>,
}

impl Interpretation {
    // TODO(oded): make this more space efficient by using the right amount of bits (probably with padding)
    pub fn get(&self, args: &[Element]) -> Element {
        assert_eq!(self.shape.len() - 1, args.len());
        let mut index: usize = 0;
        for (a, s) in zip(args, &self.shape) {
            assert!(a < s);
            index = index * s + a;
        }
        assert!(self.data[index] < self.shape[self.shape.len() - 1]);
        self.data[index]
    }

    /// Create a new interpretation of a given shape based on a function, by
    /// calling the function on all possible input tuple
    pub fn new(shape: &Vec<usize>, _f: impl Fn(&[Element]) -> Element) -> Self {
        let size = shape[..shape.len() - 1].iter().product();
        let data: Vec<Element> = vec![0; size];
        // TODO: use https://docs.rs/itertools/latest/itertools/trait.Itertools.html#method.cartesian_product to implement it (cargo add itertools)
        Self {
            shape: shape.clone(),
            data,
        }
    }
}

pub struct Model {
    // TODO(oded): to optimize, make things Rc<_> (_ = Signature, Universe, and Interpretation)
    pub signature: Signature,
    /// universe matches signature.sorts
    pub universe: Universe,
    /// interp matches signature.relations
    pub interp: Vec<Interpretation>,
}

impl Model {
    fn cardinality(&self, sort: &Sort) -> usize {
        match sort {
            Sort::Bool => 2,
            _ => self.universe[self.signature.sort_idx(sort)],
        }
    }

    fn wf(&self) {
        assert_eq!(self.universe.len(), self.signature.sorts.len());
        assert_eq!(self.interp.len(), self.signature.relations.len());
        for i in 0..self.interp.len() {
            let relation = &self.signature.relations[i];
            let interp = &self.interp[i];
            assert_eq!(relation.args.len(), interp.shape.len() - 1);
            assert_eq!(
                interp.shape.iter().last().unwrap(),
                &self.cardinality(&relation.typ),
            );
            for j in 0..relation.args.len() {
                let k = self.signature.sort_idx(&relation.args[j]);
                assert_eq!(interp.shape[j], self.universe[k]);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::fly::syntax::{RelationDecl, Signature, Sort};

    use super::{Interpretation, Model, Universe};

    #[test]
    fn test1() {
        println!("Hello!");
        let i1 = Interpretation {
            shape: vec![10, 10],
            data: (0..10).collect(),
        };
        for i in 0..10 {
            dbg!(i, i1.get(&[i]));
        }

        let i2 = Interpretation {
            shape: vec![5, 2, 10],
            data: (0..10).collect(),
        };
        for i in 0..5 {
            for j in 0..2 {
                dbg!(i, j, i2.get(&[i, j]));
            }
        }
        assert_eq!(i2.get(&[3, 1]), 3 * i2.shape[1] + 1);
    }

    #[test]
    fn test_wf() {
        let typ = |n: usize| Sort::Id(format!("T{n}"));

        let sig = Signature {
            sorts: vec![typ(1), typ(2)],
            relations: vec![
                RelationDecl {
                    mutable: true,
                    name: "r1".to_string(),
                    args: vec![typ(2), typ(1)],
                    typ: Sort::Bool,
                },
                RelationDecl {
                    mutable: true,
                    name: "r2".to_string(),
                    args: vec![typ(1)],
                    typ: typ(2),
                },
            ],
        };

        // T1 has cardinality 2, T2 has cardinality 3
        let universe: Universe = vec![2, 3];

        // r1 is of type (T2, T1) -> bool
        let r1_interp = Interpretation {
            shape: vec![3, 2, 2],
            data: vec![0, 1, 1, 0, 1, 0],
        };

        // r2 is of type (T1) -> T2
        let r2_interp = Interpretation {
            shape: vec![2, 3],
            data: vec![2, 0],
        };

        let model = Model {
            signature: sig,
            universe,
            interp: vec![r1_interp, r2_interp],
        };

        model.wf();
    }
}

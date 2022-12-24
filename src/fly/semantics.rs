// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::fmt::Write;
use std::iter::zip;

use itertools::Itertools;
use serde::Serialize;

use super::syntax::{RelationDecl, Signature, Sort};

/// Element is an integer type for representing members of a universe within an
/// interpretation.
pub type Element = usize;

/// A universe maps each sort (in the order of the Signature) to its number of
/// elements in an interpretation.
pub type Universe = Vec<usize>;

/// An interpretation gives the complete value of a function for a
/// finite-cardinality universe.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
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
    pub fn new(shape: &Vec<usize>, f: impl Fn(&[Element]) -> Element) -> Self {
        let args = &shape[..shape.len() - 1];
        let ret_card = shape[shape.len() - 1];
        // wrap f just to add this assertion
        let f = |args: &[Element]| -> Element {
            let y = f(args);
            assert!(y < ret_card, "interpretation is out-of-bounds at {args:?}");
            y
        };
        // NOTE: multi_cartesian_product has a bug and doesn't produce the empty
        // tuple for an empty iterator
        // (https://github.com/rust-itertools/itertools/issues/337). Therefore
        // we need to handle this as a special case
        let data = if args.is_empty() {
            vec![f(&[])]
        } else {
            args.iter()
                .map(|&card| (0..card).collect::<Vec<Element>>())
                .multi_cartesian_product()
                .map(|args| f(&args))
                .collect()
        };
        Self {
            shape: shape.clone(),
            data,
        }
    }
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
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

    pub fn new(sig: &Signature, universe: &Universe, interp: Vec<Interpretation>) -> Self {
        let model = Self {
            signature: sig.clone(),
            universe: universe.clone(),
            interp,
        };
        model.wf();
        model
    }

    fn fmt_sort(typ: &Sort, idx: usize) -> String {
        match typ {
            Sort::Bool => {
                if idx == 0 {
                    "false".to_string()
                } else {
                    "true".to_string()
                }
            }
            Sort::Id(s) => format!("@{s}_{idx}"),
        }
    }

    fn fmt_rel(&self, decl: &RelationDecl, interp: &Interpretation) -> String {
        let mut lines = vec![];
        let arg_shape = &interp.shape[..interp.shape.len() - 1];
        let args_list = if arg_shape.is_empty() {
            vec![vec![]]
        } else {
            arg_shape
                .iter()
                .map(|&card| (0..card).collect::<Vec<Element>>())
                .multi_cartesian_product()
                .collect()
        };
        for args in args_list {
            let name = &decl.name;
            let args_s = zip(&decl.args, args.iter())
                .map(|(typ, &idx)| Self::fmt_sort(typ, idx))
                .collect::<Vec<_>>();
            let args_s = if args_s.is_empty() {
                "".to_string()
            } else {
                format!("({})", args_s.join(","))
            };
            let ret_s = Self::fmt_sort(&decl.typ, interp.get(&args));
            lines.push(format!("{name}{args_s} = {ret_s}"));
        }
        lines.join("\n")
    }

    /// Print a model in a format suitable for display to the user.
    pub fn fmt(&self) -> String {
        let mut w = String::new();
        for (rel, interp) in zip(&self.signature.relations, &self.interp) {
            let rel_s = self.fmt_rel(rel, interp);
            _ = writeln!(&mut w, "{rel_s}");
        }
        w
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

    #[test]
    fn test_interp_new() {
        let interp = Interpretation::new(&vec![3], |_| 2);
        assert_eq!(interp.get(&[]), 2);
        assert_eq!(interp.data, vec![2]);

        let interp = Interpretation::new(&vec![3, 2, 4], |es| es[0] + es[1]);
        for i in 0..3 {
            for j in 0..2 {
                assert_eq!(interp.get(&[i, j]), i + j, "wrong value at {i}, {j}");
            }
        }

        let interp = Interpretation::new(&vec![3, 2, 4, 7], |es| es[0] + es[1] * es[2]);
        for i in 0..3 {
            for j in 0..2 {
                for k in 0..4 {
                    assert_eq!(
                        interp.get(&[i, j, k]),
                        i + j * k,
                        "wrong value at {i}, {j}, {k}"
                    );
                }
            }
        }
    }
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::iter::zip;
use std::{collections::HashMap, fmt::Write};

use itertools::Itertools;
use serde::Serialize;

use super::syntax::{BinOp, NOp, Quantifier, RelationDecl, Signature, Sort, Term, UOp};

use BinOp::*;
use NOp::*;
use Quantifier::*;
use UOp::*;

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

    // ODED: I would change this function signature to:
    // fn fmt_element(sort: &Sort, element: Element) -> String
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
    // ODED: I think we should also print the universe here
    pub fn fmt(&self) -> String {
        let mut w = String::new();
        for (rel, interp) in zip(&self.signature.relations, &self.interp) {
            let rel_s = self.fmt_rel(rel, interp);
            _ = writeln!(&mut w, "{rel_s}");
        }
        w
    }

    /// Evaluate a term to a model element. Also depends on an assignment to
    /// logical variables.
    ///
    /// * None defaults to the empty assignment.
    /// * The assignment is unsorted, and so is the return value of this
    ///   function.
    pub fn eval(&self, t: &Term, assignment: Option<&HashMap<String, Element>>) -> Element {
        match t {
            // TODO(oded): Id("true") and Id("false") should probably be separate constructors
            Term::Id(name) if name == "false" => 0,
            Term::Id(name) if name == "true" => 1,
            Term::Id(name) if assignment.is_some() && assignment.unwrap().contains_key(name) => {
                assignment.unwrap()[name]
            }
            Term::Id(name) => {
                let i = self.signature.relation_idx(name);
                assert!(
                    self.signature.relations[i].args.is_empty(),
                    "tried to eval non-nullary function {name}"
                );
                self.interp[i].get(&[])
            }
            Term::App(f, args) => {
                let args: Vec<Element> = args.iter().map(|x| self.eval(x, assignment)).collect();
                // ODED: is `&**f` really the right/idomatic thing here?
                match &**f {
                    Term::Id(name) => self.interp[self.signature.relation_idx(name)].get(&args),
                    _ => panic!("tried to apply {f}"),
                }
            }
            Term::UnaryOp(Not, t) => {
                let v = self.eval(t, assignment);
                assert!(v == 0 || v == 1);
                1 - v
            }
            Term::BinOp(Equals | Iff, lhs, rhs) => {
                let lhs = self.eval(lhs, assignment);
                let rhs = self.eval(rhs, assignment);
                if lhs == rhs {
                    1
                } else {
                    0
                }
            }
            Term::BinOp(NotEquals, lhs, rhs) => {
                // TODO(oded): make this work: self.eval(&Term::UnaryOp(Not, Term::BinOp(Equals, lhs), rhs))
                let lhs = self.eval(lhs, assignment);
                let rhs = self.eval(rhs, assignment);
                if lhs == rhs {
                    0
                } else {
                    1
                }
            }
            Term::BinOp(Implies, lhs, rhs) => {
                // TODO(oded): make this work: self.eval(&Term::UnaryOp(Not, Term::BinOp(Equals, lhs), rhs))
                let lhs = self.eval(lhs, assignment);
                let rhs = self.eval(rhs, assignment);
                if lhs <= rhs {
                    1
                } else {
                    0
                }
            }
            Term::NAryOp(And, ts) => {
                let res = ts.iter().all(|t| self.eval(t, assignment) == 1);
                if res {
                    1
                } else {
                    0
                }
            }
            Term::NAryOp(Or, ts) => {
                let res = ts.iter().any(|t| self.eval(t, assignment) == 1);
                if res {
                    1
                } else {
                    0
                }
            }
            Term::Ite { cond, then, else_ } => {
                if self.eval(cond, assignment) == 1 {
                    self.eval(then, assignment)
                } else {
                    self.eval(else_, assignment)
                }
            }
            Term::Quantified {
                quantifier: _,
                binders,
                body,
            } if binders.is_empty() => self.eval(body, assignment),
            Term::Quantified {
                quantifier,
                binders,
                body,
            } => {
                assert!(!binders.is_empty());
                let shape: Vec<usize> = binders
                    .iter()
                    .map(|b| {
                        self.cardinality(
                            b.typ.as_ref().expect("cannot evaluate unsorted quantifer"),
                        )
                    })
                    .collect();
                let names: Vec<&String> = binders.iter().map(|b| &b.name).collect();
                let mut assignment_ = match assignment {
                    Some(a) => a.clone(),
                    None => HashMap::new(),
                };
                let mut iter = shape
                    .iter()
                    .map(|&card| (0..card).collect::<Vec<Element>>())
                    .multi_cartesian_product()
                    .map(|elements| {
                        for (name, element) in zip(&names, elements) {
                            // ODED: does this make sense? updating the
                            // assignment inside the lambda? and the
                            // name.to_string()?
                            assignment_.insert(name.to_string(), element);
                        }
                        self.eval(body, Some(&assignment_)) == 1
                    });
                let result = match quantifier {
                    Forall => iter.all(|x| x),
                    Exists => iter.any(|x| x),
                };
                // TODO(oded): make a bool_to_element function (and also bool_from_element)
                if result {
                    1
                } else {
                    0
                }
            }
            Term::UnaryOp(Always | Eventually | Prime, _) => panic!("tried to eval {t}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::fly::{
        semantics::Element,
        syntax::{
            BinOp::*, Binder, NOp::*, Quantifier::*, RelationDecl, Signature, Sort, Term, Term::*,
            UOp::*,
        },
    };

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

    #[test]
    #[allow(clippy::redundant_clone)]
    fn test_eval() {
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
                RelationDecl {
                    mutable: true,
                    name: "c1".to_string(),
                    args: vec![],
                    typ: typ(1),
                },
                RelationDecl {
                    mutable: true,
                    name: "c2".to_string(),
                    args: vec![],
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
            data: vec![1, 2],
        };

        // c1 is of type T1
        let c1_interp = Interpretation {
            shape: vec![2],
            data: vec![1],
        };

        // c2 is of type T2
        let c2_interp = Interpretation {
            shape: vec![3],
            data: vec![2],
        };

        let model = Model {
            signature: sig,
            universe,
            interp: vec![r1_interp, r2_interp, c1_interp, c2_interp],
        };

        model.wf();

        println!("model is:\n{}\n", model.fmt());

        let f = Id("false".to_string());
        let t = Id("true".to_string());
        let r1 = Id("r1".to_string());
        let r2 = Id("r2".to_string());
        let c1 = Id("c1".to_string());
        let c2 = Id("c2".to_string());

        let e = |t| model.eval(t, None);
        let b = |t: &Term| Box::new(t.clone());
        let ite = |cond, then, else_| Ite {
            cond: b(cond),
            then: b(then),
            else_: b(else_),
        };

        let mut tests: Vec<(Term, Element)> = vec![];

        // Testing using bool
        tests.extend(vec![
            // true and false
            (f.clone(), 0),
            (t.clone(), 1),
            // UnaryOp: Not
            (UnaryOp(Not, b(&f)), 1),
            (UnaryOp(Not, b(&t)), 0),
            // BinOp: Equals
            (BinOp(Equals, b(&f), b(&f)), 1),
            (BinOp(Equals, b(&f), b(&t)), 0),
            (BinOp(Equals, b(&t), b(&f)), 0),
            (BinOp(Equals, b(&t), b(&t)), 1),
            // BinOp: NotEquals
            (BinOp(NotEquals, b(&f), b(&f)), 0),
            (BinOp(NotEquals, b(&f), b(&t)), 1),
            (BinOp(NotEquals, b(&t), b(&f)), 1),
            (BinOp(NotEquals, b(&t), b(&t)), 0),
            // BinOp: Implies
            (BinOp(Implies, b(&f), b(&f)), 1),
            (BinOp(Implies, b(&f), b(&t)), 1),
            (BinOp(Implies, b(&t), b(&f)), 0),
            (BinOp(Implies, b(&t), b(&t)), 1),
            // BinOp: Iff,
            (BinOp(Iff, b(&f), b(&f)), 1),
            (BinOp(Iff, b(&f), b(&t)), 0),
            (BinOp(Iff, b(&t), b(&f)), 0),
            (BinOp(Iff, b(&t), b(&t)), 1),
            // NAryOp: And
            (NAryOp(And, vec![]), 1),
            (NAryOp(And, vec![f.clone()]), 0),
            (NAryOp(And, vec![t.clone()]), 1),
            (NAryOp(And, vec![f.clone(), f.clone()]), 0),
            (NAryOp(And, vec![f.clone(), t.clone()]), 0),
            (NAryOp(And, vec![t.clone(), f.clone()]), 0),
            (NAryOp(And, vec![t.clone(), t.clone()]), 1),
            (NAryOp(And, vec![f.clone(), f.clone(), f.clone()]), 0),
            (NAryOp(And, vec![f.clone(), f.clone(), t.clone()]), 0),
            (NAryOp(And, vec![f.clone(), t.clone(), f.clone()]), 0),
            (NAryOp(And, vec![f.clone(), t.clone(), t.clone()]), 0),
            (NAryOp(And, vec![t.clone(), f.clone(), f.clone()]), 0),
            (NAryOp(And, vec![t.clone(), f.clone(), t.clone()]), 0),
            (NAryOp(And, vec![t.clone(), t.clone(), f.clone()]), 0),
            (NAryOp(And, vec![t.clone(), t.clone(), t.clone()]), 1),
            // NAryOp: Or
            (NAryOp(Or, vec![]), 0),
            (NAryOp(Or, vec![f.clone()]), 0),
            (NAryOp(Or, vec![t.clone()]), 1),
            (NAryOp(Or, vec![f.clone(), f.clone()]), 0),
            (NAryOp(Or, vec![f.clone(), t.clone()]), 1),
            (NAryOp(Or, vec![t.clone(), f.clone()]), 1),
            (NAryOp(Or, vec![t.clone(), t.clone()]), 1),
            (NAryOp(Or, vec![f.clone(), f.clone(), f.clone()]), 0),
            (NAryOp(Or, vec![f.clone(), f.clone(), t.clone()]), 1),
            (NAryOp(Or, vec![f.clone(), t.clone(), f.clone()]), 1),
            (NAryOp(Or, vec![f.clone(), t.clone(), t.clone()]), 1),
            (NAryOp(Or, vec![t.clone(), f.clone(), f.clone()]), 1),
            (NAryOp(Or, vec![t.clone(), f.clone(), t.clone()]), 1),
            (NAryOp(Or, vec![t.clone(), t.clone(), f.clone()]), 1),
            (NAryOp(Or, vec![t.clone(), t.clone(), t.clone()]), 1),
            // Ite
            (ite(&f, &f, &f), 0),
            (ite(&f, &f, &t), 1),
            (ite(&f, &t, &f), 0),
            (ite(&f, &t, &t), 1),
            (ite(&t, &f, &f), 0),
            (ite(&t, &f, &t), 0),
            (ite(&t, &t, &f), 1),
            (ite(&t, &t, &t), 1),
            // Quantified: Forall
            (
                Quantified {
                    quantifier: Forall,
                    binders: vec![Binder {
                        name: "x".to_string(),
                        typ: Some(Sort::Bool),
                    }],
                    body: Box::new(Id("x".to_string())),
                },
                0,
            ),
            // Quantified: Exists
            (
                Quantified {
                    quantifier: Exists,
                    binders: vec![Binder {
                        name: "x".to_string(),
                        typ: Some(Sort::Bool),
                    }],
                    body: Box::new(Id("x".to_string())),
                },
                1,
            ),
        ]);

        // Testing of constants and relations
        tests.extend(vec![
            (c1.clone(), 1),
            (c2.clone(), 2),
            //
            (BinOp(Equals, b(&c1), b(&c1)), 1),
            (BinOp(NotEquals, b(&c1), b(&c1)), 0),
            //
            (App(b(&r1), vec![c2.clone(), c1.clone()]), 0),
            (App(b(&r2), vec![c1.clone()]), 2),
        ]);

        for (t, v) in tests.iter() {
            println!("evaluating {t} (expecting {v})");
            assert_eq!(&e(t), v, "evaluating {t} should give {v}");
        }
    }
}

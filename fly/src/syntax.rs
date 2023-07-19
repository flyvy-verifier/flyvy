// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! The flyvy AST for terms and modules.

use itertools::Itertools;
use std::fmt;

use serde::Serialize;

use crate::ouritertools::OurItertools;

/// Unary operators
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, PartialOrd, Ord)]
pub enum UOp {
    /// Boolean negation
    Not,
    /// Gives the value of the argument one step in the future
    Prime,
    /// Always temporal modality
    Always,
    /// Eventually temporal modality
    Eventually,
    /// Used for the l2s construction (may end up replaced with just Prime)
    Next,
    /// Past operator, used only for the l2s construction
    Previously,
}

/// Binary operators
#[allow(missing_docs)]
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, PartialOrd, Ord)]
pub enum BinOp {
    Equals,
    NotEquals,
    Implies,
    Iff,
    /// Used for the l2s construction
    Until,
    /// Past operator, used only for the l2s construction
    Since,
}

/// N-ary logical operators
#[allow(missing_docs)]
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, PartialOrd, Ord)]
pub enum NOp {
    And,
    Or,
}

/// A kind of quantifier (forall or exists)
#[allow(missing_docs)]
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, PartialOrd, Ord)]
pub enum Quantifier {
    Forall,
    Exists,
}

/// A binder for a quantifier
#[derive(PartialEq, Eq, Clone, Debug, Hash, PartialOrd, Ord)]
pub struct Binder {
    /// Bound name
    pub name: String,
    /// Sort for this binder
    pub sort: Sort,
}

impl From<&str> for Sort {
    fn from(value: &str) -> Self {
        Sort::Id(value.to_string())
    }
}

impl Binder {
    /// Smart constructor for a Binder that takes arguments by reference.
    pub fn new<N>(name: N, sort: &Sort) -> Self
    where
        N: AsRef<str>,
    {
        Binder {
            name: name.as_ref().to_string(),
            sort: sort.clone(),
        }
    }
}

/// A Term is a temporal-logical formula (in LTL), which can be interpreted as
/// being a sequence of values of some sort (often bool for example) under a
/// given signature and an infinite sequence of states (consisting of values for
/// all the functions in the signature at each point in time).
#[derive(PartialEq, Eq, Clone, Debug, Hash, PartialOrd, Ord)]
pub enum Term {
    /// A constant true or false
    Literal(bool),
    /// A reference to a bound variable or function in the signature
    Id(String),
    /// Application. `App(f, n_primes, args)` represents applying the function
    /// `f` with `n_primes` primes to `args`.
    App(String, usize, Vec<Term>),
    /// An applied unary operation
    UnaryOp(UOp, Box<Term>),
    /// An applied binary operation
    BinOp(BinOp, Box<Term>, Box<Term>),
    /// An applied n-ary operation
    NAryOp(NOp, Vec<Term>),
    /// If-then-else
    Ite {
        /// A boolean conditional
        cond: Box<Term>,
        /// Value of the Ite when `cond` is true
        then: Box<Term>,
        /// Value of the Ite when `cond` is false
        else_: Box<Term>,
    },
    /// A quantifier with a sequence of binders and a body where the binders
    /// might be used freely.
    #[allow(missing_docs)]
    Quantified {
        quantifier: Quantifier,
        /// The sequence of bindings bound by this quantifier. Might be empty.
        binders: Vec<Binder>,
        body: Box<Term>,
    },
}

impl Term {
    /// Flatten an n-ary relation one level deep.
    fn flatten_nary(self) -> Self {
        match self {
            Self::NAryOp(op, ts) => {
                let new_ts = ts
                    .into_iter()
                    .flat_map(|t| match t {
                        Self::NAryOp(op2, ts2) if op == op2 => ts2,
                        _ => vec![t],
                    })
                    .collect();
                Self::NAryOp(op, new_ts)
            }
            _ => self,
        }
    }

    /// Smart constructor for function applications
    pub fn app(f: &str, n_primes: usize, args: &[Term]) -> Self {
        Self::App(f.to_string(), n_primes, args.to_vec())
    }

    /// Smart constructor for an n-ary op from two arguments
    pub fn nary(op: NOp, lhs: Term, rhs: Term) -> Self {
        Self::NAryOp(op, vec![lhs, rhs]).flatten_nary()
    }

    /// Smart constructor equivalent to the And of an iterator of terms
    pub fn and<I>(ts: I) -> Self
    where
        I: IntoIterator,
        I::IntoIter: Iterator<Item = Term>,
    {
        let mut ts: Vec<Term> = ts.into_iter().collect();
        if ts.is_empty() {
            return Term::Literal(true);
        } else if ts.len() == 1 {
            return ts.pop().unwrap();
        }
        Self::NAryOp(NOp::And, ts)
    }

    /// Smart constructor equivalent to the Or of an iterator of terms
    pub fn or<I>(ts: I) -> Self
    where
        I: IntoIterator,
        I::IntoIter: Iterator<Item = Term>,
    {
        let mut ts: Vec<Term> = ts.into_iter().collect();
        if ts.is_empty() {
            return Term::Literal(false);
        } else if ts.len() == 1 {
            return ts.pop().unwrap();
        }
        Self::NAryOp(NOp::Or, ts)
    }

    /// Convenience function to create `lhs ==> rhs`
    pub fn implies(lhs: Term, rhs: Term) -> Self {
        Self::BinOp(BinOp::Implies, Box::new(lhs), Box::new(rhs))
    }

    /// Convenience function to create `lhs == rhs`
    pub fn equals(lhs: Term, rhs: Term) -> Self {
        Self::BinOp(BinOp::Equals, Box::new(lhs), Box::new(rhs))
    }

    /// Convenience function to create `!t`
    pub fn negate(t: Term) -> Self {
        Self::UnaryOp(UOp::Not, Box::new(t))
    }

    /// Construct a simplified term logically equivalent to `!t`
    pub fn negate_and_simplify(t: Term) -> Self {
        match t {
            Term::Literal(b) => Term::Literal(!b),
            Term::UnaryOp(UOp::Not, t) => *t,
            Term::UnaryOp(..) => panic!("got UnaryOp other than Not!"),
            Term::BinOp(BinOp::NotEquals, lhs, rhs) => Term::BinOp(BinOp::Equals, lhs, rhs),
            Term::BinOp(BinOp::Equals, lhs, rhs) => Term::BinOp(BinOp::NotEquals, lhs, rhs),
            Term::NAryOp(NOp::Or, terms) => Term::NAryOp(
                NOp::And,
                terms.into_iter().map(Term::negate_and_simplify).collect(),
            ),
            Term::NAryOp(NOp::And, terms) => Term::NAryOp(
                NOp::Or,
                terms.into_iter().map(Term::negate_and_simplify).collect(),
            ),
            Term::Id(_) | Term::App(_, _, _) => Term::negate(t),
            Term::Quantified {
                quantifier: Quantifier::Forall,
                binders,
                body,
            } => Term::Quantified {
                quantifier: Quantifier::Exists,
                binders,
                body: Box::new(Term::negate_and_simplify(*body)),
            },
            _ => panic!("got illegal operator in negate and simplify"),
        }
    }

    /// Convenience to construct `exists (binders), body`
    pub fn exists<I>(binders: I, body: Term) -> Self
    where
        I: IntoIterator,
        I::IntoIter: Iterator<Item = Binder>,
    {
        Self::Quantified {
            quantifier: Quantifier::Exists,
            binders: binders.into_iter().collect(),
            body: Box::new(body),
        }
    }

    /// Convenience to construct `forall (binders), body`
    pub fn forall<I>(binders: I, body: Term) -> Self
    where
        I: IntoIterator,
        I::IntoIter: Iterator<Item = Binder>,
    {
        Self::Quantified {
            quantifier: Quantifier::Forall,
            binders: binders.into_iter().collect(),
            body: Box::new(body),
        }
    }
}

/// A Sort represents a collection of values, which can be the built-in boolean
/// sort or a named sort (coming from a Signature).
#[allow(missing_docs)]
#[derive(PartialEq, Eq, Clone, Debug, Hash, Serialize, PartialOrd, Ord)]
pub enum Sort {
    Bool,
    Id(String),
}

impl Sort {
    /// Smart constructor for a named sort
    pub fn new<S: AsRef<str>>(s: S) -> Self {
        Self::Id(s.as_ref().to_string())
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Sort::Bool => "bool".to_string(),
            Sort::Id(i) => i.to_string(),
        };
        write!(f, "{s}")
    }
}

// TODO(oded): rename Relation to Function

/// The declaration of a single function as part of a Signature
#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct RelationDecl {
    /// If false, the relation is immutable with respect to time
    pub mutable: bool,
    /// The name of the function
    pub name: String,
    /// Sorts for the arguments (which are unnamed)
    pub args: Vec<Sort>,
    /// Sort for the return value
    pub sort: Sort,
}

/// A Signature defines a state space for an LTL Term, consisting of some number
/// of uninterpreted sorts and declarations for functions using those sorts (or
/// the built-in boolean sort).
#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct Signature {
    /// Names of uninterpreted sorts
    pub sorts: Vec<String>,
    /// Declarations for functions
    pub relations: Vec<RelationDecl>,
}

impl Signature {
    /// Get the index of an unintereted sort.
    pub fn sort_idx(&self, sort: &Sort) -> usize {
        match sort {
            Sort::Bool => panic!("invalid sort {sort}"),
            Sort::Id(sort) => self
                .sorts
                .iter()
                .position(|x| x == sort)
                .unwrap_or_else(|| panic!("invalid sort {sort}")),
        }
    }

    /// Get the declaration for a given name.
    ///
    /// Removes trailing primes from name and gives the underlying relation.
    pub fn relation_decl(&self, name: &str) -> &RelationDecl {
        let name = name.trim_end_matches('\'');
        self.relations
            .iter()
            .find(|x| x.name == name)
            .unwrap_or_else(|| panic!("could not find relation {name}"))
    }

    /// Returns true if name is an immutable relation, or a primed version of one.
    pub fn is_immutable(&self, name: &str) -> bool {
        let name = name.trim_end_matches('\'');
        match self.relations.iter().find(|x| x.name == name) {
            Some(decl) => !decl.mutable,
            None => false,
        }
    }

    /// Get the index of a named function in the signature. Panics if invalid.
    pub fn relation_idx(&self, name: &str) -> usize {
        self.relations
            .iter()
            .position(|x| x.name == name)
            .unwrap_or_else(|| panic!("invalid relation {name}"))
    }

    /// Check if `name` is a relation in the signature, or a primed version of
    /// one.
    pub fn contains_name(&self, name: &str) -> bool {
        let symbol_no_primes = name.trim_end_matches(|c| c == '\'');
        return self.relations.iter().any(|r| r.name == symbol_no_primes);
    }

    /// Compute all terms up to a certain nesting depth (optional), using the given variable names.
    /// If include_eq is true, include equality terms between any two same-sorted, non-Bool terms.
    ///
    /// Both sorted_vars and the returned vector match self.sorts w.r.t sorted indices, and have an extra final entry for the Bool sort.
    pub fn terms_by_sort(
        &self,
        sorted_vars: &[Vec<String>],
        mut depth: Option<usize>,
        include_eq: bool,
    ) -> Vec<Vec<Term>> {
        let sort_idx = |sort: &Sort| -> usize {
            match sort {
                Sort::Bool => self.sorts.len(),
                _ => self.sort_idx(sort),
            }
        };

        let mut terms = vec![vec![]; self.sorts.len() + 1];
        let mut new_terms = vec![vec![]; self.sorts.len() + 1];

        // Generate sorted variables.
        for (i, names) in sorted_vars.iter().enumerate() {
            for name in names {
                new_terms[i].push(Term::Id(name.clone()));
            }
        }

        // Generate constants.
        for rel_decl in &self.relations {
            if rel_decl.args.is_empty() {
                new_terms[sort_idx(&rel_decl.sort)].push(Term::Id(rel_decl.name.clone()));
            }
        }

        // Generated terms up to the given nesting depth, or until no new terms can be generated.
        while !new_terms.iter().all(|v| v.is_empty()) && depth.unwrap_or(1) > 0 {
            if let Some(n) = depth {
                depth = Some(n - 1);
            }

            let mut new_new_terms = vec![vec![]; self.sorts.len() + 1];
            for rel_decl in &self.relations {
                if rel_decl.args.is_empty() {
                    continue;
                }

                for new_ind in (0..rel_decl.args.len())
                    .map(|_| [false, true])
                    .multi_cartesian_product_fixed()
                {
                    // Only generate terms where at least one argument is a newly generated term,
                    // to make sure each term is generated exactly once.
                    if !new_ind.iter().any(|&x| x) {
                        continue;
                    }

                    let mut arg_terms = vec![];
                    for i in 0..rel_decl.args.len() {
                        if new_ind[i] {
                            arg_terms.push(&new_terms[sort_idx(&rel_decl.args[i])]);
                        } else {
                            arg_terms.push(&terms[sort_idx(&rel_decl.args[i])]);
                        }
                    }

                    if !arg_terms.iter().any(|v| v.is_empty()) {
                        for args in arg_terms
                            .iter()
                            .map(|&t| t.iter())
                            .multi_cartesian_product_fixed()
                        {
                            let term_vec = args.iter().map(|&x| x.clone()).collect();
                            new_new_terms[sort_idx(&rel_decl.sort)].push(Term::App(
                                rel_decl.name.clone(),
                                0,
                                term_vec,
                            ));
                        }
                    }
                }
            }

            for (i, ts) in new_terms.iter_mut().enumerate() {
                terms[i].append(ts);
            }
            new_terms = new_new_terms
        }

        for (i, vt) in new_terms.iter_mut().enumerate() {
            terms[i].append(vt);
        }

        // Generate equality terms.
        if include_eq {
            let mut eq_terms = vec![];
            for term in terms.iter().take(self.sorts.len()) {
                eq_terms.append(
                    &mut term
                        .iter()
                        .combinations(2)
                        .map(|v| {
                            Term::BinOp(
                                BinOp::Equals,
                                Box::new(v[0].clone()),
                                Box::new(v[1].clone()),
                            )
                        })
                        .collect(),
                );
            }
            terms[self.sorts.len()].append(&mut eq_terms);
        }

        terms
    }
}

/// A definition and its body. These are essentially treated as macros over the
/// functions in the signature.
#[allow(missing_docs)]
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Definition {
    pub name: String,
    pub binders: Vec<Binder>,
    pub ret_sort: Sort,
    pub body: Term,
}

/// A Span records a span of text in the source code, for error reporting.
#[derive(PartialEq, Eq, Copy, Clone, Debug, Serialize)]
pub struct Span {
    /// Start of the span as a character offset
    pub start: usize,
    /// End of the span as a character offset
    pub end: usize,
}

/// Wrap a value of type `T` with its `Span`
#[allow(missing_docs)]
#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct Spanned<T> {
    pub x: T,
    pub span: Span,
}

/// A Proof is an asserted boolean Term and a list of invariants to prove that
/// assertion inductively.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Proof {
    /// A boolean term to be proven equivalent to true
    pub assert: Spanned<Term>,
    /// Invariants whose conjunction should be inductive to prove `assert`
    pub invariants: Vec<Spanned<Term>>,
}

/// A theorem statement that can appear in a module. Statements are interpreted
/// imperatively in order, so earlier assumes and asserts may be used in later
/// checks.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum ThmStmt {
    /// Assume that a term is true without proof for the remaining statements
    Assume(Term),
    /// Assert a term with an inductive proof
    Assert(Proof),
}

/// A Module consists of a Signature and some theorem statements to be proven in that signature.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Module {
    /// Signature for all terms in the module
    pub signature: Signature,
    /// Helper definitions (essentially macros) that may be used in the module's
    /// statements
    pub defs: Vec<Definition>,
    /// A sequence of theorem statements that the module makes
    pub statements: Vec<ThmStmt>,
}

#[cfg(test)]
mod tests {
    use std::vec;

    use super::{RelationDecl, Signature, Sort};
    use crate::parser::term;

    #[test]
    fn test_terms_by_sort() {
        let sort = |n: usize| Sort::Id(format!("T{n}"));

        let mut sig = Signature {
            sorts: vec!["T1".to_string(), "T2".to_string()],
            relations: vec![
                RelationDecl {
                    mutable: true,
                    name: "c1".to_string(),
                    args: vec![],
                    sort: sort(1),
                },
                RelationDecl {
                    mutable: true,
                    name: "c2".to_string(),
                    args: vec![],
                    sort: sort(2),
                },
                RelationDecl {
                    mutable: true,
                    name: "f12".to_string(),
                    args: vec![sort(1)],
                    sort: sort(2),
                },
                RelationDecl {
                    mutable: true,
                    name: "f21".to_string(),
                    args: vec![sort(2)],
                    sort: sort(1),
                },
                RelationDecl {
                    mutable: true,
                    name: "r".to_string(),
                    args: vec![sort(2), sort(1)],
                    sort: Sort::Bool,
                },
            ],
        };

        let sorted_vars = vec![
            vec!["a1".to_string(), "a2".to_string()],
            vec!["b".to_string()],
        ];

        let mut terms = sig.terms_by_sort(&sorted_vars, Some(0), true);
        assert_eq!(
            terms,
            vec![
                vec![term("a1"), term("a2"), term("c1"),],
                vec![term("b"), term("c2"),],
                vec![term("a1=a2"), term("a1=c1"), term("a2=c1"), term("b=c2"),]
            ]
        );

        terms = sig.terms_by_sort(&sorted_vars, Some(2), false);
        assert_eq!(
            terms,
            vec![
                vec![
                    term("a1"),
                    term("a2"),
                    term("c1"),
                    term("f21(b)"),
                    term("f21(c2)"),
                    term("f21(f12(a1))"),
                    term("f21(f12(a2))"),
                    term("f21(f12(c1))"),
                ],
                vec![
                    term("b"),
                    term("c2"),
                    term("f12(a1)"),
                    term("f12(a2)"),
                    term("f12(c1)"),
                    term("f12(f21(b))"),
                    term("f12(f21(c2))"),
                ],
                vec![
                    term("r(b, a1)"),
                    term("r(b, a2)"),
                    term("r(b, c1)"),
                    term("r(c2, a1)"),
                    term("r(c2, a2)"),
                    term("r(c2, c1)"),
                    term("r(b, f21(b))"),
                    term("r(b, f21(c2))"),
                    term("r(c2, f21(b))"),
                    term("r(c2, f21(c2))"),
                    term("r(f12(a1), a1)"),
                    term("r(f12(a1), a2)"),
                    term("r(f12(a1), c1)"),
                    term("r(f12(a2), a1)"),
                    term("r(f12(a2), a2)"),
                    term("r(f12(a2), c1)"),
                    term("r(f12(c1), a1)"),
                    term("r(f12(c1), a2)"),
                    term("r(f12(c1), c1)"),
                    term("r(f12(a1), f21(b))"),
                    term("r(f12(a1), f21(c2))"),
                    term("r(f12(a2), f21(b))"),
                    term("r(f12(a2), f21(c2))"),
                    term("r(f12(c1), f21(b))"),
                    term("r(f12(c1), f21(c2))"),
                ]
            ]
        );

        sig = Signature {
            sorts: vec!["T1".to_string(), "T2".to_string()],
            relations: vec![
                RelationDecl {
                    mutable: true,
                    name: "c1".to_string(),
                    args: vec![],
                    sort: sort(1),
                },
                RelationDecl {
                    mutable: true,
                    name: "c2".to_string(),
                    args: vec![],
                    sort: sort(2),
                },
                RelationDecl {
                    mutable: true,
                    name: "f12".to_string(),
                    args: vec![sort(1)],
                    sort: sort(2),
                },
                RelationDecl {
                    mutable: true,
                    name: "r".to_string(),
                    args: vec![sort(2), sort(1)],
                    sort: Sort::Bool,
                },
            ],
        };

        terms = sig.terms_by_sort(&sorted_vars, None, false);
        assert_eq!(
            terms,
            vec![
                vec![term("a1"), term("a2"), term("c1"),],
                vec![
                    term("b"),
                    term("c2"),
                    term("f12(a1)"),
                    term("f12(a2)"),
                    term("f12(c1)"),
                ],
                vec![
                    term("r(b, a1)"),
                    term("r(b, a2)"),
                    term("r(b, c1)"),
                    term("r(c2, a1)"),
                    term("r(c2, a2)"),
                    term("r(c2, c1)"),
                    term("r(f12(a1), a1)"),
                    term("r(f12(a1), a2)"),
                    term("r(f12(a1), c1)"),
                    term("r(f12(a2), a1)"),
                    term("r(f12(a2), a2)"),
                    term("r(f12(a2), c1)"),
                    term("r(f12(c1), a1)"),
                    term("r(f12(c1), a2)"),
                    term("r(f12(c1), c1)"),
                ]
            ]
        );
    }
}

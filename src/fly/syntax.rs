// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::fmt;

use serde::Serialize;

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum UOp {
    Not,
    Prime,
    Always,
    Eventually,
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum BinOp {
    Equals,
    NotEquals,
    Implies,
    Iff,
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum NOp {
    And,
    Or,
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum Quantifier {
    Forall,
    Exists,
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct Binder {
    pub name: String,
    // ODED: I would rename typ to sort, here and elsewhere
    // ODED: not sure if we should have Option here until we have type inference
    pub typ: Option<Sort>,
}

// ODED: maybe Term should be Copy? (see test_eval in semantics.rs)
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum Term {
    Id(String),
    // ODED: I think we should have App(String, Vec<Term>), since we're not high-order (yet)
    App(Box<Term>, Vec<Term>),
    UnaryOp(UOp, Box<Term>),
    BinOp(BinOp, Box<Term>, Box<Term>),
    NAryOp(NOp, Vec<Term>),
    #[allow(dead_code)]
    Ite {
        cond: Box<Term>,
        then: Box<Term>,
        else_: Box<Term>,
    },
    Quantified {
        quantifier: Quantifier,
        binders: Vec<Binder>,
        body: Box<Term>,
    },
    /// let (binder) = (val) in (body)
    Let {
        binder: Binder,
        val: Box<Term>,
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

    pub fn nary(op: NOp, lhs: Term, rhs: Term) -> Self {
        Self::NAryOp(op, vec![lhs, rhs]).flatten_nary()
    }

    pub fn and<I>(ts: I) -> Self
    where
        I: IntoIterator,
        I::IntoIter: Iterator<Item = Term>,
    {
        let mut ts: Vec<Term> = ts.into_iter().collect();
        if ts.is_empty() {
            return Term::Id("true".to_string());
        } else if ts.len() == 1 {
            return ts.pop().unwrap();
        }
        Self::NAryOp(NOp::And, ts)
    }

    pub fn or<I>(ts: I) -> Self
    where
        I: IntoIterator,
        I::IntoIter: Iterator<Item = Term>,
    {
        let mut ts: Vec<Term> = ts.into_iter().collect();
        if ts.is_empty() {
            return Term::Id("false".to_string());
        } else if ts.len() == 1 {
            return ts.pop().unwrap();
        }
        Self::NAryOp(NOp::Or, ts)
    }

    pub fn implies(lhs: Term, rhs: Term) -> Self {
        Self::BinOp(BinOp::Implies, Box::new(lhs), Box::new(rhs))
    }

    pub fn equals(lhs: Term, rhs: Term) -> Self {
        Self::BinOp(BinOp::Equals, Box::new(lhs), Box::new(rhs))
    }

    pub fn negate(t: Term) -> Self {
        Self::UnaryOp(UOp::Not, Box::new(t))
    }

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

#[derive(PartialEq, Eq, Clone, Debug, Hash, Serialize)]
pub enum Sort {
    Bool,
    Id(String),
}

impl Sort {
    pub fn new<S: AsRef<str>>(s: S) -> Self {
        Self::Id(s.as_ref().to_string())
    }

    /// Get the name of this sort if it's a user-declared sort, or None for the
    /// built-in Bool.
    pub fn id(&self) -> Option<&str> {
        match self {
            Sort::Bool => None,
            Sort::Id(s) => Some(s),
        }
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

#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct RelationDecl {
    pub mutable: bool,
    pub name: String,
    pub args: Vec<Sort>,
    pub typ: Sort,
}

#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct Signature {
    /// sorts shouldn't contain Bool, it should contain only uninterpreted sorts
    pub sorts: Vec<Sort>,
    pub relations: Vec<RelationDecl>,
}

impl Signature {
    pub fn sort_idx(&self, sort: &Sort) -> usize {
        self.sorts
            .iter()
            .position(|x| x == sort)
            .unwrap_or_else(|| panic!("invalid sort {sort}"))
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

    pub fn relation_idx(&self, name: &str) -> usize {
        self.relations
            .iter()
            .position(|x| x.name == name)
            .unwrap_or_else(|| panic!("invalid relation {name}"))
    }
}

/// A Span records a span of text in the source code, for error reporting.
#[derive(PartialEq, Eq, Copy, Clone, Debug, Serialize)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct Spanned<T> {
    pub x: T,
    pub span: Span,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Proof {
    pub assert: Spanned<Term>,
    pub invariants: Vec<Spanned<Term>>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum ThmStmt {
    Assume(Term),
    Assert(Proof),
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Module {
    pub signature: Signature,
    pub statements: Vec<ThmStmt>,
}

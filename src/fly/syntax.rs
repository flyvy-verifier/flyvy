// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::fmt;

use codespan_reporting::diagnostic::{Diagnostic, Label};
use peg::{error::ParseError, str::LineCol};
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

    fn nary(op: NOp, lhs: Term, rhs: Term) -> Self {
        Self::NAryOp(op, vec![lhs, rhs]).flatten_nary()
    }

    pub fn and(mut ts: Vec<Term>) -> Self {
        if ts.is_empty() {
            return Term::Id("true".to_string());
        } else if ts.len() == 1 {
            return ts.pop().unwrap();
        }
        Self::NAryOp(NOp::And, ts)
    }

    pub fn implies(lhs: Term, rhs: Term) -> Self {
        Self::BinOp(BinOp::Implies, Box::new(lhs), Box::new(rhs))
    }

    pub fn negate(t: Term) -> Self {
        Self::UnaryOp(UOp::Not, Box::new(t))
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Serialize)]
pub enum Sort {
    Bool,
    Id(String),
}

impl Sort {
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

// ODED: I would move the parser to parser.rs
peg::parser! {

grammar parser() for str {
    use BinOp::*;
    use NOp::*;
    use UOp::*;
    use Quantifier::*;

    rule ident_start() = ['a'..='z' | 'A'..='Z' | '_']
    rule ident_char() = ident_start() / ['0'..='9']
    pub(super) rule ident() -> String
    = s:$(quiet!{ident_start() ident_char()*} / expected!("identifier"))
    { s.to_string() }

    rule nl() = quiet!{ ['\n' | '\r'] } / expected!("newline")
    rule comment() = "#" [^'\n' | '\r']* nl()
    rule ws_no_nl() = quiet!{ [' ' | '\t' ] / comment() }
    rule whitespace() = quiet! { ws_no_nl() / nl() }
    rule word_boundary() = !ident_char()
    rule _ = whitespace()*
    rule __ = word_boundary() _

    rule binder() -> Binder
    =  "(" name:ident() _ ":" _ typ:sort() ")" { Binder {name, typ: Some(typ) } } /
       name:ident() typ:(_ ":" _ s:sort() { s })? { Binder { name, typ } }

    pub(super) rule term() -> Term = precedence!{
        q:("forall" { Forall } / "exists" { Exists }) __
            binders:(binder() ** (_ "," _)) _ "." _ body:@
        { Term::Quantified {
            quantifier: q,
            binders,
            body: Box::new(body),
          } }

        --

        x:@ _ "->" _ y:(@) { Term::BinOp(Implies, Box::new(x), Box::new(y)) }
        x:(@) _ "<->" _ y:@ { Term::BinOp(Iff, Box::new(x), Box::new(y)) }
        --

        op:("always" { Always } / "eventually" { Eventually }) __ x:@
        { Term::UnaryOp(op, Box::new(x)) }

        --
        x:(@) _ "&" _ y:@ { Term::nary(And, x, y) }
        --
        x:(@) _ "|" _ y:@ { Term::nary(Or, x, y) }
        --
        x:(@) _ "=" _ y:@ { Term::BinOp(Equals, Box::new(x), Box::new(y)) }
        x:(@) _ "!=" _ y:@ { Term::BinOp(NotEquals, Box::new(x), Box::new(y)) }
        --
        "!" x:@ { Term::UnaryOp(Not, Box::new(x)) }
        --
        t:(@) "'" { Term::UnaryOp(Prime, Box::new(t)) }
        --
        // note that no space is allowed between relation name and args, so p (q)
        // doesn't parse as a relation call
        t:(@) "(" args:(term() ** (_ "," _)) ")" { Term::App(Box::new(t), args) }
        s:ident() { Term::Id(s) }
        "(" _ t:term() _ ")" { t }
    }

    rule sort() -> Sort
    = ("bool" word_boundary() { Sort::Bool }) /
      s:ident() { Sort::Id(s) }

    rule sort_decl() -> Sort
    = "sort" __ s:sort() { s }

    // matches whitespace with at least one newline
    rule newline_separator()
    = quiet!{ ws_no_nl()* (comment() / nl()) _ } / expected!("newline separator")

    rule newline_separated<T>(e: rule<T>) -> Vec<T>
    = e() ** newline_separator()

    rule mutability() -> bool
    = "mutable" word_boundary() { true } /
      "immutable" word_boundary() { false }

    rule relation_args() -> Vec<Sort>
    = "(" _ ss:(sort() ** (_ "," _)) _ ")" { ss } /
       "" { vec![] }

    rule relation_decl() -> RelationDecl
    = m:mutability() _ r:ident() args:relation_args() _ ":" _ s:sort()
    { RelationDecl{
      mutable: m,
      name: r,
      args,
      typ: s,
    } }

    pub(super) rule signature() -> Signature
    = sorts:newline_separated(<sort_decl()>) _
      relations:newline_separated(<relation_decl()>)
     { Signature {
        sorts,
        relations,
     } }

     rule assume_stmt() -> ThmStmt
     = "assume" __ t:term() { ThmStmt::Assume(t) }

     rule invariants() -> Vec<Spanned<Term>>
     = newline_separated(<spanned(<"invariant" __ t:term() { t }>)>)

     rule assert_stmt() -> ThmStmt
     = t:spanned(<"assert" __ t:term() {t}>)
       invariants:(newline_separator()
        "proof" __ "{" _ invs:invariants() _ "}" {invs})?
       { ThmStmt::Assert(Proof{
          assert: t, invariants: invariants.unwrap_or_default(),
         }) }

      pub(super) rule stmt() -> ThmStmt
      = assume_stmt() / assert_stmt()

     rule stmts() -> Vec<ThmStmt>
     = newline_separated(<stmt()>)

     rule module0() -> Module
     = _ sig:signature() _ thm:stmts() _
       { Module{
          signature: sig, statements: thm,
         } }

      pub rule module() -> Module = traced(<module0()>)

      rule spanned<T>(e: rule<T>) -> Spanned<T>
      = start:position!() x:e() end:position!()
        { Spanned {x, span: Span{start,end} } }

     // wrap a rule with tracing support, gated under the trace feature
     rule traced<T>(e: rule<T>) -> T =
         &(input:$([_]*) {
             #[cfg(feature = "trace")]
             println!("[PEG_INPUT_START]\n{}\n[PEG_TRACE_START]", input);
         })
         e:e()? {?
             #[cfg(feature = "trace")]
             println!("[PEG_TRACE_STOP]");
             e.ok_or("")
         }
  }
}

#[cfg(test)]
mod tests {
    use super::parser::*;
    use super::*;

    #[test]
    fn test_ident() {
        assert_eq!(ident("hello"), Ok("hello".to_string()));
        assert_eq!(ident("a"), Ok("a".to_string()));
        assert_eq!(ident("hello_world"), Ok("hello_world".to_string()));
        assert_eq!(ident("_allowed"), Ok("_allowed".to_string()));
        assert!(ident("1up").is_err());
    }

    #[test]
    fn test_term() {
        term("!p & !q").unwrap();

        term("p''").unwrap();
        term("(p')'").unwrap();

        term("p(x, y)").unwrap();
        term("p(x,y)").unwrap();

        // not first order (but eventually f might be a meta abstraction that
        // reduces to a relation)
        term("(f(x))(a, b)").unwrap();

        // non-sensical but does parse
        term("(!p)(a)").unwrap();

        // & and | at the same level are grouped into a single NAry
        assert_eq!(term("(p & q) & r").unwrap(), term("p & q & r").unwrap());
        assert_eq!(term("p & (q & r)").unwrap(), term("p & q & r").unwrap());
        assert_eq!(term("p | (q | r)").unwrap(), term("(p | q) | r").unwrap());

        // always is treated as an atomic keyword
        assert_ne!(term("alwaysx").unwrap(), term("always x").unwrap());

        assert!(term("= x").is_err());
    }

    #[test]
    fn test_term_precedence() {
        assert_eq!(
            term("!p & !q & !r").unwrap(),
            term("(!p) & (!q) & (!r)").unwrap()
        );

        assert_eq!(
            term("always p'=(p|q) & q'=q").unwrap(),
            term("always (p'=(p|q) & ((q')=q))").unwrap()
        );
    }

    #[test]
    fn test_signature() {
        let s = signature(
            r"mutable p: bool
mutable q: bool",
        )
        .unwrap();
        assert_eq!(s.relations.len(), 2);
    }

    #[test]
    fn test_module() {
        let m = module(
            r"mutable p: bool
mutable q: bool

assume !p & !q & (always p'=(p|q) & q'=q)
assert always !p
proof {
    invariant !p
    invariant !q
    # invariant $l2s_w. p
}

# we don't allow this: forall x:t1. exists x:t2. p(x:t1, x:t2)
",
        )
        .unwrap();
        assert_eq!(m.signature.relations.len(), 2);
        assert_eq!(m.statements.len(), 2);
        match &m.statements[1] {
            ThmStmt::Assert(pf) => {
                assert_eq!(pf.invariants.len(), 2, "wrong number of invariants parsed")
            }
            _ => panic!("incorrect 2nd statement"),
        }
    }

    #[test]
    fn test_quantifiers() {
        term("forall x. x = y").unwrap();
        term("forall x:t, y:t. x = y").unwrap();
        term("forall x:t,y:t. x = y").unwrap();
        term("forall x:t , y:t. x = y").unwrap();
        term("forall x:t, y:t. x = y | y != x").unwrap();
        term("forall (x : t). x").unwrap();
        term("forall (x : t),(y:t). x = y").unwrap();

        assert_eq!(
            term("forall x. x = y & exists z. x = z").unwrap(),
            term("forall x. (x = y & exists z. x = z)").unwrap(),
        );

        assert_eq!(
            term("forall (x : t), (y : t2). f(x) & f(y)").unwrap(),
            term("forall x:t, y:t2 . f(x) & f(y)").unwrap(),
        );
    }
}

#[cfg(test)]
/// Parse a single term. Only used for testing.
pub fn parse_term(s: &str) -> Result<Term, String> {
    parser::term(s).map_err(|err| err.to_string())
}

/// Parse a fly module, reporting a human-readable error on failure.
pub fn parse(s: &str) -> Result<Module, ParseError<LineCol>> {
    parser::module(s)
}

pub fn parse_error_diagonistic<FileId>(
    file_id: FileId,
    e: &ParseError<LineCol>,
) -> Diagnostic<FileId> {
    Diagnostic::error()
        .with_message("could not parse file")
        .with_labels(vec![Label::primary(
            file_id,
            e.location.offset..e.location.offset + 1,
        )
        .with_message(format!("expected {}", e.expected))])
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A custom s-expression data type and parsing.
//!
//! This implementation supports comments as part of the grammar, since they are
//! needed to fully parse the models returned by for example CVC5.

use std::fmt;

use peg::str::LineCol;
use serde::Serialize;

#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, PartialOrd, Ord)]
pub enum Atom {
    I(usize),
    S(String),
}

impl Atom {
    /// Return the string value of self, if it is a string.
    pub fn s(&self) -> Option<&str> {
        if let Self::S(s) = self {
            Some(s)
        } else {
            None
        }
    }
}

/// An s-expression which also tracks comments.
#[allow(missing_docs)]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, PartialOrd, Ord)]
pub enum Sexp {
    Atom(Atom),
    Comment(String),
    List(Vec<Sexp>),
}

/// Construct an sexp atom from a string.
pub fn atom_s<S: AsRef<str>>(s: S) -> Sexp {
    Sexp::Atom(Atom::S(s.as_ref().to_string()))
}

/// Construct an sexp atom from an integer.
pub fn atom_i(i: usize) -> Sexp {
    Sexp::Atom(Atom::I(i))
}

/// Construct an sexp list from an iteratable.
pub fn sexp_l<I>(i: I) -> Sexp
where
    I: IntoIterator,
    I::IntoIter: Iterator<Item = Sexp>,
{
    Sexp::List(i.into_iter().collect())
}

/// Construct an sexp list with a string atom as its "head" element, followed by
/// an iterable of remaining arguments.
pub fn app<I>(head: &str, args: I) -> Sexp
where
    I: IntoIterator,
    I::IntoIter: Iterator<Item = Sexp>,
{
    let mut ss = vec![atom_s(head)];
    #[allow(clippy::useless_conversion)]
    ss.extend(args.into_iter());
    Sexp::List(ss)
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Atom::I(i) => write!(f, "{i}"),
            Atom::S(s) => {
                if s.contains([' ', '\"', '\'']) {
                    write!(f, "|{s}|")
                } else if s.contains('|') {
                    write!(f, "\"{s}\"")
                } else {
                    write!(f, "{s}")
                }
            }
        }
    }
}

impl fmt::Display for Sexp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sexp::Atom(s) => write!(f, "{s}"),
            Sexp::Comment(s) => write!(f, ";{s}"),
            Sexp::List(ss) => {
                write!(f, "(")?;
                for (i, s) in ss.iter().enumerate() {
                    let last = i == ss.len() - 1;
                    let this_comment = matches!(s, Sexp::Comment(_));
                    let next_comment = !last && matches!(ss[i + 1], Sexp::Comment(_));
                    let space = if last || this_comment || next_comment {
                        ""
                    } else {
                        " "
                    };
                    if this_comment {
                        write!(f, "\n{s}\n{space}")?;
                    } else {
                        write!(f, "{s}{space}")?;
                    }
                }
                write!(f, ")")?;
                Ok(())
            }
        }
    }
}

impl Sexp {
    /// Return the inner elements if self is a Sexp::List
    pub fn list(&self) -> Option<&[Sexp]> {
        if let Sexp::List(ss) = self {
            Some(ss)
        } else {
            None
        }
    }

    /// Return the inner string if self is a string atom.
    pub fn atom_s(&self) -> Option<&str> {
        if let Sexp::Atom(Atom::S(s)) = self {
            Some(s)
        } else {
            None
        }
    }

    /// Return the head and tail if self is of the form `(head rest..)`.
    pub fn app(&self) -> Option<(&str, &[Sexp])> {
        self.list().and_then(|ss| {
            if !ss.is_empty() {
                if let Some(head) = ss[0].atom_s() {
                    return Some((head, &ss[1..]));
                }
            }
            None
        })
    }
}

peg::parser! {
grammar parser() for str {
  rule ident_start() = ['a'..='z' | 'A'..='Z' | '_' | '\'' | '<' | '>' | ':' | '=' | '$' | '@' ]
  rule ident_char() = ident_start() / ['0'..='9' | '!' | '#' | '%' | '-' | '.']
  rule ident() = quiet! { ident_start() ident_char()* } / expected!("atom")

  rule whitespace() = [' ' | '\t' | '\n' | '\r']
  rule _ = whitespace()*

  rule quoted_atom() -> Atom
  = "\"" s:$([^'"']*) "\"" { Atom::S(s.to_string()) }

  rule pipe_quoted_atom() -> Atom
  = "|" s:$([^'|']*) "|" { Atom::S(s.to_string()) }

  rule unquoted_atom() -> Atom
  = s:$(ident()) { Atom::S(s.to_string()) }

  rule int_atom() -> Atom
  = i:$(['0'..='9']+) { Atom::I(i.parse().unwrap()) }

  rule atom() -> Sexp
  = s:(quoted_atom() /
       pipe_quoted_atom() /
       unquoted_atom() /
       int_atom()) { Sexp::Atom(s) }

  rule comment() -> Sexp
  = ";" s:$(([^'\n']*)) ['\n'] { Sexp::Comment(s.to_string()) }

  rule list() -> Sexp
  = "(" _ ss:(sexp() ** _) _ ")" { Sexp::List(ss) }

  rule sexp() -> Sexp
  = atom() / comment() / list()

  /// Parse an sexp but be tolerant to whitespace around it.
  pub(super) rule sexp_whitespace() -> Sexp
  = _ s:sexp() _ { s }

  /// Parse a sequence of sexps.
  pub(super) rule sexps() -> Vec<Sexp>
  = _ ss:(sexp() ** _) _ { ss }
}
}

/// Parse an sexp.
///
/// Allows whitespace before or after.
pub fn parse(s: &str) -> Result<Sexp, peg::error::ParseError<LineCol>> {
    parser::sexp_whitespace(s)
}

/// Parse a sequence of sexps, separated by whitespace.
pub fn parse_many(s: &str) -> Result<Vec<Sexp>, peg::error::ParseError<LineCol>> {
    parser::sexps(s)
}

#[cfg(test)]
mod tests {
    use super::parse;
    use super::{app, atom_i, atom_s, sexp_l};

    #[test]
    fn test_parsing() {
        assert_eq!(
            parse("(foo  a (bar () 1))"),
            Ok(app(
                "foo",
                [atom_s("a"), app("bar", [sexp_l([]), atom_i(1)])]
            ))
        );
    }

    #[test]
    fn test_printing() {
        let e = parse(
            r#"(hello a b c (there
            ; here's a comment
            (friend)))
            "#,
        )
        .unwrap();
        insta::assert_display_snapshot!(e, @r#"
        (hello a b c (there
        ; here's a comment
        (friend)))
        "#);
    }

    #[test]
    fn test_parsing_unusual_chars() {
        let s = vec![
            "(p A!val!0)",
            "(q foo.thread@0)",
            "<<DONE>>\n",
            "\n<<DONE>>\n",
            "(:reason-unknown \"timeout\")",
        ]
        .into_iter()
        .map(|s| parse(s).unwrap());
        let printed: Vec<String> = s.map(|s| s.to_string()).collect();
        insta::assert_display_snapshot!(printed.join("\n"), @r###"
        (p A!val!0)
        (q foo.thread@0)
        <<DONE>>
        <<DONE>>
        (:reason-unknown timeout)
        "###);
    }

    #[test]
    fn test_roundtrip_parsing() {
        let mut es = vec![];
        for s in vec![
            r#"  "hello there" "#,
            r#"|"hello"|"#,
            r#"|also has a space|"#,
            r#"(forall ((x thread)) (= x thread!val!0))"#,
        ]
        .into_iter()
        {
            let e = parse(s).unwrap_or_else(|_| panic!("`{s}` did not parse"));
            es.push(e.clone());
            assert_eq!(
                parse(&e.to_string()).unwrap(),
                e,
                "`{s}` does not roundtrip",
            );
        }
        insta::assert_display_snapshot!(&es[0], @"|hello there|");
        insta::assert_display_snapshot!(&es[1], @r#"|"hello"|"#);
        insta::assert_display_snapshot!(&es[2], @"|also has a space|");
    }
}

// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use lazy_static::lazy_static;
use serde::Serialize;
use std::{collections::HashMap, iter};
use thiserror::Error;

use regex::Regex;

use crate::smtlib::sexp::{atom_s, sexp_l, Atom, Sexp};

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct Model {
    pub universes: HashMap<String, Vec<String>>,
    pub symbols: HashMap<String, (Vec<String>, Sexp)>,
}

#[derive(Debug, Error)]
#[error("eval error: {0}")]
pub struct EvalError(String);

fn bool_atom(b: bool) -> Atom {
    let v = if b { "true" } else { "false" };
    Atom::S(v.to_string())
}

fn subst_hashmap(repl: &HashMap<&String, &Sexp>, e: &Sexp) -> Sexp {
    match e {
        Sexp::Atom(Atom::I(_)) | Sexp::Comment(_) => e.clone(),
        Sexp::Atom(Atom::S(s)) => repl.get(s).cloned().unwrap_or(e).clone(),
        Sexp::List(ss) => Sexp::List(ss.iter().map(|e| subst_hashmap(repl, e)).collect()),
    }
}

/// Parallel substitution into an sexp.
pub fn subst(repl: &[(&String, Sexp)], e: &Sexp) -> Sexp {
    let mut repl_map: HashMap<&String, &Sexp> = HashMap::new();
    for (name, e) in repl {
        let old = repl_map.insert(name, e);
        assert_eq!(old, None, "duplicate replacement for {name} in subst");
    }
    subst_hashmap(&repl_map, e)
}

fn parse_binders(binders: &Sexp) -> Vec<String> {
    let binder_sexps = binders.list().unwrap();
    binder_sexps
        .iter()
        .map(|b| {
            // b should be a list of (name type)
            let ss = b.list().unwrap();
            assert!(ss.len() == 2, "binder is ill-formed");
            ss[0].atom_s().unwrap().to_string()
        })
        .collect()
}

pub(crate) fn parse_z3(model: &Sexp) -> Model {
    let mut universes: HashMap<String, Vec<String>> = HashMap::new();
    let mut symbols: HashMap<String, (Vec<String>, Sexp)> = HashMap::new();
    if let Some(ss) = model.list() {
        // remove a leading "model" for older versions
        let ss = if !ss.is_empty() && ss[0] == atom_s("model") {
            &ss[1..]
        } else {
            ss
        };
        for s in ss {
            if let Some((head, args)) = s.app() {
                if head == "declare-fun" {
                    assert_eq!(args.len(), 3, "declare-fun should have name, binders, sort");
                    let name = args[0].atom_s().unwrap().to_string();
                    let binders = &args[1];
                    let sort = args[2].atom_s().unwrap();
                    // this is a universe element, with no body
                    assert_eq!(
                        binders,
                        &sexp_l([]),
                        "universe elements should take no argments"
                    );
                    universes.entry(sort.to_string()).or_default().push(name);
                } else if head == "define-fun" {
                    assert_eq!(
                        args.len(),
                        4,
                        "define-fun should have name, binders, sort, body"
                    );
                    let name = args[0].atom_s().unwrap().to_string();
                    let binders = parse_binders(&args[1]);
                    // let sort = args[2].atom_s().unwrap();
                    let body = args[3].clone();
                    symbols.insert(name, (binders, body));
                } else if head == "forall" {
                    // ignore, cardinality constraint
                } else {
                    eprintln!("warning: unexpected {head} in z3 model")
                }
            }
        }
    }
    Model { universes, symbols }
}

pub(crate) fn parse_cvc(model: &Sexp, version5: bool) -> Model {
    let version4 = !version5;
    let mut universe_cardinalities: HashMap<String, usize> = HashMap::new();
    let mut symbols: HashMap<String, (Vec<String>, Sexp)> = HashMap::new();
    lazy_static! {
        static ref CARDINALITY_RE: Regex = Regex::new("cardinality of (.*) is ([0-9]+)$").unwrap();
    }
    if let Some(ss) = model.list() {
        // remove a leading "model" for CVC4
        let ss = {
            if version4 {
                assert!(!ss.is_empty());
                assert_eq!(ss[0], atom_s("model"));
                &ss[1..]
            } else {
                ss
            }
        };
        for s in ss {
            if let Sexp::Comment(s) = s {
                if let Some(cs) = CARDINALITY_RE.captures(s) {
                    let sort = cs.get(1).unwrap().as_str().to_string();
                    let card = cs.get(2).unwrap().as_str().parse::<usize>().unwrap();
                    universe_cardinalities.insert(sort, card);
                }
                continue;
            }
            if let Some((head, args)) = s.app() {
                if head == "define-fun" {
                    assert_eq!(
                        args.len(),
                        4,
                        "define-fun should have name, binders, sort, body"
                    );
                    let name = args[0].atom_s().unwrap().to_string();
                    let binders = parse_binders(&args[1]);
                    // let sort = args[2].atom_s().unwrap();
                    let body = args[3].clone();
                    symbols.insert(name, (binders, body));
                } else if version4 && head == "declare-sort" {
                    // cvc4 only
                    continue;
                } else {
                    eprintln!("warning: unexpected {head} in cvc model")
                }
            }
        }
    }
    let mut universes = HashMap::new();
    for (sort, card) in universe_cardinalities.into_iter() {
        let elements: Vec<String> = (0..card)
            .map(|i| {
                if version4 {
                    format!("@uc_{sort}_{i}")
                } else {
                    format!("@{sort}_{i}")
                }
            })
            .collect();
        universes.insert(sort, elements);
    }
    Model { universes, symbols }
}

impl Model {
    fn eval_bool(&self, e: &Sexp) -> Result<bool, EvalError> {
        let a = self.smt_eval(e)?;
        match a {
            Atom::S(s) if s == "true" => Ok(true),
            Atom::S(s) if s == "false" => Ok(false),
            _ => Err(EvalError(format!("unexpected bool: {a}"))),
        }
    }

    /// Evaluate an SMT expression, reducing constants with known semantics. Fails
    /// if this does not result in an Atom.
    pub fn smt_eval(&self, e: &Sexp) -> Result<Atom, EvalError> {
        match e {
            Sexp::Atom(a) => Ok(a.clone()),
            Sexp::Comment(_) => Err(EvalError("comment".to_string())),
            Sexp::List(ss) => {
                let ss = ss
                    .iter()
                    .filter(|s| !matches!(s, Sexp::Comment(_)))
                    .collect::<Vec<_>>();
                if ss.is_empty() {
                    return Err(EvalError("empty list".to_string()));
                }
                let head = ss[0].atom_s().ok_or(EvalError(format!(
                    "unexpected function {} (non-atom)",
                    ss[0]
                )))?;
                let args = &ss[1..];
                if head == "and" {
                    let args = args
                        .iter()
                        .map(|s| self.eval_bool(s))
                        .collect::<Result<Vec<_>, _>>()?;
                    let v = args.iter().all(|x| *x);
                    Ok(bool_atom(v))
                } else if head == "or" {
                    let args = args
                        .iter()
                        .map(|s| self.eval_bool(s))
                        .collect::<Result<Vec<_>, _>>()?;
                    let v = args.iter().any(|x| *x);
                    Ok(bool_atom(v))
                } else if head == "not" || head == "!" {
                    assert_eq!(args.len(), 1);
                    let x = self.eval_bool(args[0])?;
                    Ok(bool_atom(!x))
                } else if head == "as" {
                    // type cast (basically ignored)
                    self.smt_eval(args[0])
                } else if head == "=" {
                    assert_eq!(args.len(), 2);
                    let lhs = self.smt_eval(args[0])?;
                    let rhs = self.smt_eval(args[1])?;
                    Ok(bool_atom(lhs == rhs))
                } else if head == "ite" {
                    assert_eq!(args.len(), 3);
                    let cond = self.eval_bool(args[0])?;
                    if cond {
                        self.smt_eval(args[1])
                    } else {
                        self.smt_eval(args[2])
                    }
                } else if self.symbols.contains_key(head) {
                    let (binders, body) = &self.symbols[head];
                    assert_eq!(
                        binders.len(),
                        args.len(),
                        "wrong number of arguments to {head}"
                    );
                    let repl: Vec<(&String, Sexp)> = iter::zip(binders, args.iter().cloned())
                        .map(|(name, e)| (name, e.clone()))
                        .collect();
                    self.smt_eval(&subst(&repl, &body))
                } else {
                    Err(EvalError(format!("unexpected function {head}")))
                }
            }
        }
    }
}

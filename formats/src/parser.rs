//! A module containing parsing utilities, e.g. for parsing SMTLIB2 s-expressions into a system of CHCs.

use crate::chc::{ChcSystem, Component, FunctionSort, HoPredicateDecl, HoVariable};
use fly::{
    syntax::{Signature, Term},
    term::subst::Substitutable,
};
use regex::Regex;
use smtlib::sexp::{atom_i, atom_s, Sexp};

enum SmtlibLine {
    Sort(String),
    Predicate(HoPredicateDecl),
    Var(HoVariable),
    Chc {
        variables: Vec<HoVariable>,
        body: Vec<Component>,
        head: Component,
    },
    Ignore,
}

impl SmtlibLine {
    fn parse_predicate(name: &Sexp, args: &[Sexp]) -> Self {
        Self::Predicate(HoPredicateDecl {
            name: name.atom_s().unwrap().to_string(),
            args: args
                .iter()
                .map(|a| FunctionSort(vec![], a.sort().unwrap()))
                .collect(),
        })
    }

    fn parse_var(name: &Sexp, sort: &Sexp) -> Self {
        Self::Var(HoVariable {
            name: name.atom_s().unwrap().to_string(),
            sort: FunctionSort(vec![], sort.sort().unwrap()),
        })
    }

    fn parse_chc(
        chc_sys: &ChcSystem,
        global_vars: &[HoVariable],
        binders: &[Sexp],
        body: &Sexp,
        head: &Sexp,
    ) -> Self {
        let parse_component = |t: Term| -> Component {
            match t {
                Term::Id(name) if chc_sys.predicates.iter().any(|p| p.name == name) => {
                    Component::Predicate(name, vec![])
                }
                Term::App(name, 0, args) if chc_sys.predicates.iter().any(|p| p.name == name) => {
                    Component::Predicate(name, args.into_iter().map(Substitutable::Term).collect())
                }
                _ => Component::Formulas(t.as_conjunction()),
            }
        };

        let variables = global_vars
            .iter()
            .cloned()
            .chain(binders.iter().map(|s| {
                let l = s.list().unwrap();
                HoVariable {
                    name: l[0].atom_s().unwrap().to_string(),
                    sort: FunctionSort(vec![], l[1].sort().unwrap()),
                }
            }))
            .collect();

        let head_component = parse_component(head.term());

        let body_components = body
            .term()
            .as_conjunction()
            .into_iter()
            .map(parse_component)
            .collect();

        Self::Chc {
            variables,
            body: body_components,
            head: head_component,
        }
    }

    fn parse(chc_sys: &ChcSystem, global_vars: &[HoVariable], s: &Sexp) -> Self {
        match s {
            Sexp::Comment(_) => Self::Ignore,
            Sexp::List(l) => match l[0].atom_s().unwrap() {
                "set-logic" | "check-sat" | "get-model" | "exit" => Self::Ignore,
                "declare-sort" => {
                    assert_eq!(&l[2], &atom_i(0));
                    Self::Sort(l[1].atom_s().unwrap().to_string())
                }
                "declare-var" => SmtlibLine::parse_var(&l[1], &l[2]),
                "declare-rel" => SmtlibLine::parse_predicate(&l[1], l[2].list().unwrap()),
                "declare-const" => {
                    assert_eq!(l[2].atom_s(), Some("Bool"));
                    SmtlibLine::parse_predicate(&l[1], &[])
                }
                "declare-fun" => {
                    assert_eq!(l[3].atom_s(), Some("Bool"));
                    SmtlibLine::parse_predicate(&l[1], l[2].list().unwrap())
                }
                "assert" | "rule" => {
                    if let Some(app) = l[1].app() {
                        match app {
                            ("forall", rest) => {
                                let binders = rest[0].list().unwrap();
                                let (implies, body_head) = rest[1].app().unwrap();
                                assert_eq!(implies, "=>");
                                return SmtlibLine::parse_chc(
                                    chc_sys,
                                    global_vars,
                                    binders,
                                    &body_head[0],
                                    &body_head[1],
                                );
                            }
                            ("=>", body_head) => {
                                return SmtlibLine::parse_chc(
                                    chc_sys,
                                    global_vars,
                                    &[],
                                    &body_head[0],
                                    &body_head[1],
                                )
                            }
                            _ => (),
                        }
                    }
                    SmtlibLine::parse_chc(chc_sys, global_vars, &[], &atom_s("true"), &l[1])
                }
                "query" => {
                    SmtlibLine::parse_chc(chc_sys, global_vars, &[], &l[1], &atom_s("false"))
                }
                _ => panic!("unsupported list head: {}", l[0]),
            },
            _ => panic!("cannot parse line:\n{s}"),
        }
    }
}

fn strip_sexp_comments(s: &str) -> String {
    let re = Regex::new(r";[^\n]*\n").unwrap();
    re.replace_all(s, "\n").to_string()
}

/// Parse a ChcSystem from an SMTLIB2 format.
pub fn parse_smtlib2(s: &str) -> ChcSystem {
    let mut chc_sys = ChcSystem {
        signature: Signature {
            sorts: vec![],
            relations: vec![],
        },
        predicates: vec![],
        chcs: vec![],
    };
    let mut global_vars = vec![];

    let s_stripped = strip_sexp_comments(s);
    for line in &smtlib::sexp::parse_many(&s_stripped).unwrap() {
        match SmtlibLine::parse(&chc_sys, &global_vars, line) {
            SmtlibLine::Sort(s) => chc_sys.signature.sorts.push(s),
            SmtlibLine::Predicate(p) => chc_sys.predicates.push(p),
            SmtlibLine::Var(v) => global_vars.push(v),
            SmtlibLine::Chc {
                variables,
                body,
                head,
            } => chc_sys.add_chc(variables, body, head),
            SmtlibLine::Ignore => (),
        }
    }

    chc_sys
}

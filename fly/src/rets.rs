// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Utility to convert all non-boolean-returning relations in a Module to boolean-returning ones.

use crate::syntax::*;
use lazy_static::lazy_static;

use std::sync::Mutex;

lazy_static! {
    static ref ID: Mutex<usize> = Mutex::new(0);
}

fn new_id() -> String {
    let mut id = ID.lock().unwrap();
    *id += 1;
    format!("___{}", id)
}

impl Module {
    /// Converts all non-boolean-returning relations to boolean-returning ones
    /// by adding an extra argument and axioms.
    pub fn convert_non_bool_relations(&mut self) {
        let changed: Vec<_> = self
            .signature
            .relations
            .iter()
            .filter(|r| r.sort != Sort::Bool)
            .cloned()
            .collect();

        let mut axioms = vec![];
        for relation in &mut self.signature.relations {
            if relation.sort != Sort::Bool {
                let binders: Vec<Binder> = relation
                    .args
                    .iter()
                    .chain([&relation.sort, &relation.sort])
                    .enumerate()
                    .map(|(i, sort)| Binder {
                        sort: sort.clone(),
                        name: format!("__{}", i),
                    })
                    .collect();
                let other_args = &binders[0..relation.args.len()];
                let new_arg_twice = &binders[relation.args.len()..];
                let all_args_new: Vec<_> = binders[0..=relation.args.len()]
                    .iter()
                    .map(|b| Term::Id(b.name.clone()))
                    .collect();
                let mut all_args_new_alt = all_args_new.clone();
                *all_args_new_alt.last_mut().unwrap() =
                    Term::Id(binders.last().unwrap().name.clone());

                let at_least_one = Term::exists(
                    [binders[relation.args.len()].clone()],
                    Term::App(relation.name.clone(), 0, all_args_new.clone()),
                );
                let at_most_one = Term::forall(
                    new_arg_twice.iter().cloned(),
                    Term::implies(
                        Term::and([
                            Term::App(relation.name.clone(), 0, all_args_new),
                            Term::App(relation.name.clone(), 0, all_args_new_alt),
                        ]),
                        Term::equals(
                            Term::Id(new_arg_twice[0].name.clone()),
                            Term::Id(new_arg_twice[1].name.clone()),
                        ),
                    ),
                );

                let at_least_one = match relation.args.len() {
                    0 => at_least_one,
                    _ => Term::forall(other_args.iter().cloned(), at_least_one),
                };
                let at_most_one = match relation.args.len() {
                    0 => at_most_one,
                    _ => Term::forall(other_args.iter().cloned(), at_most_one),
                };

                axioms.push(ThmStmt::Assume(Term::UnaryOp(
                    UOp::Always,
                    Box::new(at_least_one),
                )));
                axioms.push(ThmStmt::Assume(Term::UnaryOp(
                    UOp::Always,
                    Box::new(at_most_one),
                )));

                relation.args.push(relation.sort.clone());
                relation.sort = Sort::Bool;
            }
        }

        let mut to_quantify = vec![];
        for statement in &mut self.statements {
            match statement {
                ThmStmt::Assume(term) => fix_term(term, &changed, &mut to_quantify),
                ThmStmt::Assert(Proof { assert, invariants }) => {
                    fix_term(&mut assert.x, &changed, &mut to_quantify);
                    invariants.iter_mut().for_each(|invariant| {
                        fix_term(&mut invariant.x, &changed, &mut to_quantify)
                    });
                }
            }
        }
        assert!(to_quantify.is_empty(), "{:?}", to_quantify);

        self.statements.splice(0..0, axioms);
    }
}

#[derive(Debug)]
struct ToBeQuantified {
    name: String,
    sort: Sort,
    r: String,
    p: usize,
    xs: Vec<Term>,
}

fn fix_term(term: &mut Term, changed: &[RelationDecl], to_quantify: &mut Vec<ToBeQuantified>) {
    let mut go = |term| fix_term(term, changed, to_quantify);
    match term {
        Term::App(r, p, xs) => {
            xs.iter_mut().for_each(go);
            if let Some(c) = changed.iter().find(|c| r == &c.name) {
                let name = new_id();
                to_quantify.push(ToBeQuantified {
                    name: name.clone(),
                    sort: c.sort.clone(),
                    r: r.to_string(),
                    p: *p,
                    xs: xs.to_vec(),
                });
                *term = Term::Id(name);
            }
        }
        Term::UnaryOp(_, term) => go(term),
        Term::BinOp(_, a, b) => {
            go(a);
            go(b);
        }
        Term::NAryOp(_, terms) => terms.iter_mut().for_each(go),
        Term::Ite { cond, then, else_ } => {
            go(cond);
            go(then);
            go(else_);
        }
        Term::Quantified { body, .. } => go(body),
        Term::Literal(_) | Term::Id(_) => {}
    }

    if term_is_bool(term) {
        for ToBeQuantified {
            name,
            sort,
            r,
            p,
            mut xs,
        } in to_quantify.drain(..)
        {
            xs.push(Term::Id(name.clone()));
            *term = Term::exists(
                [Binder { name, sort }],
                Term::and([Term::App(r, p, xs), term.clone()]),
            );
        }
    }
}

fn term_is_bool(term: &Term) -> bool {
    match term {
        Term::Literal(_)
        | Term::BinOp(..)
        | Term::NAryOp(..)
        | Term::Quantified { .. }
        | Term::UnaryOp(
            UOp::Not | UOp::Always | UOp::Eventually | UOp::Next | UOp::Previously,
            _,
        ) => true,
        Term::Id(_) | Term::App(..) | Term::UnaryOp(UOp::Prime, _) | Term::Ite { .. } => false,
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::parse;

    #[test]
    fn non_bool_relations_module_conversion() {
        let source1 = "
sort s
mutable f(sort, bool): sort

assume always forall s:sort. f(s, true) = s
        ";
        let source2 = "
sort s
mutable f(sort, bool, sort): bool

assume always forall __0:sort, __1: bool. exists __2:sort. f(__0, __1, __2)
assume always forall __0:sort, __1: bool. forall __2:sort, __3:sort.
    (f(__0, __1, __2) & f(__0, __1, __3)) -> (__2 = __3)

assume always forall s:sort. exists ___1:sort. f(s, true, ___1) & ___1 = s
        ";

        let mut module1 = parse(source1).unwrap();
        module1.convert_non_bool_relations();

        let module2 = parse(source2).unwrap();

        assert_eq!(module1, module2);
    }
}

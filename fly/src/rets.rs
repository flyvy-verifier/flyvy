// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Utility to convert all non-boolean-returning relations in a Module to boolean-returning ones.

use crate::syntax::*;
use crate::term::prime::Next;

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
        let mut name = 0;
        let mut go = |term: &mut Term| {
            *term = Next::new(&self.signature).normalize(term);
            fix_term(term, &changed, &mut to_quantify, &mut name);
        };
        for statement in &mut self.statements {
            match statement {
                ThmStmt::Assume(term) => go(term),
                ThmStmt::Assert(Proof { assert, invariants }) => {
                    go(&mut assert.x);
                    invariants
                        .iter_mut()
                        .for_each(|invariant| go(&mut invariant.x));
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

fn fix_term(
    term: &mut Term,
    changed: &[RelationDecl],
    to_quantify: &mut Vec<ToBeQuantified>,
    name: &mut usize,
) {
    // wraps term with an exists quantifier
    let quantify = |term: &mut Term, to_quantify: &mut Vec<ToBeQuantified>| {
        if !to_quantify.is_empty() {
            let mut binders = vec![];
            let mut clauses = vec![term.clone()];
            for mut tbq in to_quantify.drain(..) {
                tbq.xs.push(Term::Id(tbq.name.clone()));
                binders.insert(
                    0,
                    Binder {
                        name: tbq.name,
                        sort: tbq.sort,
                    },
                );
                clauses.insert(0, Term::App(tbq.r, tbq.p, tbq.xs));
            }
            *term = Term::exists(binders, Term::and(clauses));
        }
    };

    match term {
        Term::Id(r) => {
            if let Some(c) = changed.iter().find(|c| r == &c.name) {
                *name += 1;
                let name = format!("___{}", *name);
                to_quantify.push(ToBeQuantified {
                    name: name.clone(),
                    sort: c.sort.clone(),
                    r: r.to_string(),
                    p: 0,
                    xs: vec![],
                });
                *term = Term::Id(name);
            }
        }
        Term::App(r, p, xs) => {
            xs.iter_mut()
                .for_each(|x| fix_term(x, changed, to_quantify, name));
            if let Some(c) = changed.iter().find(|c| r == &c.name) {
                *name += 1;
                let name = format!("___{}", *name);
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
        Term::UnaryOp(UOp::Always | UOp::Eventually, a) => {
            fix_term(a, changed, to_quantify, name);
            quantify(a, to_quantify);
        }
        Term::UnaryOp(_, a) => fix_term(a, changed, to_quantify, name),
        Term::BinOp(BinOp::Until | BinOp::Since, a, b) => {
            fix_term(a, changed, to_quantify, name);
            quantify(a, to_quantify);
            fix_term(b, changed, to_quantify, name);
            quantify(b, to_quantify);
        }
        Term::BinOp(_, a, b) => {
            fix_term(a, changed, to_quantify, name);
            fix_term(b, changed, to_quantify, name);
        }
        Term::NAryOp(_, terms) => terms
            .iter_mut()
            .for_each(|term| fix_term(term, changed, to_quantify, name)),
        Term::Ite { cond, then, else_ } => {
            fix_term(cond, changed, to_quantify, name);
            fix_term(then, changed, to_quantify, name);
            fix_term(else_, changed, to_quantify, name);
        }
        Term::Quantified { body, .. } => {
            fix_term(body, changed, to_quantify, name);
            quantify(body, to_quantify);
        }
        Term::Literal(_) => {}
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::parse;

    #[test]
    fn non_bool_relations_module_conversion_basic() {
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

        assert_eq!(module2, module1);
    }

    #[test]
    fn non_bool_relations_module_conversion_primes() {
        let source1 = "
sort s
mutable f: sort

assume always forall s:sort. f' = s
        ";
        let source2 = "
sort s
mutable f(sort): bool

assume always exists __0:sort. f(__0)
assume always forall __0:sort, __1:sort. (f(__0) & f(__1)) -> (__0 = __1)

assume always forall s:sort. exists ___1:sort. f'(___1) & ___1 = s
        ";

        let mut module1 = parse(source1).unwrap();
        module1.convert_non_bool_relations();

        let module2 = parse(source2).unwrap();

        assert_eq!(module2, module1);
    }
}

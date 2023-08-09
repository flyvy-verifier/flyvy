// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Utility to convert all non-boolean-returning relations in a Module to boolean-returning ones.

use crate::{semantics::*, syntax::*};

impl Module {
    /// Converts all non-boolean-returning relations to boolean-returning ones
    /// by adding an extra argument and axioms.
    pub fn convert_non_bool_relations(&mut self) -> Box<dyn Fn(&Model) -> Model> {
        let old_signature = self.signature.clone();
        let changed: Vec<_> = old_signature
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
                        name: format!("__{i}"),
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

        let mut name = 0;
        let mut go = |term: &mut Term| {
            let to_quantify = fix_term(term, &changed, &mut name);
            assert!(to_quantify.is_empty(), "{to_quantify:?}");
        };
        for statement in &mut self.statements {
            match statement {
                ThmStmt::Assume(term) => go(term),
                ThmStmt::Assert(Proof { assert, invariants }) => {
                    go(&mut assert.x);
                    for invariant in invariants {
                        go(&mut invariant.x);
                    }
                }
            }
        }

        self.statements.splice(0..0, axioms);

        Box::new(move |model| {
            Model::new(
                &old_signature,
                &model.universe,
                old_signature
                    .relations
                    .iter()
                    .map(|r| {
                        let interp = &model.interp[old_signature.relation_idx(&r.name)];
                        if r.sort == Sort::Bool {
                            return interp.clone();
                        }

                        let shape = r
                            .args
                            .iter()
                            .map(|s| model.cardinality(s))
                            .chain([model.cardinality(&r.sort)])
                            .collect();
                        let f = |elements: &[Element]| {
                            for i in 0..model.cardinality(&r.sort) {
                                let mut elements = elements.to_vec();
                                elements.push(i);
                                if interp.get(&elements) == 1 {
                                    return i;
                                }
                            }
                            unreachable!()
                        };
                        Interpretation::new(&shape, f)
                    })
                    .collect(),
            )
        })
    }
}

#[derive(Debug)]
struct ToBeQuantified {
    name: String,
    sort: Sort,
    r: String,
    p: usize,
    xs: Vec<Term>,
    primes: usize,
}

fn fix_term(term: &mut Term, changed: &[RelationDecl], name: &mut usize) -> Vec<ToBeQuantified> {
    // wraps term with an exists quantifier
    // is called at the first ast node that returns a boolean
    let quantify = |term: &mut Term, to_quantify: Vec<ToBeQuantified>| {
        if !to_quantify.is_empty() {
            let mut binders = vec![];
            let mut clauses = vec![term.clone()];
            for mut tbq in to_quantify.into_iter().rev() {
                tbq.xs.push(Term::Id(tbq.name.clone()));
                binders.insert(
                    0,
                    Binder {
                        name: tbq.name,
                        sort: tbq.sort,
                    },
                );
                let mut clause = Term::App(tbq.r, tbq.p, tbq.xs);
                for _ in 0..tbq.primes {
                    clause = Term::UnaryOp(UOp::Prime, Box::new(clause));
                }
                clauses.insert(0, clause);
            }
            *term = Term::exists(binders, Term::and(clauses));
        }
    };

    match term {
        Term::Id(r) => {
            let mut out = vec![];
            if let Some(c) = changed.iter().find(|c| r == &c.name) {
                *name += 1;
                let name = format!("___{}", *name);
                out.push(ToBeQuantified {
                    name: name.clone(),
                    sort: c.sort.clone(),
                    r: r.to_string(),
                    p: 0,
                    xs: vec![],
                    primes: 0,
                });
                *term = Term::Id(name);
            }
            out
        }
        Term::App(r, p, xs) => {
            let mut out = vec![];
            for x in &mut *xs {
                out.extend(fix_term(x, changed, name));
            }
            if let Some(c) = changed.iter().find(|c| r == &c.name) {
                *name += 1;
                let name = format!("___{}", *name);
                out.push(ToBeQuantified {
                    name: name.clone(),
                    sort: c.sort.clone(),
                    r: r.to_string(),
                    p: *p,
                    xs: xs.to_vec(),
                    primes: 0,
                });
                *term = Term::Id(name);
            }
            out
        }
        Term::UnaryOp(UOp::Always | UOp::Eventually | UOp::Not, a) => {
            let to_quantify = fix_term(a, changed, name);
            quantify(a, to_quantify);
            vec![]
        }
        Term::UnaryOp(UOp::Prime | UOp::Next, a) => fix_term(a, changed, name)
            .into_iter()
            .map(|tbq| ToBeQuantified {
                primes: tbq.primes + 1,
                ..tbq
            })
            .collect(),
        Term::UnaryOp(UOp::Previous, _) => todo!(),
        Term::BinOp(BinOp::Until | BinOp::Since | BinOp::Implies | BinOp::Iff, a, b) => {
            let to_quantify = fix_term(a, changed, name);
            quantify(a, to_quantify);
            let to_quantify = fix_term(b, changed, name);
            quantify(b, to_quantify);
            vec![]
        }
        Term::BinOp(BinOp::Equals | BinOp::NotEquals, a, b) => {
            let mut out = vec![];
            out.extend(fix_term(a, changed, name));
            out.extend(fix_term(b, changed, name));
            out
        }
        Term::NAryOp(NOp::And | NOp::Or, terms) => {
            for term in terms {
                let to_quantify = fix_term(term, changed, name);
                quantify(term, to_quantify);
            }
            vec![]
        }
        Term::Ite { cond, then, else_ } => {
            let mut out = vec![];
            out.extend(fix_term(cond, changed, name));
            out.extend(fix_term(then, changed, name));
            out.extend(fix_term(else_, changed, name));
            out
        }
        Term::Quantified { body, .. } => {
            let to_quantify = fix_term(body, changed, name);
            quantify(body, to_quantify);
            vec![]
        }
        Term::Literal(_) => vec![],
    }
}

#[cfg(test)]
mod tests {
    use crate::{parser::parse, semantics::*};

    #[test]
    fn non_bool_relations_module_conversion_basic() {
        let source1 = "
sort s
mutable f(s, bool): s

assume always forall s:s. f(s, true) = s
        ";
        let source2 = "
sort s
mutable f(s, bool, s): bool

assume always forall __0:s, __1: bool. exists __2:s. f(__0, __1, __2)
assume always forall __0:s, __1: bool, __2:s, __3:s.
    (f(__0, __1, __2) & f(__0, __1, __3)) -> (__2 = __3)

assume always forall s:s. exists ___1:s. f(s, true, ___1) & ___1 = s
        ";

        let mut module1 = parse(source1).unwrap();
        let _ = module1.convert_non_bool_relations();

        let module2 = parse(source2).unwrap();

        assert_eq!(module2, module1);
    }

    #[test]
    fn non_bool_relations_module_conversion_primes() {
        let source1 = "
sort s
mutable f(s): s

assume always forall s:s. (f(s))' = s
        ";
        let source2 = "
sort s
mutable f(s, s): bool

assume always forall __0:s. exists __1:s. f(__0, __1)
assume always forall __0:s, __1:s, __2:s. (f(__0, __1) & f(__0, __2)) -> (__1 = __2)

assume always forall s:s. exists ___1:s. (f(s, ___1))' & ___1' = s
        ";

        let mut module1 = parse(source1).unwrap();
        let _ = module1.convert_non_bool_relations();

        let module2 = parse(source2).unwrap();

        assert_eq!(module2, module1);
    }

    #[test]
    fn non_bool_relations_module_conversion_nested() {
        let source1 = "
sort s
mutable f: s

assume always forall s:s. f = s & (forall s:s. s=s)
        ";
        let source2 = "
sort s
mutable f(s): bool

assume always exists __0:s. f(__0)
assume always forall __0:s, __1:s. (f(__0) & f(__1)) -> (__0 = __1)

assume always forall s:s. (exists ___1:s. f(___1) & ___1 = s) & (forall s:s. s=s)
        ";

        let mut module1 = parse(source1).unwrap();
        let _ = module1.convert_non_bool_relations();

        let module2 = parse(source2).unwrap();

        assert_eq!(module2, module1);
    }

    #[test]
    fn non_bool_relations_model_back_conversion() {
        let source = "
sort s

mutable f(bool): s
        ";
        let mut module = parse(source).unwrap();

        let model1 = Model::new(
            &module.signature,
            &vec![3],
            vec![Interpretation::new(&vec![2, 3], |xs| {
                if xs[0] == 0 {
                    2
                } else {
                    0
                }
            })],
        );

        let back_convert_model = module.convert_non_bool_relations();
        let model2 = Model::new(
            &module.signature,
            &vec![3],
            vec![Interpretation::new(&vec![2, 3, 2], |xs| match xs {
                [0, 2] | [1, 0] => 1,
                _ => 0,
            })],
        );

        let model3 = back_convert_model(&model2);

        assert_eq!(model1, model3);
    }
}

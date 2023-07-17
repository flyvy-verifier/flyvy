// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Utility to convert all non-boolean-returning relations in a Module to boolean-returning ones.

use crate::syntax::*;

impl Module {
    /// Converts all non-boolean-returning relations to boolean-returning ones
    /// by adding an extra argument and axioms.
    pub fn convert_non_bool_relations(&mut self) {
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

                axioms.push(ThmStmt::Assume(Term::UnaryOp(
                    UOp::Always,
                    Box::new(Term::forall(
                        other_args.iter().cloned(),
                        Term::exists(
                            [binders[relation.args.len()].clone()],
                            Term::App(relation.name.clone(), 0, all_args_new.clone()),
                        ),
                    )),
                )));
                axioms.push(ThmStmt::Assume(Term::UnaryOp(
                    UOp::Always,
                    Box::new(Term::forall(
                        other_args.iter().cloned(),
                        Term::forall(
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
                        ),
                    )),
                )));

                relation.args.push(relation.sort.clone());
                relation.sort = Sort::Bool;
            }
        }
        self.statements.splice(0..0, axioms);
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
        ";
        let source2 = "
sort s
mutable f(sort, bool, sort): bool

assume always forall __0:sort, __1: bool. exists __2:sort. f(__0, __1, __2)
assume always forall __0:sort, __1: bool. forall __2:sort, __3:sort.
    (f(__0, __1, __2) & f(__0, __1, __3)) -> (__2 = __3)
        ";

        let mut module1 = parse(source1).unwrap();
        module1.convert_non_bool_relations();

        let module2 = parse(source2).unwrap();

        assert_eq!(module1, module2);
    }
}

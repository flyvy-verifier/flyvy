// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Utility to convert all non-boolean-returning relations in a Module to boolean-returning ones.

use crate::{semantics::*, syntax::*};
use thiserror::Error;

impl Module {
    /// Converts all non-boolean-returning relations to boolean-returning ones
    /// by adding an extra argument and axioms.
    pub fn convert_non_bool_relations(
        &mut self,
    ) -> Result<Box<dyn Fn(&Model) -> Model>, RetsError> {
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

        for statement in &mut self.statements {
            match statement {
                ThmStmt::Assume(term) => fix_term(term, &changed)?,
                ThmStmt::Assert(Proof { assert, invariants }) => {
                    fix_term(&mut assert.x, &changed)?;
                    for invariant in invariants {
                        fix_term(&mut invariant.x, &changed)?;
                    }
                }
            }
        }

        self.statements.splice(0..0, axioms);

        Ok(Box::new(move |model| {
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
        }))
    }
}

fn contains_changed(term: &Term, changed: &[RelationDecl]) -> bool {
    match term {
        Term::Literal(_) => false,
        Term::Id(id) => changed.iter().any(|c| id == &c.name),
        Term::App(id, ..) if changed.iter().any(|c| id == &c.name) => true,
        Term::App(.., xs) => xs.iter().any(|x| contains_changed(x, changed)),
        Term::NAryOp(_, xs) => xs.iter().any(|x| contains_changed(x, changed)),
        Term::UnaryOp(_, x) => contains_changed(x, changed),
        Term::BinOp(_, x, y) => contains_changed(x, changed) || contains_changed(y, changed),
        Term::Ite { cond, then, else_ } => {
            contains_changed(cond, changed)
                || contains_changed(then, changed)
                || contains_changed(else_, changed)
        }
        Term::Quantified { body, .. } => contains_changed(body, changed),
    }
}

fn strip_primes(term: &Term) -> Option<(Term, usize)> {
    match term {
        Term::Id(_) | Term::App(..) => Some((term.clone(), 0)),
        Term::UnaryOp(UOp::Prime, x) => strip_primes(x).map(|(t, i)| (t, i + 1)),
        Term::Literal(_)
        | Term::UnaryOp(..)
        | Term::BinOp(..)
        | Term::NAryOp(..)
        | Term::Ite { .. }
        | Term::Quantified { .. } => None,
    }
}

/// The result of an unsuccessful attempt to run [`convert_non_bool_relations`].
#[derive(Debug, Error)]
pub enum RetsError {
    /// A function was found that wasn't the direct child of an `Equals`.
    #[error("could not remove non-boolean-returning relations from {0}")]
    FoundOutsideEquals(Term),
}

fn fix_term(term: &mut Term, changed: &[RelationDecl]) -> Result<(), RetsError> {
    match term {
        Term::Literal(_) => Ok(()),
        Term::Id(_) | Term::App(..) => match contains_changed(term, changed) {
            true => Err(RetsError::FoundOutsideEquals(term.clone())),
            false => Ok(()),
        },
        Term::BinOp(BinOp::Equals, x, y) => {
            match strip_primes(x) {
                Some((Term::Id(f), x_primes)) if changed.iter().any(|c| c.name == *f) => {
                    **x = Term::App(f.clone(), x_primes, vec![])
                }
                Some((Term::App(f, p, xs), x_primes)) if changed.iter().any(|c| c.name == *f) => {
                    **x = Term::App(f.clone(), p + x_primes, xs.clone())
                }
                _ => match strip_primes(y) {
                    Some((Term::Id(f), y_primes)) if changed.iter().any(|c| c.name == *f) => {
                        **y = Term::App(f.clone(), y_primes, vec![])
                    }
                    Some((Term::App(f, p, xs), y_primes)) if changed.iter().any(|c| c.name == *f) => {
                        **y = Term::App(f.clone(), p + y_primes, xs.clone())
                    }
                    _ => {
                        fix_term(x, changed)?;
                        fix_term(y, changed)?;
                        return Ok(());
                    }
                }
            }

            if let Term::Id(id) = &**x {
                if changed.iter().any(|c| c.name == *id) {
                    **x = Term::App(id.clone(), 0, vec![]);
                }
            }
            if let Term::Id(id) = &**y {
                if changed.iter().any(|c| c.name == *id) {
                    **y = Term::App(id.clone(), 0, vec![]);
                }
            }

            let name = match &**x {
                Term::App(name, ..) => name,
                _ => match &**y {
                    Term::App(name, ..) => name,
                    _ => unreachable!(),
                },
            };
            let sort = changed
                .iter()
                .find(|c| c.name == *name)
                .unwrap()
                .sort
                .clone();
            let binder = Binder {
                name: "___1".to_string(),
                sort,
            };

            match &mut **x {
                Term::App(.., xs) => xs.push(Term::Id(binder.name.clone())),
                Term::Id(id) => {
                    **x = Term::equals(Term::Id(binder.name.clone()), Term::Id(id.clone()))
                }
                _ => unreachable!(),
            };
            match &mut **y {
                Term::App(.., xs) => xs.push(Term::Id(binder.name.clone())),
                Term::Id(id) => {
                    **y = Term::equals(Term::Id(binder.name.clone()), Term::Id(id.clone()))
                }
                _ => unreachable!(),
            };

            *term = Term::forall([binder], Term::equals((**x).clone(), (**y).clone()));
            Ok(())
        }
        Term::BinOp(BinOp::NotEquals, x, y) => {
            *term = Term::UnaryOp(
                UOp::Not,
                Box::new(Term::equals((**x).clone(), (**y).clone())),
            );
            fix_term(term, changed)
        }
        Term::UnaryOp(_, x) => fix_term(x, changed),
        Term::BinOp(_, x, y) => {
            fix_term(x, changed)?;
            fix_term(y, changed)?;
            Ok(())
        }
        Term::NAryOp(_, xs) => xs.iter_mut().try_for_each(|x| fix_term(x, changed)),
        Term::Ite { cond, then, else_ } => {
            fix_term(cond, changed)?;
            fix_term(then, changed)?;
            fix_term(else_, changed)?;
            Ok(())
        }
        Term::Quantified { body, .. } => fix_term(body, changed),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    #[test]
    fn non_bool_relations_module_conversion_basic() -> Result<(), RetsError> {
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

assume always forall s:s. forall ___1:s. f(s, true, ___1) = (___1 = s)
        ";

        let mut module1 = parse(source1).unwrap();
        let _ = module1.convert_non_bool_relations()?;

        let module2 = parse(source2).unwrap();

        assert_eq!(module2, module1);

        Ok(())
    }

    #[test]
    fn non_bool_relations_module_conversion_primes() -> Result<(), RetsError> {
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

assume always forall s:s. forall ___1:s. f'(s, ___1) = (___1 = s)
        ";

        let mut module1 = parse(source1).unwrap();
        let _ = module1.convert_non_bool_relations()?;

        let module2 = parse(source2).unwrap();

        assert_eq!(module2, module1);

        Ok(())
    }

    #[test]
    fn non_bool_relations_module_conversion_nested() -> Result<(), RetsError> {
        let source1 = "
sort s
mutable f: s

assume always forall s:s. (f = s) & (forall s:s. s=s)
        ";
        let source2 = "
sort s
mutable f(s): bool

assume always exists __0:s. f(__0)
assume always forall __0:s, __1:s. (f(__0) & f(__1)) -> (__0 = __1)

assume always forall s:s. (forall ___1:s. f(___1) = (___1 = s)) & (forall s:s. s=s)
        ";

        let mut module1 = parse(source1).unwrap();
        let _ = module1.convert_non_bool_relations();

        let module2 = parse(source2).unwrap();

        assert_eq!(module2, module1);

        Ok(())
    }

    #[test]
    fn non_bool_relations_model_back_conversion() -> Result<(), RetsError> {
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

        let back_convert_model = module.convert_non_bool_relations()?;
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

        Ok(())
    }
}

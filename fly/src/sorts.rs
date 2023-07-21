// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Infer and check sorts.
//!
//! The main entry point is [sort_check_and_infer].
//!
//! The parser represents missing sort annotations as `Sort::Id("")`. One of the
//! main purposes of sort inference is to replace these placeholders with proper
//! sort annotations. Sort inference is combined with sort checking, so another
//! main purpose of this module is to make sure the given fly program is well
//! sorted.

use crate::syntax::*;
use ena::unify::{InPlace, UnificationTable, UnifyKey, UnifyValue};
use std::collections::HashSet;
use thiserror::Error;

/// An error encountered during sort checking
#[derive(Error, Debug, PartialEq)]
pub enum SortError {
    /// The program referred to an uninterpreted sort that was not declared.
    #[error("sort {0} was not declared")]
    UnknownSort(String),
    /// An uninterpreted sort was declared multiple times.
    #[error("sort {0} was declared multiple times")]
    RedeclaredSort(String),

    /// The program referred to a variable that was not declared.
    #[error("unknown variable/constant {0}")]
    UnknownVariable(String),
    /// The program referred to a function that was not declared.
    #[error("unknown function/definition {0}")]
    UnknownFunction(String),
    /// A name was declared multiple times in a context that did not allow shadowing.
    #[error("{0} was declared multiple times")]
    RedeclaredName(String),

    /// Sort inference detected a conflict between two sorts.
    #[error("could not unify {0} and {1}")]
    UnificationFail(Sort, Sort),
    /// Sort checking detected a mismatch between the expected and actual sorts of a term.
    #[error("expected {expected} but found {found}")]
    ExpectedButFoundSorts {
        /// Expected sort coming from sort annotations
        expected: Sort,
        #[allow(missing_docs)]
        found: Sort,
    },
    /// A function or definition was applied to the wrong number of arguments.
    #[allow(missing_docs)]
    #[error("function {function_name} expected {expected} args but found {found} args")]
    ExpectedButFoundArity {
        function_name: String,
        expected: usize,
        found: usize,
    },

    /// A function/definition was referred to without passing any arguments.
    #[error("{0} is a function/definition that takes arguments, but no arguments were passed")]
    Uncalled(String),
    /// A constant or variable was called like a function.
    #[error("{0} was called but it is not a function/definition")]
    Uncallable(String),

    /// Sort inference finished without gaining enough information to figure out
    /// the sort of the given variable.
    #[error("could not solve for the sort of {0}")]
    UnsolvedSort(String),
}

/// Checks that the given fly module is well sorted, inferring sort annotations
/// on bound variables as needed.
///
/// This is the main entry point to the sort checker/inferencer.
///
/// Note that this is a *mutable* operation on the AST! Sort inference will
/// write its results back into the AST so that future passes can easily find
/// the type of a bound variable.
///
/// Sort inference allows the user to leave off the sort annotation of most
/// quantified variables. Internally, it uses unification to discover the
/// missing sorts. The sorts on arguments to definitions are required to be
/// given explicitly. (This last requirement is enforced by the parser.)
///
/// The parser represents missing sort annotations in the input AST as
/// `Sort::Id("")`. `sort_check_and_infer` guarantees that, after it returns, no
/// sort annotation is `Sort::Id("")` anywhere in the given fly module. In other
/// words, it guarantees that [module_has_all_sort_annotations] returns true.
///
/// If sort checking detects an error (see [SortError]), it will attempt to
/// provide a [Span] to locate this error in the source code. The AST has
/// limited span information, so some errors will be returned without location
/// information (the span will be `None` in that case).
pub fn sort_check_and_infer(module: &mut Module) -> Result<(), (SortError, Option<Span>)> {
    let mut sorts = HashSet::new();
    for sort in &module.signature.sorts {
        if !sorts.insert(sort.clone()) {
            return Err((SortError::RedeclaredSort(sort.clone()), None));
        }
    }

    let mut context = Context {
        sorts: &sorts,
        names: im::HashMap::new(),
        vars: &mut UnificationTable::new(),
    };

    // The sort inference algorithm proceeds in two phases.
    //
    // First, we walk the entire AST and do normal "type checking" checks.
    // During this pass, if we encounter a bound variable without a sort
    // annotation, we allocate a unification variable for it. The unification
    // variable is recorded in the unification table (self.vars) and the bound
    // variable in the AST is labeled with a string that uniquely identifies its
    // corresponding variable. Other checks elsewhere in the AST (possibly above
    // the node!) should resolve the unification variable to a concrete sort.
    // This concrete sort gets stored in the unification table, but the AST
    // still has the unification variable recorded as the sort of the variable.
    //
    // Second, we walk the AST again, looking for bound variables with
    // unification variables. We assert that the variable was successfully
    // resolved to a concrete sort (if not, report an error to the user that a
    // type annotation is required), and then replace the unification variable
    // with the concrete sort.

    // Here begins the first pass.

    // using immediately invoked closure to tag errors with None spans
    (|| {
        for rel in &module.signature.relations {
            for arg in &rel.args {
                context.check_sort_exists(arg)?;
            }
            context.check_sort_exists(&rel.sort)?;
            context.add_name(
                rel.name.clone(),
                NamedSort::Known(rel.args.clone(), rel.sort.clone()),
                ShadowingConstraint::Disallow,
            )?;
        }

        for def in &mut module.defs {
            {
                let mut context = context.new_inner_scope();
                context.add_binders(&mut def.binders)?;
                context.check_sort_exists(&def.ret_sort)?;
                let ret = context.sort_of_term(&mut def.body)?;
                context.unify_var_value(&def.ret_sort, &ret)?;
            }

            let args = def
                .binders
                .iter()
                .map(|binder| binder.sort.clone())
                .collect();

            context.add_name(
                def.name.clone(),
                NamedSort::Known(args, def.ret_sort.clone()),
                ShadowingConstraint::Disallow,
            )?;
        }

        Ok(())
    })()
    .map_err(|e| (e, None))?;

    // helper that wraps any errors
    let term_is_bool = |context: &mut Context, term: &mut Term, span: Option<Span>| {
        context
            .sort_of_term(term)
            .and_then(|sort| context.unify_var_value(&Sort::Bool, &sort))
            .map_err(|e| (e, span))
    };

    for statement in &mut module.statements {
        match statement {
            ThmStmt::Assume(term) => term_is_bool(&mut context, term, None)?,
            ThmStmt::Assert(proof) => {
                for invariant in &mut proof.invariants {
                    term_is_bool(&mut context, &mut invariant.x, Some(invariant.span))?
                }
                term_is_bool(&mut context, &mut proof.assert.x, Some(proof.assert.span))?
            }
        }
    }

    // Done with first pass.

    // At this point, bound variables without sort annotations have "var {id}"
    // as their sort annotation. Second pass fixes this.

    // Here begins the second pass.

    // helper that wraps any errors
    let fix_sorts = |context: &mut Context, term: &mut Term, span: Option<Span>| {
        context.fix_sorts_in_term(term).map_err(|e| (e, span))
    };

    for def in &mut module.defs {
        fix_sorts(&mut context, &mut def.body, None)?
    }

    for statement in &mut module.statements {
        match statement {
            ThmStmt::Assume(term) => fix_sorts(&mut context, term, None)?,
            ThmStmt::Assert(proof) => {
                for invariant in &mut proof.invariants {
                    fix_sorts(&mut context, &mut invariant.x, Some(invariant.span))?
                }
                fix_sorts(&mut context, &mut proof.assert.x, Some(proof.assert.span))?
            }
        }
    }

    // Done with second pass.

    // Double check that we didn't miss any bound variables in the first pass.
    assert!(module_has_all_sort_annotations(module));

    Ok(())
}

/// Return whether every quantified variable in every term in the given fly
/// module has a (non-empty) sort annotation.
pub fn module_has_all_sort_annotations(module: &Module) -> bool {
    // This function should be kept in sync with the parser. Currently the
    // parser only generates Sort::Id("") on quantified variables, so that is
    // the only place we need to check. If future changes to the parser
    // introduce more opportunities for sort inference, then this function
    // should be adjusted as well.

    module
        .defs
        .iter()
        .all(|def| term_has_all_sort_annotations(&def.body))
        && module.statements.iter().all(|statement| match statement {
            ThmStmt::Assume(term) => term_has_all_sort_annotations(term),
            ThmStmt::Assert(proof) => {
                proof
                    .invariants
                    .iter()
                    .all(|inv| term_has_all_sort_annotations(&inv.x))
                    && term_has_all_sort_annotations(&proof.assert.x)
            }
        })
}

/// Return whether every quantified variable in this term has a (non-empty) sort
/// annotation.
pub fn term_has_all_sort_annotations(term: &Term) -> bool {
    match term {
        Term::Literal(_) | Term::Id(_) => true,
        Term::App(_f, _p, xs) => xs.iter().all(term_has_all_sort_annotations),
        Term::UnaryOp(
            UOp::Not | UOp::Always | UOp::Eventually | UOp::Prime | UOp::Next | UOp::Previously,
            x,
        ) => term_has_all_sort_annotations(x),
        Term::BinOp(
            BinOp::Equals
            | BinOp::NotEquals
            | BinOp::Implies
            | BinOp::Iff
            | BinOp::Until
            | BinOp::Since,
            x,
            y,
        ) => term_has_all_sort_annotations(x) && term_has_all_sort_annotations(y),
        Term::NAryOp(NOp::And | NOp::Or, xs) => xs.iter().all(term_has_all_sort_annotations),
        Term::Ite { cond, then, else_ } => {
            term_has_all_sort_annotations(cond)
                && term_has_all_sort_annotations(then)
                && term_has_all_sort_annotations(else_)
        }
        Term::Quantified {
            quantifier: Quantifier::Forall | Quantifier::Exists,
            binders,
            body,
        } => {
            binders
                .iter()
                .all(|binder| binder.sort != Sort::Uninterpreted("".to_owned()))
                && term_has_all_sort_annotations(body)
        }
    }
}

// can either hold a function sort or the index of a sort variable
// all sorts must be known by the time `check` returns
#[derive(Clone, Debug)]
enum NamedSort {
    Known(Vec<Sort>, Sort),
    Unknown(SortVar),
}

#[derive(Clone, Debug)]
enum AbstractSort {
    Known(Sort),
    Unknown(SortVar),
}

// wrappers to implement ena::unify traits on
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
struct SortVar(u32);
#[derive(Clone, Debug, PartialEq)]
struct OptionSort(Option<Sort>);

impl UnifyKey for SortVar {
    type Value = OptionSort;
    fn index(&self) -> u32 {
        self.0
    }
    fn from_index(u: u32) -> SortVar {
        SortVar(u)
    }
    fn tag() -> &'static str {
        "SortVar"
    }
}

impl UnifyValue for OptionSort {
    type Error = SortError;
    fn unify_values(a: &OptionSort, b: &OptionSort) -> Result<OptionSort, SortError> {
        match (&a.0, &b.0) {
            (None, None) => Ok(OptionSort(None)),
            (None, a @ Some(_)) | (a @ Some(_), None) => Ok(OptionSort(a.clone())),
            (Some(x), Some(y)) if x == y => Ok(OptionSort(Some(x.clone()))),
            (Some(x), Some(y)) => Err(SortError::UnificationFail(x.clone(), y.clone())),
        }
    }
}

#[derive(PartialEq, Eq)]
enum ShadowingConstraint {
    Allow,
    Disallow,
}

#[derive(Debug)]
struct Context<'a> {
    sorts: &'a HashSet<String>,
    names: im::HashMap<String, NamedSort>,
    vars: &'a mut UnificationTable<InPlace<SortVar>>,
}

impl Context<'_> {
    // we don't want to clone the references, just the name map
    fn new_inner_scope(&mut self) -> Context {
        Context {
            sorts: self.sorts,
            names: self.names.clone(),
            vars: self.vars,
        }
    }

    // if the given sort is uninterpreted, check that it is declared in the module and report an error if not.
    // if empty_allowed is true, then Sort("") does not cause an error.
    // callers should not call this function directly, but rather [check_sort_exists] or [check_sort_exists_or_empty]
    fn check_sort_exists_internal(
        &self,
        sort: &Sort,
        empty_allowed: bool,
    ) -> Result<(), SortError> {
        match sort {
            Sort::Bool => Ok(()),
            Sort::Uninterpreted(a) if a.is_empty() && empty_allowed => Ok(()),
            Sort::Uninterpreted(a) => {
                if !self.sorts.contains(a) {
                    Err(SortError::UnknownSort(a.clone()))
                } else {
                    Ok(())
                }
            }
        }
    }

    // if the given sort is uninterpreted, check that it is declared in the module and report an error if not.
    fn check_sort_exists(&self, sort: &Sort) -> Result<(), SortError> {
        self.check_sort_exists_internal(sort, false)
    }

    // if the given sort is uninterpreted, check that it is declared in the module and report an error if not.
    // Sort("") does not cause an error.
    fn check_sort_exists_or_empty(&self, sort: &Sort) -> Result<(), SortError> {
        self.check_sort_exists_internal(sort, true)
    }

    // adds `(name, sort)` to `context`, potentially giving an error if name already exists
    fn add_name(
        &mut self,
        name: String,
        sort: NamedSort,
        shadowing_constraint: ShadowingConstraint,
    ) -> Result<(), SortError> {
        match self.names.insert(name.clone(), sort) {
            Some(_) if shadowing_constraint == ShadowingConstraint::Disallow => {
                Err(SortError::RedeclaredName(name))
            }
            _ => Ok(()),
        }
    }

    // doesn't allow `binders` to shadow each other, but does allow them to
    // shadow names already in `context`
    //
    // for any variables that do not have a sort annotation, this function allocates
    // a fresh unification variable to represent its sort, and annotates the AST with
    // a string that uniquely identifies the unification variable. unification variables
    // are represented by integers, and the string "var 55" is used to represent, eg, the
    // unification variable numbered 55. since this string has a space in it, it is impossible
    // for it to be confused with a user sort annotation.
    fn add_binders(&mut self, binders: &mut [Binder]) -> Result<(), SortError> {
        let mut names = HashSet::new();
        for binder in binders {
            // First check that the name is not repeated *within* this slice.
            if !names.insert(binder.name.clone()) {
                return Err(SortError::RedeclaredName(binder.name.clone()));
            }
            self.check_sort_exists_or_empty(&binder.sort)?;
            let sort = if binder.sort == Sort::Uninterpreted("".to_owned()) {
                let var = self.vars.new_key(OptionSort(None));
                binder.sort = Sort::Uninterpreted(format!("var {}", var.0));
                NamedSort::Unknown(var)
            } else {
                NamedSort::Known(vec![], binder.sort.clone())
            };
            // Now add it to the context, allowing it to shadow bindings from
            // any outer scopes.
            self.add_name(binder.name.clone(), sort, ShadowingConstraint::Allow)?;
        }
        Ok(())
    }

    // unify a sort and a sort variable, or return an error
    fn unify_var_value(&mut self, value: &Sort, var: &AbstractSort) -> Result<(), SortError> {
        match var {
            AbstractSort::Known(v) if value == v => Ok(()),
            AbstractSort::Known(v) => Err(SortError::ExpectedButFoundSorts {
                expected: value.clone(),
                found: v.clone(),
            }),
            AbstractSort::Unknown(v) => self
                .vars
                .unify_var_value(*v, OptionSort(Some(value.clone()))),
        }
    }

    // unify two sort variables, or return an error
    fn unify_var_var(&mut self, a: &AbstractSort, b: &AbstractSort) -> Result<(), SortError> {
        match (a, b) {
            (AbstractSort::Known(a), AbstractSort::Known(b)) if a == b => Ok(()),
            (AbstractSort::Known(a), AbstractSort::Known(b)) => {
                Err(SortError::UnificationFail(a.clone(), b.clone()))
            }
            (AbstractSort::Unknown(i), AbstractSort::Unknown(j)) => self.vars.unify_var_var(*i, *j),
            (AbstractSort::Known(a), AbstractSort::Unknown(i))
            | (AbstractSort::Unknown(i), AbstractSort::Known(a)) => {
                self.vars.unify_var_value(*i, OptionSort(Some(a.clone())))
            }
        }
    }

    // walk the term AST, fixing any binders that still have "var {id}" sorts
    fn fix_sorts_in_term(&mut self, term: &mut Term) -> Result<(), SortError> {
        match term {
            Term::Literal(_) | Term::Id(_) => Ok(()),
            Term::App(_f, _p, xs) => {
                for x in xs {
                    self.fix_sorts_in_term(x)?;
                }
                Ok(())
            }
            Term::UnaryOp(
                UOp::Not | UOp::Always | UOp::Eventually | UOp::Prime | UOp::Next | UOp::Previously,
                x,
            ) => self.fix_sorts_in_term(x),
            Term::BinOp(
                BinOp::Equals
                | BinOp::NotEquals
                | BinOp::Implies
                | BinOp::Iff
                | BinOp::Until
                | BinOp::Since,
                x,
                y,
            ) => {
                self.fix_sorts_in_term(x)?;
                self.fix_sorts_in_term(y)?;
                Ok(())
            }
            Term::NAryOp(NOp::And | NOp::Or, xs) => {
                for x in xs {
                    self.fix_sorts_in_term(x)?;
                }
                Ok(())
            }
            Term::Ite { cond, then, else_ } => {
                self.fix_sorts_in_term(cond)?;
                self.fix_sorts_in_term(then)?;
                self.fix_sorts_in_term(else_)?;
                Ok(())
            }
            Term::Quantified {
                quantifier: Quantifier::Forall | Quantifier::Exists,
                binders,
                body,
            } => {
                for binder in binders {
                    if let Sort::Uninterpreted(s) = binder.sort.clone() {
                        let s: Vec<&str> = s.split_whitespace().collect();
                        match s[..] {
                            [_] => {} // user sort annotation
                            ["var", id] => {
                                // encodes a sort unification variable
                                let id = id.parse::<u32>().expect(
                                    "unexpected non-integer in a sort unification variable id",
                                );
                                let sort = self.vars.probe_value(SortVar(id));
                                match sort.0 {
                                    None => {
                                        return Err(SortError::UnsolvedSort(binder.name.clone()))
                                    }
                                    Some(v) => binder.sort = v,
                                }
                            }
                            _ => unreachable!("empty string, or contains spaces without var"),
                        }
                    }
                }
                self.fix_sorts_in_term(body)
            }
        }
    }

    // recursively finds the sort of a term
    fn sort_of_term(&mut self, term: &mut Term) -> Result<AbstractSort, SortError> {
        match term {
            Term::Literal(_) => Ok(AbstractSort::Known(Sort::Bool)),
            Term::Id(name) => match self.names.get(name) {
                Some(NamedSort::Known(args, _)) if !args.is_empty() => {
                    Err(SortError::Uncalled(name.clone()))
                }
                Some(NamedSort::Known(_, ret)) => Ok(AbstractSort::Known(ret.clone())),
                Some(NamedSort::Unknown(var)) => Ok(AbstractSort::Unknown(*var)),
                None => Err(SortError::UnknownVariable(name.clone())),
            },
            Term::App(f, _p, xs) => match self.names.get(f).cloned() {
                Some(NamedSort::Known(args, _)) if args.is_empty() => {
                    Err(SortError::Uncallable(f.clone()))
                }
                Some(NamedSort::Known(args, ret)) => {
                    if args.len() != xs.len() {
                        return Err(SortError::ExpectedButFoundArity {
                            function_name: f.clone(),
                            expected: args.len(),
                            found: xs.len(),
                        });
                    }
                    for (arg, x) in args.into_iter().zip(xs) {
                        let x = self.sort_of_term(x)?;
                        self.unify_var_value(&arg, &x)?;
                    }
                    Ok(AbstractSort::Known(ret))
                }
                Some(NamedSort::Unknown(_)) => unreachable!("function sorts are always known"),
                None => Err(SortError::UnknownFunction(f.clone())),
            },
            Term::UnaryOp(
                UOp::Not | UOp::Always | UOp::Eventually | UOp::Next | UOp::Previously,
                x,
            ) => {
                let x = self.sort_of_term(x)?;
                self.unify_var_value(&Sort::Bool, &x)?;
                Ok(AbstractSort::Known(Sort::Bool))
            }
            Term::UnaryOp(UOp::Prime, x) => self.sort_of_term(x),
            Term::BinOp(BinOp::Equals | BinOp::NotEquals, x, y) => {
                let a = self.sort_of_term(x)?;
                let b = self.sort_of_term(y)?;
                self.unify_var_var(&a, &b)?;
                Ok(AbstractSort::Known(Sort::Bool))
            }
            Term::BinOp(BinOp::Implies | BinOp::Iff | BinOp::Until | BinOp::Since, x, y) => {
                let x = self.sort_of_term(x)?;
                self.unify_var_value(&Sort::Bool, &x)?;
                let y = self.sort_of_term(y)?;
                self.unify_var_value(&Sort::Bool, &y)?;
                Ok(AbstractSort::Known(Sort::Bool))
            }
            Term::NAryOp(NOp::And | NOp::Or, xs) => {
                for x in xs {
                    let sort = self.sort_of_term(x)?;
                    self.unify_var_value(&Sort::Bool, &sort)?;
                }
                Ok(AbstractSort::Known(Sort::Bool))
            }
            Term::Ite { cond, then, else_ } => {
                let cond = self.sort_of_term(cond)?;
                self.unify_var_value(&Sort::Bool, &cond)?;
                let a = self.sort_of_term(then)?;
                let b = self.sort_of_term(else_)?;
                self.unify_var_var(&a, &b)?;
                Ok(a)
            }
            Term::Quantified {
                quantifier: Quantifier::Forall | Quantifier::Exists,
                binders,
                body,
            } => {
                let mut context = self.new_inner_scope();
                context.add_binders(binders)?;
                let body = context.sort_of_term(body)?;
                context.unify_var_value(&Sort::Bool, &body)?;
                Ok(AbstractSort::Known(Sort::Bool))
            }
        }
    }
}

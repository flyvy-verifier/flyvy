// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A bounded model checker for flyvy programs using the [CaDiCaL][cadical] SAT solver.
//!
//! [cadical]: https://fmv.jku.at/cadical/

use cadical::Solver;
use fly::{ouritertools::OurItertools, semantics::*, sorts::*, syntax::*, transitions::*};
use itertools::Itertools;
use std::collections::HashMap;
use thiserror::Error;

/// Holds an ordering of all variables, as well as other context
struct Context<'a> {
    signature: &'a Signature,
    universe: &'a Universe,
    indices: HashMap<&'a str, HashMap<Vec<usize>, (usize, bool)>>,
    mutables: usize,
    vars: usize,
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Variable(usize);

impl Context<'_> {
    fn new<'a>(signature: &'a Signature, universe: &'a Universe, depth: usize) -> Context<'a> {
        let (mutable, immutable): (Vec<_>, Vec<_>) = signature
            .relations
            .iter()
            .partition(|relation| relation.mutable);
        let elements = |relation: &&'a RelationDecl| {
            relation
                .args
                .iter()
                .map(|sort| cardinality(universe, sort))
                .map(|card| (0..card).collect::<Vec<usize>>())
                .multi_cartesian_product_fixed()
                .map(|element| (relation.name.as_str(), element))
                .collect::<Vec<_>>()
        };

        let mut indices: HashMap<_, HashMap<_, _>> = HashMap::new();

        let mut mutables = 0;
        for (i, (r, e)) in mutable.iter().flat_map(elements).enumerate() {
            mutables += 1;
            indices.entry(r).or_default().insert(e, (i, true));
        }
        let mut immutables = 0;
        for (i, (r, e)) in immutable.iter().flat_map(elements).enumerate() {
            immutables += 1;
            indices
                .entry(r)
                .or_default()
                .insert(e, (mutables * (depth + 1) + i, false));
        }

        Context {
            signature,
            universe,
            indices,
            mutables,
            vars: mutables * (depth + 1) + immutables,
        }
    }

    fn get_var(&self, relation: &str, elements: &[usize], primes: usize) -> Variable {
        let (mut i, mutable) = self.indices[relation][elements];
        if mutable {
            i += primes * self.mutables;
        }
        Variable(i)
    }

    fn new_var(&mut self) -> Variable {
        self.vars += 1;
        Variable(self.vars - 1)
    }

    fn convert_counterexample(&self, solver: Solver, depth: usize) -> Vec<Model> {
        let universe = self
            .signature
            .sorts
            .iter()
            .map(|s| self.universe[s])
            .collect();
        (0..=depth)
            .map(|primes| {
                Model::new(
                    self.signature,
                    &universe,
                    self.signature
                        .relations
                        .iter()
                        .map(|r| {
                            let shape = r
                                .args
                                .iter()
                                .map(|s| cardinality(self.universe, s))
                                .chain([2])
                                .collect();
                            Interpretation::new(&shape, |elements| {
                                solver
                                    .value(self.get_var(&r.name, elements, primes).0 as i32 + 1)
                                    .unwrap_or(false) as usize
                            })
                        })
                        .collect(),
                )
            })
            .collect()
    }
}

#[allow(missing_docs)]
#[derive(Error, Debug)]
pub enum CheckerError {
    #[error("sort checking error: {0}")]
    SortError(SortError),
    #[error("sort {0} not found in universe {1:#?}")]
    UnknownSort(String, Universe),
    #[error("{0}")]
    ExtractionError(ExtractionError),

    #[error("could not translate to propositional logic {0}")]
    CouldNotTranslateToAst(Term),
    #[error("could not translate to element {0}")]
    CouldNotTranslateToElement(Term),

    #[error("solver failed, likely a timeout")]
    SolverFailed,
}

/// Map from uninterpreted sort names to sizes
type Universe = HashMap<String, usize>;

fn cardinality(universe: &Universe, sort: &Sort) -> usize {
    match sort {
        Sort::Bool => 2,
        Sort::Uninterpreted(id) => universe[id],
    }
}

/// The result of a successful run of the bounded model checker
#[derive(Debug, PartialEq)]
pub enum CheckerAnswer {
    /// The checker found a counterexample
    Counterexample(Vec<Model>),
    /// The checker did not find a counterexample
    Unknown,
}

/// Check a given Module out to some depth.
/// This function assumes that the module has been typechecked.
/// The checker ignores proof blocks.
pub fn check(
    module: &Module,
    universe: &Universe,
    depth: usize,
    print_timing: bool,
) -> Result<CheckerAnswer, CheckerError> {
    for sort in &module.signature.sorts {
        if !universe.contains_key(sort) {
            return Err(CheckerError::UnknownSort(sort.clone(), universe.clone()));
        }
    }

    for relation in &module.signature.relations {
        if relation.sort != Sort::Bool {
            panic!("non-bool relations in checker (use Module::convert_non_bool_relations)")
        }
    }

    if !module.defs.is_empty() {
        panic!("definitions in checker (use Module::inline_defs)")
    }

    let d = extract(module).map_err(CheckerError::ExtractionError)?;
    let inits = d.inits.iter().chain(&d.axioms).cloned();
    let transitions = d
        .transitions
        .iter()
        .chain(d.mutable_axioms(&module.signature.relations))
        .cloned();
    let safeties = d.proofs.iter().map(|proof| proof.safety.x.clone());

    let mut context = Context::new(&module.signature, universe, depth);

    let translate = |term| {
        let term = nullary_id_to_app(term, &module.signature.relations);
        let term = fly::term::prime::Next::new(&module.signature).normalize(&term);
        term_to_ast(&term, &context, &HashMap::new())
    };

    println!("starting translation...");
    let translation = std::time::Instant::now();

    let init = translate(Term::and(inits))?;
    let tr = translate(Term::and(transitions))?;
    let not_safe = Ast::Not(Box::new(translate(Term::and(safeties))?));

    let mut program = vec![init];
    for i in 0..depth {
        program.push(tr.clone().prime(i));
    }
    program.push(not_safe.prime(depth));

    let cnf = tseytin(&Ast::And(program), &mut context);

    if print_timing {
        println!(
            "translation finished in {:0.1}s",
            translation.elapsed().as_secs_f64()
        );
    }

    println!("starting search...");
    let search = std::time::Instant::now();

    let mut solver: Solver = Default::default();
    for clause in &cnf {
        let cadical_clause = clause
            .iter()
            .map(|l| (l.var as i32 + 1) * if l.pos { 1 } else { -1 });
        solver.add_clause(cadical_clause);
    }
    assert_eq!(solver.max_variable(), context.vars as i32);

    let answer = match solver.solve() {
        None => Err(CheckerError::SolverFailed),
        Some(false) => Ok(CheckerAnswer::Unknown),
        Some(true) => Ok(CheckerAnswer::Counterexample(
            context.convert_counterexample(solver, depth),
        )),
    };

    if print_timing {
        println!("search finished in {:0.1}s", search.elapsed().as_secs_f64());
    }

    answer
}

fn nullary_id_to_app(term: Term, relations: &[RelationDecl]) -> Term {
    match term {
        Term::Literal(b) => Term::Literal(b),
        Term::Id(id) if relations.iter().any(|r| r.name == id) => Term::App(id, 0, vec![]),
        Term::Id(id) => Term::Id(id),
        Term::App(name, primes, args) => Term::App(
            name,
            primes,
            args.into_iter()
                .map(|arg| nullary_id_to_app(arg, relations))
                .collect(),
        ),
        Term::UnaryOp(op, term) => Term::UnaryOp(op, Box::new(nullary_id_to_app(*term, relations))),
        Term::BinOp(op, a, b) => Term::BinOp(
            op,
            Box::new(nullary_id_to_app(*a, relations)),
            Box::new(nullary_id_to_app(*b, relations)),
        ),
        Term::NAryOp(op, args) => Term::NAryOp(
            op,
            args.into_iter()
                .map(|arg| nullary_id_to_app(arg, relations))
                .collect(),
        ),
        Term::Ite { cond, then, else_ } => Term::Ite {
            cond: Box::new(nullary_id_to_app(*cond, relations)),
            then: Box::new(nullary_id_to_app(*then, relations)),
            else_: Box::new(nullary_id_to_app(*else_, relations)),
        },
        Term::Quantified {
            quantifier,
            binders,
            body,
        } => Term::Quantified {
            quantifier,
            binders,
            body: Box::new(nullary_id_to_app(*body, relations)),
        },
    }
}

// true is empty And; false is empty Or
#[derive(Clone, Debug, PartialEq)]
enum Ast {
    Var(String, Vec<usize>, usize),
    And(Vec<Ast>),
    Or(Vec<Ast>),
    Not(Box<Ast>),
}

impl Ast {
    fn iff(x: Ast, y: Ast) -> Ast {
        Ast::Or(vec![
            Ast::And(vec![x.clone(), y.clone()]),
            Ast::And(vec![Ast::Not(Box::new(x)), Ast::Not(Box::new(y))]),
        ])
    }

    fn truth(&self) -> Option<bool> {
        match self {
            Ast::Var { .. } => None,
            Ast::And(vec) => vec
                .iter()
                .try_fold(true, |acc, ast| match (acc, ast.truth()) {
                    (false, _) | (_, Some(false)) => Some(false),
                    (true, x) => x,
                }),
            Ast::Or(vec) => vec
                .iter()
                .try_fold(false, |acc, ast| match (acc, ast.truth()) {
                    (true, _) | (_, Some(true)) => Some(true),
                    (false, x) => x,
                }),
            Ast::Not(ast) => ast.truth().map(|b| !b),
        }
    }

    fn prime(self, depth: usize) -> Ast {
        match self {
            Ast::Var(relation, elements, primes) => Ast::Var(relation, elements, primes + depth),
            Ast::And(vec) => Ast::And(vec.into_iter().map(|ast| ast.prime(depth)).collect()),
            Ast::Or(vec) => Ast::Or(vec.into_iter().map(|ast| ast.prime(depth)).collect()),
            Ast::Not(ast) => Ast::Not(Box::new(ast.prime(depth))),
        }
    }
}

fn term_to_ast(
    term: &Term,
    context: &Context,
    assignments: &HashMap<String, usize>,
) -> Result<Ast, CheckerError> {
    let ast = |term| term_to_ast(term, context, assignments);
    let element = |term| term_to_element(term, context, assignments);

    let ast: Ast = match term {
        Term::Literal(true) => Ast::And(vec![]),
        Term::Literal(false) => Ast::Or(vec![]),
        Term::Id(id) => match assignments.get(id) {
            Some(0) => Ast::Or(vec![]),
            Some(1) => Ast::And(vec![]),
            _ => return Err(CheckerError::CouldNotTranslateToAst(term.clone())),
        },
        Term::App(relation, primes, args) => Ast::Var(
            relation.to_string(),
            args.iter().map(element).collect::<Result<Vec<_>, _>>()?,
            *primes,
        ),
        Term::UnaryOp(UOp::Not, term) => Ast::Not(Box::new(ast(term)?)),
        Term::BinOp(BinOp::Iff, a, b) => Ast::iff(ast(a)?, ast(b)?),
        Term::BinOp(BinOp::Equals, a, b) => match (element(a), element(b)) {
            (Ok(a), Ok(b)) if a == b => Ast::And(vec![]),
            (Ok(a), Ok(b)) if a != b => Ast::Or(vec![]),
            _ => Ast::iff(ast(a)?, ast(b)?),
        },
        Term::BinOp(BinOp::NotEquals, a, b) => Ast::Not(Box::new(ast(&Term::BinOp(
            BinOp::Equals,
            a.clone(),
            b.clone(),
        ))?)),
        Term::BinOp(BinOp::Implies, a, b) => Ast::Or(vec![Ast::Not(Box::new(ast(a)?)), ast(b)?]),
        Term::NAryOp(NOp::And, terms) => {
            Ast::And(terms.iter().map(ast).collect::<Result<Vec<_>, _>>()?)
        }
        Term::NAryOp(NOp::Or, terms) => {
            Ast::Or(terms.iter().map(ast).collect::<Result<Vec<_>, _>>()?)
        }
        Term::Ite { cond, then, else_ } => Ast::Or(vec![
            Ast::And(vec![ast(cond)?, ast(then)?]),
            Ast::And(vec![Ast::Not(Box::new(ast(cond)?)), ast(else_)?]),
        ]),
        Term::Quantified {
            quantifier,
            binders,
            body,
        } => {
            assert!(!binders.is_empty());
            let shape: Vec<usize> = binders
                .iter()
                .map(|b| cardinality(context.universe, &b.sort))
                .collect();
            let names: Vec<&String> = binders.iter().map(|b| &b.name).collect();
            let bodies = shape
                .iter()
                .map(|&card| (0..card).collect::<Vec<usize>>())
                .multi_cartesian_product_fixed()
                .map(|elements| {
                    let mut new_assignments = assignments.clone();
                    for (name, element) in names.iter().zip(elements) {
                        new_assignments.insert(name.to_string(), element);
                    }
                    term_to_ast(body, context, &new_assignments)
                })
                .collect::<Result<Vec<_>, _>>()?;
            match quantifier {
                Quantifier::Forall => Ast::And(bodies),
                Quantifier::Exists => Ast::Or(bodies),
            }
        }
        Term::UnaryOp(UOp::Prime | UOp::Always | UOp::Eventually, _)
        | Term::UnaryOp(UOp::Next | UOp::Previous, _)
        | Term::BinOp(BinOp::Until | BinOp::Since, ..) => {
            return Err(CheckerError::CouldNotTranslateToAst(term.clone()))
        }
    };
    Ok(ast)
}

fn term_to_element(
    term: &Term,
    context: &Context,
    assignments: &HashMap<String, usize>,
) -> Result<usize, CheckerError> {
    let ast = |term| term_to_ast(term, context, assignments);
    let element = |term| term_to_element(term, context, assignments);

    let element: usize = match term {
        Term::Literal(_)
        | Term::UnaryOp(UOp::Not, ..)
        | Term::BinOp(BinOp::Iff | BinOp::Equals | BinOp::NotEquals | BinOp::Implies, ..)
        | Term::NAryOp(NOp::And | NOp::Or, ..)
        | Term::Quantified { .. } => match ast(term)?.truth() {
            Some(true) => 1,
            Some(false) => 0,
            None => return Err(CheckerError::CouldNotTranslateToElement(term.clone())),
        },
        Term::Id(id) => assignments[id],
        Term::Ite { cond, then, else_ } => match element(cond)? {
            1 => element(then)?,
            0 => element(else_)?,
            _ => unreachable!(),
        },
        Term::UnaryOp(UOp::Prime | UOp::Always | UOp::Eventually, _)
        | Term::UnaryOp(UOp::Next | UOp::Previous, _)
        | Term::BinOp(BinOp::Until | BinOp::Since, ..)
        | Term::App(..) => return Err(CheckerError::CouldNotTranslateToElement(term.clone())),
    };
    Ok(element)
}

#[derive(Clone, Debug, PartialEq)]
struct Literal {
    var: usize,
    pos: bool,
}
type Clause = Vec<Literal>;
type Cnf = Vec<Clause>;

impl Literal {
    fn t(Variable(var): Variable) -> Literal {
        Literal { var, pos: true }
    }
    fn f(Variable(var): Variable) -> Literal {
        Literal { var, pos: false }
    }
}

fn tseytin(ast: &Ast, context: &mut Context) -> Cnf {
    fn inner(ast: &Ast, context: &mut Context, out: &mut Cnf) -> Variable {
        let mut go = |ast| inner(ast, context, out);
        match ast {
            Ast::Var(relation, elements, primes) => context.get_var(relation, elements, *primes),
            Ast::And(vec) => {
                let olds: Vec<_> = vec.iter().map(go).collect();
                let new = context.new_var();
                for old in &olds {
                    out.push(vec![Literal::t(*old), Literal::f(new)]);
                }
                let mut clause: Vec<_> = olds.into_iter().map(Literal::f).collect();
                clause.push(Literal::t(new));
                out.push(clause);
                new
            }
            Ast::Or(vec) => {
                let olds: Vec<_> = vec.iter().map(go).collect();
                let new = context.new_var();
                for old in &olds {
                    out.push(vec![Literal::f(*old), Literal::t(new)]);
                }
                let mut clause: Vec<_> = olds.into_iter().map(Literal::t).collect();
                clause.push(Literal::f(new));
                out.push(clause);
                new
            }
            Ast::Not(ast) => {
                let old = go(ast);
                let new = context.new_var();
                out.push(vec![Literal::t(old), Literal::t(new)]);
                out.push(vec![Literal::f(old), Literal::f(new)]);
                new
            }
        }
    }

    let mut out = vec![];
    let var = inner(ast, context, &mut out);
    out.push(vec![Literal::t(var)]);
    out
}

#[allow(dead_code)]
fn dimacs(cnf: &Cnf, context: &Context) -> String {
    let mut out = format!("p cnf {} {}\n", context.vars, cnf.len());
    out.push_str(
        &cnf.iter()
            .map(|clause| {
                clause
                    .iter()
                    .map(|literal| match literal {
                        Literal { var, pos: true } => format!("{}", var + 1),
                        Literal { var, pos: false } => format!("-{}", var + 1),
                    })
                    .join(" ")
            })
            .join("\n"),
    );
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use fly::sorts::sort_check_module;

    #[test]
    fn checker_sat_basic() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/tests/examples/basic2.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = HashMap::from([]);

        assert_eq!(CheckerAnswer::Unknown, check(&module, &universe, 0, false)?);
        assert!(matches!(
            check(&module, &universe, 1, false)?,
            CheckerAnswer::Counterexample(..),
        ));

        Ok(())
    }

    #[test]
    fn checker_sat_lockserver() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/examples/lockserver.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = HashMap::from([("node".to_string(), 2)]);

        assert_eq!(
            CheckerAnswer::Unknown,
            check(&module, &universe, 10, false)?
        );

        Ok(())
    }

    #[test]
    fn checker_sat_lockserver_buggy() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/tests/examples/lockserver_buggy.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = HashMap::from([("node".to_string(), 2)]);

        let bug = check(&module, &universe, 12, false)?;
        assert!(matches!(bug, CheckerAnswer::Counterexample(..)));

        let too_short = check(&module, &universe, 11, false)?;
        assert_eq!(CheckerAnswer::Unknown, too_short);

        Ok(())
    }

    #[test]
    fn checker_sat_consensus() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/examples/consensus.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = std::collections::HashMap::from([
            ("node".to_string(), 2),
            ("quorum".to_string(), 2),
            ("value".to_string(), 2),
        ]);

        assert_eq!(
            CheckerAnswer::Unknown,
            check(&module, &universe, 10, false)?
        );

        Ok(())
    }

    #[test]
    fn checker_sat_immutability() -> Result<(), CheckerError> {
        let source =
            include_str!("../../temporal-verifier/tests/examples/success/immutability.fly");
        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = std::collections::HashMap::new();
        assert_eq!(
            CheckerAnswer::Unknown,
            check(&module, &universe, 10, false)?
        );
        Ok(())
    }
}

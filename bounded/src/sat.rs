// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A bounded model checker for flyvy programs using the [CaDiCaL][cadical] SAT solver.
//!
//! [cadical]: https://fmv.jku.at/cadical/

use crate::quantenum::*;
use cadical::Solver;
use fly::{ouritertools::OurItertools, semantics::*, syntax::*, transitions::*};
use itertools::Itertools;
use std::collections::HashMap;
use thiserror::Error;

/// Holds an ordering of all variables, as well as other context
struct Context<'a> {
    signature: &'a Signature,
    universe: &'a UniverseBounds,
    indices: HashMap<&'a str, HashMap<Vec<usize>, (usize, bool)>>,
    mutables: usize,
    vars: usize,
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Variable(usize);

impl Context<'_> {
    fn new<'a>(
        signature: &'a Signature,
        universe: &'a UniverseBounds,
        depth: usize,
    ) -> Context<'a> {
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

/// The result of an unsuccessful attempt to run the SAT checker.
#[derive(Error, Debug)]
pub enum CheckerError {
    /// A sort existed in a term but not in the universe
    #[error("sort {0} not found in universe {1:#?}")]
    UnknownSort(String, UniverseBounds),
    /// See [`ExtractionError`]
    #[error("{0}")]
    ExtractionError(ExtractionError),
    /// See [`EnumerationError`]
    #[error("{0}")]
    EnumerationError(EnumerationError),
    /// The SAT solver failed
    #[error("solver failed, likely a timeout")]
    SolverFailed,
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
    universe: &UniverseBounds,
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
        fn enumerated_to_ast(term: Enumerated) -> Ast {
            match term {
                Enumerated::And(xs) => Ast::And(xs.into_iter().map(enumerated_to_ast).collect()),
                Enumerated::Or(xs) => Ast::Or(xs.into_iter().map(enumerated_to_ast).collect()),
                Enumerated::Not(x) => Ast::Not(Box::new(enumerated_to_ast(*x))),
                Enumerated::Eq(x, y) => Ast::iff(enumerated_to_ast(*x), enumerated_to_ast(*y)),
                Enumerated::App(name, primes, args) => Ast::Var(name, args, primes),
            }
        }

        let term = enumerate_quantifiers(&term, &module.signature, universe, depth.max(1))
            .map_err(CheckerError::EnumerationError)?;
        Ok(enumerated_to_ast(term))
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

    fn prime(self, depth: usize) -> Ast {
        match self {
            Ast::Var(relation, elements, primes) => Ast::Var(relation, elements, primes + depth),
            Ast::And(vec) => Ast::And(vec.into_iter().map(|ast| ast.prime(depth)).collect()),
            Ast::Or(vec) => Ast::Or(vec.into_iter().map(|ast| ast.prime(depth)).collect()),
            Ast::Not(ast) => Ast::Not(Box::new(ast.prime(depth))),
        }
    }
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

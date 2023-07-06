// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A bounded model checker for flyvy programs using a SAT solver.

use crate::fly::{sorts::*, syntax::*};
use crate::term::FirstOrder;
use itertools::Itertools;
use std::collections::HashMap;
use thiserror::Error;

/// Holds an ordering of all variables, as well as other context
struct Context<'a> {
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
            if relation.args.is_empty() {
                vec![(relation.name.as_str(), (vec![]))]
            } else {
                relation
                    .args
                    .iter()
                    .map(|sort| cardinality(universe, sort))
                    .map(|card| (0..card).collect::<Vec<usize>>())
                    .multi_cartesian_product()
                    .map(|element| (relation.name.as_str(), element))
                    .collect()
            }
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

    fn print_counterexample(&self, solver: cadical::Solver, depth: usize) {
        println!("found counterexample!");
        for state in 0..=depth {
            println!("state {}:", state);
            for (relation, map) in &self.indices {
                print!("{}: {{", relation);
                for (elements, (i, mutable)) in map {
                    let mut var = *i;
                    if *mutable {
                        var += state * self.mutables;
                    }
                    if solver.value(var as i32 + 1) == Some(true) {
                        print!("{:?}, ", elements);
                    }
                }
                println!("}}");
            }
            println!();
        }
    }
}

#[allow(missing_docs)]
#[derive(Error, Debug)]
pub enum CheckerError {
    #[error("sort checking error: {0}")]
    SortError(SortError),
    #[error("sort {0} not found in universe {1:#?}")]
    UnknownSort(String, Universe),

    #[error("all assumes should precede all asserts, but found {0:?}")]
    OutOfOrderStatement(ThmStmt),
    #[error("expected no primes in {0}")]
    AnyFuture(Term),
    #[error("expected no primes or only one prime in {0}")]
    TooFuture(Term),
    #[error("expected all asserts be safety properties but found {0}")]
    AssertWithoutAlways(Term),

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
        Sort::Id(id) => universe[id],
    }
}

/// The result of a successful run of the bounded model checker
#[derive(Debug, PartialEq)]
pub enum CheckerAnswer {
    /// The checker found a counterexample
    Counterexample,
    /// The checker did not find a counterexample
    Unknown,
}

/// Check a given Module out to some depth.
/// This function assumes that the module has been typechecked.
pub fn check(
    module: &Module,
    universe: &Universe,
    depth: usize,
) -> Result<CheckerAnswer, CheckerError> {
    for sort in &module.signature.sorts {
        if !universe.contains_key(sort) {
            return Err(CheckerError::UnknownSort(sort.clone(), universe.clone()));
        }
    }

    for relation in &module.signature.relations {
        if relation.sort != Sort::Bool {
            todo!("non-bool relations")
        }
    }

    if !module.defs.is_empty() {
        todo!("definitions are not supported yet");
    }

    let mut assumes = Vec::new();
    let mut asserts = Vec::new();
    for statement in &module.statements {
        match statement {
            ThmStmt::Assert(Proof { assert, invariants }) => {
                asserts.push(assert.x.clone());
                if !invariants.is_empty() {
                    eprintln!("note: invariants are not yet supported, and do nothing")
                }
            }
            ThmStmt::Assume(term) if asserts.is_empty() => assumes.push(term.clone()),
            _ => return Err(CheckerError::OutOfOrderStatement(statement.clone())),
        }
    }

    let mut inits = Vec::new();
    let mut trs = Vec::new();
    for assume in assumes {
        match assume {
            Term::UnaryOp(UOp::Always, axiom) if FirstOrder::unrolling(&axiom) == Some(0) => {
                inits.push(*axiom.clone());
                trs.push(*axiom);
            }
            Term::UnaryOp(UOp::Always, tr) if FirstOrder::unrolling(&tr) == Some(1) => {
                trs.push(*tr)
            }
            Term::UnaryOp(UOp::Always, term) => return Err(CheckerError::TooFuture(*term)),
            init if FirstOrder::unrolling(&init) == Some(0) => inits.push(init),
            init => return Err(CheckerError::AnyFuture(init)),
        }
    }

    let mut safes = Vec::new();
    for assert in asserts {
        match assert {
            Term::UnaryOp(UOp::Always, safe) if FirstOrder::unrolling(&safe) == Some(0) => {
                safes.push(*safe)
            }
            Term::UnaryOp(UOp::Always, safe) => return Err(CheckerError::AnyFuture(*safe)),
            assert => return Err(CheckerError::AssertWithoutAlways(assert)),
        }
    }

    let mut context = Context::new(&module.signature, universe, depth);

    let translate = |terms| {
        let term = Term::NAryOp(NOp::And, terms);
        let term = nullary_id_to_app(term, &module.signature.relations);
        let term = crate::term::Next::new(&module.signature).normalize(&term);
        term_to_ast(&term, &context, &HashMap::new())
    };

    println!("starting translation...");
    let translation = std::time::Instant::now();

    let init = translate(inits)?;
    let tr = translate(trs)?;
    let not_safe = Ast::Not(Box::new(translate(safes)?));

    let mut program = vec![init];
    for i in 0..depth {
        program.push(tr.clone().prime(i));
    }
    program.push(not_safe.prime(depth));

    let cnf = tseytin(&Ast::And(program), &mut context);

    println!(
        "translation finished in {:0.1}s",
        translation.elapsed().as_secs_f64()
    );

    println!("starting cadical search...");
    let cadical_search = std::time::Instant::now();

    let mut solver: cadical::Solver = Default::default();
    for clause in &cnf {
        let cadical_clause = clause
            .iter()
            .map(|l| (l.var as i32 + 1) * if l.pos { 1 } else { -1 });
        solver.add_clause(cadical_clause);
    }
    assert_eq!(solver.max_variable(), context.vars as i32);

    let cadical_answer = match solver.solve() {
        None => return Err(CheckerError::SolverFailed),
        Some(false) => CheckerAnswer::Unknown,
        Some(true) => {
            context.print_counterexample(solver, depth);
            CheckerAnswer::Counterexample
        }
    };

    println!(
        "cadical search finished in {:0.1}s",
        cadical_search.elapsed().as_secs_f64()
    );

    println!("starting kissat search...");
    let kissat_search = std::time::Instant::now();

    let mut solver: kissat::Solver = Default::default();
    let vars: Vec<kissat::Var> = (0..context.vars).map(|_| solver.var()).collect();
    for clause in &cnf {
        let kissat_clause = clause
            .iter()
            .map(|l| if l.pos { vars[l.var] } else { !vars[l.var] })
            .collect::<Vec<_>>();
        solver.add(&kissat_clause);
    }

    let kissat_answer = match solver.sat() {
        Some(_) => CheckerAnswer::Counterexample,
        None => CheckerAnswer::Unknown,
    };

    println!(
        "kissat search finished in {:0.1}s",
        kissat_search.elapsed().as_secs_f64()
    );

    if kissat_answer != cadical_answer {
        panic!("solvers disagreed!")
    }

    Ok(cadical_answer)
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
                .fold(Some(true), |acc, ast| match (acc, ast.truth()) {
                    (Some(false), _) | (_, Some(false)) => Some(false),
                    (Some(true), x) => x,
                    (None, _) => None,
                }),
            Ast::Or(vec) => vec
                .iter()
                .fold(Some(false), |acc, ast| match (acc, ast.truth()) {
                    (Some(true), _) | (_, Some(true)) => Some(true),
                    (Some(false), x) => x,
                    (None, _) => None,
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
                .multi_cartesian_product()
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
        | Term::UnaryOp(UOp::Next | UOp::Previously, _)
        | Term::BinOp(BinOp::Until | BinOp::Since, ..)
        | Term::Id(_) => return Err(CheckerError::CouldNotTranslateToAst(term.clone())),
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
        | Term::UnaryOp(UOp::Next | UOp::Previously, _)
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
    use crate::fly::sorts::sort_check_and_infer;

    #[test]
    fn checker_basic() -> Result<(), CheckerError> {
        let source = "
mutable x: bool

assume x

assume always (x -> !x')

assert always x
        ";

        let mut module = crate::fly::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();
        let universe = HashMap::from([]);

        assert_eq!(CheckerAnswer::Unknown, check(&module, &universe, 0)?);
        assert_eq!(CheckerAnswer::Counterexample, check(&module, &universe, 1)?);

        Ok(())
    }

    #[test]
    fn checker_lockserver() -> Result<(), CheckerError> {
        let source = "
sort node

mutable lock_msg(node): bool
mutable grant_msg(node): bool
mutable unlock_msg(node): bool
mutable holds_lock(node): bool
mutable server_holds_lock: bool

# inits:
assume (forall N:node. !lock_msg(N)) & (forall N:node. !grant_msg(N)) & (forall N:node.
    !unlock_msg(N)) & (forall N:node. !holds_lock(N)) & (server_holds_lock)

# transitions:
assume always
    (exists n:node. 
        (forall N:node. ((lock_msg(N))') <-> lock_msg(N) | N = n) & 
        (forall x0:node. ((grant_msg(x0))') = grant_msg(x0)) & 
        (forall x0:node. ((unlock_msg(x0))') = unlock_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0)) & 
        ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. server_holds_lock & lock_msg(n) & 
            !((server_holds_lock)') & 
            (((lock_msg(N))') <-> lock_msg(N) & N != n) & 
            (((grant_msg(N))') <-> grant_msg(N) | N = n)) & 
        (forall x0:node. ((unlock_msg(x0))') = unlock_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0))) | 
    (exists n:node. 
        (forall N:node. grant_msg(n) & 
            (((grant_msg(N))') <-> grant_msg(N) & N != n) & 
            (((holds_lock(N))') <-> holds_lock(N) | N = n)) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) & 
        (forall x0:node. 
            ((unlock_msg(x0))') = unlock_msg(x0)) & 
            ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. holds_lock(n) & 
            (((holds_lock(N))') <-> holds_lock(N) & N != n) & 
            (((unlock_msg(N))') <-> unlock_msg(N) | N = n)) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) &
        (forall x0:node. 
            ((grant_msg(x0))') = grant_msg(x0)) & 
            ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. unlock_msg(n) & 
            (((unlock_msg(N))') <-> unlock_msg(N) & N != n) & 
            ((server_holds_lock)')) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) & 
        (forall x0:node. ((grant_msg(x0))') = grant_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0)))

# safety:
assert always (forall N1:node, N2:node. holds_lock(N1) & holds_lock(N2) -> N1 = N2)
        ";

        let mut module = crate::fly::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();
        let universe = HashMap::from([("node".to_string(), 2)]);

        assert_eq!(CheckerAnswer::Unknown, check(&module, &universe, 10)?);

        Ok(())
    }

    #[test]
    fn checker_lockserver_buggy() -> Result<(), CheckerError> {
        let source = "
sort node

mutable lock_msg(node): bool
mutable grant_msg(node): bool
mutable unlock_msg(node): bool
mutable holds_lock(node): bool
mutable server_holds_lock: bool

# inits:
assume (forall N:node. !lock_msg(N)) & (forall N:node. !grant_msg(N)) & (forall N:node.
    !unlock_msg(N)) & (forall N:node. !holds_lock(N)) & (server_holds_lock)

# transitions:
assume always
    (exists n:node. 
        (forall N:node. ((lock_msg(N))') <-> lock_msg(N) | N = n) & 
        (forall x0:node. ((grant_msg(x0))') = grant_msg(x0)) & 
        (forall x0:node. ((unlock_msg(x0))') = unlock_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0)) & 
        ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. server_holds_lock & lock_msg(n) & 
            !((server_holds_lock)') & 
            (((lock_msg(N))') <-> lock_msg(N) & N != n) & 
            (((grant_msg(N))') <-> grant_msg(N) | N = n)) & 
        (forall x0:node. ((unlock_msg(x0))') = unlock_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0))) | 
    (exists n:node. 
        (forall N:node. grant_msg(n) & 
            (((grant_msg(N))') <-> grant_msg(N) & N != n) & 
            (((holds_lock(N))') <-> holds_lock(N) | N = n)) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) & 
        (forall x0:node. 
            ((unlock_msg(x0))') = unlock_msg(x0)) & 
            ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. holds_lock(n) & 
            (((holds_lock(N))') <-> holds_lock(N) & N != n) & 
            (((unlock_msg(N))') <-> unlock_msg(N) | N = n)) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) &
        (forall x0:node. 
            ((grant_msg(x0))') = grant_msg(x0)) & 
            ((server_holds_lock)') = server_holds_lock) | 
    (exists n:node. 
        (forall N:node. unlock_msg(n) & 
            (((unlock_msg(N))') <-> unlock_msg(N)) & 
            ((server_holds_lock)')) & 
        (forall x0:node. ((lock_msg(x0))') = lock_msg(x0)) & 
        (forall x0:node. ((grant_msg(x0))') = grant_msg(x0)) & 
        (forall x0:node. ((holds_lock(x0))') = holds_lock(x0)))

# safety:
assert always (forall N1:node, N2:node. holds_lock(N1) & holds_lock(N2) -> N1 = N2)
        ";

        let mut module = crate::fly::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();
        let universe = HashMap::from([("node".to_string(), 2)]);

        let bug = check(&module, &universe, 12)?;
        assert_eq!(CheckerAnswer::Counterexample, bug);

        let too_short = check(&module, &universe, 11)?;
        assert_eq!(CheckerAnswer::Unknown, too_short);

        Ok(())
    }

    #[test]
    fn checker_consensus() -> Result<(), CheckerError> {
        let source = "
sort node
sort quorum
sort value

# relations:
immutable member(node, quorum): bool
mutable vote_request_msg(node, node): bool
mutable voted(node): bool
mutable vote_msg(node, node): bool
mutable votes(node, node): bool
mutable leader(node): bool
mutable decided(node, value): bool

# init:
assume (forall N1:node, N2:node. !vote_request_msg(N1, N2)) & (forall N:node. !voted(N)) &
    (forall N1:node, N2:node. !vote_msg(N1, N2)) & (forall N1:node, N2:node. !votes(N1, N2)) &
    (forall N1:node. !leader(N1)) & (forall N:node, V:value. !decided(N, V))

# transitions:
assume always (exists src:node, dst:node. (forall N1:node, N2:node. (vote_request_msg(N1, N2))' <->
    vote_request_msg(N1, N2) | N1 = src & N2 = dst) & (forall x0:node. (voted(x0))' = voted(x0)) &
    (forall x0:node, x1:node. (vote_msg(x0, x1))' = vote_msg(x0, x1)) & (forall x0:node, x1:node.
    (votes(x0, x1))' = votes(x0, x1)) & (forall x0:node. (leader(x0))' = leader(x0)) &
    (forall x0:node, x1:value. (decided(x0, x1))' = decided(x0, x1))) | (exists src:node, dst:node.
    (forall N1:node, N2:node, N:node. !voted(src) & vote_request_msg(dst, src) & ((vote_msg(N1, N2))' <->
    vote_msg(N1, N2) | N1 = src & N2 = dst) & ((voted(N))' <-> voted(N) | N = src) & (!(N1 = dst &
    N2 = src) -> ((vote_request_msg(N1, N2))' <-> vote_request_msg(N1, N2)))) & (forall x0:node, x1:node.
    (votes(x0, x1))' = votes(x0, x1)) & (forall x0:node. (leader(x0))' = leader(x0)) & (forall x0:node,
    x1:value. (decided(x0, x1))' = decided(x0, x1))) | (exists n:node, sender:node. (forall N1:node, N2:node.
    vote_msg(sender, n) & ((votes(N1, N2))' <-> votes(N1, N2) | N1 = n & N2 = sender)) & (forall x0:node,
    x1:node. (vote_request_msg(x0, x1))' = vote_request_msg(x0, x1)) & (forall x0:node. (voted(x0))' = voted(x0))
    & (forall x0:node, x1:node. (vote_msg(x0, x1))' = vote_msg(x0, x1)) & (forall x0:node. (leader(x0))' =
    leader(x0)) & (forall x0:node, x1:value. (decided(x0, x1))' = decided(x0, x1))) | (exists n:node, q:quorum.
    (forall N:node. (member(N, q) -> votes(n, N)) & ((leader(N))' <-> leader(N) | N = n)) & (forall x0:node,
    x1:node. (vote_request_msg(x0, x1))' = vote_request_msg(x0, x1)) & (forall x0:node. (voted(x0))' = voted(x0))
    & (forall x0:node, x1:node. (vote_msg(x0, x1))' = vote_msg(x0, x1)) & (forall x0:node, x1:node.
    (votes(x0, x1))' = votes(x0, x1)) & (forall x0:node, x1:value. (decided(x0, x1))' = decided(x0, x1))) |
    (exists n:node, v:value. (forall V:value, N:node. leader(n) & !decided(n, V) & ((decided(N, V))' <->
    decided(N, V) | N = n & V = v)) & (forall x0:node, x1:node. (vote_request_msg(x0, x1))' =
    vote_request_msg(x0, x1)) & (forall x0:node. (voted(x0))' = voted(x0)) & (forall x0:node, x1:node.
    (vote_msg(x0, x1))' = vote_msg(x0, x1)) & (forall x0:node, x1:node. (votes(x0, x1))' = votes(x0, x1)) &
    (forall x0:node. (leader(x0))' = leader(x0)))

# added by hand
# axiom
assume always (forall Q1:quorum, Q2:quorum. exists N:node. member(N, Q1) & member(N, Q2))

# safety:
assert always (forall N1:node, V1:value, N2:node, V2:value. decided(N1, V1) & decided(N2, V2) -> V1 = V2)
        ";

        let mut module = crate::fly::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();
        let universe = std::collections::HashMap::from([
            ("node".to_string(), 2),
            ("quorum".to_string(), 2),
            ("value".to_string(), 2),
        ]);

        assert_eq!(CheckerAnswer::Unknown, check(&module, &universe, 10)?);

        Ok(())
    }

    #[test]
    fn checker_immutability() -> Result<(), CheckerError> {
        let source = "
immutable r: bool
assume r
assert always r
        ";
        let mut module = crate::fly::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();
        let universe = std::collections::HashMap::new();
        assert_eq!(CheckerAnswer::Unknown, check(&module, &universe, 10)?);
        Ok(())
    }
}

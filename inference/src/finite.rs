// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Infer an inductive invariant from the set of reachable states
//! with small sort bounds.

use biodivine_lib_bdd::boolean_expression::BooleanExpression;
use bounded::bdd::*;
use fly::syntax::*;
use std::collections::HashMap;
use verify::verify_module;

pub fn invariant(
    module: &Module,
    universe: HashMap<String, usize>,
) -> Result<Option<Term>, CheckerError> {
    let (bdd, context) = match check(module, &universe, None, false) {
        Ok(CheckerAnswer::Convergence(bdd, context)) => (bdd, context),
        Ok(CheckerAnswer::Counterexample(_)) => return Ok(None),
        Ok(CheckerAnswer::Unknown) => unreachable!(),
        Err(e) => return Err(e),
    };

    // Build a map from sort elements to Term variable names
    let mut next_binding = 0;
    let mut bindings: HashMap<(&str, usize), String> = HashMap::new();
    for (sort, bound) in &universe {
        for i in 0..*bound {
            bindings.insert((sort, i), format!("${}", next_binding));
            next_binding += 1;
        }
    }

    // Build a map from BDD variable names to Terms
    let mut vars_to_terms: HashMap<String, Term> = HashMap::new();
    for (relation, map) in context.indices {
        for (elements, (i, _mutable)) in map {
            let name = context.bdds.name_of(context.vars[i]);
            let args = module
                .signature
                .relations
                .iter()
                .find(|r| r.name == relation)
                .unwrap()
                .args
                .iter()
                .zip(elements)
                .map(|(sort, element)| match sort {
                    Sort::Id(sort) => Term::Id(bindings[&(sort.as_str(), element)].clone()),
                    Sort::Bool => match element {
                        0 => Term::Literal(false),
                        1 => Term::Literal(true),
                        _ => unreachable!(),
                    },
                });
            let term = Term::App(relation.to_string(), 0, args.collect());
            vars_to_terms.insert(name, term);
        }
    }

    // Convert the BDD to a Term
    let ast = bdd.to_boolean_expression(&context.bdds);
    let ast = to_term(ast, &vars_to_terms);

    // Add not-equal clauses between same-sort elements
    let mut not_equals = vec![];
    for ((sort_1, element_1), name_1) in &bindings {
        for ((sort_2, element_2), name_2) in &bindings {
            if element_1 < element_2 && sort_1 == sort_2 {
                not_equals.push(Term::BinOp(
                    BinOp::NotEquals,
                    Box::new(Term::Id(name_1.to_string())),
                    Box::new(Term::Id(name_2.to_string())),
                ));
            }
        }
    }

    // Wrap the Term in foralls
    let binders = bindings
        .into_iter()
        .map(|((sort, _), name)| Binder {
            name,
            sort: Sort::Id(sort.to_string()),
        })
        .collect();
    let ast = Term::Quantified {
        quantifier: Quantifier::Forall,
        body: Box::new(Term::BinOp(
            BinOp::Implies,
            Box::new(Term::NAryOp(NOp::And, not_equals)),
            Box::new(ast),
        )),
        binders,
    };

    println!("{}", ast);
    todo!()
}

fn to_term(term: BooleanExpression, vars_to_terms: &HashMap<String, Term>) -> Term {
    let go = |term| to_term(term, vars_to_terms);
    use BooleanExpression::*;
    match term {
        Const(b) => Term::Literal(b),
        Variable(name) => vars_to_terms.get(&name).unwrap().clone(),
        Not(term) => Term::UnaryOp(UOp::Not, Box::new(go(*term))),
        And(a, b) => Term::NAryOp(NOp::And, vec![go(*a), go(*b)]),
        Or(a, b) => Term::NAryOp(NOp::Or, vec![go(*a), go(*b)]),
        // Bdd::to_boolean_expression never produces Xor, Imp, or Iff
        Xor(..) | Imp(..) | Iff(..) => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fly::sorts::sort_check_and_infer;

    #[test]
    fn finite_lockserver() -> Result<(), CheckerError> {
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

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_and_infer(&mut module).unwrap();

        let universe = HashMap::from([("node".to_string(), 2)]);

        println!("{:?}", invariant(&module, universe)?);

        Ok(())
    }
}

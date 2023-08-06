// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A bounded model checker for flyvy programs using symbolic evaluation.

use crate::{checker::*, indices::*, quantenum::*};
use biodivine_lib_bdd::*;
use boolean_expression::BooleanExpression;
use fly::{semantics::*, syntax::*, transitions::*};
use itertools::Itertools;
use std::collections::HashMap;

/// Check a given Module out to some depth.
/// This assumes that the module has been typechecked.
/// Passing `None` for depth means to run until a counterexample is found.
/// The checker ignores proof blocks.
pub fn check<'a>(
    module: &'a Module,
    universe: &'a UniverseBounds,
    depth: Option<usize>,
    print_timing: bool,
) -> Result<CheckerAnswer<(Bdd, BddIndices<'a>)>, CheckerError> {
    check_internal(module, universe, depth, print_timing, false)
}

/// The same as `check`, but instead of starting at `init` and going until it gets to `not_safe`,
/// it starts at `not_safe` and goes backwards until it gets to `init`.
/// It also returns a negated Bdd if it returns Convergence.
pub fn check_reversed<'a>(
    module: &'a Module,
    universe: &'a UniverseBounds,
    depth: Option<usize>,
    print_timing: bool,
) -> Result<CheckerAnswer<(Bdd, BddIndices<'a>)>, CheckerError> {
    check_internal(module, universe, depth, print_timing, true)
}

fn check_internal<'a>(
    module: &'a Module,
    universe: &'a UniverseBounds,
    depth: Option<usize>,
    print_timing: bool,
    reversed: bool,
) -> Result<CheckerAnswer<(Bdd, BddIndices<'a>)>, CheckerError> {
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

    let indices = BddIndices::new(&module.signature, universe);

    let translate = |term| {
        fn enumerated_to_bdd(term: Enumerated, indices: &BddIndices) -> Bdd {
            let go = |term| enumerated_to_bdd(term, indices);
            match term {
                Enumerated::And(xs) => indices.mk_and(xs.into_iter().map(go)),
                Enumerated::Or(xs) => indices.mk_or(xs.into_iter().map(go)),
                Enumerated::Not(x) => go(*x).not(),
                Enumerated::Eq(x, y) => go(*x).iff(&go(*y)),
                Enumerated::App(name, primes, args) => indices.get(&name, primes as usize, &args),
            }
        }

        let term = enumerate_quantifiers(&term, &module.signature, universe)
            .map_err(CheckerError::EnumerationError)?;
        Ok(enumerated_to_bdd(term, &indices))
    };

    println!("starting translation...");
    let time = std::time::Instant::now();

    let init = translate(Term::and(inits))?;
    let tr = translate(Term::and(transitions))?;
    let not_safe = translate(Term::and(safeties))?.not();

    if print_timing {
        println!(
            "translation finished in {:0.1}s",
            time.elapsed().as_secs_f64()
        );
    }
    println!("starting search...");
    let time = std::time::Instant::now();

    // Choose which way to search
    let (mut trace, mut current, mut reachable, not_safe, update): (
        Vec<Bdd>,
        Bdd,
        Bdd,
        Bdd,
        Box<dyn Fn(&mut Bdd, &BddIndices)>,
    ) = match reversed {
        false => (
            vec![init.clone()],
            init.clone(),
            init,
            not_safe,
            Box::new(|current: &mut Bdd, indices: &BddIndices| {
                let unprimed = 0..indices.indices.num_mutables;
                *current = Bdd::binary_op_with_exists(
                    current,
                    &tr,
                    op_function::and,
                    &indices.vars[unprimed.clone()],
                );
                for i in unprimed {
                    unsafe {
                        current.rename_variable(
                            indices.vars[i + indices.indices.num_mutables],
                            indices.vars[i],
                        );
                    }
                }
            }),
        ),
        true => (
            vec![not_safe.clone()],
            not_safe.clone(),
            not_safe,
            init,
            Box::new(|current: &mut Bdd, indices: &BddIndices| {
                let primed = indices.indices.num_mutables..indices.indices.num_mutables * 2;
                for i in primed.clone().rev() {
                    unsafe {
                        current.rename_variable(
                            indices.vars[i - indices.indices.num_mutables],
                            indices.vars[i],
                        );
                    }
                }
                *current = Bdd::binary_op_with_exists(
                    current,
                    &tr,
                    op_function::and,
                    &indices.vars[primed],
                );
            }),
        ),
    };

    // Do the search
    if let Some(valuation) = current.and(&not_safe).sat_witness() {
        let models = indices.trace_to_models(&valuation, &trace, &tr, reversed);
        return Ok(CheckerAnswer::Counterexample(models));
    }
    let mut i = 0;
    while depth.map(|d| i < d).unwrap_or(true) {
        update(&mut current, &indices);
        let new_reachable = reachable.or(&current);

        if print_timing {
            println!("depth {} in {:0.1}s", i + 1, time.elapsed().as_secs_f64());
        }

        if reachable == new_reachable {
            return Ok(CheckerAnswer::Convergence((reachable, indices)));
        } else {
            reachable = new_reachable;
        }

        trace.push(current.clone());
        if let Some(valuation) = current.and(&not_safe).sat_witness() {
            let models = indices.trace_to_models(&valuation, &trace, &tr, reversed);
            return Ok(CheckerAnswer::Counterexample(models));
        }

        i += 1;
    }

    Ok(CheckerAnswer::Unknown)
}

/// A wrapper around an `Indices` object that also holds objects used to create BDDs.
pub struct BddIndices<'a> {
    /// The wrapped `Indices` object
    indices: Indices<'a>,
    /// Data used by the BDD library to build new BDDs
    bdds: BddVariableSet,
    /// Map from indices to BddVariable objects
    vars: Vec<BddVariable>,
}

impl BddIndices<'_> {
    fn new<'a>(signature: &'a Signature, universe: &'a UniverseBounds) -> BddIndices<'a> {
        let indices = Indices::new(signature, universe, 2);
        let bdds = BddVariableSet::new_anonymous(indices.num_vars.try_into().unwrap());
        let vars = bdds.variables();
        BddIndices {
            indices,
            bdds,
            vars,
        }
    }

    fn get(&self, relation: &str, primes: usize, elements: &[usize]) -> Bdd {
        self.bdds
            .mk_var(self.vars[self.indices.get(relation, primes, elements)])
    }

    fn trace_to_models(
        &self,
        valuation: &BddValuation,
        trace: &[Bdd],
        tr: &Bdd,
        reversed: bool,
    ) -> Vec<Model> {
        let mutables = self.indices.num_mutables;
        let mut valuations: Vec<Option<BddValuation>> = Vec::with_capacity(trace.len());
        valuations.resize(trace.len(), None);

        // Choose which way to search
        let (start, stop, incr, next): (
            usize,
            usize,
            Box<dyn Fn(usize) -> usize>,
            Box<dyn Fn(usize, &mut Vec<Option<BddValuation>>) -> Bdd>,
        ) = match reversed {
            false => (
                trace.len() - 1,
                0,
                Box::new(|i| i - 1),
                Box::new(|i, valuations| {
                    let unprimed = trace[i - 1].clone();

                    let primed = self.mk_and(self.indices.iter().flat_map(|(relation, map)| {
                        map.iter().map(|(elements, (v, _))| {
                            let var = self.get(relation, 1, elements);
                            if valuations[i].as_ref().unwrap().value(self.vars[*v]) {
                                var
                            } else {
                                var.not()
                            }
                        })
                    }));

                    self.mk_and([unprimed, tr.clone(), primed])
                        .exists(&self.vars[mutables..mutables * 2])
                }),
            ),
            true => (
                0,
                trace.len() - 1,
                Box::new(|i| i + 1),
                Box::new(|i, valuations| {
                    let unprimed = self.mk_and(self.indices.iter().flat_map(|(relation, map)| {
                        map.iter().map(|(elements, (v, _))| {
                            let var = self.get(relation, 0, elements);
                            if valuations[i].as_ref().unwrap().value(self.vars[*v]) {
                                var
                            } else {
                                var.not()
                            }
                        })
                    }));

                    // traces is backwards relative to valuations
                    let mut primed = trace[trace.len() - 1 - (i + 1)].clone();
                    for j in (0..mutables).rev() {
                        unsafe {
                            primed.rename_variable(self.vars[j], self.vars[j + mutables]);
                        }
                    }

                    let mut out = self
                        .mk_and([unprimed, tr.clone(), primed])
                        .exists(&self.vars[0..mutables]);
                    // but valuations expects the primed variables in the unprimed slots
                    for j in 0..mutables {
                        unsafe {
                            out.rename_variable(self.vars[j + mutables], self.vars[j]);
                        }
                    }
                    out
                }),
            ),
        };

        // Do the search
        valuations[start] = Some(valuation.clone());
        let mut i = start;
        while i != stop {
            let bdd = next(i, &mut valuations);
            i = incr(i);
            valuations[i] = Some(bdd.sat_witness().unwrap());
        }

        // Convert valuations to models
        valuations
            .into_iter()
            .map(|valuation| self.valuation_to_model(valuation.unwrap()))
            .collect()
    }

    fn valuation_to_model(&self, valuation: BddValuation) -> Model {
        let universe = self
            .indices
            .signature
            .sorts
            .iter()
            .map(|s| self.indices.universe[s])
            .collect();
        Model::new(
            self.indices.signature,
            &universe,
            self.indices
                .signature
                .relations
                .iter()
                .map(|r| {
                    let shape = r
                        .args
                        .iter()
                        .map(|s| cardinality(self.indices.universe, s))
                        .chain([2])
                        .collect();
                    Interpretation::new(&shape, |elements| {
                        valuation.value(self.vars[self.indices.get(&r.name, 0, elements)]) as usize
                    })
                })
                .collect(),
        )
    }

    fn mk_and(&self, bdds: impl IntoIterator<Item = Bdd>) -> Bdd {
        bdds.into_iter()
            .fold(self.bdds.mk_true(), |acc, term| acc.and(&term))
    }

    fn mk_or(&self, bdds: impl IntoIterator<Item = Bdd>) -> Bdd {
        bdds.into_iter()
            .fold(self.bdds.mk_false(), |acc, term| acc.or(&term))
    }
}

/// Convert a `BDD` back into a `Term`.
/// Returns the term and a map from (sort, element) pairs to the name of the variable.
pub fn bdd_to_term<'a>(
    bdd: &Bdd,
    indices: &BddIndices<'a>,
) -> (Term, HashMap<(&'a str, usize), String>) {
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

    // Build a map from sort elements to Term variable names
    let mut next_binding = 0;
    let mut bindings: HashMap<(&str, usize), String> = HashMap::new();
    for (sort, bound) in indices.indices.universe {
        for i in 0..*bound {
            bindings.insert((sort, i), format!("${next_binding}"));
            next_binding += 1;
        }
    }

    // Build a map from BDD variable names to Terms
    let mut vars_to_terms: HashMap<String, Term> = HashMap::new();
    for (relation, map) in indices.indices.iter() {
        for (elements, (i, _mutable)) in map {
            let name = indices.bdds.name_of(indices.vars[*i]);
            let args = indices
                .indices
                .signature
                .relations
                .iter()
                .find(|r| &r.name == relation)
                .unwrap()
                .args
                .iter()
                .zip_eq(elements)
                .map(|(sort, element)| match sort {
                    Sort::Uninterpreted(sort) => {
                        Term::Id(bindings[&(sort.as_str(), *element)].clone())
                    }
                    Sort::Bool => match element {
                        0 => Term::Literal(false),
                        1 => Term::Literal(true),
                        _ => unreachable!(),
                    },
                });
            let term = match args.len() {
                0 => Term::Id(relation.to_string()),
                _ => Term::App(relation.to_string(), 0, args.collect()),
            };
            vars_to_terms.insert(name, term);
        }
    }

    // Convert the BDD to a Term
    let term = to_term(bdd.to_boolean_expression(&indices.bdds), &vars_to_terms);
    (term, bindings)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fly::sorts::sort_check_module;

    #[test]
    fn checker_bdd_basic() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/tests/examples/basic2.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = HashMap::from([]);

        assert!(matches!(
            check(&module, &universe, Some(0), false)?,
            CheckerAnswer::Unknown,
        ));
        assert!(matches!(
            check(&module, &universe, Some(1), false)?,
            CheckerAnswer::Counterexample(_),
        ));

        Ok(())
    }

    #[test]
    fn checker_bdd_lockserver() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/examples/lockserver.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = HashMap::from([("node".to_string(), 2)]);

        assert!(matches!(
            check(&module, &universe, None, false)?,
            CheckerAnswer::Convergence(..),
        ));

        Ok(())
    }

    #[test]
    fn checker_bdd_lockserver_buggy() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/tests/examples/lockserver_buggy.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = HashMap::from([("node".to_string(), 2)]);

        let bug = check(&module, &universe, Some(12), false)?;
        assert!(matches!(bug, CheckerAnswer::Counterexample(_)));
        let bug = check(&module, &universe, None, false)?;
        assert!(matches!(bug, CheckerAnswer::Counterexample(_)));

        let too_short = check(&module, &universe, Some(11), false)?;
        assert!(matches!(too_short, CheckerAnswer::Unknown));

        Ok(())
    }

    #[test]
    fn checker_bdd_consensus() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/examples/consensus.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = std::collections::HashMap::from([
            ("node".to_string(), 1),
            ("quorum".to_string(), 1),
            ("value".to_string(), 1),
        ]);

        assert!(matches!(
            check(&module, &universe, Some(0), false)?,
            CheckerAnswer::Unknown,
        ));

        Ok(())
    }

    #[test]
    fn checker_bdd_immutability() -> Result<(), CheckerError> {
        let source =
            include_str!("../../temporal-verifier/tests/examples/success/immutability.fly");
        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = std::collections::HashMap::new();
        assert!(matches!(
            check(&module, &universe, None, false)?,
            CheckerAnswer::Convergence(..),
        ));
        Ok(())
    }

    #[test]
    fn checker_bdd_basic_reversed() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/tests/examples/basic2.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = HashMap::from([]);

        assert!(matches!(
            check_reversed(&module, &universe, Some(0), false)?,
            CheckerAnswer::Unknown,
        ));
        assert!(matches!(
            check_reversed(&module, &universe, Some(1), false)?,
            CheckerAnswer::Counterexample(_),
        ));

        Ok(())
    }

    #[test]
    fn checker_bdd_lockserver_reversed() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/examples/lockserver.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = HashMap::from([("node".to_string(), 2)]);

        assert!(matches!(
            check_reversed(&module, &universe, None, false)?,
            CheckerAnswer::Convergence(..),
        ));

        Ok(())
    }

    #[test]
    fn checker_bdd_lockserver_buggy_reversed() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/tests/examples/lockserver_buggy.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = HashMap::from([("node".to_string(), 2)]);

        let bug = check_reversed(&module, &universe, Some(12), false)?;
        assert!(matches!(bug, CheckerAnswer::Counterexample(_)));
        let bug = check_reversed(&module, &universe, None, false)?;
        assert!(matches!(bug, CheckerAnswer::Counterexample(_)));

        let too_short = check_reversed(&module, &universe, Some(11), false)?;
        assert!(matches!(too_short, CheckerAnswer::Unknown));

        Ok(())
    }

    #[test]
    fn checker_bdd_consensus_reversed() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/examples/consensus.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = std::collections::HashMap::from([
            ("node".to_string(), 1),
            ("quorum".to_string(), 1),
            ("value".to_string(), 1),
        ]);

        assert!(matches!(
            check_reversed(&module, &universe, Some(0), false)?,
            CheckerAnswer::Unknown,
        ));

        Ok(())
    }

    #[test]
    fn checker_bdd_immutability_reversed() -> Result<(), CheckerError> {
        let source =
            include_str!("../../temporal-verifier/tests/examples/success/immutability.fly");
        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = std::collections::HashMap::new();
        assert!(matches!(
            check_reversed(&module, &universe, None, false)?,
            CheckerAnswer::Convergence(..),
        ));
        Ok(())
    }
}

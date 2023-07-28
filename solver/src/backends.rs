// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Support for launching a solver (Z3, CVC4, or CVC5) and then parsing its
//! models, which are the two features that generally differ from solver to
//! solver.

use std::{
    collections::{HashMap, HashSet},
    iter::zip,
};

use fly::{
    semantics::{Element, Interpretation},
    syntax::{Signature, Sort},
};
use smtlib::{
    conf::{CvcConf, SolverCmd, Z3Conf},
    sexp::{self, Atom},
};

use crate::{
    imp::{Backend, FOModel},
    models::{self, ModelSymbol, PartialInterp},
};

/// The type of solver being used
#[allow(missing_docs)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SolverType {
    Z3,
    Cvc4,
    Cvc5,
}

#[derive(Debug, Clone, Default)]
struct GenericOptions {
    timeout_ms: Option<usize>,
    seed: usize,
}

/// A Backend for launching and parsing Z3/CVC4/CVC5, with some hard-coded options.
#[derive(Debug, Clone)]
pub struct GenericBackend {
    solver_type: SolverType,
    bin: String,
    opts: GenericOptions,
}

impl GenericBackend {
    /// Create a Backend for a given type of solver and with a path to the
    /// solver binary.
    pub fn new(solver_type: SolverType, bin: &str) -> Self {
        Self {
            solver_type,
            bin: bin.to_string(),
            opts: Default::default(),
        }
    }

    /// Set the solver timeout. None disables the timeout.
    pub fn timeout_ms(&mut self, timeout_ms: Option<usize>) -> &mut Self {
        self.opts.timeout_ms = timeout_ms;
        return self;
    }

    /// Set the solver's random seed.
    pub fn seed(&mut self, seed: usize) -> &mut Self {
        self.opts.seed = seed;
        return self;
    }

    /// Get the solver type.
    pub fn get_solver_type(&self) -> SolverType {
        self.solver_type
    }

    /// Get the solver timeout.
    pub fn get_timeout_ms(&self) -> Option<usize> {
        self.opts.timeout_ms
    }
}

fn sort_cardinality(universes: &HashMap<String, usize>, sort: &Sort) -> usize {
    match sort {
        Sort::Bool => 2,
        Sort::Uninterpreted(s) => *universes
            .get(s)
            .unwrap_or_else(|| panic!("unknown sort {s}")),
    }
}

impl Backend for &GenericBackend {
    fn get_cmd(&self) -> SolverCmd {
        match self.solver_type {
            SolverType::Z3 => {
                let mut conf = Z3Conf::new(&self.bin);
                conf.model_compact();
                conf.timeout_ms(self.opts.timeout_ms);
                if self.opts.seed != 0 {
                    conf.options()
                        .option("smt.random_seed", format!("{}", self.opts.seed));
                    conf.options()
                        .option("sat.random_seed", format!("{}", self.opts.seed));
                }
                conf.done()
            }
            SolverType::Cvc4 => {
                let mut conf = CvcConf::new_cvc4(&self.bin);
                conf.finite_models();
                conf.interleave_enumerative_instantiation();
                conf.timeout_ms(self.opts.timeout_ms);
                if self.opts.seed != 0 {
                    conf.options().option("seed", format!("{}", self.opts.seed));
                }
                conf.done()
            }
            SolverType::Cvc5 => {
                let mut conf = CvcConf::new_cvc5(&self.bin);
                conf.finite_models();
                conf.interleave_enumerative_instantiation();
                conf.timeout_ms(self.opts.timeout_ms);
                if self.opts.seed != 0 {
                    conf.options().option("seed", format!("{}", self.opts.seed));
                }
                conf.done()
            }
        }
    }

    fn parse(
        &self,
        sig: &Signature,
        // TODO(tej): unused, maybe we can remove from Backend trait
        _n_states: usize,
        indicators: &HashSet<String>,
        model: &sexp::Sexp,
    ) -> FOModel {
        let model = match self.solver_type {
            SolverType::Z3 => models::parse_z3(model),
            SolverType::Cvc4 => models::parse_cvc(model, false),
            SolverType::Cvc5 => models::parse_cvc(model, true),
        };

        let universe: HashMap<String, usize> = model
            .universes
            .iter()
            .map(|(sort, elements)| (sort.clone(), elements.len()))
            .collect();

        let mut part_interp = PartialInterp::for_model(&model);
        let mut symbols = model.symbols.iter().collect::<Vec<_>>();
        symbols.sort_unstable_by_key(|(symbol, _)| {
            let in_signature = sig.contains_relation(symbol);
            // sort the model-only signatures first
            //
            // NOTE: this is just a heuristic to evaluate auxilliary functions
            // first, for now.
            (in_signature, symbol.to_string())
        });
        for (symbol, model_sym) in symbols.into_iter() {
            if indicators.contains(symbol) {
                continue;
            }
            let ModelSymbol {
                binders,
                body,
                ret_sort,
            } = model_sym;
            let arg_sorts = binders
                .iter()
                .map(|(_, sort)| sort.clone())
                .collect::<Vec<_>>();
            let mut shape = arg_sorts
                .iter()
                .map(|sort| sort_cardinality(&universe, sort))
                .collect::<Vec<usize>>();
            shape.push(sort_cardinality(&universe, ret_sort));
            let interp = Interpretation::new(&shape, |args: &[Element]| -> Element {
                // get the arguments as terms, based on model.universes
                let args = zip(args, &arg_sorts)
                    .map(|(&e_idx, typ)| match typ {
                        Sort::Bool => {
                            if e_idx == 0 {
                                Atom::S("false".to_string())
                            } else {
                                Atom::S("true".to_string())
                            }
                        }
                        Sort::Uninterpreted(sort) => {
                            let elements = &model.universes[sort];
                            let element = elements[e_idx].clone();
                            Atom::S(element)
                        }
                    })
                    .collect::<Vec<_>>();
                let repl: HashMap<&str, Atom> =
                    zip(binders.iter().map(|s| s.0.as_str()), args).collect();
                let e = model
                    .smt_eval(&repl, &part_interp, body)
                    .unwrap_or_else(|err| panic!("could not interpret {symbol}: {err}"));
                let res = e.s().expect("unhandled evaluation result");
                match ret_sort {
                    Sort::Bool => {
                        if res == "false" {
                            return 0;
                        } else if res == "true" {
                            return 1;
                        } else {
                            panic!("unexpected bool {res}")
                        }
                    }
                    Sort::Uninterpreted(sort) => {
                        let elements = &model.universes[sort];
                        let res_idx = elements
                            .iter()
                            .position(|x| x == res)
                            .unwrap_or_else(|| panic!("unknown {sort} element {res}"));
                        return res_idx as Element;
                    }
                }
            });
            part_interp
                .interps
                .insert(symbol.clone(), (interp, ret_sort.clone()));
        }

        let interp = part_interp
            .interps
            .into_iter()
            .filter(|(symbol, _)| sig.contains_relation(symbol))
            .map(|(symbol, (interp, _))| (symbol, interp))
            .collect();
        FOModel { universe, interp }
    }

    fn returns_minimal(&self) -> bool {
        // TODO: make sure CVC4 and CVC5 return minimal models
        match self.solver_type {
            SolverType::Z3 => false,
            SolverType::Cvc4 | SolverType::Cvc5 => true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::imp::Solver;
    use fly::parser::{parse_signature, term};
    use fly::syntax::Term;
    use smtlib::{path::solver_path, proc::SatResp};

    use std::fs::read_to_string;

    use test_log::test;

    #[test]
    fn test_issue_5_parse_model_with_auxilliary_defs() {
        let _ = pretty_env_logger::try_init();
        let sig = parse_signature(
            r#"
        sort node
        sort quorum
        sort value

        # constants:


        # functions:


        # relations:
        mutable member(node, quorum): bool
        mutable vote_request_msg(node, node): bool
        mutable voted(node): bool
        mutable vote_msg(node, node): bool
        mutable votes(node, node): bool
        mutable leader(node): bool
        mutable decided(node, value): bool
        "#,
        );

        let backend = GenericBackend {
            solver_type: SolverType::Z3,
            bin: "z3".to_string(),
            opts: Default::default(),
        };

        let model_text = read_to_string("../temporal-verifier/tests/issue_5_model.sexp")
            .expect("could not find model file");
        let model_sexp = sexp::parse(&model_text).expect("test model does not parse");

        let fo_model = (&backend).parse(&sig, 1, &HashSet::new(), &model_sexp);
        // a (primed) relation from the signature
        assert!(fo_model.interp.contains_key("leader'"));
        // auxilliary definition in Z3's model
        assert!(!fo_model.interp.contains_key("k!1058"));
    }

    #[test]
    fn test_parse_test_model() {
        let _ = pretty_env_logger::try_init();
        let sig = parse_signature(
            r#"
        sort node
        mutable votes(node, node): bool
        "#,
        );

        let backend = GenericBackend {
            solver_type: SolverType::Z3,
            bin: solver_path("z3"),
            opts: Default::default(),
        };

        let model_text = read_to_string("../temporal-verifier/tests/test_model.sexp")
            .expect("could not find model file");
        let model_sexp = sexp::parse(&model_text).expect("test model does not parse");

        let fo_model = (&backend).parse(&sig, 0, &HashSet::new(), &model_sexp);
        assert!(fo_model.interp.contains_key("votes"));
    }

    #[test]
    fn test_check_sat_assuming_and_get_minimal_model() {
        let sig = parse_signature(
            r#"
            sort A
            mutable x: A
            mutable p(A): bool
        "#,
        );
        let backend = GenericBackend {
            solver_type: SolverType::Z3,
            bin: solver_path("z3"),
            opts: Default::default(),
        };
        let mut solver =
            Solver::new(&sig, 1, &backend, None).expect("could not create solver for test");
        let ind = solver.get_indicator("i");
        // make sure that the first universe tried is not minimal
        solver.assert(&term("exists a1:A, a2:A. a1 != a2"));
        solver.assert(&Term::implies(ind.clone(), term("p(x)")));
        let mut assumptions = HashMap::new();
        assumptions.insert(ind, true);
        let resp = solver.check_sat(assumptions).unwrap();
        assert!(resp == SatResp::Sat);
        let model = &solver
            .get_minimal_model()
            .expect("solver error while minimizing")[0];
        assert_eq!(
            model.eval(&term("p(x)")),
            1,
            "p(x) should be true due to assumption"
        );
    }
}

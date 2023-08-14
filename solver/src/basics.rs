// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Traits defining a very basic interface to SMT solvers and a few implementations of them.

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

use fly::{
    semantics::Model,
    syntax::{Signature, Term},
};
use smtlib::proc::{SatResp, SmtPid, SolverError};

use crate::conf::SolverConf;

/// Check the following SMT query with the given solver configuration.
/// The query is defined by the query configuration, a sequence of assertions,
/// and a sequence of assumptions which are mapped from integer keys (which would
/// later represent them in an unsat core) and a `bool` determining whether they
/// should be assumed to be true or false.
fn check_sat_conf(
    solver_conf: &SolverConf,
    query_conf: &QueryConf<SmtPid>,
    assertions: &[Term],
    assumptions: &HashMap<usize, (Term, bool)>,
) -> Result<BasicSolverResp, SolverError> {
    let start_time = std::time::Instant::now();
    let log_result = |res: String| {
        log::debug!(
            "            {:?}(timeout={}) returned {res} after {}ms ({} assertions, {} assumptions)",
            solver_conf.solver_type(),
            solver_conf.get_timeout_ms().unwrap_or(0) / 1000,
            start_time.elapsed().as_millis(),
            assertions.len(),
            assumptions.len(),
        );
    };
    let mut solver = solver_conf.solver(query_conf.sig, query_conf.n_states);
    if query_conf
        .cancelers
        .as_ref()
        .is_some_and(|c| !c.add_canceler(solver.pid()))
    {
        return Err(SolverError::Killed);
    }

    for t in assertions {
        solver.assert(t);
    }

    let mut solver_assumptions = HashMap::new();
    for (i, (t, b)) in assumptions {
        let ind = solver.get_indicator(i.to_string().as_str());
        solver.assert(&Term::iff(&ind, t));
        solver_assumptions.insert(ind, *b);
    }

    let resp = match solver.check_sat(solver_assumptions) {
        Ok(SatResp::Sat) => {
            log_result("SAT".to_string());
            let get_model_resp = if query_conf.minimal_model {
                solver.get_minimal_model()
            } else {
                solver.get_model()
            };
            get_model_resp.map(BasicSolverResp::Sat)
        }
        Ok(SatResp::Unsat) => solver.get_unsat_core().map(|core| {
            log_result("UNSAT".to_string());
            BasicSolverResp::Unsat(
                core.into_iter()
                    .map(|ind| match ind.0 {
                        Term::Id(s) => s[6..].parse::<usize>().unwrap(),
                        _ => panic!("indicator is not Term::Id"),
                    })
                    .collect(),
            )
        }),
        Ok(SatResp::Unknown(reason)) => {
            log_result(format!("unknown: {reason}"));
            Ok(BasicSolverResp::Unknown(reason))
        }
        Err(err) => {
            log_result(format!("error: {err}"));
            Err(err)
        }
    };

    if query_conf.save_tee {
        solver.save_tee();
    }

    resp
}

/// Defines a configuration for performing a solver query.
pub struct QueryConf<'a, C: BasicSolverCanceler> {
    /// The signature used
    pub sig: &'a Signature,
    /// The number of states
    pub n_states: usize,
    /// Optional [`SolverCancelers`] which can be used to cancel the query at any time
    pub cancelers: Option<SolverCancelers<C>>,
    /// Whether to return a minimal model in case of satifiability
    pub minimal_model: bool,
    /// Whether to save the solver tee after the query
    pub save_tee: bool,
}

/// A basic solver response
pub enum BasicSolverResp {
    /// A sat response together with a satisfying trace
    Sat(Vec<Model>),
    /// An unsat response together with an unsat core
    Unsat(HashSet<usize>),
    /// An unknown response together with a reason
    Unknown(String),
}

/// A basic solver interface
pub trait BasicSolver: Sync + Send {
    /// A canceler type for this solver, able to cancel queries at any time
    type Canceler: BasicSolverCanceler;

    /// Check the satisfiability of the following query using the solver.
    /// The query is defined by a query configuration, a sequence of assertions,
    /// and a sequence of assumptions which are mapped from integer keys (which
    /// would later represent them in an unsat core) and a `bool` determining
    /// whether they should be assumed to be true or false.
    fn check_sat(
        &self,
        query_conf: &QueryConf<Self::Canceler>,
        assertions: &[Term],
        assumptions: &HashMap<usize, (Term, bool)>,
    ) -> Result<BasicSolverResp, SolverError>;
}

/// A basic canceler object for a solver, able to cancel queries at any time
pub trait BasicSolverCanceler: Sync + Send {
    /// Cancel the query associated with this canceler.
    fn cancel(&self);
}

/// Maintains a set of [`BasicSolverCanceler`]'s which can be used to cancel queries whenever necessary.
/// Composed of a `bool` which tracks whether the set has been canceled, followed by the
/// [`BasicSolverCanceler`]'s of the solvers it tracks.
pub struct SolverCancelers<C: BasicSolverCanceler>(Arc<Mutex<(bool, Vec<C>)>>);

impl<C: BasicSolverCanceler> Clone for SolverCancelers<C> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<C: BasicSolverCanceler> Default for SolverCancelers<C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: BasicSolverCanceler> SolverCancelers<C> {
    /// Create a new empty set of solver cancelers.
    pub fn new() -> Self {
        SolverCancelers(Arc::new(Mutex::new((false, vec![]))))
    }

    /// Add the given canceler to the set of cancelers.
    ///
    /// Returns `true` if the [`BasicSolverCanceler`] was added, or `false` if the set has already been canceled.
    pub fn add_canceler(&self, canceler: C) -> bool {
        let mut cancelers = self.0.lock().unwrap();
        if cancelers.0 {
            false
        } else {
            cancelers.1.push(canceler);
            true
        }
    }

    /// Cancel all solvers tracked by this set of cancelers.
    pub fn cancel(&self) {
        let mut cancelers = self.0.lock().unwrap();
        cancelers.0 = true;
        for canceler in cancelers.1.drain(..) {
            canceler.cancel();
        }
    }
}

/// A basic solver which uses a single solver configuration
pub struct SingleSolver(SolverConf);

/// A set of solvers used in a fallback fashion: on each query the solvers
/// are tried sequentially until (1) one of them returns a sat or unsat response,
/// (2) all solvers return unknown, or (3) the query is canceled.
pub struct FallbackSolvers(Vec<SolverConf>);

impl BasicSolverCanceler for SmtPid {
    fn cancel(&self) {
        self.kill()
    }
}

impl SingleSolver {
    /// Create a new solver with the given configuration.
    pub fn new(conf: SolverConf) -> Self {
        Self(conf)
    }

    /// Return a reference to the solver configuration used.
    pub fn as_conf(&self) -> &SolverConf {
        &self.0
    }
}

impl BasicSolver for SingleSolver {
    type Canceler = SmtPid;

    fn check_sat(
        &self,
        query_conf: &QueryConf<Self::Canceler>,
        assertions: &[Term],
        assumptions: &HashMap<usize, (Term, bool)>,
    ) -> Result<BasicSolverResp, SolverError> {
        match check_sat_conf(&self.0, query_conf, assertions, assumptions) {
            Ok(BasicSolverResp::Unknown(reason)) | Err(SolverError::CouldNotMinimize(reason)) => {
                Ok(BasicSolverResp::Unknown(reason))
            }
            res => res,
        }
    }
}

impl FallbackSolvers {
    /// Create a new set of fallback solvers with the given configurations.
    pub fn new(confs: Vec<SolverConf>) -> Self {
        Self(confs)
    }
}

impl BasicSolver for FallbackSolvers {
    type Canceler = SmtPid;

    fn check_sat(
        &self,
        query_conf: &QueryConf<Self::Canceler>,
        assertions: &[Term],
        assumptions: &HashMap<usize, (Term, bool)>,
    ) -> Result<BasicSolverResp, SolverError> {
        let mut unknowns: Vec<String> = vec![];
        for solver_conf in &self.0 {
            match check_sat_conf(solver_conf, query_conf, assertions, assumptions) {
                Ok(BasicSolverResp::Unknown(reason))
                | Err(SolverError::CouldNotMinimize(reason)) => {
                    unknowns.push(reason);
                }
                res => return res,
            }
        }

        Ok(BasicSolverResp::Unknown(unknowns.join("\n")))
    }
}

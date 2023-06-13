use std::path::PathBuf;

use crate::fly::syntax::Signature;

use super::{backends::GenericBackend, Solver};

/// Wrapper around the configuration needed to launch a solver.
#[derive(Debug, Clone)]
pub struct SolverConf {
    /// Which backend to use for launched solvers.
    pub backend: GenericBackend,
    /// The optional path to tee SMT output to.
    pub tee: Option<PathBuf>,
}

impl SolverConf {
    /// Launch a new solver with the given configuration.
    pub fn solver(&self, sig: &Signature, n_states: usize) -> Solver<&GenericBackend> {
        // TODO: failures to start the solver should be bubbled up to user nicely
        Solver::new(sig, n_states, &self.backend, self.tee.as_deref())
            .expect("could not start solver")
    }
}

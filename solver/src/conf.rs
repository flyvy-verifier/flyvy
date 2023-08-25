// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Holds the configuration need to launch a solver.

use std::fs::{self, create_dir_all};
use std::path::{Path, PathBuf};

use crate::{
    backends::{GenericBackend, SolverType},
    imp::Solver,
    log_dir, solver_path,
};

use fly::syntax::Signature;

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

    /// Get a new solver configuration with the specified settings
    pub fn new(
        backend_type: SolverType,
        smt: bool,
        fname: &String,
        timeout_s: usize,
        seed: usize,
    ) -> Self {
        let solver_bin = solver_path(backend_type.bin_name());
        let tee: Option<PathBuf> = if smt {
            let dir = log_dir(Path::new(fname));
            create_dir_all(&dir).expect("could not create log dir");
            if let Ok(rdir) = dir.read_dir() {
                for entry in rdir {
                    match entry {
                        Err(_) => {}
                        Ok(name) => {
                            _ = fs::remove_file(name.path());
                        }
                    }
                }
            }
            Some(dir)
        } else {
            None
        };
        let mut backend = GenericBackend::new(backend_type, &solver_bin);
        backend.timeout_ms(if timeout_s > 0 {
            Some(timeout_s * 1000)
        } else {
            None
        });
        backend.seed(seed);
        SolverConf { backend, tee }
    }

    /// Get the solver type.
    pub fn solver_type(&self) -> SolverType {
        self.backend.solver_type()
    }

    /// Get the solver timeout.
    pub fn get_timeout_ms(&self) -> Option<usize> {
        self.backend.get_timeout_ms()
    }
}

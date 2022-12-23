// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::path::PathBuf;

use crate::smtlib::proc::{CvcConf, SmtProc, SolverCmd, Z3Conf};

#[derive(Debug, Clone)]
pub struct SolverConf {
    /// Path to send all SMT output to.
    pub tee: Option<PathBuf>,
    /// Solver backend to run.
    pub backend: Backend,
    /// Command to run for the solver.
    pub solver_bin: String,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Backend {
    Z3,
    Cvc4,
    Cvc5,
}

impl Backend {
    fn cmd(&self, bin: &str) -> SolverCmd {
        match self {
            Backend::Z3 => {
                let mut conf = Z3Conf::new(bin);
                conf.model_compact();
                conf.done()
            }
            Backend::Cvc4 => {
                let mut conf = CvcConf::new_cvc4(bin);
                conf.finite_models();
                conf.done()
            }
            Backend::Cvc5 => {
                let mut conf = CvcConf::new_cvc5(bin);
                conf.finite_models();
                conf.done()
            }
        }
    }
}

impl SolverConf {
    pub fn launch(&self) -> SmtProc {
        let cmd = self.backend.cmd(&self.solver_bin);
        let mut smt_proc = SmtProc::new(cmd)
            .map_err(|err| format!("could not start solver: {err}"))
            .unwrap();
        if let Some(path) = &self.tee {
            // TODO: need some way of adding a counter to the path for
            // non-incremental assertions
            smt_proc
                .tee(path)
                .map_err(|err| format!("could not open smt2 file: {err}"))
                .unwrap();
        }
        smt_proc
    }
}

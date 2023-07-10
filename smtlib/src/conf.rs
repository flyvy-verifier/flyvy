// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Construct launch and option configurations for Z3 and CVC5.

/// The full invocation of a solver binary.
#[derive(Debug, Clone)]
pub struct SolverCmd {
    /// Binary to launch
    pub cmd: String,
    /// Arguments to pass
    pub args: Vec<String>,
    /// SMT options to send on startup
    pub options: Vec<(String, String)>,
}

impl SolverCmd {
    fn args<I, S>(&mut self, args: I)
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        self.args
            .extend(args.into_iter().map(|s| s.as_ref().to_string()));
    }

    /// Set an option.
    pub fn option<S: AsRef<str>>(&mut self, name: &str, val: S) {
        self.options
            .push((name.to_string(), val.as_ref().to_string()));
    }

    /// Build the command line string, for printing purposes.
    pub fn cmdline(&self) -> String {
        #[allow(clippy::useless_format)]
        let args: Vec<_> = self
            .args
            .iter()
            .map(|a| {
                if a.contains(' ') {
                    format!("\"{a}\"")
                } else {
                    format!("{a}")
                }
            })
            .collect();
        format!("{} {}", &self.cmd, args.join(" "))
    }
}

/// Builder for creating a Z3 [`SolverCmd`].
#[derive(Debug, Clone)]
pub struct Z3Conf(SolverCmd);

impl Z3Conf {
    /// Create a Z3Conf with some default options. Uses `cmd` as the path to Z3.
    pub fn new(cmd: &str) -> Self {
        let mut cmd = SolverCmd {
            cmd: cmd.to_string(),
            args: vec![],
            options: vec![],
        };
        cmd.args(["-in", "-smt2"]);
        cmd.option("model.completion", "true");
        let mut conf = Self(cmd);
        conf.timeout_ms(Some(30000 * 100));
        conf
    }

    /// Enable model compaction
    pub fn model_compact(&mut self) {
        self.0.option("model.compact", "true");
    }

    /// Set the SMT timeout option
    pub fn timeout_ms(&mut self, ms: Option<usize>) {
        // this is the default Z3 timeout
        let ms = ms.unwrap_or(4294967295);
        self.0.option("timeout", format!("{ms}"));
    }

    /// Get access to the raw options of the solver.
    pub fn options(&mut self) -> &mut SolverCmd {
        &mut self.0
    }

    /// Get the final command to run the solver.
    pub fn done(self) -> SolverCmd {
        self.0
    }
}

/// Builder for a CVC4 or CVC5 [`SolverCmd`].
#[derive(Debug, Clone)]
pub struct CvcConf {
    version5: bool,
    cmd: SolverCmd,
}

impl CvcConf {
    fn new_cvc(cmd: &str, version5: bool) -> Self {
        let mut cmd = SolverCmd {
            cmd: cmd.to_string(),
            args: vec![],
            options: vec![],
        };
        // for CVC4, --lang smt2 is needed when using stdin, but when run on a
        // file with a .smt2 extension it will automatically use the right input
        // format.
        cmd.args(vec!["-q", "--lang", "smt2"]);
        cmd.option("interactive", "false");
        cmd.option("incremental", "true");
        cmd.option("seed", "1");
        Self { version5, cmd }
    }

    /// Create a new CVC4 builder with some default options.
    pub fn new_cvc4(cmd: &str) -> Self {
        Self::new_cvc(cmd, /*version5*/ false)
    }

    /// Create a new CVC5 builder with some default options.
    pub fn new_cvc5(cmd: &str) -> Self {
        Self::new_cvc(cmd, /*version5*/ true)
    }

    /// Enable finite model finding with mbqi.
    pub fn finite_models(&mut self) {
        self.cmd.option("finite-model-find", "true");
        if self.version5 {
            self.cmd.option("mbqi", "true");
            self.cmd.option("fmf-mbqi", "fmc")
        } else {
            self.cmd.option("mbqi", "fmc");
        }
    }

    /// Enable interleaving enumerative instantiation with other techniques.
    pub fn interleave_enumerative_instantiation(&mut self) {
        if self.version5 {
            self.cmd.option("enum-inst-interleave", "true");
        } else {
            self.cmd.option("fs-interleave", "true");
        }
    }

    /// Set a per-query time limit. None sets no time limit.
    pub fn timeout_ms(&mut self, ms: Option<usize>) {
        let ms = ms.unwrap_or(0);
        self.cmd.option("tlimit-per", format!("{ms}"));
    }

    /// Get access to the raw options of the solver.
    pub fn options(&mut self) -> &mut SolverCmd {
        &mut self.cmd
    }

    /// Get the final command to run the solver.
    pub fn done(self) -> SolverCmd {
        self.cmd
    }
}

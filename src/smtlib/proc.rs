// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Manage a running SMT process.
//!
//! This is a low-level generic API for SMT-LIB solvers; the solver-specific
//! parts are captured by the [`SolverCmd`] passed to launch the solver and in
//! the code that parses models returned by [`SmtProc::check_sat`].

use crate::smtlib::sexp;
use std::{
    ffi::{OsStr, OsString},
    fs::{File, OpenOptions},
    io::{self, BufRead, BufReader, Write},
    path::Path,
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
};
use thiserror::Error;

use super::sexp::{app, atom_s, sexp_l, Sexp};

/// SmtProc wraps an instance of a solver process.
#[derive(Debug)]
pub struct SmtProc {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    tee: Option<File>,
    cmdline: String,
}

/// SatResp is a solver's response to a `(check-sat)` or similar command.
///
/// For unknown it also returns the reason the solver provides.
#[derive(Debug, Clone)]
pub enum SatResp {
    /// The query is satisfiable.
    Sat,
    /// The query is unsatisfiable (and thus negated assertions are valid).
    Unsat,
    /// Unknown whether the query is sat or unsat. The reason is the one given
    /// by (get-info :reason-unknown).
    ///
    /// This can happen to a timeout or limitations of quantifier instantiation
    /// heuristics, for example.
    Unknown(String),
}

#[derive(Error, Debug)]
pub enum SolverError {
    #[error("some io went wrong")]
    Io(#[from] io::Error),
    #[error("solver unexpectedly exited")]
    UnexpectedClose,
}

type Result<T> = std::result::Result<T, SolverError>;

#[derive(Debug, Clone)]
pub struct SolverCmd {
    pub cmd: String,
    pub args: Vec<String>,
}

impl SolverCmd {
    fn arg<S: AsRef<str>>(&mut self, arg: S) {
        self.args.push(arg.as_ref().to_string());
    }

    fn args<I, S>(&mut self, args: I)
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        self.args
            .extend(args.into_iter().map(|s| s.as_ref().to_string()));
    }

    fn cmdline(&self) -> String {
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

#[derive(Debug, Clone)]
pub struct Z3Conf(SolverCmd);

impl Z3Conf {
    pub fn new(cmd: &str) -> Self {
        let mut cmd = SolverCmd {
            cmd: cmd.to_string(),
            args: vec![],
        };
        cmd.args(vec!["-in", "-smt2", "model.completion=true"]);
        let mut conf = Self(cmd);
        conf.timeout_ms(10000);
        conf
    }

    pub fn model_compact(&mut self) {
        self.0.arg("model.compact=true");
    }

    pub fn timeout_ms(&mut self, ms: usize) {
        self.0.arg(format!("timeout={ms}"));
    }

    /// Get the final command to run the solver.
    pub fn done(self) -> SolverCmd {
        self.0
    }
}

#[derive(Debug, Clone)]
pub struct CvcConf {
    version5: bool,
    cmd: SolverCmd,
}

impl CvcConf {
    fn default_args() -> Vec<String> {
        vec!["-q", "--no-interactive", "--lang", "smt2", "--incremental"]
            .into_iter()
            .map(|s| s.to_string())
            .collect()
    }

    pub fn new_cvc4(cmd: &str) -> Self {
        let cmd = SolverCmd {
            cmd: cmd.to_string(),
            args: Self::default_args(),
        };
        Self {
            version5: false,
            cmd,
        }
    }

    pub fn new_cvc5(cmd: &str) -> Self {
        let cmd = SolverCmd {
            cmd: cmd.to_string(),
            args: Self::default_args(),
        };
        Self {
            version5: true,
            cmd,
        }
    }

    /// Enable finite model finding with mbqi.
    pub fn finite_models(&mut self) {
        self.cmd.arg("--finite-model-find");
        if self.version5 {
            self.cmd.args(["--mbqi", "--fmf-mbqi=fmc"]);
        } else {
            self.cmd.arg("--mbqi=fmc");
        }
    }

    pub fn done(self) -> SolverCmd {
        self.cmd
    }
}

impl Drop for SmtProc {
    fn drop(&mut self) {
        self.kill();
    }
}

impl SmtProc {
    pub fn new(cmd: SolverCmd) -> Result<Self> {
        let cmdline = cmd.cmdline();
        let mut child = Command::new(OsStr::new(&cmd.cmd))
            .args(cmd.args.into_iter().map(OsString::from))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .map_err(SolverError::from)?;
        let stdin = child.stdin.take().unwrap();
        let stdout = BufReader::new(child.stdout.take().unwrap());
        let mut proc = Self {
            child,
            stdin,
            stdout,
            cmdline,
            tee: None,
        };
        proc.send(&app(
            "set-option",
            vec![atom_s(":produce-models"), atom_s("true")],
        ));
        proc.send(&app(
            "set-option",
            vec![atom_s(":produce-unsat-assumptions"), atom_s("true")],
        ));
        Ok(proc)
    }

    /// Direct all SMT-LIB input to a new file at `path` while also sending to
    /// the solver process.
    pub fn tee<P: AsRef<Path>>(&mut self, path: P) -> Result<()> {
        if self.tee.is_some() {
            panic!("attempt to tee solver twice");
        }
        let mut f = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(path)
            .map_err(SolverError::from)?;
        _ = writeln!(f, ";; {}", self.cmdline);
        self.tee = Some(f);
        Ok(())
    }

    /// Low-level API to send the solver a command as an s-expression. This
    /// should only be used for commands that do not require a response.
    pub fn send(&mut self, data: &sexp::Sexp) {
        writeln!(self.stdin, "{data}").expect("I/O error: failed to send to solver");
        if let Some(f) = &mut self.tee {
            // TODO: this should be pretty-printed
            writeln!(f, "{data}").unwrap();
        }
    }

    /// Low-level API to send the solver a command that expects a response,
    /// which is parsed as a single s-expression.
    pub fn send_with_reply(&mut self, data: &sexp::Sexp) -> Result<sexp::Sexp> {
        self.send(data);
        self.get_sexp()
    }

    /// Add a comment to the tee'd file.
    ///
    /// The comment is passed as a closure, which is not evaluated if there is
    /// no tee'd smt2 file.
    pub fn comment_with<F>(&mut self, comment: F)
    where
        F: FnOnce() -> String,
    {
        if let Some(f) = &mut self.tee {
            let comment = comment();
            _ = writeln!(f);
            _ = writeln!(f, ";; {comment}");
        }
    }

    pub fn get_info(&mut self, attribute: &str) -> Result<Sexp> {
        let resp = self.send_with_reply(&app("get-info", [atom_s(attribute)]))?;
        match resp {
            Sexp::List(s) => {
                assert_eq!(s.len(), 2);
                assert_eq!(
                    &s[0],
                    &atom_s(attribute),
                    "unexpected response to get-info {}",
                    &s[0],
                );
                Ok(s[1].clone())
            }
            _ => panic!("unexpected get-info format {resp}"),
        }
    }

    fn parse_sat(&mut self, resp: &str) -> SatResp {
        if resp == "unsat" {
            return SatResp::Unsat;
        }
        if resp == "sat" {
            return SatResp::Sat;
        }
        if resp == "unknown" {
            let reason = self
                .get_info(":reason-unknown")
                .expect("could not get :reason-unknown");
            return SatResp::Unknown(reason.to_string());
        }
        panic!("unexpected check-sat response {resp}");
    }

    /// Send the solver `(check-sat)`. For unknown gets a reason, but does not
    /// call `(get-model)` for sat.
    pub fn check_sat(&mut self) -> Result<SatResp> {
        self.send(&app("check-sat", []));
        let resp = self.get_response(|s| s.to_string())?;
        Ok(self.parse_sat(&resp))
    }

    pub fn check_sat_assuming(&mut self, assumptions: &[Sexp]) -> Result<SatResp> {
        self.send(&app(
            "check-sat-assuming",
            vec![sexp_l(assumptions.to_vec())],
        ));
        let resp = self.get_response(|s| s.to_string())?;
        Ok(self.parse_sat(&resp))
    }

    /// Run `(get-unsat-assumptions)` following an unsat response to get the
    /// list of terms used in the proof.
    ///
    /// Fails if the previous command wasn't a check_sat or check_sat_assuming
    /// that returned sat.
    pub fn get_unsat_assumptions(&mut self) -> Result<Vec<Sexp>> {
        let sexp = self.send_with_reply(&app("get-unsat-assumptions", vec![]))?;
        if let Sexp::List(ss) = sexp {
            Ok(ss)
        } else {
            panic!("malformed get-unsat-assumptions response: {sexp}")
        }
    }

    /// A marker for determining end of solver response.
    const DONE: &str = "<<DONE>>";

    /// Low-level mechanism to get a response. Note that this needs to be issued
    /// after each query that returns a response, since it sends a marker and
    /// waits for the solver to reach that marker.
    fn get_response<F, T>(&mut self, cb: F) -> Result<T>
    where
        F: FnOnce(&str) -> T,
    {
        writeln!(self.stdin, r#"(echo "{}")"#, Self::DONE)
            .expect("I/O error: failed to send to solver");
        self.stdin
            .flush()
            .expect("I/O error: failed to send to solver");
        // buf accumulates the entire response, which is read line-by-line
        // looking for the DONE marker.
        let mut buf = String::new();
        loop {
            let last_end = buf.len();
            // n is the number of bytes read (that is, the length of this line
            // including the newline)
            let n = self.stdout.read_line(&mut buf)?;
            if n == 0 {
                return Err(SolverError::UnexpectedClose);
            }
            // last line, without the newline
            let last_line = &buf[last_end..last_end + n - 1];
            // Z3 doesn't put quotes and CVC does (quotes do follow SMT-LIB)
            if last_line == Self::DONE || last_line == format!("\"{}\"", Self::DONE) {
                let response = buf[..last_end].trim_end();
                return Ok(cb(response));
            }
        }
    }

    fn get_sexp(&mut self) -> Result<Sexp> {
        self.get_response(|s| sexp::parse(s).expect("could not parse solver response"))
    }

    fn kill(&mut self) {
        _ = writeln!(self.stdin, "(exit)");
        _ = self.stdin.flush();
        _ = self.child.kill();
    }
}

#[cfg(test)]
mod tests {
    use crate::smtlib::{
        proc::{SatResp, Z3Conf},
        sexp::{app, atom_s, parse},
    };
    use eyre::Context;

    use super::SmtProc;

    #[test]
    fn test_check_sat_z3() {
        let z3 = Z3Conf::new("z3").done();
        let mut solver = SmtProc::new(z3).unwrap();
        let response = solver.check_sat().wrap_err("could not check-sat").unwrap();
        assert!(
            matches!(response, SatResp::Sat { .. }),
            "should be sat, got {response:?}"
        );
    }

    #[test]
    fn test_get_model_z3() {
        let z3 = Z3Conf::new("z3").done();
        let mut solver = SmtProc::new(z3).unwrap();
        solver.send(&app("declare-const", [atom_s("a"), atom_s("Bool")]));

        let e = parse("(assert (and a (not a)))").unwrap();
        solver.send(&e);

        let response = solver.check_sat().wrap_err("could not check-sat").unwrap();
        insta::assert_debug_snapshot!(response, @"Unsat");
    }
}

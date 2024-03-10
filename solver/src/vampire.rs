// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Support for the Vampire theorem prover

use lazy_static::lazy_static;
use std::{
    collections::HashMap,
    ffi::OsStr,
    fs::{create_dir_all, remove_file, File},
    io::{Read, Write},
    path::PathBuf,
    process::{Command, Stdio},
    sync::Mutex,
};

use crate::{
    basics::{BasicCanceler, BasicSolver, BasicSolverResp, QueryConf},
    sexp,
    tptp::parse_trace,
};
use fly::syntax::{Binder, Signature, Sort, Term};
use smtlib::{
    proc::{SmtPid, SolverError, Status},
    sexp::{app, atom_i, atom_s, sexp_l, Sexp},
};

lazy_static! {
    static ref QUERY_COUNT: Mutex<usize> = Mutex::new(0);
}

static QUERY_DIR: &str = ".vampire-queries";

fn new_query_id() -> usize {
    let mut count = QUERY_COUNT.lock().unwrap();
    let id = *count;
    *count += 1;
    id
}

#[derive(Debug)]
/// Mode of operation for a Vampire solver
pub enum VampireMode {
    /// Default mode
    None,
    /// Finite-model building
    Fmb,
    /// CASC competition mode
    Casc,
    /// CASC-SAT competition mode
    CascSat,
}

/// A Vampire solver configuration
pub struct VampireOptions {
    mode: VampireMode,
}

struct Contents(Vec<Sexp>);

impl Contents {
    fn append(&mut self, data: Sexp) {
        self.0.push(data)
    }
}

impl ToString for Contents {
    fn to_string(&self) -> String {
        self.0
            .iter()
            .map(|s| {
                if let Sexp::Comment(c) = s {
                    #[allow(clippy::comparison_to_empty)]
                    if c == "" {
                        return "".to_string();
                    }
                    return format!(";; {c}");
                }
                // TODO: this should be pretty-printed
                s.to_string()
            })
            .collect::<Vec<_>>()
            .join("\n")
    }
}

fn append_signature(contents: &mut Contents, signature: &Signature, n_states: usize) {
    contents.append(app("set-logic", vec![atom_s("UFNIA")]));
    for sort in &signature.sorts {
        contents.append(app("declare-sort", [atom_s(sort.clone()), atom_i(0)]));
    }
    for r in &signature.relations {
        // immutable symbols are always declared once
        if !r.mutable {
            contents.append(app(
                "declare-fun",
                [
                    atom_s(&r.name),
                    sexp_l(r.args.iter().map(sexp::sort)),
                    sexp::sort(&r.sort),
                ],
            ));
        }
        // mutable symbols are declared according to n_states (or not at all
        // if n_states=0)
        if r.mutable {
            for n_primes in 0..n_states {
                let name = &r.name;
                contents.append(app(
                    "declare-fun",
                    [
                        atom_s(format!("{name}{}", "'".repeat(n_primes))),
                        sexp_l(r.args.iter().map(sexp::sort)),
                        sexp::sort(&r.sort),
                    ],
                ));
            }
        }
    }
}

fn append_model_axioms(tee: &mut Contents, signature: &Signature, n_states: usize) {
    for r in &signature.relations {
        let binders: Vec<Binder> = r
            .args
            .iter()
            .enumerate()
            .map(|(i, s)| match s {
                Sort::Uninterpreted(sort) => Binder {
                    name: format!("__{sort}_{i}"),
                    sort: s.clone(),
                },
                _ => unimplemented!(),
            })
            .collect();
        let n = if r.mutable { n_states } else { 1 };
        let args: Vec<Term> = binders.iter().map(|b| Term::id(&b.name)).collect();
        for i in 0..n {
            let term = Term::app(&r.name, i, args.clone());
            let refl = Term::equals(term.clone(), term);
            tee.append(app(
                "assert",
                [sexp::term(&Term::forall(binders.clone(), refl))],
            ));
        }
    }

    for sort in signature
        .sorts
        .iter()
        .cloned()
        .map(Sort::Uninterpreted)
        .chain([Sort::Bool])
    {
        let refl_var = "__refl_var".to_string();
        let term = Term::id(&refl_var);
        let refl = Term::equals(term.clone(), term);
        tee.append(app(
            "assert",
            [sexp::term(&Term::forall(
                vec![Binder {
                    name: refl_var,
                    sort,
                }],
                refl,
            ))],
        ));
    }
}

fn append_term(contents: &mut Contents, term: &Term) {
    contents.append(app("assert", [sexp::term(term)]));
}

fn append_check_sat(contents: &mut Contents) {
    contents.append(app("check-sat", []));
}

impl VampireMode {
    fn mode_str(&self) -> &str {
        match self {
            VampireMode::None => "none",
            VampireMode::Fmb => "fmb",
            VampireMode::Casc => "casc",
            VampireMode::CascSat => "casc_sat",
        }
    }
}

impl VampireOptions {
    /// Create a new Vampire configuration with the given mode.
    pub fn new(mode: VampireMode) -> Self {
        Self { mode }
    }

    fn args(&self) -> Vec<&str> {
        let mut a: Vec<&str> = vec!["--input_syntax", "smtlib2"];
        match self.mode {
            VampireMode::None => (),
            VampireMode::Fmb => a.extend(["-sa", "fmb"]),
            VampireMode::Casc => a.extend(["--mode", "casc"]),
            VampireMode::CascSat => a.extend(["--mode", "casc_sat"]),
        }
        a
    }

    fn get_stdin_fname(&self, id: usize) -> PathBuf {
        PathBuf::from(QUERY_DIR).join(format!("query-{}-{id}.smt2", self.mode.mode_str(),))
    }

    fn get_stdout_fname(&self, id: usize) -> PathBuf {
        PathBuf::from(QUERY_DIR).join(format!("result-{}-{id}.smt2", self.mode.mode_str(),))
    }

    fn run(
        &self,
        contents: Contents,
        query_conf: &QueryConf<SmtPid>,
    ) -> Result<String, SolverError> {
        create_dir_all(QUERY_DIR).unwrap();
        let id = new_query_id();
        let in_fname = self.get_stdin_fname(id);
        let data = contents.to_string();
        let mut stdin = File::create(&in_fname).unwrap();
        write!(&mut stdin, "{data}").unwrap();
        drop(stdin);

        let out_fname = self.get_stdout_fname(id);
        let stdout = File::create(&out_fname).unwrap();

        let cleanup = || {
            remove_file(&in_fname).unwrap();
            remove_file(&out_fname).unwrap();
        };

        let mut child = Command::new(OsStr::new(&"./solvers/vampire"))
            .args(
                self.args()
                    .iter()
                    .map(AsRef::as_ref)
                    .chain([in_fname.as_os_str()]),
            )
            .stdin(Stdio::null())
            .stdout(stdout)
            .stderr(Stdio::inherit())
            .spawn()
            .unwrap();

        let pid = SmtPid::new(child.id(), Status::Running { in_call: true });
        if query_conf
            .cancelers
            .as_ref()
            .is_some_and(|c| !c.add_canceler(pid.clone()))
        {
            cleanup();
            pid.cancel();
            child.wait().unwrap();
            return Err(SolverError::Killed);
        }

        child.wait().unwrap();
        if pid.is_canceled() {
            cleanup();
            return Err(SolverError::Killed);
        }

        let mut out_buf = String::new();
        let mut stdout = File::open(&out_fname).unwrap();
        stdout.read_to_string(&mut out_buf).unwrap();
        drop(stdout);
        cleanup();

        Ok(out_buf)
    }
}

impl BasicSolver for VampireOptions {
    type Canceler = SmtPid;

    fn check_sat(
        &self,
        query_conf: &QueryConf<Self::Canceler>,
        assertions: &[Term],
        assumptions: &HashMap<usize, (Term, bool)>,
    ) -> Result<BasicSolverResp, SolverError> {
        assert!(!query_conf.save_tee);
        let assump_sizes: Vec<_> = assumptions.values().map(|(t, _)| t.size()).collect();
        let start_time = std::time::Instant::now();
        let log_result = |res: String| {
            log::debug!(
            "            Vampire({:?}) returned {res} after {}ms ({} assertions, {} assumptions: max_lit={}, sum_lit={})",
            self.mode,
            start_time.elapsed().as_millis(),
            assertions.len(),
            assumptions.len(),
            assump_sizes.iter().max().unwrap_or(&0),
            assump_sizes.iter().sum::<usize>()
        );
        };

        let mut contents = Contents(vec![]);
        append_signature(&mut contents, query_conf.sig, query_conf.n_states);
        append_model_axioms(&mut contents, query_conf.sig, query_conf.n_states);

        for t in assertions {
            append_term(&mut contents, t);
        }

        for (t, b) in assumptions.values() {
            match b {
                true => append_term(&mut contents, t),
                false => append_term(&mut contents, &Term::not(t)),
            }
        }

        append_check_sat(&mut contents);

        let out = self.run(contents, query_conf)?;
        let lines: Vec<&str> = out.split('\n').collect();

        if lines
            .iter()
            .any(|line| line.starts_with("% SZS status Unsatisfiable"))
        {
            log_result("UNSAT".to_string());
            return Ok(BasicSolverResp::Unsat(
                assumptions.keys().cloned().collect(),
            ));
        }

        if lines
            .iter()
            .any(|line| line.starts_with("% SZS status Satisfiable"))
        {
            if let (Some(start), Some(end)) = (
                lines
                    .iter()
                    .position(|line| line.starts_with("% SZS output start FiniteModel")),
                lines
                    .iter()
                    .position(|line| line.starts_with("% SZS output end FiniteModel")),
            ) {
                log_result("SAT".to_string());
                let model_str = lines[(start + 1)..end].join("\n");
                return Ok(BasicSolverResp::Sat(parse_trace(
                    query_conf.sig,
                    query_conf.n_states,
                    &model_str,
                )));
            }
        }

        log_result(format!("unknown: {out}"));
        Ok(BasicSolverResp::Unknown(out))
    }
}

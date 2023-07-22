// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Record SMT output and save to a file for debugging purposes.

use std::{
    collections::hash_map::DefaultHasher,
    fs::OpenOptions,
    hash::{Hash, Hasher},
    io::{self, Write},
    path::{Path, PathBuf},
};

use crate::sexp::Sexp;

/// Track and save SMT sent to solver so far.
#[derive(Debug)]
pub struct Tee {
    dir: PathBuf,
    contents: Vec<Sexp>,
}

fn calculate_hash<T: Hash>(v: T) -> String {
    let mut hash_state = DefaultHasher::new();
    v.hash(&mut hash_state);
    let h = hash_state.finish();
    return format!("{h:016x}")[..8].to_string();
}

impl Tee {
    /// Create a new empty `Tee`.
    pub fn new<P: AsRef<Path>>(dir: P) -> Self {
        Self {
            dir: dir.as_ref().to_path_buf(),
            contents: vec![],
        }
    }

    /// Append a raw s-expression sent to solver.
    pub fn append(&mut self, s: Sexp) {
        self.contents.push(s)
    }

    /// Save the SMT2 input currently sent to the solver to a file based on
    /// content hash. Returns the saved file name.
    pub fn save(&self) -> io::Result<PathBuf> {
        let contents = self
            .contents
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
            .join("\n");
        let hash = calculate_hash(&contents);
        let fname = PathBuf::from(format!("query-{hash}.smt2"));
        let dest = self.dir.join(&fname);
        let mut f = OpenOptions::new()
            .create(true)
            .write(true)
            .truncate(true)
            .open(dest)?;
        write!(&mut f, "{contents}")?;
        Ok(fname)
    }
}

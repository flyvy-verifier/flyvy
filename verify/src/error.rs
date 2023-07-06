// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use codespan_reporting::diagnostic::{Diagnostic, Label};
use serde::Serialize;

use fly::{semantics::Model, syntax::Span};

#[derive(Debug, Copy, Clone, Serialize, PartialEq, Eq)]
pub enum FailureType {
    FirstOrder,
    InitInv,
    NotInductive,
    Unsupported,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub enum QueryError {
    Sat(Model),
    Unknown(String),
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct AssertionFailure {
    pub loc: Span,
    pub reason: FailureType,
    pub error: QueryError,
}

impl AssertionFailure {
    pub fn diagnostic<FileId>(&self, file_id: FileId) -> Diagnostic<FileId> {
        let msg = match self.reason {
            FailureType::FirstOrder => "assertion failure",
            FailureType::InitInv => "init does not imply invariant",
            FailureType::NotInductive => "invariant is not inductive",
            FailureType::Unsupported => "unsupported assertion",
        };
        Diagnostic::error()
            .with_message(msg)
            .with_labels(vec![Label::primary(file_id, self.loc.start..self.loc.end)])
            .with_notes(vec![match &self.error {
                QueryError::Sat(model) => format!("counter example:\n{}", model.fmt()),
                QueryError::Unknown(err) => format!("smt solver returned unknown: {err}"),
            }])
    }
}

#[derive(Debug, Clone, Default, Serialize, PartialEq, Eq)]
pub struct SolveError {
    pub fails: Vec<AssertionFailure>,
}

impl SolveError {
    pub fn push(&mut self, e: AssertionFailure) {
        self.fails.push(e);
    }
}

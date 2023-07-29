// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Contains error types for verification.

use codespan_reporting::diagnostic::{Diagnostic, Label};
use fly::semantics::Model;
use fly::syntax::Span;
use serde::Serialize;

/// Ways that an file can fail to be verified.
#[derive(Debug, Copy, Clone, Serialize, PartialEq, Eq)]
pub enum FailureType {
    /// An invariant was not implied by the initial condition
    InitInv,
    /// An invariant was not inductive
    NotInductive,
    /// An invariant was not determined to be first order
    /// and could not become a temporal assertion.
    Unsupported,
}

/// Results from the solver that aren't Unsat.
// This is used as a Result<(), QueryError>
#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub enum QueryError {
    /// The solver returned Sat
    Sat(Vec<Model>),
    /// The solver returned Unknown
    Unknown(String),
}

/// Contains information needed to report a good error message.
#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct AssertionFailure {
    /// The location of the error
    pub loc: Option<Span>,
    /// The reason for the error
    pub reason: FailureType,
    /// The symptom of the error
    pub error: QueryError,
}

impl AssertionFailure {
    /// Convert the AssertionFailure struct to a Diagnostic that can be printed.
    pub fn diagnostic<FileId>(&self, file_id: FileId) -> Diagnostic<FileId> {
        let msg = match self.reason {
            FailureType::InitInv => "init does not imply invariant",
            FailureType::NotInductive => "invariant is not inductive",
            FailureType::Unsupported => "unsupported assertion",
        };
        let out = Diagnostic::error()
            .with_message(msg)
            .with_notes(vec![match &self.error {
                QueryError::Sat(models) => {
                    let mut message = "counter example:".to_string();
                    for (i, model) in models.iter().enumerate() {
                        message.push_str(&format!("\nstate {i}:\n"));
                        message.push_str(&model.fmt());
                    }
                    message
                }
                QueryError::Unknown(err) => format!("smt solver returned unknown: {err}"),
            }]);
        if let Some(loc) = self.loc {
            out.with_labels(vec![Label::primary(file_id, loc.start..loc.end)])
        } else {
            out
        }
    }
}

/// Contains multiple errors so that they can all be returned at once.
#[derive(Debug, Clone, Default, Serialize, PartialEq, Eq)]
pub struct SolveError {
    /// List of failures
    pub fails: Vec<AssertionFailure>,
}

impl SolveError {
    /// Add a failure to the `SolveError`.
    pub fn push(&mut self, e: AssertionFailure) {
        self.fails.push(e);
    }
}

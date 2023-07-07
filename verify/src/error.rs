// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Contains error types for verification.

use codespan_reporting::diagnostic::{Diagnostic, Label};
use serde::Serialize;

use fly::{semantics::Model, syntax::Span};

/// Ways that an file can fail to be verified.
#[derive(Debug, Copy, Clone, Serialize, PartialEq, Eq)]
pub enum FailureType {
    /// An invariant was not first order
    FirstOrder,
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
    Sat(Model),
    /// The solver returned Unknown
    Unknown(String),
}

/// Contains information needed to report a good error message.
#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct AssertionFailure {
    /// The location of the error
    pub loc: Span,
    /// The reason for the error
    pub reason: FailureType,
    /// The symptom of the error
    pub error: QueryError,
}

impl AssertionFailure {
    /// Convert the AssertionFailure struct to a Diagnostic that can be printed.
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

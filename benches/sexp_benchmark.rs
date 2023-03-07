// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::fs;

use criterion::{criterion_group, criterion_main, Criterion};
use temporal_verifier::smtlib::sexp;

pub fn sexp_parse_benchmark(c: &mut Criterion) {
    let s = fs::read_to_string("tests/issue_5_model.sexp").expect("could not open sexp file");
    c.bench_function("sexp::parse", |b| b.iter(|| sexp::parse(&s)));
}

pub fn sexp_to_string_benchmark(c: &mut Criterion) {
    let sexp_str =
        fs::read_to_string("tests/issue_5_model.sexp").expect("could not open sexp file");
    let s = sexp::parse(&sexp_str).expect("could not parse sexp");
    c.bench_function("sexp::ToString", |b| b.iter(|| s.to_string()));
}

criterion_group!(benches, sexp_parse_benchmark, sexp_to_string_benchmark);
criterion_main!(benches);

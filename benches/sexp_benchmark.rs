use criterion::{criterion_group, criterion_main, Criterion, black_box};
use temporal_verifier::smtlib::sexp;

pub fn sexp_parse_benchmark(c: &mut Criterion) {
    let s = black_box(
        "(and (= (k!1058 x!0) node!val!13)
             (= x!1 quorum!val!2)
             (not (= x!1 quorum!val!4))
             (not (= x!1 quorum!val!5)))",
    );
    c.bench_function("sexp::parse", |b| b.iter(|| sexp::parse(s)));
}

pub fn sexp_to_string_benchmark(c: &mut Criterion) {
    let s = sexp::parse(
        "(and (= (k!1058 x!0) node!val!13)
             (= x!1 quorum!val!2)
             (not (= x!1 quorum!val!4))
             (not (= x!1 quorum!val!5)))",
    )
    .unwrap();
    c.bench_function("sexp::ToString", |b| b.iter(|| s.to_string()));
}

criterion_group!(benches, sexp_parse_benchmark, sexp_to_string_benchmark);
criterion_main!(benches);

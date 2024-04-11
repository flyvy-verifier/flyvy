# Run flyvy benchmarks over examples

The `benchmark` binary implements configuration for running benchmark suites
over the examples in `temporal-verifier/examples` and recording output and
timing results. Use `--help` (including with each subcommand) to get info on
parameters.

## qalpha invariant inference

Run `temporal-verifier infer qalpha` with a hand-written configuration per
example. Records the full output of each run, as well as timing info. To
configure this benchmark edit [qalpha.rs](src/qalpha.rs).

Benchmark identifiers have the form `[fragment]/[category]/[filename]/[experiment-type]`,
and can be filtered using the `-F` option. For example, this runs the `fixpoint` experiments
in the `small` category and `epr` fragment, and should only take a few minutes.

```sh
cargo run --bin benchmark -- qalpha --dir qalpha-results -F "**/epr/small/**/fixpoint"
```

Loading and printing the saved results can then be done using `--load`:

```sh
cargo run --bin benchmark -- qalpha --dir qalpha-results --load
```

Add `--tsv <filename>` to save the printed table to a TSV file.

## Verification

Run `temporal-verifier verify` over all the examples.

```sh
cargo run --bin benchmark -- verify --time-limit 60s
```

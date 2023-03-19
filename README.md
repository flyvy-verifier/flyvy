# Temporal Verifier

[![CI](https://github.com/vmware-research/temporal-verifier/actions/workflows/build.yml/badge.svg)](https://github.com/vmware-research/temporal-verifier/actions/workflows/build.yml)

## Overview

An experimental framework for temporal verification based on
first-order linear-time temporal logic. Our goal is to express
transition systems in first-order logic and verify temporal
correctness properties, including safety and liveness.

## Try it out

Run `./tools/download-solvers.sh` to get compatible versions of the supported SMT solvers (Z3, CVC5, and CVC4).

```sh
cargo run -- verify examples/lockserver.fly`

cargo run -- infer examples/lockserver.fly --quantifier "F node n1 n2" --kpdnf-lit 3

env RUST_LOG=info cargo run --release -- \
  infer examples/consensus_epr.fly --time \
  --quantifier "E quorum q" --quantifier "F node n1 n2 n3" --quantifier "F value v" \
  --kpdnf-lit 3
# note: this last example takes about two minutes to run
```

### Prerequisites

You'll need Rust (for example, through `rustup`) and recent versions of [Z3](https://github.com/Z3Prover/z3), [CVC4](https://cvc4.github.io/), and [cvc5](https://cvc5.github.io/).

### Build & Run

1. `cargo build`
2. `cargo test` to run tests
3. `cargo run -- verify <file.fly>` will run the verifier on an input file

You can run `cargo bench` to run the performance benchmarks.

For debug logging, we use the
[env_logger](https://docs.rs/env_logger/latest/env_logger/) crate, which uses
the `RUST_LOG` environment variable to configure logging. For example, to get
info-level messages run with `env RUST_LOG=info cargo run -- ...`.

## Documentation

Run `cargo doc` to generate the low-level API documentation. Currently there
isn't much documentation for the language itself, but you can look at the
examples under `examples/`.

## Contributing

The temporal-verifier project team welcomes contributions from the community. Before you start working with temporal-verifier, please
read our [Developer Certificate of Origin](https://cla.vmware.com/dco). All contributions to this repository must be
signed as described on that page. Your signature certifies that you wrote the patch or have the right to pass it on
as an open-source patch. For more detailed information, refer to [CONTRIBUTING.md](CONTRIBUTING.md).

## License

Copyright 2022-2023 VMware, Inc.

SPDX-License-Identifier: BSD-2-Clause

See [NOTICE](NOTICE) and [LICENSE](LICENSE).

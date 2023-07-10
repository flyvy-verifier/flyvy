# Example tests

The files in this directory serve as tests for the whole language.

There are two configuration modes for tests: lines within an input file starting
with `# TEST`, and a TOML file that configures a whole directory (though not
recursively). Each input file can be tested multiple times (for example, to vary
command line arguments), and these tests can come from a mix of `# TEST` lines
and TOML files.

For example, we can test that verification fails on a single file with CVC5 by
adding a line:

```
# TEST --expect-fail verify --solver=cvc5
```

Note that `--expect-fail` is an option for the testing infrastructure itself,
whereas after the `--` are arguments for the `temporal-verifier` binary.

Similarly, we could configure the same test for a whole directory by adding a
`tests.toml` file with the following:

```
[[tests]]
expect_fail = true
args = ["verify", "--solver=cvc5"]
```

Both forms of configuration support multiple tests, either with multiple `#
TEST` lines or with multiple configurations in the `[[tests]]` array.

The complete configuration options for an individual test are best understood by
reading the [`TestCfg`](../tests/test_examples.rs) struct.

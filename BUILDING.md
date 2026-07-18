# Building

Requires Lean 4 (the toolchain pinned in `lean-toolchain`, installed via
[elan](https://github.com/leanprover/elan)). No other dependencies — the library
uses only Lean core and `Std`, not Mathlib.

## Verify the proofs

```bash
lake build
```

On a memory-constrained machine, cap the workers: `taskset -c 0-1 lake build`
(one core is roughly one Lean worker at ~3 GB).

## Build the CLI

```bash
lake build haxpipeT     # binary: .lake/build/bin/haxpipeT
```

## Build the JSON parser suite

```bash
lake build HaxLean.Json.All     # forces the whole verified-parser suite (CI rot-guard)
```

## Run the tests

```bash
bash tests/run_tests.sh     # integration tests; skipped without a hax JSON fixture
```

## Reproduce the axiom ledger

```bash
lake env lean AxiomAudit.lean     # prints the axioms each pipeline capstone depends on
```

## Generate the API documentation (docgen4)

```bash
lake -R -Kenv=doc update
lake -R -Kenv=doc build HaxLean:docs     # output under .lake/build/doc/ (open index.html)
```

For running the CLI on a hax JSON dump, see the README.

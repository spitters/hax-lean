# Verification Status

All 5 phases of the hax core lowering pipeline are formalized in Lean 4,
with machine-checked correctness proofs. The project builds with `0 sorry`
and `0 axiom`, no Mathlib dependency.

## Typed pipeline (primary interface)

`haxpipeT` runs the typed pipeline on hax JSON AST dumps.
[`Hax/TPipeline.lean`](../Hax/TPipeline.lean) defines

```lean
tPipeline    : TExpr → TExpr      -- core 4 phases
tPipelineExt : TExpr → TExpr      -- + explicitMonadic (phase 5)
```

and its properties:

| Theorem                          | Statement                                          |
|----------------------------------|----------------------------------------------------|
| `tPipeline_erase`                | `(tPipeline e).erase = pipeline e.erase`           |
| `tPipelineExt_erase`             | `(tPipelineExt e).erase = pipelineExt e.erase`     |
| `tPipeline_fullyFunctional`      | `TFullyFunctional (tPipeline e)`                   |
| `tPipelineExt_fullyFunctional`   | `TFullyFunctional (tPipelineExt e)`                |

Semantic correctness is inherited from the untyped pipeline via the
`erase` equations.

## Untyped pipeline (semantic foundation)

[`Hax/Pipeline.lean`](../Hax/Pipeline.lean) and
[`Hax/PipelineCF.lean`](../Hax/PipelineCF.lean) carry the correctness
proofs that the typed layer reduces to:

| Theorem                       | Statement                                                       |
|-------------------------------|-----------------------------------------------------------------|
| `pipeline_fullyFunctional`    | `FullyFunctional (pipeline e)`                                  |
| `pipeline_correct`            | `denote (pipeline e) = denote e` (fuel-bounded, well-scoped)    |
| `pipeline_full_correct`       | untyped pipeline preserves `denote'` (ControlFlow-aware)         |
| `pipelineExt_full_correct`    | end-to-end over all 5 phases including `explicitMonadic`         |

The `CF` variants handle Rust's `core::ops::ControlFlow` encoding
(`Break`/`Continue` wrapping) in the semantics.

## Phase files

| Phase | Untyped                                 | CF variant                               | Typed                                  |
|-------|-----------------------------------------|------------------------------------------|----------------------------------------|
| 1     | `Phase/DropReferences.lean`             | —                                        | `TPhase/DropReferences.lean`           |
| 2     | `Phase/LocalMutation.lean`              | —                                        | `TPhase/LocalMutation.lean`            |
| 3     | `Phase/FunctionalizeLoops.lean`         | `Phase/FunctionalizeLoopsCF.lean`        | `TPhase/FunctionalizeLoops.lean`       |
| 4     | `Phase/CfIntoMonads.lean`               | `Phase/CfIntoMonadsCF.lean`              | `TPhase/CfIntoMonads.lean`             |
| 5     | `Phase/ExplicitMonadic.lean`            | `Phase/ExplicitMonadicCF.lean`           | `TPhase/ExplicitMonadic.lean`          |

Phases 1–2 do not need a CF variant.

## Preconditions

The correctness theorem requires three input well-scopedness properties:

| Precondition          | Meaning                                  |
|----------------------|------------------------------------------|
| `LoopScoped e`       | `break`/`continue` only inside loops     |
| `NoQuestionMark e`   | no `?` operator (handled pre-pipeline)   |
| `NoCFConstructors e` | no `cfBreak`/`cfContinue` in input       |

These hold for all well-formed hax output.

## Trusted components

| Component             | Role                                          |
|----------------------|-----------------------------------------------|
| `HaxAdapter.lean`    | Parses hax JSON → AST (~650 LOC, no proof)    |
| `Json.lean`          | JSON round-trip not formally proved           |
| `PrettyPrint{T}.lean`| AST → Lean 4 source; no preservation proof    |
| `Runtime.lean`       | Implements `denote'`; no linking proof        |
| Lean 4 compiler      | Assumed correct                               |

This matches CompCert's structure: the AST-to-AST transformation is proved;
the parser/printer/runtime form the TCB.

## Known limitations

- **Expression-level only** — no recursive functions, modules, or item-level
  structure.
- **Fuel-bounded semantics** — non-termination is not modeled.
- **Closures approximated** — bodies are not represented (mapped to
  `app "__closure"`).
- **Generics** — complex types map to `.unknown` escape hatch.
- **Traits** — no dispatch; trait methods are unresolved function names.
- **Runtime folds are `partial`** — `Hax.forFold` / `Hax.whileFold` use
  `partial def` (standard for general recursion).

## Statistics

- **38 files** under `Hax/`, ~22 975 lines of Lean 4
- **0 sorries, 0 axioms**
- **0 Mathlib dependency**

## Build

```bash
lake build               # verify proofs
lake build haxpipeT      # build the CLI
bash tests/run_tests.sh  # integration tests
```

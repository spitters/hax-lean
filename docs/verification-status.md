# Verification Status

The hax core lowering pipeline is formalized in Lean 4 as a typed,
syntax-directed AST-to-AST transformation (`TExpr → TExpr`). Each phase
carries machine-checked `_erase` (commutes with `TExpr.erase`) and `_ty`
(preserves the type projection) theorems. Semantic preservation is
inherited from the untyped layer through the `_erase` equations — there
is no independent typed denotation `TExpr → Value`, which keeps the
typed layer slim at the cost of having the untyped `denote` in the TCB
chain for any typed semantic claim.

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

The core lowering chain (per-phase, untyped and typed variants):

| Phase | Untyped                                 | CF variant                               | Typed                                  |
|-------|-----------------------------------------|------------------------------------------|----------------------------------------|
| 1     | `Phase/DropReferences.lean`             | —                                        | `TPhase/DropReferences.lean`           |
| 2     | `Phase/LocalMutation.lean`              | —                                        | `TPhase/LocalMutation.lean`            |
| 3     | `Phase/FunctionalizeLoops.lean`         | `Phase/FunctionalizeLoopsCF.lean`        | `TPhase/FunctionalizeLoops.lean`       |
| 4     | `Phase/CfIntoMonads.lean`               | `Phase/CfIntoMonadsCF.lean`              | `TPhase/CfIntoMonads.lean`             |
| 5     | `Phase/ExplicitMonadic.lean`            | `Phase/ExplicitMonadicCF.lean`           | `TPhase/ExplicitMonadic.lean`          |

Phases 1–2 do not need a CF variant.

Additional verified phases (typed layer, post-pipeline normalisations
and render-shaping rewrites):

`TPhase/WrapMatchArms`, `TPhase/AnnotateLets`, `TPhase/ElideNewtypeProj`,
`TPhase/FlattenLetFoldReturn`, `TPhase/RewriteAppName`,
`TPhase/RewriteNewToStructCtor`, `TPhase/RewriteStructFromElem`,
`TPhase/FixProjectionPaths`, `TPhase/QualifyProjections`,
`TPhase/InitFoldAccums`, `TPhase/StructMetaT`.

The corresponding untyped versions (`Phase/RewriteAppName`,
`Phase/InitFoldAccums`, `Phase/WrapMatchArms`) carry the matching
correctness theorems the typed `_erase` proofs reduce to.

`tFlattenLetFoldReturn` is a render-time normalisation; its correctness
relies on a `"_"` not-free-in invariant discussed in
`Hax/TPhase/FlattenLetFoldReturn.lean` and is outside the verified-core
diagram for that reason.

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
|-----------------------|-----------------------------------------------|
| `Json/Parser.lean`    | **Verified.** RFC 8259-conformant JSON parser, replaces `Lean.Json.parse` via `Json.parseVerified`. |
| `HaxAdapter.lean`     | Parses hax JSON → AST (~650 LOC). Trusted at the top level. Companion `AdapterRefinement.lean` (~7800 LOC) proves per-constructor refinement (`JsonRefinesExpr`, ~30 theorems including the `reconstructForLoops` preservation cases); the end-to-end `parseHaxExpr_refines` is documented TODO, blocked on `partial def` equational lemmas and a JSON-size termination measure. |
| `PrettyPrint{T}.lean` | AST → Lean 4 source; no preservation proof. |
| `Runtime.lean`        | Implements `denote'`; declares two intentional interface axioms (`bridgeCast`, `sha256`) that the CatCrypt-side bridge instantiates. No linking proof. |
| Lean 4 compiler       | Assumed correct.                              |

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

## Build

```bash
lake build               # verify proofs
lake build haxpipeT      # build the CLI
bash tests/run_tests.sh  # integration tests
```

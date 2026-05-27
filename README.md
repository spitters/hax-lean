# Verified Hax Pipeline in Lean 4

Formal verification of the [hax](https://github.com/hacspec/hax) compiler
phases that lower a Rust subset into a purely functional form, together
with the `haxpipeT` CLI that drives the pipeline on hax JSON dumps.

The pipeline is a typed, syntax-directed AST-to-AST transformation
(`TExpr → TExpr`) with three layered guarantees per phase:

1. **Feature elimination** — the phase removes certain AST constructors
2. **Preservation** — the phase does not re-introduce constructors removed earlier
3. **Semantics preservation** — the untyped erase commutes with the phase,
   so big-step denotation is preserved (via the proved untyped layer)

## Pipeline

```
TExpr
  ──[tDropReferences]──────→  TExpr  (no borrows / derefs)
  ──[tLocalMutation]───────→  TExpr  (no mutable assigns)
  ──[tFunctionalizeLoops]──→  TExpr  (no for / while / break / continue)
  ──[tCfIntoMonads]────────→  TExpr  (no early return / ?)
  ──[tWrapMatchArms]───────→  TExpr  (Rust fall-through-as-continue)
  ──[tExplicitMonadic]─────→  TExpr  (explicit monadic lowering)
  ──[tAnnotateLetBindings]─→  TExpr  (let-RHS type markers)
  ──[tElideToNamedProj]────→  TExpr  (newtype projection elision)
  ──[tFlattenLetFoldReturn]→  TExpr  (post-pipeline render normalisation)
```

The core four phases (`tDropReferences` … `tCfIntoMonads`) carry
machine-checked `_erase` and `_ty` preservation theorems. The
post-pipeline rewrites (`tWrapMatchArmsCF`, `tElideToNamedProj`,
`tFlattenLetFoldReturn`) are denotation-identity at the AST level; one
(`tFlattenLetFoldReturn`) is a render-time normalisation whose
correctness rests on a `"_"` not-free-in invariant discussed in the
phase file.

## Verified properties

The typed layer has two kinds of per-phase theorems: `_erase` (commutes
with `TExpr.erase`) and `_ty` (preserves the type projection). Semantic
preservation is inherited from the untyped layer through the `_erase`
equations — there is no independent typed denotation `TExpr → Value`.
This keeps the typed layer slim at the cost of having the untyped
`denote` in the TCB chain for any typed semantic claim.

| Theorem                          | Statement                                          |
|----------------------------------|----------------------------------------------------|
| `tPipeline_erase`                | `(tPipeline e).erase = pipeline e.erase`           |
| `tPipelineExt_erase`             | `(tPipelineExt e).erase = pipelineExt e.erase`     |
| `tPipeline_fullyFunctional`      | `TFullyFunctional (tPipeline e)`                   |
| `tPipelineExt_fullyFunctional`   | `TFullyFunctional (tPipelineExt e)`                |

Untyped-layer correctness (the foundation the typed `_erase` equations
reduce to):

| Theorem                       | Statement                                                       |
|-------------------------------|-----------------------------------------------------------------|
| `pipeline_correct`            | `denote (pipeline e) = denote e` (fuel-bounded, well-scoped)    |
| `pipeline_full_correct`       | untyped pipeline preserves `denote'` (ControlFlow-aware)        |
| `pipelineExt_full_correct`    | end-to-end over all 5 phases including `explicitMonadic`        |
| `pipelineToRawCode_noOracleCall` | translated free-monad output contains no oracle calls        |

## File layout

```
Hax.lean                             # root import (typed + untyped)
Hax/
├── AST.lean                         # ImpExpr: untyped imperative AST
├── TExpr.lean                       # typed expression AST
├── ImpType.lean                     # type language for typed AST
├── Value.lean                       # runtime values
├── Features.lean / TFeatures.lean   # feature predicates (untyped / typed)
├── FreeVars.lean                    # free-variable analysis
├── Semantics.lean / SemanticsCF.lean# fuel-bounded big-step (with / without CF)
├── Runtime.lean / RuntimeCorrectness.lean  # width-aware builtins + proofs
├── Json/                            # verified RFC 8259 JSON parser
│   ├── Lexer.lean
│   ├── Parser.lean
│   └── Adapter.lean
├── HaxAdapter.lean                  # hax-JSON → AST
├── AdapterRefinement.lean           # per-constructor refinement proofs (~7800 LOC)
├── Canonicalize.lean                # AST canonicalisation
├── Phase/                           # untyped verified phases
│   ├── DropReferences / LocalMutation / FunctionalizeLoops(CF)
│   ├── CfIntoMonads(CF) / ExplicitMonadic(CF)
│   └── RewriteAppName / InitFoldAccums / WrapMatchArms
├── TPhase/                          # typed verified phases (16 files)
│   ├── DropReferences / LocalMutation / FunctionalizeLoops / CfIntoMonads
│   ├── WrapMatchArms / ExplicitMonadic / AnnotateLets
│   ├── ElideNewtypeProj / FlattenLetFoldReturn
│   ├── RewriteAppName / RewriteNewToStructCtor / RewriteStructFromElem
│   ├── FixProjectionPaths / QualifyProjections
│   ├── InitFoldAccums / StructMetaT
├── Pipeline.lean / PipelineCF.lean  # untyped pipeline + correctness
├── TPipeline.lean                   # typed pipeline + commuting diagrams
├── ToRawCode.lean                   # translation to free-monad RawCode
├── PrettyPrint.lean / PrettyPrintT.lean  # AST → Lean source (trusted)
├── CLI.lean / MainT.lean            # haxpipeT entry point
└── Deep/RawCode.lean                # minimal RawCode stub (ret/bind/fail)
```

## Building

```bash
lake build              # verify the proofs
lake build haxpipeT     # build the CLI: .lake/build/bin/haxpipeT
bash tests/run_tests.sh # integration tests (skipped if no hax JSON fixture)
```

## Running the CLI

`haxpipeT` reads a hax JSON dump (produced by `cargo hax json` from the
[hax](https://github.com/hacspec/hax) toolchain) and emits Lean 4
source via the typed pipeline.

| Flag | Output |
|------|--------|
| `--emit-certified --hax` | Typed extraction: surface code plus post-pipeline `ImpExpr` literals, with hax JSON types preserved end-to-end. **The production path.** |
| `--emit-json`            | Transformed `ImpExpr` AST as JSON (debug / inspection). |
| `--emit-debug-meta`      | Debug metadata about hax types and struct layouts. |

```bash
haxpipeT --hax INPUT.json --emit-certified --name MyModule -o out.lean
```

Generated Lean files compile standalone against this repo's `Hax.*`
modules.

The untyped emit paths (`--emit-lean`, `--emit-certified` without
`--hax`, `--emit-bridge`) are deprecated and emit a runtime warning;
they remain only to support legacy tests and the dropped `HaxBridge.lean`
template. See `Hax/PrettyPrint.lean`'s module docstring for the removal
plan.

## Trusted vs. verified

The pipeline follows CompCert-style TCB minimisation: the AST-to-AST
transformations are proved; the I/O ring around them is trusted.

| Component             | Status                                          |
|-----------------------|-------------------------------------------------|
| `TPhase/*`, `Phase/*` | **Verified.** `_erase` / `_ty` / `*_correct`.   |
| `TPipeline`, `Pipeline` | **Verified.** Composition + correctness.      |
| `Json/Parser.lean`    | **Verified.** RFC 8259 conformance.             |
| `HaxAdapter.lean`     | Trusted *at the top level*. Companion `AdapterRefinement.lean` proves per-constructor JSON-to-AST refinement (`JsonRefinesExpr`, ~30 theorems including the `reconstructForLoops` preservation cases); the end-to-end `parseHaxExpr_refines` is documented TODO, blocked on `partial def` equational lemmas and a JSON-size termination measure. |
| `PrettyPrint{T}.lean` | Trusted. AST → Lean source. No preservation proof. |
| `Runtime.lean`        | Trusted. Width-aware builtins; declares two intentional interface axioms (`bridgeCast`, `sha256`) that the CatCrypt-side bridge instantiates. |
| Lean 4 compiler       | Assumed correct.                                |

## Known limitations

- **Expression-level only** — no recursive functions, modules, or item-level structure
- **Fuel-bounded semantics** — non-termination is not modeled
- **Closures approximated** — bodies mapped to `app "__closure"`
- **Generics** — complex types fall back to `.unknown`
- **Traits** — no dispatch; trait methods are unresolved function names
- **Runtime folds are `partial`** — `Hax.forFold` / `Hax.whileFold` use `partial def`

## Relationship to CatCrypt

`Hax/Deep/RawCode.lean` is a minimal extract of CatCrypt's free-monad deep
embedding (ret / bind / fail). In CatCrypt, `toRawCode` connects to
game-based cryptographic proofs via that deep embedding, and the
typed-pipeline output drops directly into the `SurfaceDeps.lean` extraction
bridge.

## License

MIT — see [LICENSE](LICENSE).

# Verified Hax Pipeline in Lean 4

Formal verification of the [hax](https://github.com/hacspec/hax) compiler phases
that lower a Rust subset to a purely functional form, with the `haxpipeT` CLI that
drives the pipeline on hax JSON dumps. It is a verified counterpart to part of the
[hax](https://github.com/hacspec/hax) and
[Aeneas](https://github.com/AeneasVerif/aeneas) Rust-to-functional pipelines.

> 🚧 **Under construction — experimental research prototype.** Interfaces, proofs,
> and the emitted surface are evolving, and breaking changes are expected.

## Three roles of a cryptographic spec

A `haxpipeT` extraction serves three roles at once. Each consumes a different
aspect of the same crate, and each feeds the **CatCrypt** compiler and proof
stack.

**Role 1 — compiler front-end source.** The certified extraction carries the
function body as an `ImpExpr` AST literal, which the CatCrypt compiler lowers to
owned x86/ARM/RISC-V bytes. Two source-declared aspects travel with the body:

- **Information flow / constant-time.** Each certified function emits a
  `<name>_secrecy : List String` table — the bindings whose Rust type is a secret
  newtype (an integer whose only escape is `.declassify()`, or a secret buffer or
  scalar), recognized by `secrecyOfBindings` (which sees through `[U8; n]` and
  `&[U8]` buffers). The CatCrypt constant-time gate reads that list and rejects
  data-dependent use of a secret, so the source's secret/public distinction
  survives extraction rather than being erased at the integer boundary.
- **Prime-IR.** A trait surface (`Field` / `ModArith` / `EcGroup`) names each
  field, modular, and elliptic-curve operation after the arithmetic op-family it
  denotes. The CatCrypt compiler recognizes those calls by name and ties each to
  its dialect operation (`Field::mul` to `ZMod p` multiplication, and so on); a
  source-declared modulus (a `pub const`) travels through and is reconstructed
  downstream, so the prime is derived from the source rather than trusted. The
  traits compile unchanged with `rustc`.

**Role 2 — crypto-proof anchor.** The extraction's typeclass surface (`<X>Deps`)
wires into an abstract CatCrypt security proof, which consumes the protocol shape
and leaves the primitive opaque.

Explicit value-agreement ties join Roles 1 and 2: the primitive the security
proof leaves opaque is proven equal to the value the compiler emits, so the
guarantee holds of the compiled implementation.

**Role 3 — independent validation.** The crate's own functions run against
published test vectors (RFC/NIST) — an evidence base for the realization,
disjoint from the Lean side.

## Backends and refinement

The verified core is the imperative pipeline. Each pass carries a machine-checked
`denote`-preservation proof, the typed layer adds an `_erase` refinement, and the
passes compose end-to-end (`pipeline_correct`, `pipelineExt_full_correct`). The
input IR is imperative (`ImpExpr`, typed as `TExpr` — references, mutable
assignment, `for`/`while` loops, `break`/`continue`/`return`); the pipeline
eliminates every imperative feature while preserving `denote`, landing in the
`FullyFunctional` fragment of `ImpExpr` under the same `denote`.
`TPhase/EncodeControlFlow.lean` relates imperative loops to the runtime folds the
pretty-printer emits.

This repo builds no functional deep-embedding backend. CatCrypt supplies the
functional form over emitted code through verified `RawCode` reflection (`rawCode%`
/ `SPComp` quoting), with proved faithfulness (`RawCode.eval (rawCode% c) = c`),
and supplies the imperative→functional abstraction downstream (`ascend` / `Corres`
over `LowCT` / `semScalar`). The refinement endpoint follows *The Last Yard* (IACR
ePrint [2023/185](https://eprint.iacr.org/2023/185)) and the multi-backend hax
methodology (IACR ePrint [2025/980](https://eprint.iacr.org/2025/980)).

## Pipeline design

The pipeline is a typed, syntax-directed AST-to-AST transformation (`TExpr →
TExpr`) with three layered guarantees per phase:

1. **Feature elimination** — the phase removes certain AST constructors.
2. **Preservation** — the phase does not re-introduce constructors removed
   earlier.
3. **Semantics preservation** — the untyped `erase` commutes with the phase, so
   big-step denotation is preserved through the proved untyped layer.

The phase decomposition mirrors §3 of the hax paper (Bhargavan, Buyse,
Franceschino, Hansen, Kiefer, Schneider-Bensch, Spitters, IACR ePrint
[2025/142](https://eprint.iacr.org/2025/142)). Two pre-pipeline passes normalize
the input, four core phases eliminate the imperative features, and post-pipeline
passes encode loop control-flow and normalize for rendering:

```
pre-pipeline
  ──[tLowerClosureCalls]───→  TExpr  (inline let-bound local closures)
  ──[tThreadMut]───────────→  TExpr  (thread mutations across if-statement joins)

core phases
  ──[tDropReferences]──────→  TExpr  (no borrows / derefs)
  ──[tLocalMutation]───────→  TExpr  (no mutable assigns)
  ──[tFunctionalizeLoops]──→  TExpr  (no for / while / break / continue)
  ──[tCfIntoMonads]────────→  TExpr  (no early return / ?)

post-pipeline
  ──[tWrapMatchArmsCF]─────→  TExpr  (Rust fall-through-as-continue)
  ──[tExplicitMonadic]─────→  TExpr  (explicit monadic lowering)
  ──[tAnnotateLetBindings]─→  TExpr  (let-RHS type markers)
  ──[tElideToNamedProj]────→  TExpr  (newtype projection elision)
  ──[tEncodeControlFlow]───→  TExpr  (loop CF → ControlFlow-valued fold bodies)
  ──[tFlattenLetFoldReturn]→  TExpr  (render normalisation)
```

Loop control-flow — threading the loop's mutated accumulators and encoding
`break` / `continue` / `return` into the `ControlFlow`-valued fold bodies the
runtime expects — is a correct-by-construction transformation
(`TPhase/EncodeControlFlow.lean`), so the pretty-printer performs only a
structural emit. Every pass carries a machine-checked `_erase` refinement, and the
whole chain composes into a single commuting square (`TPipelineErase.lean`).

### Verified properties

The typed layer has two kinds of per-phase theorem: `_erase` (commutes with
`TExpr.erase`) and `_ty` (preserves the type projection). Semantic preservation is
inherited from the untyped layer through the `_erase` equations — there is no
independent typed denotation `TExpr → Value`, so the untyped `denote` stays in the
trust chain for any typed semantic claim.

| Theorem                          | Statement                                          |
|----------------------------------|----------------------------------------------------|
| `tPipeline_erase`                | `(tPipeline e).erase = pipeline e.erase`           |
| `tPipelineExt_erase`             | `(tPipelineExt e).erase = pipelineExt e.erase`     |
| `prePipeline_erase`              | pre-passes commute with `erase`                    |
| `tPipelineFull_eq_flatten_inner` | full chain (pre ∘ core ∘ post) as one commuting square |
| `tPipeline_fullyFunctional`      | `TFullyFunctional (tPipeline e)`                   |
| `tPipelineExt_fullyFunctional`   | `TFullyFunctional (tPipelineExt e)`                |

Untyped-layer correctness, the foundation the typed `_erase` equations reduce to:

| Theorem                       | Statement                                                       |
|-------------------------------|-----------------------------------------------------------------|
| `pipeline_correct`            | `denote (pipeline e) = denote e` (fuel-bounded, well-scoped)    |
| `pipeline_full_correct`       | untyped pipeline preserves `denote'` (ControlFlow-aware)        |
| `pipelineExt_full_correct`    | end-to-end over all 5 phases including `explicitMonadic`        |

## Running the CLI

`haxpipeT` reads a hax JSON dump (produced by `cargo hax json` from the
[hax](https://github.com/hacspec/hax) toolchain) and emits Lean 4 source via the
typed pipeline.

| Flag | Output |
|------|--------|
| `--emit-certified --hax` | Typed extraction: surface code plus post-pipeline `ImpExpr` literals, with hax JSON types preserved end-to-end. Each certified function also gets a sibling `<name>_lowct` def (`Option LowCT`) lowering its `ImpExpr` through CatCrypt's verified front (`haxToLowCT`), so the extraction is renderable as the reviewable kernel/orchestration surface the proofs consume. **The production path.** |
| `--emit-json`            | Transformed `ImpExpr` AST as JSON (debug / inspection). |
| `--emit-debug-meta`      | Debug metadata about hax types and struct layouts. |

```bash
haxpipeT --hax INPUT.json --emit-certified --name MyModule -o out.lean
```

Generated Lean files compile standalone against this repo's `HaxLean.*` modules,
which provide the `Hax.*` runtime namespace.

## File layout

```
HaxLean.lean                         # root import (typed + untyped)
HaxLean/
├── AST.lean                         # ImpExpr: untyped imperative AST (incl. first-class lam)
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
├── InlineClosures.lean / InlineClosuresErase.lean  # pre-pass: closure-as-value + erase
├── ThreadMutations.lean / ThreadMutationsErase.lean # pre-pass: if-join mutation + erase
├── Phase/                           # untyped verified phases
│   ├── DropReferences / LocalMutation / FunctionalizeLoops(CF)
│   ├── CfIntoMonads(CF) / ExplicitMonadic(CF)
│   └── RewriteAppName / InitFoldAccums / WrapMatchArms
├── TPhase/                          # typed verified phases
│   ├── DropReferences / LocalMutation / FunctionalizeLoops / CfIntoMonads
│   ├── WrapMatchArms / ExplicitMonadic / AnnotateLets
│   ├── ElideNewtypeProj / EncodeControlFlow / FlattenLetFoldReturn
│   ├── RewriteAppName / RewriteNewToStructCtor / RewriteStructFromElem
│   ├── FixProjectionPaths / QualifyProjections
│   ├── InitFoldAccums / StructMetaT
├── Pipeline.lean / PipelineCF.lean  # untyped pipeline + correctness
├── TPipeline.lean / TPipelineErase.lean  # typed pipeline + full-chain commuting square
├── PrettyPrint.lean / PrettyPrintT.lean  # AST → Lean source (structural emit, trusted)
└── CLI.lean / MainT.lean            # haxpipeT entry point
```

## Building

See [BUILDING.md](BUILDING.md) for building the proofs, the `haxpipeT` CLI, the
JSON suite, the tests, and the API docs. The trusted-vs-verified boundary is in
[TRUSTED_VS_VERIFIED.md](TRUSTED_VS_VERIFIED.md); known limitations are in
[LIMITATIONS.md](LIMITATIONS.md).

## Relationship to CatCrypt

CatCrypt's functional, proof-facing form is its own free-monad deep embedding
`RawCode` (with `SPComp` semantics), obtained by verified reflection (`rawCode%` /
`SPComp` quoting), not by a translation in this repo. The typed-pipeline output
drops directly into the `SurfaceDeps.lean` extraction bridge for game-based proofs.

The `_lowct` sibling defs (see the CLI table above) apply CatCrypt's front
`haxToLowCT : ImpExpr → Option LowCT` to the extracted `ImpExpr`. The two IRs play
complementary roles:

- **`ImpExpr`** is this pipeline's imperative *expression* AST — the working form
  of the phases and the handoff format of the extraction. (CatCrypt mirrors it as
  `CatCrypt.Hax.AST.ImpExpr`; the emitter's `ImpExpr` literals elaborate against
  that copy.)
- **`LowCT`** is CatCrypt's typed, low-level *constant-time command* IR over
  tower-field elements — branchless select, kernel-call ABIs, machine intrinsics,
  limb stores. It is the frontend IR of the CatCrypt compiler, whose verified
  backend lowers it to Jasmin / x86 — a compiler close in design to the one used
  in [AUCurves](https://github.com/AU-COBRA/AUCurves), from which `LowCT` and its
  `bedrockC` / `rust_cmd` command language are ported.

The map is partial: `ImpExpr` is expression-shaped while `LowCT` is
statement-shaped, so `haxToLowCT` is defined on the A-normal-form
("LowCT-representable") subset of `ImpExpr` and returns `none` elsewhere; its
domain is characterised decidably (`haxToLowCT_isSome_iff_anf`). The connection is
semantic rather than syntactic: `haxToLowCT_simulates` establishes that the
`LowCT` command's `RustExec` execution agrees with the `ImpExpr` big-step `denote`
(structural cases closed; scalar/tower leaf-call cases in progress).

So `LowCT` is the imperative, machine-facing target of an `ImpExpr`; its
functional, proof-facing counterpart is CatCrypt's `RawCode`.

## Upstream & related

- **hax** — the upstream Rust extraction toolchain this project formalizes:
  <https://github.com/hacspec/hax>
- **hax paper** — Bhargavan, Buyse, Franceschino, Hansen, Kiefer,
  Schneider-Bensch, Spitters, *hax: Verifying Security-Critical Rust Software
  using Multiple Provers*, IACR ePrint 2025/142:
  <https://eprint.iacr.org/2025/142> (the pipeline is described in §3).
- **The Last Yard** — Haselwarter, Hvass, Hansen, Winterhalter, Hritcu, Spitters,
  *The Last Yard: Foundational End-to-End Verification of High-Speed
  Cryptography*, IACR ePrint 2023/185: <https://eprint.iacr.org/2023/185>
  (functional↔imperative refinement: Hacspec → SSProve → Jasmin).
- **hax methodology** — Bhargavan, Hansen, Kiefer, Schneider-Bensch, Spitters,
  *Formal Security and Functional Verification of Cryptographic Protocol
  Implementations in Rust*, IACR ePrint 2025/980:
  <https://eprint.iacr.org/2025/980> (multiple backends over one Rust source).
- **Aeneas** — a related Rust-to-functional verification toolchain:
  <https://github.com/AeneasVerif/aeneas>
- **AUCurves** — bedrock2 `bedrockC` / `rust_cmd` command IRs that inspired
  CatCrypt's `LowCT`: <https://github.com/AU-COBRA/AUCurves>

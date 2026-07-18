# Verified Hax Pipeline in Lean 4

Formal verification of the [hax](https://github.com/hacspec/hax) compiler
phases that lower a Rust subset into a purely functional form, together
with the `haxpipeT` CLI that drives the pipeline on hax JSON dumps.

> 🚧 **Under construction — experimental research prototype.** This project is an
> experiment in what a *verified* version of part of the
> [hax](https://github.com/hacspec/hax) and
> [Aeneas](https://github.com/AeneasVerif/aeneas) Rust-to-functional pipelines
> could look like. It is not a production tool; interfaces, proofs, and the
> emitted surface are still evolving, and breaking changes are expected.

The pipeline is a typed, syntax-directed AST-to-AST transformation
(`TExpr → TExpr`) with three layered guarantees per phase:

1. **Feature elimination** — the phase removes certain AST constructors
2. **Preservation** — the phase does not re-introduce constructors removed earlier
3. **Semantics preservation** — the untyped erase commutes with the phase,
   so big-step denotation is preserved (via the proved untyped layer)

## Pipeline

The phase decomposition mirrors the hax extraction pipeline described in §3 of
the hax paper (Bhargavan, Buyse, Franceschino, Hansen, Kiefer, Schneider-Bensch,
Spitters, *hax: Verifying Security-Critical Rust Software using Multiple
Provers*, IACR ePrint [2025/142](https://eprint.iacr.org/2025/142)).

Two verified pre-pipeline passes normalise the input, the four core phases
eliminate the imperative features, and verified post-pipeline passes encode loop
control-flow and normalise for rendering:

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
structural emit. Every pass carries a machine-checked `_erase` refinement, and
the whole chain — pre-passes, core phases, and post-pipeline passes — composes
into a single commuting square (`TPipelineErase.lean`).

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
| `prePipeline_erase`              | pre-passes commute with `erase`                    |
| `tPipelineFull_eq_flatten_inner` | full chain (pre ∘ core ∘ post) as one commuting square |
| `tPipeline_fullyFunctional`      | `TFullyFunctional (tPipeline e)`                   |
| `tPipelineExt_fullyFunctional`   | `TFullyFunctional (tPipelineExt e)`                |

Untyped-layer correctness (the foundation the typed `_erase` equations
reduce to):

| Theorem                       | Statement                                                       |
|-------------------------------|-----------------------------------------------------------------|
| `pipeline_correct`            | `denote (pipeline e) = denote e` (fuel-bounded, well-scoped)    |
| `pipeline_full_correct`       | untyped pipeline preserves `denote'` (ControlFlow-aware)        |
| `pipelineExt_full_correct`    | end-to-end over all 5 phases including `explicitMonadic`        |

## Backends and refinement

The **verified** core is the imperative pipeline: each pass carries a
machine-checked `denote`-preservation proof (and the typed layer an `_erase`
refinement), composed end-to-end (`pipeline_correct`, `pipelineExt_full_correct`).

- an **imperative** IR (`ImpExpr`, typed as `TExpr` — references, mutable
  assignment, `for` / `while` loops, `break` / `continue` / `return`). The pipeline
  eliminates every imperative feature, `denote`-preserving, landing in the
  `FullyFunctional` *fragment of `ImpExpr`* (still evaluated by the same `denote`).
  `TPhase/EncodeControlFlow.lean` additionally relates imperative loops to the
  runtime folds the pretty-printer emits.
- a **functional** deep embedding (`Deep/RawCode`, a `ret` / `bind` / `fail` free
  monad). **This edge is a direction, not a verified backend.** `ToRawCode.lean`'s
  translation is a lossy structural placeholder with *no* correctness proof (see
  its status note: it drops calls/variables/loop structure), and the real semantic
  `RawCode` (with `SPComp` semantics) lives in CatCrypt, not here.

The intended endpoint — a *proven* functional↔imperative refinement — follows the
design of *The Last Yard* (Haselwarter, Hvass, Hansen, Winterhalter, Hritcu,
Spitters, IACR ePrint [2023/185](https://eprint.iacr.org/2023/185)) and the
multi-backend hax methodology (Bhargavan, Hansen, Kiefer, Schneider-Bensch,
Spitters, IACR ePrint [2025/980](https://eprint.iacr.org/2025/980)). The verified
`imperative → clean functional model` abstraction of the pipeline output is
provided **downstream, in CatCrypt** (`ascend`/`Corres` over `LowCT`/`semScalar`),
not by `toRawCode`.

## File layout

```
Hax.lean                             # root import (typed + untyped)
Hax/
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
├── ToRawCode.lean                   # translation to free-monad RawCode
├── PrettyPrint.lean / PrettyPrintT.lean  # AST → Lean source (structural emit, trusted)
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
| `--emit-certified --hax` | Typed extraction: surface code plus post-pipeline `ImpExpr` literals, with hax JSON types preserved end-to-end. Each certified function also gets a sibling `<name>_lowct` def (`Option LowCT`) lowering its `ImpExpr` through CatCrypt's verified front (`haxToLowCT`), so the extraction is renderable as the reviewable kernel/orchestration surface the proofs consume. **The production path.** |
| `--emit-json`            | Transformed `ImpExpr` AST as JSON (debug / inspection). |
| `--emit-debug-meta`      | Debug metadata about hax types and struct layouts. |

```bash
haxpipeT --hax INPUT.json --emit-certified --name MyModule -o out.lean
```

Generated Lean files compile standalone against this repo's `Hax.*`
modules.

## Trusted vs. verified

The pipeline follows CompCert-style TCB minimisation: the AST-to-AST
transformations are proved; the I/O ring around them is trusted.

| Component             | Status                                          |
|-----------------------|-------------------------------------------------|
| `TPhase/*`, `Phase/*` | **Verified.** `_erase` / `_ty` / `*_correct`.   |
| `TPipeline`, `Pipeline`, `TPipelineErase` | **Verified.** Composition + full-chain commuting square. |
| `Json/*.lean` (verified-parser suite, forced into the build by `Json/All.lean`) | **Verified against RFC 8259, with documented scope limits.** The parser is pinned from *both* sides: soundness (`parse_sound`, a fuel-free relational grammar) and completeness (`parse_complete` over a tightened `ValuePStrict`), plus faithful rejection of the empty and trailing-comma streams. Number conformance §6 is general (`tokenize_accepts_number` / `tokenize_number_reject`, `∀`); string conformance §7/§8.2 has a general tokenize-acceptance capstone (`tokenize_string_singleton`, escaped bodies included) over the escape/surrogate validator lemmas. Roundtrip `tokenize (serialize j) >>= parse = .ok j` holds on the `null`/`bool`/`arr` fragment (nested induction), the integer-mantissa `num` fragment (`Int.toInt?_repr` inversion), and — since `Json.obj` stores a `Std.TreeMap.Raw` the parser rebuilds via `mkObj`, so structural equality is provably unattainable — the `obj` case **modulo canonicalisation**. Every module is `sorry`-free and axiom-clean (`propext`/`Classical.choice`/`Quot.sound`); totality (`parse_total`) and trailing-content rejection are also proved. Open: `num` beyond integer mantissa (serializer drops the exponent) and full escaped-string roundtrip. |
| `HaxAdapter.lean`     | Trusted *at the top level*. Companion `AdapterRefinement.lean` proves per-constructor JSON-to-AST refinement (`JsonRefinesExpr`, ~30 theorems including the `reconstructForLoops` preservation cases); the end-to-end `parseHaxExpr_refines` remains open, blocked on `partial def` equational lemmas and a JSON-size termination measure. |
| `PrettyPrint{T}.lean` | Trusted. AST → Lean source; a structural emit, since control-flow encoding is done by the verified `EncodeControlFlow` phase. No preservation proof. |
| `Runtime.lean`        | Trusted. Width-aware builtins; declares two intentional interface axioms (`bridgeCast`, `sha256`) that the CatCrypt-side bridge instantiates. |
| Lean 4 compiler       | Assumed correct.                                |

## Known limitations

- **Expression-level only** — no recursive functions, modules, or item-level structure
- **Fuel-bounded semantics** — non-termination is not modeled
- **Closures** — first-class `lam` values; local closure calls are inlined by the pre-pass, higher-order use is not otherwise resolved
- **Generics** — complex types fall back to `.unknown`
- **Traits** — no dispatch; trait methods are unresolved function names
- **Runtime folds are `partial`** — `Hax.forFold` / `Hax.whileFold` use `partial def`

## Relationship to CatCrypt

`Hax/Deep/RawCode.lean` is a minimal extract of CatCrypt's free-monad deep
embedding (ret / bind / fail). In CatCrypt, `toRawCode` connects to
game-based cryptographic proofs via that deep embedding, and the
typed-pipeline output drops directly into the `SurfaceDeps.lean` extraction
bridge.

### `ImpExpr` and `LowCT`

The `_lowct` sibling defs (see the CLI table above) apply CatCrypt's front
`haxToLowCT : ImpExpr → Option LowCT` to the extracted `ImpExpr`. The two IRs
play complementary roles:

- **`ImpExpr`** is this pipeline's imperative *expression* AST — the working
  form of the phases and the handoff format of the extraction. (CatCrypt mirrors
  it as `CatCrypt.Hax.AST.ImpExpr`; the emitter's `ImpExpr` literals elaborate
  against that copy.)
- **`LowCT`** is CatCrypt's typed, low-level *constant-time command* IR over
  tower-field elements — branchless select, kernel-call ABIs, machine
  intrinsics, limb stores. It is the **frontend IR of the CatCrypt compiler**,
  whose verified backend lowers it to Jasmin / x86 — a compiler close in design
  to the one used in [AUCurves](https://github.com/AU-COBRA/AUCurves), from which
  `LowCT` and its `bedrockC` / `rust_cmd` command language are ported.

The map is **partial**: `ImpExpr` is expression-shaped while `LowCT` is
statement-shaped, so `haxToLowCT` is defined on the A-normal-form
("LowCT-representable") subset of `ImpExpr` and returns `none` elsewhere; its
domain is characterised decidably (`haxToLowCT_isSome_iff_anf`). The connection
is **semantic**, not merely syntactic — `haxToLowCT_simulates` establishes that
the `LowCT` command's `RustExec` execution agrees with the `ImpExpr` big-step
`denote` (structural cases closed; scalar/tower leaf-call cases in progress).

So `LowCT` is the *imperative, machine-facing* target of an `ImpExpr` — the
counterpart to `RawCode`, its *functional, proof-facing* target — and both are
reached from the same extracted `ImpExpr`.

## Upstream & related

- **hax** — the upstream Rust extraction toolchain this project formalizes:
  <https://github.com/hacspec/hax>
- **hax paper** — Bhargavan, Buyse, Franceschino, Hansen, Kiefer,
  Schneider-Bensch, Spitters, *hax: Verifying Security-Critical Rust Software
  using Multiple Provers*, IACR ePrint 2025/142:
  <https://eprint.iacr.org/2025/142> (the pipeline is described in §3).
- **The Last Yard** — Haselwarter, Hvass, Hansen, Winterhalter, Hritcu,
  Spitters, *The Last Yard: Foundational End-to-End Verification of High-Speed
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

## License

MIT — see [LICENSE](LICENSE).

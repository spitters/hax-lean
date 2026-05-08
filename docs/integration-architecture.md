# Integration Architecture

How `hax-lean` relates to the upstream hax compiler and to downstream Lean
consumers.

## Repository Boundary

```
spitters/hax-lean (this repo)          cryspen/hax (upstream)
├── Verified 5-phase pipeline           ├── Rust engine (25+ phases)
├── Typed layer (TExpr, commuting)      ├── Lean 4 backend / printer
├── Runtime.lean                        ├── cargo hax CLI
├── haxpipeT CLI                        └── Phase pipeline (OCaml + Rust)
├── JSON adapter (HaxAdapter.lean)
└── Pretty-printer (PrettyPrint{T}.lean)
```

This repo is self-contained Lean 4. It does not depend on any hax Rust crate;
it consumes hax's JSON AST dumps and emits Lean 4 source.

## Pipeline Correspondence

The 5 verified phases line up 1-to-1 with hax's core lowering:

| Our phase                 | Hax phase                                    |
|--------------------------|----------------------------------------------|
| `dropReferences`         | `DropReferences`                             |
| `localMutation`          | `LocalMutation`                              |
| `functionalizeLoops`     | `FunctionalizeLoops`                         |
| `cfIntoMonads`           | `RewriteControlFlow` + `DropReturnBreakContinue` |
| `explicitMonadic`        | `ExplicitMonadic`                            |

Hax has ~11 pre-processing and ~10 post-processing phases on either side.
Those are syntactic rewrites (assert reconstruction, for/while recovery,
item sorting, etc.) that do not change evaluation semantics; they are
outside the verified core.

## Workflows

### Standalone extraction

Input is hax's JSON AST dump; output is Lean 4 source plus a deps class.

```bash
haxpipeT --emit-certified input.json --name my_fn -o out.lean
```

Generated files import `Hax.Runtime` and use the width-aware runtime
builtins. They compile standalone against this repo (no hax, no Mathlib).

### Translation validation

Given hax's pre- and post-lowering AST dumps, verify that hax's core
lowering is structurally equivalent to the verified pipeline:

```bash
haxpipeT --validate --pre pre.json --post post.json
```

The comparator runs `tPipeline` on `pre.json` and compares the erased
output with `post.json`. A mismatch flags a potential hax bug; a match is
a per-invocation certificate for the 5 core phases.

### Downstream deep embedding

`Hax/Deep/RawCode.lean` carries a minimal free-monad stub (`ret`/`bind`/`fail`).
Downstream projects can replace it with their own deep embedding; the
certified `tToRawCode` path lifts extracted code into that embedding with
a commuting-diagram correspondence.

## Trusted Computing Base

| Component                 | Role                             |
|---------------------------|----------------------------------|
| `HaxAdapter.lean`         | hax JSON → ImpExpr / TExpr       |
| `Json.lean`               | JSON (de)serialization           |
| `PrettyPrint{T}.lean`     | AST → Lean 4 source              |
| `Runtime.lean`            | Width-aware builtins             |
| Lean 4 compiler           | Compiles generated code          |

This matches the standard CompCert-style verified-core architecture: the
AST-to-AST transformation is proved; the parser, printer, and runtime
are the TCB.

## What NOT to do

- Do not add Lean proofs to the upstream hax repo — they are independent
  concerns. The coupling is the JSON interchange format, not code.
- Do not modify hax's phase implementations from this repo — we validate,
  not replace.
- Do not vendor `Runtime.lean` into hax — hax has its own
  `rust_primitives` library.

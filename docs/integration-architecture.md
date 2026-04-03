# Integration Architecture: Where Does What Live?

## Repository Boundary

```
spitters/hax-lean (this repo)          cryspen/hax (upstream)
├── Lean 4 verification               ├── Rust engine (25+ phases)
├── Runtime library                    ├── Lean 4 backend printer
├── haxpipe CLI                        ├── cargo hax CLI
├── JSON adapter (Lean-side)           └── Phase pipeline
└── Translation validator (Lean-side)
```

### What stays in `spitters/hax-lean`

Everything that IS Lean 4 or consumes hax output:

| Component | Purpose |
|-----------|---------|
| `CatCrypt/Hax/*.lean` | Verified pipeline, proofs, semantics |
| `CatCrypt/Hax/Runtime.lean` | Runtime for generated code |
| `CatCrypt/Hax/HaxAdapter.lean` | Parse hax's `Decorated<ExprKind>` JSON |
| `CatCrypt/Hax/Main.lean` | `haxpipe` CLI tool |
| Translation validator | Compare our pipeline output with hax's |
| CatCrypt backend | `toRawCode` and certified translation |

### What goes to `cryspen/hax` as a PR

The minimal hook to expose hax's intermediate ASTs:

| Component | Purpose | Where in hax |
|-----------|---------|-------------|
| `--dump-pre-lowering` flag | Serialize AST before core lowering | `engine/src/` |
| `--dump-post-lowering` flag | Serialize AST after core lowering | `engine/src/` |
| JSON schema for `Decorated<ExprKind>` | Stable interchange format | `engine/src/` |
| CI integration (optional) | Run translation validator on test suite | `.github/workflows/` |

The PR to hax should be small (~200 LOC Rust) — just two serialization
points in the phase pipeline, outputting the AST as JSON at the boundaries
between pre-processing ↔ core lowering ↔ post-processing.

## Integration Workflow

### For validation (primary use case)

```bash
# 1. Run hax, dumping intermediate ASTs
cargo hax into lean4 --dump-pre-lowering pre.json --dump-post-lowering post.json

# 2. Run our verified pipeline on the pre-lowering AST
haxpipe --hax --extended pre.json --validate post.json

# Output: PASS or FAIL with diff at first divergence
```

### For standalone use (no hax dependency)

```bash
# Run pipeline on hand-written or test JSON
echo '{"forLoop": ...}' | haxpipe --emit-lean --extended --name my_fn

# Generated code compiles with just Runtime.lean
lake env lean generated.lean
```

### For CatCrypt backend

```bash
# Parse hax output → run verified pipeline → produce RawCode
cargo hax into lean4 --dump-pre-lowering - | haxpipe --emit-rawcode
```

## Phased Integration Plan

### Phase 1: No hax changes needed (current state)

What works now:
- `haxpipe` reads ImpExpr JSON or hax's `Decorated<ExprKind>` format
- Runs verified 5-phase pipeline
- Outputs Lean 4 source or transformed JSON
- Generated code compiles with `import CatCrypt.Hax.Runtime`

This is sufficient for:
- Validating individual expressions manually
- Demonstrating the verified pipeline on examples
- Testing against hand-crafted hax JSON dumps

### Phase 2: hax PR for AST dump (~200 LOC Rust)

PR to `cryspen/hax`:
1. Add `--dump-lowering-ast` flag to the engine CLI
2. Serialize `Decorated<ExprKind>` to JSON at two points:
   - After pre-processing (before `DropReferences`)
   - After core lowering (after `FunctionalizeLoops`)
3. Use existing `serde_json` serialization (hax already has `Serialize` on its AST)

This enables automated translation validation.

### Phase 3: CI integration

Add to hax's CI:
1. Build `haxpipe` from `spitters/hax-lean`
2. For each test in `lean-tests/`:
   - Run `cargo hax into lean4 --dump-lowering-ast`
   - Run `haxpipe --hax --validate`
   - Report match/mismatch
3. Failures indicate either:
   - A bug in hax's lowering phases, or
   - A feature our pipeline doesn't model (closures, generics)

### Phase 4: CatCrypt certified backend

Extend `haxpipe` with `--emit-rawcode` that:
1. Parses hax AST
2. Runs `tPipeline` (typed, verified)
3. Applies `tToRawCode` → `RawCode Value`
4. Outputs CatCrypt-compatible Lean 4

## What NOT to Put in hax

- **Do not add Lean 4 verification code to hax** — it would be an unrelated dependency
- **Do not modify hax's phase implementations** — we validate, not replace
- **Do not add our Runtime.lean to hax** — hax has its own `rust_primitives` library
- The hax PR should be minimal: just expose what's already there via JSON serialization

## Dependency Diagram

```
cryspen/hax
  │
  │ (cargo hax --dump-lowering-ast)
  │ produces JSON
  ↓
spitters/hax-lean
  │
  ├── HaxAdapter.lean (parses JSON)
  ├── Pipeline + proofs (verified transformation)
  ├── PrettyPrint.lean (generates Lean 4)
  └── Runtime.lean (runtime for generated code)
       │
       ↓
  Generated Lean 4 code
  (standalone, no hax dependency)
```

The key principle: **hax produces, we consume**. The coupling is a JSON
interchange format, not a code dependency.

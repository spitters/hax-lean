# Integration Plan: Verified Hax Pipeline (Revised)

## What Changed Since v1

1. **Typed layer implemented**: `TExpr`/`ImpType` with commuting diagrams — all 4 phases lift to typed expressions
2. **Hax uses a Rust engine for Lean 4**: The Lean backend runs in `rust-engine/`, not OCaml. It applies **25+ phases** (not 12)
3. **Hax's output IS our pipeline's output**: The generated Lean 4 code uses `rust_primitives.hax.for_loop`, double-wrapped `ControlFlow.Break`, and `ControlFlow.Break` for early returns — structurally identical to what our `functionalizeLoops` + `cfIntoMonads` produce
4. **Option C (full replacement) is not realistic**: Hax's AST has closures, generics, trait bounds, associated types, monadic encoding, and 20+ phases beyond our 4. Replacing the engine is a multi-year effort with diminishing returns

## Architecture Comparison

### Hax's Lean 4 Backend Pipeline (25+ phases)
```
Rust Source
  → Frontend: extract THIR → .haxmeta
  → Rust Engine phases:
      Pre-processing (11 phases):
        RejectRawOrMutPointer, Specialize, DropSizedTrait,
        SimplifyQuestionMarks, ReconstructAsserts,
        ReconstructForLoops, ReconstructWhileLoops,
        DirectAndMut, RejectArbitraryLhs, DropBlocks,
        DropMatchGuards
      Core lowering (4 phases):                    ← WE VERIFY THESE
        DropReferences, LocalMutation,
        RewriteControlFlow+DropReturnBreakContinue,
        FunctionalizeLoops
      Post-processing (10+ phases):
        HoistSideEffects, SimplifyMatchReturn,
        TraitsSpecs, NewtypeAsRefinement,
        SortItems, FilterUnprintableItems,
        ExplicitMonadic, RecursiveFunctions, LetPure
  → LeanPrinter: render AST → Lean 4 source code
```

### Our Verified Pipeline
```
TExpr
  → tDropReferences     (= hax DropReferences)
  → tLocalMutation      (= hax LocalMutation)
  → tFunctionalizeLoops (= hax FunctionalizeLoops)
  → tCfIntoMonads       (= hax RewriteControlFlow)
  → FullyFunctional TExpr

Verified: erase ∘ tPipeline = pipeline ∘ erase
Verified: pipeline preserves big-step semantics
```

### What Matches

| Our phase | Hax phase | Generated Lean 4 code |
|-----------|-----------|----------------------|
| `dropReferences` (borrow/deref → id) | `DropReferences` | References erased |
| `localMutation` (assign → letBind) | `LocalMutation` + `HoistSideEffects` | Pure let bindings |
| `functionalizeLoops` (for/while → fold) | `FunctionalizeLoops` | `rust_primitives.hax.for_loop (fun x i => ...)` |
| `cfIntoMonads` (earlyReturn → cfBreak) | `RewriteControlFlow` + `DropReturnBreakContinue` | `ControlFlow.Break(...)` |
| Nested encoding (break in earlyReturn loop) | Same double-wrapping | `ControlFlow.Break(ControlFlow.Break(...))` |

The structural correspondence is exact. Hax generates the same AST shapes our phases produce.

## Revised Strategy

### Drop Option C

Full engine replacement requires verifying 25+ phases, generics, traits, closures, and a full Lean 4 printer. The effort-to-impact ratio is poor — the pre/post-processing phases are mostly syntactic sugar transformations, not semantically critical.

### Primary: Translation Validation (Option A+)

**Goal**: Certify that hax's Rust engine produces correct output for the 4 core lowering phases, on every invocation.

```
                         Rust Source
                             │
                    ┌────────┴────────┐
                    ↓                  ↓
             hax frontend         hax frontend
                    ↓                  ↓
             pre-processing       pre-processing
              (11 phases)          (11 phases)
                    ↓                  ↓
              ┌─────┴─────┐     ┌─────┴─────┐
              │ hax core  │     │ our verified│
              │ lowering  │     │  pipeline   │
              │ (Rust)    │     │  (Lean 4)   │
              └─────┬─────┘     └─────┬─────┘
                    ↓                  ↓
              post-AST₁          post-AST₂
                    │                  │
                    └──── compare ─────┘
                              │
                         ✓ match → certified
                         ✗ mismatch → bug report
```

**Why this is the right approach**:
- We don't need to verify the pre/post-processing phases (they don't affect the core semantics)
- The 4 core phases are exactly where subtle bugs would hide (loop semantics, control flow encoding)
- Translation validation is standard in verified compilers (CompCert uses this approach for register allocation)
- No changes to hax's production pipeline needed

**Implementation**:

1. **Intercept the AST before and after core lowering** in hax's Rust engine
   - Add a `--dump-pre-lowering` / `--dump-post-lowering` flag
   - Or: hook into the phase pipeline to serialize the intermediate ASTs
   - Format: JSON with our `TExpr` schema

2. **Parse into `TExpr`** via `FromJson` instances
   - Map hax's expression constructors to `TExprKind`
   - Map hax's type representation to `ImpType`
   - Constructors we don't handle (closures, constructs, macros) map to `app` calls

3. **Run our verified `tPipeline`** on the pre-lowering AST

4. **Compare post-lowering ASTs** via erasure: `erase(hax_output) = erase(tPipeline(our_input))`
   - Comparison ignores types (via erasure) — only checks structural equivalence
   - This is sufficient because we've proved the untyped pipeline preserves semantics

5. **Report**: "Lowering certified correct" or "Mismatch at expression X — potential bug in hax"

### Secondary: Verified SSProve Backend

**Goal**: When targeting SSProve, use our pipeline directly instead of hax's, producing `RawCode` with a correctness certificate.

```
Rust Source
  → hax frontend → JSON AST
  → adapter: strip to TExpr
  → tPipeline (verified)
  → toRawCode (verified)
  → RawCode Value (SSProve deep embedding)
```

This is the most natural fit because:
- SSProve is already our target (`toRawCode` exists)
- The SSProve hax backend already skips some phases (e.g., `LocalMutation`)
- We can produce a correctness certificate alongside the `RawCode`

## Concrete Implementation Plan

### Step 1: JSON Serialization (~200 LOC)

New file: `SSProve/Hax/Json.lean`

```lean
import Lean.Data.Json
-- FromJson/ToJson for ImpType, TExpr, TExprKind, ImpPat, ImpLit
-- Round-trip theorem: fromJson(toJson(e)) = some e
```

This enables:
- Importing hax's AST dumps
- Exporting our pipeline's output for comparison
- Property-based testing via JSON round-trips

### Step 2: Hax AST Adapter (~300 LOC)

A small Rust crate (or Python script) that:
1. Takes hax's internal AST (from `--dump-pre-lowering`)
2. Maps it to our `TExpr` JSON schema:
   - `hax::Expr::If` → `TExprKind.ifThenElse`
   - `hax::Expr::Let` → `TExprKind.letBind`
   - `hax::Expr::App` → `TExprKind.app`
   - `hax::Expr::Loop` → `TExprKind.forLoop` / `TExprKind.whileLoop`
   - `hax::Expr::Return` → `TExprKind.earlyReturn`
   - `hax::Expr::Break` → `TExprKind.break_`
   - `hax::Expr::Borrow` → `TExprKind.borrow`
   - `hax::Expr::Assign` → `TExprKind.assign`
   - `hax::Expr::Closure` → `TExprKind.app "__closure"` (approximation)
   - `hax::Expr::Construct` → `TExprKind.app "Constructor"` (approximation)
3. Maps hax's type system to `ImpType`:
   - `TBool → .bool`, `TInt → .int`, `TStr → .str`
   - `TApp { ident, args }` → `.adt name (map args)`
   - `TRef { typ, mut }` → `.ref typ isMut`
   - `TArrow` → `.fn params ret`
   - `TParam` → `.typeVar name`
   - Unknown/complex → `.unknown`

### Step 3: Comparison Harness (~150 LOC Lean + ~100 LOC Rust)

A `lake exe` target that:
1. Reads pre-lowering AST JSON → parses to `TExpr`
2. Runs `tPipeline`
3. Reads post-lowering AST JSON → parses to `TExpr`
4. Compares `erase(tPipeline(input))` with `erase(hax_output)`
5. Reports match/mismatch with diff on first divergence

### Step 4: Hax Integration (~200 LOC Rust)

PR to `cryspen/hax`:
1. Add `--dump-lowering-ast` flag to `cargo hax`
2. Serialize pre/post-lowering AST to JSON at the phase boundaries
3. Add CI job: for each test case, run translation validator

### Step 5: SSProve Backend (~400 LOC Lean)

New files:
- `SSProve/Hax/TToRawCode.lean` — typed version of `toRawCode`
- Certified pipeline: `TExpr → tPipeline → tToRawCode → RawCode Value`
- Certificate type:
  ```lean
  structure CertifiedTranslation where
    input : TExpr
    output : RawCode Value
    proof : output = tToRawCode (tPipeline input)
  ```

## What We Don't Need to Do

| Task | Why not |
|------|---------|
| Verify pre-processing phases (11 phases) | Syntactic sugar; don't affect semantics of the 4 core lowering steps |
| Verify post-processing phases (10+ phases) | Monadic encoding, sorting, filtering — orthogonal to lowering correctness |
| Verify the Lean printer | It's a pretty-printer, not a transformation; bugs are immediately visible |
| Handle generics/traits in proofs | Type erasure handles this — our proofs are parametric over types |
| Replace hax's Rust engine | Too much effort for marginal benefit; translation validation gives the same assurance |
| Formalize the JSON parser | The parser is trusted (as in CompCert); the verified core is the pipeline |

## Effort Estimate

| Component | LOC | Effort |
|-----------|-----|--------|
| JSON serialization (Lean) | ~200 | 2-3 days |
| Hax AST adapter (Rust/Python) | ~300 | 3-4 days |
| Comparison harness | ~250 | 2-3 days |
| Hax PR (dump flag) | ~200 | 2-3 days |
| SSProve backend | ~400 | 1 week |
| **Total** | **~1,350** | **3-4 weeks** |

## Success Criteria

1. **Translation validator runs on hax's full test suite** (lean-tests, toolchain tests)
   - Expected: 100% match on expression-level programs
   - Some mismatches possible for features we approximate (closures, constructs)

2. **At least one real crate validated** (e.g., a libcrux module)

3. **PR accepted to hax** with `--dump-lowering-ast` flag

4. **SSProve backend produces certified `RawCode`** for test programs

## Comparison with v1 Plan

| Aspect | v1 Plan | Revised |
|--------|---------|---------|
| Primary strategy | Reference oracle (Option A) | Translation validator (more targeted) |
| Engine replacement | Long-term goal (Option C) | Dropped — not cost-effective |
| Typed layer | Not yet built | Done (`TExpr`, commuting diagrams) |
| Hax engine | Assumed OCaml | Now known to be Rust for Lean backend |
| Phase count | Assumed ~12 | Now known to be 25+ |
| Integration point | JSON AST (vague) | Specific: between pre-processing and post-processing |
| SSProve backend | Not in v1 | Primary deliverable (most natural fit) |

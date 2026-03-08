# Plan: Upgrading ImpExpr to a Typed Language

## Executive Summary

**Refactor size**: ~2,500–3,500 LOC of new/changed code across 15+ files.
**Risk**: Medium — a commuting-diagram strategy lets us keep all existing untyped proofs intact.
**Recommended timeline**: 3–5 weeks.

## Current State

`ImpExpr` is an untyped expression language with 27 constructors.
Hax's AST wraps every subexpression with `{e: expr', typ: ty, span: span}` — every subexpression is fully typed (types come from the Rust frontend, no inference needed).

**Codebase statistics** (what gets touched):

| File | LOC | Pattern matches | Constructor uses | Impact |
|------|-----|----------------|-----------------|--------|
| AST.lean | 165 | 27 (ImpExpr.ind) | 27 | Critical |
| Features.lean | 462 | 91 | 80+ | High |
| FreeVars.lean | 106 | 51 | 0 | Low |
| Semantics.lean | 357 | 27 | 5 | Medium |
| SemanticsCF.lean | 685 | 28+ | 10+ | Medium |
| DropReferences.lean | 229 | 54 | 27 | Medium |
| LocalMutation.lean | 334 | 54 | 27+ | Medium |
| FunctionalizeLoops.lean | 510 | 54+ | 30+ | Medium-High |
| CfIntoMonads.lean | 462 | 54 | 30+ | Medium |
| FunctionalizeLoopsCF.lean | 1,645 | 120+ | 50+ | High (proofs) |
| CfIntoMonadsCF.lean | 1,680 | 120+ | 50+ | High (proofs) |
| ToRawCode.lean | 105 | 27 | 0 | Low |
| Pipeline.lean | 96 | 0 | 0 | Low |
| PipelineCF.lean | 488 | 0 | 0 | Low |
| **Total** | **~7,760** | **~363** | **~340** | |

## Architecture Decision: Commuting Diagram

The key insight: **types don't affect evaluation**. Our `denote` function never examines types — it evaluates expressions purely by structure. This means we can:

1. Keep all existing untyped definitions and proofs **unchanged**
2. Build a typed layer **on top** that commutes with type erasure
3. Prove phase correctness lifts from untyped to typed via the commuting diagram

```
TExpr ──[typed phase]──→ TExpr
  │                         │
  │ erase                   │ erase
  ↓                         ↓
ImpExpr ─[untyped phase]─→ ImpExpr   (already verified!)
```

If `erase ∘ typedPhase = untypedPhase ∘ erase`, then correctness follows for free.

**Why this is better than a direct refactor**: A direct refactor touching all 363 pattern matches and all proof files would be ~900–1,100 LOC of invasive changes with high risk of breaking proofs. The commuting approach adds ~600 LOC of new typed definitions + ~400 LOC of commuting proofs, while leaving the verified core untouched.

## Type Representation

### `ImpType` — Simplified Rust Type System

```lean
inductive ImpType where
  -- Primitives
  | bool
  | int
  | unit
  | str
  -- Compound
  | tuple (elems : List ImpType)
  | option (inner : ImpType)
  | result (ok err : ImpType)
  | controlFlow (brk cont : ImpType)
  -- Named types (ADTs, post-monomorphization)
  | adt (name : String) (args : List ImpType)
  -- Functions
  | fn (params : List ImpType) (ret : ImpType)
  -- References (erased by Phase 1)
  | ref (inner : ImpType) (mut : Bool)
  -- Slices / arrays
  | slice (inner : ImpType)
  | array (inner : ImpType) (len : Nat)
  -- Type variable (for generics before monomorphization)
  | typeVar (name : String)
  -- Unknown / erased (escape hatch for gradual adoption)
  | unknown
  deriving Inhabited, BEq, Repr
```

**Design choices**:
- Post-monomorphization: generic types are instantiated via `adt` args, no polymorphism
- `unknown` escape hatch: allows incremental adoption, can be eliminated later
- Mirrors hax's type representation but simplified (no lifetimes, no trait objects)
- `ref` present but erased by Phase 1 (matches `dropReferences`)

### `TExpr` — Typed Expression (Mutual Inductive)

```lean
mutual
/-- A typed expression: pairs a kind with its type. -/
inductive TExpr where
  | mk (kind : TExprKind) (ty : ImpType)

/-- Expression kinds — mirrors ImpExpr constructors but with TExpr in recursive positions. -/
inductive TExprKind where
  -- Core
  | lit (v : ImpLit)
  | var (name : String)
  | letBind (name : String) (val body : TExpr)
  | app (f : String) (args : List TExpr)
  | tuple (elems : List TExpr)
  | proj (e : TExpr) (i : Nat)
  | ifThenElse (cond thn els : TExpr)
  | match_ (scrut : TExpr) (arms : List (ImpPat × TExpr))
  | unitVal
  | seq (e1 e2 : TExpr)
  -- Phase 1
  | borrow (e : TExpr)
  | deref (e : TExpr)
  -- Phase 2
  | assign (name : String) (rhs : TExpr)
  -- Phase 3
  | forLoop (var : String) (lo hi body : TExpr)
  | whileLoop (cond body : TExpr)
  | break_ (e : Option TExpr)
  | continue_
  -- Phase 4
  | earlyReturn (e : TExpr)
  | questionMark (e : TExpr)
  -- Phase 3 output
  | forFold (var : String) (lo hi body : TExpr)
  | whileFold (cond body : TExpr)
  | forFoldReturn (var : String) (lo hi body : TExpr)
  | whileFoldReturn (cond body : TExpr)
  | cfBreak (e : TExpr)
  | cfContinue (e : TExpr)
  | cfBreakContinue (e : TExpr)
end
```

### Type Erasure

```lean
mutual
def TExpr.erase : TExpr → ImpExpr
  | .mk kind _ => kind.erase

def TExprKind.erase : TExprKind → ImpExpr
  | .lit v => .lit v
  | .var n => .var n
  | .letBind n val body => .letBind n val.erase body.erase
  | .app f args => .app f (args.map TExpr.erase)
  | .tuple elems => .tuple (elems.map TExpr.erase)
  | .proj e i => .proj e.erase i
  | .ifThenElse c t e => .ifThenElse c.erase t.erase e.erase
  | .match_ s arms => .match_ s.erase (arms.map fun (p, e) => (p, e.erase))
  | .unitVal => .unitVal
  | .seq e1 e2 => .seq e1.erase e2.erase
  -- ... (one line per constructor, mechanical)
end
```

### Typed Patterns

Hax's patterns also carry types. Extend `ImpPat`:

```lean
inductive TImpPat where
  | wildcard (ty : ImpType)
  | litPat (l : ImpLit) (ty : ImpType)
  | varPat (name : String) (ty : ImpType)
  | tuplePat (pats : List TImpPat)
  | somePat (p : TImpPat)
  | nonePat (ty : ImpType)          -- type of the Option
  | okPat (p : TImpPat) (errTy : ImpType)
  | errPat (p : TImpPat) (okTy : ImpType)
```

## Implementation Plan

### Step 1: Define Types (new files, no existing changes)

**New file: `SSProve/Hax/ImpType.lean`** (~80 LOC)
- `ImpType` inductive
- `ImpType.toString` for debugging
- Basic operations: `ImpType.isRef`, `ImpType.stripRef`

**New file: `SSProve/Hax/TExpr.lean`** (~250 LOC)
- `TExpr` / `TExprKind` mutual inductive
- `TExpr.erase` / `TExprKind.erase` (type erasure to `ImpExpr`)
- `TExpr.ind` custom induction principle (mirrors `ImpExpr.ind`)
- `TExpr.ty` accessor
- Smart constructors: `TExpr.mkLit`, `TExpr.mkVar`, etc.

**Estimated**: ~330 LOC new code, 0 lines changed.

### Step 2: Lift Feature Predicates

**New file: `SSProve/Hax/TFeatures.lean`** (~150 LOC)
- `TNoReferences`, `TNoMutation`, `TNoLoops`, `TNoEarlyExit` on `TExpr`
- Commuting lemma for each:
  ```lean
  theorem TNoReferences_iff_erase (e : TExpr) :
      TNoReferences e ↔ NoReferences e.erase
  ```
- Alternative: define feature predicates *only* via erasure:
  ```lean
  def TNoReferences (e : TExpr) : Prop := NoReferences e.erase
  ```
  This is zero-cost — all existing proofs apply directly through `erase`.

**Recommended**: Use the erasure-based definition. It's trivial and requires no new proofs.

**Estimated**: ~50 LOC (with erasure approach), 0 lines changed.

### Step 3: Lift Phase Transformations

For each phase, define the typed version and prove it commutes with erasure.

**New file: `SSProve/Hax/TPhase/DropReferences.lean`** (~120 LOC)
```lean
def tDropReferences : TExpr → TExpr
  | .mk (.borrow e) (.ref inner _) => tDropReferences e
  | .mk (.deref e) ty => tDropReferences e
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty =>
      .mk (.letBind n (tDropReferences val) (tDropReferences body)) ty
  -- ... (mechanical, same recursion as dropReferences but preserving types)

theorem tDropReferences_commutes (e : TExpr) :
    (tDropReferences e).erase = dropReferences e.erase
```

Similarly for the other 3 phases:
- **`TPhase/LocalMutation.lean`** (~150 LOC) — type-preserving mutation elimination
- **`TPhase/FunctionalizeLoops.lean`** (~200 LOC) — loops → folds with appropriate types
  - `forFold` gets type `ImpType.controlFlow bodyTy accTy`
  - `cfBreak`/`cfContinue` wrap with `ImpType.controlFlow`
- **`TPhase/CfIntoMonads.lean`** (~150 LOC) — early return → monadic with type changes
  - `earlyReturn e` of type `retTy` becomes `cfBreak e` of type `ImpType.controlFlow retTy bodyTy`

**Estimated**: ~620 LOC new code, 0 lines changed.

### Step 4: Typed Semantics

Two options:

**Option A (recommended): Inherit via erasure**
```lean
def tDenote (bi : Builtins) (fuel : Nat) (e : TExpr) (env : Env) :=
    denote bi fuel e.erase env

-- Correctness is FREE:
theorem tPipeline_correct (bi : Builtins) (fuel : Nat) (e : TExpr) ... :
    tDenote bi fuel (tPipeline e) env = tDenote bi fuel e env := by
  unfold tDenote
  rw [tPipeline_commutes]  -- reduces to untyped pipeline_correct
  exact pipeline_correct ...
```

**Option B: Direct typed semantics**
Define `tDenote` directly on `TExpr`. More work (~400 LOC) but enables future type-directed evaluation (e.g., typed environments, type-safe values).

**Recommended**: Option A for now. Option B can be added later when needed.

**Estimated**: ~30 LOC (Option A), 0 lines changed.

### Step 5: Typed Pipeline Composition

**New file: `SSProve/Hax/TPipeline.lean`** (~100 LOC)
```lean
def tPipeline (e : TExpr) : TExpr :=
  tCfIntoMonads (tFunctionalizeLoops (tLocalMutation (tMutatedVars e) (tDropReferences e)))

theorem tPipeline_commutes (e : TExpr) :
    (tPipeline e).erase = pipeline e.erase

theorem tPipeline_fullyFunctional (e : TExpr) :
    TFullyFunctional (tPipeline e) :=
  -- Follows from untyped proof via erasure
  pipeline_fullyFunctional e.erase

theorem tPipeline_correct ... :=
  -- Follows from untyped proof via commuting diagram
  ...
```

**Estimated**: ~100 LOC new code, 0 lines changed.

### Step 6: JSON Interface

**New file: `SSProve/Hax/Json.lean`** (~200 LOC)
- `FromJson ImpType`, `ToJson ImpType`
- `FromJson TExpr`, `ToJson TExpr`
- `FromJson TImpPat`, `ToJson TImpPat`
- Round-trip theorem: `fromJson (toJson e) = some e`

**New file: `SSProve/Hax/HaxAdapter.lean`** (~150 LOC)
- Parse hax's JSON AST format into `TExpr`
- Strip hax-specific fields (spans, attributes, hir_id)
- Map hax type constructors to `ImpType`

**Estimated**: ~350 LOC new code.

### Step 7: Typed Pretty Printer

**New file: `SSProve/Hax/TPrint.lean`** (~200 LOC)
- `TExpr → Format` for Lean 4 syntax output
- Uses type annotations for:
  - Function signatures
  - Let binding type annotations
  - Match arm return types

**Estimated**: ~200 LOC new code.

## File Layout (after refactor)

```
SSProve/Hax/
├── AST.lean                      # ImpExpr (UNCHANGED)
├── ImpType.lean                  # NEW: type representation
├── TExpr.lean                    # NEW: typed expressions
├── Value.lean                    # UNCHANGED
├── Features.lean                 # UNCHANGED
├── TFeatures.lean                # NEW: typed feature predicates (via erasure)
├── FreeVars.lean                 # UNCHANGED
├── Semantics.lean                # UNCHANGED
├── SemanticsCF.lean              # UNCHANGED
├── Phase/
│   ├── DropReferences.lean       # UNCHANGED
│   ├── LocalMutation.lean        # UNCHANGED
│   ├── FunctionalizeLoops.lean   # UNCHANGED
│   ├── FunctionalizeLoopsCF.lean # UNCHANGED
│   ├── CfIntoMonads.lean         # UNCHANGED
│   └── CfIntoMonadsCF.lean       # UNCHANGED
├── TPhase/                       # NEW directory
│   ├── DropReferences.lean       # NEW: typed Phase 1
│   ├── LocalMutation.lean        # NEW: typed Phase 2
│   ├── FunctionalizeLoops.lean   # NEW: typed Phase 3
│   └── CfIntoMonads.lean         # NEW: typed Phase 4
├── ToRawCode.lean                # UNCHANGED
├── Pipeline.lean                 # UNCHANGED
├── PipelineCF.lean               # UNCHANGED
├── TPipeline.lean                # NEW: typed pipeline
├── Json.lean                     # NEW: JSON serialization
├── HaxAdapter.lean               # NEW: hax JSON → TExpr
└── TPrint.lean                   # NEW: Lean 4 printer
```

**Key property: 0 existing files modified.**

## Estimated LOC

| Component | New LOC | Changed LOC |
|-----------|---------|-------------|
| ImpType.lean | 80 | 0 |
| TExpr.lean | 250 | 0 |
| TFeatures.lean | 50 | 0 |
| TPhase/ (4 files) | 620 | 0 |
| TPipeline.lean | 100 | 0 |
| Json.lean | 200 | 0 |
| HaxAdapter.lean | 150 | 0 |
| TPrint.lean | 200 | 0 |
| Hax.lean (imports) | 0 | 10 |
| **Total** | **~1,650** | **~10** |

## Commuting Proofs: Difficulty Assessment

| Phase | Commuting proof difficulty | Why |
|-------|---------------------------|-----|
| dropReferences | Easy | Structural recursion, types just pass through |
| localMutation | Easy-Medium | Variable renaming must preserve types |
| functionalizeLoops | Medium | Must compute types for generated folds/cfBreak/cfContinue |
| cfIntoMonads | Medium | Must compute ControlFlow types from earlyReturn type |

The main subtlety: Phases 3 and 4 **change the type** of some subexpressions (e.g., a loop body returning `T` becomes a fold body returning `ControlFlow T T`). The commuting proof must show that type *erasure* still commutes despite these type changes. This is true by construction since `erase` discards all type information.

## Risks and Mitigations

| Risk | Likelihood | Mitigation |
|------|-----------|------------|
| Lean 4 mutual inductive limitations | Low | Well-tested feature; similar to current `ImpExpr` |
| Custom induction principle for `TExpr` | Medium | Mirror existing `ImpExpr.ind` structure |
| Commuting proofs harder than expected | Low | By construction, `erase` discards types — proofs should be mechanical |
| `ImpType.unknown` proliferates | Medium | Lint check: reject `unknown` in fully-typed mode |
| Hax JSON format changes | Medium | Pin to specific hax version; version field in JSON |

## Future Extensions (not in this plan)

1. **Well-typedness predicate**: `WellTyped : TExpr → TEnv → Prop` — proves expressions respect their type annotations
2. **Typed values**: `TValue : ImpType → Type` — type-indexed runtime values
3. **Type preservation**: `WellTyped e env → WellTyped (phase e) (phaseEnv env)`
4. **Dependent features**: `TExpr (features : FeatureSet)` — phantom type preventing use of consumed constructors (mirrors hax's OCaml functors)

## Comparison: Direct Refactor vs Commuting Diagram

| Aspect | Direct Refactor | Commuting Diagram (recommended) |
|--------|----------------|----------------------------------|
| Existing files changed | 15+ files, 900–1,100 LOC | 1 file (imports), ~10 LOC |
| Existing proofs broken | All (363 pattern matches) | None |
| New code required | ~900 LOC edits | ~1,650 LOC new files |
| Risk of regression | High | Negligible |
| Verification gap | None (single source of truth) | Must prove commuting lemmas |
| Maintenance burden | Single AST to maintain | Two ASTs (typed + untyped) |
| Path to removing untyped | N/A (already removed) | Future refactor once stable |

The commuting diagram adds ~750 more LOC but eliminates all regression risk and keeps the verified core pristine. Once the typed layer is stable and tested, we can optionally collapse the two layers in a future refactor.

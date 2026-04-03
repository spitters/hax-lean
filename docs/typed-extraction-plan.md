# Typed Extraction Plan: Eliminate Heuristic Type Recovery

## Status (2026-03-17)

**Phase 1 complete: `generatePreambleTyped` wired in. 73/94 use typed preamble, 21 pending.**

| Component | File | Status |
|-----------|------|--------|
| TExpr definition | TExpr.lean (354 LOC) | Done, 0 sorries |
| ImpType | ImpType.lean (177 LOC) | Done, 0 sorries |
| 5 typed phases | TPhase/*.lean (~869 LOC) | Done, commuting diagrams proved |
| tPipeline | TPipeline.lean (70 LOC) | Done, `tPipeline_erase` proved |
| parseHaxTExpr | HaxAdapter.lean | Done, types from hax JSON |
| PrettyPrintT | PrettyPrintT.lean (~440 LOC) | **`generatePreambleTyped` wired in** |
| MainT / haxpipeT | MainT.lean (162 LOC) | Done, 94/94 generate output |

## Phase 1 Results

`toLeanCertifiedFileTyped` now calls `generatePreambleTyped(rawTdefs, processedDefs=defs)`
instead of `generatePreamble(defs, ..., callRetTypes, callSigs, varRefTypes)`.

### What changed
- `depTypeStr`: unknown/unit → "Array Int" (matches untyped default)
- `generatePreambleTyped`: takes `processedDefs` for struct analysis (ImpExpr),
  uses `tdefs` (TExpr) only for deps class type annotations
- Collection ops override: iter/map/collect/etc. always return Array Int
- 0-arity dep reconciliation: when typed says "Int" but `isVarUsedAsInt` disagrees,
  prefer the usage-based type
- `isVarUsedAsInt` made non-private for cross-module use

### Preamble diff categories across 94 crates
- **57 identical** (only comment changes)
- **16 improved** (build OK, better types: e.g., `Mul : Int` instead of `Array Int`)
- **2 preamble-only regressions** (aegis, argon2: `uint 128` → "Int" but extraction model needs Array Int)
- **19 body+preamble diffs** (from `parseHaxTExpr` producing different ASTs, separate issue)

### Remaining issues
1. **`ImpType.toLeanTypeStr` maps ALL uint/sint → "Int"**, but extraction model uses "Array Int"
   for large constants (AEGIS_C0, BLAKE2B_IV). Need width-sensitive or context-sensitive mapping.
2. **`parseHaxTExpr` body diffs**: Sha256State::new() → `#[]`, Hax.literal → `()`,
   tuple flattening. These are parseHaxTExpr correctness issues, not preamble issues.
3. **21 crates need body-level parseHaxTExpr fixes** before typed extraction can replace untyped.

### Build verification
- 73/94 extraction files use typed preamble (haxpipeT), all build
- 21/94 reverted to untyped (haxpipe), all build
- Full CatCrypt.Crypto: 3927/3927 jobs, 0 failures

## Phases

### Phase 1: Wire in `generatePreambleTyped` for deps class ✓

Completed 2026-03-17. See results above.

### Phase 2: Fix `parseHaxTExpr` body parity

**Goal**: Make `parseHaxTExpr(j).erase == parseHaxExpr(j)` for all constructs.

**Known diffs** (21 crates affected):
- Sha256State::new() rendered as `#[]` instead of `Sha256State(repeat 0 8, repeat 0 64, 0, 0)`
- Rust `literal()` → `()` instead of `Hax.literal`
- Tuple flattening: `(ZERO, ZERO)` → `ZERO` in from_elem args
- Byte string literals: `array_lit [66, 66, ...]` → `(0 : Int)`

**Approach**: Fix TExpr parsing for struct constructors (new → expand fields),
unit/string literals (preserve as `app "literal" []`), tuple construction.

### Phase 3: Type-directed parameter annotations

**Goal**: Use actual `ImpType` from TExpr for parameter annotations.
Keep integer collapse (all uint/sint → Int) since extraction model uses Int.
Annotate struct-typed params with their tuple type.

### Phase 4: Type-directed body rendering (future)

Build `toLeanTyped : TExpr → Nat → String` that uses `e.ty` for:
- Operator selection, cast insertion, struct projection disambiguation
- Replaces ~500 lines of heuristic code in `PrettyPrint.lean`

### Phase 5: Delete heuristics (future)

Once all 94 build through the typed path: delete ~500 lines from PrettyPrint.lean.

## Key Design Decisions

- **Integer collapse preserved**: All `uint`/`sint` → `Int` in `toLeanTypeStr`.
  The extraction model uses unboxed `Int`. Changing requires Runtime.lean changes.
- **Struct gen stays untyped**: Struct definitions use post-pipeline ImpExpr analysis
  (qualified projections, passthrough detection). Structural, not heuristic.
- **Deps class is typed**: Call-site types from TExpr replace heuristic detection.
- **0-arity dep reconciliation**: Typed info + `isVarUsedAsInt` heuristic together.
  Pure typed info insufficient because `uint → "Int"` doesn't distinguish
  scalar integers from byte arrays.
- **`processedDefs` parameter**: `generatePreambleTyped` accepts post-pipeline ImpExprs
  for struct analysis while using raw TExprs for type extraction. This ensures
  qualified projection names and struct passthrough detection work correctly.

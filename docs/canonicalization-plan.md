# PrettyPrint Canonicalization Plan (Approach C)

Move `toLean`'s semantic transformations from string-rendering into ImpExpr→ImpExpr
pipeline passes, so that `toLean` becomes a trivial syntax mapping and per-function
agreement is `rfl` by construction.

## Current trust gap

```
file bytes → [Hax.Json.parseJsonString, VERIFIED]   → Lean.Json
           → [parseHaxExpr, VERIFIED]               → ImpExpr
           → [pipeline phases, VERIFIED]            → ImpExpr (FullyFunctional)
           → [PrettyPrint, UNVERIFIED]              → Lean source string ← THIS GAP
```

`toLean` is unverified because it performs semantic transformations during string
emission. After this plan, the post-pipeline ImpExpr is **canonical** — every
constructor maps directly to a Lean syntax form — and `toLean` becomes faithful
by construction.

## Transformations inventory (what `toLean` currently does that's semantic)

Surveyed from `Hax/PrettyPrint.lean`:

| # | Pattern (input ImpExpr) | Surface code emitted | Semantic? |
|---|---|---|---|
| 1 | `letBind "_tup" rhs (letBind "a" (proj "_tup" 0) (letBind "b" (proj "_tup" 1) body))` | `let (a, b) := rhs; body` | Yes |
| 2 | `letBind n (cfBreak _) body` where `n.startsWith "_"` | skip the binding, render `body` only | Yes |
| 3 | `letBind "_assign…" val body` where `body = var n` (self-ref) | `let _ := val; ()` | Yes |
| 4 | `letBind n (match scrut with arms-with-cfBreak) body` | if-else chain with continuation inlined into non-cfBreak arms, cfBreak unwrapped in cfBreak arms | Yes |
| 5 | `seq(forFold "i" lo hi body, var acc)` | `Hax.foldRange lo hi acc fun i acc => body'` (accumulator extraction) | Yes |
| 6 | `seq(ifThenElse cond unitVal work, rest)` | rewrite to `cfContinue` form | Yes |
| 7 | `ifThenElse c t (var "_assign…")` in mutation context | conditional update — else branch is dropped/unit-ified | Yes |
| 8 | `app "map" [iter, fn]` etc. | `(iter).map fn` (method-call rewrite) | Mostly syntactic; could stay |
| 9 | `app "panic" args` | `()` (panics become unit) | Yes |
| 10 | `forFold` whose body has surface cfBreak | wrap with `.merge` for ControlFlow → α extraction | Yes |
| 11 | Guard `n.startsWith "_assign" && body == .var n` | `let _ := val; ()` | Yes |
| 12 | Dead ControlFlow bindings (cfBreak/cfContinue/cfBreakContinue with `_`-prefix bind) | skip | Yes |

Items 1, 5, 9, 12 are the highest-impact (most invocations across the 160 extracted files).

## Plan

### Pass A — `canonicalizeTupleDestructure` (item 1)

Detect `letBind "_tup" rhs (letBind "a" (proj "_tup" 0) (letBind "b" (proj "_tup" 1) body))`
and rewrite to a new ImpExpr constructor `tupleLetBind : List String → ImpExpr → ImpExpr → ImpExpr`
where the names list captures the destructured pattern. `toLean` then renders this
trivially as `let (a, b) := rhs; body`.

**New AST**: `ImpExpr.tupleLetBind names rhs body`.
**toLean rule**: `let ({names.intercalate ", "}) := {toLean rhs}; {toLean body}`.

### Pass B — `canonicalizeFolds` (item 5)

Detect `seq(forFold "i" lo hi body, var acc)` and rewrite to a new constructor
`foldAccum : String → ImpExpr → ImpExpr → String → ImpExpr → ImpExpr`
representing `Hax.foldRange lo hi acc fun i acc => body`.

**New AST**: `ImpExpr.foldAccum i lo hi accName body`.
**toLean rule**: trivial.

### Pass C — `canonicalizeMutationDiscard` (items 3, 11)

Rewrite `letBind n val (var n)` patterns where `n.startsWith "_assign"` to
`letBind "_" val .unitVal` (or a new `discardLet`).

**toLean rule**: trivial.

### Pass D — `canonicalizeDeadCFBindings` (items 2, 12)

Rewrite `letBind n (cfBreak _) body` where `n.startsWith "_"` to just `body`.
Same for cfContinue / cfBreakContinue.

**toLean rule**: just renders `body`.

### Pass E — `canonicalizePanic` (item 9)

Rewrite `app "panic" args` (and `panic_fmt`) to `unitVal`.

**toLean rule**: trivial.

### Pass F — `canonicalizeMatchCfBreak` (item 4)

Hardest. Rewrite `letBind n (match scrut with arms-with-cfBreak) body`
to a flattened if-else chain at the AST level.

**Risk**: changes program shape significantly; may break extraction of some
protocols that rely on the specific match shape.

### Pass G — `canonicalizeIfElseAssign` (item 7)

Rewrite `letBind n (ifThenElse c t (var "_assign…")) body` to drop the
self-referential else branch.

## Order of execution

```
ImpExpr (post-existing-pipeline, FullyFunctional)
  → canonicalizeDeadCFBindings  (D)
  → canonicalizePanic            (E)
  → canonicalizeMutationDiscard  (C)
  → canonicalizeTupleDestructure (A)
  → canonicalizeFolds            (B)
  → canonicalizeMatchCfBreak     (F)
  → canonicalizeIfElseAssign     (G)
  → ImpExpr (Canonical)
  → toLean (trivial syntax mapping)
  → Lean source string
```

After this, every `ImpExpr` constructor maps to exactly one Lean syntax form
(no detection, no heuristics).

## Per-pass effort estimate

| Pass | New constructor | Detection logic | toLean rule | Test coverage | Effort |
|---|---|---|---|---|---|
| D — DeadCFBindings | none | ~10 LOC | ~3 LOC | 5+ existing extractions | ~30 min |
| E — Panic | none | ~5 LOC | ~3 LOC | a few protocols use panic | ~15 min |
| C — MutationDiscard | none | ~10 LOC | ~3 LOC | many | ~30 min |
| A — TupleDestructure | `tupleLetBind` | ~20 LOC | ~5 LOC | many | ~1 hr |
| B — Folds | `foldAccum` | ~30 LOC | ~10 LOC | dozens | ~1.5 hr |
| F — MatchCfBreak | maybe `ifElseChain` | ~50 LOC | ~10 LOC | several | ~3 hr |
| G — IfElseAssign | none | ~10 LOC | ~3 LOC | several | ~30 min |

**Total new LOC**: ~150 lines of pass logic + ~40 lines of toLean simplification
= ~190 net lines. Plus removal of equivalent detection logic from existing toLean
(~300 lines deleted). **Net: ~110 LOC reduction.**

## Risk and validation

After each pass:
1. `lake build Hax` should remain clean.
2. Run haxpipeT over each of the 160 already-extracted files; the output should
   be byte-identical (or modulo whitespace) to the pre-refactor output.
3. If a file produces different output, investigate before proceeding.

The 160-file regression suite is the main safety net. Without it, this refactor
is too risky.

## Per-function agreement theorems (after refactor)

Once `toLean` is trivial, define `shallowEval : ImpExpr → Lean.Expr` (or
`ImpExpr → String`-with-tagging) such that for canonical ImpExpr,
`toLean e = shallowEval e` definitionally. Then for each extracted function:

```lean
theorem f_agrees : f = denoteValue fullBuiltins f_impExpr [params] := by
  rfl  -- or native_decide if reduction is hard
```

The `--emit-certified` mode emits these per-function alongside surface + ImpExpr
literal, giving a per-function machine-checked certificate that the surface code
matches the verified pipeline output.

## Deferred (not in this plan)

- **Lean.Expr formalization** (Approach A from agreement-proof-investigation.md) —
  research-level, 2000-4000 LOC.
- **Per-function `native_decide` agreement** without canonical ImpExpr —
  blocked, function equality undecidable.

## Status / next steps

Phase order:
1. ✅ Plan written (this doc).
2. Implement Passes D, E, C (the simple ones) — should be quick wins.
3. Validate against existing extracted files.
4. Implement Passes A, B (medium-effort).
5. Implement Pass F (hardest).
6. Skip G or implement opportunistically.
7. Simplify `toLean` accordingly, deleting detection logic.
8. Add per-function agreement emission to `--emit-certified` mode.

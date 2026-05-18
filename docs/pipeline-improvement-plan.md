# Verified pipeline improvement plan

A roadmap for shrinking the trusted computing base and improving feature
coverage of `haxpipeT`. Guiding principle: **stay close to upstream
cryspen/hax unless we have a concrete reason to deviate.**

## Why stay close to upstream

1. **Feature coverage.** Upstream's lean-refines backend handles real
   crypto codebases (libcrux, bertie) that span the hax-supported Rust
   subset. Re-deriving feature support from scratch is wasted effort.
2. **Bug surface.** Every divergence is a place where we accumulate
   bugs upstream has already fixed (e.g. the AEGIS tuple-arity issue —
   upstream's `⟨a, b, c⟩ ← call ...` pattern bypasses the wrong-arity
   annotation entirely).
3. **Maintenance.** Upstream evolves the hax JSON format. Closer
   alignment means cheaper rebases.

Deviation is justified only when we have a verified-pipeline-specific
goal that upstream's design actively blocks. Two examples that meet
that bar:
- AST-to-AST phase verification (CompCert-style `erase`-preservation
  theorems). Upstream's OCaml backend can't host this.
- ImpExpr literal emission for downstream agreement proofs.

Everything else should track upstream.

## Status of the six bugs

| Bug | Status | Approach |
|---|---|---|
| AEGIS / OPAQUE tuple-arity | ✅ fixed (hax-lean c9c6b66, 6081098) | Skip annotation on tuples — Lean infers from destructure + signature, just like upstream's `⟨…⟩ ← call` pattern |
| OPAQUE `_tup` Unknown | ✅ fixed | Drop only when body doesn't reference the name |
| Empty deps class | ✅ fixed | Emit `class XDeps where` even when empty |
| **CPABE / Noise enum-as-axiom** | ✅ **fixed (7087c86)** | Emit `inductive T where | A | B` — matches upstream's enum handling |
| AESGCMSIV match wildcard | ❌ deferred | See §3.1 below |
| SPDZ struct-from-elem | ❌ deferred | See §4.2 below |

## 1. Architectural alignment with upstream

Upstream's `lean_refines_backend.ml` defines a typed Lean AST
(`lean_ast.ml`) with first-class nodes for everything that matters in
the target language. We use an untyped `ImpExpr` plus a parallel
`TExpr` wrapper, with type info threaded through `.ann` markers and
`::annot::T` string sentinels.

**Strong reason to deviate exists** (verification benefits from a
small AST), but we pay for it:
- `::annot::T` string markers in `PrettyPrint.lean` are fragile —
  every renderer site must peek through them.
- Wrong-type annotations cause real bugs (AEGIS).
- We can't catch ill-typed annotations at construction time.

### 1.1 Add `ImpExpr.typeAscription` (P1)

A first-class AST node `typeAscription (e : ImpExpr) (ty : ImpType)`
replaces `::annot::T` string markers entirely. The renderer renders
it as `(e : T.toLeanTypeStrSurface)`. Construction sites that get the
type wrong now produce a type error in haxpipeT itself, not silently
in the generated Lean.

Closes one class of "wrong annotation" bugs at the source.

**Upstream alignment.** Their `term` has `TypeAscription of term * ty`
as a first-class variant. Direct mirror.

### 1.2 Add `ImpPat.ascriptionPat` (P3)

Same shape for patterns. Lets match arms carry type info where Lean's
inference can't reach. Upstream has `AscriptionPat of pat * ty`.

### 1.3 Operator table as data (P2)

Replace `isAlwaysBuiltin`'s 30-line pattern match with a
`List (String × OpInfo)` table keyed by hax name. Upstream has
`let operators = Map.of_alist_exn ...` — a one-line addition for any
new operator. Our pattern match is fragile (we just shipped a fix for
missing `Mul`).

## 2. Shrink the TCB by moving rewriters into verified phases

`PrettyPrint.lean` currently contains 8 `ImpExpr → ImpExpr` rewriters
(see [`docs/integration-architecture.md`](integration-architecture.md)).
They live in the TCB but aren't rendering logic:

| Rewriter | Lines | Type-dependent? |
|---|---|---|
| `qualifyProjections` | ~70 | yes (struct types) |
| `rewriteAppName` | ~35 | no |
| `rewriteNewToStructCtor` | ~130 | yes |
| `rewriteStructFromElem` | ~170 | yes |
| `fixProjectionPaths` | ~100 | yes (tuple arities) |
| `initMissingFoldAccums` | ~60 | no |
| `reconcileFnTypes` | ~30 | yes (fn signatures) |
| `qualifyProjectionsFromUsageT` | ~190 | yes |

Total: ~785 lines moveable.

### 2.1 Move type-independent rewriters first (P2)

`rewriteAppName` and `initMissingFoldAccums` don't need type info.
They can move to `Hax/Phase/StructResolution.lean` as untyped phases
with denotation-preservation proofs. Verified-pipeline approach,
matches the existing `Hax/Phase/LocalMutation.lean` structure.

### 2.2 Move type-dependent rewriters as TPhases (P3)

`qualifyProjections`, `rewriteNewToStructCtor`, etc. need typed
information. As `TPhase`s with TExpr input, they can:
- Read `.ty` directly instead of using `inferExprStructType`
  heuristics — this also fixes the SPDZ `rewriteStructFromElem`
  bug, which fails precisely because struct-type inference from
  context misses the call-site type.
- Prove `erase`-preservation against the existing untyped versions
  (CompCert pattern).

### 2.3 Static bounds analysis (P4 — direct upstream borrow)

Upstream emits `arr[i]'(by omega)` when `i` is a literal and `arr`
has a static-size type, eliminating panic obligations at extraction
time. They have `try_array_static_size` + `ProvenIndex` AST node. We
go through `getElem!` for every index.

A new TPhase that walks TExpr and rewrites
`.app "index" [arr, .lit (.int n)]` to a proven-index node when
`arr.ty = .array _ N` and `n < N`. Mirrors upstream directly.

## 3. Match-arm type unification (fixes AESGCMSIV)

AESGCMSIV: the match has 4 arms returning `Array Int` plus a wildcard
`| _ => ()` returning `Unit`. Lean rejects on type mismatch.

The issue is that the match is a *statement* in the original Rust
(updates `auth_key`/`enc_key` by side effect), but our renderer treats
it as an *expression*. The wildcard's `()` is the renderer's default
for arms with no value, which is wrong here.

### 3.1 Detect statement-context matches (P2)

Two reasonable approaches:

**3.1a Source-side workaround.** Rewrite the Rust to use `if/else if`
instead of `match` for statement-context branching. This is what we
did for `while` → `for` (the hax-supported subset preference).
Lowest-friction, but doesn't help other crates with the same shape.

**3.1b Renderer fix (closer to upstream).** When the match is in
statement context (no value used), emit it as Lean `match _ with` and
use `()` consistently. Upstream's `Match` AST node has a `result_ty`
field that makes context explicit. Borrow that.

I'd lean toward 3.1b for the same reason as 3.1a felt wrong for `while`
→ `for`: workarounds in source don't compose. The renderer should
handle statement-context matches.

## 4. Two bugs deserve direct attention

### 4.1 Inductive emission with payloads (P2 follow-on)

The enum fix in 7087c86 handles unit-only variants. Real cases will
hit payload-carrying variants soon (e.g. `enum Maybe { Some(T), None }`,
`enum Result { Ok(T), Err(E) }` — though those are special-cased in
hax). Upstream emits the payload types:

```
inductive PolicyNodeType : Type
  | And : PolicyNodeType
  | WithData : Int → PolicyNodeType
```

Extend `EnumInfo` to carry per-variant payload types
(`variants : List (String × List ImpType)`). Renderer emits
`| WithData : Int → T`. Builds on the just-landed framework.

### 4.2 Verified `rewriteStructFromElem` (fixes SPDZ)

The current rewriter detects "struct array initializer" via heuristics
on the surrounding context — it walks the body looking for struct-style
projections on the resulting array. For SPDZ, the heuristic fails: the
struct array's projections are downstream of a fold that the rewriter
doesn't peer into.

A TPhase version using `TExpr.ty` would just read the array's element
type directly — no heuristic needed.

## 5. Test infrastructure improvements

Currently the audit suite is:
- `scripts/audit_haxpipe.sh` — golden-diff + lake build + TCB ratchet
- `scripts/reextract.sh` — regenerate the 94 *_haxpipe.lean

### 5.1 Add upstream-comparison mode (P3)

`scripts/audit_haxpipe.sh --upstream` runs `cargo hax into lean` on
each crate and diffs against haxpipeT output (modulo backend-specific
differences). When we deviate, the diff explains why.

### 5.2 Coverage report (P3)

Per-crate: how many features (loops, traits, generics, enums, ...) of
the hax-supported subset does the crate exercise? Cross-reference with
known-broken extractions to find feature gaps proactively.

### 5.3 Run upstream's test suite (P4)

cryspen/hax has `~/tracked/hax/test-harness/` with unit tests for the
lean-refines backend. Vendoring or running these against haxpipeT
catches a different class of bugs than our crate-level audit.

## Suggested execution order

1. **P1** — `ImpExpr.typeAscription` (small change, eliminates a whole
   class of bugs, ~150-line net TCB shrink).
2. **P2** — Move 2 type-independent rewriters to `Hax/Phase/` (~100
   lines moved, two new erase theorems mechanical from existing
   templates).
3. **P2** — Operator table (~30 lines net wash, but easier to extend).
4. **P2** — Inductive payloads (closes a class of future bugs in one
   pass).
5. **P2** — Match-arm type unification (closes AESGCMSIV; statement-
   context match detection).
6. **P3** — Move type-dependent rewriters as TPhases (~700 lines moved,
   closes SPDZ along the way).
7. **P3** — `ImpPat.ascriptionPat` (smaller follow-on of P1).
8. **P4** — Static bounds analysis (correctness improvement; new
   feature, direct mirror of upstream).
9. **P4** — `--upstream` audit mode + coverage report (test
   infrastructure).

P1 + P2 items together remove ~250 lines from the TCB, close 3-4 known
bug classes, and align our renderer's shape with upstream's typed AST.
That's a focused 1-2 week work block.

P3 items continue the TCB shrink and finish the deferred bug closure.

P4 items are net additions (new features) but mirror upstream directly
— the cost is mostly translation, not design.

## What we should NOT mirror from upstream

A few places where we already deviate for good reason:

- **Erase-preservation theorems on phases.** Upstream has none. Keep
  ours.
- **TCB/verified-core split.** Upstream doesn't articulate this.
  Keep our discipline.
- **ImpExpr literal emission** (`toLeanImpExpr`). Upstream doesn't
  emit a Lean literal of the post-pipeline AST for downstream
  agreement proofs. We do, and it's how the `*_impExpr` definitions
  in `*_haxpipe.lean` are wired to the security proofs in `CatCrypt/`.
  Keep this.
- **Audit infrastructure**. Upstream has unit tests; we have a
  93-crate regression suite. Different scales, both valuable.

## Closing note

The bugs we hit aren't a sign that the verified pipeline is wrong —
they're a sign that the verified part is narrower than the project
name suggests. The pipeline verification is real: `tPipeline` preserves
`erase` semantics, every TPhase is proved erase-equivalent to its
untyped counterpart, and the audit infrastructure exercises the TCB
end-to-end. What's left is to **expand the verified core** at the
expense of the TCB. The plan above does that incrementally without
abandoning what upstream has already worked out.

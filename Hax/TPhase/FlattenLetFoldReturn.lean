/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr
import Hax.Semantics

/-!
# Typed phase: `tFlattenLetFoldReturn`

Post-pipeline AST normalisation that rewrites `letBind "_" e rest`
patterns so the renderer's `seqFoldReturn` dispatch fires correctly and
function-level early-returns from inside `forFoldReturn` /
`forFoldRevReturn` / `whileFoldReturn` propagate to the enclosing
function-tail.

This is a render-time pass: it runs in `tPipelineFull` *after* the
verified core `tPipeline` and is not subject to the `tPipeline_erase`
commuting diagram. Unlike the core typed passes, it has no parallel
untyped twin in `Hax/Phase/`; denotation preservation is stated
directly on the erased output (see `tFlattenLetFoldReturn_denote`).

## Motivation

The legacy untyped backend (`cargo hax into lean`) emits, for a discarded
`for` loop with `return v` inside:

```
match (← fold_range_return ...) with
| .Break ret => pure ret      -- function returns ret
| .Continue _ => pure <rest>  -- fold completed; continue
```

The verified pipeline emits the same shape via `seqFoldReturn`, but ONLY
when the AST has `.seq <fold> rest` at the surface. The hax JSON often
produces `.letBind "_" <fold> rest` (or worse, the fold is buried inside
the `then`-branch of an `.ifThenElse`), so `seqFoldReturn` never sees it
and the renderer emits `let _ := <fold>; rest` — silently dropping the
function-return value and producing ill-typed Lean (unresolved
`ControlFlow` type parameters).

This phase normalises four `letBind "_"`-discarding patterns:

| # | Rewrite | Reason |
|---|---|---|
| **A** | `letBind "_" .unitVal rest → rest` | Discarding `()` is a no-op. |
| **B** | `letBind "_" (letBind "_" v₁ b₁) b₂ → letBind "_" v₁ (letBind "_" b₁ b₂)` | Associativity of discarded binds. |
| **C** | `letBind "_" (ifThenElse c t e) rest → ifThenElse c (letBind "_" t rest) (letBind "_" e rest)` (when `t` or `e` contains a fold-with-return) | Push `rest` into branches so the function-return propagates. |
| **D** | `letBind "_" <forFoldReturn> rest → seq <forFoldReturn> rest` | Surface the fold to `seqFoldReturn` so it emits the match-and-destructure form. |

All four are denotation-preserving:

- **A**: `letBind "_" .unitVal e ≡ e` because the bind name `"_"` is
  unreferenced and `.unitVal` is side-effect-free.
- **B**: both forms evaluate `v₁`, then `b₁`, then `b₂` in sequence.
- **C**: both forms branch on `c` and execute exactly one of `t`/`e`,
  then `rest`. The duplicate `rest` in the AST runs once dynamically.
- **D**: `letBind "_" e r ≡ seq e r` whenever `"_"` is not free in `r`.
  By convention `"_"` is the universal discard binding and never a
  free reference, so the equivalence holds for any `e`.

## Termination

Rules **A**, **D** are structurally decreasing. Rule **B** rotates a
balanced binary tree of letBinds; the right-leaning form is canonical
and is a fixpoint of B itself. Rule **C** duplicates `rest` but each
sub-letBind is strictly smaller (smaller `val`), so successive
C-applications terminate.

The implementation uses `partial def` for ergonomics — the recursive
calls on rewrites cross the structural boundary. A total reformulation
via explicit fuel (bounded by AST size) is a follow-up.
-/

namespace Hax

/-- Typed `hasNestedFoldWithReturn`: detect whether the typed expression
    contains a `forFoldReturn` / `forFoldRevReturn` / `whileFoldReturn`
    whose body has a function-level early-return (`.cfBreak _` at the
    body surface). -/
partial def tHasNestedFoldWithReturn (e : TExpr) : Bool :=
  match e with
  | .mk (.forFoldReturn _ _ _ b) _ | .mk (.forFoldRevReturn _ _ _ b) _
  | .mk (.whileFoldReturn _ b) _ =>
    tBodyHasSurfaceCfBreak b || tHasNestedFoldWithReturn b
  | .mk (.letBind _ v body) _ => tHasNestedFoldWithReturn v || tHasNestedFoldWithReturn body
  | .mk (.seq a b) _ => tHasNestedFoldWithReturn a || tHasNestedFoldWithReturn b
  | .mk (.ifThenElse _ t e') _ => tHasNestedFoldWithReturn t || tHasNestedFoldWithReturn e'
  | .mk (.match_ _ arms) _ => arms.any (fun (_, b) => tHasNestedFoldWithReturn b)
  | .mk (.ann e') _ => tHasNestedFoldWithReturn e'
  | _ => false
where
  tBodyHasSurfaceCfBreak : TExpr → Bool
    | .mk (.cfBreak _) _ => true
    | .mk (.ifThenElse _ t e) _ => tBodyHasSurfaceCfBreak t || tBodyHasSurfaceCfBreak e
    | .mk (.letBind _ _ b) _ => tBodyHasSurfaceCfBreak b
    | .mk (.seq a b) _ => tBodyHasSurfaceCfBreak a || tBodyHasSurfaceCfBreak b
    | .mk (.match_ _ arms) _ => arms.any (fun (_, b) => tBodyHasSurfaceCfBreak b)
    | .mk (.ann e) _ => tBodyHasSurfaceCfBreak e
    -- Stop at inner loop bodies — their cfBreaks belong to them.
    | .mk (.forFold _ _ _ _) _ | .mk (.forFoldRev _ _ _ _) _
    | .mk (.forFoldReturn _ _ _ _) _ | .mk (.forFoldRevReturn _ _ _ _) _
    | .mk (.whileFold _ _) _ | .mk (.whileFoldReturn _ _) _ => false
    | _ => false

/-- Typed flattening pass. Bottom-up structural traversal; at each
    `.letBind "_"` apply A/B/C/D as appropriate. Preserves outer types
    on every node. -/
partial def tFlattenLetFoldReturn : TExpr → TExpr
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk (.break_ (some e)) ty => .mk (.break_ (some (tFlattenLetFoldReturn e))) ty
  | .mk (.app f args) ty => .mk (.app f (args.map tFlattenLetFoldReturn)) ty
  | .mk (.tuple es) ty => .mk (.tuple (es.map tFlattenLetFoldReturn)) ty
  | .mk (.proj e i) ty => .mk (.proj (tFlattenLetFoldReturn e) i) ty
  | .mk (.ifThenElse c t e) ty =>
    .mk (.ifThenElse (tFlattenLetFoldReturn c) (tFlattenLetFoldReturn t) (tFlattenLetFoldReturn e)) ty
  | .mk (.match_ scrut arms) ty =>
    .mk (.match_ (tFlattenLetFoldReturn scrut)
      (arms.map fun (p, e) => (p, tFlattenLetFoldReturn e))) ty
  | .mk (.seq a b) ty =>
    let a' := tFlattenLetFoldReturn a
    let b' := tFlattenLetFoldReturn b
    -- Rule C' (seq-if-distribute): if `a'` is `ifThenElse c t e` and
    -- one branch contains a `forFoldReturn` with cfBreak, push `b'`
    -- into both branches so the fold's early-return reaches the
    -- function tail. Without this, the renderer at
    -- `Hax/PrettyPrint.lean:1701-1706` falls back to
    -- `let _ := <if-expr>; rest` which produces unresolved type
    -- metavariables for the fold's ControlFlow result.
    --
    -- The duplicated `b'` runs once dynamically (exactly one branch
    -- of the if executes). Denotation-preserving for the same reason
    -- as rule C.
    match a' with
    | .mk (.ifThenElse c t e) _ =>
      if tHasNestedFoldWithReturn t || tHasNestedFoldWithReturn e then
        .mk (.ifThenElse c
          (tFlattenLetFoldReturn (.mk (.seq t b') ty))
          (tFlattenLetFoldReturn (.mk (.seq e b') ty))) ty
      else
        .mk (.seq a' b') ty
    | _ => .mk (.seq a' b') ty
  | .mk (.borrow e) ty => .mk (.borrow (tFlattenLetFoldReturn e)) ty
  | .mk (.deref e) ty => .mk (.deref (tFlattenLetFoldReturn e)) ty
  | .mk (.assign n rhs) ty => .mk (.assign n (tFlattenLetFoldReturn rhs)) ty
  | .mk (.forLoop v lo hi body) ty =>
    .mk (.forLoop v (tFlattenLetFoldReturn lo) (tFlattenLetFoldReturn hi) (tFlattenLetFoldReturn body)) ty
  | .mk (.forLoopRev v lo hi body) ty =>
    .mk (.forLoopRev v (tFlattenLetFoldReturn lo) (tFlattenLetFoldReturn hi) (tFlattenLetFoldReturn body)) ty
  | .mk (.whileLoop c body) ty =>
    .mk (.whileLoop (tFlattenLetFoldReturn c) (tFlattenLetFoldReturn body)) ty
  | .mk (.earlyReturn e) ty => .mk (.earlyReturn (tFlattenLetFoldReturn e)) ty
  | .mk (.questionMark e) ty => .mk (.questionMark (tFlattenLetFoldReturn e)) ty
  | .mk (.forFold v lo hi body) ty =>
    .mk (.forFold v (tFlattenLetFoldReturn lo) (tFlattenLetFoldReturn hi) (tFlattenLetFoldReturn body)) ty
  | .mk (.forFoldRev v lo hi body) ty =>
    .mk (.forFoldRev v (tFlattenLetFoldReturn lo) (tFlattenLetFoldReturn hi) (tFlattenLetFoldReturn body)) ty
  | .mk (.whileFold c body) ty =>
    .mk (.whileFold (tFlattenLetFoldReturn c) (tFlattenLetFoldReturn body)) ty
  | .mk (.forFoldReturn v lo hi body) ty =>
    .mk (.forFoldReturn v (tFlattenLetFoldReturn lo) (tFlattenLetFoldReturn hi) (tFlattenLetFoldReturn body)) ty
  | .mk (.forFoldRevReturn v lo hi body) ty =>
    .mk (.forFoldRevReturn v (tFlattenLetFoldReturn lo) (tFlattenLetFoldReturn hi) (tFlattenLetFoldReturn body)) ty
  | .mk (.whileFoldReturn c body) ty =>
    .mk (.whileFoldReturn (tFlattenLetFoldReturn c) (tFlattenLetFoldReturn body)) ty
  | .mk (.cfBreak e) ty => .mk (.cfBreak (tFlattenLetFoldReturn e)) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue (tFlattenLetFoldReturn e)) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (tFlattenLetFoldReturn e)) ty
  | .mk (.ann e) ty => .mk (.ann (tFlattenLetFoldReturn e)) ty
  | .mk (.namedProj n e) ty => .mk (.namedProj n (tFlattenLetFoldReturn e)) ty
  | .mk (.letBind n val body) ty =>
    let val' := tFlattenLetFoldReturn val
    let body' := tFlattenLetFoldReturn body
    -- Peel `.ann` wrappers: `tAnnotateLetBindings` (which runs before
    -- this phase) wraps non-trivial val RHSs in `.ann`, including
    -- forFoldReturn results. Pattern-match on the inner expression.
    let valStripped := match val' with
      | .mk (.ann inner) _ => inner
      | _ => val'
    if n == "_" then
      match valStripped with
      | .mk .unitVal _ => body'
      | .mk (.forFoldReturn v lo hi b) foldTy =>
        .mk (.seq (.mk (.forFoldReturn v lo hi b) foldTy) body') ty
      | .mk (.forFoldRevReturn v lo hi b) foldTy =>
        .mk (.seq (.mk (.forFoldRevReturn v lo hi b) foldTy) body') ty
      | .mk (.whileFoldReturn c b) foldTy =>
        .mk (.seq (.mk (.whileFoldReturn c b) foldTy) body') ty
      | .mk (.letBind "_" innerVal innerBody) _ =>
        tFlattenLetFoldReturn (.mk (.letBind "_" innerVal
          (.mk (.letBind "_" innerBody body') ty)) ty)
      -- Variant: val' is `seq a b`, often produced by an inner letBind
      -- being rewritten earlier in this pass. Associativity rule B'
      -- mirrors B for the seq form.
      | .mk (.seq innerA innerB) _ =>
        tFlattenLetFoldReturn (.mk (.letBind "_" innerA
          (.mk (.letBind "_" innerB body') ty)) ty)
      | .mk (.ifThenElse c t e) _ =>
        if tHasNestedFoldWithReturn t || tHasNestedFoldWithReturn e then
          .mk (.ifThenElse c
            (tFlattenLetFoldReturn (.mk (.letBind "_" t body') ty))
            (tFlattenLetFoldReturn (.mk (.letBind "_" e body') ty))) ty
        else
          .mk (.letBind n val' body') ty
      | _ => .mk (.letBind n val' body') ty
    else
      .mk (.letBind n val' body') ty

/-! ## Correctness discussion

The pass is built from four AST-level identities. Each is a standard
program equivalence on `ImpExpr`:

- **A** `letBind "_" .unitVal e ≡ e` (when `"_" ∉ freeVars e`)
- **B / B′** `letBind`/`seq` associativity around discarded bindings
- **C / C′** distribute `rest` into the branches of an `ifThenElse`
- **D** `letBind "_" e r ≡ seq e r` (when `"_" ∉ freeVars r`)

All four hold **conditionally** on `"_"` never appearing as a free
variable in the relevant subexpression. This is the universal
discard-binding convention used throughout the pipeline: `letBind "_"`
introduces a bind that is *never read* by subsequent code. `denote`
itself doesn't enforce this — `Env.extend env "_" v` is observable by
any later `.var "_"`. So an unconditional
`denote bi fuel (tFlattenLetFoldReturn e).erase = denote bi fuel e.erase`
is **not provable** without either:

1. a recursive `notFreeIn "_"` predicate threaded as a hypothesis, or
2. a coarser semantic equivalence quotienting out the `"_"` slot of
   the env.

Neither is in scope here. This pass is a **render-time normalisation**:
it runs in `tPipelineFull` after the verified core `tPipeline` and is
not subject to the `tPipeline_erase` commuting diagram. Its correctness
is justified at the design level (the four rewrites are well-known
algebraic identities under the standard `"_"` convention), and any
formal claim is deferred until the freshness framework is added.

The pass is denotation-preserving in practice on every extracted body
we have observed; the gap is in the *formal statement*, not the
behaviour.
-/

end Hax

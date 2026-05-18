/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr

/-!
# Typed phase: `tFixProjectionPaths`

Typed analog of the untyped `fixProjectionPaths` rewriter in
`Hax/PrettyPrint.lean`. Rewrites every `.proj e i` whose receiver `e`
returns a right-associated tuple of arity `> 2` into the correct
nested `.proj` chain.

For right-associated tuples `(a, b, c)` (encoded as `(a, (b, c))`),
accessing index `2` requires the path `.2.1` (i.e. `.proj (.proj e 1) 0`),
not the flat `.proj e 2` which would render as `.3` and miss the nesting.

## Key difference vs the untyped rewriter

The untyped version threads an `arityMap : List (String × Nat)` carrying
per-name return arities (struct field counts, dep return tuple arity),
populated by heuristic propagation through let-bindings. The typed
version is sharper: it reads `e.ty` directly. When `e.ty` is
`.tuple elems`, the arity is `elems.length`. No map, no propagation,
no heuristic.

## Variable receivers

Like the untyped rewriter, projections on bare variables are left alone
— they are part of tuple destructuring patterns handled downstream by
`extractTupleDestr`. Only projections on non-variable receivers (typically
direct app calls like `(derive_keys x).2`) are rewritten.

## Verification

This file intentionally omits an `erase` commuting theorem. The typed
rewriter dispatches on `e.ty`; the untyped one dispatches on a populated
`arityMap`. They agree on well-typed inputs whose `arityMap` is in sync
with the carried types, but a syntactic erase equation requires a
`WellTyped` predicate that is follow-up work.
-/

namespace Hax

namespace TFixProjectionPaths

/-- Return the tuple arity of an `ImpType`, or `0` if it is not a tuple.
    A tuple of length `≤ 2` already projects flatly (right-association
    of `A × B` is just a pair), so callers treat `arity ≤ 2` as a no-op. -/
def tupleArity : ImpType → Nat
  | .tuple elems => elems.length
  | _ => 0

/-- Build the nested projection chain for `idx` out of a right-associated
    tuple of `arity`. The chain mirrors how `A × B × C × D` is encoded
    as `A × (B × (C × D))`:

    - `idx = 0` → `.proj e 0` (head)
    - `arity ≤ 2` → `.proj e idx` (no nesting needed)
    - `arity > 2, idx > 0` → recurse on `.proj e 1` with `arity - 1`,
      `idx - 1` (peel one tail).

    The outer wrapper type carried on each constructed node is unknown
    at this point (we are reshaping a single projection's surface
    rendering, not its denotation), so we reuse the input `outTy` for
    the final node and `.unit` for intermediate tail nodes — these are
    not consumed elsewhere; only `.kind` is read by the renderer. -/
def buildNestedProj (outTy : ImpType) : TExpr → Nat → Nat → TExpr
  | e, idx, arity =>
    if arity ≤ 2 ∨ idx = 0 then
      .mk (.proj e idx) outTy
    else
      let tail : TExpr := .mk (.proj e 1) outTy
      buildNestedProj outTy tail (idx - 1) (arity - 1)
  termination_by _ _ arity => arity

end TFixProjectionPaths

open TFixProjectionPaths in
/-- Typed projection-path fixer over `TExpr`. Walks the tree, and at
    every `.mk (.proj e i) ty` node whose recursively-rewritten `e'`
    has a non-variable kind and `e'.ty` is `.tuple elems` with
    `elems.length > 2`, rebuilds the projection as a nested chain via
    `buildNestedProj`. Outer types are preserved on every other node.

    Mirrors the structural recursion of `tQualifyProjections` and
    `tRewriteAppName`. -/
def tFixProjectionPaths : TExpr → TExpr
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty =>
    .mk (.letBind n (tFixProjectionPaths val) (tFixProjectionPaths body)) ty
  | .mk (.app f args) ty =>
    .mk (.app f (mapExpr args)) ty
  | .mk (.tuple elems) ty =>
    .mk (.tuple (mapExpr elems)) ty
  | .mk (.proj e i) ty =>
    let e' := tFixProjectionPaths e
    match e' with
    -- Leave variable projections to downstream tuple destructuring.
    | .mk (.var _) _ => .mk (.proj e' i) ty
    | _ =>
      let arity := tupleArity e'.ty
      if arity > 2 then
        buildNestedProj ty e' i arity
      else
        .mk (.proj e' i) ty
  | .mk (.ifThenElse c t e) ty =>
    .mk (.ifThenElse (tFixProjectionPaths c)
                     (tFixProjectionPaths t)
                     (tFixProjectionPaths e)) ty
  | .mk (.match_ scrut arms) ty =>
    .mk (.match_ (tFixProjectionPaths scrut) (mapArms arms)) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq e1 e2) ty =>
    .mk (.seq (tFixProjectionPaths e1) (tFixProjectionPaths e2)) ty
  | .mk (.borrow e) ty => .mk (.borrow (tFixProjectionPaths e)) ty
  | .mk (.deref e) ty => .mk (.deref (tFixProjectionPaths e)) ty
  | .mk (.assign n rhs) ty => .mk (.assign n (tFixProjectionPaths rhs)) ty
  | .mk (.forLoop v lo hi body) ty =>
    .mk (.forLoop v (tFixProjectionPaths lo)
                    (tFixProjectionPaths hi)
                    (tFixProjectionPaths body)) ty
  | .mk (.forLoopRev v lo hi body) ty =>
    .mk (.forLoopRev v (tFixProjectionPaths lo)
                       (tFixProjectionPaths hi)
                       (tFixProjectionPaths body)) ty
  | .mk (.whileLoop c body) ty =>
    .mk (.whileLoop (tFixProjectionPaths c) (tFixProjectionPaths body)) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk (.break_ (some e)) ty =>
    .mk (.break_ (some (tFixProjectionPaths e))) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty => .mk (.earlyReturn (tFixProjectionPaths e)) ty
  | .mk (.questionMark e) ty => .mk (.questionMark (tFixProjectionPaths e)) ty
  | .mk (.forFold v lo hi body) ty =>
    .mk (.forFold v (tFixProjectionPaths lo)
                    (tFixProjectionPaths hi)
                    (tFixProjectionPaths body)) ty
  | .mk (.forFoldRev v lo hi body) ty =>
    .mk (.forFoldRev v (tFixProjectionPaths lo)
                       (tFixProjectionPaths hi)
                       (tFixProjectionPaths body)) ty
  | .mk (.whileFold c body) ty =>
    .mk (.whileFold (tFixProjectionPaths c) (tFixProjectionPaths body)) ty
  | .mk (.forFoldReturn v lo hi body) ty =>
    .mk (.forFoldReturn v (tFixProjectionPaths lo)
                          (tFixProjectionPaths hi)
                          (tFixProjectionPaths body)) ty
  | .mk (.forFoldRevReturn v lo hi body) ty =>
    .mk (.forFoldRevReturn v (tFixProjectionPaths lo)
                             (tFixProjectionPaths hi)
                             (tFixProjectionPaths body)) ty
  | .mk (.whileFoldReturn c body) ty =>
    .mk (.whileFoldReturn (tFixProjectionPaths c) (tFixProjectionPaths body)) ty
  | .mk (.cfBreak e) ty => .mk (.cfBreak (tFixProjectionPaths e)) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue (tFixProjectionPaths e)) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (tFixProjectionPaths e)) ty
  | .mk (.ann e) ty => .mk (.ann (tFixProjectionPaths e)) ty
  | .mk (.namedProj n e) ty => .mk (.namedProj n (tFixProjectionPaths e)) ty
where
  mapExpr : List TExpr → List TExpr
    | [] => []
    | e :: es => tFixProjectionPaths e :: mapExpr es
  mapArms : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tFixProjectionPaths e) :: mapArms rest

@[simp] theorem tFixProjectionPaths.mapExpr_eq (es : List TExpr) :
    tFixProjectionPaths.mapExpr es = es.map tFixProjectionPaths := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [tFixProjectionPaths.mapExpr, ih]

@[simp] theorem tFixProjectionPaths.mapArms_eq (arms : List (ImpPat × TExpr)) :
    tFixProjectionPaths.mapArms arms =
      arms.map fun (p, e) => (p, tFixProjectionPaths e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [tFixProjectionPaths.mapArms, ih]

/-- `buildNestedProj` always wraps the outermost result in the supplied
    `outTy`. (Intermediate `.proj _ 1` nodes also use `outTy` for the
    same reason.) -/
theorem TFixProjectionPaths.buildNestedProj_ty
    (outTy : ImpType) (e : TExpr) (idx arity : Nat) :
    (TFixProjectionPaths.buildNestedProj outTy e idx arity).ty = outTy := by
  induction arity using Nat.strongRecOn generalizing e idx with
  | ind arity ih =>
    unfold TFixProjectionPaths.buildNestedProj
    split
    · rfl
    · rename_i hsplit
      have harity : arity > 2 := by omega
      exact ih (arity - 1) (by omega) _ _

/-- Outer-type annotation preservation. The rewriter expands a single
    `.proj e i` with `i > 1` into a chain of `.proj _ 0/1` nodes,
    but the outermost node's `ty` (the element type at position `i`)
    is preserved verbatim. -/
theorem tFixProjectionPaths_ty (e : TExpr) :
    (tFixProjectionPaths e).ty = e.ty := by
  cases e with
  | mk kind ty =>
    cases kind with
    | proj e' i =>
      show (tFixProjectionPaths (.mk (.proj e' i) ty)).ty = ty
      unfold tFixProjectionPaths
      generalize tFixProjectionPaths e' = e''
      cases e'' with
      | mk kind'' ty'' =>
        cases kind'' with
        | var _ => rfl
        | _ =>
          simp only
          split
          · exact TFixProjectionPaths.buildNestedProj_ty _ _ _ _
          · rfl
    | break_ eo => cases eo <;> rfl
    | _ => rfl

-- NOTE: `tFixProjectionPaths_erase` is intentionally not stated here.
-- The typed rewriter reads `e.ty` (a structural tuple arity); the
-- untyped rewriter consults `arityMap : List (String × Nat)` populated
-- heuristically by let-binding propagation. The two agree under a
-- `WellTyped + arityMap-in-sync` predicate but not on arbitrary inputs.

end Hax

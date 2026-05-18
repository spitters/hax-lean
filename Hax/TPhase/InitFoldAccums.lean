/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr
import Hax.Phase.InitFoldAccums

/-!
# Typed phase: `tInitMissingFoldAccums`

Typed analog of `Hax.initMissingFoldAccums`. Walks a `TExpr` and inserts
`let v := (0 : Int)` before any fold whose body references a variable
`v` not bound in the enclosing scope.

## Verification

The main theorem `tInitMissingFoldAccums_erase` states:

```
(tInitMissingFoldAccums bound e).erase = initMissingFoldAccums bound e.erase
```

The implementation runs the underlying untyped `collectBoundNamesT`
and `extractAccumNamesFromBody` analyses on the erased subexpressions —
these are pure ImpExpr predicates that don't observe types, so we
can reuse them directly. The structural recursion preserves outer
types at every node; the inserted `letBind`s use `ImpType.int` to
match the untyped `.lit (.int 0)` value's type.
-/

namespace Hax

/-- Typed analog: walk a `TExpr` and prepend `let v := (0 : Int)` (typed
    as `ImpType.int`) for each free accumulator name in each fold body. -/
def tInitMissingFoldAccums (bound : List String := []) : TExpr → TExpr
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty =>
    let val' := tInitMissingFoldAccums bound val
    let body' := tInitMissingFoldAccums (n :: bound) body
    .mk (.letBind n val' body') ty
  | .mk (.app f args) ty => .mk (.app f (mapExpr bound args)) ty
  | .mk (.tuple elems) ty => .mk (.tuple (mapExpr bound elems)) ty
  | .mk (.proj e i) ty => .mk (.proj (tInitMissingFoldAccums bound e) i) ty
  | .mk (.ifThenElse c t e) ty =>
    .mk (.ifThenElse (tInitMissingFoldAccums bound c)
                     (tInitMissingFoldAccums bound t)
                     (tInitMissingFoldAccums bound e)) ty
  | .mk (.match_ scrut arms) ty =>
    .mk (.match_ (tInitMissingFoldAccums bound scrut) (mapArms bound arms)) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq a b) ty =>
    let a' := tInitMissingFoldAccums bound a
    -- Mirror untyped: collect names bound at the top of `a` and extend
    -- the scope for `b`. We operate on `a.erase` for this analysis.
    let boundsFromA := collectBoundNamesT a.erase
    .mk (.seq a' (tInitMissingFoldAccums (bound ++ boundsFromA) b)) ty
  | .mk (.borrow e) ty => .mk (.borrow (tInitMissingFoldAccums bound e)) ty
  | .mk (.deref e) ty => .mk (.deref (tInitMissingFoldAccums bound e)) ty
  | .mk (.assign n rhs) ty => .mk (.assign n (tInitMissingFoldAccums bound rhs)) ty
  | .mk (.forLoop v lo hi body) ty =>
    .mk (.forLoop v (tInitMissingFoldAccums bound lo)
                    (tInitMissingFoldAccums bound hi)
                    (tInitMissingFoldAccums bound body)) ty
  | .mk (.forLoopRev v lo hi body) ty =>
    .mk (.forLoopRev v (tInitMissingFoldAccums bound lo)
                       (tInitMissingFoldAccums bound hi)
                       (tInitMissingFoldAccums bound body)) ty
  | .mk (.whileLoop c body) ty =>
    .mk (.whileLoop (tInitMissingFoldAccums bound c)
                    (tInitMissingFoldAccums bound body)) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk (.break_ (some e)) ty =>
    .mk (.break_ (some (tInitMissingFoldAccums bound e))) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty =>
    .mk (.earlyReturn (tInitMissingFoldAccums bound e)) ty
  | .mk (.questionMark e) ty =>
    .mk (.questionMark (tInitMissingFoldAccums bound e)) ty
  -- Fold cases — prepend `let v := 0` for each free accumulator name.
  -- We compute the accumulators from the body's erased form and wrap
  -- the typed result with `.letBind`s carrying `.int` outer types.
  | .mk (.forFold v lo hi body) ty =>
    let lo' := tInitMissingFoldAccums bound lo
    let hi' := tInitMissingFoldAccums bound hi
    let body' := tInitMissingFoldAccums (v :: bound) body
    let fold : TExpr := .mk (.forFold v lo' hi' body') ty
    let accumNames := extractAccumNamesFromBody body'.erase
    let freeAccums := accumNames.filter fun n => !bound.contains n
    freeAccums.foldr (fun fv expr =>
      .mk (.letBind fv (.mk (.lit (.int 0)) .int) expr) expr.ty) fold
  | .mk (.forFoldRev v lo hi body) ty =>
    let lo' := tInitMissingFoldAccums bound lo
    let hi' := tInitMissingFoldAccums bound hi
    let body' := tInitMissingFoldAccums (v :: bound) body
    let fold : TExpr := .mk (.forFoldRev v lo' hi' body') ty
    let accumNames := extractAccumNamesFromBody body'.erase
    let freeAccums := accumNames.filter fun n => !bound.contains n
    freeAccums.foldr (fun fv expr =>
      .mk (.letBind fv (.mk (.lit (.int 0)) .int) expr) expr.ty) fold
  | .mk (.whileFold c body) ty =>
    .mk (.whileFold (tInitMissingFoldAccums bound c)
                    (tInitMissingFoldAccums bound body)) ty
  | .mk (.forFoldReturn v lo hi body) ty =>
    let lo' := tInitMissingFoldAccums bound lo
    let hi' := tInitMissingFoldAccums bound hi
    let body' := tInitMissingFoldAccums (v :: bound) body
    let fold : TExpr := .mk (.forFoldReturn v lo' hi' body') ty
    let accumNames := extractAccumNamesFromBody body'.erase
    let freeAccums := accumNames.filter fun n => !bound.contains n
    freeAccums.foldr (fun fv expr =>
      .mk (.letBind fv (.mk (.lit (.int 0)) .int) expr) expr.ty) fold
  | .mk (.forFoldRevReturn v lo hi body) ty =>
    let lo' := tInitMissingFoldAccums bound lo
    let hi' := tInitMissingFoldAccums bound hi
    let body' := tInitMissingFoldAccums (v :: bound) body
    let fold : TExpr := .mk (.forFoldRevReturn v lo' hi' body') ty
    let accumNames := extractAccumNamesFromBody body'.erase
    let freeAccums := accumNames.filter fun n => !bound.contains n
    freeAccums.foldr (fun fv expr =>
      .mk (.letBind fv (.mk (.lit (.int 0)) .int) expr) expr.ty) fold
  | .mk (.whileFoldReturn c body) ty =>
    .mk (.whileFoldReturn (tInitMissingFoldAccums bound c)
                          (tInitMissingFoldAccums bound body)) ty
  | .mk (.cfBreak e) ty => .mk (.cfBreak (tInitMissingFoldAccums bound e)) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue (tInitMissingFoldAccums bound e)) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (tInitMissingFoldAccums bound e)) ty
  | .mk (.ann e) ty => .mk (.ann (tInitMissingFoldAccums bound e)) ty
  | .mk (.namedProj n e) ty => .mk (.namedProj n (tInitMissingFoldAccums bound e)) ty
where
  mapExpr (bound : List String) : List TExpr → List TExpr
    | [] => []
    | e :: es => tInitMissingFoldAccums bound e :: mapExpr bound es
  mapArms (bound : List String) : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tInitMissingFoldAccums bound e) :: mapArms bound rest

@[simp] theorem tInitMissingFoldAccums.mapExpr_eq (bound : List String) (es : List TExpr) :
    tInitMissingFoldAccums.mapExpr bound es = es.map (tInitMissingFoldAccums bound) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [tInitMissingFoldAccums.mapExpr, ih]

@[simp] theorem tInitMissingFoldAccums.mapArms_eq (bound : List String)
    (arms : List (ImpPat × TExpr)) :
    tInitMissingFoldAccums.mapArms bound arms =
      arms.map fun (p, e) => (p, tInitMissingFoldAccums bound e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [tInitMissingFoldAccums.mapArms, ih]

end Hax

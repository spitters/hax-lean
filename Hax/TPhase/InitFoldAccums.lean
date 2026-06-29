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

The main theorem `tInitMissingFoldAccums_erase` (proved below) states:

```
(tInitMissingFoldAccums bound e).erase = initMissingFoldAccums bound e.erase
```

The implementation runs the underlying untyped `collectBoundNamesT`
and `extractAccumNamesFromBody` analyses on the erased subexpressions —
these are pure ImpExpr predicates that don't observe types, so we
can reuse them directly. The structural recursion preserves outer
types at every node; the inserted `letBind`s use `ImpType.int` to
match the untyped `.lit (.int 0)` value's type.

Both passes recurse defensively into pre-pipeline constructors
(`.borrow`, `.deref`, `.assign`, loop variants, `.earlyReturn`,
`.questionMark`) so the erase commutation goes through structurally
even though those constructors are eliminated by earlier phases in
practice.
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
  | .mk (.lam ps body) ty => .mk (.lam ps (tInitMissingFoldAccums (ps ++ bound) body)) ty
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

/-- The `letBind`-prepending `foldr` preserves the outer `ty` of its
    starting expression — each iteration wraps with `expr.ty`, which on
    the first step is `fold.ty`, and on every subsequent step is the
    previous wrapper's `ty` (also `fold.ty`). -/
private theorem foldr_letBindLit_ty (names : List String) (fold : TExpr) :
    (names.foldr
        (fun fv expr =>
          TExpr.mk (.letBind fv (.mk (.lit (.int 0)) .int) expr) expr.ty)
        fold).ty
      = fold.ty := by
  induction names with
  | nil => rfl
  | cons n ns ih =>
    show (TExpr.mk (.letBind n _ _) _).ty = fold.ty
    show _ = fold.ty
    exact ih

/-- Outer-type preservation for `tInitMissingFoldAccums`. Every node's
    `ty` annotation is preserved by the phase, including the freshly
    inserted `letBind`s at fold sites (which carry the fold's outer
    `ty` per `foldr_letBindLit_ty`). -/
theorem tInitMissingFoldAccums_ty (bound : List String) (e : TExpr) :
    (tInitMissingFoldAccums bound e).ty = e.ty := by
  cases e with
  | mk kind ty =>
    cases kind with
    | forFold _ _ _ _ =>
      show (List.foldr (fun fv expr =>
              TExpr.mk (.letBind fv (.mk (.lit (.int 0)) .int) expr) expr.ty) _ _).ty = ty
      exact foldr_letBindLit_ty _ _
    | forFoldRev _ _ _ _ =>
      show (List.foldr (fun fv expr =>
              TExpr.mk (.letBind fv (.mk (.lit (.int 0)) .int) expr) expr.ty) _ _).ty = ty
      exact foldr_letBindLit_ty _ _
    | forFoldReturn _ _ _ _ =>
      show (List.foldr (fun fv expr =>
              TExpr.mk (.letBind fv (.mk (.lit (.int 0)) .int) expr) expr.ty) _ _).ty = ty
      exact foldr_letBindLit_ty _ _
    | forFoldRevReturn _ _ _ _ =>
      show (List.foldr (fun fv expr =>
              TExpr.mk (.letBind fv (.mk (.lit (.int 0)) .int) expr) expr.ty) _ _).ty = ty
      exact foldr_letBindLit_ty _ _
    | break_ eo => cases eo <;> rfl
    | _ => rfl

/-- Erasing a `letBind`-prepending `foldr` commutes with applying the
    same `foldr` over erased nodes. -/
private theorem foldr_letBindLit_erase (names : List String) (fold : TExpr) :
    (names.foldr
        (fun fv expr =>
          TExpr.mk (.letBind fv (.mk (.lit (.int 0)) .int) expr) expr.ty)
        fold).erase
      = names.foldr (fun fv expr => .letBind fv (.lit (.int 0)) expr) fold.erase := by
  induction names with
  | nil => rfl
  | cons n ns ih => simp [List.foldr, TExpr.erase, ih]

/-- Erase commutation for `tInitMissingFoldAccums`. The typed pass operates
    on `TExpr` (with type annotations on every `.letBind` insertion); the
    untyped pass operates on `ImpExpr` directly. After erasure they produce
    identical ImpExpr trees because both compute `accumNames` from the same
    erased body and prepend the same `letBind v (.lit (.int 0))` chain. -/
theorem tInitMissingFoldAccums_erase (bound : List String) (e : TExpr) :
    (tInitMissingFoldAccums bound e).erase
      = initMissingFoldAccums bound e.erase := by
  induction e using TExpr.ind generalizing bound with
  | lit | var | unitVal | continue_ | break_none =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums]
  | lam _ _ _ ih =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih]
  | letBind _ _ _ _ ih1 ih2 =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih1, ih2]
  | app _ _ args ih =>
    simp only [tInitMissingFoldAccums, tInitMissingFoldAccums.mapExpr_eq,
      TExpr.erase, TExpr.eraseList_eq, initMissingFoldAccums,
      initMissingFoldAccums.mapExpr_eq, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha bound)
  | tuple _ elems ih =>
    simp only [tInitMissingFoldAccums, tInitMissingFoldAccums.mapExpr_eq,
      TExpr.erase, TExpr.eraseList_eq, initMissingFoldAccums,
      initMissingFoldAccums.mapExpr_eq, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha bound)
  | proj _ _ _ ih =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih]
  | ifThenElse _ _ _ _ ih1 ih2 ih3 =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih1, ih2, ih3]
  | match_ _ _ arms ih1 ih2 =>
    simp only [tInitMissingFoldAccums, tInitMissingFoldAccums.mapArms_eq,
      TExpr.erase, TExpr.eraseArms_eq, initMissingFoldAccums,
      initMissingFoldAccums.mapArms_eq, ih1, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun ⟨p, e⟩ hpa => by
      simp only [ih2 (p, e) hpa])
  | seq _ a b iha ihb =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, iha, ihb]
  | borrow _ _ ih =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih]
  | deref _ _ ih =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih]
  | assign _ _ _ ih =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih]
  | forLoop _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih1, ih2, ih3]
  | forLoopRev _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih1, ih2, ih3]
  | whileLoop _ _ _ ih1 ih2 =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih1, ih2]
  | break_some _ _ ih =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih]
  | earlyReturn _ _ ih =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih]
  | questionMark _ _ ih =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih]
  | forFold _ _ _ _ _ ihlo ihhi ihbody =>
    simp only [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums,
      foldr_letBindLit_erase, ihbody, ihlo, ihhi]
  | forFoldRev _ _ _ _ _ ihlo ihhi ihbody =>
    simp only [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums,
      foldr_letBindLit_erase, ihbody, ihlo, ihhi]
  | whileFold _ _ _ ih1 ih2 =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih1, ih2]
  | forFoldReturn _ _ _ _ _ ihlo ihhi ihbody =>
    simp only [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums,
      foldr_letBindLit_erase, ihbody, ihlo, ihhi]
  | forFoldRevReturn _ _ _ _ _ ihlo ihhi ihbody =>
    simp only [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums,
      foldr_letBindLit_erase, ihbody, ihlo, ihhi]
  | whileFoldReturn _ _ _ ih1 ih2 =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih1, ih2]
  | cfBreak _ _ ih =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih]
  | cfContinue _ _ ih =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih]
  | cfBreakContinue _ _ ih =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih]
  | ann _ _ ih =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih]
  | namedProj _ _ _ ih =>
    simp [tInitMissingFoldAccums, TExpr.erase, initMissingFoldAccums, ih]

end Hax

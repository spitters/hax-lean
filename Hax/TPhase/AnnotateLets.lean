/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr
import Hax.Pipeline

/-!
# Typed Phase 6 (post-pipeline): Annotate Let Bindings

Walks a `TExpr` and wraps the RHS of each let-binding whose value type
is non-trivial (not Int/Unknown/Unit and not a param-shadowing `let n := var n`)
with the denotation-identity marker `.ann`. The PrettyPrint layer then
renders these as Lean type ascriptions `(val : T)`, propagating the
JSON-declared type through Lean's elaboration at use sites.

Phase semantics: **denotational identity**. The `.ann` constructor erases
to its inner expression (see `TExpr.erase`), so the untyped pipeline never
sees `.ann` and all existing correctness theorems carry through.

## Verification

The only obligation is to show that `tAnnotateLetBindings` is erase-preserving:

```
(tAnnotateLetBindings e).erase = e.erase
```

This is proved by structural induction (`TExpr.ind`), using the fact that
`.ann e ty` erases to `e.erase`.
-/

namespace Hax

/-- Is this an "Int-like" / trivial type for which we don't need an
    explicit annotation? Mirrors the renderer's surface-type collapse
    rules (`toLeanTypeStrSurface`) so we only wrap let-bindings whose
    rendering will produce a non-`Int` Lean type. -/
private def isTrivialAnnotType (ty : ImpType) : Bool :=
  match ty with
  | .unknown => true
  -- All integer-like types collapse to `Int` in the untyped Runtime.
  | .int | .uint _ | .sint _ => true
  -- Function types collapse to `Int` (function values are not first-class
  -- in the untyped Runtime). Annotating `let f := Hax.beq` with
  -- `(... : Int)` would produce a type mismatch.
  | .fn _ _ => true
  -- Type variables collapse to `Int` in the surface stringifier.
  | .typeVar _ => true
  -- Tuples skip annotation: Lean infers the tuple type from the destructure
  -- pattern + the function's return type. Annotating risks emitting an
  -- arity-wrong type when the JSON's call-site `ty` differs from the
  -- function's declared return type (observed on AEGIS / AESGCMSIV /
  -- OPAQUE / SPDZ where the JSON encodes the call result as a 2-tuple
  -- but the function returns a 3-tuple). Skipping the annotation is
  -- always safe; the destructure pattern fully determines the binding's
  -- shape downstream.
  | .tuple _ => true
  | _ => false

/-- Should this let-binding's RHS receive a `.ann` wrapper?

    Skip when:
    - The RHS type is trivial (Int/Unknown/Sized integer).
    - The RHS is `var v` and the bound name `n == v` (param-shadowing
      pattern from `extractParams`; an outer parameter annotation
      already pins the type). -/
private def shouldAnnotate (n : String) (val : TExpr) : Bool :=
  if isTrivialAnnotType val.ty then false
  else match val with
    | .mk (.var v) _ => n != v  -- annotate non-param-shadow only
    | _ => true

/-- Wrap a `TExpr` with `.ann` (preserving its outer type) IF the
    annotation predicate fires; otherwise return unchanged. -/
@[inline] private def maybeAnn (cond : Bool) (e : TExpr) : TExpr :=
  if cond then .mk (.ann e) e.ty else e

/-- Phase 6 transformation: annotate non-trivial let-binding RHSs with `.ann`.
    Every other constructor is a structural traversal (preserve outer type,
    recurse into children). -/
def tAnnotateLetBindings : TExpr → TExpr
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty =>
      let val' := tAnnotateLetBindings val
      let body' := tAnnotateLetBindings body
      let valAnnotated := maybeAnn (shouldAnnotate n val) val'
      .mk (.letBind n valAnnotated body') ty
  | .mk (.app f args) ty => .mk (.app f (mapExpr args)) ty
  | .mk (.tuple elems) ty => .mk (.tuple (mapExpr elems)) ty
  | .mk (.proj e i) ty => .mk (.proj (tAnnotateLetBindings e) i) ty
  | .mk (.ifThenElse c t e) ty =>
      .mk (.ifThenElse (tAnnotateLetBindings c) (tAnnotateLetBindings t) (tAnnotateLetBindings e)) ty
  | .mk (.match_ scrut arms) ty =>
      .mk (.match_ (tAnnotateLetBindings scrut) (mapArms arms)) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq e1 e2) ty => .mk (.seq (tAnnotateLetBindings e1) (tAnnotateLetBindings e2)) ty
  | .mk (.borrow e) ty => .mk (.borrow (tAnnotateLetBindings e)) ty
  | .mk (.deref e) ty => .mk (.deref (tAnnotateLetBindings e)) ty
  | .mk (.assign n rhs) ty => .mk (.assign n (tAnnotateLetBindings rhs)) ty
  | .mk (.forLoop v lo hi body) ty =>
      .mk (.forLoop v (tAnnotateLetBindings lo) (tAnnotateLetBindings hi) (tAnnotateLetBindings body)) ty
  | .mk (.forLoopRev v lo hi body) ty =>
      .mk (.forLoopRev v (tAnnotateLetBindings lo) (tAnnotateLetBindings hi) (tAnnotateLetBindings body)) ty
  | .mk (.whileLoop c body) ty =>
      .mk (.whileLoop (tAnnotateLetBindings c) (tAnnotateLetBindings body)) ty
  | .mk (.break_ (some e)) ty => .mk (.break_ (some (tAnnotateLetBindings e))) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty => .mk (.earlyReturn (tAnnotateLetBindings e)) ty
  | .mk (.questionMark e) ty => .mk (.questionMark (tAnnotateLetBindings e)) ty
  | .mk (.forFold v lo hi body) ty =>
      .mk (.forFold v (tAnnotateLetBindings lo) (tAnnotateLetBindings hi) (tAnnotateLetBindings body)) ty
  | .mk (.forFoldRev v lo hi body) ty =>
      .mk (.forFoldRev v (tAnnotateLetBindings lo) (tAnnotateLetBindings hi) (tAnnotateLetBindings body)) ty
  | .mk (.whileFold c body) ty =>
      .mk (.whileFold (tAnnotateLetBindings c) (tAnnotateLetBindings body)) ty
  | .mk (.forFoldReturn v lo hi body) ty =>
      .mk (.forFoldReturn v (tAnnotateLetBindings lo) (tAnnotateLetBindings hi) (tAnnotateLetBindings body)) ty
  | .mk (.forFoldRevReturn v lo hi body) ty =>
      .mk (.forFoldRevReturn v (tAnnotateLetBindings lo) (tAnnotateLetBindings hi) (tAnnotateLetBindings body)) ty
  | .mk (.whileFoldReturn c body) ty =>
      .mk (.whileFoldReturn (tAnnotateLetBindings c) (tAnnotateLetBindings body)) ty
  | .mk (.cfBreak e) ty => .mk (.cfBreak (tAnnotateLetBindings e)) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue (tAnnotateLetBindings e)) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (tAnnotateLetBindings e)) ty
  | .mk (.ann e) ty => .mk (.ann (tAnnotateLetBindings e)) ty
  | .mk (.namedProj n e) ty => .mk (.namedProj n (tAnnotateLetBindings e)) ty
where
  mapExpr : List TExpr → List TExpr
    | [] => []
    | e :: es => tAnnotateLetBindings e :: mapExpr es
  mapArms : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tAnnotateLetBindings e) :: mapArms rest

@[simp] theorem tAnnotateLetBindings.mapExpr_eq (es : List TExpr) :
    tAnnotateLetBindings.mapExpr es = es.map tAnnotateLetBindings := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [tAnnotateLetBindings.mapExpr, ih]

@[simp] theorem tAnnotateLetBindings.mapArms_eq (arms : List (ImpPat × TExpr)) :
    tAnnotateLetBindings.mapArms arms = arms.map fun (p, e) => (p, tAnnotateLetBindings e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [tAnnotateLetBindings.mapArms, ih]

/-- `maybeAnn` is denotation-identity under erasure: wrapping with `.ann`
    or not produces the same `ImpExpr` after erase. -/
@[simp] theorem maybeAnn_erase (cond : Bool) (e : TExpr) :
    (maybeAnn cond e).erase = e.erase := by
  unfold maybeAnn
  cases cond <;> simp [TExpr.erase]

/-- **Main theorem.** `tAnnotateLetBindings` is denotation-preserving via
    erasure: applying it to a TExpr and then erasing yields the same
    `ImpExpr` as just erasing. -/
theorem tAnnotateLetBindings_erase (e : TExpr) :
    (tAnnotateLetBindings e).erase = e.erase := by
  induction e using TExpr.ind with
  | lit | var | unitVal | continue_ | break_none => rfl
  | letBind _ _ _ _ ih1 ih2 =>
    simp [tAnnotateLetBindings, TExpr.erase, ih1, ih2, maybeAnn_erase]
  | seq _ _ _ ih1 ih2 =>
    simp [tAnnotateLetBindings, TExpr.erase, ih1, ih2]
  | proj _ _ _ ih => simp [tAnnotateLetBindings, TExpr.erase, ih]
  | ifThenElse _ _ _ _ ih1 ih2 ih3 =>
    simp [tAnnotateLetBindings, TExpr.erase, ih1, ih2, ih3]
  | borrow _ _ ih => simp [tAnnotateLetBindings, TExpr.erase, ih]
  | deref _ _ ih => simp [tAnnotateLetBindings, TExpr.erase, ih]
  | assign _ _ _ ih => simp [tAnnotateLetBindings, TExpr.erase, ih]
  | forLoop _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tAnnotateLetBindings, TExpr.erase, ih1, ih2, ih3]
  | forLoopRev _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tAnnotateLetBindings, TExpr.erase, ih1, ih2, ih3]
  | whileLoop _ _ _ ih1 ih2 =>
    simp [tAnnotateLetBindings, TExpr.erase, ih1, ih2]
  | break_some _ _ ih => simp [tAnnotateLetBindings, TExpr.erase, ih]
  | earlyReturn _ _ ih => simp [tAnnotateLetBindings, TExpr.erase, ih]
  | questionMark _ _ ih => simp [tAnnotateLetBindings, TExpr.erase, ih]
  | forFold _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tAnnotateLetBindings, TExpr.erase, ih1, ih2, ih3]
  | forFoldRev _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tAnnotateLetBindings, TExpr.erase, ih1, ih2, ih3]
  | whileFold _ _ _ ih1 ih2 =>
    simp [tAnnotateLetBindings, TExpr.erase, ih1, ih2]
  | forFoldReturn _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tAnnotateLetBindings, TExpr.erase, ih1, ih2, ih3]
  | forFoldRevReturn _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tAnnotateLetBindings, TExpr.erase, ih1, ih2, ih3]
  | whileFoldReturn _ _ _ ih1 ih2 =>
    simp [tAnnotateLetBindings, TExpr.erase, ih1, ih2]
  | cfBreak _ _ ih => simp [tAnnotateLetBindings, TExpr.erase, ih]
  | cfContinue _ _ ih => simp [tAnnotateLetBindings, TExpr.erase, ih]
  | cfBreakContinue _ _ ih => simp [tAnnotateLetBindings, TExpr.erase, ih]
  | ann _ _ ih => simp [tAnnotateLetBindings, TExpr.erase, ih]
  | namedProj _ _ _ ih =>
    simp [tAnnotateLetBindings, TExpr.erase, ih]
  | app _ _ args ih =>
    simp only [tAnnotateLetBindings, tAnnotateLetBindings.mapExpr_eq, TExpr.erase,
      TExpr.eraseList_eq, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha)
  | tuple _ elems ih =>
    simp only [tAnnotateLetBindings, tAnnotateLetBindings.mapExpr_eq, TExpr.erase,
      TExpr.eraseList_eq, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha)
  | match_ _ _ arms _ ih2 =>
    simp only [tAnnotateLetBindings, tAnnotateLetBindings.mapArms_eq, TExpr.erase,
      TExpr.eraseArms_eq, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun ⟨p, e⟩ hpa => by
      simp only [ih2 (p, e) hpa])

end Hax

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr
import Hax.Phase.WrapMatchArms

/-!
# Typed Phase 4.5: Wrap Match Arms with cfContinue

Typed version of `wrapMatchArmsCF` on `TExpr`, with a commuting lemma
showing that type erasure commutes with the transformation.
-/

namespace Hax

/-- Does this typed expression end in a control-flow constructor? -/
def TExpr.endsInCF : TExpr → Bool
  | .mk (.cfBreak _) _ | .mk (.cfContinue _) _ | .mk (.cfBreakContinue _) _ => true
  | .mk (.letBind _ _ body) _ => body.endsInCF
  | .mk (.seq _ e2) _ => e2.endsInCF
  | .mk (.ifThenElse _ t e) _ => t.endsInCF && e.endsInCF
  | .mk (.ann e) _ => e.endsInCF
  | _ => false

/-- Wrap with cfContinue if not already CF. -/
def TExpr.maybeWrapContinue (e : TExpr) : TExpr :=
  if e.endsInCF then e else .mk (.cfContinue e) (.controlFlow .unknown e.ty)

/-- Typed version of `wrapMatchArmsCF`. -/
def tWrapMatchArmsCF : TExpr → TExpr
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty =>
      .mk (.letBind n (tWrapMatchArmsCF val) (tWrapMatchArmsCF body)) ty
  | .mk (.app f args) ty => .mk (.app f (mapExpr args)) ty
  | .mk (.tuple elems) ty => .mk (.tuple (mapExpr elems)) ty
  | .mk (.proj e i) ty => .mk (.proj (tWrapMatchArmsCF e) i) ty
  | .mk (.ifThenElse c t e) ty =>
      .mk (.ifThenElse (tWrapMatchArmsCF c) (tWrapMatchArmsCF t) (tWrapMatchArmsCF e)) ty
  | .mk (.match_ scrut arms) ty =>
      let arms' := mapArms arms
      let anyCF := arms'.any (fun (_, b) => b.endsInCF)
      let armsWrapped := if anyCF then mapArmsWrap arms' else arms'
      .mk (.match_ (tWrapMatchArmsCF scrut) armsWrapped) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq e1 e2) ty => .mk (.seq (tWrapMatchArmsCF e1) (tWrapMatchArmsCF e2)) ty
  | .mk (.borrow e) ty => .mk (.borrow (tWrapMatchArmsCF e)) ty
  | .mk (.deref e) ty => .mk (.deref (tWrapMatchArmsCF e)) ty
  | .mk (.assign n rhs) ty => .mk (.assign n (tWrapMatchArmsCF rhs)) ty
  | .mk (.forLoop v lo hi body) ty =>
      .mk (.forLoop v (tWrapMatchArmsCF lo) (tWrapMatchArmsCF hi) (tWrapMatchArmsCF body)) ty
  | .mk (.forLoopRev v lo hi body) ty =>
      .mk (.forLoopRev v (tWrapMatchArmsCF lo) (tWrapMatchArmsCF hi) (tWrapMatchArmsCF body)) ty
  | .mk (.whileLoop c body) ty =>
      .mk (.whileLoop (tWrapMatchArmsCF c) (tWrapMatchArmsCF body)) ty
  | .mk (.break_ (some e)) ty => .mk (.break_ (some (tWrapMatchArmsCF e))) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty => .mk (.earlyReturn (tWrapMatchArmsCF e)) ty
  | .mk (.questionMark e) ty => .mk (.questionMark (tWrapMatchArmsCF e)) ty
  | .mk (.forFold v lo hi body) ty =>
      .mk (.forFold v (tWrapMatchArmsCF lo) (tWrapMatchArmsCF hi) (tWrapMatchArmsCF body)) ty
  | .mk (.forFoldRev v lo hi body) ty =>
      .mk (.forFoldRev v (tWrapMatchArmsCF lo) (tWrapMatchArmsCF hi) (tWrapMatchArmsCF body)) ty
  | .mk (.whileFold c body) ty =>
      .mk (.whileFold (tWrapMatchArmsCF c) (tWrapMatchArmsCF body)) ty
  | .mk (.forFoldReturn v lo hi body) ty =>
      .mk (.forFoldReturn v (tWrapMatchArmsCF lo) (tWrapMatchArmsCF hi) (tWrapMatchArmsCF body)) ty
  | .mk (.forFoldRevReturn v lo hi body) ty =>
      .mk (.forFoldRevReturn v (tWrapMatchArmsCF lo) (tWrapMatchArmsCF hi) (tWrapMatchArmsCF body)) ty
  | .mk (.whileFoldReturn c body) ty =>
      .mk (.whileFoldReturn (tWrapMatchArmsCF c) (tWrapMatchArmsCF body)) ty
  | .mk (.cfBreak e) ty => .mk (.cfBreak (tWrapMatchArmsCF e)) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue (tWrapMatchArmsCF e)) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (tWrapMatchArmsCF e)) ty
  | .mk (.ann e) ty => .mk (.ann (tWrapMatchArmsCF e)) ty
where
  mapExpr : List TExpr → List TExpr
    | [] => []
    | e :: es => tWrapMatchArmsCF e :: mapExpr es
  mapArms : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tWrapMatchArmsCF e) :: mapArms rest
  mapArmsWrap : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, e.maybeWrapContinue) :: mapArmsWrap rest

@[simp] theorem tWrapMatchArmsCF.mapExpr_eq (es : List TExpr) :
    tWrapMatchArmsCF.mapExpr es = es.map tWrapMatchArmsCF := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [tWrapMatchArmsCF.mapExpr, ih]

@[simp] theorem tWrapMatchArmsCF.mapArms_eq (arms : List (ImpPat × TExpr)) :
    tWrapMatchArmsCF.mapArms arms = arms.map (fun (p, e) => (p, tWrapMatchArmsCF e)) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [tWrapMatchArmsCF.mapArms, ih]

@[simp] theorem tWrapMatchArmsCF.mapArmsWrap_eq (arms : List (ImpPat × TExpr)) :
    tWrapMatchArmsCF.mapArmsWrap arms = arms.map (fun (p, e) => (p, e.maybeWrapContinue)) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [tWrapMatchArmsCF.mapArmsWrap, ih]

/-! ## Erase commutativity

The TExpr `tWrapMatchArmsCF` mirrors the ImpExpr `wrapMatchArmsCF`
structurally, with `.ann` erased to its inner. So erasure commutes with
the transformation:

  (tWrapMatchArmsCF e).erase = wrapMatchArmsCF e.erase

This is the key lemma that lets tPipeline integrate this phase while
preserving the existing `pipeline_correct` and friends — the untyped
pipeline already proves preservation properties for `wrapMatchArmsCF`,
and via erase-commutativity those transfer to the typed side.

Lemmas about the helper predicates: `endsInCF` and `maybeWrapContinue`
on TExpr agree with their ImpExpr counterparts under erasure.
-/

/-- `endsInCF` is preserved under erasure. -/
theorem TExpr.endsInCF_erase (e : TExpr) :
    e.endsInCF = Hax.endsInCF e.erase := by
  induction e using TExpr.ind with
  | lit | var | unitVal | continue_ | break_none => rfl
  | letBind _ _ _ _ _ ih2 =>
    simp [TExpr.endsInCF, TExpr.erase, Hax.endsInCF, ih2]
  | seq _ _ _ _ ih2 =>
    simp [TExpr.endsInCF, TExpr.erase, Hax.endsInCF, ih2]
  | ifThenElse _ _ _ _ _ ih2 ih3 =>
    simp [TExpr.endsInCF, TExpr.erase, Hax.endsInCF, ih2, ih3]
  | ann _ _ ih =>
    simp [TExpr.endsInCF, TExpr.erase, ih]
  | cfBreak | cfContinue | cfBreakContinue =>
    simp [TExpr.endsInCF, TExpr.erase, Hax.endsInCF]
  -- Leaf-shaped cases all return false
  | app | tuple | proj | match_ | borrow | deref | assign
  | forLoop | forLoopRev | whileLoop | break_some | earlyReturn | questionMark
  | forFold | forFoldRev | whileFold | forFoldReturn | forFoldRevReturn | whileFoldReturn =>
    simp [TExpr.endsInCF, TExpr.erase, Hax.endsInCF]

/-- `maybeWrapContinue` commutes with erasure. -/
theorem TExpr.maybeWrapContinue_erase (e : TExpr) :
    e.maybeWrapContinue.erase = Hax.maybeWrapContinue e.erase := by
  unfold TExpr.maybeWrapContinue Hax.maybeWrapContinue
  rw [TExpr.endsInCF_erase]
  split <;> rfl

end Hax

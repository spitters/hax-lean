/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.TExpr
import SSProve.Hax.Phase.DropReferences

/-!
# Typed Phase 1: Drop References

Typed version of `dropReferences` on `TExpr`, with a commuting lemma
showing that type erasure commutes with the transformation.
-/

namespace SSProve.Hax

/-- Typed version of `dropReferences`: erases borrow/deref nodes,
    stripping reference types. -/
def tDropReferences : TExpr → TExpr
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty =>
      .mk (.letBind n (tDropReferences val) (tDropReferences body)) ty
  | .mk (.app f args) ty => .mk (.app f (mapExpr args)) ty
  | .mk (.tuple elems) ty => .mk (.tuple (mapExpr elems)) ty
  | .mk (.proj e i) ty => .mk (.proj (tDropReferences e) i) ty
  | .mk (.ifThenElse c t e) ty =>
      .mk (.ifThenElse (tDropReferences c) (tDropReferences t) (tDropReferences e)) ty
  | .mk (.match_ scrut arms) ty =>
      .mk (.match_ (tDropReferences scrut) (mapArms arms)) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq e1 e2) ty => .mk (.seq (tDropReferences e1) (tDropReferences e2)) ty
  | .mk (.borrow e) _ => tDropReferences e
  | .mk (.deref e) _ => tDropReferences e
  | .mk (.assign n rhs) ty => .mk (.assign n (tDropReferences rhs)) ty
  | .mk (.forLoop v lo hi body) ty =>
      .mk (.forLoop v (tDropReferences lo) (tDropReferences hi) (tDropReferences body)) ty
  | .mk (.whileLoop c body) ty =>
      .mk (.whileLoop (tDropReferences c) (tDropReferences body)) ty
  | .mk (.break_ (some e)) ty => .mk (.break_ (some (tDropReferences e))) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty => .mk (.earlyReturn (tDropReferences e)) ty
  | .mk (.questionMark e) ty => .mk (.questionMark (tDropReferences e)) ty
  | .mk (.forFold v lo hi body) ty =>
      .mk (.forFold v (tDropReferences lo) (tDropReferences hi) (tDropReferences body)) ty
  | .mk (.whileFold c body) ty =>
      .mk (.whileFold (tDropReferences c) (tDropReferences body)) ty
  | .mk (.forFoldReturn v lo hi body) ty =>
      .mk (.forFoldReturn v (tDropReferences lo) (tDropReferences hi) (tDropReferences body)) ty
  | .mk (.whileFoldReturn c body) ty =>
      .mk (.whileFoldReturn (tDropReferences c) (tDropReferences body)) ty
  | .mk (.cfBreak e) ty => .mk (.cfBreak (tDropReferences e)) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue (tDropReferences e)) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (tDropReferences e)) ty
where
  mapExpr : List TExpr → List TExpr
    | [] => []
    | e :: es => tDropReferences e :: mapExpr es
  mapArms : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tDropReferences e) :: mapArms rest

@[simp] theorem tDropReferences.mapExpr_eq (es : List TExpr) :
    tDropReferences.mapExpr es = es.map tDropReferences := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [tDropReferences.mapExpr, ih]

@[simp] theorem tDropReferences.mapArms_eq (arms : List (ImpPat × TExpr)) :
    tDropReferences.mapArms arms = arms.map fun (p, e) => (p, tDropReferences e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [tDropReferences.mapArms, ih]

/-- Commuting diagram: type erasure commutes with `tDropReferences`. -/
theorem tDropReferences_erase (e : TExpr) :
    (tDropReferences e).erase = dropReferences e.erase := by
  induction e using TExpr.ind with
  | lit | var | unitVal | continue_ | break_none => rfl
  | borrow _ _ ih => simp [tDropReferences, TExpr.erase, dropReferences, ih]
  | deref _ _ ih => simp [tDropReferences, TExpr.erase, dropReferences, ih]
  | letBind _ _ _ _ ih1 ih2 =>
    simp [tDropReferences, TExpr.erase, dropReferences, ih1, ih2]
  | seq _ _ _ ih1 ih2 =>
    simp [tDropReferences, TExpr.erase, dropReferences, ih1, ih2]
  | proj _ _ _ ih => simp [tDropReferences, TExpr.erase, dropReferences, ih]
  | ifThenElse _ _ _ _ ih1 ih2 ih3 =>
    simp [tDropReferences, TExpr.erase, dropReferences, ih1, ih2, ih3]
  | assign _ _ _ ih => simp [tDropReferences, TExpr.erase, dropReferences, ih]
  | forLoop _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tDropReferences, TExpr.erase, dropReferences, ih1, ih2, ih3]
  | whileLoop _ _ _ ih1 ih2 =>
    simp [tDropReferences, TExpr.erase, dropReferences, ih1, ih2]
  | break_some _ _ ih => simp [tDropReferences, TExpr.erase, dropReferences, ih]
  | earlyReturn _ _ ih => simp [tDropReferences, TExpr.erase, dropReferences, ih]
  | questionMark _ _ ih => simp [tDropReferences, TExpr.erase, dropReferences, ih]
  | forFold _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tDropReferences, TExpr.erase, dropReferences, ih1, ih2, ih3]
  | whileFold _ _ _ ih1 ih2 =>
    simp [tDropReferences, TExpr.erase, dropReferences, ih1, ih2]
  | forFoldReturn _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tDropReferences, TExpr.erase, dropReferences, ih1, ih2, ih3]
  | whileFoldReturn _ _ _ ih1 ih2 =>
    simp [tDropReferences, TExpr.erase, dropReferences, ih1, ih2]
  | cfBreak _ _ ih => simp [tDropReferences, TExpr.erase, dropReferences, ih]
  | cfContinue _ _ ih => simp [tDropReferences, TExpr.erase, dropReferences, ih]
  | cfBreakContinue _ _ ih => simp [tDropReferences, TExpr.erase, dropReferences, ih]
  | app _ _ args ih =>
    simp only [tDropReferences, tDropReferences.mapExpr_eq, TExpr.erase, TExpr.eraseList_eq,
      dropReferences, dropReferences.mapExpr_eq, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha)
  | tuple _ elems ih =>
    simp only [tDropReferences, tDropReferences.mapExpr_eq, TExpr.erase, TExpr.eraseList_eq,
      dropReferences, dropReferences.mapExpr_eq, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha)
  | match_ _ _ arms ih1 ih2 =>
    simp only [tDropReferences, tDropReferences.mapArms_eq, TExpr.erase, TExpr.eraseArms_eq,
      dropReferences, dropReferences.mapArms_eq, ih1, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun ⟨p, e⟩ hpa => by
      simp only [ih2 (p, e) hpa])

end SSProve.Hax

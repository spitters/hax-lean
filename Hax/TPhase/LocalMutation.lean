/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr
import Hax.Phase.LocalMutation

/-!
# Typed Phase 2: Local Mutation Elimination

Typed version of `localMutation` on `TExpr`, with a commuting lemma
showing that type erasure commutes with the transformation.
-/

namespace Hax

/-- Typed version of `localMutation`: transforms `assign` into let-rebindings. -/
def tLocalMutation (mvars : List String) : TExpr → TExpr
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty =>
      .mk (.letBind n (tLocalMutation mvars val) (tLocalMutation mvars body)) ty
  | .mk (.lam ps body) ty => .mk (.lam ps (tLocalMutation mvars body)) ty
  | .mk (.app f args) ty => .mk (.app f (mapExpr mvars args)) ty
  | .mk (.tuple elems) ty => .mk (.tuple (mapExpr mvars elems)) ty
  | .mk (.proj e i) ty => .mk (.proj (tLocalMutation mvars e) i) ty
  | .mk (.ifThenElse c t e) ty =>
      .mk (.ifThenElse (tLocalMutation mvars c) (tLocalMutation mvars t)
        (tLocalMutation mvars e)) ty
  | .mk (.match_ scrut arms) ty =>
      .mk (.match_ (tLocalMutation mvars scrut) (mapArms mvars arms)) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq e1 e2) ty =>
      .mk (.seq (tLocalMutation mvars e1) (tLocalMutation mvars e2)) ty
  | .mk (.borrow e) ty => .mk (.borrow (tLocalMutation mvars e)) ty
  | .mk (.deref e) ty => .mk (.deref (tLocalMutation mvars e)) ty
  | .mk (.assign n rhs) ty =>
      let rhs' := tLocalMutation mvars rhs
      .mk (.seq (.mk (.letBind n rhs' (.mk (.var n) rhs'.ty)) rhs'.ty) (.mk .unitVal .unit)) ty
  | .mk (.forLoop v lo hi body) ty =>
      .mk (.forLoop v (tLocalMutation mvars lo) (tLocalMutation mvars hi)
        (tLocalMutation mvars body)) ty
  | .mk (.forLoopRev v lo hi body) ty =>
      .mk (.forLoopRev v (tLocalMutation mvars lo) (tLocalMutation mvars hi)
        (tLocalMutation mvars body)) ty
  | .mk (.whileLoop c body) ty =>
      .mk (.whileLoop (tLocalMutation mvars c) (tLocalMutation mvars body)) ty
  | .mk (.break_ (some e)) ty => .mk (.break_ (some (tLocalMutation mvars e))) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty => .mk (.earlyReturn (tLocalMutation mvars e)) ty
  | .mk (.questionMark e) ty => .mk (.questionMark (tLocalMutation mvars e)) ty
  | .mk (.forFold v lo hi body) ty =>
      .mk (.forFold v (tLocalMutation mvars lo) (tLocalMutation mvars hi)
        (tLocalMutation mvars body)) ty
  | .mk (.forFoldRev v lo hi body) ty =>
      .mk (.forFoldRev v (tLocalMutation mvars lo) (tLocalMutation mvars hi)
        (tLocalMutation mvars body)) ty
  | .mk (.whileFold c body) ty =>
      .mk (.whileFold (tLocalMutation mvars c) (tLocalMutation mvars body)) ty
  | .mk (.forFoldReturn v lo hi body) ty =>
      .mk (.forFoldReturn v (tLocalMutation mvars lo) (tLocalMutation mvars hi)
        (tLocalMutation mvars body)) ty
  | .mk (.forFoldRevReturn v lo hi body) ty =>
      .mk (.forFoldRevReturn v (tLocalMutation mvars lo) (tLocalMutation mvars hi)
        (tLocalMutation mvars body)) ty
  | .mk (.whileFoldReturn c body) ty =>
      .mk (.whileFoldReturn (tLocalMutation mvars c) (tLocalMutation mvars body)) ty
  | .mk (.cfBreak e) ty => .mk (.cfBreak (tLocalMutation mvars e)) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue (tLocalMutation mvars e)) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (tLocalMutation mvars e)) ty
  | .mk (.ann e) ty => .mk (.ann (tLocalMutation mvars e)) ty
  | .mk (.namedProj n e) ty => .mk (.namedProj n (tLocalMutation mvars e)) ty
where
  mapExpr (mvars : List String) : List TExpr → List TExpr
    | [] => []
    | e :: es => tLocalMutation mvars e :: mapExpr mvars es
  mapArms (mvars : List String) : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tLocalMutation mvars e) :: mapArms mvars rest

@[simp] theorem tLocalMutation.mapExpr_eq (mvars : List String) (es : List TExpr) :
    tLocalMutation.mapExpr mvars es = es.map (tLocalMutation mvars) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [tLocalMutation.mapExpr, ih]

@[simp] theorem tLocalMutation.mapArms_eq (mvars : List String)
    (arms : List (ImpPat × TExpr)) :
    tLocalMutation.mapArms mvars arms =
      arms.map fun (p, e) => (p, tLocalMutation mvars e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [tLocalMutation.mapArms, ih]

/-- Commuting diagram: type erasure commutes with `tLocalMutation`. -/
theorem tLocalMutation_erase (mvars : List String) (e : TExpr) :
    (tLocalMutation mvars e).erase = localMutation mvars e.erase := by
  induction e using TExpr.ind with
  | lit | var | unitVal | continue_ | break_none => rfl
  | lam _ _ _ ih =>
    simp [tLocalMutation, TExpr.erase, localMutation, ih]
  | letBind _ _ _ _ ih1 ih2 =>
    simp [tLocalMutation, TExpr.erase, localMutation, ih1, ih2]
  | seq _ _ _ ih1 ih2 =>
    simp [tLocalMutation, TExpr.erase, localMutation, ih1, ih2]
  | proj _ _ _ ih => simp [tLocalMutation, TExpr.erase, localMutation, ih]
  | ifThenElse _ _ _ _ ih1 ih2 ih3 =>
    simp [tLocalMutation, TExpr.erase, localMutation, ih1, ih2, ih3]
  | borrow _ _ ih => simp [tLocalMutation, TExpr.erase, localMutation, ih]
  | deref _ _ ih => simp [tLocalMutation, TExpr.erase, localMutation, ih]
  | assign _ _ _ ih => simp [tLocalMutation, TExpr.erase, localMutation, ih]
  | forLoop _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tLocalMutation, TExpr.erase, localMutation, ih1, ih2, ih3]
  | forLoopRev _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tLocalMutation, TExpr.erase, localMutation, ih1, ih2, ih3]
  | whileLoop _ _ _ ih1 ih2 =>
    simp [tLocalMutation, TExpr.erase, localMutation, ih1, ih2]
  | break_some _ _ ih => simp [tLocalMutation, TExpr.erase, localMutation, ih]
  | earlyReturn _ _ ih => simp [tLocalMutation, TExpr.erase, localMutation, ih]
  | questionMark _ _ ih => simp [tLocalMutation, TExpr.erase, localMutation, ih]
  | forFold _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tLocalMutation, TExpr.erase, localMutation, ih1, ih2, ih3]
  | forFoldRev _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tLocalMutation, TExpr.erase, localMutation, ih1, ih2, ih3]
  | whileFold _ _ _ ih1 ih2 =>
    simp [tLocalMutation, TExpr.erase, localMutation, ih1, ih2]
  | forFoldReturn _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tLocalMutation, TExpr.erase, localMutation, ih1, ih2, ih3]
  | forFoldRevReturn _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tLocalMutation, TExpr.erase, localMutation, ih1, ih2, ih3]
  | whileFoldReturn _ _ _ ih1 ih2 =>
    simp [tLocalMutation, TExpr.erase, localMutation, ih1, ih2]
  | cfBreak _ _ ih => simp [tLocalMutation, TExpr.erase, localMutation, ih]
  | cfContinue _ _ ih => simp [tLocalMutation, TExpr.erase, localMutation, ih]
  | cfBreakContinue _ _ ih => simp [tLocalMutation, TExpr.erase, localMutation, ih]
  | ann _ _ ih => simp [tLocalMutation, TExpr.erase, localMutation, ih]
  | namedProj _ _ _ ih =>
    simp [tLocalMutation, TExpr.erase, localMutation, ih]
  | app _ _ args ih =>
    simp only [tLocalMutation, tLocalMutation.mapExpr_eq, TExpr.erase, TExpr.eraseList_eq,
      localMutation, localMutation.mapExpr_eq, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha)
  | tuple _ elems ih =>
    simp only [tLocalMutation, tLocalMutation.mapExpr_eq, TExpr.erase, TExpr.eraseList_eq,
      localMutation, localMutation.mapExpr_eq, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha)
  | match_ _ _ arms ih1 ih2 =>
    simp only [tLocalMutation, tLocalMutation.mapArms_eq, TExpr.erase, TExpr.eraseArms_eq,
      localMutation, localMutation.mapArms_eq, ih1, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun ⟨p, e⟩ hpa => by
      simp only [ih2 (p, e) hpa])

end Hax

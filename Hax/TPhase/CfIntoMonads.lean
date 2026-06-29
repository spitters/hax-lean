/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr
import Hax.Phase.CfIntoMonads

/-!
# Typed Phase 4: Control Flow into Monads

Typed version of `cfIntoMonads` on `TExpr`, with a commuting lemma.
-/

namespace Hax

/-- Typed version of `cfIntoMonads`: converts early returns and `?` into
    monadic ControlFlow patterns. -/
def tCfIntoMonads : TExpr → TExpr
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty =>
      .mk (.letBind n (tCfIntoMonads val) (tCfIntoMonads body)) ty
  | .mk (.lam ps body) ty => .mk (.lam ps (tCfIntoMonads body)) ty
  | .mk (.app f args) ty => .mk (.app f (mapExpr args)) ty
  | .mk (.tuple elems) ty => .mk (.tuple (mapExpr elems)) ty
  | .mk (.proj e i) ty => .mk (.proj (tCfIntoMonads e) i) ty
  | .mk (.ifThenElse c t e) ty =>
      .mk (.ifThenElse (tCfIntoMonads c) (tCfIntoMonads t) (tCfIntoMonads e)) ty
  | .mk (.match_ scrut arms) ty =>
      .mk (.match_ (tCfIntoMonads scrut) (mapArms arms)) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq e1 e2) ty =>
      .mk (.seq (tCfIntoMonads e1) (tCfIntoMonads e2)) ty
  | .mk (.borrow e) ty => .mk (.borrow (tCfIntoMonads e)) ty
  | .mk (.deref e) ty => .mk (.deref (tCfIntoMonads e)) ty
  | .mk (.assign n rhs) ty => .mk (.assign n (tCfIntoMonads rhs)) ty
  | .mk (.forLoop v lo hi body) ty =>
      .mk (.forLoop v (tCfIntoMonads lo) (tCfIntoMonads hi) (tCfIntoMonads body)) ty
  | .mk (.forLoopRev v lo hi body) ty =>
      .mk (.forLoopRev v (tCfIntoMonads lo) (tCfIntoMonads hi) (tCfIntoMonads body)) ty
  | .mk (.whileLoop c body) ty =>
      .mk (.whileLoop (tCfIntoMonads c) (tCfIntoMonads body)) ty
  | .mk (.break_ (some e)) ty => .mk (.break_ (some (tCfIntoMonads e))) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty =>
      .mk (.cfBreak (tCfIntoMonads e)) (.controlFlow e.ty ty)
  | .mk (.questionMark e) ty =>
      .mk (.match_ (tCfIntoMonads e) [
        (.okPat (.varPat "__ok_val"), .mk (.var "__ok_val") .unknown),
        (.errPat (.varPat "__err_val"),
          .mk (.cfBreak (.mk (.app "Err" [.mk (.var "__err_val") .unknown]) .unknown))
            .unknown)
      ]) ty
  | .mk (.forFold v lo hi body) ty =>
      .mk (.forFold v (tCfIntoMonads lo) (tCfIntoMonads hi) (tCfIntoMonads body)) ty
  | .mk (.forFoldRev v lo hi body) ty =>
      .mk (.forFoldRev v (tCfIntoMonads lo) (tCfIntoMonads hi) (tCfIntoMonads body)) ty
  | .mk (.whileFold c body) ty =>
      .mk (.whileFold (tCfIntoMonads c) (tCfIntoMonads body)) ty
  | .mk (.forFoldReturn v lo hi body) ty =>
      .mk (.forFoldReturn v (tCfIntoMonads lo) (tCfIntoMonads hi)
        (tCfIntoMonads body)) ty
  | .mk (.forFoldRevReturn v lo hi body) ty =>
      .mk (.forFoldRevReturn v (tCfIntoMonads lo) (tCfIntoMonads hi)
        (tCfIntoMonads body)) ty
  | .mk (.whileFoldReturn c body) ty =>
      .mk (.whileFoldReturn (tCfIntoMonads c) (tCfIntoMonads body)) ty
  | .mk (.cfBreak e) ty => .mk (.cfBreak (tCfIntoMonads e)) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue (tCfIntoMonads e)) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (tCfIntoMonads e)) ty
  | .mk (.ann e) ty => .mk (.ann (tCfIntoMonads e)) ty
  | .mk (.namedProj n e) ty => .mk (.namedProj n (tCfIntoMonads e)) ty
where
  mapExpr : List TExpr → List TExpr
    | [] => []
    | e :: es => tCfIntoMonads e :: mapExpr es
  mapArms : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tCfIntoMonads e) :: mapArms rest

@[simp] theorem tCfIntoMonads.mapExpr_eq (es : List TExpr) :
    tCfIntoMonads.mapExpr es = es.map tCfIntoMonads := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [tCfIntoMonads.mapExpr, ih]

@[simp] theorem tCfIntoMonads.mapArms_eq (arms : List (ImpPat × TExpr)) :
    tCfIntoMonads.mapArms arms = arms.map fun (p, e) => (p, tCfIntoMonads e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [tCfIntoMonads.mapArms, ih]

/-- Commuting diagram: type erasure commutes with `tCfIntoMonads`. -/
theorem tCfIntoMonads_erase (e : TExpr) :
    (tCfIntoMonads e).erase = cfIntoMonads e.erase := by
  induction e using TExpr.ind with
  | lit | var | unitVal | continue_ | break_none => rfl
  | lam _ _ _ ih =>
    simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih]
  | letBind _ _ _ _ ih1 ih2 =>
    simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih1, ih2]
  | seq _ _ _ ih1 ih2 =>
    simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih1, ih2]
  | proj _ _ _ ih => simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih]
  | ifThenElse _ _ _ _ ih1 ih2 ih3 =>
    simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih1, ih2, ih3]
  | borrow _ _ ih => simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih]
  | deref _ _ ih => simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih]
  | assign _ _ _ ih => simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih]
  | forLoop _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih1, ih2, ih3]
  | forLoopRev _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih1, ih2, ih3]
  | whileLoop _ _ _ ih1 ih2 =>
    simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih1, ih2]
  | break_some _ _ ih => simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih]
  | earlyReturn _ _ ih => simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih]
  | questionMark _ _ ih => simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih]
  | forFold _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih1, ih2, ih3]
  | forFoldRev _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih1, ih2, ih3]
  | whileFold _ _ _ ih1 ih2 =>
    simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih1, ih2]
  | forFoldReturn _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih1, ih2, ih3]
  | forFoldRevReturn _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih1, ih2, ih3]
  | whileFoldReturn _ _ _ ih1 ih2 =>
    simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih1, ih2]
  | cfBreak _ _ ih => simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih]
  | cfContinue _ _ ih => simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih]
  | cfBreakContinue _ _ ih => simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih]
  | ann _ _ ih => simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih]
  | namedProj _ _ _ ih =>
    simp [tCfIntoMonads, TExpr.erase, cfIntoMonads, ih]
  | app _ _ args ih =>
    simp only [tCfIntoMonads, tCfIntoMonads.mapExpr_eq, TExpr.erase, TExpr.eraseList_eq,
      cfIntoMonads, cfIntoMonads.mapExpr_eq, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha)
  | tuple _ elems ih =>
    simp only [tCfIntoMonads, tCfIntoMonads.mapExpr_eq, TExpr.erase, TExpr.eraseList_eq,
      cfIntoMonads, cfIntoMonads.mapExpr_eq, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha)
  | match_ _ _ arms ih1 ih2 =>
    simp only [tCfIntoMonads, tCfIntoMonads.mapArms_eq, TExpr.erase, TExpr.eraseArms_eq,
      cfIntoMonads, cfIntoMonads.mapArms_eq, ih1, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun ⟨p, e⟩ hpa => by
      simp only [ih2 (p, e) hpa])

end Hax

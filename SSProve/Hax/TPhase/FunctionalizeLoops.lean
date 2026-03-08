/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.TExpr
import SSProve.Hax.TFeatures
import SSProve.Hax.Phase.FunctionalizeLoops

/-!
# Typed Phase 3: Functionalize Loops

Typed version of `functionalizeLoops` on `TExpr`, with a commuting lemma.
-/

namespace SSProve.Hax

/-- Check if a typed expression has early exits (via erasure). -/
private def tCheckNoEarlyExit (e : TExpr) : Bool :=
  checkNoEarlyExit e.erase

/-- Typed version of `functionalizeLoopsAux`. -/
def tFunctionalizeLoopsAux (nested : Bool) : TExpr → TExpr
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty =>
      .mk (.letBind n (tFunctionalizeLoopsAux nested val)
        (tFunctionalizeLoopsAux nested body)) ty
  | .mk (.app f args) ty => .mk (.app f (mapExpr nested args)) ty
  | .mk (.tuple elems) ty => .mk (.tuple (mapExpr nested elems)) ty
  | .mk (.proj e i) ty => .mk (.proj (tFunctionalizeLoopsAux nested e) i) ty
  | .mk (.ifThenElse c t e) ty =>
      .mk (.ifThenElse (tFunctionalizeLoopsAux nested c)
        (tFunctionalizeLoopsAux nested t) (tFunctionalizeLoopsAux nested e)) ty
  | .mk (.match_ scrut arms) ty =>
      .mk (.match_ (tFunctionalizeLoopsAux nested scrut) (mapArms nested arms)) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq e1 e2) ty =>
      .mk (.seq (tFunctionalizeLoopsAux nested e1)
        (tFunctionalizeLoopsAux nested e2)) ty
  | .mk (.borrow e) ty => .mk (.borrow (tFunctionalizeLoopsAux nested e)) ty
  | .mk (.deref e) ty => .mk (.deref (tFunctionalizeLoopsAux nested e)) ty
  | .mk (.assign n rhs) ty =>
      .mk (.assign n (tFunctionalizeLoopsAux nested rhs)) ty
  | .mk (.forLoop v lo hi body) ty =>
      let bodyHasEE := !tCheckNoEarlyExit body
      if bodyHasEE then
        .mk (.forFoldReturn v (tFunctionalizeLoopsAux nested lo)
          (tFunctionalizeLoopsAux nested hi)
          (tFunctionalizeLoopsAux true body)) ty
      else
        .mk (.forFold v (tFunctionalizeLoopsAux nested lo)
          (tFunctionalizeLoopsAux nested hi)
          (tFunctionalizeLoopsAux false body)) ty
  | .mk (.whileLoop cond body) ty =>
      let bodyHasEE := !tCheckNoEarlyExit body
      if bodyHasEE then
        .mk (.whileFoldReturn (tFunctionalizeLoopsAux nested cond)
          (tFunctionalizeLoopsAux true body)) ty
      else
        .mk (.whileFold (tFunctionalizeLoopsAux nested cond)
          (tFunctionalizeLoopsAux false body)) ty
  | .mk (.break_ (some e)) ty =>
      if nested then
        .mk (.cfBreakContinue (tFunctionalizeLoopsAux nested e)) ty
      else
        .mk (.cfBreak (tFunctionalizeLoopsAux nested e)) ty
  | .mk (.break_ none) ty =>
      if nested then
        .mk (.cfBreakContinue (.mk .unitVal .unit)) ty
      else
        .mk (.cfBreak (.mk .unitVal .unit)) ty
  | .mk .continue_ ty => .mk (.cfContinue (.mk .unitVal .unit)) ty
  | .mk (.earlyReturn e) ty =>
      .mk (.earlyReturn (tFunctionalizeLoopsAux nested e)) ty
  | .mk (.questionMark e) ty =>
      .mk (.questionMark (tFunctionalizeLoopsAux nested e)) ty
  | .mk (.forFold v lo hi body) ty =>
      .mk (.forFold v (tFunctionalizeLoopsAux nested lo)
        (tFunctionalizeLoopsAux nested hi)
        (tFunctionalizeLoopsAux nested body)) ty
  | .mk (.whileFold c body) ty =>
      .mk (.whileFold (tFunctionalizeLoopsAux nested c)
        (tFunctionalizeLoopsAux nested body)) ty
  | .mk (.forFoldReturn v lo hi body) ty =>
      .mk (.forFoldReturn v (tFunctionalizeLoopsAux nested lo)
        (tFunctionalizeLoopsAux nested hi)
        (tFunctionalizeLoopsAux nested body)) ty
  | .mk (.whileFoldReturn c body) ty =>
      .mk (.whileFoldReturn (tFunctionalizeLoopsAux nested c)
        (tFunctionalizeLoopsAux nested body)) ty
  | .mk (.cfBreak e) ty =>
      .mk (.cfBreak (tFunctionalizeLoopsAux nested e)) ty
  | .mk (.cfContinue e) ty =>
      .mk (.cfContinue (tFunctionalizeLoopsAux nested e)) ty
  | .mk (.cfBreakContinue e) ty =>
      .mk (.cfBreakContinue (tFunctionalizeLoopsAux nested e)) ty
where
  mapExpr (nested : Bool) : List TExpr → List TExpr
    | [] => []
    | e :: es => tFunctionalizeLoopsAux nested e :: mapExpr nested es
  mapArms (nested : Bool) : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tFunctionalizeLoopsAux nested e) :: mapArms nested rest

/-- Top-level entry point: starts with `nested = false`. -/
def tFunctionalizeLoops (e : TExpr) : TExpr :=
  tFunctionalizeLoopsAux false e

@[simp] theorem tFunctionalizeLoopsAux.mapExpr_eq (n : Bool) (es : List TExpr) :
    tFunctionalizeLoopsAux.mapExpr n es = es.map (tFunctionalizeLoopsAux n) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [tFunctionalizeLoopsAux.mapExpr, ih]

@[simp] theorem tFunctionalizeLoopsAux.mapArms_eq (n : Bool) (arms : List (ImpPat × TExpr)) :
    tFunctionalizeLoopsAux.mapArms n arms =
      arms.map fun (p, e) => (p, tFunctionalizeLoopsAux n e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [tFunctionalizeLoopsAux.mapArms, ih]

/-- Key lemma: `tCheckNoEarlyExit` matches `checkNoEarlyExit` after erasure. -/
private theorem tCheckNoEarlyExit_eq (e : TExpr) :
    tCheckNoEarlyExit e = checkNoEarlyExit e.erase := rfl

/-- Commuting diagram: type erasure commutes with `tFunctionalizeLoopsAux`. -/
theorem tFunctionalizeLoopsAux_erase (nested : Bool) (e : TExpr) :
    (tFunctionalizeLoopsAux nested e).erase = functionalizeLoopsAux nested e.erase := by
  induction e using TExpr.ind generalizing nested with
  | lit | var | unitVal => rfl
  | continue_ => simp [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux]
  | letBind _ _ _ _ ih1 ih2 =>
    simp [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux, ih1, ih2]
  | seq _ _ _ ih1 ih2 =>
    simp [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux, ih1, ih2]
  | proj _ _ _ ih =>
    simp [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux, ih]
  | ifThenElse _ _ _ _ ih1 ih2 ih3 =>
    simp [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux, ih1, ih2, ih3]
  | borrow _ _ ih =>
    simp [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux, ih]
  | deref _ _ ih =>
    simp [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux, ih]
  | assign _ _ _ ih =>
    simp [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux, ih]
  | earlyReturn _ _ ih =>
    simp [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux, ih]
  | questionMark _ _ ih =>
    simp [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux, ih]
  | forLoop _ _ _ _ _ ih1 ih2 ih3 =>
    simp only [tFunctionalizeLoopsAux, tCheckNoEarlyExit_eq, TExpr.erase, functionalizeLoopsAux]
    split <;> simp [TExpr.erase, ih1, ih2, ih3]
  | whileLoop _ _ _ ih1 ih2 =>
    simp only [tFunctionalizeLoopsAux, tCheckNoEarlyExit_eq, TExpr.erase, functionalizeLoopsAux]
    split <;> simp [TExpr.erase, ih1, ih2]
  | break_none =>
    simp only [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux]
    split <;> simp [TExpr.erase]
  | break_some _ _ ih =>
    simp only [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux]
    split <;> simp [TExpr.erase, ih]
  | forFold _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux, ih1, ih2, ih3]
  | whileFold _ _ _ ih1 ih2 =>
    simp [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux, ih1, ih2]
  | forFoldReturn _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux, ih1, ih2, ih3]
  | whileFoldReturn _ _ _ ih1 ih2 =>
    simp [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux, ih1, ih2]
  | cfBreak _ _ ih =>
    simp [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux, ih]
  | cfContinue _ _ ih =>
    simp [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux, ih]
  | cfBreakContinue _ _ ih =>
    simp [tFunctionalizeLoopsAux, TExpr.erase, functionalizeLoopsAux, ih]
  | app _ _ args ih =>
    simp only [tFunctionalizeLoopsAux, tFunctionalizeLoopsAux.mapExpr_eq, TExpr.erase,
      TExpr.eraseList_eq, functionalizeLoopsAux, functionalizeLoopsAux.mapExpr_eq,
      List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha nested)
  | tuple _ elems ih =>
    simp only [tFunctionalizeLoopsAux, tFunctionalizeLoopsAux.mapExpr_eq, TExpr.erase,
      TExpr.eraseList_eq, functionalizeLoopsAux, functionalizeLoopsAux.mapExpr_eq,
      List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha nested)
  | match_ _ _ arms ih1 ih2 =>
    simp only [tFunctionalizeLoopsAux, tFunctionalizeLoopsAux.mapArms_eq, TExpr.erase,
      TExpr.eraseArms_eq, functionalizeLoopsAux, functionalizeLoopsAux.mapArms_eq, ih1,
      List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun ⟨p, e⟩ hpa => by
      simp only [ih2 (p, e) hpa nested])

/-- Commuting diagram for `tFunctionalizeLoops`. -/
theorem tFunctionalizeLoops_erase (e : TExpr) :
    (tFunctionalizeLoops e).erase = functionalizeLoops e.erase := by
  exact tFunctionalizeLoopsAux_erase false e

end SSProve.Hax

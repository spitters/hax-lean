/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr
import Hax.Phase.ExplicitMonadic

/-!
# Typed Phase 5: Explicit Monadic Encoding

Typed version of `explicitMonadic` on `TExpr`, with a commuting lemma.
-/

namespace Hax

/-- Typed version of `wrapReturns`: wraps pure return positions in `cfContinue`. -/
def tWrapReturns : TExpr → TExpr
  -- Already CF: leave unchanged
  | .mk (.cfBreak e) ty => .mk (.cfBreak e) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue e) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue e) ty
  -- Annotation marker on a return position: preserve and recurse.
  -- The annotation is denotationally identity, so wrapping cfContinue
  -- around the inner e is equivalent to wrapping it around .ann e.
  | .mk (.ann e) ty => .mk (.ann (tWrapReturns e)) ty
  -- Return spine: recurse into return positions
  | .mk (.letBind n val body) ty =>
      .mk (.letBind n val (tWrapReturns body)) ty
  | .mk (.ifThenElse c t e) ty =>
      .mk (.ifThenElse c (tWrapReturns t) (tWrapReturns e)) ty
  | .mk (.seq e1 e2) ty =>
      .mk (.seq e1 (tWrapReturns e2)) ty
  | .mk (.match_ scrut arms) ty =>
      .mk (.match_ scrut (tWrapReturnsArms arms)) ty
  -- Leaf return position: wrap in cfContinue
  | e => .mk (.cfContinue e) (.controlFlow e.ty .unknown)
where
  tWrapReturnsArms : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tWrapReturns e) :: tWrapReturnsArms rest

@[simp] theorem tWrapReturns.tWrapReturnsArms_eq (arms : List (ImpPat × TExpr)) :
    tWrapReturns.tWrapReturnsArms arms =
      arms.map fun (p, e) => (p, tWrapReturns e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [tWrapReturns.tWrapReturnsArms, ih]

/-- Typed version of `explicitMonadic`. -/
def tExplicitMonadic : TExpr → TExpr
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.letBind n val body) ty =>
      .mk (.letBind n (tExplicitMonadic val) (tExplicitMonadic body)) ty
  | .mk (.app f args) ty => .mk (.app f (mapExpr args)) ty
  | .mk (.tuple elems) ty => .mk (.tuple (mapExpr elems)) ty
  | .mk (.proj e i) ty => .mk (.proj (tExplicitMonadic e) i) ty
  | .mk (.ifThenElse c t e) ty =>
      .mk (.ifThenElse (tExplicitMonadic c) (tExplicitMonadic t)
        (tExplicitMonadic e)) ty
  | .mk (.match_ scrut arms) ty =>
      .mk (.match_ (tExplicitMonadic scrut) (mapArms arms)) ty
  | .mk (.seq e1 e2) ty =>
      .mk (.seq (tExplicitMonadic e1) (tExplicitMonadic e2)) ty
  -- Fold bodies: recurse then wrap returns
  | .mk (.forFold v lo hi body) ty =>
      .mk (.forFold v (tExplicitMonadic lo) (tExplicitMonadic hi)
        (tWrapReturns (tExplicitMonadic body))) ty
  | .mk (.forFoldRev v lo hi body) ty =>
      .mk (.forFoldRev v (tExplicitMonadic lo) (tExplicitMonadic hi)
        (tWrapReturns (tExplicitMonadic body))) ty
  | .mk (.whileFold c body) ty =>
      .mk (.whileFold (tExplicitMonadic c)
        (tWrapReturns (tExplicitMonadic body))) ty
  | .mk (.forFoldReturn v lo hi body) ty =>
      .mk (.forFoldReturn v (tExplicitMonadic lo) (tExplicitMonadic hi)
        (tWrapReturns (tExplicitMonadic body))) ty
  | .mk (.forFoldRevReturn v lo hi body) ty =>
      .mk (.forFoldRevReturn v (tExplicitMonadic lo) (tExplicitMonadic hi)
        (tWrapReturns (tExplicitMonadic body))) ty
  | .mk (.whileFoldReturn c body) ty =>
      .mk (.whileFoldReturn (tExplicitMonadic c)
        (tWrapReturns (tExplicitMonadic body))) ty
  -- CF constructors: recurse
  | .mk (.cfBreak e) ty => .mk (.cfBreak (tExplicitMonadic e)) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue (tExplicitMonadic e)) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (tExplicitMonadic e)) ty
  -- Pre-pipeline constructors: pass through
  | .mk (.borrow e) ty => .mk (.borrow (tExplicitMonadic e)) ty
  | .mk (.deref e) ty => .mk (.deref (tExplicitMonadic e)) ty
  | .mk (.assign n rhs) ty => .mk (.assign n (tExplicitMonadic rhs)) ty
  | .mk (.forLoop v lo hi body) ty =>
      .mk (.forLoop v (tExplicitMonadic lo) (tExplicitMonadic hi)
        (tExplicitMonadic body)) ty
  | .mk (.forLoopRev v lo hi body) ty =>
      .mk (.forLoopRev v (tExplicitMonadic lo) (tExplicitMonadic hi)
        (tExplicitMonadic body)) ty
  | .mk (.whileLoop c body) ty =>
      .mk (.whileLoop (tExplicitMonadic c) (tExplicitMonadic body)) ty
  | .mk (.break_ (some e)) ty => .mk (.break_ (some (tExplicitMonadic e))) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty => .mk (.earlyReturn (tExplicitMonadic e)) ty
  | .mk (.questionMark e) ty => .mk (.questionMark (tExplicitMonadic e)) ty
  | .mk (.ann e) ty => .mk (.ann (tExplicitMonadic e)) ty
  | .mk (.namedProj n e) ty => .mk (.namedProj n (tExplicitMonadic e)) ty
where
  mapExpr : List TExpr → List TExpr
    | [] => []
    | e :: es => tExplicitMonadic e :: mapExpr es
  mapArms : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tExplicitMonadic e) :: mapArms rest

@[simp] theorem tExplicitMonadic.mapExpr_eq (es : List TExpr) :
    tExplicitMonadic.mapExpr es = es.map tExplicitMonadic := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [tExplicitMonadic.mapExpr, ih]

@[simp] theorem tExplicitMonadic.mapArms_eq (arms : List (ImpPat × TExpr)) :
    tExplicitMonadic.mapArms arms =
      arms.map fun (p, e) => (p, tExplicitMonadic e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [tExplicitMonadic.mapArms, ih]

/-! ## Commuting diagram: wrapReturns -/

/-- Key lemma: `tWrapReturns` commutes with erasure. -/
theorem tWrapReturns_erase (e : TExpr) :
    (tWrapReturns e).erase = wrapReturns e.erase := by
  induction e using TExpr.ind with
  | cfBreak _ _ _ => rfl
  | cfContinue _ _ _ => rfl
  | cfBreakContinue _ _ _ => rfl
  | letBind _ _ _ _ _ ih2 =>
    simp [tWrapReturns, TExpr.erase, wrapReturns, ih2]
  | ifThenElse _ _ _ _ _ ih2 ih3 =>
    simp [tWrapReturns, TExpr.erase, wrapReturns, ih2, ih3]
  | seq _ _ _ _ ih2 =>
    simp [tWrapReturns, TExpr.erase, wrapReturns, ih2]
  | match_ _ _ arms _ ih2 =>
    simp only [tWrapReturns, tWrapReturns.tWrapReturnsArms_eq, TExpr.erase,
      TExpr.eraseArms_eq, wrapReturns, wrapReturns.wrapReturnsArms_eq,
      List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun ⟨p, e⟩ hpa => by
      simp only [ih2 (p, e) hpa])
  -- Annotation marker: recursive case (annotation is denote-identity)
  | ann _ _ ih =>
    simp [tWrapReturns, TExpr.erase, wrapReturns, ih]
  | namedProj _ _ _ ih =>
    simp [tWrapReturns, TExpr.erase, wrapReturns, ih]
  -- Leaf cases: all map to cfContinue
  | lit | var | unitVal | app | tuple | proj
  | borrow | deref | assign
  | forLoop | forLoopRev | whileLoop | break_none | break_some | continue_
  | earlyReturn | questionMark
  | forFold | forFoldRev | whileFold | forFoldReturn | forFoldRevReturn | whileFoldReturn =>
    simp [tWrapReturns, TExpr.erase, wrapReturns]

/-! ## Commuting diagram: explicitMonadic -/

/-- Commuting diagram: type erasure commutes with `tExplicitMonadic`. -/
theorem tExplicitMonadic_erase (e : TExpr) :
    (tExplicitMonadic e).erase = explicitMonadic e.erase := by
  induction e using TExpr.ind with
  | lit | var | unitVal | continue_ | break_none => rfl
  | letBind _ _ _ _ ih1 ih2 =>
    simp [tExplicitMonadic, TExpr.erase, explicitMonadic, ih1, ih2]
  | seq _ _ _ ih1 ih2 =>
    simp [tExplicitMonadic, TExpr.erase, explicitMonadic, ih1, ih2]
  | proj _ _ _ ih => simp [tExplicitMonadic, TExpr.erase, explicitMonadic, ih]
  | ifThenElse _ _ _ _ ih1 ih2 ih3 =>
    simp [tExplicitMonadic, TExpr.erase, explicitMonadic, ih1, ih2, ih3]
  | borrow _ _ ih => simp [tExplicitMonadic, TExpr.erase, explicitMonadic, ih]
  | deref _ _ ih => simp [tExplicitMonadic, TExpr.erase, explicitMonadic, ih]
  | assign _ _ _ ih => simp [tExplicitMonadic, TExpr.erase, explicitMonadic, ih]
  | forLoop _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tExplicitMonadic, TExpr.erase, explicitMonadic, ih1, ih2, ih3]
  | forLoopRev _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tExplicitMonadic, TExpr.erase, explicitMonadic, ih1, ih2, ih3]
  | whileLoop _ _ _ ih1 ih2 =>
    simp [tExplicitMonadic, TExpr.erase, explicitMonadic, ih1, ih2]
  | break_some _ _ ih => simp [tExplicitMonadic, TExpr.erase, explicitMonadic, ih]
  | earlyReturn _ _ ih => simp [tExplicitMonadic, TExpr.erase, explicitMonadic, ih]
  | questionMark _ _ ih => simp [tExplicitMonadic, TExpr.erase, explicitMonadic, ih]
  | forFold _ _ _ _ _ ih1 ih2 ih3 =>
    simp only [tExplicitMonadic, TExpr.erase, explicitMonadic]
    rw [tWrapReturns_erase, ih1, ih2, ih3]
  | forFoldRev _ _ _ _ _ ih1 ih2 ih3 =>
    simp only [tExplicitMonadic, TExpr.erase, explicitMonadic]
    rw [tWrapReturns_erase, ih1, ih2, ih3]
  | whileFold _ _ _ ih1 ih2 =>
    simp only [tExplicitMonadic, TExpr.erase, explicitMonadic]
    rw [tWrapReturns_erase, ih1, ih2]
  | forFoldReturn _ _ _ _ _ ih1 ih2 ih3 =>
    simp only [tExplicitMonadic, TExpr.erase, explicitMonadic]
    rw [tWrapReturns_erase, ih1, ih2, ih3]
  | forFoldRevReturn _ _ _ _ _ ih1 ih2 ih3 =>
    simp only [tExplicitMonadic, TExpr.erase, explicitMonadic]
    rw [tWrapReturns_erase, ih1, ih2, ih3]
  | whileFoldReturn _ _ _ ih1 ih2 =>
    simp only [tExplicitMonadic, TExpr.erase, explicitMonadic]
    rw [tWrapReturns_erase, ih1, ih2]
  | cfBreak _ _ ih => simp [tExplicitMonadic, TExpr.erase, explicitMonadic, ih]
  | cfContinue _ _ ih => simp [tExplicitMonadic, TExpr.erase, explicitMonadic, ih]
  | cfBreakContinue _ _ ih => simp [tExplicitMonadic, TExpr.erase, explicitMonadic, ih]
  | ann _ _ ih => simp [tExplicitMonadic, TExpr.erase, ih]
  | namedProj _ _ _ ih =>
    simp [tExplicitMonadic, TExpr.erase, explicitMonadic, ih]
  | app _ _ args ih =>
    simp only [tExplicitMonadic, tExplicitMonadic.mapExpr_eq, TExpr.erase,
      TExpr.eraseList_eq, explicitMonadic, explicitMonadic.mapExpr_eq,
      List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha)
  | tuple _ elems ih =>
    simp only [tExplicitMonadic, tExplicitMonadic.mapExpr_eq, TExpr.erase,
      TExpr.eraseList_eq, explicitMonadic, explicitMonadic.mapExpr_eq,
      List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha)
  | match_ _ _ arms ih1 ih2 =>
    simp only [tExplicitMonadic, tExplicitMonadic.mapArms_eq, TExpr.erase,
      TExpr.eraseArms_eq, explicitMonadic, explicitMonadic.mapArms_eq, ih1,
      List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun ⟨p, e⟩ hpa => by
      simp only [ih2 (p, e) hpa])

end Hax

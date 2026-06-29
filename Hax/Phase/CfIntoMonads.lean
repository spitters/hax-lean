/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.AST
import Hax.Value
import Hax.Features
import Hax.Semantics

/-!
# Phase 4: Control Flow into Monads

Convert `earlyReturn` and `questionMark` into monadic operations.

## Main definitions

* `cfIntoMonads` — the transformation
* `cfIntoMonads_noEarlyExit` — output guarantee: `NoEarlyExit`
* `cfIntoMonads_preserves_noRefs` — preservation: `NoReferences`
* `cfIntoMonads_preserves_noMut` — preservation: `NoMutation`
* `cfIntoMonads_preserves_noLoops` — preservation: `NoLoops`
-/

namespace Hax

/-- Convert early returns and `?` into monadic ControlFlow patterns. -/
def cfIntoMonads : ImpExpr → ImpExpr
  | .lit v => .lit v
  | .var n => .var n
  | .letBind n val body =>
    .letBind n (cfIntoMonads val) (cfIntoMonads body)
  | .lam ps body => .lam ps (cfIntoMonads body)
  | .app f args => .app f (mapExpr args)
  | .tuple elems => .tuple (mapExpr elems)
  | .proj e i => .proj (cfIntoMonads e) i
  | .ifThenElse c t e =>
    .ifThenElse (cfIntoMonads c) (cfIntoMonads t) (cfIntoMonads e)
  | .match_ scrut arms =>
    .match_ (cfIntoMonads scrut) (mapArms arms)
  | .unitVal => .unitVal
  | .seq e1 e2 => .seq (cfIntoMonads e1) (cfIntoMonads e2)
  | .borrow e => .borrow (cfIntoMonads e)
  | .deref e => .deref (cfIntoMonads e)
  | .assign n rhs => .assign n (cfIntoMonads rhs)
  | .forLoop v lo hi body =>
    .forLoop v (cfIntoMonads lo) (cfIntoMonads hi) (cfIntoMonads body)
  | .forLoopRev v lo hi body =>
    .forLoopRev v (cfIntoMonads lo) (cfIntoMonads hi) (cfIntoMonads body)
  | .whileLoop c body => .whileLoop (cfIntoMonads c) (cfIntoMonads body)
  | .break_ (some e) => .break_ (some (cfIntoMonads e))
  | .break_ none => .break_ none
  | .continue_ => .continue_
  | .earlyReturn e =>
    .cfBreak (cfIntoMonads e)
  | .questionMark e =>
    .match_ (cfIntoMonads e) [
      (.okPat (.varPat "__ok_val"), .var "__ok_val"),
      (.errPat (.varPat "__err_val"),
        .cfBreak (.app "Err" [.var "__err_val"]))
    ]
  -- Phase 3 output constructors: pass through
  | .forFold v lo hi body =>
    .forFold v (cfIntoMonads lo) (cfIntoMonads hi) (cfIntoMonads body)
  | .whileFold c body =>
    .whileFold (cfIntoMonads c) (cfIntoMonads body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (cfIntoMonads lo) (cfIntoMonads hi) (cfIntoMonads body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (cfIntoMonads c) (cfIntoMonads body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (cfIntoMonads lo) (cfIntoMonads hi) (cfIntoMonads body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (cfIntoMonads lo) (cfIntoMonads hi) (cfIntoMonads body)
  | .cfBreak e => .cfBreak (cfIntoMonads e)
  | .cfContinue e => .cfContinue (cfIntoMonads e)
  | .cfBreakContinue e => .cfBreakContinue (cfIntoMonads e)
  | .typeAscription e ty => .typeAscription (cfIntoMonads e) ty
where
  mapExpr : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => cfIntoMonads e :: mapExpr es
  mapArms : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, cfIntoMonads e) :: mapArms rest

@[simp] theorem cfIntoMonads.mapExpr_eq (es : List ImpExpr) :
    cfIntoMonads.mapExpr es = es.map cfIntoMonads := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [cfIntoMonads.mapExpr, ih]

@[simp] theorem cfIntoMonads.mapArms_eq (arms : List (ImpPat × ImpExpr)) :
    cfIntoMonads.mapArms arms = arms.map fun (p, e) => (p, cfIntoMonads e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [cfIntoMonads.mapArms, ih]

/-- `cfIntoMonads` produces an expression with no early exit nodes. -/
theorem cfIntoMonads_noEarlyExit (e : ImpExpr) :
    NoEarlyExit (cfIntoMonads e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | letBind _ _ _ ih1 ih2 => exact .letBind ih1 ih2
  | lam _ _ ih => exact .lam ih
  | app _ args ih =>
    simp only [cfIntoMonads, cfIntoMonads.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb)
  | tuple elems ih =>
    simp only [cfIntoMonads, cfIntoMonads.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb)
  | proj _ _ ih => exact .proj ih
  | ifThenElse _ _ _ ih1 ih2 ih3 => exact .ifThenElse ih1 ih2 ih3
  | match_ _ arms ih1 ih2 =>
    simp only [cfIntoMonads, cfIntoMonads.mapArms_eq]
    exact .match_ ih1 (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb)
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | borrow _ ih => exact .borrow ih
  | deref _ ih => exact .deref ih
  | assign _ _ ih => exact .assign ih
  | forLoop _ _ _ _ ih1 ih2 ih3 => exact .forLoop ih1 ih2 ih3
  | forLoopRev _ _ _ _ ih1 ih2 ih3 => exact .forLoopRev ih1 ih2 ih3
  | whileLoop _ _ ih1 ih2 => exact .whileLoop ih1 ih2
  | break_none => exact .break_none
  | break_some _ ih => exact .break_some ih
  | continue_ => exact .continue_
  | earlyReturn _ ih => exact .cfBreak ih
  | questionMark _ ih =>
    exact .match_ ih (fun pa hpa => by
      simp at hpa
      rcases hpa with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact .var
      · exact .cfBreak (.app (fun a ha => by simp at ha; subst ha; exact .var)))
  | forFold _ _ _ _ ih1 ih2 ih3 => exact .forFold ih1 ih2 ih3
  | whileFold _ _ ih1 ih2 => exact .whileFold ih1 ih2
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 => exact .forFoldReturn ih1 ih2 ih3
  | whileFoldReturn _ _ ih1 ih2 => exact .whileFoldReturn ih1 ih2
  | forFoldRev _ _ _ _ ih1 ih2 ih3 => exact .forFoldRev ih1 ih2 ih3
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 => exact .forFoldRevReturn ih1 ih2 ih3
  | cfBreak _ ih => exact .cfBreak ih
  | cfContinue _ ih => exact .cfContinue ih
  | cfBreakContinue _ ih => exact .cfBreakContinue ih
  | typeAscription _ _ ih => exact .typeAscription ih

/-- When an expression has no early exit nodes, `cfIntoMonads` is the identity. -/
theorem cfIntoMonads_identity (e : ImpExpr) (h : NoEarlyExit e) :
    cfIntoMonads e = e := by
  induction e using ImpExpr.ind with
  | lit | var | unitVal | continue_ => rfl
  | lam _ _ ih =>
    cases h with | lam h1 =>
    simp only [cfIntoMonads, ih h1]
  | letBind _ _ _ ih1 ih2 =>
    cases h with | letBind h1 h2 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2]
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [cfIntoMonads, cfIntoMonads.mapExpr_eq]
    congr 1
    rw [show args.map cfIntoMonads = args.map id from
      List.map_congr_left (fun a ha => ih a ha (hargs a ha)), List.map_id]
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [cfIntoMonads, cfIntoMonads.mapExpr_eq]
    congr 1
    rw [show elems.map cfIntoMonads = elems.map id from
      List.map_congr_left (fun a ha => ih a ha (helems a ha)), List.map_id]
  | proj _ _ ih => cases h with | proj he => simp only [cfIntoMonads, ih he]
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2, ih3 h3]
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [cfIntoMonads, cfIntoMonads.mapArms_eq, ih1 hs]
    congr 1
    have : arms.map (fun (p, e) => (p, cfIntoMonads e)) = arms.map id :=
      List.map_congr_left (fun ⟨p, b⟩ hpb => by
        simp only [id, ih2 (p, b) hpb (harms (p, b) hpb)])
    rw [this, List.map_id]
  | seq _ _ ih1 ih2 =>
    cases h with | seq h1 h2 => simp only [cfIntoMonads, ih1 h1, ih2 h2]
  | borrow _ ih => cases h with | borrow he => simp only [cfIntoMonads, ih he]
  | deref _ ih => cases h with | deref he => simp only [cfIntoMonads, ih he]
  | assign _ _ ih => cases h with | assign hrhs => simp only [cfIntoMonads, ih hrhs]
  | forLoop _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoop h1 h2 h3 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2, ih3 h3]
  | forLoopRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoopRev h1 h2 h3 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2, ih3 h3]
  | whileLoop _ _ ih1 ih2 =>
    cases h with | whileLoop h1 h2 => simp only [cfIntoMonads, ih1 h1, ih2 h2]
  | break_none => rfl
  | break_some _ ih =>
    cases h with | break_some he => simp only [cfIntoMonads, ih he]
  | earlyReturn => exact absurd h NoEarlyExit.not_earlyReturn
  | questionMark => exact absurd h NoEarlyExit.not_questionMark
  | forFold _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFold h1 h2 h3 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2, ih3 h3]
  | whileFold _ _ ih1 ih2 =>
    cases h with | whileFold h1 h2 => simp only [cfIntoMonads, ih1 h1, ih2 h2]
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldReturn h1 h2 h3 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2, ih3 h3]
  | whileFoldReturn _ _ ih1 ih2 =>
    cases h with | whileFoldReturn h1 h2 => simp only [cfIntoMonads, ih1 h1, ih2 h2]
  | forFoldRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRev h1 h2 h3 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2, ih3 h3]
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRevReturn h1 h2 h3 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2, ih3 h3]
  | cfBreak _ ih => cases h with | cfBreak he => simp only [cfIntoMonads, ih he]
  | cfContinue _ ih => cases h with | cfContinue he => simp only [cfIntoMonads, ih he]
  | cfBreakContinue _ ih => cases h with | cfBreakContinue he => simp only [cfIntoMonads, ih he]
  | typeAscription _ _ ih => cases h with | typeAscription he => simp only [cfIntoMonads, ih he]

/-- `cfIntoMonads` preserves `NoReferences`. -/
theorem cfIntoMonads_preserves_noRefs (e : ImpExpr)
    (h : NoReferences e) : NoReferences (cfIntoMonads e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | letBind _ _ _ ih1 ih2 => cases h with | letBind h1 h2 => exact .letBind (ih1 h1) (ih2 h2)
  | lam _ _ ih => cases h with | lam h1 => exact .lam (ih h1)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [cfIntoMonads, cfIntoMonads.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [cfIntoMonads, cfIntoMonads.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (helems b hb))
  | proj _ _ ih => cases h with | proj he => exact .proj (ih he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 => exact .ifThenElse (ih1 h1) (ih2 h2) (ih3 h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [cfIntoMonads, cfIntoMonads.mapArms_eq]
    exact .match_ (ih1 hs) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb (harms (p, b) hpb))
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => cases h with | seq h1 h2 => exact .seq (ih1 h1) (ih2 h2)
  | borrow => exact absurd h NoReferences.not_borrow
  | deref => exact absurd h NoReferences.not_deref
  | assign _ _ ih => cases h with | assign hrhs => exact .assign (ih hrhs)
  | forLoop _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoop h1 h2 h3 => exact .forLoop (ih1 h1) (ih2 h2) (ih3 h3)
  | forLoopRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoopRev h1 h2 h3 => exact .forLoopRev (ih1 h1) (ih2 h2) (ih3 h3)
  | whileLoop _ _ ih1 ih2 => cases h with | whileLoop h1 h2 => exact .whileLoop (ih1 h1) (ih2 h2)
  | break_none => exact .break_none
  | break_some _ ih => cases h with | break_some he => exact .break_some (ih he)
  | continue_ => exact .continue_
  | earlyReturn _ ih =>
    cases h with | earlyReturn he => exact .cfBreak (ih he)
  | questionMark _ ih =>
    cases h with | questionMark he =>
    exact .match_ (ih he) (fun pa hpa => by
      simp at hpa
      rcases hpa with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact .var
      · exact .cfBreak (.app (fun a ha => by simp at ha; subst ha; exact .var)))
  | forFold _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFold h1 h2 h3 => exact .forFold (ih1 h1) (ih2 h2) (ih3 h3)
  | whileFold _ _ ih1 ih2 =>
    cases h with | whileFold h1 h2 => exact .whileFold (ih1 h1) (ih2 h2)
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldReturn h1 h2 h3 => exact .forFoldReturn (ih1 h1) (ih2 h2) (ih3 h3)
  | whileFoldReturn _ _ ih1 ih2 =>
    cases h with | whileFoldReturn h1 h2 => exact .whileFoldReturn (ih1 h1) (ih2 h2)
  | forFoldRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRev h1 h2 h3 => exact .forFoldRev (ih1 h1) (ih2 h2) (ih3 h3)
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRevReturn h1 h2 h3 => exact .forFoldRevReturn (ih1 h1) (ih2 h2) (ih3 h3)
  | cfBreak _ ih => cases h with | cfBreak he => exact .cfBreak (ih he)
  | cfContinue _ ih => cases h with | cfContinue he => exact .cfContinue (ih he)
  | cfBreakContinue _ ih => cases h with | cfBreakContinue he => exact .cfBreakContinue (ih he)
  | typeAscription _ _ ih => cases h with | typeAscription he => exact .typeAscription (ih he)

/-- `cfIntoMonads` preserves `NoMutation`. -/
theorem cfIntoMonads_preserves_noMut (e : ImpExpr)
    (h : NoMutation e) : NoMutation (cfIntoMonads e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | letBind _ _ _ ih1 ih2 => cases h with | letBind h1 h2 => exact .letBind (ih1 h1) (ih2 h2)
  | lam _ _ ih => cases h with | lam h1 => exact .lam (ih h1)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [cfIntoMonads, cfIntoMonads.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [cfIntoMonads, cfIntoMonads.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (helems b hb))
  | proj _ _ ih => cases h with | proj he => exact .proj (ih he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 => exact .ifThenElse (ih1 h1) (ih2 h2) (ih3 h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [cfIntoMonads, cfIntoMonads.mapArms_eq]
    exact .match_ (ih1 hs) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb (harms (p, b) hpb))
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => cases h with | seq h1 h2 => exact .seq (ih1 h1) (ih2 h2)
  | borrow _ ih => cases h with | borrow he => exact .borrow (ih he)
  | deref _ ih => cases h with | deref he => exact .deref (ih he)
  | assign => exact absurd h NoMutation.not_assign
  | forLoop _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoop h1 h2 h3 => exact .forLoop (ih1 h1) (ih2 h2) (ih3 h3)
  | forLoopRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoopRev h1 h2 h3 => exact .forLoopRev (ih1 h1) (ih2 h2) (ih3 h3)
  | whileLoop _ _ ih1 ih2 => cases h with | whileLoop h1 h2 => exact .whileLoop (ih1 h1) (ih2 h2)
  | break_none => exact .break_none
  | break_some _ ih => cases h with | break_some he => exact .break_some (ih he)
  | continue_ => exact .continue_
  | earlyReturn _ ih =>
    cases h with | earlyReturn he => exact .cfBreak (ih he)
  | questionMark _ ih =>
    cases h with | questionMark he =>
    exact .match_ (ih he) (fun pa hpa => by
      simp at hpa
      rcases hpa with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact .var
      · exact .cfBreak (.app (fun a ha => by simp at ha; subst ha; exact .var)))
  | forFold _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFold h1 h2 h3 => exact .forFold (ih1 h1) (ih2 h2) (ih3 h3)
  | whileFold _ _ ih1 ih2 =>
    cases h with | whileFold h1 h2 => exact .whileFold (ih1 h1) (ih2 h2)
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldReturn h1 h2 h3 => exact .forFoldReturn (ih1 h1) (ih2 h2) (ih3 h3)
  | whileFoldReturn _ _ ih1 ih2 =>
    cases h with | whileFoldReturn h1 h2 => exact .whileFoldReturn (ih1 h1) (ih2 h2)
  | forFoldRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRev h1 h2 h3 => exact .forFoldRev (ih1 h1) (ih2 h2) (ih3 h3)
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRevReturn h1 h2 h3 => exact .forFoldRevReturn (ih1 h1) (ih2 h2) (ih3 h3)
  | cfBreak _ ih => cases h with | cfBreak he => exact .cfBreak (ih he)
  | cfContinue _ ih => cases h with | cfContinue he => exact .cfContinue (ih he)
  | cfBreakContinue _ ih => cases h with | cfBreakContinue he => exact .cfBreakContinue (ih he)
  | typeAscription _ _ ih => cases h with | typeAscription he => exact .typeAscription (ih he)

/-- `cfIntoMonads` preserves `NoLoops`. -/
theorem cfIntoMonads_preserves_noLoops (e : ImpExpr)
    (h : NoLoops e) : NoLoops (cfIntoMonads e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | letBind _ _ _ ih1 ih2 => cases h with | letBind h1 h2 => exact .letBind (ih1 h1) (ih2 h2)
  | lam _ _ ih => cases h with | lam h1 => exact .lam (ih h1)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [cfIntoMonads, cfIntoMonads.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [cfIntoMonads, cfIntoMonads.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (helems b hb))
  | proj _ _ ih => cases h with | proj he => exact .proj (ih he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 => exact .ifThenElse (ih1 h1) (ih2 h2) (ih3 h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [cfIntoMonads, cfIntoMonads.mapArms_eq]
    exact .match_ (ih1 hs) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb (harms (p, b) hpb))
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => cases h with | seq h1 h2 => exact .seq (ih1 h1) (ih2 h2)
  | borrow _ ih => cases h with | borrow he => exact .borrow (ih he)
  | deref _ ih => cases h with | deref he => exact .deref (ih he)
  | assign _ _ ih => cases h with | assign hrhs => exact .assign (ih hrhs)
  | forLoop => exact absurd h NoLoops.not_forLoop
  | forLoopRev => exact absurd h NoLoops.not_forLoopRev
  | whileLoop => exact absurd h NoLoops.not_whileLoop
  | break_none => exact absurd h NoLoops.not_break
  | break_some => exact absurd h NoLoops.not_break
  | continue_ => exact absurd h NoLoops.not_continue
  | earlyReturn _ ih =>
    cases h with | earlyReturn he => exact .cfBreak (ih he)
  | questionMark _ ih =>
    cases h with | questionMark he =>
    exact .match_ (ih he) (fun pa hpa => by
      simp at hpa
      rcases hpa with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact .var
      · exact .cfBreak (.app (fun a ha => by simp at ha; subst ha; exact .var)))
  | forFold _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFold h1 h2 h3 => exact .forFold (ih1 h1) (ih2 h2) (ih3 h3)
  | whileFold _ _ ih1 ih2 =>
    cases h with | whileFold h1 h2 => exact .whileFold (ih1 h1) (ih2 h2)
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldReturn h1 h2 h3 => exact .forFoldReturn (ih1 h1) (ih2 h2) (ih3 h3)
  | whileFoldReturn _ _ ih1 ih2 =>
    cases h with | whileFoldReturn h1 h2 => exact .whileFoldReturn (ih1 h1) (ih2 h2)
  | forFoldRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRev h1 h2 h3 => exact .forFoldRev (ih1 h1) (ih2 h2) (ih3 h3)
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRevReturn h1 h2 h3 => exact .forFoldRevReturn (ih1 h1) (ih2 h2) (ih3 h3)
  | cfBreak _ ih => cases h with | cfBreak he => exact .cfBreak (ih he)
  | cfContinue _ ih => cases h with | cfContinue he => exact .cfContinue (ih he)
  | cfBreakContinue _ ih => cases h with | cfBreakContinue he => exact .cfBreakContinue (ih he)
  | typeAscription _ _ ih => cases h with | typeAscription he => exact .typeAscription (ih he)

/-- On early-exit-free inputs, `cfIntoMonads` is the identity.

    For inputs with `earlyReturn`/`questionMark`, the transform rewrites
    them into `app`/`match_` patterns (e.g. `ControlFlow.Break`), which
    changes the `denote` semantics unless appropriate builtins are provided. -/
theorem cfIntoMonads_correct (e : ImpExpr) (h : NoEarlyExit e) :
    cfIntoMonads e = e := by
  induction e using ImpExpr.ind with
  | lit | var | unitVal | continue_ | break_none => rfl
  | lam _ _ ih =>
    cases h with | lam h1 =>
    simp only [cfIntoMonads, ih h1]
  | letBind n val body ih1 ih2 =>
    cases h with | letBind h1 h2 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2]
  | seq e1 e2 ih1 ih2 =>
    cases h with | seq h1 h2 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2]
  | proj e i ih =>
    cases h with | proj he =>
    simp only [cfIntoMonads, ih he]
  | ifThenElse c t e ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2, ih3 h3]
  | borrow e ih =>
    cases h with | borrow he =>
    simp only [cfIntoMonads, ih he]
  | deref e ih =>
    cases h with | deref he =>
    simp only [cfIntoMonads, ih he]
  | assign n rhs ih =>
    cases h with | assign hrhs =>
    simp only [cfIntoMonads, ih hrhs]
  | forLoop v lo hi body ih1 ih2 ih3 =>
    cases h with | forLoop h1 h2 h3 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2, ih3 h3]
  | forLoopRev v lo hi body ih1 ih2 ih3 =>
    cases h with | forLoopRev h1 h2 h3 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2, ih3 h3]
  | whileLoop c body ih1 ih2 =>
    cases h with | whileLoop h1 h2 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2]
  | break_some e ih =>
    cases h with | break_some he =>
    simp only [cfIntoMonads, ih he]
  | app f args ih =>
    cases h with | app hargs =>
    simp only [cfIntoMonads, cfIntoMonads.mapExpr_eq]
    congr 1
    conv => rhs; rw [← List.map_id args]
    exact List.map_congr_left (fun a ha => ih a ha (hargs a ha))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [cfIntoMonads, cfIntoMonads.mapExpr_eq]
    congr 1
    conv => rhs; rw [← List.map_id elems]
    exact List.map_congr_left (fun a ha => ih a ha (helems a ha))
  | match_ scrut arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [cfIntoMonads, cfIntoMonads.mapArms_eq, ih1 hs]
    congr 1
    conv => rhs; rw [← List.map_id arms]
    exact List.map_congr_left (fun pa hpa =>
      Prod.ext rfl (ih2 pa hpa (harms pa hpa)))
  | earlyReturn => exact absurd h NoEarlyExit.not_earlyReturn
  | questionMark => exact absurd h NoEarlyExit.not_questionMark
  | forFold v lo hi body ih1 ih2 ih3 =>
    cases h with | forFold h1 h2 h3 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2, ih3 h3]
  | whileFold c body ih1 ih2 =>
    cases h with | whileFold h1 h2 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2]
  | forFoldReturn v lo hi body ih1 ih2 ih3 =>
    cases h with | forFoldReturn h1 h2 h3 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2, ih3 h3]
  | whileFoldReturn c body ih1 ih2 =>
    cases h with | whileFoldReturn h1 h2 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2]
  | forFoldRev v lo hi body ih1 ih2 ih3 =>
    cases h with | forFoldRev h1 h2 h3 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2, ih3 h3]
  | forFoldRevReturn v lo hi body ih1 ih2 ih3 =>
    cases h with | forFoldRevReturn h1 h2 h3 =>
    simp only [cfIntoMonads, ih1 h1, ih2 h2, ih3 h3]
  | cfBreak e ih =>
    cases h with | cfBreak he =>
    simp only [cfIntoMonads, ih he]
  | cfContinue e ih =>
    cases h with | cfContinue he =>
    simp only [cfIntoMonads, ih he]
  | cfBreakContinue e ih =>
    cases h with | cfBreakContinue he =>
    simp only [cfIntoMonads, ih he]
  | typeAscription e _ ih =>
    cases h with | typeAscription he =>
    simp only [cfIntoMonads, ih he]

end Hax

/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import HaxLean.Pipeline
import HaxLean.Phase.FunctionalizeLoopsCF
import HaxLean.Phase.CfIntoMonadsCF

/-!
# Pipeline Semantic Correctness with ControlFlow Encoding

Composes the 4-phase correctness theorems into end-to-end pipeline results.

## Main results

* `pipeline_full_correct` — full pipeline theorem for ALL well-scoped programs,
  mapping `denote` to `denote'` with `Outcome.encodeCF` encoding
* `pipeline_cf` — for `NoEarlyExit` programs
* `pipeline_cf_val` — corollary: normal-terminating programs evaluate to the
  same value under `denote'`

## Refactored design

With dedicated AST constructors, `NoReservedApps` is eliminated:
- No preservation theorems needed (dropReferences/localMutation/FL preserve NoReservedApps)
- `pipeline_full_correct` has simpler hypotheses: just `LoopScoped`, `NoQuestionMark`,
  and `NoCFConstructors`
- `pipeline_cf` also simplified (no `NoReservedApps` on intermediate form)
- `CF4_on_FL_output` eliminated — `CF4_combined` handles all constructors directly
-/

namespace Hax

/-! ### Preservation: functionalizeLoops preserves NoEarlyExit -/

-- functionalizeLoopsAux_preserves_noEarlyExit is defined in FunctionalizeLoops.lean

theorem functionalizeLoops_preserves_noEarlyExit (e : ImpExpr) (h : NoEarlyExit e) :
    NoEarlyExit (functionalizeLoops e) :=
  functionalizeLoopsAux_preserves_noEarlyExit false e h

/-! ### Phases 1-2 preserve NoCFConstructors -/

private theorem dropReferences_preserves_noCFConstructors (e : ImpExpr)
    (h : NoCFConstructors e) : NoCFConstructors (dropReferences e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | lam _ _ ih => cases h with | lam hb => exact .lam (ih hb)
  | letBind _ _ _ ih1 ih2 =>
    cases h with | letBind h1 h2 => exact .letBind (ih1 h1) (ih2 h2)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [dropReferences, dropReferences.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [dropReferences, dropReferences.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (helems b hb))
  | proj _ _ ih => cases h with | proj he => exact .proj (ih he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 => exact .ifThenElse (ih1 h1) (ih2 h2) (ih3 h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [dropReferences, dropReferences.mapArms_eq]
    exact .match_ (ih1 hs) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb (harms (p, b) hpb))
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => cases h with | seq h1 h2 => exact .seq (ih1 h1) (ih2 h2)
  | borrow _ ih => cases h with | borrow he => exact ih he
  | deref _ ih => cases h with | deref he => exact ih he
  | assign _ _ ih => cases h with | assign hrhs => exact .assign (ih hrhs)
  | forLoop _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoop h1 h2 h3 => exact .forLoop (ih1 h1) (ih2 h2) (ih3 h3)
  | forLoopRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoopRev h1 h2 h3 => exact .forLoopRev (ih1 h1) (ih2 h2) (ih3 h3)
  | whileLoop _ _ ih1 ih2 =>
    cases h with | whileLoop h1 h2 => exact .whileLoop (ih1 h1) (ih2 h2)
  | break_none => exact .break_none
  | break_some _ ih => cases h with | break_some he => exact .break_some (ih he)
  | continue_ => exact .continue_
  | earlyReturn _ ih => cases h with | earlyReturn he => exact .earlyReturn (ih he)
  | questionMark _ ih => cases h with | questionMark he => exact .questionMark (ih he)
  | forFold => exact absurd h NoCFConstructors.not_forFold
  | forFoldRev => exact absurd h NoCFConstructors.not_forFoldRev
  | whileFold => exact absurd h NoCFConstructors.not_whileFold
  | forFoldReturn => exact absurd h NoCFConstructors.not_forFoldReturn
  | forFoldRevReturn => exact absurd h NoCFConstructors.not_forFoldRevReturn
  | whileFoldReturn => exact absurd h NoCFConstructors.not_whileFoldReturn
  | cfBreak => exact absurd h NoCFConstructors.not_cfBreak
  | cfContinue => exact absurd h NoCFConstructors.not_cfContinue
  | cfBreakContinue => exact absurd h NoCFConstructors.not_cfBreakContinue
  | typeAscription _ _ ih => cases h with | typeAscription he => exact .typeAscription (ih he)

private theorem localMutation_preserves_noCFConstructors (vars : List String) (e : ImpExpr)
    (h : NoCFConstructors e) : NoCFConstructors (localMutation vars e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | lam _ _ ih => cases h with | lam hb => exact .lam (ih hb)
  | letBind _ _ _ ih1 ih2 =>
    cases h with | letBind h1 h2 => exact .letBind (ih1 h1) (ih2 h2)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [localMutation, localMutation.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [localMutation, localMutation.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (helems b hb))
  | proj _ _ ih => cases h with | proj he => exact .proj (ih he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 => exact .ifThenElse (ih1 h1) (ih2 h2) (ih3 h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [localMutation, localMutation.mapArms_eq]
    exact .match_ (ih1 hs) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb (harms (p, b) hpb))
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => cases h with | seq h1 h2 => exact .seq (ih1 h1) (ih2 h2)
  | borrow _ ih => cases h with | borrow he => exact .borrow (ih he)
  | deref _ ih => cases h with | deref he => exact .deref (ih he)
  | assign _ _ ih =>
    cases h with | assign hrhs => exact .seq (.letBind (ih hrhs) .var) .unitVal
  | forLoop _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoop h1 h2 h3 => exact .forLoop (ih1 h1) (ih2 h2) (ih3 h3)
  | forLoopRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoopRev h1 h2 h3 => exact .forLoopRev (ih1 h1) (ih2 h2) (ih3 h3)
  | whileLoop _ _ ih1 ih2 =>
    cases h with | whileLoop h1 h2 => exact .whileLoop (ih1 h1) (ih2 h2)
  | break_none => exact .break_none
  | break_some _ ih => cases h with | break_some he => exact .break_some (ih he)
  | continue_ => exact .continue_
  | earlyReturn _ ih => cases h with | earlyReturn he => exact .earlyReturn (ih he)
  | questionMark _ ih => cases h with | questionMark he => exact .questionMark (ih he)
  | forFold => exact absurd h NoCFConstructors.not_forFold
  | forFoldRev => exact absurd h NoCFConstructors.not_forFoldRev
  | whileFold => exact absurd h NoCFConstructors.not_whileFold
  | forFoldReturn => exact absurd h NoCFConstructors.not_forFoldReturn
  | forFoldRevReturn => exact absurd h NoCFConstructors.not_forFoldRevReturn
  | whileFoldReturn => exact absurd h NoCFConstructors.not_whileFoldReturn
  | cfBreak => exact absurd h NoCFConstructors.not_cfBreak
  | cfContinue => exact absurd h NoCFConstructors.not_cfContinue
  | cfBreakContinue => exact absurd h NoCFConstructors.not_cfBreakContinue
  | typeAscription _ _ ih => cases h with | typeAscription he => exact .typeAscription (ih he)

/-! ### Phases 1-3 preserve NoQuestionMark -/

private theorem dropReferences_preserves_noQuestionMark (e : ImpExpr)
    (h : NoQuestionMark e) : NoQuestionMark (dropReferences e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | lam _ _ ih => cases h with | lam hb => exact .lam (ih hb)
  | letBind _ _ _ ih1 ih2 =>
    cases h with | letBind h1 h2 => exact .letBind (ih1 h1) (ih2 h2)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [dropReferences, dropReferences.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [dropReferences, dropReferences.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (helems b hb))
  | proj _ _ ih => cases h with | proj he => exact .proj (ih he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 => exact .ifThenElse (ih1 h1) (ih2 h2) (ih3 h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [dropReferences, dropReferences.mapArms_eq]
    exact .match_ (ih1 hs) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb (harms (p, b) hpb))
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => cases h with | seq h1 h2 => exact .seq (ih1 h1) (ih2 h2)
  | borrow _ ih => cases h with | borrow he => exact ih he
  | deref _ ih => cases h with | deref he => exact ih he
  | assign _ _ ih => cases h with | assign hrhs => exact .assign (ih hrhs)
  | forLoop _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoop h1 h2 h3 => exact .forLoop (ih1 h1) (ih2 h2) (ih3 h3)
  | forLoopRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoopRev h1 h2 h3 => exact .forLoopRev (ih1 h1) (ih2 h2) (ih3 h3)
  | whileLoop _ _ ih1 ih2 =>
    cases h with | whileLoop h1 h2 => exact .whileLoop (ih1 h1) (ih2 h2)
  | break_none => exact .break_none
  | break_some _ ih => cases h with | break_some he => exact .break_some (ih he)
  | continue_ => exact .continue_
  | earlyReturn _ ih => cases h with | earlyReturn he => exact .earlyReturn (ih he)
  | questionMark => exact absurd h NoQuestionMark.not_questionMark
  | forFold _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFold h1 h2 h3 => exact .forFold (ih1 h1) (ih2 h2) (ih3 h3)
  | forFoldRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRev h1 h2 h3 => exact .forFoldRev (ih1 h1) (ih2 h2) (ih3 h3)
  | whileFold _ _ ih1 ih2 =>
    cases h with | whileFold h1 h2 => exact .whileFold (ih1 h1) (ih2 h2)
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldReturn h1 h2 h3 => exact .forFoldReturn (ih1 h1) (ih2 h2) (ih3 h3)
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRevReturn h1 h2 h3 => exact .forFoldRevReturn (ih1 h1) (ih2 h2) (ih3 h3)
  | whileFoldReturn _ _ ih1 ih2 =>
    cases h with | whileFoldReturn h1 h2 => exact .whileFoldReturn (ih1 h1) (ih2 h2)
  | cfBreak _ ih => cases h with | cfBreak he => exact .cfBreak (ih he)
  | cfContinue _ ih => cases h with | cfContinue he => exact .cfContinue (ih he)
  | cfBreakContinue _ ih => cases h with | cfBreakContinue he => exact .cfBreakContinue (ih he)
  | typeAscription _ _ ih => cases h with | typeAscription he => exact .typeAscription (ih he)

private theorem localMutation_preserves_noQuestionMark (vars : List String) (e : ImpExpr)
    (h : NoQuestionMark e) : NoQuestionMark (localMutation vars e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | lam _ _ ih => cases h with | lam hb => exact .lam (ih hb)
  | letBind _ _ _ ih1 ih2 =>
    cases h with | letBind h1 h2 => exact .letBind (ih1 h1) (ih2 h2)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [localMutation, localMutation.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [localMutation, localMutation.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (helems b hb))
  | proj _ _ ih => cases h with | proj he => exact .proj (ih he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 => exact .ifThenElse (ih1 h1) (ih2 h2) (ih3 h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [localMutation, localMutation.mapArms_eq]
    exact .match_ (ih1 hs) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb (harms (p, b) hpb))
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => cases h with | seq h1 h2 => exact .seq (ih1 h1) (ih2 h2)
  | borrow _ ih => cases h with | borrow he => exact .borrow (ih he)
  | deref _ ih => cases h with | deref he => exact .deref (ih he)
  | assign _ _ ih =>
    cases h with | assign hrhs => exact .seq (.letBind (ih hrhs) .var) .unitVal
  | forLoop _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoop h1 h2 h3 => exact .forLoop (ih1 h1) (ih2 h2) (ih3 h3)
  | forLoopRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoopRev h1 h2 h3 => exact .forLoopRev (ih1 h1) (ih2 h2) (ih3 h3)
  | whileLoop _ _ ih1 ih2 =>
    cases h with | whileLoop h1 h2 => exact .whileLoop (ih1 h1) (ih2 h2)
  | break_none => exact .break_none
  | break_some _ ih => cases h with | break_some he => exact .break_some (ih he)
  | continue_ => exact .continue_
  | earlyReturn _ ih => cases h with | earlyReturn he => exact .earlyReturn (ih he)
  | questionMark => exact absurd h NoQuestionMark.not_questionMark
  | forFold _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFold h1 h2 h3 => exact .forFold (ih1 h1) (ih2 h2) (ih3 h3)
  | forFoldRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRev h1 h2 h3 => exact .forFoldRev (ih1 h1) (ih2 h2) (ih3 h3)
  | whileFold _ _ ih1 ih2 =>
    cases h with | whileFold h1 h2 => exact .whileFold (ih1 h1) (ih2 h2)
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldReturn h1 h2 h3 => exact .forFoldReturn (ih1 h1) (ih2 h2) (ih3 h3)
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRevReturn h1 h2 h3 => exact .forFoldRevReturn (ih1 h1) (ih2 h2) (ih3 h3)
  | whileFoldReturn _ _ ih1 ih2 =>
    cases h with | whileFoldReturn h1 h2 => exact .whileFoldReturn (ih1 h1) (ih2 h2)
  | cfBreak _ ih => cases h with | cfBreak he => exact .cfBreak (ih he)
  | cfContinue _ ih => cases h with | cfContinue he => exact .cfContinue (ih he)
  | cfBreakContinue _ ih => cases h with | cfBreakContinue he => exact .cfBreakContinue (ih he)
  | typeAscription _ _ ih => cases h with | typeAscription he => exact .typeAscription (ih he)

private theorem functionalizeLoopsAux_preserves_noQuestionMark (nested : Bool) (e : ImpExpr)
    (h : NoQuestionMark e) : NoQuestionMark (functionalizeLoopsAux nested e) := by
  induction e using ImpExpr.ind generalizing nested with
  | lit => exact .lit
  | var => exact .var
  | lam _ _ ih => cases h with | lam hb => exact .lam (ih _ hb)
  | letBind _ _ _ ih1 ih2 =>
    cases h with | letBind h1 h2 => exact .letBind (ih1 _ h1) (ih2 _ h2)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [functionalizeLoopsAux, functionalizeLoopsAux.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb _ (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [functionalizeLoopsAux, functionalizeLoopsAux.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb _ (helems b hb))
  | proj _ _ ih => cases h with | proj he => exact .proj (ih _ he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 =>
    exact .ifThenElse (ih1 _ h1) (ih2 _ h2) (ih3 _ h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [functionalizeLoopsAux, functionalizeLoopsAux.mapArms_eq]
    exact .match_ (ih1 _ hs) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb _ (harms (p, b) hpb))
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => cases h with | seq h1 h2 => exact .seq (ih1 _ h1) (ih2 _ h2)
  | borrow _ ih => cases h with | borrow he => exact .borrow (ih _ he)
  | deref _ ih => cases h with | deref he => exact .deref (ih _ he)
  | assign _ _ ih => cases h with | assign hrhs => exact .assign (ih _ hrhs)
  | forLoop _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoop h1 h2 h3 =>
    simp only [functionalizeLoopsAux]; split
    · exact .forFoldReturn (ih1 _ h1) (ih2 _ h2) (ih3 _ h3)
    · exact .forFold (ih1 _ h1) (ih2 _ h2) (ih3 _ h3)
  | forLoopRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoopRev h1 h2 h3 =>
    simp only [functionalizeLoopsAux]; split
    · exact .forFoldRevReturn (ih1 _ h1) (ih2 _ h2) (ih3 _ h3)
    · exact .forFoldRev (ih1 _ h1) (ih2 _ h2) (ih3 _ h3)
  | whileLoop _ _ ih1 ih2 =>
    cases h with | whileLoop h1 h2 =>
    simp only [functionalizeLoopsAux]; split
    · exact .whileFoldReturn (ih1 _ h1) (ih2 _ h2)
    · exact .whileFold (ih1 _ h1) (ih2 _ h2)
  | break_none =>
    simp only [functionalizeLoopsAux]; split
    · exact .cfBreakContinue .unitVal
    · exact .cfBreak .unitVal
  | break_some _ ih =>
    cases h with | break_some he =>
    simp only [functionalizeLoopsAux]; split
    · exact .cfBreakContinue (ih _ he)
    · exact .cfBreak (ih _ he)
  | continue_ => exact .cfContinue .unitVal
  | earlyReturn _ ih => cases h with | earlyReturn he => exact .earlyReturn (ih _ he)
  | questionMark => exact absurd h NoQuestionMark.not_questionMark
  | forFold _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFold h1 h2 h3 => exact .forFold (ih1 _ h1) (ih2 _ h2) (ih3 _ h3)
  | forFoldRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRev h1 h2 h3 => exact .forFoldRev (ih1 _ h1) (ih2 _ h2) (ih3 _ h3)
  | whileFold _ _ ih1 ih2 =>
    cases h with | whileFold h1 h2 => exact .whileFold (ih1 _ h1) (ih2 _ h2)
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldReturn h1 h2 h3 => exact .forFoldReturn (ih1 _ h1) (ih2 _ h2) (ih3 _ h3)
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRevReturn h1 h2 h3 => exact .forFoldRevReturn (ih1 _ h1) (ih2 _ h2) (ih3 _ h3)
  | whileFoldReturn _ _ ih1 ih2 =>
    cases h with | whileFoldReturn h1 h2 => exact .whileFoldReturn (ih1 _ h1) (ih2 _ h2)
  | cfBreak _ ih => cases h with | cfBreak he => exact .cfBreak (ih _ he)
  | cfContinue _ ih => cases h with | cfContinue he => exact .cfContinue (ih _ he)
  | cfBreakContinue _ ih => cases h with | cfBreakContinue he => exact .cfBreakContinue (ih _ he)
  | typeAscription _ _ ih => cases h with | typeAscription he => exact .typeAscription (ih _ he)

private theorem functionalizeLoops_preserves_noQuestionMark (e : ImpExpr)
    (h : NoQuestionMark e) : NoQuestionMark (functionalizeLoops e) :=
  functionalizeLoopsAux_preserves_noQuestionMark false e h

/-! ### Phase 3 produces WellFormedFolds -/

private theorem functionalizeLoopsAux_wellFormedFolds (nested : Bool) (e : ImpExpr)
    (h : NoCFConstructors e) : WellFormedFolds (functionalizeLoopsAux nested e) := by
  induction e using ImpExpr.ind generalizing nested with
  | lit => exact .lit
  | var => exact .var
  | lam _ _ ih => cases h with | lam hb => exact .lam (ih _ hb)
  | letBind _ _ _ ih1 ih2 =>
    cases h with | letBind h1 h2 => exact .letBind (ih1 _ h1) (ih2 _ h2)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [functionalizeLoopsAux, functionalizeLoopsAux.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb _ (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [functionalizeLoopsAux, functionalizeLoopsAux.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb _ (helems b hb))
  | proj _ _ ih => cases h with | proj he => exact .proj (ih _ he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 =>
    exact .ifThenElse (ih1 _ h1) (ih2 _ h2) (ih3 _ h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [functionalizeLoopsAux, functionalizeLoopsAux.mapArms_eq]
    exact .match_ (ih1 _ hs) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb _ (harms (p, b) hpb))
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 =>
    cases h with | seq h1 h2 => exact .seq (ih1 _ h1) (ih2 _ h2)
  | borrow _ ih => cases h with | borrow he => exact .borrow (ih _ he)
  | deref _ ih => cases h with | deref he => exact .deref (ih _ he)
  | assign _ _ ih => cases h with | assign hrhs => exact .assign (ih _ hrhs)
  | forLoop v lo hi body ih_lo ih_hi ih_body =>
    cases h with | forLoop hlo hhi hbody =>
    simp only [functionalizeLoopsAux]
    split
    · exact .forFoldReturn (ih_lo _ hlo) (ih_hi _ hhi) (ih_body _ hbody)
    · rename_i hee
      have hee_body : checkNoEarlyExit body = true := by
        rcases hb : checkNoEarlyExit body with _ | _ <;> simp_all
      exact .forFold (ih_lo _ hlo) (ih_hi _ hhi) (ih_body _ hbody)
        (functionalizeLoopsAux_preserves_noEarlyExit false body
          (checkNoEarlyExit_sound body hee_body))
  | forLoopRev v lo hi body ih_lo ih_hi ih_body =>
    cases h with | forLoopRev hlo hhi hbody =>
    simp only [functionalizeLoopsAux]
    split
    · exact .forFoldRevReturn (ih_lo _ hlo) (ih_hi _ hhi) (ih_body _ hbody)
    · rename_i hee
      have hee_body : checkNoEarlyExit body = true := by
        rcases hb : checkNoEarlyExit body with _ | _ <;> simp_all
      exact .forFoldRev (ih_lo _ hlo) (ih_hi _ hhi) (ih_body _ hbody)
        (functionalizeLoopsAux_preserves_noEarlyExit false body
          (checkNoEarlyExit_sound body hee_body))
  | whileLoop c body ih_c ih_body =>
    cases h with | whileLoop hc hbody =>
    simp only [functionalizeLoopsAux]
    split
    · exact .whileFoldReturn (ih_c _ hc) (ih_body _ hbody)
    · rename_i hee
      have hee_body : checkNoEarlyExit body = true := by
        rcases hb : checkNoEarlyExit body with _ | _ <;> simp_all
      exact .whileFold (ih_c _ hc) (ih_body _ hbody)
        (functionalizeLoopsAux_preserves_noEarlyExit false body
          (checkNoEarlyExit_sound body hee_body))
  | break_none =>
    cases h with | break_none =>
    simp only [functionalizeLoopsAux]; split
    · exact .cfBreakContinue .unitVal
    · exact .cfBreak .unitVal
  | break_some _ ih =>
    cases h with | break_some he =>
    simp only [functionalizeLoopsAux]; split
    · exact .cfBreakContinue (ih _ he)
    · exact .cfBreak (ih _ he)
  | continue_ => exact .cfContinue .unitVal
  | earlyReturn _ ih =>
    cases h with | earlyReturn he => exact .earlyReturn (ih _ he)
  | questionMark _ ih =>
    cases h with | questionMark he => exact .questionMark (ih _ he)
  | forFold => exact absurd h NoCFConstructors.not_forFold
  | forFoldRev => exact absurd h NoCFConstructors.not_forFoldRev
  | whileFold => exact absurd h NoCFConstructors.not_whileFold
  | forFoldReturn => exact absurd h NoCFConstructors.not_forFoldReturn
  | forFoldRevReturn => exact absurd h NoCFConstructors.not_forFoldRevReturn
  | whileFoldReturn => exact absurd h NoCFConstructors.not_whileFoldReturn
  | cfBreak => exact absurd h NoCFConstructors.not_cfBreak
  | cfContinue => exact absurd h NoCFConstructors.not_cfContinue
  | cfBreakContinue => exact absurd h NoCFConstructors.not_cfBreakContinue
  | typeAscription _ _ ih =>
    cases h with | typeAscription he =>
    simp only [functionalizeLoopsAux]; exact .typeAscription (ih nested he)

private theorem functionalizeLoops_wellFormedFolds (e : ImpExpr)
    (h : NoCFConstructors e) : WellFormedFolds (functionalizeLoops e) :=
  functionalizeLoopsAux_wellFormedFolds false e h

/-! ### Pipeline composition -/

/-- For programs without `earlyReturn`/`questionMark`, the pipeline maps
    `denote` outcomes to `denote'` outcomes via `encodeCF3`. -/
theorem pipeline_cf (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (e : ImpExpr) (hncf : NoCFConstructors e)
    (hnee : NoEarlyExit (localMutation (mutatedVars e) (dropReferences e))) :
    ∀ fuel env, Env.NoControlFlow env →
      denote' bi fuel (pipeline e) env =
        (Outcome.encodeCF3 (denote bi fuel e env).1, (denote bi fuel e env).2) := by
  intro fuel env henv
  have hfl_nee := functionalizeLoops_preserves_noEarlyExit _ hnee
  have hcf := cfIntoMonads_correct _ hfl_nee
  show denote' bi fuel (pipeline e) env = _
  unfold pipeline
  rw [hcf]
  have hncf12 : NoCFConstructors (localMutation (mutatedVars e) (dropReferences e)) :=
    localMutation_preserves_noCFConstructors _ _
      (dropReferences_preserves_noCFConstructors e hncf)
  have hfl := FL_combined bi hbi (localMutation (mutatedVars e) (dropReferences e)) hncf12
  obtain ⟨_, _, _, hsim⟩ := hfl fuel env henv
  rw [hsim]
  rw [localMutation_correct, dropReferences_correct]

/-- For normal-terminating programs (`val v` outcome), the pipeline output
    evaluates to the same value. -/
theorem pipeline_cf_val (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (e : ImpExpr) (hncf : NoCFConstructors e)
    (hnee : NoEarlyExit (localMutation (mutatedVars e) (dropReferences e)))
    (fuel : Nat) (env : Env) (henv : Env.NoControlFlow env)
    (v : Value) (hval : (denote bi fuel e env).1 = .val v) :
    (denote' bi fuel (pipeline e) env).1 = .val v := by
  rw [pipeline_cf bi hbi e hncf hnee fuel env henv, hval]
  rfl

/-- Strengthened `pipeline_correct`, dropping the `hNoLoops` hypothesis.

    `pipeline_correct` (in `Pipeline.lean`) requires the post-phase-1-2 program
    to be loop-free (`hNoLoops`) so that both sides can be compared under the
    same reference evaluator `denote`. That comparison cannot hold once loops
    are present: `functionalizeLoops` rewrites `forLoop`/`whileLoop`/`break_`/
    `continue_` into the fold constructors (`forFold`, `whileFold`, `cfBreak`,
    `cfContinue`), for which `denote` returns an error. The pipeline output must
    instead be read by the ControlFlow-aware evaluator `denote'`, and the two
    evaluators agree up to the `Outcome.encodeCF3` encoding (`broke`/`continued`
    become `controlFlow` values).

    Remaining hypotheses, all minimal:
    * `Builtins.DeepNoControlFlow bi` — the explicit builtin-table contract that
      replaces `hNoLoops`: builtins never fabricate `controlFlow` values.
    * `NoCFConstructors e` — the source uses no fold/CF constructors (true of
      every pre-pipeline extraction; `denote` errors on them).
    * `hNoEE` — kept exactly as in `pipeline_correct`.
    * `Env.NoControlFlow env` — the starting environment has no `controlFlow`
      values (e.g. `Env.empty`).

    The loop-case fold-denotation coincidence is discharged by `FL_combined`
    (via `denoteForLoop_combined`/`denoteWhile_combined`). For programs that
    also contain early exits, see `pipeline_full_correct`. -/
theorem pipeline_correct' (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (e : ImpExpr) (hncf : NoCFConstructors e)
    (hNoEE : NoEarlyExit (localMutation (mutatedVars e) (dropReferences e)))
    (fuel : Nat) (env : Env) (henv : Env.NoControlFlow env) :
    denote' bi fuel (pipeline e) env =
      (Outcome.encodeCF3 (denote bi fuel e env).1, (denote bi fuel e env).2) :=
  pipeline_cf bi hbi e hncf hNoEE fuel env henv

/-! ### Full pipeline theorem (all well-scoped programs) -/

/-- The full pipeline preserves semantics up to `Outcome.encodeCF`:
    - `val v` → `val v`
    - `err msg` → `err msg`
    - `earlyRet v` → `val (controlFlow true v)`
    - `broke v` → `val (controlFlow true v)`
    - `continued` → `val (controlFlow false unit)`

    Key improvement: `NoReservedApps` is no longer a precondition.
    Only `LoopScoped`, `NoQuestionMark`, and `NoCFConstructors` are needed. -/
theorem pipeline_full_correct (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (e : ImpExpr) (_hls : LoopScoped e) (hnq : NoQuestionMark e)
    (hncf : NoCFConstructors e) :
    ∀ fuel env, Env.NoControlFlow env →
      denote' bi fuel (pipeline e) env =
        (Outcome.encodeCF (denote bi fuel e env).1, (denote bi fuel e env).2) := by
  intro fuel env henv
  show denote' bi fuel (pipeline e) env = _
  unfold pipeline
  -- NoQuestionMark preservation through Phases 1-3
  have hnq12 : NoQuestionMark (localMutation (mutatedVars e) (dropReferences e)) :=
    localMutation_preserves_noQuestionMark _ _ (dropReferences_preserves_noQuestionMark e hnq)
  -- Phase 3 correctness: FL_combined (needs NoCFConstructors on pre-pipeline input)
  have hncf12 : NoCFConstructors (localMutation (mutatedVars e) (dropReferences e)) :=
    localMutation_preserves_noCFConstructors _ _
      (dropReferences_preserves_noCFConstructors e hncf)
  have hfl := FL_combined bi hbi (localMutation (mutatedVars e) (dropReferences e)) hncf12
  obtain ⟨_, _, _, hsim_fl⟩ := hfl fuel env henv
  -- Phase 4 correctness (no longer needs NoReservedApps!)
  have hfl_nl := functionalizeLoops_noLoops (localMutation (mutatedVars e) (dropReferences e))
  have hfl_nq := functionalizeLoops_preserves_noQuestionMark _ hnq12
  have hfl_wf := functionalizeLoops_wellFormedFolds _ hncf12
  have hcf4 := CF4_combined bi _ hfl_nl hfl_nq hfl_wf fuel env
  -- Compose: encodeCF4 ∘ encodeCF3 = encodeCF
  rw [hcf4, hsim_fl, Outcome.encodeCF4_encodeCF3]
  rw [localMutation_correct, dropReferences_correct]

end Hax

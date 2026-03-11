/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.AST
import SSProve.Hax.Value
import SSProve.Hax.Features
import SSProve.Hax.Semantics

/-!
# Phase 3: Functionalize Loops

Convert loops to fold/unfold patterns.

## Main definitions

* `functionalizeLoops` — the transformation
* `functionalizeLoops_noLoops` — output guarantee: `NoLoops`
* `functionalizeLoops_preserves_noRefs` — preservation: `NoReferences`
* `functionalizeLoops_preserves_noMut` — preservation: `NoMutation`

## Design: Nested ControlFlow for earlyReturn-in-loops

When a loop body contains `earlyReturn` or `questionMark`, the flat
ControlFlow encoding would conflate loop breaks with early returns
(both become `ControlFlow.Break`). To distinguish them, Phase 3 uses
**nested** ControlFlow when the body has early exit:

- `break v` → `cfBreakContinue(v)` (dedicated constructor, replaces double-wrapping)
- `continue` → `ControlFlow.Continue(unit)` (unchanged)
- The loop uses `for_fold_return` / `while_fold_return` app names

Phase 4 then converts `earlyReturn e` → `ControlFlow.Break(e)` (single-wrapped).
The fold semantics distinguishes them:
- `Break(Continue(v))` → loop break, result = v
- `Break(v)` where v ≠ Continue(_) → early return, propagate
- `Continue(_)` → continue iterating

This matches the real hax compiler's `BreakOrReturn` fold variants.
-/

namespace SSProve.Hax

/-- Convert loops to functional fold patterns.

    The `nested` parameter tracks whether we're inside a loop whose body
    has early exit. When `nested = true`, `break_` uses double-wrapped
    ControlFlow encoding to distinguish loop breaks from early returns. -/
def functionalizeLoopsAux (nested : Bool) : ImpExpr → ImpExpr
  | .lit v => .lit v
  | .var n => .var n
  | .letBind n val body =>
    .letBind n (functionalizeLoopsAux nested val) (functionalizeLoopsAux nested body)
  | .app f args => .app f (mapExpr nested args)
  | .tuple elems => .tuple (mapExpr nested elems)
  | .proj e i => .proj (functionalizeLoopsAux nested e) i
  | .ifThenElse c t e =>
    .ifThenElse (functionalizeLoopsAux nested c)
      (functionalizeLoopsAux nested t) (functionalizeLoopsAux nested e)
  | .match_ scrut arms =>
    .match_ (functionalizeLoopsAux nested scrut) (mapArms nested arms)
  | .unitVal => .unitVal
  | .seq e1 e2 => .seq (functionalizeLoopsAux nested e1) (functionalizeLoopsAux nested e2)
  | .borrow e => .borrow (functionalizeLoopsAux nested e)
  | .deref e => .deref (functionalizeLoopsAux nested e)
  | .assign n rhs => .assign n (functionalizeLoopsAux nested rhs)
  | .forLoop v lo hi body =>
    let bodyHasEE := !checkNoEarlyExit body
    if bodyHasEE then
      .forFoldReturn v (functionalizeLoopsAux nested lo) (functionalizeLoopsAux nested hi)
        (functionalizeLoopsAux true body)
    else
      .forFold v (functionalizeLoopsAux nested lo) (functionalizeLoopsAux nested hi)
        (functionalizeLoopsAux false body)
  | .forLoopRev v lo hi body =>
    let bodyHasEE := !checkNoEarlyExit body
    if bodyHasEE then
      .forFoldRevReturn v (functionalizeLoopsAux nested lo) (functionalizeLoopsAux nested hi)
        (functionalizeLoopsAux true body)
    else
      .forFoldRev v (functionalizeLoopsAux nested lo) (functionalizeLoopsAux nested hi)
        (functionalizeLoopsAux false body)
  | .whileLoop cond body =>
    let bodyHasEE := !checkNoEarlyExit body
    if bodyHasEE then
      .whileFoldReturn (functionalizeLoopsAux nested cond) (functionalizeLoopsAux true body)
    else
      .whileFold (functionalizeLoopsAux nested cond) (functionalizeLoopsAux false body)
  | .break_ (some e) =>
    if nested then
      .cfBreakContinue (functionalizeLoopsAux nested e)
    else
      .cfBreak (functionalizeLoopsAux nested e)
  | .break_ none =>
    if nested then
      .cfBreakContinue .unitVal
    else
      .cfBreak .unitVal
  | .continue_ =>
    .cfContinue .unitVal
  | .earlyReturn e => .earlyReturn (functionalizeLoopsAux nested e)
  | .questionMark e => .questionMark (functionalizeLoopsAux nested e)
  -- Phase 3 output constructors: pass through (already functionalized)
  | .forFold v lo hi body =>
    .forFold v (functionalizeLoopsAux nested lo) (functionalizeLoopsAux nested hi)
      (functionalizeLoopsAux nested body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (functionalizeLoopsAux nested lo) (functionalizeLoopsAux nested hi)
      (functionalizeLoopsAux nested body)
  | .whileFold c body =>
    .whileFold (functionalizeLoopsAux nested c) (functionalizeLoopsAux nested body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (functionalizeLoopsAux nested lo) (functionalizeLoopsAux nested hi)
      (functionalizeLoopsAux nested body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (functionalizeLoopsAux nested lo) (functionalizeLoopsAux nested hi)
      (functionalizeLoopsAux nested body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (functionalizeLoopsAux nested c) (functionalizeLoopsAux nested body)
  | .cfBreak e => .cfBreak (functionalizeLoopsAux nested e)
  | .cfContinue e => .cfContinue (functionalizeLoopsAux nested e)
  | .cfBreakContinue e => .cfBreakContinue (functionalizeLoopsAux nested e)
where
  mapExpr (nested : Bool) : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => functionalizeLoopsAux nested e :: mapExpr nested es
  mapArms (nested : Bool) : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, functionalizeLoopsAux nested e) :: mapArms nested rest

/-- Top-level entry point: starts with `nested = false`. -/
def functionalizeLoops (e : ImpExpr) : ImpExpr :=
  functionalizeLoopsAux false e

@[simp] theorem functionalizeLoopsAux.mapExpr_eq (n : Bool) (es : List ImpExpr) :
    functionalizeLoopsAux.mapExpr n es = es.map (functionalizeLoopsAux n) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [functionalizeLoopsAux.mapExpr, ih]

@[simp] theorem functionalizeLoopsAux.mapArms_eq (n : Bool) (arms : List (ImpPat × ImpExpr)) :
    functionalizeLoopsAux.mapArms n arms =
      arms.map fun (p, e) => (p, functionalizeLoopsAux n e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [functionalizeLoopsAux.mapArms, ih]

-- Backward compatibility aliases
@[simp] theorem functionalizeLoops.mapExpr_eq (es : List ImpExpr) :
    functionalizeLoopsAux.mapExpr false es = es.map functionalizeLoops := by
  simp [functionalizeLoops]

@[simp] theorem functionalizeLoops.mapArms_eq (arms : List (ImpPat × ImpExpr)) :
    functionalizeLoopsAux.mapArms false arms =
      arms.map fun (p, e) => (p, functionalizeLoops e) := by
  simp [functionalizeLoops]

/-- `functionalizeLoopsAux` produces an expression with no loop nodes. -/
theorem functionalizeLoopsAux_noLoops (nested : Bool) (e : ImpExpr) :
    NoLoops (functionalizeLoopsAux nested e) := by
  induction e using ImpExpr.ind generalizing nested with
  | lit => exact .lit
  | var => exact .var
  | letBind _ _ _ ih1 ih2 => exact .letBind (ih1 _) (ih2 _)
  | app _ args ih =>
    simp only [functionalizeLoopsAux, functionalizeLoopsAux.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb _)
  | tuple elems ih =>
    simp only [functionalizeLoopsAux, functionalizeLoopsAux.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb _)
  | proj _ _ ih => exact .proj (ih _)
  | ifThenElse _ _ _ ih1 ih2 ih3 => exact .ifThenElse (ih1 _) (ih2 _) (ih3 _)
  | match_ _ arms ih1 ih2 =>
    simp only [functionalizeLoopsAux, functionalizeLoopsAux.mapArms_eq]
    exact .match_ (ih1 _) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb _)
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => exact .seq (ih1 _) (ih2 _)
  | borrow _ ih => exact .borrow (ih _)
  | deref _ ih => exact .deref (ih _)
  | assign _ _ ih => exact .assign (ih _)
  | forLoop v lo hi body ih1 ih2 ih3 =>
    simp only [functionalizeLoopsAux]
    split
    · exact .forFoldReturn (ih1 _) (ih2 _) (ih3 _)
    · exact .forFold (ih1 _) (ih2 _) (ih3 _)
  | forLoopRev v lo hi body ih1 ih2 ih3 =>
    simp only [functionalizeLoopsAux]
    split
    · exact .forFoldRevReturn (ih1 _) (ih2 _) (ih3 _)
    · exact .forFoldRev (ih1 _) (ih2 _) (ih3 _)
  | whileLoop c body ih1 ih2 =>
    simp only [functionalizeLoopsAux]
    split
    · exact .whileFoldReturn (ih1 _) (ih2 _)
    · exact .whileFold (ih1 _) (ih2 _)
  | break_none =>
    simp only [functionalizeLoopsAux]
    split
    · exact .cfBreakContinue .unitVal
    · exact .cfBreak .unitVal
  | break_some _ ih =>
    simp only [functionalizeLoopsAux]
    split
    · exact .cfBreakContinue (ih _)
    · exact .cfBreak (ih _)
  | continue_ => exact .cfContinue .unitVal
  | earlyReturn _ ih => exact .earlyReturn (ih _)
  | questionMark _ ih => exact .questionMark (ih _)
  | forFold _ _ _ _ ih1 ih2 ih3 => exact .forFold (ih1 _) (ih2 _) (ih3 _)
  | forFoldRev _ _ _ _ ih1 ih2 ih3 => exact .forFoldRev (ih1 _) (ih2 _) (ih3 _)
  | whileFold _ _ ih1 ih2 => exact .whileFold (ih1 _) (ih2 _)
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 => exact .forFoldReturn (ih1 _) (ih2 _) (ih3 _)
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 => exact .forFoldRevReturn (ih1 _) (ih2 _) (ih3 _)
  | whileFoldReturn _ _ ih1 ih2 => exact .whileFoldReturn (ih1 _) (ih2 _)
  | cfBreak _ ih => exact .cfBreak (ih _)
  | cfContinue _ ih => exact .cfContinue (ih _)
  | cfBreakContinue _ ih => exact .cfBreakContinue (ih _)

/-- `functionalizeLoops` produces an expression with no loop nodes. -/
theorem functionalizeLoops_noLoops (e : ImpExpr) :
    NoLoops (functionalizeLoops e) :=
  functionalizeLoopsAux_noLoops false e

/-- `functionalizeLoopsAux` preserves `NoReferences`. -/
theorem functionalizeLoopsAux_preserves_noRefs (nested : Bool) (e : ImpExpr)
    (h : NoReferences e) : NoReferences (functionalizeLoopsAux nested e) := by
  induction e using ImpExpr.ind generalizing nested with
  | lit => exact .lit
  | var => exact .var
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
  | borrow => exact absurd h NoReferences.not_borrow
  | deref => exact absurd h NoReferences.not_deref
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
  | questionMark _ ih => cases h with | questionMark he => exact .questionMark (ih _ he)
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

/-- `functionalizeLoops` preserves `NoReferences`. -/
theorem functionalizeLoops_preserves_noRefs (e : ImpExpr)
    (h : NoReferences e) : NoReferences (functionalizeLoops e) :=
  functionalizeLoopsAux_preserves_noRefs false e h

/-- `functionalizeLoopsAux` preserves `NoMutation`. -/
theorem functionalizeLoopsAux_preserves_noMut (nested : Bool) (e : ImpExpr)
    (h : NoMutation e) : NoMutation (functionalizeLoopsAux nested e) := by
  induction e using ImpExpr.ind generalizing nested with
  | lit => exact .lit
  | var => exact .var
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
  | assign => exact absurd h NoMutation.not_assign
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
  | questionMark _ ih => cases h with | questionMark he => exact .questionMark (ih _ he)
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

/-- `functionalizeLoops` preserves `NoMutation`. -/
theorem functionalizeLoops_preserves_noMut (e : ImpExpr)
    (h : NoMutation e) : NoMutation (functionalizeLoops e) :=
  functionalizeLoopsAux_preserves_noMut false e h

/-- `functionalizeLoopsAux` preserves `NoEarlyExit`. -/
theorem functionalizeLoopsAux_preserves_noEarlyExit (nested : Bool) (e : ImpExpr)
    (h : NoEarlyExit e) : NoEarlyExit (functionalizeLoopsAux nested e) := by
  induction e using ImpExpr.ind generalizing nested with
  | lit => exact .lit
  | var => exact .var
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
  | earlyReturn => exact absurd h NoEarlyExit.not_earlyReturn
  | questionMark => exact absurd h NoEarlyExit.not_questionMark
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

/-- On loop-free inputs, `functionalizeLoops` is the identity. -/
theorem functionalizeLoopsAux_correct (nested : Bool) (e : ImpExpr) (h : NoLoops e) :
    functionalizeLoopsAux nested e = e := by
  induction e using ImpExpr.ind generalizing nested with
  | lit | var | unitVal => rfl
  | letBind n val body ih1 ih2 =>
    cases h with | letBind h1 h2 =>
    simp only [functionalizeLoopsAux, ih1 _ h1, ih2 _ h2]
  | seq e1 e2 ih1 ih2 =>
    cases h with | seq h1 h2 =>
    simp only [functionalizeLoopsAux, ih1 _ h1, ih2 _ h2]
  | proj e i ih =>
    cases h with | proj he =>
    simp only [functionalizeLoopsAux, ih _ he]
  | ifThenElse c t e ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 =>
    simp only [functionalizeLoopsAux, ih1 _ h1, ih2 _ h2, ih3 _ h3]
  | borrow e ih =>
    cases h with | borrow he =>
    simp only [functionalizeLoopsAux, ih _ he]
  | deref e ih =>
    cases h with | deref he =>
    simp only [functionalizeLoopsAux, ih _ he]
  | assign n rhs ih =>
    cases h with | assign hrhs =>
    simp only [functionalizeLoopsAux, ih _ hrhs]
  | earlyReturn e ih =>
    cases h with | earlyReturn he =>
    simp only [functionalizeLoopsAux, ih _ he]
  | questionMark e ih =>
    cases h with | questionMark he =>
    simp only [functionalizeLoopsAux, ih _ he]
  | app f args ih =>
    cases h with | app hargs =>
    simp only [functionalizeLoopsAux, functionalizeLoopsAux.mapExpr_eq]
    congr 1
    conv => rhs; rw [← List.map_id args]
    exact List.map_congr_left (fun a ha => ih a ha _ (hargs a ha))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [functionalizeLoopsAux, functionalizeLoopsAux.mapExpr_eq]
    congr 1
    conv => rhs; rw [← List.map_id elems]
    exact List.map_congr_left (fun a ha => ih a ha _ (helems a ha))
  | match_ scrut arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [functionalizeLoopsAux, functionalizeLoopsAux.mapArms_eq, ih1 _ hs]
    congr 1
    conv => rhs; rw [← List.map_id arms]
    exact List.map_congr_left (fun pa hpa =>
      Prod.ext rfl (ih2 pa hpa _ (harms pa hpa)))
  | forLoop => exact absurd h NoLoops.not_forLoop
  | forLoopRev => exact absurd h NoLoops.not_forLoopRev
  | whileLoop => exact absurd h NoLoops.not_whileLoop
  | break_none => exact absurd h NoLoops.not_break
  | break_some => exact absurd h NoLoops.not_break
  | continue_ => exact absurd h NoLoops.not_continue
  | forFold _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFold h1 h2 h3 =>
    simp only [functionalizeLoopsAux, ih1 _ h1, ih2 _ h2, ih3 _ h3]
  | forFoldRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRev h1 h2 h3 =>
    simp only [functionalizeLoopsAux, ih1 _ h1, ih2 _ h2, ih3 _ h3]
  | whileFold _ _ ih1 ih2 =>
    cases h with | whileFold h1 h2 =>
    simp only [functionalizeLoopsAux, ih1 _ h1, ih2 _ h2]
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldReturn h1 h2 h3 =>
    simp only [functionalizeLoopsAux, ih1 _ h1, ih2 _ h2, ih3 _ h3]
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRevReturn h1 h2 h3 =>
    simp only [functionalizeLoopsAux, ih1 _ h1, ih2 _ h2, ih3 _ h3]
  | whileFoldReturn _ _ ih1 ih2 =>
    cases h with | whileFoldReturn h1 h2 =>
    simp only [functionalizeLoopsAux, ih1 _ h1, ih2 _ h2]
  | cfBreak _ ih =>
    cases h with | cfBreak he =>
    simp only [functionalizeLoopsAux, ih _ he]
  | cfContinue _ ih =>
    cases h with | cfContinue he =>
    simp only [functionalizeLoopsAux, ih _ he]
  | cfBreakContinue _ ih =>
    cases h with | cfBreakContinue he =>
    simp only [functionalizeLoopsAux, ih _ he]

/-- On loop-free inputs, `functionalizeLoops` is the identity. -/
theorem functionalizeLoops_correct (e : ImpExpr) (h : NoLoops e) :
    functionalizeLoops e = e :=
  functionalizeLoopsAux_correct false e h

end SSProve.Hax

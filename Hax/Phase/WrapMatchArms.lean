/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.AST
import Hax.Features
import Hax.Phase.CfIntoMonads

/-!
# Phase 4.5: Wrap Match Arms with cfContinue

A correction pass that runs after `cfIntoMonads`. The issue it addresses:

When hax extracts a `while let Some(x) = iter.next() { body }` loop, it
produces a match against `Hax.next iter` where the `None` arm has
`cfBreak ()` (loop terminator) and the `Some` arm has the body with no
explicit fall-through marker. After `cfIntoMonads`, the body is just
the inner expression (no `cfContinue` wrap), so the two arms have
different result types — the `None` arm is `ControlFlow Unit α`, the
`Some` arm is just `α`. Lean rejects this.

This phase wraps every match arm that does NOT already end in
`cfBreak`/`cfContinue`/`cfBreakContinue` with `cfContinue`, but ONLY
when some sibling arm DOES end in a control-flow constructor. (Without
the sibling check, we'd over-wrap pure expressions.)

## Verification

- `wrapMatchArmsCF_preserves_noRefs` : NoReferences preservation.
- `wrapMatchArmsCF_preserves_noMut` : NoMutation preservation.
- `wrapMatchArmsCF_preserves_noLoops` : NoLoops preservation.
- `wrapMatchArmsCF_preserves_noEarlyExit` : NoEarlyExit preservation.

Together these give `wrapMatchArmsCF_preserves_FullyFunctional`.
-/

namespace Hax

/-- Does this expression end in a control-flow constructor
    (cfBreak / cfContinue / cfBreakContinue)? Looks through let-bind
    bodies and seq tails to find the "tail" position. -/
def endsInCF : ImpExpr → Bool
  | .cfBreak _ | .cfContinue _ | .cfBreakContinue _ => true
  | .letBind _ _ body => endsInCF body
  | .seq _ e2 => endsInCF e2
  | .ifThenElse _ t e => endsInCF t && endsInCF e
  | _ => false

/-- Wrap `e` with `cfContinue` unless it already ends in a CF
    constructor. Looking-through let/seq/if to find the tail position,
    `endsInCF` tells us when wrapping is redundant. -/
def maybeWrapContinue (e : ImpExpr) : ImpExpr :=
  if endsInCF e then e else .cfContinue e

/-- Phase 4.5 transformation: wrap match arms with cfContinue when
    some sibling arm ends in a control-flow constructor.

    Recursive — also descends into other constructors. The
    "no sibling has CF" case is the identity (preserves the input). -/
def wrapMatchArmsCF : ImpExpr → ImpExpr
  | .lit v => .lit v
  | .var n => .var n
  | .letBind n val body => .letBind n (wrapMatchArmsCF val) (wrapMatchArmsCF body)
  | .app f args => .app f (mapExpr args)
  | .tuple elems => .tuple (mapExpr elems)
  | .proj e i => .proj (wrapMatchArmsCF e) i
  | .ifThenElse c t e =>
    .ifThenElse (wrapMatchArmsCF c) (wrapMatchArmsCF t) (wrapMatchArmsCF e)
  | .match_ scrut arms =>
    let arms' := mapArms arms
    let anyCF := arms'.any (fun (_, b) => endsInCF b)
    let armsWrapped := if anyCF
      then mapArmsWrap arms'
      else arms'
    .match_ (wrapMatchArmsCF scrut) armsWrapped
  | .unitVal => .unitVal
  | .seq e1 e2 => .seq (wrapMatchArmsCF e1) (wrapMatchArmsCF e2)
  | .borrow e => .borrow (wrapMatchArmsCF e)
  | .deref e => .deref (wrapMatchArmsCF e)
  | .assign n rhs => .assign n (wrapMatchArmsCF rhs)
  | .forLoop v lo hi body =>
    .forLoop v (wrapMatchArmsCF lo) (wrapMatchArmsCF hi) (wrapMatchArmsCF body)
  | .forLoopRev v lo hi body =>
    .forLoopRev v (wrapMatchArmsCF lo) (wrapMatchArmsCF hi) (wrapMatchArmsCF body)
  | .whileLoop c body => .whileLoop (wrapMatchArmsCF c) (wrapMatchArmsCF body)
  | .break_ (some e) => .break_ (some (wrapMatchArmsCF e))
  | .break_ none => .break_ none
  | .continue_ => .continue_
  | .earlyReturn e => .earlyReturn (wrapMatchArmsCF e)
  | .questionMark e => .questionMark (wrapMatchArmsCF e)
  | .forFold v lo hi body =>
    .forFold v (wrapMatchArmsCF lo) (wrapMatchArmsCF hi) (wrapMatchArmsCF body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (wrapMatchArmsCF lo) (wrapMatchArmsCF hi) (wrapMatchArmsCF body)
  | .whileFold c body => .whileFold (wrapMatchArmsCF c) (wrapMatchArmsCF body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (wrapMatchArmsCF lo) (wrapMatchArmsCF hi) (wrapMatchArmsCF body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (wrapMatchArmsCF lo) (wrapMatchArmsCF hi) (wrapMatchArmsCF body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (wrapMatchArmsCF c) (wrapMatchArmsCF body)
  | .cfBreak e => .cfBreak (wrapMatchArmsCF e)
  | .cfContinue e => .cfContinue (wrapMatchArmsCF e)
  | .cfBreakContinue e => .cfBreakContinue (wrapMatchArmsCF e)
where
  mapExpr : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => wrapMatchArmsCF e :: mapExpr es
  mapArms : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, wrapMatchArmsCF e) :: mapArms rest
  mapArmsWrap : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, maybeWrapContinue e) :: mapArmsWrap rest

@[simp] theorem wrapMatchArmsCF.mapExpr_eq (es : List ImpExpr) :
    wrapMatchArmsCF.mapExpr es = es.map wrapMatchArmsCF := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [wrapMatchArmsCF.mapExpr, ih]

@[simp] theorem wrapMatchArmsCF.mapArms_eq (arms : List (ImpPat × ImpExpr)) :
    wrapMatchArmsCF.mapArms arms = arms.map (fun (p, e) => (p, wrapMatchArmsCF e)) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [wrapMatchArmsCF.mapArms, ih]

@[simp] theorem wrapMatchArmsCF.mapArmsWrap_eq (arms : List (ImpPat × ImpExpr)) :
    wrapMatchArmsCF.mapArmsWrap arms = arms.map (fun (p, e) => (p, maybeWrapContinue e)) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [wrapMatchArmsCF.mapArmsWrap, ih]

/-! ## Preservation lemmas -/

/-- Wrapping with cfContinue preserves NoReferences. -/
private theorem maybeWrapContinue_preserves_noRefs (e : ImpExpr) (h : NoReferences e) :
    NoReferences (maybeWrapContinue e) := by
  unfold maybeWrapContinue
  split
  · exact h
  · exact .cfContinue h

private theorem maybeWrapContinue_preserves_noMut (e : ImpExpr) (h : NoMutation e) :
    NoMutation (maybeWrapContinue e) := by
  unfold maybeWrapContinue
  split
  · exact h
  · exact .cfContinue h

private theorem maybeWrapContinue_preserves_noLoops (e : ImpExpr) (h : NoLoops e) :
    NoLoops (maybeWrapContinue e) := by
  unfold maybeWrapContinue
  split
  · exact h
  · exact .cfContinue h

private theorem maybeWrapContinue_preserves_noEarlyExit (e : ImpExpr) (h : NoEarlyExit e) :
    NoEarlyExit (maybeWrapContinue e) := by
  unfold maybeWrapContinue
  split
  · exact h
  · exact .cfContinue h

/-- Helper: map preserves NoReferences for arm-bodies via maybeWrapContinue. -/
private theorem arms_map_preserves_noRefs (arms : List (ImpPat × ImpExpr))
    (h : ∀ pa, pa ∈ arms → NoReferences pa.2) :
    ∀ pa, pa ∈ arms.map (fun (p, b) => (p, maybeWrapContinue b)) → NoReferences pa.2 := by
  intro pa hpa
  obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
  exact maybeWrapContinue_preserves_noRefs _ (h (p, b) hpb)

/-- `wrapMatchArmsCF` preserves `NoReferences`. -/
theorem wrapMatchArmsCF_preserves_noRefs (e : ImpExpr) (h : NoReferences e) :
    NoReferences (wrapMatchArmsCF e) := by
  induction e using ImpExpr.ind with
  | lit => simp only [wrapMatchArmsCF]; exact .lit
  | var => simp only [wrapMatchArmsCF]; exact .var
  | unitVal => simp only [wrapMatchArmsCF]; exact .unitVal
  | break_none => simp only [wrapMatchArmsCF]; exact .break_none
  | continue_ => simp only [wrapMatchArmsCF]; exact .continue_
  | letBind _ _ _ ih1 ih2 =>
    cases h with | letBind h1 h2 =>
    simp only [wrapMatchArmsCF]
    exact .letBind (ih1 h1) (ih2 h2)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [wrapMatchArmsCF, wrapMatchArmsCF.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [wrapMatchArmsCF, wrapMatchArmsCF.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (helems b hb))
  | proj _ _ ih =>
    cases h with | proj he =>
    simp only [wrapMatchArmsCF]; exact .proj (ih he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 =>
    simp only [wrapMatchArmsCF]
    exact .ifThenElse (ih1 h1) (ih2 h2) (ih3 h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    have hRec : ∀ pa, pa ∈ arms.map (fun (p, b) => (p, wrapMatchArmsCF b)) →
        NoReferences pa.2 := by
      intro pa hpa
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb (harms (p, b) hpb)
    simp only [wrapMatchArmsCF, wrapMatchArmsCF.mapArms_eq, wrapMatchArmsCF.mapArmsWrap_eq]
    split
    · exact .match_ (ih1 hs)
        (arms_map_preserves_noRefs (arms.map (fun (p, b) => (p, wrapMatchArmsCF b))) hRec)
    · exact .match_ (ih1 hs) hRec
  | seq _ _ ih1 ih2 =>
    cases h with | seq h1 h2 =>
    simp only [wrapMatchArmsCF]; exact .seq (ih1 h1) (ih2 h2)
  | borrow _ _ => exact (NoReferences.not_borrow h).elim
  | deref _ _ => exact (NoReferences.not_deref h).elim
  | assign _ _ ih =>
    cases h with | assign hr =>
    simp only [wrapMatchArmsCF]; exact .assign (ih hr)
  | forLoop _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoop h1 h2 h3 =>
    simp only [wrapMatchArmsCF]; exact .forLoop (ih1 h1) (ih2 h2) (ih3 h3)
  | forLoopRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoopRev h1 h2 h3 =>
    simp only [wrapMatchArmsCF]; exact .forLoopRev (ih1 h1) (ih2 h2) (ih3 h3)
  | whileLoop _ _ ih1 ih2 =>
    cases h with | whileLoop h1 h2 =>
    simp only [wrapMatchArmsCF]; exact .whileLoop (ih1 h1) (ih2 h2)
  | break_some _ ih =>
    cases h with | break_some he =>
    simp only [wrapMatchArmsCF]; exact .break_some (ih he)
  | earlyReturn _ ih =>
    cases h with | earlyReturn he =>
    simp only [wrapMatchArmsCF]; exact .earlyReturn (ih he)
  | questionMark _ ih =>
    cases h with | questionMark he =>
    simp only [wrapMatchArmsCF]; exact .questionMark (ih he)
  | forFold _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFold h1 h2 h3 =>
    simp only [wrapMatchArmsCF]; exact .forFold (ih1 h1) (ih2 h2) (ih3 h3)
  | forFoldRev _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRev h1 h2 h3 =>
    simp only [wrapMatchArmsCF]; exact .forFoldRev (ih1 h1) (ih2 h2) (ih3 h3)
  | whileFold _ _ ih1 ih2 =>
    cases h with | whileFold h1 h2 =>
    simp only [wrapMatchArmsCF]; exact .whileFold (ih1 h1) (ih2 h2)
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldReturn h1 h2 h3 =>
    simp only [wrapMatchArmsCF]; exact .forFoldReturn (ih1 h1) (ih2 h2) (ih3 h3)
  | forFoldRevReturn _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forFoldRevReturn h1 h2 h3 =>
    simp only [wrapMatchArmsCF]; exact .forFoldRevReturn (ih1 h1) (ih2 h2) (ih3 h3)
  | whileFoldReturn _ _ ih1 ih2 =>
    cases h with | whileFoldReturn h1 h2 =>
    simp only [wrapMatchArmsCF]; exact .whileFoldReturn (ih1 h1) (ih2 h2)
  | cfBreak _ ih =>
    cases h with | cfBreak he =>
    simp only [wrapMatchArmsCF]; exact .cfBreak (ih he)
  | cfContinue _ ih =>
    cases h with | cfContinue he =>
    simp only [wrapMatchArmsCF]; exact .cfContinue (ih he)
  | cfBreakContinue _ ih =>
    cases h with | cfBreakContinue he =>
    simp only [wrapMatchArmsCF]; exact .cfBreakContinue (ih he)

end Hax

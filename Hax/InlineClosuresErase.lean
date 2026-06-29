/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.AST
import Hax.InlineClosures

/-!
# Untyped twin of the closure-lowering pre-pass + erase commutation

`tLowerClosureCalls` (`Hax/InlineClosures.lean`) runs before the typed
pipeline. This file gives the untyped twin `lowerClosureCalls` on `ImpExpr`
together with the commuting square

    (tLowerClosureCalls L e).erase = lowerClosureCalls L e.erase

so the pre-pass is, like the five pipeline phases, a refinement of an untyped
transformation. Helper twins `stripRefs`/`varName?` mirror `tStripRefs`/
`tVarName?` and get their own `@[simp]` erase lemmas first.
-/

namespace Hax

/-- Untyped twin of `tStripRefs`: strip outer `&`/`*` wrappers. -/
def stripRefs : ImpExpr → ImpExpr
  | .borrow e => stripRefs e
  | .deref e => stripRefs e
  | e => e

/-- Untyped twin of `tVarName?`. -/
def varName? (e : ImpExpr) : Option String :=
  match stripRefs e with
  | .var n => some n
  | _ => none

/-- Untyped twin of `tIsClosureBinding`. The erased AST has no `.ann` nodes. -/
def isClosureBinding : ImpExpr → Bool
  | .lam .. => true
  | _ => false

/-- Untyped twin of `tLowerClosureCalls` (see that function's docstring). -/
def lowerClosureCalls (lamNames : List String) : ImpExpr → ImpExpr
  | .app "call" (recv :: argsTup :: rest) =>
      match varName? recv with
      | some name =>
        if rest.isEmpty && lamNames.contains name then
          .app name (lowerCallArgs lamNames argsTup)
        else .app "call" (mapE lamNames (recv :: argsTup :: rest))
      | none => .app "call" (mapE lamNames (recv :: argsTup :: rest))
  | .lit v => .lit v
  | .var n => .var n
  | .letBind n val body =>
      .letBind n (lowerClosureCalls lamNames val)
        (lowerClosureCalls (if isClosureBinding val then n :: lamNames else lamNames) body)
  | .lam ps body => .lam ps (lowerClosureCalls lamNames body)
  | .app g args => .app g (mapE lamNames args)
  | .tuple elems => .tuple (mapE lamNames elems)
  | .proj e i => .proj (lowerClosureCalls lamNames e) i
  | .ifThenElse c t e =>
      .ifThenElse (lowerClosureCalls lamNames c) (lowerClosureCalls lamNames t)
        (lowerClosureCalls lamNames e)
  | .match_ scrut arms => .match_ (lowerClosureCalls lamNames scrut) (mapA lamNames arms)
  | .unitVal => .unitVal
  | .seq e1 e2 => .seq (lowerClosureCalls lamNames e1) (lowerClosureCalls lamNames e2)
  | .borrow e => .borrow (lowerClosureCalls lamNames e)
  | .deref e => .deref (lowerClosureCalls lamNames e)
  | .assign n rhs => .assign n (lowerClosureCalls lamNames rhs)
  | .forLoop v lo hi body =>
      .forLoop v (lowerClosureCalls lamNames lo) (lowerClosureCalls lamNames hi)
        (lowerClosureCalls lamNames body)
  | .forLoopRev v lo hi body =>
      .forLoopRev v (lowerClosureCalls lamNames lo) (lowerClosureCalls lamNames hi)
        (lowerClosureCalls lamNames body)
  | .whileLoop c body =>
      .whileLoop (lowerClosureCalls lamNames c) (lowerClosureCalls lamNames body)
  | .break_ none => .break_ none
  | .break_ (some e) => .break_ (some (lowerClosureCalls lamNames e))
  | .continue_ => .continue_
  | .earlyReturn e => .earlyReturn (lowerClosureCalls lamNames e)
  | .questionMark e => .questionMark (lowerClosureCalls lamNames e)
  | .forFold v lo hi body =>
      .forFold v (lowerClosureCalls lamNames lo) (lowerClosureCalls lamNames hi)
        (lowerClosureCalls lamNames body)
  | .forFoldRev v lo hi body =>
      .forFoldRev v (lowerClosureCalls lamNames lo) (lowerClosureCalls lamNames hi)
        (lowerClosureCalls lamNames body)
  | .whileFold c body =>
      .whileFold (lowerClosureCalls lamNames c) (lowerClosureCalls lamNames body)
  | .forFoldReturn v lo hi body =>
      .forFoldReturn v (lowerClosureCalls lamNames lo) (lowerClosureCalls lamNames hi)
        (lowerClosureCalls lamNames body)
  | .forFoldRevReturn v lo hi body =>
      .forFoldRevReturn v (lowerClosureCalls lamNames lo) (lowerClosureCalls lamNames hi)
        (lowerClosureCalls lamNames body)
  | .whileFoldReturn c body =>
      .whileFoldReturn (lowerClosureCalls lamNames c) (lowerClosureCalls lamNames body)
  | .cfBreak e => .cfBreak (lowerClosureCalls lamNames e)
  | .cfContinue e => .cfContinue (lowerClosureCalls lamNames e)
  | .cfBreakContinue e => .cfBreakContinue (lowerClosureCalls lamNames e)
  | .typeAscription e ty => .typeAscription (lowerClosureCalls lamNames e) ty
where
  /-- Untyped twin of `tLowerClosureCalls.lowerCallArgs`. The erased AST has no
      `.ann` nodes (erasure deletes them), so there is no `.ann` case here. -/
  lowerCallArgs (lamNames : List String) : ImpExpr → List ImpExpr
    | .tuple elems => mapE lamNames elems
    | other => [lowerClosureCalls lamNames other]
  mapE (lamNames : List String) : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => lowerClosureCalls lamNames e :: mapE lamNames es
  mapA (lamNames : List String) : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, lowerClosureCalls lamNames e) :: mapA lamNames rest

/-! ### Erase commutation for the helpers -/

@[simp] theorem tStripRefs_erase (e : TExpr) :
    (tStripRefs e).erase = stripRefs e.erase := by
  induction e using TExpr.ind with
  | borrow _ _ ih => simp only [tStripRefs, TExpr.erase]; exact ih
  | deref _ _ ih => simp only [tStripRefs, TExpr.erase]; exact ih
  | ann _ _ ih => simp only [tStripRefs, TExpr.erase]; exact ih
  | _ => rfl

@[simp] theorem tVarName?_erase (e : TExpr) :
    tVarName? e = varName? e.erase := by
  induction e using TExpr.ind with
  | borrow _ _ ih =>
      simp only [tVarName?, varName?, tStripRefs, stripRefs, TExpr.erase] at ih ⊢; exact ih
  | deref _ _ ih =>
      simp only [tVarName?, varName?, tStripRefs, stripRefs, TExpr.erase] at ih ⊢; exact ih
  | ann _ _ ih =>
      simp only [tVarName?, varName?, tStripRefs, stripRefs, TExpr.erase] at ih ⊢; exact ih
  | _ => rfl

@[simp] theorem tIsClosureBinding_erase (e : TExpr) :
    tIsClosureBinding e = isClosureBinding e.erase := by
  induction e using TExpr.ind with
  | ann _ _ ih => simpa only [tIsClosureBinding, TExpr.erase, isClosureBinding] using ih
  | _ => rfl

/-- For a non-`.tuple` head, `lowerClosureCalls.lowerCallArgs` wraps a single
    (lowered) argument — the `.tuple` arm only fires on a genuine `.tuple`. -/
theorem lowerCallArgs_not_tuple (lamNames : List String) (e : ImpExpr)
    (h : ∀ elems, e ≠ .tuple elems) :
    lowerClosureCalls.lowerCallArgs lamNames e = [lowerClosureCalls lamNames e] := by
  cases e <;> simp_all [lowerClosureCalls.lowerCallArgs]

/-- An `.app` that is not a `Fn::call` of arity ≥ 2 is traversed by the general
    arm of `lowerClosureCalls`. -/
theorem lowerClosureCalls_app_general (lamNames : List String) (g : String)
    (args : List ImpExpr)
    (h : ∀ recv argsTup rest, g = "call" → args ≠ recv :: argsTup :: rest) :
    lowerClosureCalls lamNames (.app g args)
      = .app g (lowerClosureCalls.mapE lamNames args) := by
  simp only [lowerClosureCalls] <;> split <;> simp_all

/-! ### Main erase commutation -/

/-- Commuting diagram: type erasure commutes with `tLowerClosureCalls`. -/
theorem tLowerClosureCalls_erase (lamNames : List String) (e : TExpr) :
    (tLowerClosureCalls lamNames e).erase = lowerClosureCalls lamNames e.erase := by
  apply tLowerClosureCalls.induct
    (motive1 := fun L t => (tLowerClosureCalls.lowerCallArgs L t).map TExpr.erase
                            = lowerClosureCalls.lowerCallArgs L t.erase)
    (motive2 := fun L e => (tLowerClosureCalls L e).erase = lowerClosureCalls L e.erase)
    (motive3 := fun L arms => (tLowerClosureCalls.mapA L arms).map (fun pe => (pe.1, pe.2.erase))
                               = lowerClosureCalls.mapA L (arms.map (fun pe => (pe.1, pe.2.erase))))
    (motive4 := fun L es => (tLowerClosureCalls.mapE L es).map TExpr.erase
                             = lowerClosureCalls.mapE L (es.map TExpr.erase))
  all_goals intros
  all_goals
    try simp_all [tLowerClosureCalls, lowerClosureCalls, TExpr.erase,
      tLowerClosureCalls.lowerCallArgs, tLowerClosureCalls.mapE, tLowerClosureCalls.mapA,
      lowerClosureCalls.lowerCallArgs, lowerClosureCalls.mapE, lowerClosureCalls.mapA,
      TExpr.eraseList_eq, TExpr.eraseArms_eq]
  -- Remaining: case3 (lowerCallArgs non-tuple), case5 (Fn::call else-branch),
  -- case11 (general `.app`).
  · -- case3
    rename_i L other hnt hna ih
    rw [lowerCallArgs_not_tuple L other.erase (by
      obtain ⟨k, ty⟩ := other
      intro elems
      cases k
      case tuple es => exact absurd rfl (hnt es ty)
      case ann ee => exact absurd rfl (hna ee ty)
      case break_ opt => cases opt <;> simp [TExpr.erase]
      all_goals simp [TExpr.erase])]
  · -- case5
    rename_i L recv argsTup rest ty name _hvar hcond ih
    have hneg : ¬(rest = [] ∧ name ∈ L) := fun h => hcond h.1 h.2
    rw [if_neg hneg, if_neg hneg]
    obtain ⟨ihr, iha, ihm⟩ := ih
    simp [TExpr.erase, TExpr.eraseList_eq, ihr, iha, ihm]
  · -- case11
    rename_i L g args ty hnc ih
    rw [lowerClosureCalls_app_general L g (args.map TExpr.erase) (by
      intro recv argsTup rest hg hcons
      rcases args with _ | ⟨a, _ | ⟨b, rest'⟩⟩
      · simp at hcons
      · simp at hcons
      · exact hnc a b rest' hg rfl)]

end Hax

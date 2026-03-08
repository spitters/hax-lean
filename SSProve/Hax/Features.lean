/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.AST

/-!
# Feature Predicates

Inductive predicates on `ImpExpr` that characterize which imperative
features have been eliminated. Each verified compiler phase establishes
one predicate as a post-condition and may require others as pre-conditions.

Follows the `IsDeterministic` pattern from `Deep/Deterministic.lean`.
-/

namespace SSProve.Hax

/-! ## NoReferences -/

/-- An expression contains no `borrow` or `deref` nodes. -/
inductive NoReferences : ImpExpr → Prop where
  | lit {v} : NoReferences (.lit v)
  | var {n} : NoReferences (.var n)
  | letBind {n val body} : NoReferences val → NoReferences body →
      NoReferences (.letBind n val body)
  | app {f args} : (∀ a, a ∈ args → NoReferences a) →
      NoReferences (.app f args)
  | tuple {elems} : (∀ a, a ∈ elems → NoReferences a) →
      NoReferences (.tuple elems)
  | proj {e i} : NoReferences e → NoReferences (.proj e i)
  | ifThenElse {c t e} : NoReferences c → NoReferences t → NoReferences e →
      NoReferences (.ifThenElse c t e)
  | match_ {scrut arms} : NoReferences scrut →
      (∀ pa, pa ∈ arms → NoReferences pa.2) →
      NoReferences (.match_ scrut arms)
  | unitVal : NoReferences .unitVal
  | seq {e1 e2} : NoReferences e1 → NoReferences e2 →
      NoReferences (.seq e1 e2)
  | assign {n rhs} : NoReferences rhs →
      NoReferences (.assign n rhs)
  | forLoop {v lo hi body} : NoReferences lo → NoReferences hi → NoReferences body →
      NoReferences (.forLoop v lo hi body)
  | whileLoop {c body} : NoReferences c → NoReferences body →
      NoReferences (.whileLoop c body)
  | break_none : NoReferences (.break_ none)
  | break_some {e} : NoReferences e → NoReferences (.break_ (some e))
  | continue_ : NoReferences .continue_
  | earlyReturn {e} : NoReferences e →
      NoReferences (.earlyReturn e)
  | questionMark {e} : NoReferences e →
      NoReferences (.questionMark e)
  | forFold {v lo hi body} : NoReferences lo → NoReferences hi → NoReferences body →
      NoReferences (.forFold v lo hi body)
  | whileFold {c body} : NoReferences c → NoReferences body →
      NoReferences (.whileFold c body)
  | forFoldReturn {v lo hi body} : NoReferences lo → NoReferences hi → NoReferences body →
      NoReferences (.forFoldReturn v lo hi body)
  | whileFoldReturn {c body} : NoReferences c → NoReferences body →
      NoReferences (.whileFoldReturn c body)
  | cfBreak {e} : NoReferences e → NoReferences (.cfBreak e)
  | cfContinue {e} : NoReferences e → NoReferences (.cfContinue e)
  | cfBreakContinue {e} : NoReferences e → NoReferences (.cfBreakContinue e)

theorem NoReferences.not_borrow {e : ImpExpr} : ¬NoReferences (.borrow e) := by
  intro h; cases h
theorem NoReferences.not_deref {e : ImpExpr} : ¬NoReferences (.deref e) := by
  intro h; cases h

/-! ## NoMutation -/

/-- An expression contains no `assign` nodes. -/
inductive NoMutation : ImpExpr → Prop where
  | lit {v} : NoMutation (.lit v)
  | var {n} : NoMutation (.var n)
  | letBind {n val body} : NoMutation val → NoMutation body →
      NoMutation (.letBind n val body)
  | app {f args} : (∀ a, a ∈ args → NoMutation a) →
      NoMutation (.app f args)
  | tuple {elems} : (∀ a, a ∈ elems → NoMutation a) →
      NoMutation (.tuple elems)
  | proj {e i} : NoMutation e → NoMutation (.proj e i)
  | ifThenElse {c t e} : NoMutation c → NoMutation t → NoMutation e →
      NoMutation (.ifThenElse c t e)
  | match_ {scrut arms} : NoMutation scrut →
      (∀ pa, pa ∈ arms → NoMutation pa.2) →
      NoMutation (.match_ scrut arms)
  | unitVal : NoMutation .unitVal
  | seq {e1 e2} : NoMutation e1 → NoMutation e2 →
      NoMutation (.seq e1 e2)
  | borrow {e} : NoMutation e → NoMutation (.borrow e)
  | deref {e} : NoMutation e → NoMutation (.deref e)
  | forLoop {v lo hi body} : NoMutation lo → NoMutation hi → NoMutation body →
      NoMutation (.forLoop v lo hi body)
  | whileLoop {c body} : NoMutation c → NoMutation body →
      NoMutation (.whileLoop c body)
  | break_none : NoMutation (.break_ none)
  | break_some {e} : NoMutation e → NoMutation (.break_ (some e))
  | continue_ : NoMutation .continue_
  | earlyReturn {e} : NoMutation e →
      NoMutation (.earlyReturn e)
  | questionMark {e} : NoMutation e →
      NoMutation (.questionMark e)
  | forFold {v lo hi body} : NoMutation lo → NoMutation hi → NoMutation body →
      NoMutation (.forFold v lo hi body)
  | whileFold {c body} : NoMutation c → NoMutation body →
      NoMutation (.whileFold c body)
  | forFoldReturn {v lo hi body} : NoMutation lo → NoMutation hi → NoMutation body →
      NoMutation (.forFoldReturn v lo hi body)
  | whileFoldReturn {c body} : NoMutation c → NoMutation body →
      NoMutation (.whileFoldReturn c body)
  | cfBreak {e} : NoMutation e → NoMutation (.cfBreak e)
  | cfContinue {e} : NoMutation e → NoMutation (.cfContinue e)
  | cfBreakContinue {e} : NoMutation e → NoMutation (.cfBreakContinue e)

theorem NoMutation.not_assign {n : String} {rhs : ImpExpr} :
    ¬NoMutation (.assign n rhs) := by intro h; cases h

/-! ## NoLoops -/

/-- An expression contains no `forLoop`, `whileLoop`, `break_`, or `continue_`. -/
inductive NoLoops : ImpExpr → Prop where
  | lit {v} : NoLoops (.lit v)
  | var {n} : NoLoops (.var n)
  | letBind {n val body} : NoLoops val → NoLoops body →
      NoLoops (.letBind n val body)
  | app {f args} : (∀ a, a ∈ args → NoLoops a) →
      NoLoops (.app f args)
  | tuple {elems} : (∀ a, a ∈ elems → NoLoops a) →
      NoLoops (.tuple elems)
  | proj {e i} : NoLoops e → NoLoops (.proj e i)
  | ifThenElse {c t e} : NoLoops c → NoLoops t → NoLoops e →
      NoLoops (.ifThenElse c t e)
  | match_ {scrut arms} : NoLoops scrut →
      (∀ pa, pa ∈ arms → NoLoops pa.2) →
      NoLoops (.match_ scrut arms)
  | unitVal : NoLoops .unitVal
  | seq {e1 e2} : NoLoops e1 → NoLoops e2 →
      NoLoops (.seq e1 e2)
  | borrow {e} : NoLoops e → NoLoops (.borrow e)
  | deref {e} : NoLoops e → NoLoops (.deref e)
  | assign {n rhs} : NoLoops rhs → NoLoops (.assign n rhs)
  | earlyReturn {e} : NoLoops e → NoLoops (.earlyReturn e)
  | questionMark {e} : NoLoops e → NoLoops (.questionMark e)
  | forFold {v lo hi body} : NoLoops lo → NoLoops hi → NoLoops body →
      NoLoops (.forFold v lo hi body)
  | whileFold {c body} : NoLoops c → NoLoops body →
      NoLoops (.whileFold c body)
  | forFoldReturn {v lo hi body} : NoLoops lo → NoLoops hi → NoLoops body →
      NoLoops (.forFoldReturn v lo hi body)
  | whileFoldReturn {c body} : NoLoops c → NoLoops body →
      NoLoops (.whileFoldReturn c body)
  | cfBreak {e} : NoLoops e → NoLoops (.cfBreak e)
  | cfContinue {e} : NoLoops e → NoLoops (.cfContinue e)
  | cfBreakContinue {e} : NoLoops e → NoLoops (.cfBreakContinue e)

theorem NoLoops.not_forLoop {v : String} {lo hi body : ImpExpr} :
    ¬NoLoops (.forLoop v lo hi body) := by intro h; cases h
theorem NoLoops.not_whileLoop {c body : ImpExpr} :
    ¬NoLoops (.whileLoop c body) := by intro h; cases h
theorem NoLoops.not_break {oe : Option ImpExpr} :
    ¬NoLoops (.break_ oe) := by intro h; cases h
theorem NoLoops.not_continue :
    ¬NoLoops (.continue_) := by intro h; cases h

/-! ## NoEarlyExit -/

/-- An expression contains no `earlyReturn` or `questionMark`. -/
inductive NoEarlyExit : ImpExpr → Prop where
  | lit {v} : NoEarlyExit (.lit v)
  | var {n} : NoEarlyExit (.var n)
  | letBind {n val body} : NoEarlyExit val → NoEarlyExit body →
      NoEarlyExit (.letBind n val body)
  | app {f args} : (∀ a, a ∈ args → NoEarlyExit a) →
      NoEarlyExit (.app f args)
  | tuple {elems} : (∀ a, a ∈ elems → NoEarlyExit a) →
      NoEarlyExit (.tuple elems)
  | proj {e i} : NoEarlyExit e → NoEarlyExit (.proj e i)
  | ifThenElse {c t e} : NoEarlyExit c → NoEarlyExit t → NoEarlyExit e →
      NoEarlyExit (.ifThenElse c t e)
  | match_ {scrut arms} : NoEarlyExit scrut →
      (∀ pa, pa ∈ arms → NoEarlyExit pa.2) →
      NoEarlyExit (.match_ scrut arms)
  | unitVal : NoEarlyExit .unitVal
  | seq {e1 e2} : NoEarlyExit e1 → NoEarlyExit e2 →
      NoEarlyExit (.seq e1 e2)
  | borrow {e} : NoEarlyExit e → NoEarlyExit (.borrow e)
  | deref {e} : NoEarlyExit e → NoEarlyExit (.deref e)
  | assign {n rhs} : NoEarlyExit rhs → NoEarlyExit (.assign n rhs)
  | forLoop {v lo hi body} : NoEarlyExit lo → NoEarlyExit hi → NoEarlyExit body →
      NoEarlyExit (.forLoop v lo hi body)
  | whileLoop {c body} : NoEarlyExit c → NoEarlyExit body →
      NoEarlyExit (.whileLoop c body)
  | break_none : NoEarlyExit (.break_ none)
  | break_some {e} : NoEarlyExit e → NoEarlyExit (.break_ (some e))
  | continue_ : NoEarlyExit .continue_
  | forFold {v lo hi body} : NoEarlyExit lo → NoEarlyExit hi → NoEarlyExit body →
      NoEarlyExit (.forFold v lo hi body)
  | whileFold {c body} : NoEarlyExit c → NoEarlyExit body →
      NoEarlyExit (.whileFold c body)
  | forFoldReturn {v lo hi body} : NoEarlyExit lo → NoEarlyExit hi → NoEarlyExit body →
      NoEarlyExit (.forFoldReturn v lo hi body)
  | whileFoldReturn {c body} : NoEarlyExit c → NoEarlyExit body →
      NoEarlyExit (.whileFoldReturn c body)
  | cfBreak {e} : NoEarlyExit e → NoEarlyExit (.cfBreak e)
  | cfContinue {e} : NoEarlyExit e → NoEarlyExit (.cfContinue e)
  | cfBreakContinue {e} : NoEarlyExit e → NoEarlyExit (.cfBreakContinue e)

theorem NoEarlyExit.not_earlyReturn {e : ImpExpr} :
    ¬NoEarlyExit (.earlyReturn e) := by intro h; cases h
theorem NoEarlyExit.not_questionMark {e : ImpExpr} :
    ¬NoEarlyExit (.questionMark e) := by intro h; cases h

/-! ## Decidable Boolean Checkers -/

/-- Check that an expression has no `borrow`/`deref` nodes. -/
def checkNoReferences : ImpExpr → Bool
  | .borrow _ | .deref _ => false
  | .lit _ | .var _ | .unitVal | .continue_ => true
  | .letBind _ v b => checkNoReferences v && checkNoReferences b
  | .app _ args => checkNoReferencesList args
  | .tuple elems => checkNoReferencesList elems
  | .proj e _ => checkNoReferences e
  | .ifThenElse c t e => checkNoReferences c && checkNoReferences t && checkNoReferences e
  | .match_ s arms => checkNoReferences s && checkNoReferencesArms arms
  | .seq e1 e2 => checkNoReferences e1 && checkNoReferences e2
  | .assign _ rhs => checkNoReferences rhs
  | .forLoop _ lo hi body =>
    checkNoReferences lo && checkNoReferences hi && checkNoReferences body
  | .whileLoop c body => checkNoReferences c && checkNoReferences body
  | .break_ none => true
  | .break_ (some e) => checkNoReferences e
  | .earlyReturn e => checkNoReferences e
  | .questionMark e => checkNoReferences e
  | .forFold _ lo hi body =>
    checkNoReferences lo && checkNoReferences hi && checkNoReferences body
  | .whileFold c body => checkNoReferences c && checkNoReferences body
  | .forFoldReturn _ lo hi body =>
    checkNoReferences lo && checkNoReferences hi && checkNoReferences body
  | .whileFoldReturn c body => checkNoReferences c && checkNoReferences body
  | .cfBreak e => checkNoReferences e
  | .cfContinue e => checkNoReferences e
  | .cfBreakContinue e => checkNoReferences e
where
  checkNoReferencesList : List ImpExpr → Bool
    | [] => true
    | e :: es => checkNoReferences e && checkNoReferencesList es
  checkNoReferencesArms : List (ImpPat × ImpExpr) → Bool
    | [] => true
    | (_, e) :: rest => checkNoReferences e && checkNoReferencesArms rest

/-- Check that an expression has no `assign` nodes. -/
def checkNoMutation : ImpExpr → Bool
  | .assign _ _ => false
  | .lit _ | .var _ | .unitVal | .continue_ => true
  | .letBind _ v b => checkNoMutation v && checkNoMutation b
  | .app _ args => checkNoMutationList args
  | .tuple elems => checkNoMutationList elems
  | .proj e _ => checkNoMutation e
  | .ifThenElse c t e => checkNoMutation c && checkNoMutation t && checkNoMutation e
  | .match_ s arms => checkNoMutation s && checkNoMutationArms arms
  | .seq e1 e2 => checkNoMutation e1 && checkNoMutation e2
  | .borrow e => checkNoMutation e
  | .deref e => checkNoMutation e
  | .forLoop _ lo hi body =>
    checkNoMutation lo && checkNoMutation hi && checkNoMutation body
  | .whileLoop c body => checkNoMutation c && checkNoMutation body
  | .break_ none => true
  | .break_ (some e) => checkNoMutation e
  | .earlyReturn e => checkNoMutation e
  | .questionMark e => checkNoMutation e
  | .forFold _ lo hi body =>
    checkNoMutation lo && checkNoMutation hi && checkNoMutation body
  | .whileFold c body => checkNoMutation c && checkNoMutation body
  | .forFoldReturn _ lo hi body =>
    checkNoMutation lo && checkNoMutation hi && checkNoMutation body
  | .whileFoldReturn c body => checkNoMutation c && checkNoMutation body
  | .cfBreak e => checkNoMutation e
  | .cfContinue e => checkNoMutation e
  | .cfBreakContinue e => checkNoMutation e
where
  checkNoMutationList : List ImpExpr → Bool
    | [] => true
    | e :: es => checkNoMutation e && checkNoMutationList es
  checkNoMutationArms : List (ImpPat × ImpExpr) → Bool
    | [] => true
    | (_, e) :: rest => checkNoMutation e && checkNoMutationArms rest

/-- Check that an expression has no loop nodes. -/
def checkNoLoops : ImpExpr → Bool
  | .forLoop _ _ _ _ | .whileLoop _ _ | .break_ _ | .continue_ => false
  | .lit _ | .var _ | .unitVal => true
  | .letBind _ v b => checkNoLoops v && checkNoLoops b
  | .app _ args => checkNoLoopsList args
  | .tuple elems => checkNoLoopsList elems
  | .proj e _ => checkNoLoops e
  | .ifThenElse c t e => checkNoLoops c && checkNoLoops t && checkNoLoops e
  | .match_ s arms => checkNoLoops s && checkNoLoopsArms arms
  | .seq e1 e2 => checkNoLoops e1 && checkNoLoops e2
  | .borrow e => checkNoLoops e
  | .deref e => checkNoLoops e
  | .assign _ rhs => checkNoLoops rhs
  | .earlyReturn e => checkNoLoops e
  | .questionMark e => checkNoLoops e
  | .forFold _ lo hi body =>
    checkNoLoops lo && checkNoLoops hi && checkNoLoops body
  | .whileFold c body => checkNoLoops c && checkNoLoops body
  | .forFoldReturn _ lo hi body =>
    checkNoLoops lo && checkNoLoops hi && checkNoLoops body
  | .whileFoldReturn c body => checkNoLoops c && checkNoLoops body
  | .cfBreak e => checkNoLoops e
  | .cfContinue e => checkNoLoops e
  | .cfBreakContinue e => checkNoLoops e
where
  checkNoLoopsList : List ImpExpr → Bool
    | [] => true
    | e :: es => checkNoLoops e && checkNoLoopsList es
  checkNoLoopsArms : List (ImpPat × ImpExpr) → Bool
    | [] => true
    | (_, e) :: rest => checkNoLoops e && checkNoLoopsArms rest

/-- Check that an expression has no early exit nodes. -/
def checkNoEarlyExit : ImpExpr → Bool
  | .earlyReturn _ | .questionMark _ => false
  | .lit _ | .var _ | .unitVal | .continue_ => true
  | .letBind _ v b => checkNoEarlyExit v && checkNoEarlyExit b
  | .app _ args => checkNoEarlyExitList args
  | .tuple elems => checkNoEarlyExitList elems
  | .proj e _ => checkNoEarlyExit e
  | .ifThenElse c t e => checkNoEarlyExit c && checkNoEarlyExit t && checkNoEarlyExit e
  | .match_ s arms => checkNoEarlyExit s && checkNoEarlyExitArms arms
  | .seq e1 e2 => checkNoEarlyExit e1 && checkNoEarlyExit e2
  | .borrow e => checkNoEarlyExit e
  | .deref e => checkNoEarlyExit e
  | .assign _ rhs => checkNoEarlyExit rhs
  | .forLoop _ lo hi body =>
    checkNoEarlyExit lo && checkNoEarlyExit hi && checkNoEarlyExit body
  | .whileLoop c body => checkNoEarlyExit c && checkNoEarlyExit body
  | .break_ none => true
  | .break_ (some e) => checkNoEarlyExit e
  | .forFold _ lo hi body =>
    checkNoEarlyExit lo && checkNoEarlyExit hi && checkNoEarlyExit body
  | .whileFold c body => checkNoEarlyExit c && checkNoEarlyExit body
  | .forFoldReturn _ lo hi body =>
    checkNoEarlyExit lo && checkNoEarlyExit hi && checkNoEarlyExit body
  | .whileFoldReturn c body => checkNoEarlyExit c && checkNoEarlyExit body
  | .cfBreak e => checkNoEarlyExit e
  | .cfContinue e => checkNoEarlyExit e
  | .cfBreakContinue e => checkNoEarlyExit e
where
  checkNoEarlyExitList : List ImpExpr → Bool
    | [] => true
    | e :: es => checkNoEarlyExit e && checkNoEarlyExitList es
  checkNoEarlyExitArms : List (ImpPat × ImpExpr) → Bool
    | [] => true
    | (_, e) :: rest => checkNoEarlyExit e && checkNoEarlyExitArms rest

/-- Check all four feature predicates at once. -/
def checkFullyFunctional (e : ImpExpr) : Bool :=
  checkNoReferences e && checkNoMutation e && checkNoLoops e && checkNoEarlyExit e

/-! ## Soundness -/

/-- `checkNoEarlyExit` is sound: `true` implies `NoEarlyExit`. -/
theorem checkNoEarlyExit_sound :
    ∀ e : ImpExpr, checkNoEarlyExit e = true → NoEarlyExit e := by
  intro e
  induction e using ImpExpr.ind with
  | lit | var | unitVal | continue_ => intro; constructor
  | earlyReturn => intro h; simp [checkNoEarlyExit] at h
  | questionMark => intro h; simp [checkNoEarlyExit] at h
  | break_none => intro; exact .break_none
  | break_some _ ih =>
    intro h; simp [checkNoEarlyExit] at h; exact .break_some (ih h)
  | letBind _ _ _ ih1 ih2 =>
    intro h; simp [checkNoEarlyExit] at h
    exact .letBind (ih1 h.1) (ih2 h.2)
  | seq _ _ ih1 ih2 =>
    intro h; simp [checkNoEarlyExit] at h
    exact .seq (ih1 h.1) (ih2 h.2)
  | proj _ _ ih =>
    intro h; simp [checkNoEarlyExit] at h; exact .proj (ih h)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    intro h; simp [checkNoEarlyExit] at h
    exact .ifThenElse (ih1 h.1.1) (ih2 h.1.2) (ih3 h.2)
  | borrow _ ih =>
    intro h; simp [checkNoEarlyExit] at h; exact .borrow (ih h)
  | deref _ ih =>
    intro h; simp [checkNoEarlyExit] at h; exact .deref (ih h)
  | assign _ _ ih =>
    intro h; simp [checkNoEarlyExit] at h; exact .assign (ih h)
  | forLoop _ _ _ _ ih1 ih2 ih3 =>
    intro h; simp [checkNoEarlyExit] at h
    exact .forLoop (ih1 h.1.1) (ih2 h.1.2) (ih3 h.2)
  | whileLoop _ _ ih1 ih2 =>
    intro h; simp [checkNoEarlyExit] at h
    exact .whileLoop (ih1 h.1) (ih2 h.2)
  | app _ args ih =>
    intro h; simp [checkNoEarlyExit] at h
    exact .app (fun a ha => by
      have := checkNoEarlyExit_sound_list args h a ha
      exact ih a ha this)
  | tuple elems ih =>
    intro h; simp [checkNoEarlyExit] at h
    exact .tuple (fun a ha => by
      have := checkNoEarlyExit_sound_list elems h a ha
      exact ih a ha this)
  | match_ _ arms ih_scrut ih_arms =>
    intro h; simp [checkNoEarlyExit] at h
    exact .match_ (ih_scrut h.1) (fun pa hpa => by
      have := checkNoEarlyExit_sound_arms arms h.2 pa hpa
      exact ih_arms pa hpa this)
  | forFold _ _ _ _ ih1 ih2 ih3 =>
    intro h; simp [checkNoEarlyExit] at h
    exact .forFold (ih1 h.1.1) (ih2 h.1.2) (ih3 h.2)
  | whileFold _ _ ih1 ih2 =>
    intro h; simp [checkNoEarlyExit] at h
    exact .whileFold (ih1 h.1) (ih2 h.2)
  | forFoldReturn _ _ _ _ ih1 ih2 ih3 =>
    intro h; simp [checkNoEarlyExit] at h
    exact .forFoldReturn (ih1 h.1.1) (ih2 h.1.2) (ih3 h.2)
  | whileFoldReturn _ _ ih1 ih2 =>
    intro h; simp [checkNoEarlyExit] at h
    exact .whileFoldReturn (ih1 h.1) (ih2 h.2)
  | cfBreak _ ih =>
    intro h; simp [checkNoEarlyExit] at h; exact .cfBreak (ih h)
  | cfContinue _ ih =>
    intro h; simp [checkNoEarlyExit] at h; exact .cfContinue (ih h)
  | cfBreakContinue _ ih =>
    intro h; simp [checkNoEarlyExit] at h; exact .cfBreakContinue (ih h)
where
  checkNoEarlyExit_sound_list : ∀ (es : List ImpExpr),
      checkNoEarlyExit.checkNoEarlyExitList es = true →
      ∀ a, a ∈ es → checkNoEarlyExit a = true := by
    intro es; induction es with
    | nil => intro _ a ha; cases ha
    | cons e es ih =>
      intro h a ha
      simp [checkNoEarlyExit.checkNoEarlyExitList] at h
      cases ha with
      | head => exact h.1
      | tail _ ha => exact ih h.2 a ha
  checkNoEarlyExit_sound_arms : ∀ (arms : List (ImpPat × ImpExpr)),
      checkNoEarlyExit.checkNoEarlyExitArms arms = true →
      ∀ pa, pa ∈ arms → checkNoEarlyExit pa.2 = true := by
    intro arms; induction arms with
    | nil => intro _ pa hpa; cases hpa
    | cons pa arms ih =>
      intro h pa' hpa'
      simp [checkNoEarlyExit.checkNoEarlyExitArms] at h
      cases hpa' with
      | head => exact h.1
      | tail _ hpa' => exact ih h.2 pa' hpa'

/-! ## Fully Functional -/

/-- An expression is fully functional: all imperative features eliminated. -/
def FullyFunctional (e : ImpExpr) : Prop :=
  NoReferences e ∧ NoMutation e ∧ NoLoops e ∧ NoEarlyExit e

end SSProve.Hax

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

theorem NoEarlyExit.not_earlyReturn {e : ImpExpr} :
    ¬NoEarlyExit (.earlyReturn e) := by intro h; cases h
theorem NoEarlyExit.not_questionMark {e : ImpExpr} :
    ¬NoEarlyExit (.questionMark e) := by intro h; cases h

/-! ## Fully Functional -/

/-- An expression is fully functional: all imperative features eliminated. -/
def FullyFunctional (e : ImpExpr) : Prop :=
  NoReferences e ∧ NoMutation e ∧ NoLoops e ∧ NoEarlyExit e

end SSProve.Hax

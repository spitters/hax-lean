/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr
import Hax.Features

/-!
# Typed Feature Predicates

Feature predicates on `TExpr`, defined via erasure to reuse all
existing proofs on `ImpExpr` without any new proof obligations.
-/

namespace Hax

/-- A typed expression has no references iff its erasure does. -/
def TNoReferences (e : TExpr) : Prop := NoReferences e.erase

/-- A typed expression has no mutation iff its erasure does. -/
def TNoMutation (e : TExpr) : Prop := NoMutation e.erase

/-- A typed expression has no loops iff its erasure does. -/
def TNoLoops (e : TExpr) : Prop := NoLoops e.erase

/-- A typed expression has no early exits iff its erasure does. -/
def TNoEarlyExit (e : TExpr) : Prop := NoEarlyExit e.erase

/-- A typed expression is fully functional iff its erasure is. -/
def TFullyFunctional (e : TExpr) : Prop := FullyFunctional e.erase

theorem TFullyFunctional_iff (e : TExpr) :
    TFullyFunctional e ↔ TNoReferences e ∧ TNoMutation e ∧ TNoLoops e ∧ TNoEarlyExit e :=
  Iff.rfl

end Hax

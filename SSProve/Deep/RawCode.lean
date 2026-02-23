/-
Copyright (c) 2024 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/

/-!
# RawCode Stub

Minimal stub of SSProve's `RawCode` free monad, providing only the
constructors used by `ToRawCode.lean`: `ret`, `bind`, and `fail`.

The full `RawCode` (with `sample`, `get`, `put`, `oracleCall`) lives in
the SSProve repository under `SSProve/Deep/RawCode.lean`.
-/

namespace SSProve.Deep

universe u

/-- Minimal free monad for computations, providing ret/bind/fail. -/
inductive RawCode : Type u → Type (u+1) where
  | ret {α : Type u} (a : α) : RawCode α
  | bind {α β : Type u} (c : RawCode α) (k : α → RawCode β) : RawCode β
  | fail {α : Type u} : RawCode α

namespace RawCode

/-- A predicate asserting that a `RawCode` tree contains no oracle calls.
    In this stub all constructors trivially satisfy it. -/
inductive NoOracleCall : {α : Type u} → RawCode α → Prop where
  | ret {α : Type u} (a : α) : NoOracleCall (.ret a)
  | bind {α β : Type u} {c : RawCode β} {k : β → RawCode α}
      (hc : NoOracleCall c) (hk : ∀ b, NoOracleCall (k b)) : NoOracleCall (.bind c k)
  | fail {α : Type u} : NoOracleCall (@RawCode.fail α)

end RawCode

end SSProve.Deep

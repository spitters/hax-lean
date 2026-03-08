/-
Copyright (c) 2024 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/

/-!
# RawCode Deep Embedding (Stub)

Minimal free monad for deterministic computations, used as the target of
the hax `toRawCode` translation.

## Relation to SSProve-lean

The full `RawCode` lives in `SSProve-lean/SSProve/Deep/RawCode.lean` with
constructors for `sample`, `get`, `put`, `oracleCall`, and `fail`, plus
proper `Location` and `Fintype` infrastructure.

This stub provides only the three constructors that `toRawCode` actually
produces: `ret`, `bind`, and `fail`. When connecting to the real SSProve
library, this file should be replaced by an import of
`SSProve.Deep.RawCode` from SSProve-lean, and predicates like
`NoOracleCall` / `IsDeterministic` proved against the real type.
-/

namespace SSProve.Deep

universe u

/-- Minimal free monad for deterministic computations.

    Constructors:
    - `ret` — return a pure value
    - `bind` — sequential composition
    - `fail` — computation failure (e.g., pattern match failure) -/
inductive RawCode : Type u → Type (u+1) where
  | ret {α : Type u} (a : α) : RawCode α
  | bind {α β : Type u} (c : RawCode α) (k : α → RawCode β) : RawCode β
  | fail {α : Type u} : RawCode α

namespace RawCode

/-- Interpret a `RawCode` as an `Option`. -/
noncomputable def eval : {α : Type u} → RawCode α → Option α
  | _, .ret a => some a
  | _, .bind c k => do let a ← eval c; eval (k a)
  | _, .fail => none

end RawCode

end SSProve.Deep

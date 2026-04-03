/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-!
# RawCode Deep Embedding (Stub)

Minimal free monad for deterministic computations, used as the target of
the hax `toRawCode` translation.

## Relation to CatCrypt

The full `RawCode` lives in `CatCrypt/SSProve/Deep/RawCode.lean` with
constructors for `sample`, `get`, `put`, `oracleCall`, and `fail`, plus
proper `Location` and `Fintype` infrastructure.

This stub provides only the three constructors that `toRawCode` actually
produces: `ret`, `bind`, and `fail`. When connecting to the real CatCrypt
library, this file should be replaced by an import of
`Hax.Deep.RawCode` from CatCrypt, and predicates like
`NoOracleCall` / `IsDeterministic` proved against the real type.
-/

namespace Hax.Deep

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

end Hax.Deep

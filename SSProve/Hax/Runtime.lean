/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/

/-!
# Runtime Library for Generated Lean 4 Code

Defines `ControlFlow`, `Hax.forFold`, `Hax.whileFold`, and their
`Return` variants used by the pretty-printer output.

Generated Lean 4 code from `haxpipe --emit-lean` imports this module.

## Design

The `ControlFlow` type mirrors Rust's `core::ops::ControlFlow<B, C>`.
Fold operations thread an accumulator through a closure that returns
`ControlFlow`: `Continue acc'` continues iteration with the new accumulator,
`Break v` exits the loop with value `v`.

### Correspondence with the AST

| AST constructor        | Runtime function       |
|------------------------|------------------------|
| `forFold v lo hi body` | `Hax.forFold`          |
| `whileFold c body`     | `Hax.whileFold`        |
| `forFoldReturn`        | `Hax.forFoldReturn`    |
| `whileFoldReturn`      | `Hax.whileFoldReturn`  |
| `cfBreak e`            | `ControlFlow.Break`    |
| `cfContinue e`         | `ControlFlow.Continue` |
| `cfBreakContinue e`    | `ControlFlow.Break (ControlFlow.Continue e)` |
-/

/-- Rust's `ControlFlow<B, C>`: either stop with `Break b` or continue
    with `Continue c`. -/
inductive ControlFlow (B C : Type) where
  | Break (b : B)
  | Continue (c : C)
  deriving BEq, Repr

/-- `ControlFlow` is inhabited whenever the continue type is.
    (Uses `Continue default` rather than requiring `Inhabited B`.) -/
instance {B C : Type} [Inhabited C] : Inhabited (ControlFlow B C) :=
  ⟨.Continue default⟩

namespace ControlFlow

variable {B C : Type}

/-- Extract the break value if present. -/
def breakVal? : ControlFlow B C → Option B
  | .Break b => some b
  | .Continue _ => none

/-- Extract the continue value if present. -/
def continueVal? : ControlFlow B C → Option C
  | .Break _ => none
  | .Continue c => some c

/-- Is this a `Break`? -/
def isBreak : ControlFlow B C → Bool
  | .Break _ => true
  | .Continue _ => false

end ControlFlow

namespace Hax

/-- Fold over `[lo, hi)` with accumulator.
    The body returns `ControlFlow`:
    - `Continue acc'` → continue with new accumulator
    - `Break v` → exit loop with value `v` -/
partial def forFold {α β : Type} [Inhabited α]
    (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow β α) : ControlFlow β α :=
  if lo ≥ hi then .Continue init
  else
    match f lo init with
    | .Break v => .Break v
    | .Continue acc => forFold (lo + 1) hi acc f

/-- While-fold with accumulator.
    Iterates while the condition returns `true`. -/
partial def whileFold {α β : Type} [Inhabited α]
    (init : α) (cond : α → Bool) (f : α → ControlFlow β α) :
    ControlFlow β α :=
  if cond init then
    match f init with
    | .Break v => .Break v
    | .Continue acc => whileFold acc cond f
  else .Continue init

/-- For-fold with early return support (nested ControlFlow).
    The body returns `ControlFlow (ControlFlow β γ) α`:
    - `Continue acc'` → continue iteration
    - `Break (Continue v)` → loop break, return `v`
    - `Break (Break v)` → early return, propagate `Break v` -/
partial def forFoldReturn {α β γ : Type}
    [Inhabited α] [Inhabited γ]
    (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow (ControlFlow β γ) α) :
    ControlFlow β (ControlFlow γ α) :=
  if lo ≥ hi then .Continue (.Continue init)
  else
    match f lo init with
    | .Break (.Continue v) => .Continue (.Break v)  -- loop break
    | .Break (.Break v) => .Break v                  -- early return
    | .Continue acc => forFoldReturn (lo + 1) hi acc f

/-- While-fold with early return support (nested ControlFlow). -/
partial def whileFoldReturn {α β γ : Type}
    [Inhabited α] [Inhabited γ]
    (init : α) (cond : α → Bool)
    (f : α → ControlFlow (ControlFlow β γ) α) :
    ControlFlow β (ControlFlow γ α) :=
  if cond init then
    match f init with
    | .Break (.Continue v) => .Continue (.Break v)  -- loop break
    | .Break (.Break v) => .Break v                  -- early return
    | .Continue acc => whileFoldReturn acc cond f
  else .Continue (.Continue init)

/-- Extract the final value from a non-early-returning fold result. -/
def unwrapContinue {B C : Type} [Inhabited C] : ControlFlow B C → C
  | .Continue c => c
  | .Break _ => panic! "unexpected Break in unwrapContinue"

/-! ## Builtin operations for generated code

These definitions are referenced by generated Lean 4 code via `Hax.add`, `Hax.Sub`, etc.
Capitalized variants match hax's Rust operator names. -/

-- Arithmetic
@[inline] def add (a b : Int) : Int := a + b
@[inline] def sub (a b : Int) : Int := a - b
@[inline] def mul (a b : Int) : Int := a * b
@[inline] def div (a b : Int) : Int := a / b
@[inline] def rem (a b : Int) : Int := a % b
@[inline] def neg (a : Int) : Int := -a

-- Comparison
@[inline] def beq {α : Type} [BEq α] (a b : α) : Bool := a == b
@[inline] def bne {α : Type} [BEq α] (a b : α) : Bool := !(a == b)
@[inline] def lt (a b : Int) : Bool := a < b
@[inline] def le (a b : Int) : Bool := a ≤ b
@[inline] def gt (a b : Int) : Bool := a > b
@[inline] def ge (a b : Int) : Bool := a ≥ b

-- Boolean
@[inline] def bnot (b : Bool) : Bool := !b
@[inline] def band (a b : Bool) : Bool := a && b
@[inline] def bor (a b : Bool) : Bool := a || b

-- Capitalized aliases (hax's Rust operator names)
abbrev Add := @add
abbrev Sub := @sub
abbrev Mul := @mul
abbrev Div := @div
abbrev Rem := @rem
abbrev Neg := @neg
abbrev Eq := @beq
abbrev Ne := @bne
abbrev Lt := @lt
abbrev Le := @le
abbrev Gt := @gt
abbrev Ge := @ge
abbrev Not := @bnot
abbrev And := @band
abbrev Or := @bor

end Hax

/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
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

/-- Extract the value from either variant when both carry the same type. -/
def merge {α : Type} : ControlFlow α α → α
  | .Break v => v
  | .Continue v => v

end ControlFlow

namespace Hax

/-- Simple fold over `[lo, hi)` — no ControlFlow, no break/continue.
    Used for loops whose body only mutates accumulators without early exit. -/
def foldRange {α : Type} (lo hi : Int) (init : α)
    (f : Int → α → α) : α :=
  if lo ≥ hi then init
  else foldRange (lo + 1) hi (f lo init) f
termination_by (hi - lo).toNat

/-- Simple reverse fold over `(lo, hi]` — no ControlFlow. -/
def foldRangeRev {α : Type} (lo hi : Int) (init : α)
    (f : Int → α → α) : α :=
  if lo ≥ hi then init
  else foldRangeRev lo (hi - 1) (f (hi - 1) init) f
termination_by (hi - lo).toNat

/-- Fold over `[lo, hi)` with accumulator.
    The body returns `ControlFlow`:
    - `Continue acc'` → continue with new accumulator
    - `Break v` → exit loop with value `v` -/
def forFold {α β : Type}
    (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow β α) : ControlFlow β α :=
  if lo ≥ hi then .Continue init
  else
    match f lo init with
    | .Break v => .Break v
    | .Continue acc => forFold (lo + 1) hi acc f
termination_by (hi - lo).toNat

/-- Reverse fold over `(lo, hi]` (i.e., hi-1, hi-2, ..., lo) with accumulator.
    The body receives indices in descending order. -/
def forFoldRev {α β : Type}
    (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow β α) : ControlFlow β α :=
  if lo ≥ hi then .Continue init
  else
    match f (hi - 1) init with
    | .Break v => .Break v
    | .Continue acc => forFoldRev lo (hi - 1) acc f
termination_by (hi - lo).toNat

/-- While-fold with accumulator.
    Iterates while the condition returns `true`. -/
partial def whileFold {α β : Type}
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
def forFoldReturn {α β γ : Type}
    (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow (ControlFlow β γ) α) :
    ControlFlow β (ControlFlow γ α) :=
  if lo ≥ hi then .Continue (.Continue init)
  else
    match f lo init with
    | .Break (.Continue v) => .Continue (.Break v)  -- loop break
    | .Break (.Break v) => .Break v                  -- early return
    | .Continue acc => forFoldReturn (lo + 1) hi acc f
termination_by (hi - lo).toNat

/-- Reverse for-fold with early return support (nested ControlFlow). -/
def forFoldRevReturn {α β γ : Type}
    (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow (ControlFlow β γ) α) :
    ControlFlow β (ControlFlow γ α) :=
  if lo ≥ hi then .Continue (.Continue init)
  else
    match f (hi - 1) init with
    | .Break (.Continue v) => .Continue (.Break v)  -- loop break
    | .Break (.Break v) => .Break v                  -- early return
    | .Continue acc => forFoldRevReturn lo (hi - 1) acc f
termination_by (hi - lo).toNat

/-- While-fold with early return support (nested ControlFlow). -/
partial def whileFoldReturn {α β γ : Type}
    (init : α) (cond : α → Bool)
    (f : α → ControlFlow (ControlFlow β γ) α) :
    ControlFlow β (ControlFlow γ α) :=
  if cond init then
    match f init with
    | .Break (.Continue v) => .Continue (.Break v)  -- loop break
    | .Break (.Break v) => .Break v                  -- early return
    | .Continue acc => whileFoldReturn acc cond f
  else .Continue (.Continue init)

/-- Helper for code generation: wraps `ControlFlow.Break` with explicit type params. -/
@[inline] def cfBreak {B C : Type} (v : B) : ControlFlow B C := ControlFlow.Break v

/-- Helper for code generation: wraps `ControlFlow.Continue` with explicit type params. -/
@[inline] def cfContinue {B C : Type} (v : C) : ControlFlow B C := ControlFlow.Continue v

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

-- Comparison (Int-specialized to avoid typeclass issues with untyped parameters)
@[inline] def beq (a b : Int) : Bool := a == b
@[inline] def bne (a b : Int) : Bool := !(a == b)
-- Polymorphic versions for typed extraction
@[inline] def beq_ {α : Type} [BEq α] (a b : α) : Bool := a == b
@[inline] def bne_ {α : Type} [BEq α] (a b : α) : Bool := !(a == b)
@[inline] def lt (a b : Int) : Bool := a < b
@[inline] def le (a b : Int) : Bool := a ≤ b
@[inline] def gt (a b : Int) : Bool := a > b
@[inline] def ge (a b : Int) : Bool := a ≥ b

-- Boolean
@[inline] def bnot (b : Bool) : Bool := !b
@[inline] def band (a b : Bool) : Bool := a && b
@[inline] def bor (a b : Bool) : Bool := a || b

-- Bitwise (untyped, operates on magnitude — backward compat)
@[inline] def shl (a b : Int) : Int := ↑(a.toNat <<< b.toNat)
@[inline] def shr (a b : Int) : Int := ↑(a.toNat >>> b.toNat)
@[inline] def bitand (a b : Int) : Int := ↑(a.toNat &&& b.toNat)
@[inline] def bitor (a b : Int) : Int := ↑(a.toNat ||| b.toNat)
@[inline] def bitxor (a b : Int) : Int := ↑(a.toNat ^^^ b.toNat)
@[inline] def bitnot (a : Int) : Int := -(a + 1)

-- Indexing — uses sorry for empty array fallback (never reached in extracted code)
@[inline] def index {α : Type} (a : Array α) (i : Int) : α :=
  if h : i.toNat < a.size then a[i.toNat]
  else if h2 : 0 < a.size then a[0]
  else have : Inhabited α := ⟨sorry⟩; default

-- Capitalized aliases (hax's Rust operator names)
-- These are polymorphic so they work with both Int and fixed-width UInt types.
-- Lean's type inference resolves to the correct width-specific operation.
@[inline] def Add {α : Type} [HAdd α α α] (a b : α) : α := a + b
@[inline] def Sub {α : Type} [HSub α α α] (a b : α) : α := a - b
@[inline] def Mul {α : Type} [HMul α α α] (a b : α) : α := a * b
@[inline] def Div {α : Type} [HDiv α α α] (a b : α) : α := a / b
@[inline] def Rem {α : Type} [HMod α α α] (a b : α) : α := a % b
@[inline] def Neg {α : Type} [_root_.Neg α] (a : α) : α := -a
abbrev Eq := @beq
abbrev Ne := @bne
@[inline] def Lt {α : Type} [_root_.LT α] [DecidableRel (α := α) (· < ·)] (a b : α) : Bool :=
  decide (a < b)
@[inline] def Le {α : Type} [_root_.LE α] [DecidableRel (α := α) (· ≤ ·)] (a b : α) : Bool :=
  decide (a ≤ b)
@[inline] def Gt {α : Type} [_root_.LT α] [DecidableRel (α := α) (· < ·)] (a b : α) : Bool :=
  decide (b < a)
@[inline] def Ge {α : Type} [_root_.LE α] [DecidableRel (α := α) (· ≤ ·)] (a b : α) : Bool :=
  decide (b ≤ a)
/-- Polymorphic NOT: boolean negation for Bool, bitwise complement for UInt. -/
class HaxNot (α : Type) where
  not : α → α
instance : HaxNot Bool where not := fun b => !b
instance : HaxNot Int where not := fun a => -(a + 1)  -- bitwise complement
instance : HaxNot UInt8 where not := fun a => ~~~a
instance : HaxNot UInt16 where not := fun a => ~~~a
instance : HaxNot UInt32 where not := fun a => ~~~a
instance : HaxNot UInt64 where not := fun a => ~~~a
@[inline] def Not {α : Type} [HaxNot α] (a : α) : α := HaxNot.not a
abbrev And := @band
abbrev Or := @bor
@[inline] def Shl {α β γ : Type} [HShiftLeft α β γ] (a : α) (b : β) : γ := a <<< b
@[inline] def Shr {α β γ : Type} [HShiftRight α β γ] (a : α) (b : β) : γ := a >>> b
@[inline] def BitAnd {α : Type} [HAnd α α α] (a b : α) : α := a &&& b
@[inline] def BitOr {α : Type} [HOr α α α] (a b : α) : α := a ||| b
@[inline] def BitXor {α : Type} [HXor α α α] (a b : α) : α := a ^^^ b

/-- Polymorphic condition: coerce any type to Bool for `if` conditions.
    Bool passes through; Int uses C-style truth (nonzero = true). -/
class HaxCond (α : Type) where
  toBool : α → Bool
instance : HaxCond Bool where toBool := id
instance : HaxCond Int where toBool := fun n => n != 0
@[inline] def cond {α : Type} [HaxCond α] (a : α) : Bool := HaxCond.toBool a

/-- Generic cast (identity in untyped mode).
    Named `castVal` to avoid conflict with Lean's kernel `cast`.
    For width-specific casts, use `cast_u8_u64` etc. -/
@[inline] def castVal {α : Type} (a : α) : α := a

/-! ## Width-Aware Operations

These use Lean's built-in fixed-width integer types (`UInt8`, `UInt16`, `UInt32`,
`UInt64`), which are `BitVec n` under the hood. This ensures exact agreement
with Rust's wrapping semantics for unsigned integers.

The naming convention is `op_uN` where `op` is the operation and `N` is the
bit width (e.g., `shl_u32`, `bitxor_u64`). -/

-- UInt8 operations
@[inline] def add_u8  (a b : UInt8)  : UInt8  := a + b
@[inline] def sub_u8  (a b : UInt8)  : UInt8  := a - b
@[inline] def mul_u8  (a b : UInt8)  : UInt8  := a * b
@[inline] def div_u8  (a b : UInt8)  : UInt8  := a / b
@[inline] def rem_u8  (a b : UInt8)  : UInt8  := a % b
@[inline] def shl_u8  (a b : UInt8)  : UInt8  := a <<< b
@[inline] def shr_u8  (a b : UInt8)  : UInt8  := a >>> b
@[inline] def bitand_u8  (a b : UInt8) : UInt8 := a &&& b
@[inline] def bitor_u8   (a b : UInt8) : UInt8 := a ||| b
@[inline] def bitxor_u8  (a b : UInt8) : UInt8 := a ^^^ b
@[inline] def bitnot_u8  (a : UInt8)   : UInt8 := ~~~a
@[inline] def eq_u8  (a b : UInt8)  : Bool := a == b
@[inline] def ne_u8  (a b : UInt8)  : Bool := a != b
@[inline] def lt_u8  (a b : UInt8)  : Bool := a < b
@[inline] def le_u8  (a b : UInt8)  : Bool := a ≤ b
@[inline] def gt_u8  (a b : UInt8)  : Bool := a > b
@[inline] def ge_u8  (a b : UInt8)  : Bool := a ≥ b

-- UInt16 operations
@[inline] def add_u16 (a b : UInt16) : UInt16 := a + b
@[inline] def sub_u16 (a b : UInt16) : UInt16 := a - b
@[inline] def mul_u16 (a b : UInt16) : UInt16 := a * b
@[inline] def div_u16 (a b : UInt16) : UInt16 := a / b
@[inline] def rem_u16 (a b : UInt16) : UInt16 := a % b
@[inline] def shl_u16 (a b : UInt16) : UInt16 := a <<< b
@[inline] def shr_u16 (a b : UInt16) : UInt16 := a >>> b
@[inline] def bitand_u16 (a b : UInt16) : UInt16 := a &&& b
@[inline] def bitor_u16  (a b : UInt16) : UInt16 := a ||| b
@[inline] def bitxor_u16 (a b : UInt16) : UInt16 := a ^^^ b
@[inline] def bitnot_u16 (a : UInt16)   : UInt16 := ~~~a
@[inline] def eq_u16 (a b : UInt16) : Bool := a == b
@[inline] def ne_u16 (a b : UInt16) : Bool := a != b
@[inline] def lt_u16 (a b : UInt16) : Bool := a < b
@[inline] def le_u16 (a b : UInt16) : Bool := a ≤ b
@[inline] def gt_u16 (a b : UInt16) : Bool := a > b
@[inline] def ge_u16 (a b : UInt16) : Bool := a ≥ b

-- UInt32 operations
@[inline] def add_u32 (a b : UInt32) : UInt32 := a + b
@[inline] def sub_u32 (a b : UInt32) : UInt32 := a - b
@[inline] def mul_u32 (a b : UInt32) : UInt32 := a * b
@[inline] def div_u32 (a b : UInt32) : UInt32 := a / b
@[inline] def rem_u32 (a b : UInt32) : UInt32 := a % b
@[inline] def shl_u32 (a b : UInt32) : UInt32 := a <<< b
@[inline] def shr_u32 (a b : UInt32) : UInt32 := a >>> b
@[inline] def bitand_u32 (a b : UInt32) : UInt32 := a &&& b
@[inline] def bitor_u32  (a b : UInt32) : UInt32 := a ||| b
@[inline] def bitxor_u32 (a b : UInt32) : UInt32 := a ^^^ b
@[inline] def bitnot_u32 (a : UInt32)   : UInt32 := ~~~a
@[inline] def eq_u32 (a b : UInt32) : Bool := a == b
@[inline] def ne_u32 (a b : UInt32) : Bool := a != b
@[inline] def lt_u32 (a b : UInt32) : Bool := a < b
@[inline] def le_u32 (a b : UInt32) : Bool := a ≤ b
@[inline] def gt_u32 (a b : UInt32) : Bool := a > b
@[inline] def ge_u32 (a b : UInt32) : Bool := a ≥ b

-- UInt64 operations
@[inline] def add_u64 (a b : UInt64) : UInt64 := a + b
@[inline] def sub_u64 (a b : UInt64) : UInt64 := a - b
@[inline] def mul_u64 (a b : UInt64) : UInt64 := a * b
@[inline] def div_u64 (a b : UInt64) : UInt64 := a / b
@[inline] def rem_u64 (a b : UInt64) : UInt64 := a % b
@[inline] def shl_u64 (a b : UInt64) : UInt64 := a <<< b
@[inline] def shr_u64 (a b : UInt64) : UInt64 := a >>> b
@[inline] def bitand_u64 (a b : UInt64) : UInt64 := a &&& b
@[inline] def bitor_u64  (a b : UInt64) : UInt64 := a ||| b
@[inline] def bitxor_u64 (a b : UInt64) : UInt64 := a ^^^ b
@[inline] def bitnot_u64 (a : UInt64)   : UInt64 := ~~~a
@[inline] def eq_u64 (a b : UInt64) : Bool := a == b
@[inline] def ne_u64 (a b : UInt64) : Bool := a != b
@[inline] def lt_u64 (a b : UInt64) : Bool := a < b
@[inline] def le_u64 (a b : UInt64) : Bool := a ≤ b
@[inline] def gt_u64 (a b : UInt64) : Bool := a > b
@[inline] def ge_u64 (a b : UInt64) : Bool := a ≥ b

/-! ### Cast operations

Widening casts preserve the value; narrowing casts truncate (mod 2^target_bits),
exactly matching Rust's `as` semantics for unsigned integers. -/

-- Widening: u8 → larger
@[inline] def cast_u8_u16  (x : UInt8) : UInt16 := x.toUInt16
@[inline] def cast_u8_u32  (x : UInt8) : UInt32 := x.toUInt32
@[inline] def cast_u8_u64  (x : UInt8) : UInt64 := x.toUInt64

-- Widening: u16 → larger
@[inline] def cast_u16_u32 (x : UInt16) : UInt32 := x.toUInt32
@[inline] def cast_u16_u64 (x : UInt16) : UInt64 := x.toUInt64

-- Widening: u32 → u64
@[inline] def cast_u32_u64 (x : UInt32) : UInt64 := x.toUInt64

-- Narrowing: u64 → smaller (truncates)
@[inline] def cast_u64_u32 (x : UInt64) : UInt32 := x.toUInt32
@[inline] def cast_u64_u16 (x : UInt64) : UInt16 := x.toUInt16
@[inline] def cast_u64_u8  (x : UInt64) : UInt8  := x.toUInt8

-- Narrowing: u32 → smaller
@[inline] def cast_u32_u16 (x : UInt32) : UInt16 := x.toUInt16
@[inline] def cast_u32_u8  (x : UInt32) : UInt8  := x.toUInt8

-- Narrowing: u16 → u8
@[inline] def cast_u16_u8  (x : UInt16) : UInt8  := x.toUInt8

/-! ### Signed Integer Operations

Rust signed integers use two's complement wrapping. Since Lean 4.26 has no
`Int8`/`Int16`/`Int32`/`Int64`, we represent them as `Int` with explicit
modular reduction. `bmod_signed w n` reduces `n` to `[-2^(w-1), 2^(w-1))`. -/

/-- Signed modular reduction: maps integer to [-2^(w-1), 2^(w-1)). -/
@[inline] def bmod_signed (bits : Nat) (n : Int) : Int :=
  let m := 2 ^ bits
  let r := n % m
  if r ≥ m / 2 then r - m else r

-- Signed 8-bit operations
@[inline] def add_i8  (a b : Int) : Int := bmod_signed 8 (a + b)
@[inline] def sub_i8  (a b : Int) : Int := bmod_signed 8 (a - b)
@[inline] def mul_i8  (a b : Int) : Int := bmod_signed 8 (a * b)
@[inline] def div_i8  (a b : Int) : Int := if b = 0 then 0 else bmod_signed 8 (a / b)
@[inline] def rem_i8  (a b : Int) : Int := if b = 0 then 0 else bmod_signed 8 (a % b)
@[inline] def neg_i8  (a : Int) : Int := bmod_signed 8 (-a)
@[inline] def eq_i8   (a b : Int) : Bool := a == b
@[inline] def ne_i8   (a b : Int) : Bool := a != b
@[inline] def lt_i8   (a b : Int) : Bool := a < b
@[inline] def le_i8   (a b : Int) : Bool := a ≤ b
@[inline] def gt_i8   (a b : Int) : Bool := a > b
@[inline] def ge_i8   (a b : Int) : Bool := a ≥ b

-- Signed 16-bit operations
@[inline] def add_i16 (a b : Int) : Int := bmod_signed 16 (a + b)
@[inline] def sub_i16 (a b : Int) : Int := bmod_signed 16 (a - b)
@[inline] def mul_i16 (a b : Int) : Int := bmod_signed 16 (a * b)
@[inline] def div_i16 (a b : Int) : Int := if b = 0 then 0 else bmod_signed 16 (a / b)
@[inline] def rem_i16 (a b : Int) : Int := if b = 0 then 0 else bmod_signed 16 (a % b)
@[inline] def neg_i16 (a : Int) : Int := bmod_signed 16 (-a)
@[inline] def eq_i16  (a b : Int) : Bool := a == b
@[inline] def ne_i16  (a b : Int) : Bool := a != b
@[inline] def lt_i16  (a b : Int) : Bool := a < b
@[inline] def le_i16  (a b : Int) : Bool := a ≤ b
@[inline] def gt_i16  (a b : Int) : Bool := a > b
@[inline] def ge_i16  (a b : Int) : Bool := a ≥ b

-- Signed 32-bit operations
@[inline] def add_i32 (a b : Int) : Int := bmod_signed 32 (a + b)
@[inline] def sub_i32 (a b : Int) : Int := bmod_signed 32 (a - b)
@[inline] def mul_i32 (a b : Int) : Int := bmod_signed 32 (a * b)
@[inline] def div_i32 (a b : Int) : Int := if b = 0 then 0 else bmod_signed 32 (a / b)
@[inline] def rem_i32 (a b : Int) : Int := if b = 0 then 0 else bmod_signed 32 (a % b)
@[inline] def neg_i32 (a : Int) : Int := bmod_signed 32 (-a)
@[inline] def eq_i32  (a b : Int) : Bool := a == b
@[inline] def ne_i32  (a b : Int) : Bool := a != b
@[inline] def lt_i32  (a b : Int) : Bool := a < b
@[inline] def le_i32  (a b : Int) : Bool := a ≤ b
@[inline] def gt_i32  (a b : Int) : Bool := a > b
@[inline] def ge_i32  (a b : Int) : Bool := a ≥ b

-- Signed 64-bit operations
@[inline] def add_i64 (a b : Int) : Int := bmod_signed 64 (a + b)
@[inline] def sub_i64 (a b : Int) : Int := bmod_signed 64 (a - b)
@[inline] def mul_i64 (a b : Int) : Int := bmod_signed 64 (a * b)
@[inline] def div_i64 (a b : Int) : Int := if b = 0 then 0 else bmod_signed 64 (a / b)
@[inline] def rem_i64 (a b : Int) : Int := if b = 0 then 0 else bmod_signed 64 (a % b)
@[inline] def neg_i64 (a : Int) : Int := bmod_signed 64 (-a)
@[inline] def eq_i64  (a b : Int) : Bool := a == b
@[inline] def ne_i64  (a b : Int) : Bool := a != b
@[inline] def lt_i64  (a b : Int) : Bool := a < b
@[inline] def le_i64  (a b : Int) : Bool := a ≤ b
@[inline] def gt_i64  (a b : Int) : Bool := a > b
@[inline] def ge_i64  (a b : Int) : Bool := a ≥ b

/-! ### Signed cast operations -/

@[inline] def cast_i8_i16  (x : Int) : Int := bmod_signed 16 x
@[inline] def cast_i8_i32  (x : Int) : Int := bmod_signed 32 x
@[inline] def cast_i8_i64  (x : Int) : Int := bmod_signed 64 x
@[inline] def cast_i16_i32 (x : Int) : Int := bmod_signed 32 x
@[inline] def cast_i16_i64 (x : Int) : Int := bmod_signed 64 x
@[inline] def cast_i32_i64 (x : Int) : Int := bmod_signed 64 x
@[inline] def cast_i64_i32 (x : Int) : Int := bmod_signed 32 x
@[inline] def cast_i64_i16 (x : Int) : Int := bmod_signed 16 x
@[inline] def cast_i64_i8  (x : Int) : Int := bmod_signed 8 x
@[inline] def cast_i32_i16 (x : Int) : Int := bmod_signed 16 x
@[inline] def cast_i32_i8  (x : Int) : Int := bmod_signed 8 x
@[inline] def cast_i16_i8  (x : Int) : Int := bmod_signed 8 x

-- Cross-sign casts
@[inline] def cast_u8_i16  (x : UInt8)  : Int := bmod_signed 16 (x.toBitVec.toNat : Int)
@[inline] def cast_u16_i32 (x : UInt16) : Int := bmod_signed 32 (x.toBitVec.toNat : Int)
@[inline] def cast_u32_i64 (x : UInt32) : Int := bmod_signed 64 (x.toBitVec.toNat : Int)
@[inline] def cast_i8_u8   (x : Int) : UInt8  := UInt8.ofNat x.toNat
@[inline] def cast_i16_u16 (x : Int) : UInt16 := UInt16.ofNat x.toNat
@[inline] def cast_i32_u32 (x : Int) : UInt32 := UInt32.ofNat x.toNat
@[inline] def cast_i64_u64 (x : Int) : UInt64 := UInt64.ofNat x.toNat

/-! ### Collection operations -/

/-- Create an array filled with `n` copies of `val`. -/
@[inline] def repeat_ {α : Type} (val : α) (n : Int) : Array α :=
  (List.replicate n.toNat val).toArray

/-- Array length. -/
@[inline] def array_len {α : Type} (arr : Array α) : Nat := arr.size

/-- Rotate a UInt64 right by `n` bits. -/
@[inline] def rotate_right_u64 (x : UInt64) (n : UInt32) : UInt64 :=
  let shift := n.toUInt64 % 64
  (x >>> shift) ||| (x <<< (64 - shift))

/-- Rotate right (Int version for untyped mode). -/
@[inline] def rotate_right (x n : Int) : Int :=
  let xn := x.toNat
  let shift := n.toNat % 64
  (((xn >>> shift) ||| (xn <<< (64 - shift))) % (2 ^ 64) : Nat)

/-- Rotate a UInt32 left by `n` bits. -/
@[inline] def rotate_left_u32 (x : UInt32) (n : UInt32) : UInt32 :=
  let shift := n % 32
  (x <<< shift) ||| (x >>> (32 - shift))

/-- Rotate a UInt64 left by `n` bits. -/
@[inline] def rotate_left_u64 (x : UInt64) (n : UInt32) : UInt64 :=
  let shift := n.toUInt64 % 64
  (x <<< shift) ||| (x >>> (64 - shift))

/-- Rotate left (Int version for untyped mode). -/
@[inline] def rotate_left (x n : Int) : Int :=
  let xn := x.toNat
  let shift := n.toNat % 64
  (((xn <<< shift) ||| (xn >>> (64 - shift))) % (2 ^ 64) : Nat)

/-- Wrapping add — alias for width-aware addition. -/
@[inline] def wrapping_add_u32 (a b : UInt32) : UInt32 := a + b
@[inline] def wrapping_add_u64 (a b : UInt64) : UInt64 := a + b
@[inline] def wrapping_sub_u32 (a b : UInt32) : UInt32 := a - b
@[inline] def wrapping_sub_u64 (a b : UInt64) : UInt64 := a - b
@[inline] def wrapping_mul_u32 (a b : UInt32) : UInt32 := a * b
@[inline] def wrapping_mul_u64 (a b : UInt64) : UInt64 := a * b

/-- Wrapping add (Int version for untyped mode). -/
@[inline] def wrapping_add (a b : Int) : Int := a + b
@[inline] def wrapping_sub (a b : Int) : Int := a - b
@[inline] def wrapping_mul (a b : Int) : Int := a * b

/-- Update array element at index `i` with value `v`. Out-of-bounds is a no-op. -/
@[inline] def array_update {α : Type} (arr : Array α) (i : Int) (v : α) : Array α :=
  let n := i.toNat
  if h : n < arr.size then arr.set n v else arr

/-- Push an element onto an array. -/
@[inline] def push {α : Type} (arr : Array α) (x : α) : Array α := arr.push x

-- Array literal — surface code uses `#[...]` syntax instead.
-- Not called directly; `array_lit` in ImpExpr maps to `#[...]` in surface Lean.

/-- Byte string literal placeholder (untyped extraction). -/
@[inline] def literal : Array Int := #[]

/-- Copy from slice — identity in untyped extraction. -/
@[inline] def copy_from_slice {α : Type} (_dst : Array α) (src : Array α) : Array α := src

/-- Extend from slice — append in untyped extraction. -/
@[inline] def extend_from_slice {α : Type} (dst : Array α) (src : Array α) : Array α := dst ++ src

/-- Into iter — identity in untyped extraction. -/
@[inline] def into_iter {α : Type} (x : α) : α := x

/-- Into vec — identity in untyped extraction. -/
@[inline] def into_vec {α : Type} (x : α) : α := x

/-- Next (iterator) — identity in untyped extraction. -/
@[inline] def next {α : Type} (x : α) : α := x

/-- Enumerate — identity in untyped extraction. -/
@[inline] def enumerate {α : Type} (x : α) : α := x

/-- With capacity — empty array in untyped extraction. -/
@[inline] def with_capacity {α : Type} (_n : Int) : Array α := #[]

/-- From elem — repeat in untyped extraction. -/
@[inline] def from_elem {α : Type} (val : α) (n : Int) : Array α :=
  (List.replicate n.toNat val).toArray

/-- Check if array is empty (Vec::is_empty). -/
@[inline] def is_empty {α : Type} (arr : Array α) : Bool := arr.isEmpty

/-- Truncate — identity in untyped extraction. -/
@[inline] def truncate {α : Type} (arr : Array α) (_n : Int) : Array α := arr

/-- Mutable index — identity in untyped extraction (slice access pattern). -/
@[inline] def index_mut {α : Type} (arr : α) (_i : Int) : α := arr

/-- Range-to constructor (0..hi). -/
@[inline] def RangeTo (hi : Int) : Int := hi

/-- Range-from constructor (lo..). -/
@[inline] def RangeFrom (lo : Int) : Int := lo

/-- Slice to: arr[..hi] — take first hi elements. -/
@[inline] def slice_to {α : Type} (arr : Array α) (hi : Int) : Array α :=
  arr.toList.take hi.toNat |>.toArray

/-- Slice from: arr[lo..] — drop first lo elements. -/
@[inline] def slice_from {α : Type} (arr : Array α) (lo : Int) : Array α :=
  arr.toList.drop lo.toNat |>.toArray

/-- Slice range: arr[lo..hi] — subarray from lo to hi. -/
@[inline] def slice_range {α : Type} (arr : Array α) (lo hi : Int) : Array α :=
  (arr.toList.drop lo.toNat).take (hi.toNat - lo.toNat) |>.toArray

/-- Collect range into array. -/
@[inline] def range (lo hi : Int) : Array Int :=
  (List.range (hi.toNat - lo.toNat)).map (· + lo.toNat) |>.map (Int.ofNat) |>.toArray

/-- Convert Bool to Int (true → 1, false → 0). -/
@[inline] def boolToInt (b : Bool) : Int := if b then 1 else 0

/-- Deref — identity in untyped extraction. -/
@[inline] def deref {α : Type} (x : α) : α := x

/-- Assignment placeholder (identity). -/
@[inline] def assign {α : Type} (x : α) : α := x

/-- From constructor placeholder (identity). -/
@[inline] def from_val {α : Type} (x : α) : α := x

-- USize casts
@[inline] def cast_usize_u64 (x : USize) : UInt64 := UInt64.ofNat x.toNat
@[inline] def cast_u64_usize (x : UInt64) : USize := USize.ofNat x.toBitVec.toNat

end Hax

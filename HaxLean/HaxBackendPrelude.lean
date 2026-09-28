/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import HaxLean.Rust.Scalar
public import HaxLean.Rust.Array

/-!
# A prelude for the hax Lean backend over the Aeneas `Std` model

The hax Lean backend (`cargo hax into lean`) prints code against the hax proof-libs
package `Hax`. This module gives the names that output uses, each defined as the
corresponding operation of the vendored Aeneas `Std` model (`HaxLean/Rust`), so a backend
file elaborates with `import Hax` replaced by `import HaxLean.HaxBackendPrelude` and
`open HaxBackend`.

The definitions follow the proof-libs sources of the backend's commit (hax
`36174312c7`, `hax-lib/proof-libs/lean/Hax`):

* `RustM` is `Aeneas.Std.RustM`, the machine integers are `UScalar` and `IScalar`.
* `^^^?`, `&&&?`, `|||?` are total; `+?`, `-?`, `*?` are the Aeneas checked operations
  (a panic on overflow); `>>>?`, `<<<?` panic when the amount is negative or at least the
  width.
* `Rust_primitives.Hax.cast_op` is Rust `as` between unsigned integers (truncation or zero
  extension).
* `RustArray α n` is `Aeneas.Std.Array α n`; `a[i]_?` is `Array.index_usize` and
  `update_at_usize` is `Array.update`, both panicking out of range.
* `Rust_primitives.Hax.Folds.fold_range s e inv init body` runs `body` on the indices
  `s, …, e - 1` in order, ignoring the invariant `inv`.

The two preludes differ in the following respects:

* proof-libs has seven error kinds (`integerOverflow`, `arrayOutOfBounds`, …); the Aeneas
  model has `panic` and `undef`, and every failure here is `panic`.
* proof-libs `usize` is `USize64`, always 64 bits; Aeneas `Usize` has width
  `System.Platform.numBits`.
* proof-libs `u128` is `BitVec 128` and has no `Cast` from `u64` and no checked `*?`;
  here `u128` is `UScalar .U128` with both.
* Integer literals wrap modulo the width in both (`OfNat`, scoped here).
-/

@[expose] public section

set_option autoImplicit false

namespace HaxBackend

open Aeneas.Std

/-- The result monad of the backend output. -/
abbrev RustM := Aeneas.Std.RustM

abbrev u8 := UScalar .U8
abbrev u16 := UScalar .U16
abbrev u32 := UScalar .U32
abbrev u64 := UScalar .U64
abbrev u128 := UScalar .U128
abbrev usize := UScalar .Usize
abbrev i8 := IScalar .I8
abbrev i16 := IScalar .I16
abbrev i32 := IScalar .I32
abbrev i64 := IScalar .I64
abbrev i128 := IScalar .I128
abbrev isize := IScalar .Isize

/-- An unsigned literal, modulo `2 ^ numBits`. -/
scoped instance instOfNatUScalar {ty : UScalarTy} {n : Nat} : OfNat (UScalar ty) n :=
  ⟨⟨BitVec.ofNat _ n⟩⟩

/-- A signed literal, modulo `2 ^ numBits` in two's complement. -/
scoped instance instOfNatIScalar {ty : IScalarTy} {n : Nat} : OfNat (IScalar ty) n :=
  ⟨⟨BitVec.ofNat _ n⟩⟩

/-! ## Operators -/

/-- Bitwise exclusive or, total. -/
def bitxor {α : Type} [HXor α α α] (a b : α) : RustM α := .ok (a ^^^ b)

/-- Bitwise and, total. -/
def bitand {α : Type} [HAnd α α α] (a b : α) : RustM α := .ok (a &&& b)

/-- Bitwise or, total. -/
def bitor {α : Type} [HOr α α α] (a b : α) : RustM α := .ok (a ||| b)

/-- Bitwise complement, total. -/
def bitnot {α : Type} [Complement α] (a : α) : RustM α := .ok (~~~a)

/-- Checked addition: the Aeneas `+`, a panic on overflow. -/
def add {α : Type} [HAdd α α (RustM α)] (a b : α) : RustM α := a + b

/-- Checked subtraction: the Aeneas `-`, a panic on overflow. -/
def sub {α : Type} [HSub α α (RustM α)] (a b : α) : RustM α := a - b

/-- Checked multiplication: the Aeneas `*`, a panic on overflow. -/
def mul {α : Type} [HMul α α (RustM α)] (a b : α) : RustM α := a * b

/-- Right shift: the Aeneas `>>>`, a panic when the amount is negative or at least the
    width of the shifted operand. -/
def shr {α β : Type} [HShiftRight α β (RustM α)] (a : α) (b : β) : RustM α := a >>> b

/-- Left shift: the Aeneas `<<<`, a panic when the amount is negative or at least the
    width of the shifted operand. -/
def shl {α β : Type} [HShiftLeft α β (RustM α)] (a : α) (b : β) : RustM α := a <<< b

scoped infixl:58 " ^^^? " => bitxor
scoped infixl:60 " &&&? " => bitand
scoped infixl:60 " |||? " => bitor
scoped prefix:75 "~?" => bitnot
scoped infixl:65 " +? " => add
scoped infixl:65 " -? " => sub
scoped infixl:70 " *? " => mul
scoped infixl:75 " >>>? " => shr
scoped infixl:75 " <<<? " => shl

/-! ## Methods of `u64` -/

namespace Core_models.Num.Impl_9

/-- `u64::wrapping_add`: addition modulo `2 ^ 64`. -/
def wrapping_add (x y : u64) : RustM u64 := .ok (UScalar.wrapping_add x y)

/-- `u64::wrapping_sub`: subtraction modulo `2 ^ 64`. -/
def wrapping_sub (x y : u64) : RustM u64 := .ok (UScalar.wrapping_sub x y)

/-- `u64::wrapping_mul`: multiplication modulo `2 ^ 64`. -/
def wrapping_mul (x y : u64) : RustM u64 := .ok (UScalar.wrapping_mul x y)

end Core_models.Num.Impl_9

/-! ## Casts -/

/-- A Rust `as` cast from `α` to `β`. -/
class Cast (α β : Type) where
  cast : α → RustM β

/-- `as` between unsigned integers: truncation or zero extension. -/
instance instCastUScalar {s t : UScalarTy} : Cast (UScalar s) (UScalar t) where
  cast x := .ok (UScalar.cast t x)

/-- The cast the backend prints for `as`. -/
def Rust_primitives.Hax.cast_op {α β : Type} [Cast α β] (x : α) : RustM β := Cast.cast x

/-! ## Tuples -/

/-- A pair. -/
structure Rust_primitives.Hax.Tuple2 (α0 α1 : Type) where
  _0 : α0
  _1 : α1

/-! ## Arrays -/

/-- A Rust array `[α; n]`. -/
abbrev RustArray (α : Type) (n : usize) := Aeneas.Std.Array α n

/-- Panicking lookup `xs[i]_?`. -/
class GetElemResult (coll : Type) (idx : Type) (elem : outParam Type) where
  getElemResult : coll → idx → RustM elem

/-- `xs[i]_?`: the element at `i`, a panic out of range. -/
scoped syntax:max term noWs "[" withoutPosition(term) "]" noWs "_?" : term
macro_rules | `($x[$i]_?) => `(GetElemResult.getElemResult $x $i)

/-- Array lookup at a `usize` index: `Array.index_usize`. -/
instance instGetElemResultArray {α : Type} {n : usize} :
    GetElemResult (RustArray α n) usize α where
  getElemResult xs i := Array.index_usize xs i

/-- Array update at a `usize` index: `Array.update`, a panic out of range. -/
def Rust_primitives.Hax.Monomorphized_update_at.update_at_usize {α : Type} {n : usize}
    (a : RustArray α n) (i : usize) (v : α) : RustM (RustArray α n) :=
  Array.update a i v

/-! ## Loops -/

/-- `body` run on `k` successive indices from `i`. -/
def foldRangeAux {α : Type} {ty : UScalarTy} (body : α → UScalar ty → RustM α) :
    Nat → Nat → α → RustM α
  | 0, _, acc => .ok acc
  | k + 1, i, acc => do
    let acc ← body acc ⟨BitVec.ofNat _ i⟩
    foldRangeAux body k (i + 1) acc

/-- `for i in s..e`: `body` run on the indices `s, …, e - 1` in order; the invariant `inv`
    is not evaluated. -/
def Rust_primitives.Hax.Folds.fold_range {α : Type} {ty : UScalarTy}
    (s e : UScalar ty) (_inv : α → UScalar ty → RustM Bool) (init : α)
    (body : α → UScalar ty → RustM α) : RustM α :=
  foldRangeAux body (e.val - s.val) s.val init

end HaxBackend

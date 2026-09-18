/-
Copyright (c) the Aeneas contributors. Licensed under the Apache License,
Version 2.0 (the "License"); you may not use this file except in compliance with
the License. You may obtain a copy of the License at
http://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable law or
agreed to in writing, software distributed under the License is distributed on
an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and
limitations under the License.

Ported to Lean v4.33.1 without Mathlib by the CatCrypt Contributors.
Source: cryspen/aeneas at 6852e6474ec508930acba4df79977b3483a10d10,
  backends/lean/Aeneas/Std/Scalar/Core.lean
-/

module

public import HaxLean.Rust.Core
public import HaxLean.Rust.Arith

/-!
# Machine Integers

Unsigned integers `UScalar ty` and signed integers `IScalar ty` are bit vectors of width
`ty.numBits`; the width of `usize` and `isize` is `System.Platform.numBits`.
`UScalar.val` reads the bit vector as a natural number, `IScalar.val` as a two's-complement
integer. The module gives the bounds, the checked constructors `tryMk`, the literals
`ofNat`/`ofInt`, the `core::num` constants and the comparison instances.
-/

@[expose] public section

set_option autoImplicit false

namespace Aeneas

namespace Std

open RustM Error

/-- Kinds of unsigned integers -/
inductive UScalarTy where
| Usize
| U8
| U16
| U32
| U64
| U128

/-- Kinds of signed integers -/
inductive IScalarTy where
| Isize
| I8
| I16
| I32
| I64
| I128

/-- Bit width of an unsigned integer kind. -/
@[implicit_reducible]
def UScalarTy.numBits (ty : UScalarTy) : Nat :=
  match ty with
  | Usize => System.Platform.numBits
  | U8 => 8
  | U16 => 16
  | U32 => 32
  | U64 => 64
  | U128 => 128

/-- Bit width of a signed integer kind. -/
@[implicit_reducible]
def IScalarTy.numBits (ty : IScalarTy) : Nat :=
  match ty with
  | Isize => System.Platform.numBits
  | I8 => 8
  | I16 => 16
  | I32 => 32
  | I64 => 64
  | I128 => 128

/-- Unsigned integer -/
structure UScalar (ty : UScalarTy) where
  bv : BitVec ty.numBits
deriving Repr, BEq, DecidableEq

/-- The value of an unsigned integer. -/
def UScalar.val {ty} (x : UScalar ty) : Nat := x.bv.toNat

/-- Signed integer -/
structure IScalar (ty : IScalarTy) where
  bv : BitVec ty.numBits
deriving Repr, BEq, DecidableEq

/-- The value of a signed integer (two's-complement reading). -/
def IScalar.val {ty} (x : IScalar ty) : Int := x.bv.toInt

/-!
# Bounds, Size

The bounds are irreducible so that unification does not evaluate powers such as `2^128`.
-/

@[irreducible] def UScalar.max (ty : UScalarTy) : Nat := 2^ty.numBits-1
@[irreducible] def IScalar.min (ty : IScalarTy) : Int := -2^(ty.numBits - 1)
@[irreducible] def IScalar.max (ty : IScalarTy) : Int := 2^(ty.numBits - 1)-1

@[irreducible] def UScalar.size (ty : UScalarTy) : Nat := 2^ty.numBits
@[irreducible] def IScalar.size (ty : IScalarTy) : Int := 2^ty.numBits

/-! ## Num Bits -/
@[irreducible] def U8.numBits    : Nat := UScalarTy.U8.numBits
@[irreducible] def U16.numBits   : Nat := UScalarTy.U16.numBits
@[irreducible] def U32.numBits   : Nat := UScalarTy.U32.numBits
@[irreducible] def U64.numBits   : Nat := UScalarTy.U64.numBits
@[irreducible] def U128.numBits  : Nat := UScalarTy.U128.numBits
@[irreducible] def Usize.numBits : Nat := UScalarTy.Usize.numBits

@[irreducible] def I8.numBits    : Nat := IScalarTy.I8.numBits
@[irreducible] def I16.numBits   : Nat := IScalarTy.I16.numBits
@[irreducible] def I32.numBits   : Nat := IScalarTy.I32.numBits
@[irreducible] def I64.numBits   : Nat := IScalarTy.I64.numBits
@[irreducible] def I128.numBits  : Nat := IScalarTy.I128.numBits
@[irreducible] def Isize.numBits : Nat := IScalarTy.Isize.numBits

/-! ## Bounds -/
@[irreducible] def U8.max    : Nat := 2^U8.numBits - 1
@[irreducible] def U16.max   : Nat := 2^U16.numBits - 1
@[irreducible] def U32.max   : Nat := 2^U32.numBits - 1
@[irreducible] def U64.max   : Nat := 2^U64.numBits - 1
@[irreducible] def U128.max  : Nat := 2^U128.numBits - 1
@[irreducible] def Usize.max : Nat := 2^Usize.numBits - 1

@[irreducible] def I8.min    : Int := -2^(I8.numBits - 1)
@[irreducible] def I8.max    : Int := 2^(I8.numBits - 1) - 1
@[irreducible] def I16.min   : Int := -2^(I16.numBits - 1)
@[irreducible] def I16.max   : Int := 2^(I16.numBits - 1) - 1
@[irreducible] def I32.min   : Int := -2^(I32.numBits - 1)
@[irreducible] def I32.max   : Int := 2^(I32.numBits - 1) - 1
@[irreducible] def I64.min   : Int := -2^(I64.numBits - 1)
@[irreducible] def I64.max   : Int := 2^(I64.numBits - 1) - 1
@[irreducible] def I128.min  : Int := -2^(I128.numBits - 1)
@[irreducible] def I128.max  : Int := 2^(I128.numBits - 1) - 1
@[irreducible] def Isize.min : Int := -2^(Isize.numBits - 1)
@[irreducible] def Isize.max : Int := 2^(Isize.numBits - 1) - 1

/-! ## Size -/
@[irreducible] def U8.size    : Nat := 2^U8.numBits
@[irreducible] def U16.size   : Nat := 2^U16.numBits
@[irreducible] def U32.size   : Nat := 2^U32.numBits
@[irreducible] def U64.size   : Nat := 2^U64.numBits
@[irreducible] def U128.size  : Nat := 2^U128.numBits
@[irreducible] def Usize.size : Nat := 2^Usize.numBits

@[irreducible] def I8.size    : Nat := 2^I8.numBits
@[irreducible] def I16.size   : Nat := 2^I16.numBits
@[irreducible] def I32.size   : Nat := 2^I32.numBits
@[irreducible] def I64.size   : Nat := 2^I64.numBits
@[irreducible] def I128.size  : Nat := 2^I128.numBits
@[irreducible] def Isize.size : Nat := 2^Isize.numBits

/-! ## "Reduced" Constants -/
/-! ### Size -/
def I8.rSize   : Int := 256
def I16.rSize  : Int := 65536
def I32.rSize  : Int := 4294967296
def I64.rSize  : Int := 18446744073709551616
def I128.rSize : Int := 340282366920938463463374607431768211456

def U8.rSize   : Nat := 256
def U16.rSize  : Nat := 65536
def U32.rSize  : Nat := 4294967296
def U64.rSize  : Nat := 18446744073709551616
def U128.rSize : Nat := 340282366920938463463374607431768211456

/-! ### Bounds -/
def U8.rMax   : Nat := 255
def U16.rMax  : Nat := 65535
def U32.rMax  : Nat := 4294967295
def U64.rMax  : Nat := 18446744073709551615
def U128.rMax : Nat := 340282366920938463463374607431768211455
def Usize.rMax : Nat := 2^System.Platform.numBits-1

def I8.rMin   : Int := -128
def I8.rMax   : Int := 127
def I16.rMin  : Int := -32768
def I16.rMax  : Int := 32767
def I32.rMin  : Int := -2147483648
def I32.rMax  : Int := 2147483647
def I64.rMin  : Int := -9223372036854775808
def I64.rMax  : Int := 9223372036854775807
def I128.rMin : Int := -170141183460469231731687303715884105728
def I128.rMax : Int := 170141183460469231731687303715884105727
def Isize.rMin : Int := -2^(System.Platform.numBits - 1)
def Isize.rMax : Int := 2^(System.Platform.numBits - 1)-1

def UScalar.rMax (ty : UScalarTy) : Nat :=
  match ty with
  | .Usize => Usize.rMax
  | .U8    => U8.rMax
  | .U16   => U16.rMax
  | .U32   => U32.rMax
  | .U64   => U64.rMax
  | .U128  => U128.rMax

def IScalar.rMin (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => Isize.rMin
  | .I8    => I8.rMin
  | .I16   => I16.rMin
  | .I32   => I32.rMin
  | .I64   => I64.rMin
  | .I128  => I128.rMin

def IScalar.rMax (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => Isize.rMax
  | .I8    => I8.rMax
  | .I16   => I16.rMax
  | .I32   => I32.rMax
  | .I64   => I64.rMax
  | .I128  => I128.rMax

/-! # Theorems -/
theorem UScalarTy.numBits_nonzero (ty : UScalarTy) : ty.numBits ≠ 0 := by
  cases ty <;> simp [numBits]
  cases System.Platform.numBits_eq <;> simp_all

theorem IScalarTy.numBits_nonzero (ty : IScalarTy) : ty.numBits ≠ 0 := by
  cases ty <;> simp [numBits]
  cases System.Platform.numBits_eq <;> simp_all

@[simp, grind =] theorem UScalarTy.U8_numBits_eq    : UScalarTy.U8.numBits    = 8 := by rfl
@[simp, grind =] theorem UScalarTy.U16_numBits_eq   : UScalarTy.U16.numBits   = 16 := by rfl
@[simp, grind =] theorem UScalarTy.U32_numBits_eq   : UScalarTy.U32.numBits   = 32 := by rfl
@[simp, grind =] theorem UScalarTy.U64_numBits_eq   : UScalarTy.U64.numBits   = 64 := by rfl
@[simp, grind =] theorem UScalarTy.U128_numBits_eq  : UScalarTy.U128.numBits  = 128 := by rfl
@[simp, grind =] theorem UScalarTy.Usize_numBits_eq :
    UScalarTy.Usize.numBits = System.Platform.numBits := by rfl

@[simp, grind =] theorem IScalarTy.I8_numBits_eq    : IScalarTy.I8.numBits    = 8 := by rfl
@[simp, grind =] theorem IScalarTy.I16_numBits_eq   : IScalarTy.I16.numBits   = 16 := by rfl
@[simp, grind =] theorem IScalarTy.I32_numBits_eq   : IScalarTy.I32.numBits   = 32 := by rfl
@[simp, grind =] theorem IScalarTy.I64_numBits_eq   : IScalarTy.I64.numBits   = 64 := by rfl
@[simp, grind =] theorem IScalarTy.I128_numBits_eq  : IScalarTy.I128.numBits  = 128 := by rfl
@[simp, grind =] theorem IScalarTy.Isize_numBits_eq :
    IScalarTy.Isize.numBits = System.Platform.numBits := by rfl

@[simp, grind =] theorem UScalar.max_UScalarTy_U8_eq    : UScalar.max .U8 = U8.max := by
  simp [UScalar.max, U8.max, U8.numBits]
@[simp, grind =] theorem UScalar.max_UScalarTy_U16_eq   : UScalar.max .U16 = U16.max := by
  simp [UScalar.max, U16.max, U16.numBits]
@[simp, grind =] theorem UScalar.max_UScalarTy_U32_eq   : UScalar.max .U32 = U32.max := by
  simp [UScalar.max, U32.max, U32.numBits]
@[simp, grind =] theorem UScalar.max_UScalarTy_U64_eq   : UScalar.max .U64 = U64.max := by
  simp [UScalar.max, U64.max, U64.numBits]
@[simp, grind =] theorem UScalar.max_UScalarTy_U128_eq  : UScalar.max .U128 = U128.max := by
  simp [UScalar.max, U128.max, U128.numBits]
@[grind =] theorem UScalar.max_USize_eq : UScalar.max .Usize = Usize.max := by
  simp [UScalar.max, Usize.max, Usize.numBits]

@[simp, grind =] theorem IScalar.min_IScalarTy_I8_eq    : IScalar.min .I8 = I8.min := by
  simp [IScalar.min, I8.min, I8.numBits]
@[simp, grind =] theorem IScalar.max_IScalarTy_I8_eq    : IScalar.max .I8 = I8.max := by
  simp [IScalar.max, I8.max, I8.numBits]
@[simp, grind =] theorem IScalar.min_IScalarTy_I16_eq   : IScalar.min .I16 = I16.min := by
  simp [IScalar.min, I16.min, I16.numBits]
@[simp, grind =] theorem IScalar.max_IScalarTy_I16_eq   : IScalar.max .I16 = I16.max := by
  simp [IScalar.max, I16.max, I16.numBits]
@[simp, grind =] theorem IScalar.min_IScalarTy_I32_eq   : IScalar.min .I32 = I32.min := by
  simp [IScalar.min, I32.min, I32.numBits]
@[simp, grind =] theorem IScalar.max_IScalarTy_I32_eq   : IScalar.max .I32 = I32.max := by
  simp [IScalar.max, I32.max, I32.numBits]
@[simp, grind =] theorem IScalar.min_IScalarTy_I64_eq   : IScalar.min .I64 = I64.min := by
  simp [IScalar.min, I64.min, I64.numBits]
@[simp, grind =] theorem IScalar.max_IScalarTy_I64_eq   : IScalar.max .I64 = I64.max := by
  simp [IScalar.max, I64.max, I64.numBits]
@[simp, grind =] theorem IScalar.min_IScalarTy_I128_eq  : IScalar.min .I128 = I128.min := by
  simp [IScalar.min, I128.min, I128.numBits]
@[simp, grind =] theorem IScalar.max_IScalarTy_I128_eq  : IScalar.max .I128 = I128.max := by
  simp [IScalar.max, I128.max, I128.numBits]
@[grind =] theorem IScalar.min_ISize_eq : IScalar.min .Isize = Isize.min := by
  simp [IScalar.min, Isize.min, Isize.numBits]
@[grind =] theorem IScalar.max_ISize_eq : IScalar.max .Isize = Isize.max := by
  simp [IScalar.max, Isize.max, Isize.numBits]

@[grind =] theorem U8.max_eq    : U8.max = 255 := by simp [U8.max, U8.numBits]
@[grind =] theorem U16.max_eq   : U16.max = 65535 := by simp [U16.max, U16.numBits]
@[grind =] theorem U32.max_eq   : U32.max = 4294967295 := by simp [U32.max, U32.numBits]
@[grind =] theorem U64.max_eq   : U64.max = 18446744073709551615 := by simp [U64.max, U64.numBits]
@[grind =] theorem U128.max_eq  : U128.max = 340282366920938463463374607431768211455 := by
  simp [U128.max, U128.numBits]

@[grind =] theorem I8.min_eq    : I8.min = -128 := by simp [I8.min, I8.numBits]
@[grind =] theorem I8.max_eq    : I8.max = 127 := by simp [I8.max, I8.numBits]
@[grind =] theorem I16.min_eq   : I16.min = -32768 := by simp [I16.min, I16.numBits]
@[grind =] theorem I16.max_eq   : I16.max = 32767 := by simp [I16.max, I16.numBits]
@[grind =] theorem I32.min_eq   : I32.min = -2147483648 := by simp [I32.min, I32.numBits]
@[grind =] theorem I32.max_eq   : I32.max = 2147483647 := by simp [I32.max, I32.numBits]
@[grind =] theorem I64.min_eq   : I64.min = -9223372036854775808 := by simp [I64.min, I64.numBits]
@[grind =] theorem I64.max_eq   : I64.max = 9223372036854775807 := by simp [I64.max, I64.numBits]
@[grind =] theorem I128.min_eq  : I128.min = -170141183460469231731687303715884105728 := by
  simp [I128.min, I128.numBits]
@[grind =] theorem I128.max_eq  : I128.max = 170141183460469231731687303715884105727 := by
  simp [I128.max, I128.numBits]

local syntax "simp_bounds" : tactic
local macro_rules
| `(tactic|simp_bounds) =>
  `(tactic|
      simp [
      UScalar.rMax, UScalar.max,
      Usize.rMax, Usize.rMax, Usize.max,
      U8.rMax, U8.max, U16.rMax, U16.max, U32.rMax, U32.max,
      U64.rMax, U64.max, U128.rMax, U128.max,
      U8.numBits, U16.numBits, U32.numBits, U64.numBits, U128.numBits, Usize.numBits,
      UScalar.size, U8.size, U16.size, U32.size, U64.size, U128.size, Usize.size,
      IScalar.rMax, IScalar.max,
      IScalar.rMin, IScalar.min,
      Isize.rMax, Isize.rMax, Isize.max,
      I8.rMax, I8.max, I16.rMax, I16.max, I32.rMax, I32.max,
      I64.rMax, I64.max, I128.rMax, I128.max,
      Isize.rMin, Isize.rMin, Isize.min,
      I8.rMin, I8.min, I16.rMin, I16.min, I32.rMin, I32.min,
      I64.rMin, I64.min, I128.rMin, I128.min,
      I8.numBits, I16.numBits, I32.numBits, I64.numBits, I128.numBits, Isize.numBits,
      IScalar.size, I8.size, I16.size, I32.size, I64.size, I128.size, Isize.size])

theorem Usize.bounds_eq :
  Usize.max = U32.max ∨ Usize.max = U64.max := by
  simp [Usize.max, Usize.numBits]
  cases System.Platform.numBits_eq <;>
  simp [*] <;>
  simp_bounds

grind_pattern Usize.bounds_eq => Usize.max

theorem Isize.bounds_eq :
  (Isize.min = I32.min ∧ Isize.max = I32.max)
  ∨ (Isize.min = I64.min ∧ Isize.max = I64.max) := by
  simp [Isize.min, Isize.max, Isize.numBits]
  cases System.Platform.numBits_eq <;>
  simp [*] <;> simp [I32.min, I32.numBits, I32.max, I64.min, I64.numBits, I64.max]

grind_pattern Isize.bounds_eq => Isize.max
grind_pattern Isize.bounds_eq => Isize.min

theorem UScalar.rMax_eq_max (ty : UScalarTy) : UScalar.rMax ty = UScalar.max ty := by
  cases ty <;>
  simp_bounds

theorem IScalar.rbound_eq_bound (ty : IScalarTy) :
  IScalar.rMin ty = IScalar.min ty ∧ IScalar.rMax ty = IScalar.max ty := by
  cases ty <;> refine ⟨?_, ?_⟩ <;>
  simp_bounds

theorem IScalar.rMin_eq_min (ty : IScalarTy) : IScalar.rMin ty = IScalar.min ty := by
  apply (IScalar.rbound_eq_bound ty).left

theorem IScalar.rMax_eq_max (ty : IScalarTy) : IScalar.rMax ty = IScalar.max ty := by
  apply (IScalar.rbound_eq_bound ty).right

/-!
# Conservative Bounds

The bounds of `usize` and `isize` depend on `System.Platform.numBits` and do not reduce;
the conservative bounds use the 32-bit bounds for them and reduce, so that a literal can be
checked against them by `decide`.
-/

def UScalarTy.cNumBits (ty : UScalarTy) : Nat :=
  match ty with
  | .Usize => U32.numBits
  | _ => ty.numBits

def IScalarTy.cNumBits (ty : IScalarTy) : Nat :=
  match ty with
  | .Isize => I32.numBits
  | _ => ty.numBits

theorem UScalarTy.cNumBits_le (ty : UScalarTy) : ty.cNumBits ≤ ty.numBits := by
  cases ty <;> simp only [cNumBits, U32.numBits, numBits, System.Platform.le_numBits,
    Nat.le_refl]

theorem IScalarTy.cNumBits_le (ty : IScalarTy) : ty.cNumBits ≤ ty.numBits := by
  cases ty <;> simp only [cNumBits, I32.numBits, numBits, System.Platform.le_numBits,
    Nat.le_refl]

theorem UScalarTy.cNumBits_nonzero (ty : UScalarTy) : ty.cNumBits ≠ 0 := by
  cases ty <;> simp [cNumBits, U32.numBits, numBits]

theorem IScalarTy.cNumBits_nonzero (ty : IScalarTy) : ty.cNumBits ≠ 0 := by
  cases ty <;> simp [cNumBits, I32.numBits, numBits]

def UScalar.cMax (ty : UScalarTy) : Nat :=
  match ty with
  | .Usize => UScalar.rMax .U32
  | _ => UScalar.rMax ty

def IScalar.cMin (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => IScalar.rMin .I32
  | _ => IScalar.rMin ty

def IScalar.cMax (ty : IScalarTy) : Int :=
  match ty with
  | .Isize => IScalar.rMax .I32
  | _ => IScalar.rMax ty

@[grind .]
theorem UScalar.hBounds {ty} (x : UScalar ty) : x.val < 2^ty.numBits := by
  simp only [val]; exact x.bv.isLt

theorem UScalar.hSize {ty} (x : UScalar ty) : x.val < UScalar.size ty := by
  simp only [size]; exact x.hBounds

theorem UScalar.rMax_eq_pow_numBits (ty : UScalarTy) : UScalar.rMax ty = 2^ty.numBits - 1 := by
  cases ty <;> simp [rMax] <;> simp_bounds

theorem UScalar.cMax_eq_pow_cNumBits (ty : UScalarTy) :
    UScalar.cMax ty = 2^ty.cNumBits - 1 := by
  cases ty <;> simp [cMax, UScalarTy.cNumBits] <;> simp_bounds

theorem UScalar.cMax_le_rMax (ty : UScalarTy) : UScalar.cMax ty ≤ UScalar.rMax ty := by
  have := rMax_eq_pow_numBits ty
  have := cMax_eq_pow_cNumBits ty
  have := ty.cNumBits_le
  have := @Nat.pow_le_pow_right 2 (by simp) ty.cNumBits ty.numBits ty.cNumBits_le
  omega

theorem UScalar.hrBounds {ty} (x : UScalar ty) : x.val ≤ UScalar.rMax ty := by
  have := UScalar.hBounds x
  have := UScalar.rMax_eq_pow_numBits ty
  omega

theorem UScalar.hmax {ty} (x : UScalar ty) : x.val < 2^ty.numBits := x.hBounds

theorem IScalar.hBounds {ty} (x : IScalar ty) :
  -2^(ty.numBits - 1) ≤ x.val ∧ x.val < 2^(ty.numBits - 1) :=
  ⟨BitVec.le_toInt x.bv, BitVec.toInt_lt⟩

theorem IScalar.rMin_eq_pow_numBits (ty : IScalarTy) :
    IScalar.rMin ty = -2^(ty.numBits - 1) := by
  cases ty <;> simp <;> simp_bounds

theorem IScalar.rMax_eq_pow_numBits (ty : IScalarTy) :
    IScalar.rMax ty = 2^(ty.numBits - 1) - 1 := by
  cases ty <;> simp [rMax] <;> simp_bounds

theorem IScalar.cMin_eq_pow_cNumBits (ty : IScalarTy) :
    IScalar.cMin ty = -2^(ty.cNumBits - 1) := by
  cases ty <;> simp [cMin, IScalarTy.cNumBits] <;> simp_bounds

theorem IScalar.cMax_eq_pow_cNumBits (ty : IScalarTy) :
    IScalar.cMax ty = 2^(ty.cNumBits - 1) - 1 := by
  cases ty <;> simp [cMax, IScalarTy.cNumBits] <;> simp_bounds

theorem IScalar.rMin_le_cMin (ty : IScalarTy) : IScalar.rMin ty ≤ IScalar.cMin ty := by
  have := rMin_eq_pow_numBits ty
  have := cMin_eq_pow_cNumBits ty
  have := ty.cNumBits_le
  have := ty.cNumBits_nonzero
  have h := @Nat.pow_le_pow_right 2 (by simp) (ty.cNumBits - 1) (ty.numBits - 1) (by omega)
  have h' : ((2 ^ (ty.cNumBits - 1) : Nat) : Int) ≤ ((2 ^ (ty.numBits - 1) : Nat) : Int) := by
    exact_mod_cast h
  simp only [Int.natCast_pow, Int.cast_ofNat_Int] at h'
  omega

theorem IScalar.cMax_le_rMax (ty : IScalarTy) : IScalar.cMax ty ≤ IScalar.rMax ty := by
  have := rMax_eq_pow_numBits ty
  have := cMax_eq_pow_cNumBits ty
  have := ty.cNumBits_le
  have := ty.cNumBits_nonzero
  have h := @Nat.pow_le_pow_right 2 (by simp) (ty.cNumBits - 1) (ty.numBits - 1) (by omega)
  have h' : ((2 ^ (ty.cNumBits - 1) : Nat) : Int) ≤ ((2 ^ (ty.numBits - 1) : Nat) : Int) := by
    exact_mod_cast h
  simp only [Int.natCast_pow, Int.cast_ofNat_Int] at h'
  omega

theorem IScalar.hrBounds {ty} (x : IScalar ty) :
  IScalar.rMin ty ≤ x.val ∧ x.val ≤ IScalar.rMax ty := by
  have := IScalar.hBounds x
  have := IScalar.rMin_eq_pow_numBits ty
  have := IScalar.rMax_eq_pow_numBits ty
  omega

theorem IScalar.hmin {ty} (x : IScalar ty) : -2^(ty.numBits - 1) ≤ x.val := x.hBounds.left
theorem IScalar.hmax {ty} (x : IScalar ty) : x.val < 2^(ty.numBits - 1) := x.hBounds.right

instance {ty} : BEq (UScalar ty) where
  beq a b := a.bv = b.bv

instance {ty} : BEq (IScalar ty) where
  beq a b := a.bv = b.bv

instance {ty} : LawfulBEq (UScalar ty) where
  eq_of_beq {a b} := by cases a; cases b; simp [BEq.beq]
  rfl {a} := by cases a; simp [BEq.beq]

instance {ty} : LawfulBEq (IScalar ty) where
  eq_of_beq {a b} := by cases a; cases b; simp[BEq.beq]
  rfl {a} := by cases a; simp [BEq.beq]

instance (ty : UScalarTy) : CoeOut (UScalar ty) Nat where
  coe := λ v => v.val

instance (ty : IScalarTy) : CoeOut (IScalar ty) Int where
  coe := λ v => v.val

attribute [coe] UScalar.val IScalar.val

theorem UScalar.bound_suffices (ty : UScalarTy) (x : Nat) :
  x ≤ UScalar.cMax ty -> x < 2^ty.numBits
  := by
  intro h
  have := UScalar.rMax_eq_pow_numBits ty
  have : 0 < 2^ty.numBits := Nat.two_pow_pos _
  have := cMax_le_rMax ty
  omega

theorem IScalar.bound_suffices (ty : IScalarTy) (x : Int) :
  IScalar.cMin ty ≤ x ∧ x ≤ IScalar.cMax ty ->
  -2^(ty.numBits - 1) ≤ x ∧ x < 2^(ty.numBits - 1)
  := by
  intro h
  have := IScalar.rMin_eq_pow_numBits ty
  have := IScalar.rMax_eq_pow_numBits ty
  have := rMin_le_cMin ty
  have := cMax_le_rMax ty
  omega

def UScalar.ofNatCore {ty : UScalarTy} (x : Nat) (h : x < 2^ty.numBits) : UScalar ty :=
  { bv := ⟨ x, h ⟩ }

def IScalar.ofIntCore {ty : IScalarTy} (x : Int)
    (_ : -2^(ty.numBits-1) ≤ x ∧ x < 2^(ty.numBits - 1)) : IScalar ty :=
  let x' := (x % 2^ty.numBits).toNat
  have h : x' < 2^ty.numBits := by
    have hpos : (0 : Int) < 2^ty.numBits := Int.pow_pos (by decide)
    have h0 := Int.emod_nonneg x (Int.ne_of_gt hpos)
    have h1 := Int.emod_lt_of_pos x hpos
    have : ((2 ^ ty.numBits : Nat) : Int) = (2 : Int) ^ ty.numBits := by simp
    simp only [x']
    omega
  { bv := ⟨ x', h ⟩ }

@[reducible] def UScalar.ofNat {ty : UScalarTy} (x : Nat)
  (hInBounds : x ≤ UScalar.cMax ty := by decide) : UScalar ty :=
  UScalar.ofNatCore x (UScalar.bound_suffices ty x hInBounds)

@[reducible] def IScalar.ofInt {ty : IScalarTy} (x : Int)
  (hInBounds : IScalar.cMin ty ≤ x ∧ x ≤ IScalar.cMax ty := by decide) : IScalar ty :=
  IScalar.ofIntCore x (IScalar.bound_suffices ty x hInBounds)

/-!
## Canonical zero and one
-/

abbrev UScalar.zero {ty : UScalarTy} : UScalar ty :=
  UScalar.ofNatCore 0 (Nat.two_pow_pos _)

abbrev UScalar.one {ty : UScalarTy} : UScalar ty := UScalar.ofNatCore 1 (by
    have := UScalarTy.numBits_nonzero ty
    have := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.one_le_iff_ne_zero.mpr this)
    simp at this; omega
  )

abbrev IScalar.zero {ty : IScalarTy} : IScalar ty := IScalar.ofIntCore 0 (by
    have : (0 : Int) < 2 ^ (ty.numBits - 1) := Int.pow_pos (by decide)
    omega)

abbrev IScalar.one {ty : IScalarTy} : IScalar ty := IScalar.ofIntCore 1
  (by
    have := IScalarTy.numBits_nonzero ty
    cases ty <;> simp [IScalarTy.numBits] at * <;>
    cases System.Platform.numBits_eq <;> simp_all)

theorem UScalar.zero_bv {ty : UScalarTy}: UScalar.zero.bv = BitVec.ofNat ty.numBits 0 := by
  simp[UScalar.zero, UScalar.ofNatCore]

theorem IScalar.zero_bv {ty : IScalarTy}: IScalar.zero.bv = BitVec.ofNat ty.numBits 0 := by
  simp[IScalar.zero, IScalar.ofIntCore]

theorem UScalar.one_bv {ty : UScalarTy}: UScalar.one.bv = BitVec.ofNat ty.numBits 1 := by
  apply BitVec.eq_of_toNat_eq
  simp [UScalar.one, UScalar.ofNatCore]
  have := UScalarTy.numBits_nonzero ty
  have := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.one_le_iff_ne_zero.mpr this)
  simp at this
  rw [Nat.mod_eq_of_lt (by omega)]

theorem IScalar.one_bv {ty : IScalarTy}: IScalar.one.bv = BitVec.ofNat ty.numBits 1 := by
  apply BitVec.eq_of_toNat_eq
  simp [IScalar.one, IScalar.ofIntCore]
  have := IScalarTy.numBits_nonzero ty
  have := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.one_le_iff_ne_zero.mpr this)
  simp at this
  rw [Nat.mod_eq_of_lt (by omega), Int.emod_eq_of_lt (by decide)]
  · rfl
  · have : ((2 ^ ty.numBits : Nat) : Int) = (2 : Int) ^ ty.numBits := by simp
    omega

@[simp] abbrev UScalar.inBounds (ty : UScalarTy) (x : Nat) : Prop :=
  x < 2^ty.numBits

@[simp] abbrev IScalar.inBounds (ty : IScalarTy) (x : Int) : Prop :=
  - 2^(ty.numBits - 1) ≤ x ∧ x < 2^(ty.numBits - 1)

@[simp] abbrev UScalar.check_bounds (ty : UScalarTy) (x : Nat) : Bool :=
  x < 2^ty.numBits

@[simp] abbrev IScalar.check_bounds (ty : IScalarTy) (x : Int) : Bool :=
  -2^(ty.numBits - 1) ≤ x ∧ x < 2^(ty.numBits - 1)

theorem UScalar.check_bounds_imp_inBounds {ty : UScalarTy} {x : Nat}
  (h: UScalar.check_bounds ty x) :
  UScalar.inBounds ty x := by
  simp at *; apply h

theorem UScalar.check_bounds_eq_inBounds (ty : UScalarTy) (x : Nat) :
  UScalar.check_bounds ty x ↔ UScalar.inBounds ty x := by
  constructor <;> intro h
  . apply (check_bounds_imp_inBounds h)
  . simp_all

theorem IScalar.check_bounds_imp_inBounds {ty : IScalarTy} {x : Int}
  (h: IScalar.check_bounds ty x) :
  IScalar.inBounds ty x := by
  simp at *; apply h

theorem IScalar.check_bounds_eq_inBounds (ty : IScalarTy) (x : Int) :
  IScalar.check_bounds ty x ↔ IScalar.inBounds ty x := by
  constructor <;> intro h
  . apply (check_bounds_imp_inBounds h)
  . simp_all

/-- `some` of the scalar with value `x` when `x` is in bounds. -/
def UScalar.tryMkOpt (ty : UScalarTy) (x : Nat) : Option (UScalar ty) :=
  if h:UScalar.check_bounds ty x then
    some (UScalar.ofNatCore x (UScalar.check_bounds_imp_inBounds h))
  else none

/-- The scalar with value `x`; a panic when `x` is out of bounds. -/
def UScalar.tryMk (ty : UScalarTy) (x : Nat) : RustM (UScalar ty) :=
  RustM.ofOption (tryMkOpt ty x) panic

/-- `some` of the scalar with value `x` when `x` is in bounds. -/
def IScalar.tryMkOpt (ty : IScalarTy) (x : Int) : Option (IScalar ty) :=
  if h:IScalar.check_bounds ty x then
    some (IScalar.ofIntCore x (IScalar.check_bounds_imp_inBounds h))
  else none

/-- The scalar with value `x`; a panic when `x` is out of bounds. -/
def IScalar.tryMk (ty : IScalarTy) (x : Int) : RustM (IScalar ty) :=
  RustM.ofOption (tryMkOpt ty x) panic

@[simp, grind =]
theorem UScalar.ofNatCore_val_eq {ty : UScalarTy} {x : Nat} (h : x < 2^ty.numBits) :
  (UScalar.ofNatCore x h).val = x := by
  simp [UScalar.ofNatCore, UScalar.val]

@[simp, grind! .]
theorem IScalar.ofInt_val_eq {ty : IScalarTy} {x : Int}
    (h : - 2^(ty.numBits - 1) ≤ x ∧ x < 2^(ty.numBits - 1)) :
  (IScalar.ofIntCore x h).val = x := by
  have hn := ty.numBits_nonzero
  simp only [IScalar.ofIntCore, IScalar.val, BitVec.toInt_eq_toNat_bmod]
  have hpos : (0 : Int) < 2^ty.numBits := Int.pow_pos (by decide)
  have h0 := Int.emod_nonneg x (Int.ne_of_gt hpos)
  simp only [BitVec.toNat_ofFin, Int.toNat_of_nonneg h0]
  rw [show (2:Int)^ty.numBits = ((2^ty.numBits : Nat) : Int) by simp, Int.emod_bmod]
  exact Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' _ _ hn h.1 h.2

theorem UScalar.tryMkOpt_eq (ty : UScalarTy) (x : Nat) :
  match tryMkOpt ty x with
  | some y => y.val = x ∧ inBounds ty x
  | none => ¬ (inBounds ty x) := by
  simp only [tryMkOpt]
  by_cases h : x < 2 ^ ty.numBits
  · simp [h]
  · simp [h]

theorem UScalar.tryMk_eq (ty : UScalarTy) (x : Nat) :
  match tryMk ty x with
  | ok y => y.val = x ∧ inBounds ty x
  | fail _ => ¬ (inBounds ty x)
  | _ => False := by
  have := UScalar.tryMkOpt_eq ty x
  simp only [tryMk, ofOption]
  cases h: tryMkOpt ty x <;> simp_all

theorem IScalar.tryMkOpt_eq (ty : IScalarTy) (x : Int) :
  match tryMkOpt ty x with
  | some y => y.val = x ∧ inBounds ty x
  | none => ¬ (inBounds ty x) := by
  simp only [tryMkOpt]
  by_cases h : -2 ^ (ty.numBits - 1) ≤ x ∧ x < 2 ^ (ty.numBits - 1)
  · simp [h]
  · simp [h]

theorem IScalar.tryMk_eq (ty : IScalarTy) (x : Int) :
  match tryMk ty x with
  | ok y => y.val = x ∧ inBounds ty x
  | fail _ => ¬ (inBounds ty x)
  | _ => False := by
  have := tryMkOpt_eq ty x
  simp only [tryMk, ofOption]
  cases h : tryMkOpt ty x <;> simp_all

@[simp] theorem UScalar.zero_in_cbounds {ty : UScalarTy} : 0 < 2^ty.numBits :=
  Nat.two_pow_pos _

@[simp] theorem IScalar.zero_in_cbounds {ty : IScalarTy} :
  -2^(ty.numBits - 1) ≤ 0 ∧ 0 < 2^(ty.numBits - 1) := by
  have : (0 : Int) < 2 ^ (ty.numBits - 1) := Int.pow_pos (by decide)
  constructor
  · omega
  · first | exact Nat.two_pow_pos _ | exact this

/-! The scalar types. -/
abbrev  Usize := UScalar .Usize
abbrev  U8    := UScalar .U8
abbrev  U16   := UScalar .U16
abbrev  U32   := UScalar .U32
abbrev  U64   := UScalar .U64
abbrev  U128  := UScalar .U128
abbrev  Isize := IScalar .Isize
abbrev  I8    := IScalar .I8
abbrev  I16   := IScalar .I16
abbrev  I32   := IScalar .I32
abbrev  I64   := IScalar .I64
abbrev  I128  := IScalar .I128

/-!  ofNatCore -/
def Usize.ofNatCore := @UScalar.ofNatCore .Usize
def U8.ofNatCore    := @UScalar.ofNatCore .U8
def U16.ofNatCore   := @UScalar.ofNatCore .U16
def U32.ofNatCore   := @UScalar.ofNatCore .U32
def U64.ofNatCore   := @UScalar.ofNatCore .U64
def U128.ofNatCore  := @UScalar.ofNatCore .U128

/-!  ofIntCore -/
def Isize.ofIntCore := @IScalar.ofIntCore .Isize
def I8.ofIntCore    := @IScalar.ofIntCore .I8
def I16.ofIntCore   := @IScalar.ofIntCore .I16
def I32.ofIntCore   := @IScalar.ofIntCore .I32
def I64.ofIntCore   := @IScalar.ofIntCore .I64
def I128.ofIntCore  := @IScalar.ofIntCore .I128

/-!  ofNat -/
abbrev Usize.ofNat := @UScalar.ofNat .Usize
abbrev U8.ofNat    := @UScalar.ofNat .U8
abbrev U16.ofNat   := @UScalar.ofNat .U16
abbrev U32.ofNat   := @UScalar.ofNat .U32
abbrev U64.ofNat   := @UScalar.ofNat .U64
abbrev U128.ofNat  := @UScalar.ofNat .U128

/-!  ofInt -/
abbrev Isize.ofInt := @IScalar.ofInt .Isize
abbrev I8.ofInt    := @IScalar.ofInt .I8
abbrev I16.ofInt   := @IScalar.ofInt .I16
abbrev I32.ofInt   := @IScalar.ofInt .I32
abbrev I64.ofInt   := @IScalar.ofInt .I64
abbrev I128.ofInt  := @IScalar.ofInt .I128

@[simp, grind =]
theorem U8.ofNatCore_val_eq {x : Nat} (h : x < 2^UScalarTy.U8.numBits) :
    (U8.ofNatCore x h).val = x := by
  apply UScalar.ofNatCore_val_eq h

@[simp, grind =]
theorem U16.ofNatCore_val_eq {x : Nat} (h : x < 2^UScalarTy.U16.numBits) :
    (U16.ofNatCore x h).val = x := by
  apply UScalar.ofNatCore_val_eq h

@[simp, grind =]
theorem U32.ofNatCore_val_eq {x : Nat} (h : x < 2^UScalarTy.U32.numBits) :
    (U32.ofNatCore x h).val = x := by
  apply UScalar.ofNatCore_val_eq h

@[simp, grind =]
theorem U64.ofNatCore_val_eq {x : Nat} (h : x < 2^UScalarTy.U64.numBits) :
    (U64.ofNatCore x h).val = x := by
  apply UScalar.ofNatCore_val_eq h

@[simp, grind =]
theorem U128.ofNatCore_val_eq {x : Nat} (h : x < 2^UScalarTy.U128.numBits) :
    (U128.ofNatCore x h).val = x := by
  apply UScalar.ofNatCore_val_eq h

@[simp, grind =]
theorem Usize.ofNatCore_val_eq {x : Nat} (h : x < 2^UScalarTy.Usize.numBits) :
    (Usize.ofNatCore x h).val = x := by
  apply UScalar.ofNatCore_val_eq h

@[simp, grind =]
theorem I8.ofInt_val_eq {x : Int}
    (h : -2^(IScalarTy.I8.numBits-1) ≤ x ∧ x < 2^(IScalarTy.I8.numBits-1)) :
    (I8.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq

@[simp, grind =]
theorem I16.ofInt_val_eq {x : Int}
    (h : -2^(IScalarTy.I16.numBits-1) ≤ x ∧ x < 2^(IScalarTy.I16.numBits-1)) :
    (I16.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq

@[simp, grind =]
theorem I32.ofInt_val_eq {x : Int}
    (h : -2^(IScalarTy.I32.numBits-1) ≤ x ∧ x < 2^(IScalarTy.I32.numBits-1)) :
    (I32.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq

@[simp, grind =]
theorem I64.ofInt_val_eq {x : Int}
    (h : -2^(IScalarTy.I64.numBits-1) ≤ x ∧ x < 2^(IScalarTy.I64.numBits-1)) :
    (I64.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq

@[simp, grind =]
theorem I128.ofInt_val_eq {x : Int}
    (h : -2^(IScalarTy.I128.numBits-1) ≤ x ∧ x < 2^(IScalarTy.I128.numBits-1)) :
    (I128.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq

@[simp, grind =]
theorem Isize.ofInt_val_eq {x : Int}
    (h : -2^(IScalarTy.Isize.numBits-1) ≤ x ∧ x < 2^(IScalarTy.Isize.numBits-1)) :
    (Isize.ofIntCore x h).val = x := by
  apply IScalar.ofInt_val_eq

theorem UScalar.eq_equiv_bv_eq {ty : UScalarTy} (x y : UScalar ty) :
  x = y ↔ x.bv = y.bv := by
  cases x; cases y; simp

theorem U8.eq_equiv_bv_eq (x y : U8) : x = y ↔ x.bv = y.bv := by apply UScalar.eq_equiv_bv_eq
theorem U16.eq_equiv_bv_eq (x y : U16) : x = y ↔ x.bv = y.bv := by apply UScalar.eq_equiv_bv_eq
theorem U32.eq_equiv_bv_eq (x y : U32) : x = y ↔ x.bv = y.bv := by apply UScalar.eq_equiv_bv_eq
theorem U64.eq_equiv_bv_eq (x y : U64) : x = y ↔ x.bv = y.bv := by apply UScalar.eq_equiv_bv_eq
theorem U128.eq_equiv_bv_eq (x y : U128) : x = y ↔ x.bv = y.bv := by
  apply UScalar.eq_equiv_bv_eq
theorem Usize.eq_equiv_bv_eq (x y : Usize) : x = y ↔ x.bv = y.bv := by
  apply UScalar.eq_equiv_bv_eq

@[ext, grind ext] theorem U8.bv_eq_imp_eq (x y : U8) : x.bv = y.bv → x = y := by
  simp [UScalar.eq_equiv_bv_eq]
@[ext, grind ext] theorem U16.bv_eq_imp_eq (x y : U16) : x.bv = y.bv → x = y := by
  simp [UScalar.eq_equiv_bv_eq]
@[ext, grind ext] theorem U32.bv_eq_imp_eq (x y : U32) : x.bv = y.bv → x = y := by
  simp [UScalar.eq_equiv_bv_eq]
@[ext, grind ext] theorem U64.bv_eq_imp_eq (x y : U64) : x.bv = y.bv → x = y := by
  simp [UScalar.eq_equiv_bv_eq]
@[ext, grind ext] theorem U128.bv_eq_imp_eq (x y : U128) : x.bv = y.bv → x = y := by
  simp [UScalar.eq_equiv_bv_eq]
@[ext, grind ext] theorem Usize.bv_eq_imp_eq (x y : Usize) : x.bv = y.bv → x = y := by
  simp [UScalar.eq_equiv_bv_eq]

theorem UScalar.ofNatCore_bv {ty : UScalarTy} (x : Nat) h :
  (@UScalar.ofNatCore ty x h).bv = BitVec.ofNat _ x := by
  apply BitVec.eq_of_toNat_eq
  simp [ofNatCore, Nat.mod_eq_of_lt h]

@[simp, grind =] theorem U8.ofNat_bv (x : Nat) h : (U8.ofNat x h).bv = BitVec.ofNat _ x := by
  apply UScalar.ofNatCore_bv
@[simp, grind =] theorem U16.ofNat_bv (x : Nat) h : (U16.ofNat x h).bv = BitVec.ofNat _ x := by
  apply UScalar.ofNatCore_bv
@[simp, grind =] theorem U32.ofNat_bv (x : Nat) h : (U32.ofNat x h).bv = BitVec.ofNat _ x := by
  apply UScalar.ofNatCore_bv
@[simp, grind =] theorem U64.ofNat_bv (x : Nat) h : (U64.ofNat x h).bv = BitVec.ofNat _ x := by
  apply UScalar.ofNatCore_bv
@[simp, grind =] theorem U128.ofNat_bv (x : Nat) h :
    (U128.ofNat x h).bv = BitVec.ofNat _ x := by
  apply UScalar.ofNatCore_bv
@[simp, grind =] theorem Usize.ofNat_bv (x : Nat) h :
    (Usize.ofNat x h).bv = BitVec.ofNat _ x := by
  apply UScalar.ofNatCore_bv

theorem IScalar.eq_equiv_bv_eq {ty : IScalarTy} (x y : IScalar ty) :
  x = y ↔ x.bv = y.bv := by
  cases x; cases y; simp

theorem I8.eq_equiv_bv_eq (x y : I8) : x = y ↔ x.bv = y.bv := by apply IScalar.eq_equiv_bv_eq
theorem I16.eq_equiv_bv_eq (x y : I16) : x = y ↔ x.bv = y.bv := by apply IScalar.eq_equiv_bv_eq
theorem I32.eq_equiv_bv_eq (x y : I32) : x = y ↔ x.bv = y.bv := by apply IScalar.eq_equiv_bv_eq
theorem I64.eq_equiv_bv_eq (x y : I64) : x = y ↔ x.bv = y.bv := by apply IScalar.eq_equiv_bv_eq
theorem I128.eq_equiv_bv_eq (x y : I128) : x = y ↔ x.bv = y.bv := by
  apply IScalar.eq_equiv_bv_eq
theorem Isize.eq_equiv_bv_eq (x y : Isize) : x = y ↔ x.bv = y.bv := by
  apply IScalar.eq_equiv_bv_eq

@[ext, grind ext] theorem I8.bv_eq_imp_eq (x y : I8) : x.bv = y.bv → x = y := by
  simp[IScalar.eq_equiv_bv_eq]
@[ext, grind ext] theorem I16.bv_eq_imp_eq (x y : I16) : x.bv = y.bv → x = y := by
  simp[IScalar.eq_equiv_bv_eq]
@[ext, grind ext] theorem I32.bv_eq_imp_eq (x y : I32) : x.bv = y.bv → x = y := by
  simp[IScalar.eq_equiv_bv_eq]
@[ext, grind ext] theorem I64.bv_eq_imp_eq (x y : I64) : x.bv = y.bv → x = y := by
  simp[IScalar.eq_equiv_bv_eq]
@[ext, grind ext] theorem I128.bv_eq_imp_eq (x y : I128) : x.bv = y.bv → x = y := by
  simp[IScalar.eq_equiv_bv_eq]
@[ext, grind ext] theorem Isize.bv_eq_imp_eq (x y : Isize) : x.bv = y.bv → x = y := by
  simp[IScalar.eq_equiv_bv_eq]

theorem IScalar.ofIntCore_bv {ty : IScalarTy} (x : Int) h :
  (@IScalar.ofIntCore ty x h).bv = BitVec.ofInt _ x := by
  apply BitVec.eq_of_toNat_eq
  simp [ofIntCore, BitVec.toNat_ofInt]

@[simp, grind =] theorem I8.ofInt_bv (x : Int) h : (I8.ofInt x h).bv = BitVec.ofInt _ x := by
  apply IScalar.ofIntCore_bv
@[simp, grind =] theorem I16.ofInt_bv (x : Int) h : (I16.ofInt x h).bv = BitVec.ofInt _ x := by
  apply IScalar.ofIntCore_bv
@[simp, grind =] theorem I32.ofInt_bv (x : Int) h : (I32.ofInt x h).bv = BitVec.ofInt _ x := by
  apply IScalar.ofIntCore_bv
@[simp, grind =] theorem I64.ofInt_bv (x : Int) h : (I64.ofInt x h).bv = BitVec.ofInt _ x := by
  apply IScalar.ofIntCore_bv
@[simp, grind =] theorem I128.ofInt_bv (x : Int) h :
    (I128.ofInt x h).bv = BitVec.ofInt _ x := by
  apply IScalar.ofIntCore_bv
@[simp, grind =] theorem Isize.ofInt_bv (x : Int) h :
    (Isize.ofInt x h).bv = BitVec.ofInt _ x := by
  apply IScalar.ofIntCore_bv

instance (ty : UScalarTy) : Inhabited (UScalar ty) := by
  constructor; cases ty <;> apply (UScalar.ofNat 0 (by simp))

instance (ty : IScalarTy) : Inhabited (IScalar ty) := by
  constructor; cases ty <;> apply (IScalar.ofInt 0 (by
    simp only [IScalar.cMin, IScalar.cMax, IScalar.rMin, IScalar.rMax]; simp_bounds))

@[simp, grind =]
theorem UScalar.default_val {ty} : (default : UScalar ty).val = 0 := by
  simp only [default]; cases ty <;> simp

@[simp, grind =]
theorem UScalar.default_bv {ty} : (default : UScalar ty).bv = 0 := by
  simp only [default]; cases ty <;> simp <;> rfl

theorem IScalar.min_lt_max (ty : IScalarTy) : IScalar.min ty < IScalar.max ty := by
  simp only [IScalar.min, IScalar.max]
  have : (0 : Int) < 2 ^ (ty.numBits - 1) := Int.pow_pos (by decide)
  omega

theorem IScalar.min_le_max (ty : IScalarTy) : IScalar.min ty ≤ IScalar.max ty := by
  have := IScalar.min_lt_max ty
  omega

@[reducible] def core.num.U8.MIN : U8 := UScalar.ofNat 0
@[reducible] def core.num.U8.MAX : U8 := UScalar.ofNat U8.rMax
@[reducible] def core.num.U16.MIN : U16 := UScalar.ofNat 0
@[reducible] def core.num.U16.MAX : U16 := UScalar.ofNat U16.rMax
@[reducible] def core.num.U32.MIN : U32 := UScalar.ofNat 0
@[reducible] def core.num.U32.MAX : U32 := UScalar.ofNat U32.rMax
@[reducible] def core.num.U64.MIN : U64 := UScalar.ofNat 0
@[reducible] def core.num.U64.MAX : U64 := UScalar.ofNat U64.rMax
@[reducible] def core.num.U128.MIN : U128 := UScalar.ofNat 0
@[reducible] def core.num.U128.MAX : U128 := UScalar.ofNat U128.rMax
@[reducible] def core.num.Usize.MIN : Usize :=
  UScalar.ofNatCore 0 (Nat.two_pow_pos _)
@[reducible] def core.num.Usize.MAX : Usize := UScalar.ofNatCore Usize.max (by
  simp only [Usize.max, Usize.numBits]
  have : 0 < 2 ^ UScalarTy.Usize.numBits := Nat.two_pow_pos _
  omega)

@[reducible] def core.num.I8.MIN : I8 := IScalar.ofInt I8.rMin
@[reducible] def core.num.I8.MAX : I8 := IScalar.ofInt I8.rMax
@[reducible] def core.num.I16.MIN : I16 := IScalar.ofInt I16.rMin
@[reducible] def core.num.I16.MAX : I16 := IScalar.ofInt I16.rMax
@[reducible] def core.num.I32.MIN : I32 := IScalar.ofInt I32.rMin
@[reducible] def core.num.I32.MAX : I32 := IScalar.ofInt I32.rMax
@[reducible] def core.num.I64.MIN : I64 := IScalar.ofInt I64.rMin
@[reducible] def core.num.I64.MAX : I64 := IScalar.ofInt I64.rMax
@[reducible] def core.num.I128.MIN : I128 := IScalar.ofInt I128.rMin
@[reducible] def core.num.I128.MAX : I128 := IScalar.ofInt I128.rMax
@[reducible] def core.num.Isize.MIN : Isize := IScalar.ofIntCore Isize.min (by
  simp only [Isize.min, Isize.numBits]
  have : (0 : Int) < 2 ^ (IScalarTy.Isize.numBits - 1) := Int.pow_pos (by decide)
  omega)
@[reducible] def core.num.Isize.MAX : Isize := IScalar.ofIntCore Isize.max (by
  simp only [Isize.max, Isize.numBits]
  have : (0 : Int) < 2 ^ (IScalarTy.Isize.numBits - 1) := Int.pow_pos (by decide)
  omega)

@[reducible] def core.num.U8.BITS : U32 := UScalar.ofNat (UScalarTy.numBits .U8)
@[reducible] def core.num.U16.BITS : U32 := UScalar.ofNat (UScalarTy.numBits .U16)
@[reducible] def core.num.U32.BITS : U32 := UScalar.ofNat (UScalarTy.numBits .U32)
@[reducible] def core.num.U64.BITS : U32 := UScalar.ofNat (UScalarTy.numBits .U64)
@[reducible] def core.num.U128.BITS : U32 := UScalar.ofNat (UScalarTy.numBits .U128)
@[reducible] def core.num.Usize.BITS : U32 := UScalar.ofNat (UScalarTy.numBits .Usize) (by
  simp only [UScalar.cMax, UScalar.rMax, U32.rMax, UScalarTy.numBits]
  cases System.Platform.numBits_eq <;> simp_all)
@[reducible] def core.num.I8.BITS : U32 := UScalar.ofNat (IScalarTy.numBits .I8)
@[reducible] def core.num.I16.BITS : U32 := UScalar.ofNat (IScalarTy.numBits .I16)
@[reducible] def core.num.I32.BITS : U32 := UScalar.ofNat (IScalarTy.numBits .I32)
@[reducible] def core.num.I64.BITS : U32 := UScalar.ofNat (IScalarTy.numBits .I64)
@[reducible] def core.num.I128.BITS : U32 := UScalar.ofNat (IScalarTy.numBits .I128)
@[reducible] def core.num.Isize.BITS : U32 := UScalar.ofNat (IScalarTy.numBits .Isize) (by
  simp only [UScalar.cMax, UScalar.rMax, U32.rMax, IScalarTy.numBits]
  cases System.Platform.numBits_eq <;> simp_all)

/-! # Comparisons -/
instance {ty} : LT (UScalar ty) where
  lt a b := LT.lt a.val b.val

instance {ty} : LE (UScalar ty) where le a b := LE.le a.val b.val

instance {ty} : LT (IScalar ty) where
  lt a b := LT.lt a.val b.val

instance {ty} : LE (IScalar ty) where le a b := LE.le a.val b.val

theorem UScalar.eq_equiv {ty : UScalarTy} (x y : UScalar ty) :
  x = y ↔ (↑x : Nat) = ↑y := by
  cases x; cases y; simp_all [UScalar.val, BitVec.toNat_eq]

@[ext, grind ext] theorem UScalar.val_eq_imp {ty : UScalarTy} (x y : UScalar ty) :
  (↑x : Nat) = ↑y → x = y := by
  simp [eq_equiv]

theorem UScalar.eq_imp {ty : UScalarTy} (x y : UScalar ty) :
  (↑x : Nat) = ↑y → x = y := (eq_equiv x y).mpr

@[simp, grind =] theorem UScalar.lt_equiv {ty : UScalarTy} (x y : UScalar ty) :
  x < y ↔ (↑x : Nat) < ↑y := by
  rw [LT.lt, instLTUScalar]

@[simp] theorem UScalar.lt_imp {ty : UScalarTy} (x y : UScalar ty) :
  (↑x : Nat) < (↑y) → x < y := (lt_equiv x y).mpr

@[simp, grind =] theorem UScalar.le_equiv {ty : UScalarTy} (x y : UScalar ty) :
  x ≤ y ↔ (↑x : Nat) ≤ ↑y := by
  rw [LE.le, instLEUScalar]

@[simp] theorem UScalar.le_imp {ty : UScalarTy} (x y : UScalar ty) :
  (↑x : Nat) ≤ ↑y → x ≤ y := (le_equiv x y).mpr

theorem IScalar.eq_equiv {ty : IScalarTy} (x y : IScalar ty) :
  x = y ↔ (↑x : Int) = ↑y := by
  cases x; cases y; simp_all [IScalar.val]
  constructor <;> intro h
  · simp [h]
  · exact BitVec.eq_of_toInt_eq h

@[ext, grind ext] theorem IScalar.val_eq_imp {ty : IScalarTy} (x y : IScalar ty) :
  (↑x : Int) = ↑y → x = y := by
  simp [eq_equiv]

theorem IScalar.eq_imp {ty : IScalarTy} (x y : IScalar ty) :
  (↑x : Int) = ↑y → x = y := (eq_equiv x y).mpr

@[simp, grind =] theorem IScalar.lt_equiv {ty : IScalarTy} (x y : IScalar ty) :
  x < y ↔ (↑x : Int) < ↑y := by
  rw [LT.lt, instLTIScalar]

@[simp] theorem IScalar.lt_imp {ty : IScalarTy} (x y : IScalar ty) :
  (↑x : Int) < (↑y) → x < y := (lt_equiv x y).mpr

@[simp, grind =] theorem IScalar.le_equiv {ty : IScalarTy} (x y : IScalar ty) :
  x ≤ y ↔ (↑x : Int) ≤ ↑y := by simp [LE.le]

@[simp] theorem IScalar.le_imp {ty : IScalarTy} (x y : IScalar ty) :
  (↑x : Int) ≤ ↑y → x ≤ y := (le_equiv x y).mpr

instance UScalar.decLt {ty} (a b : UScalar ty) : Decidable (LT.lt a b) := Nat.decLt ..
instance UScalar.decLe {ty} (a b : UScalar ty) : Decidable (LE.le a b) := Nat.decLe ..
instance IScalar.decLt {ty} (a b : IScalar ty) : Decidable (LT.lt a b) := Int.decLt ..
instance IScalar.decLe {ty} (a b : IScalar ty) : Decidable (LE.le a b) := Int.decLe ..

theorem UScalar.eq_of_val_eq {ty} : ∀ {i j : UScalar ty}, Eq i.val j.val → Eq i j := by
  intro i j h
  exact (UScalar.eq_equiv i j).mpr h

theorem IScalar.eq_of_val_eq {ty} : ∀ {i j : IScalar ty}, Eq i.val j.val → Eq i j := by
  intro i j hEq
  cases i; cases j
  simp [IScalar.val] at hEq; simp
  apply BitVec.eq_of_toInt_eq; assumption

theorem UScalar.val_eq_of_eq {ty} {i j : UScalar ty} (h : Eq i j) : Eq i.val j.val := h ▸ rfl
theorem IScalar.val_eq_of_eq {ty} {i j : IScalar ty} (h : Eq i j) : Eq i.val j.val := h ▸ rfl

theorem UScalar.ne_of_val_ne {ty} {i j : UScalar ty} (h : Not (Eq i.val j.val)) :
    Not (Eq i j) :=
  fun h' => absurd (val_eq_of_eq h') h

theorem IScalar.ne_of_val_ne {ty} {i j : IScalar ty} (h : Not (Eq i.val j.val)) :
    Not (Eq i j) :=
  fun h' => absurd (val_eq_of_eq h') h

instance (ty : UScalarTy) : DecidableEq (UScalar ty) :=
  fun i j =>
    match decEq i.val j.val with
    | isTrue h  => isTrue (UScalar.eq_of_val_eq h)
    | isFalse h => isFalse (UScalar.ne_of_val_ne h)

instance (ty : IScalarTy) : DecidableEq (IScalar ty) :=
  fun i j =>
    match decEq i.val j.val with
    | isTrue h  => isTrue (IScalar.eq_of_val_eq h)
    | isFalse h => isFalse (IScalar.ne_of_val_ne h)

@[simp]
theorem UScalar.neq_to_neq_val {ty} :
  ∀ {i j : UScalar ty}, (¬ i = j) ↔ ¬ i.val = j.val := by
  simp [eq_equiv]

@[simp]
theorem IScalar.neq_to_neq_val {ty} :
  ∀ {i j : IScalar ty}, (¬ i = j) ↔ ¬ i.val = j.val := by
  simp [eq_equiv]

theorem UScalar.zero_le {ty} (x: UScalar ty) : UScalar.ofNat 0 (by simp) ≤ x := by
  simp [UScalar.ofNat]

/-! Conversions -/
@[simp, grind] abbrev IScalar.toNat {ty} (x : IScalar ty) : Nat := x.val.toNat
@[simp, grind] abbrev I8.toNat      (x : I8) : Nat := x.val.toNat
@[simp, grind] abbrev I16.toNat     (x : I16) : Nat := x.val.toNat
@[simp, grind] abbrev I32.toNat     (x : I32) : Nat := x.val.toNat
@[simp, grind] abbrev I64.toNat     (x : I64) : Nat := x.val.toNat
@[simp, grind] abbrev I128.toNat    (x : I128) : Nat := x.val.toNat
@[simp, grind] abbrev Isize.toNat   (x : Isize) : Nat := x.val.toNat

abbrev U8.bv (x : U8)   : BitVec 8 := UScalar.bv x
abbrev U16.bv (x : U16) : BitVec 16 := UScalar.bv x
abbrev U32.bv (x : U32) : BitVec 32 := UScalar.bv x
abbrev U64.bv (x : U64) : BitVec 64 := UScalar.bv x
abbrev U128.bv (x : U128) : BitVec 128 := UScalar.bv x
abbrev Usize.bv (x : Usize) : BitVec System.Platform.numBits := UScalar.bv x

abbrev I8.bv (x : I8) : BitVec 8 := IScalar.bv x
abbrev I16.bv (x : I16) : BitVec 16 := IScalar.bv x
abbrev I32.bv (x : I32) : BitVec 32 := IScalar.bv x
abbrev I64.bv (x : I64) : BitVec 64 := IScalar.bv x
abbrev I128.bv (x : I128) : BitVec 128 := IScalar.bv x
abbrev Isize.bv (x : Isize) : BitVec System.Platform.numBits := IScalar.bv x

@[simp, grind =] theorem UScalar.bv_toNat {ty : UScalarTy} (x : UScalar ty) :
  (UScalar.bv x).toNat  = x.val := by
  simp [val]

@[simp, grind =] theorem U8.bv_toNat (x : U8) : x.bv.toNat = x.val := by apply UScalar.bv_toNat
@[simp, grind =] theorem U16.bv_toNat (x : U16) : x.bv.toNat = x.val := by apply UScalar.bv_toNat
@[simp, grind =] theorem U32.bv_toNat (x : U32) : x.bv.toNat = x.val := by apply UScalar.bv_toNat
@[simp, grind =] theorem U64.bv_toNat (x : U64) : x.bv.toNat = x.val := by apply UScalar.bv_toNat
@[simp, grind =] theorem U128.bv_toNat (x : U128) : x.bv.toNat = x.val := by
  apply UScalar.bv_toNat
@[simp, grind =] theorem Usize.bv_toNat (x : Usize) : x.bv.toNat = x.val := by
  apply UScalar.bv_toNat

@[simp, grind =] theorem IScalar.bv_toInt_eq {ty : IScalarTy} (x : IScalar ty) :
  (IScalar.bv x).toInt  = x.val := by
  simp [val]

@[simp, grind =] theorem I8.bv_toInt_eq (x : I8) : x.bv.toInt = x.val := by
  apply IScalar.bv_toInt_eq
@[simp, grind =] theorem I16.bv_toInt_eq (x : I16) : x.bv.toInt = x.val := by
  apply IScalar.bv_toInt_eq
@[simp, grind =] theorem I32.bv_toInt_eq (x : I32) : x.bv.toInt = x.val := by
  apply IScalar.bv_toInt_eq
@[simp, grind =] theorem I64.bv_toInt_eq (x : I64) : x.bv.toInt = x.val := by
  apply IScalar.bv_toInt_eq
@[simp, grind =] theorem I128.bv_toInt_eq (x : I128) : x.bv.toInt = x.val := by
  apply IScalar.bv_toInt_eq
@[simp, grind =] theorem Isize.bv_toInt_eq (x : Isize) : x.bv.toInt = x.val := by
  apply IScalar.bv_toInt_eq

theorem U8.lt_succ_max (x: U8) : x.val < 256 := by have := x.hBounds; simp at this; omega
theorem U16.lt_succ_max (x: U16) : x.val < 65536 := by have := x.hBounds; simp at this; omega
theorem U32.lt_succ_max (x: U32) : x.val < 4294967296 := by
  have := x.hBounds; simp at this; omega
theorem U64.lt_succ_max (x: U64) : x.val < 18446744073709551616 := by
  have := x.hBounds; simp at this; omega
theorem U128.lt_succ_max (x: U128) : x.val < 340282366920938463463374607431768211456 := by
  have := x.hBounds; simp at this; omega

theorem U8.le_max (x: U8) : x.val ≤ 255 := by have := x.hBounds; simp at this; omega
theorem U16.le_max (x: U16) : x.val ≤ 65535 := by have := x.hBounds; simp at this; omega
theorem U32.le_max (x: U32) : x.val ≤ 4294967295 := by have := x.hBounds; simp at this; omega
theorem U64.le_max (x: U64) : x.val ≤ 18446744073709551615 := by
  have := x.hBounds; simp at this; omega
theorem U128.le_max (x: U128) : x.val ≤ 340282366920938463463374607431768211455 := by
  have := x.hBounds; simp at this; omega

@[simp, grind =]
theorem UScalar.ofNat_self_val {ty} (x : UScalar ty) (hInBounds : x.val ≤ UScalar.cMax ty) :
  UScalar.ofNat x hInBounds = x := by
  apply UScalar.eq_imp; simp [UScalar.ofNat]

@[simp, grind =]
theorem IScalar.ofInt_val {ty} (x : IScalar ty)
    (hInBounds : IScalar.cMin ty ≤ x.val ∧ x.val ≤ IScalar.cMax ty) :
  IScalar.ofInt x hInBounds = x := by
  apply IScalar.eq_imp; simp [IScalar.ofInt]

@[simp] theorem UScalar.BitVec_ofNat_val {ty} (x : UScalar ty) :
    BitVec.ofNat ty.numBits x.val = x.bv := by
  cases x; simp only [val, BitVec.ofNat_toNat, BitVec.setWidth_eq]

@[simp] theorem U8.BitVec_ofNat_val (x : U8) : BitVec.ofNat 8 x.val = x.bv := by
  apply UScalar.BitVec_ofNat_val
@[simp] theorem U16.BitVec_ofNat_val (x : U16) : BitVec.ofNat 16 x.val = x.bv := by
  apply UScalar.BitVec_ofNat_val
@[simp] theorem U32.BitVec_ofNat_val (x : U32) : BitVec.ofNat 32 x.val = x.bv := by
  apply UScalar.BitVec_ofNat_val
@[simp] theorem U64.BitVec_ofNat_val (x : U64) : BitVec.ofNat 64 x.val = x.bv := by
  apply UScalar.BitVec_ofNat_val
@[simp] theorem U128.BitVec_ofNat_val (x : U128) : BitVec.ofNat 128 x.val = x.bv := by
  apply UScalar.BitVec_ofNat_val
@[simp] theorem Usize.BitVec_ofNat_val (x : Usize) :
    BitVec.ofNat System.Platform.numBits x.val = x.bv := by
  apply UScalar.BitVec_ofNat_val

@[simp]
theorem IScalar.BitVec_ofInt_val {ty} (x : IScalar ty) : BitVec.ofInt ty.numBits x.val = x.bv := by
  cases x; simp only [IScalar.val, BitVec.ofInt_toInt]

@[simp] theorem I8.BitVec_ofInt_val (x : I8) : BitVec.ofInt 8 x.val = x.bv :=
  IScalar.BitVec_ofInt_val x
@[simp] theorem I16.BitVec_ofInt_val (x : I16) : BitVec.ofInt 16 x.val = x.bv :=
  IScalar.BitVec_ofInt_val x
@[simp] theorem I32.BitVec_ofInt_val (x : I32) : BitVec.ofInt 32 x.val = x.bv :=
  IScalar.BitVec_ofInt_val x
@[simp] theorem I64.BitVec_ofInt_val (x : I64) : BitVec.ofInt 64 x.val = x.bv :=
  IScalar.BitVec_ofInt_val x
@[simp] theorem I128.BitVec_ofInt_val (x : I128) : BitVec.ofInt 128 x.val = x.bv :=
  IScalar.BitVec_ofInt_val x
@[simp] theorem Isize.BitVec_ofInt_val (x : Isize) :
    BitVec.ofInt System.Platform.numBits x.val = x.bv :=
  IScalar.BitVec_ofInt_val x

@[simp]
theorem UScalar.Nat_cast_BitVec_val {ty} (x : UScalar ty) : Nat.cast x.val = x.bv := by
  simp only [BitVec.natCast_eq_ofNat, UScalar.BitVec_ofNat_val]

@[simp] theorem U8.Nat_cast_BitVec_val (x : U8) : Nat.cast x.val = x.bv :=
  UScalar.Nat_cast_BitVec_val x
@[simp] theorem U16.Nat_cast_BitVec_val (x : U16) : Nat.cast x.val = x.bv :=
  UScalar.Nat_cast_BitVec_val x
@[simp] theorem U32.Nat_cast_BitVec_val (x : U32) : Nat.cast x.val = x.bv :=
  UScalar.Nat_cast_BitVec_val x
@[simp] theorem U64.Nat_cast_BitVec_val (x : U64) : Nat.cast x.val = x.bv :=
  UScalar.Nat_cast_BitVec_val x
@[simp] theorem U128.Nat_cast_BitVec_val (x : U128) : Nat.cast x.val = x.bv :=
  UScalar.Nat_cast_BitVec_val x
@[simp] theorem Usize.Nat_cast_BitVec_val (x : Usize) : Nat.cast x.val = x.bv :=
  UScalar.Nat_cast_BitVec_val x

@[simp]
theorem IScalar.Nat_cast_BitVec_val {ty} (x : IScalar ty) : Int.cast x.val = x.bv := by
  simp only [Int.cast, IntCast.intCast, BitVec_ofInt_val]

@[simp] theorem I8.Nat_cast_BitVec_val (x : I8) : Int.cast x.val = x.bv :=
  IScalar.Nat_cast_BitVec_val x
@[simp] theorem I16.Nat_cast_BitVec_val (x : I16) : Int.cast x.val = x.bv :=
  IScalar.Nat_cast_BitVec_val x
@[simp] theorem I32.Nat_cast_BitVec_val (x : I32) : Int.cast x.val = x.bv :=
  IScalar.Nat_cast_BitVec_val x
@[simp] theorem I64.Nat_cast_BitVec_val (x : I64) : Int.cast x.val = x.bv :=
  IScalar.Nat_cast_BitVec_val x
@[simp] theorem I128.Nat_cast_BitVec_val (x : I128) : Int.cast x.val = x.bv :=
  IScalar.Nat_cast_BitVec_val x
@[simp] theorem Isize.Nat_cast_BitVec_val (x : Isize) : Int.cast x.val = x.bv :=
  IScalar.Nat_cast_BitVec_val x

@[simp] theorem UScalar.size_UScalarTyU8 : UScalar.size .U8 = U8.size := by simp_bounds
@[simp] theorem UScalar.size_UScalarTyU16 : UScalar.size .U16 = U16.size := by simp_bounds
@[simp] theorem UScalar.size_UScalarTyU32 : UScalar.size .U32 = U32.size := by simp_bounds
@[simp] theorem UScalar.size_UScalarTyU64 : UScalar.size .U64 = U64.size := by simp_bounds
@[simp] theorem UScalar.size_UScalarTyU128 : UScalar.size .U128 = U128.size := by simp_bounds
@[simp] theorem UScalar.size_UScalarTyUsize : UScalar.size .Usize = Usize.size := by simp_bounds

@[simp] theorem IScalar.size_IScalarTyI8 : IScalar.size .I8 = I8.size := by simp_bounds
@[simp] theorem IScalar.size_IScalarTyI16 : IScalar.size .I16 = I16.size := by simp_bounds
@[simp] theorem IScalar.size_IScalarTyI32 : IScalar.size .I32 = I32.size := by simp_bounds
@[simp] theorem IScalar.size_IScalarTyI64 : IScalar.size .I64 = I64.size := by simp_bounds
@[simp] theorem IScalar.size_IScalarTyI128 : IScalar.size .I128 = I128.size := by simp_bounds
@[simp] theorem IScalar.size_IScalarTyIsize : IScalar.size .Isize = Isize.size := by simp_bounds

@[simp↓]
theorem UScalar.bv_mk {ty} : (@UScalar.bv ty) ∘ UScalar.mk = id := by rfl

@[simp↓]
theorem UScalar.bv_mk_apply {ty : UScalarTy} (x : BitVec ty.numBits) :
    (UScalar.mk x).bv = x := rfl

@[simp↓] theorem U8.bv_UScalar_mk : U8.bv ∘ UScalar.mk = id := by rfl
@[simp↓] theorem U16.bv_UScalar_mk : U16.bv ∘ UScalar.mk = id := by rfl
@[simp↓] theorem U32.bv_UScalar_mk : U32.bv ∘ UScalar.mk = id := by rfl
@[simp↓] theorem U64.bv_UScalar_mk : U64.bv ∘ UScalar.mk = id := by rfl
@[simp↓] theorem U128.bv_UScalar_mk : U128.bv ∘ UScalar.mk = id := by rfl
@[simp↓] theorem Usize.bv_UScalar_mk : Usize.bv ∘ UScalar.mk = id := by rfl

@[simp↓]
theorem IScalar.bv_mk {ty} : (@UScalar.bv ty) ∘ UScalar.mk = id := by rfl

@[simp↓]
theorem IScalar.bv_mk_apply {ty : IScalarTy} (x : BitVec ty.numBits) :
    (IScalar.mk x).bv = x := rfl

@[simp↓] theorem I8.bv_IScalar_mk : I8.bv ∘ IScalar.mk = id := by rfl
@[simp↓] theorem I16.bv_IScalar_mk : I16.bv ∘ IScalar.mk = id := by rfl
@[simp↓] theorem I32.bv_IScalar_mk : I32.bv ∘ IScalar.mk = id := by rfl
@[simp↓] theorem I64.bv_IScalar_mk : I64.bv ∘ IScalar.mk = id := by rfl
@[simp↓] theorem I128.bv_IScalar_mk : I128.bv ∘ IScalar.mk = id := by rfl
@[simp↓] theorem Isize.bv_IScalar_mk : Isize.bv ∘ IScalar.mk = id := by rfl

end Std

end Aeneas

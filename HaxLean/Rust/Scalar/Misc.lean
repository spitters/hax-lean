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
  backends/lean/Aeneas/Std/Scalar/Misc.lean
-/

module

public import HaxLean.Rust.Scalar.Core

/-!
# Scalar lemmas

The balanced modulus of a signed value at its own width, and the reduction of an
unsigned value modulo its size.
-/

@[expose] public section

set_option autoImplicit false

namespace Aeneas.Std

open RustM Error Arith

/-- `Int.bmod x (2^ty.numBits) = x` for `x` in the bounds of `ty`. -/
theorem bmod_pow_numBits_eq_of_lt (ty : IScalarTy) (x : Int)
  (h0 : - 2 ^ (ty.numBits-1) ≤ x) (h1 : x < 2 ^ (ty.numBits -1)) :
  Int.bmod x (2^ty.numBits) = x :=
  Int.bmod_pow2_eq_of_inBounds' _ x ty.numBits_nonzero h0 h1

theorem UScalar.ofNatCore_bv_lt_equiv {ty} (x y : Nat) (hx) (hy) :
  (@UScalar.ofNatCore ty x hx).bv < (@UScalar.ofNatCore ty y hy).bv ↔ x < y := by
  simp only [ofNatCore, BitVec.lt_def, BitVec.toNat_ofFin]

@[simp] theorem U8.val_mod_size_eq (x : U8) : x.val % U8.size = x.val := by
  apply Nat.mod_eq_of_lt; simpa [U8.size, U8.numBits] using x.hBounds
@[simp] theorem U8.val_mod_size_eq' (x : U8) : x.val % 256 = x.val := by
  apply Nat.mod_eq_of_lt; simpa using x.hBounds
@[simp] theorem U16.val_mod_size_eq (x : U16) : x.val % U16.size = x.val := by
  apply Nat.mod_eq_of_lt; simpa [U16.size, U16.numBits] using x.hBounds
@[simp] theorem U16.val_mod_size_eq' (x : U16) : x.val % 65536 = x.val := by
  apply Nat.mod_eq_of_lt; simpa using x.hBounds
@[simp] theorem U32.val_mod_size_eq (x : U32) : x.val % U32.size = x.val := by
  apply Nat.mod_eq_of_lt; simpa [U32.size, U32.numBits] using x.hBounds
@[simp] theorem U32.val_mod_size_eq' (x : U32) : x.val % 4294967296 = x.val := by
  apply Nat.mod_eq_of_lt; simpa using x.hBounds
@[simp] theorem U64.val_mod_size_eq (x : U64) : x.val % U64.size = x.val := by
  apply Nat.mod_eq_of_lt; simpa [U64.size, U64.numBits] using x.hBounds
@[simp] theorem U64.val_mod_size_eq' (x : U64) : x.val % 18446744073709551616 = x.val := by
  apply Nat.mod_eq_of_lt; simpa using x.hBounds
@[simp] theorem U128.val_mod_size_eq (x : U128) : x.val % U128.size = x.val := by
  apply Nat.mod_eq_of_lt; simpa [U128.size, U128.numBits] using x.hBounds
@[simp] theorem U128.val_mod_size_eq' (x : U128) :
    x.val % 340282366920938463463374607431768211456 = x.val := by
  apply Nat.mod_eq_of_lt; simpa using x.hBounds
@[simp] theorem Usize.val_mod_size_eq (x : Usize) : x.val % Usize.size = x.val := by
  apply Nat.mod_eq_of_lt; simpa [Usize.size, Usize.numBits] using x.hBounds

end Aeneas.Std

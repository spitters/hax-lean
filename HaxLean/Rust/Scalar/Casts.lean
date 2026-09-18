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
  backends/lean/Aeneas/Std/Scalar/Casts.lean
-/

module

public import HaxLean.Rust.Scalar.Core

/-!
# Casts

Unsigned sources are truncated or zero-extended, signed sources truncated or sign-extended
(the Rust reference, "Semantics" of numeric casts). Casts never fail.
-/

@[expose] public section

set_option autoImplicit false

namespace Aeneas.Std

open RustM Error Arith WP

/-- When casting between unsigned integers, we truncate or **zero**-extend the integer. -/
def UScalar.cast {src_ty : UScalarTy} (tgt_ty : UScalarTy) (x : UScalar src_ty) :
    UScalar tgt_ty :=
  ⟨ x.bv.zeroExtend tgt_ty.numBits ⟩

/-- Unsigned to signed: truncate or **zero**-extend. -/
def UScalar.hcast {src_ty : UScalarTy} (tgt_ty : IScalarTy) (x : UScalar src_ty) :
    IScalar tgt_ty :=
  ⟨ x.bv.zeroExtend tgt_ty.numBits ⟩

/-- When casting between signed integers, we truncate or **sign**-extend. -/
def IScalar.cast {src_ty : IScalarTy} (tgt_ty : IScalarTy) (x : IScalar src_ty) :
    IScalar tgt_ty :=
  ⟨ x.bv.signExtend tgt_ty.numBits ⟩

/-- Signed to unsigned: truncate or **sign**-extend. -/
def IScalar.hcast {src_ty : IScalarTy} (tgt_ty : UScalarTy) (x : IScalar src_ty) :
    UScalar tgt_ty :=
  ⟨ x.bv.signExtend tgt_ty.numBits ⟩

/-- `b as uN`: `1` or `0`. -/
def UScalar.cast_fromBool (ty : UScalarTy) (x : Bool) : UScalar ty :=
  if x then ⟨ 1#ty.numBits ⟩ else ⟨ 0#ty.numBits ⟩

/-- `b as iN`: `1` or `0`. -/
def IScalar.cast_fromBool (ty : IScalarTy) (x : Bool) : IScalar ty :=
  if x then ⟨ 1#ty.numBits ⟩ else ⟨ 0#ty.numBits ⟩

theorem UScalar.cast_inBounds_spec {src_ty : UScalarTy}
  (tgt_ty : UScalarTy) (x : UScalar src_ty) (h : x.val ≤ UScalar.max tgt_ty) :
  lift (UScalar.cast tgt_ty x) ⦃ y => y.val = x.val ⦄ := by
  simp only [lift, cast, BitVec.zeroExtend_eq_setWidth, WP.spec_ok]
  have : 0 < 2^tgt_ty.numBits := Nat.two_pow_pos _
  simp only [max] at h
  show (BitVec.setWidth tgt_ty.numBits x.bv).toNat = x.bv.toNat
  rw [BitVec.toNat_setWidth]
  apply Nat.mod_eq_of_lt
  change x.val < _
  omega

theorem UScalar.hcast_inBounds_spec {src_ty : UScalarTy}
  (tgt_ty : IScalarTy) (x : UScalar src_ty)
  (h : x.val ≤ IScalar.max tgt_ty) :
  lift (UScalar.hcast tgt_ty x) ⦃ y => y.val = x.val ⦄ := by
  simp only [lift, hcast, BitVec.zeroExtend_eq_setWidth, WP.spec_ok]
  simp only [IScalar.max] at h
  show (BitVec.setWidth tgt_ty.numBits x.bv).toInt = ((x.bv.toNat : Nat) : Int)
  rw [BitVec.toInt_setWidth]
  apply Int.bmod_pow2_eq_of_inBounds' _ _ tgt_ty.numBits_nonzero
  · have : (0 : Int) ≤ 2 ^ (tgt_ty.numBits - 1) := Int.le_of_lt (Int.pow_pos (by decide))
    omega
  · change ((x.val : Nat) : Int) < _
    omega

theorem IScalar.cast_inBounds_spec {src_ty : IScalarTy}
  (tgt_ty : IScalarTy) (x : IScalar src_ty)
  (h : IScalar.min tgt_ty ≤ x.val ∧ x.val ≤ IScalar.max tgt_ty) :
  lift (IScalar.cast tgt_ty x) ⦃ y => y.val = x.val ⦄ := by
  simp only [lift, cast, WP.spec_ok]
  simp only [min, max] at h
  show (BitVec.signExtend tgt_ty.numBits x.bv).toInt = x.bv.toInt
  rw [BitVec.signExtend, BitVec.toInt_ofInt]
  change x.val.bmod _ = x.val
  apply Int.bmod_pow2_eq_of_inBounds' _ _ tgt_ty.numBits_nonzero <;> omega

theorem IScalar.hcast_inBounds_spec {src_ty : IScalarTy}
  (tgt_ty : UScalarTy) (x : IScalar src_ty) (h : 0 ≤ x.val ∧ x.val ≤ UScalar.max tgt_ty) :
  lift (IScalar.hcast tgt_ty x) ⦃ y => y.val = x.val ⦄ := by
  simp only [lift, hcast, WP.spec_ok]
  simp only [UScalar.max] at h
  show (((BitVec.signExtend tgt_ty.numBits x.bv).toNat : Nat) : Int) = x.bv.toInt
  rw [BitVec.signExtend, BitVec.toNat_ofInt]
  change (((x.val % ((2 ^ tgt_ty.numBits : Nat) : Int)).toNat : Nat) : Int) = x.val
  have hpos : 0 < 2 ^ tgt_ty.numBits := Nat.two_pow_pos _
  have hc : ((2 ^ tgt_ty.numBits - 1 : Nat) : Int) = ((2 ^ tgt_ty.numBits : Nat) : Int) - 1 := by
    omega
  rw [Int.emod_eq_of_lt h.1 (by omega), Int.toNat_of_nonneg h.1]

@[simp]
theorem UScalar.cast_fromBool_val_eq ty (b : Bool) :
    (UScalar.cast_fromBool ty b).val = b.toNat := by
  have := UScalarTy.numBits_nonzero ty
  have : 1 < 2 ^ ty.numBits := Nat.one_lt_two_pow this
  cases b
  · rfl
  · show (1#ty.numBits).toNat = 1
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt this

@[simp]
theorem IScalar.cast_fromBool_val_eq ty (b : Bool) :
    (IScalar.cast_fromBool ty b).val = b.toInt := by
  have hn := IScalarTy.numBits_nonzero ty
  have h8 : 8 ≤ ty.numBits := by
    cases ty <;> simp [IScalarTy.numBits]
  have hp : (2 : Int) ≤ 2 ^ (ty.numBits - 1) := by
    have e : ty.numBits - 1 = (ty.numBits - 2) + 1 := by omega
    rw [e, Int.pow_succ]
    have : (0:Int) < 2 ^ (ty.numBits - 2) := Int.pow_pos (by decide)
    omega
  cases b
  · show (0#ty.numBits).toInt = 0
    simp
  · show (1#ty.numBits).toInt = 1
    rw [BitVec.toInt_ofNat', Int.bmod_pow2_eq_of_inBounds' _ _ hn] <;> omega

theorem UScalar.cast_fromBool_bound_eq ty (b : Bool) : (UScalar.cast_fromBool ty b).val ≤ 1 := by
  rw [UScalar.cast_fromBool_val_eq]; cases b <;> decide

theorem IScalar.cast_fromBool_bound_eq ty (b : Bool) :
  0 ≤ (IScalar.cast_fromBool ty b).val ∧ (IScalar.cast_fromBool ty b).val ≤ 1 := by
  rw [IScalar.cast_fromBool_val_eq]; cases b <;> decide

theorem UScalar.cast_val_eq {src_ty : UScalarTy} (tgt_ty : UScalarTy) (x : UScalar src_ty) :
  (cast tgt_ty x).val = x.val % 2^(tgt_ty.numBits) := by
  show (x.bv.zeroExtend tgt_ty.numBits).toNat = x.bv.toNat % 2^(tgt_ty.numBits)
  rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]

theorem UScalar.cast_val_mod_pow_greater_numBits_eq {src_ty : UScalarTy} (tgt_ty : UScalarTy)
    (x : UScalar src_ty) (h : src_ty.numBits ≤ tgt_ty.numBits) :
  (cast tgt_ty x).val = x.val := by
  rw [UScalar.cast_val_eq]
  have hBounds := x.hBounds
  apply Nat.mod_eq_of_lt
  have := Nat.pow_le_pow_right (n := 2) (by decide) h
  omega

theorem UScalar.cast_val_mod_pow_of_inBounds_eq {src_ty : UScalarTy} (tgt_ty : UScalarTy)
    (x : UScalar src_ty) (h : x.val < 2^tgt_ty.numBits) :
  (cast tgt_ty x).val = x.val := by
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt h

theorem UScalar.cast_bv_eq {src_ty : UScalarTy} (tgt_ty : UScalarTy) (x : UScalar src_ty) :
  (cast tgt_ty x).bv = x.bv.setWidth tgt_ty.numBits := by
  simp [UScalar.cast]

theorem UScalar.hcast_bv_eq {src_ty : UScalarTy} (tgt_ty : IScalarTy) (x : UScalar src_ty) :
  (hcast tgt_ty x).bv = x.bv.setWidth tgt_ty.numBits := by
  simp [UScalar.hcast]

theorem IScalar.cast_bv_eq {src_ty : IScalarTy} (tgt_ty : IScalarTy) (x : IScalar src_ty) :
  (cast tgt_ty x).bv = x.bv.signExtend tgt_ty.numBits := by
  simp [IScalar.cast]

theorem IScalar.hcast_bv_eq {src_ty : IScalarTy} (tgt_ty : UScalarTy) (x : IScalar src_ty) :
  (hcast tgt_ty x).bv = x.bv.signExtend tgt_ty.numBits := by
  simp [IScalar.hcast]

theorem UScalar.hcast_val_eq {src_ty : UScalarTy} (tgt_ty : IScalarTy) (x : UScalar src_ty) :
  (hcast tgt_ty x).val = Int.bmod x.val (2 ^ tgt_ty.numBits) := by
  show (x.bv.zeroExtend tgt_ty.numBits).toInt = Int.bmod x.bv.toNat (2 ^ tgt_ty.numBits)
  rw [BitVec.zeroExtend_eq_setWidth, BitVec.toInt_setWidth]

theorem IScalar.hcast_val_eq {src_ty : IScalarTy} (tgt_ty : UScalarTy) (x : IScalar src_ty) :
  (hcast tgt_ty x).val = (x.val % (2 ^ tgt_ty.numBits)).toNat := by
  show (x.bv.signExtend tgt_ty.numBits).toNat = (x.bv.toInt % (2 ^ tgt_ty.numBits)).toNat
  rw [BitVec.signExtend, BitVec.toNat_ofInt]
  simp

theorem IScalar.cast_val_eq {src_ty : IScalarTy} (tgt_ty : IScalarTy) (x : IScalar src_ty) :
  (cast tgt_ty x).val = Int.bmod x.val (2^(Min.min tgt_ty.numBits src_ty.numBits)) := by
  show (x.bv.signExtend tgt_ty.numBits).toInt = _
  rw [BitVec.toInt_signExtend]
  rfl

theorem IScalar.val_mod_pow_greater_numBits {src_ty : IScalarTy} (tgt_ty : IScalarTy)
    (x : IScalar src_ty) (h : src_ty.numBits ≤ tgt_ty.numBits) :
  (cast tgt_ty x).val = x.val := by
  rw [IScalar.cast_val_eq, Nat.min_eq_right h]
  have hBounds := x.hBounds
  exact Int.bmod_pow2_eq_of_inBounds' _ _ src_ty.numBits_nonzero hBounds.1 hBounds.2

theorem IScalar.val_mod_pow_inBounds {src_ty : IScalarTy} (tgt_ty : IScalarTy)
    (x : IScalar src_ty)
  (hMin : -2^(tgt_ty.numBits - 1) ≤ x.val) (hMax : x.val < 2^(tgt_ty.numBits - 1)) :
  (cast tgt_ty x).val = x.val := by
  rw [IScalar.cast_val_eq]
  have hBounds := x.hBounds
  have h1 := src_ty.numBits_nonzero
  have h2 := tgt_ty.numBits_nonzero
  apply Int.bmod_pow2_eq_of_inBounds' _ _ (by omega)
  · rcases Nat.le_total tgt_ty.numBits src_ty.numBits with h | h
    · rw [Nat.min_eq_left h]; exact hMin
    · rw [Nat.min_eq_right h]; exact hBounds.1
  · rcases Nat.le_total tgt_ty.numBits src_ty.numBits with h | h
    · rw [Nat.min_eq_left h]; exact hMax
    · rw [Nat.min_eq_right h]; exact hBounds.2

end Aeneas.Std

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
  backends/lean/Aeneas/Std/Scalar/Bitwise.lean
-/

module

public import HaxLean.Rust.Scalar.Core
public import HaxLean.Rust.Scalar.Elab

/-!
# Shifts and bitwise operations

`<<<` and `>>>` in `RustM` (a panic when the amount is at least the bit width or negative;
`>>>` is logical on unsigned and arithmetic on signed integers), and the total
`&&&`, `|||`, `^^^`, `~~~`.
-/

@[expose] public section

set_option autoImplicit false

namespace Aeneas.Std

open RustM Error Arith ScalarElab WP

/-!
# Bit shifts
-/

def UScalar.shiftLeft {ty : UScalarTy} (x : UScalar ty) (s : Nat) :
  RustM (UScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.bv.shiftLeft s ⟩
  else fail .panic

def UScalar.shiftRight {ty : UScalarTy} (x : UScalar ty) (s : Nat) :
  RustM (UScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.bv.ushiftRight s ⟩
  else fail .panic

def UScalar.shiftLeft_UScalar {ty tys} (x : UScalar ty) (s : UScalar tys) :
  RustM (UScalar ty) :=
  x.shiftLeft s.val

def UScalar.shiftRight_UScalar {ty tys} (x : UScalar ty) (s : UScalar tys) :
  RustM (UScalar ty) :=
  x.shiftRight s.val

def UScalar.shiftLeft_IScalar {ty tys} (x : UScalar ty) (s : IScalar tys) :
  RustM (UScalar ty) :=
  if s.val ≥ 0 then
    x.shiftLeft s.toNat
  else fail .panic

def UScalar.shiftRight_IScalar {ty tys} (x : UScalar ty) (s : IScalar tys) :
  RustM (UScalar ty) :=
  if s.val ≥ 0 then
    x.shiftRight s.toNat
  else fail .panic

def IScalar.shiftLeft {ty : IScalarTy} (x : IScalar ty) (s : Nat) :
  RustM (IScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.bv.shiftLeft s ⟩
  else fail .panic

def IScalar.shiftRight {ty : IScalarTy} (x : IScalar ty) (s : Nat) :
  RustM (IScalar ty) :=
  if s < ty.numBits then
    ok ⟨ x.bv.sshiftRight s ⟩
  else fail .panic

def IScalar.shiftLeft_UScalar {ty tys} (x : IScalar ty) (s : UScalar tys) :
  RustM (IScalar ty) :=
  x.shiftLeft s.val

def IScalar.shiftRight_UScalar {ty tys} (x : IScalar ty) (s : UScalar tys) :
  RustM (IScalar ty) :=
  x.shiftRight s.val

def IScalar.shiftLeft_IScalar {ty tys} (x : IScalar ty) (s : IScalar tys) :
  RustM (IScalar ty) :=
  if s.val ≥ 0 then
    x.shiftLeft s.toNat
  else fail .panic

def IScalar.shiftRight_IScalar {ty tys} (x : IScalar ty) (s : IScalar tys) :
  RustM (IScalar ty) :=
  if s.val ≥ 0 then
    x.shiftRight s.toNat
  else fail .panic

instance {ty0 ty1} : HShiftLeft (UScalar ty0) (UScalar ty1) (RustM (UScalar ty0)) where
  hShiftLeft x y := UScalar.shiftLeft_UScalar x y

instance {ty0 ty1} : HShiftLeft (UScalar ty0) (IScalar ty1) (RustM (UScalar ty0)) where
  hShiftLeft x y := UScalar.shiftLeft_IScalar x y

instance {ty0 ty1} : HShiftLeft (IScalar ty0) (UScalar ty1) (RustM (IScalar ty0)) where
  hShiftLeft x y := IScalar.shiftLeft_UScalar x y

instance {ty0 ty1} : HShiftLeft (IScalar ty0) (IScalar ty1) (RustM (IScalar ty0)) where
  hShiftLeft x y := IScalar.shiftLeft_IScalar x y

instance {ty0 ty1} : HShiftRight (UScalar ty0) (UScalar ty1) (RustM (UScalar ty0)) where
  hShiftRight x y := UScalar.shiftRight_UScalar x y

instance {ty0 ty1} : HShiftRight (UScalar ty0) (IScalar ty1) (RustM (UScalar ty0)) where
  hShiftRight x y := UScalar.shiftRight_IScalar x y

instance {ty0 ty1} : HShiftRight (IScalar ty0) (UScalar ty1) (RustM (IScalar ty0)) where
  hShiftRight x y := IScalar.shiftRight_UScalar x y

instance {ty0 ty1} : HShiftRight (IScalar ty0) (IScalar ty1) (RustM (IScalar ty0)) where
  hShiftRight x y := IScalar.shiftRight_IScalar x y

/-!
# Bitwise and, or, xor, not
-/
def UScalar.and {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv &&& y.bv ⟩

def IScalar.and {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.bv &&& y.bv ⟩

instance {ty} : HAnd (UScalar ty) (UScalar ty) (UScalar ty) where
  hAnd x y := UScalar.and x y

instance {ty} : HAnd (IScalar ty) (IScalar ty) (IScalar ty) where
  hAnd x y := IScalar.and x y

def UScalar.or {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv ||| y.bv ⟩

def IScalar.or {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.bv ||| y.bv ⟩

instance {ty} : HOr (UScalar ty) (UScalar ty) (UScalar ty) where
  hOr x y := UScalar.or x y

instance {ty} : HOr (IScalar ty) (IScalar ty) (IScalar ty) where
  hOr x y := IScalar.or x y

def UScalar.xor {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv ^^^ y.bv ⟩

def IScalar.xor {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.bv ^^^ y.bv ⟩

instance {ty} : HXor (UScalar ty) (UScalar ty) (UScalar ty) where
  hXor x y := UScalar.xor x y

instance {ty} : HXor (IScalar ty) (IScalar ty) (IScalar ty) where
  hXor x y := IScalar.xor x y

def UScalar.not {ty} (x : UScalar ty) : UScalar ty := ⟨ ~~~x.bv ⟩

def IScalar.not {ty} (x : IScalar ty) : IScalar ty := ⟨ ~~~x.bv ⟩

instance {ty} : Complement (UScalar ty) where
  complement x := UScalar.not x

instance {ty} : Complement (IScalar ty) where
  complement x := IScalar.not x

/-!
## Shift theorems
-/

theorem UScalar.ShiftRight_spec {ty0 ty1} (x : UScalar ty0) (y : UScalar ty1) :
    partialSpec (x >>> y)
      (fun z => z.val = x.val >>> y.val ∧ z.bv = x.bv >>> y.val ∧ y.val < ty0.numBits)
      (fun | .panic => y.val ≥ ty0.numBits | _ => False)
      False := by
  simp only [HShiftRight.hShiftRight, shiftRight_UScalar, shiftRight]
  split
  · simp only [partialSpec_ok]
    refine ⟨?_, trivial, by assumption⟩
    show (x.bv >>> y.val).toNat = x.bv.toNat >>> y.val
    rw [BitVec.toNat_ushiftRight]
  · simp only [partialSpec_fail]; omega

uscalar theorem «%S».ShiftRight_spec {ty1} (x : «%S») (y : UScalar ty1) :
    partialSpec (x >>> y)
      (fun z => z.val = x.val >>> y.val ∧ z.bv = x.bv >>> y.val ∧ y.val < %BitWidth)
      (fun | .panic => y.val ≥ %BitWidth | _ => False)
      False :=
  UScalar.ShiftRight_spec x y

theorem UScalar.ShiftRight_IScalar_spec {ty0 ty1} (x : UScalar ty0) (y : IScalar ty1) :
    partialSpec (x >>> y)
      (fun z => z.val = x.val >>> y.toNat ∧ z.bv = x.bv >>> y.toNat ∧ y.toNat < ty0.numBits)
      (fun | .panic => y.val < 0 ∨ y.toNat ≥ ty0.numBits | _ => False)
      False := by
  simp only [HShiftRight.hShiftRight, shiftRight_IScalar, shiftRight]
  split
  · split
    · simp only [partialSpec_ok]
      refine ⟨?_, trivial, by assumption⟩
      show (x.bv >>> y.toNat).toNat = x.bv.toNat >>> y.toNat
      rw [BitVec.toNat_ushiftRight]
    · simp only [partialSpec_fail]; omega
  · simp only [partialSpec_fail]; omega

uscalar theorem «%S».ShiftRight_IScalar_spec {ty1} (x : «%S») (y : IScalar ty1) :
    partialSpec (x >>> y)
      (fun z => z.val = x.val >>> y.toNat ∧ z.bv = x.bv >>> y.toNat ∧ y.toNat < %BitWidth)
      (fun | .panic => y.val < 0 ∨ y.toNat ≥ %BitWidth | _ => False)
      False :=
  UScalar.ShiftRight_IScalar_spec x y

theorem UScalar.ShiftLeft_spec {ty0 ty1} (x : UScalar ty0) (y : UScalar ty1) (size : Nat)
    (hsize : size = UScalar.size ty0) :
    partialSpec (x <<< y)
      (fun z => z.val = (x.val <<< y.val) % size ∧ z.bv = x.bv <<< y.val ∧ y.val < ty0.numBits)
      (fun | .panic => y.val ≥ ty0.numBits | _ => False)
      False := by
  simp only [HShiftLeft.hShiftLeft, shiftLeft_UScalar, shiftLeft]
  split <;> rename_i h
  · simp only [partialSpec_ok, hsize, UScalar.size]
    refine ⟨?_, trivial, h⟩
    show (x.bv <<< y.val).toNat = x.bv.toNat <<< y.val % 2 ^ ty0.numBits
    rw [BitVec.toNat_shiftLeft]
  · simp only [partialSpec_fail]; omega

uscalar theorem «%S».ShiftLeft_spec {ty1} (x : «%S») (y : UScalar ty1) :
    partialSpec (x <<< y)
      (fun z => z.val = (x.val <<< y.val) % «%S».size ∧ z.bv = x.bv <<< y.val ∧
        y.val < %BitWidth)
      (fun | .panic => y.val ≥ %BitWidth | _ => False)
      False :=
  UScalar.ShiftLeft_spec x y «%S».size (by simp)

theorem UScalar.ShiftLeft_IScalar_spec {ty0 ty1} (x : UScalar ty0) (y : IScalar ty1) (size : Nat)
    (hsize : size = UScalar.size ty0) :
    partialSpec (x <<< y)
      (fun z => z.val = (x.val <<< y.toNat) % size ∧ z.bv = x.bv <<< y.toNat ∧
        y.toNat < ty0.numBits)
      (fun | .panic => y.val < 0 ∨ y.toNat ≥ ty0.numBits | _ => False)
      False := by
  simp only [HShiftLeft.hShiftLeft, shiftLeft_IScalar, shiftLeft]
  split
  · split <;> rename_i h
    · simp only [partialSpec_ok, hsize, UScalar.size]
      refine ⟨?_, trivial, h⟩
      show (x.bv <<< y.toNat).toNat = x.bv.toNat <<< y.toNat % 2 ^ ty0.numBits
      rw [BitVec.toNat_shiftLeft]
    · simp only [partialSpec_fail]; omega
  · simp only [partialSpec_fail]; omega

uscalar theorem «%S».ShiftLeft_IScalar_spec {ty1} (x : «%S») (y : IScalar ty1) :
    partialSpec (x <<< y)
      (fun z => z.val = (x.val <<< y.toNat) % «%S».size ∧ z.bv = x.bv <<< y.toNat ∧
        y.toNat < %BitWidth)
      (fun | .panic => y.val < 0 ∨ y.toNat ≥ %BitWidth | _ => False)
      False :=
  UScalar.ShiftLeft_IScalar_spec x y «%S».size (by simp)

theorem IScalar.ShiftRight_spec {ty0 ty1} (x : IScalar ty0) (y : UScalar ty1) :
    partialSpec (x >>> y)
      (fun z => z.val = x.val >>> y.val ∧ z.bv = x.bv.sshiftRight y.val ∧ y.val < ty0.numBits)
      (fun | .panic => y.val ≥ ty0.numBits | _ => False)
      False := by
  simp only [HShiftRight.hShiftRight, shiftRight_UScalar, shiftRight]
  split <;> rename_i h
  · simp only [partialSpec_ok]
    refine ⟨?_, trivial, h⟩
    show (x.bv.sshiftRight y.val).toInt = x.bv.toInt >>> y.val
    rw [BitVec.toInt_sshiftRight]
  · simp only [partialSpec_fail]; omega

iscalar theorem «%S».ShiftRight_spec {ty1} (x : «%S») (y : UScalar ty1) :
    partialSpec (x >>> y)
      (fun z => z.val = x.val >>> y.val ∧ z.bv = x.bv.sshiftRight y.val ∧ y.val < %BitWidth)
      (fun | .panic => y.val ≥ %BitWidth | _ => False)
      False :=
  IScalar.ShiftRight_spec x y

theorem IScalar.ShiftRight_IScalar_spec {ty0 ty1} (x : IScalar ty0) (y : IScalar ty1) :
    partialSpec (x >>> y)
      (fun z => z.val = x.val >>> y.toNat ∧ z.bv = x.bv.sshiftRight y.toNat ∧
        y.toNat < ty0.numBits)
      (fun | .panic => y.val < 0 ∨ y.toNat ≥ ty0.numBits | _ => False)
      False := by
  simp only [HShiftRight.hShiftRight, shiftRight_IScalar, shiftRight]
  split
  · split <;> rename_i h1
    · simp only [partialSpec_ok]
      refine ⟨?_, trivial, h1⟩
      show (x.bv.sshiftRight y.toNat).toInt = x.bv.toInt >>> y.toNat
      rw [BitVec.toInt_sshiftRight]
    · simp only [partialSpec_fail]; omega
  · simp only [partialSpec_fail]; omega

iscalar theorem «%S».ShiftRight_IScalar_spec {ty1} (x : «%S») (y : IScalar ty1) :
    partialSpec (x >>> y)
      (fun z => z.val = x.val >>> y.toNat ∧ z.bv = x.bv.sshiftRight y.toNat ∧ y.toNat < %BitWidth)
      (fun | .panic => y.val < 0 ∨ y.toNat ≥ %BitWidth | _ => False)
      False :=
  IScalar.ShiftRight_IScalar_spec x y

theorem IScalar.ShiftLeft_spec {ty0 ty1} (x : IScalar ty0) (y : UScalar ty1) :
    partialSpec (x <<< y)
      (fun z => z.val = Int.bmod (x.val <<< y.val) (2 ^ ty0.numBits) ∧ z.bv = x.bv <<< y.val ∧
        y.val < ty0.numBits)
      (fun | .panic => y.val ≥ ty0.numBits | _ => False)
      False := by
  simp only [HShiftLeft.hShiftLeft, shiftLeft_UScalar, shiftLeft]
  split <;> rename_i h
  · simp only [partialSpec_ok]
    refine ⟨?_, trivial, h⟩
    show (x.bv <<< y.val).toInt = Int.bmod (x.bv.toInt <<< y.val) (2 ^ ty0.numBits)
    rw [BitVec.toInt_shiftLeft, Int.shiftLeft_eq, Nat.shiftLeft_eq, BitVec.toInt_eq_toNat_bmod]
    simp only [Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int, Int.bmod_mul_bmod]
  · simp only [partialSpec_fail]; omega

iscalar theorem «%S».ShiftLeft_spec {ty1} (x : «%S») (y : UScalar ty1) :
    partialSpec (x <<< y)
      (fun z => z.val = Int.bmod (x.val <<< y.val) «%S».size ∧ z.bv = x.bv <<< y.val ∧
        y.val < %BitWidth)
      (fun | .panic => y.val ≥ %BitWidth | _ => False)
      False := by
  simpa only [«%S».size, «%S».numBits, IScalarTy.numBits] using IScalar.ShiftLeft_spec x y

theorem IScalar.ShiftLeft_IScalar_spec {ty0 ty1} (x : IScalar ty0) (y : IScalar ty1) :
    partialSpec (x <<< y)
      (fun z => z.val = Int.bmod (x.val <<< y.toNat) (2 ^ ty0.numBits) ∧
        z.bv = x.bv <<< y.toNat ∧ y.toNat < ty0.numBits)
      (fun | .panic => y.val < 0 ∨ y.toNat ≥ ty0.numBits | _ => False)
      False := by
  simp only [HShiftLeft.hShiftLeft, shiftLeft_IScalar, shiftLeft]
  split
  · split <;> rename_i h
    · simp only [partialSpec_ok]
      refine ⟨?_, trivial, h⟩
      show (x.bv <<< y.toNat).toInt = Int.bmod (x.bv.toInt <<< y.toNat) (2 ^ ty0.numBits)
      rw [BitVec.toInt_shiftLeft, Int.shiftLeft_eq, Nat.shiftLeft_eq, BitVec.toInt_eq_toNat_bmod]
      simp only [Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int, Int.bmod_mul_bmod]
    · simp only [partialSpec_fail]; omega
  · simp only [partialSpec_fail]; omega

iscalar theorem «%S».ShiftLeft_IScalar_spec {ty1} (x : «%S») (y : IScalar ty1) :
    partialSpec (x <<< y)
      (fun z => z.val = Int.bmod (x.val <<< y.toNat) «%S».size ∧ z.bv = x.bv <<< y.toNat ∧
        y.toNat < %BitWidth)
      (fun | .panic => y.val < 0 ∨ y.toNat ≥ %BitWidth | _ => False)
      False := by
  simpa only [«%S».size, «%S».numBits, IScalarTy.numBits] using IScalar.ShiftLeft_IScalar_spec x y

/-!
## Bitwise and, or, xor, not: theorems
-/

theorem UScalar.and_spec {ty} (x y : UScalar ty) :
  lift (x &&& y) ⦃ z => z.val = (x &&& y).val ∧ z.bv = x.bv &&& y.bv ⦄ := by
  simp [lift]
  rfl

theorem UScalar.or_spec {ty} (x y : UScalar ty) :
  lift (x ||| y) ⦃ z => z.val = (x ||| y).val ∧ z.bv = x.bv ||| y.bv ⦄ := by
  simp [lift]
  rfl

theorem UScalar.xor_spec {ty} (x y : UScalar ty) :
  lift (x ^^^ y) ⦃ z => z.val = (x ^^^ y).val ∧ z.bv = x.bv ^^^ y.bv ⦄ := by
  simp [lift]
  rfl

theorem IScalar.and_spec {ty} (x y : IScalar ty) :
  lift (x &&& y) ⦃ z => z.val = (x &&& y).val ∧ z.bv = x.bv &&& y.bv ⦄ := by
  simp [lift]
  rfl

theorem IScalar.or_spec {ty} (x y : IScalar ty) :
  lift (x ||| y) ⦃ z => z.val = (x ||| y).val ∧ z.bv = x.bv ||| y.bv ⦄ := by
  simp [lift]
  rfl

theorem IScalar.xor_spec {ty} (x y : IScalar ty) :
  lift (x ^^^ y) ⦃ z => z.val = (x ^^^ y).val ∧ z.bv = x.bv ^^^ y.bv ⦄ := by
  simp [lift]
  rfl

theorem UScalar.not_spec {ty} (x : UScalar ty) :
  lift (~~~x) ⦃ z => z = ~~~x ⦄ := by
  simp [lift]

theorem IScalar.not_spec {ty} (x : IScalar ty) :
  lift (~~~x) ⦃ z => z = ~~~x ⦄ := by
  simp [lift]

@[simp, grind =] theorem UScalar.bv_and {ty} (x y : UScalar ty) :
    (x &&& y).bv = x.bv &&& y.bv := by rfl
@[simp, grind =] theorem UScalar.bv_or {ty} (x y : UScalar ty) :
    (x ||| y).bv = x.bv ||| y.bv := by rfl
@[simp, grind =] theorem UScalar.bv_xor {ty} (x y : UScalar ty) :
    (x ^^^ y).bv = x.bv ^^^ y.bv := by rfl
@[simp, grind =] theorem UScalar.bv_not {ty} (x : UScalar ty) : (~~~x).bv = ~~~x.bv := by rfl
@[simp, grind =] theorem IScalar.bv_and {ty} (x y : IScalar ty) :
    (x &&& y).bv = x.bv &&& y.bv := by rfl
@[simp, grind =] theorem IScalar.bv_or {ty} (x y : IScalar ty) :
    (x ||| y).bv = x.bv ||| y.bv := by rfl
@[simp, grind =] theorem IScalar.bv_xor {ty} (x y : IScalar ty) :
    (x ^^^ y).bv = x.bv ^^^ y.bv := by rfl
@[simp, grind =] theorem IScalar.bv_not {ty} (x : IScalar ty) : (~~~x).bv = ~~~x.bv := by rfl

@[simp, grind =] theorem UScalar.val_and {ty} (x y : UScalar ty) :
    (x &&& y).val = x.val &&& y.val := by
  show (x.bv &&& y.bv).toNat = x.bv.toNat &&& y.bv.toNat
  rw [BitVec.toNat_and]
@[simp, grind =] theorem UScalar.val_or {ty} (x y : UScalar ty) :
    (x ||| y).val = x.val ||| y.val := by
  show (x.bv ||| y.bv).toNat = x.bv.toNat ||| y.bv.toNat
  rw [BitVec.toNat_or]
@[simp, grind =] theorem UScalar.val_xor {ty} (x y : UScalar ty) :
    (x ^^^ y).val = x.val ^^^ y.val := by
  show (x.bv ^^^ y.bv).toNat = x.bv.toNat ^^^ y.bv.toNat
  rw [BitVec.toNat_xor]

end Aeneas.Std

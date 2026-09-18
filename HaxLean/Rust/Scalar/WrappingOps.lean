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
  backends/lean/Aeneas/Std/Scalar/WrappingOps/Add.lean
  backends/lean/Aeneas/Std/Scalar/WrappingOps/Sub.lean
  backends/lean/Aeneas/Std/Scalar/WrappingOps/Mul.lean
  backends/lean/Aeneas/Std/Scalar/WrappingOps/Shl.lean
  backends/lean/Aeneas/Std/Scalar/WrappingOps/Shr.lean
-/

module

public import HaxLean.Rust.Scalar.Core
public import HaxLean.Rust.Scalar.Elab

/-!
# Wrapping arithmetic

`wrapping_add`, `wrapping_sub`, `wrapping_mul` compute modulo `2^numBits`;
`wrapping_shl`, `wrapping_shr` reduce the shift amount modulo the bit width. These are
Rust's release-profile semantics, available in every profile through the `wrapping_*`
methods.
-/

@[expose] public section

set_option autoImplicit false

namespace Aeneas.Std

open RustM Error ScalarElab

def UScalar.wrapping_add {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv + y.bv ⟩

def IScalar.wrapping_add {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.bv + y.bv ⟩

uscalar def «%S».wrapping_add (x y : «%S») : «%S» := @UScalar.wrapping_add UScalarTy.«%S» x y

iscalar def «%S».wrapping_add (x y : «%S») : «%S» := @IScalar.wrapping_add IScalarTy.«%S» x y

/- `core::num::{_}::wrapping_add` -/
uscalar def core.num.«%S».wrapping_add : «%S» → «%S» → «%S» :=
  @UScalar.wrapping_add UScalarTy.«%S»

/- `core::num::{_}::wrapping_add` -/
iscalar def core.num.«%S».wrapping_add : «%S» → «%S» → «%S»  :=
  @IScalar.wrapping_add IScalarTy.«%S»

@[simp] theorem UScalar.wrapping_add_bv_eq {ty} (x y : UScalar ty) :
  (wrapping_add x y).bv = x.bv + y.bv := by
  simp only [wrapping_add]

uscalar @[simp, grind =] theorem «%S».wrapping_add_bv_eq (x y : «%S») :
  («%S».wrapping_add x y).bv = x.bv + y.bv := by
  simp [«%S».wrapping_add]

uscalar @[simp, grind =] theorem core.num.«%S».wrapping_add_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.«%S».wrapping_add]

@[simp] theorem IScalar.wrapping_add_bv_eq {ty} (x y : IScalar ty) :
  (wrapping_add x y).bv = x.bv + y.bv := by
  simp only [wrapping_add]

iscalar @[simp, grind =] theorem «%S».wrapping_add_bv_eq (x y : «%S») :
  («%S».wrapping_add x y).bv = x.bv + y.bv := by
  simp [«%S».wrapping_add]

iscalar @[simp, grind =] theorem core.num.«%S».wrapping_add_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).bv = x.bv + y.bv := by
  simp [core.num.«%S».wrapping_add]

@[simp] theorem UScalar.wrapping_add_val_eq {ty} (x y : UScalar ty) :
  (wrapping_add x y).val = (x.val + y.val) % (UScalar.size ty) := by
  show (x.bv + y.bv).toNat = (x.bv.toNat + y.bv.toNat) % UScalar.size ty
  rw [BitVec.toNat_add, UScalar.size]

uscalar @[simp, grind =] theorem «%S».wrapping_add_val_eq (x y : «%S») :
  («%S».wrapping_add x y).val = (x.val + y.val) % (UScalar.size .«%S») :=
  UScalar.wrapping_add_val_eq x y

uscalar @[simp, grind =] theorem core.num.«%S».wrapping_add_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).val = (x.val + y.val) % (UScalar.size .«%S») :=
  UScalar.wrapping_add_val_eq x y

@[simp] theorem IScalar.wrapping_add_val_eq {ty} (x y : IScalar ty) :
  (wrapping_add x y).val = Int.bmod (x.val + y.val) (2^ty.numBits) := by
  show (x.bv + y.bv).toInt = Int.bmod (x.bv.toInt + y.bv.toInt) (2^ty.numBits)
  rw [BitVec.toInt_add]

iscalar @[simp, grind =] theorem «%S».wrapping_add_val_eq (x y : «%S») :
  («%S».wrapping_add x y).val = Int.bmod (x.val + y.val) (2^ %BitWidth) :=
  IScalar.wrapping_add_val_eq x y

iscalar @[simp, grind =] theorem core.num.«%S».wrapping_add_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_add x y).val = Int.bmod (x.val + y.val) (2^ %BitWidth) :=
  IScalar.wrapping_add_val_eq x y

def UScalar.wrapping_sub {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv - y.bv ⟩

def IScalar.wrapping_sub {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.bv - y.bv ⟩

uscalar def «%S».wrapping_sub : «%S» → «%S» → «%S» := @UScalar.wrapping_sub UScalarTy.«%S»

iscalar def «%S».wrapping_sub : «%S» → «%S» → «%S»  := @IScalar.wrapping_sub IScalarTy.«%S»

/- `core::num::{_}::wrapping_sub` -/
uscalar def core.num.«%S».wrapping_sub : «%S» → «%S» → «%S» :=
  @UScalar.wrapping_sub UScalarTy.«%S»

/- `core::num::{_}::wrapping_sub` -/
iscalar def core.num.«%S».wrapping_sub : «%S» → «%S» → «%S»  :=
  @IScalar.wrapping_sub IScalarTy.«%S»

@[simp] theorem UScalar.wrapping_sub_bv_eq {ty} (x y : UScalar ty) :
  (wrapping_sub x y).bv = x.bv - y.bv := by
  simp only [wrapping_sub]

uscalar @[simp, grind =] theorem «%S».wrapping_sub_bv_eq (x y : «%S») :
  («%S».wrapping_sub x y).bv = x.bv - y.bv := by
  simp [«%S».wrapping_sub]

uscalar @[simp, grind =] theorem core.num.«%S».wrapping_sub_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).bv = x.bv - y.bv := by
  simp [core.num.«%S».wrapping_sub]

@[simp] theorem IScalar.wrapping_sub_bv_eq {ty} (x y : IScalar ty) :
  (wrapping_sub x y).bv = x.bv - y.bv := by
  simp only [wrapping_sub]

iscalar @[simp, grind =] theorem «%S».wrapping_sub_bv_eq (x y : «%S») :
  («%S».wrapping_sub x y).bv = x.bv - y.bv := by
  simp [«%S».wrapping_sub]

iscalar @[simp, grind =] theorem core.num.«%S».wrapping_sub_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).bv = x.bv - y.bv := by
  simp [core.num.«%S».wrapping_sub]

@[simp] theorem UScalar.wrapping_sub_val_eq {ty} (x y : UScalar ty) :
  (wrapping_sub x y).val = (x.val + (UScalar.size ty - y.val)) % UScalar.size ty := by
  show (x.bv - y.bv).toNat = (x.bv.toNat + (UScalar.size ty - y.bv.toNat)) % UScalar.size ty
  rw [BitVec.toNat_sub, UScalar.size, Nat.add_comm]

uscalar @[simp, grind =] theorem «%S».wrapping_sub_val_eq (x y : «%S») :
  («%S».wrapping_sub x y).val = (x.val + (UScalar.size .«%S» - y.val)) % UScalar.size .«%S» :=
  UScalar.wrapping_sub_val_eq x y

uscalar @[simp, grind =] theorem core.num.«%S».wrapping_sub_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).val =
    (x.val + (UScalar.size .«%S» - y.val)) % UScalar.size .«%S» :=
  UScalar.wrapping_sub_val_eq x y

@[simp] theorem IScalar.wrapping_sub_val_eq {ty} (x y : IScalar ty) :
  (wrapping_sub x y).val = Int.bmod (x.val - y.val) (2^ty.numBits) := by
  show (x.bv - y.bv).toInt = Int.bmod (x.bv.toInt - y.bv.toInt) (2^ty.numBits)
  rw [BitVec.toInt_sub]

iscalar @[simp, grind =] theorem «%S».wrapping_sub_val_eq (x y : «%S») :
  («%S».wrapping_sub x y).val = Int.bmod (x.val - y.val) (2^ %BitWidth) :=
  IScalar.wrapping_sub_val_eq x y

iscalar @[simp, grind =] theorem core.num.«%S».wrapping_sub_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_sub x y).val = Int.bmod (x.val - y.val) (2^ %BitWidth) :=
  IScalar.wrapping_sub_val_eq x y

def UScalar.wrapping_mul {ty} (x y : UScalar ty) : UScalar ty := ⟨ x.bv * y.bv ⟩

def IScalar.wrapping_mul {ty} (x y : IScalar ty) : IScalar ty := ⟨ x.bv * y.bv ⟩

uscalar def «%S».wrapping_mul (x y : «%S») : «%S» := @UScalar.wrapping_mul UScalarTy.«%S» x y

iscalar def «%S».wrapping_mul (x y : «%S») : «%S» := @IScalar.wrapping_mul IScalarTy.«%S» x y

/- `core::num::{_}::wrapping_mul` -/
uscalar def core.num.«%S».wrapping_mul : «%S» → «%S» → «%S» :=
  @UScalar.wrapping_mul UScalarTy.«%S»

/- `core::num::{_}::wrapping_mul` -/
iscalar def core.num.«%S».wrapping_mul : «%S» → «%S» → «%S»  :=
  @IScalar.wrapping_mul IScalarTy.«%S»

@[simp, grind =] theorem UScalar.wrapping_mul_bv_eq {ty} (x y : UScalar ty) :
  (wrapping_mul x y).bv = x.bv * y.bv := by
  simp only [wrapping_mul]

uscalar @[simp, grind =] theorem «%S».wrapping_mul_bv_eq (x y : «%S») :
  («%S».wrapping_mul x y).bv = x.bv * y.bv := by
  simp [«%S».wrapping_mul]

uscalar @[simp, grind =] theorem core.num.«%S».wrapping_mul_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).bv = x.bv * y.bv := by
  simp [core.num.«%S».wrapping_mul]

@[simp, grind =] theorem IScalar.wrapping_mul_bv_eq {ty} (x y : IScalar ty) :
  (wrapping_mul x y).bv = x.bv * y.bv := by
  simp only [wrapping_mul]

iscalar @[simp, grind =] theorem «%S».wrapping_mul_bv_eq (x y : «%S») :
  («%S».wrapping_mul x y).bv = x.bv * y.bv := by
  simp [«%S».wrapping_mul]

iscalar @[simp, grind =] theorem core.num.«%S».wrapping_mul_bv_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).bv = x.bv * y.bv := by
  simp [core.num.«%S».wrapping_mul]

@[simp] theorem UScalar.wrapping_mul_val_eq {ty} (x y : UScalar ty) :
  (wrapping_mul x y).val = (x.val * y.val) % (UScalar.size ty) := by
  show (x.bv * y.bv).toNat = (x.bv.toNat * y.bv.toNat) % UScalar.size ty
  rw [BitVec.toNat_mul, UScalar.size]

uscalar @[simp, grind =] theorem «%S».wrapping_mul_val_eq (x y : «%S») :
  («%S».wrapping_mul x y).val = (x.val * y.val) % (UScalar.size .«%S») :=
  UScalar.wrapping_mul_val_eq x y

uscalar @[simp, grind =] theorem core.num.«%S».wrapping_mul_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).val = (x.val * y.val) % (UScalar.size .«%S») :=
  UScalar.wrapping_mul_val_eq x y

@[simp] theorem IScalar.wrapping_mul_val_eq {ty} (x y : IScalar ty) :
  (wrapping_mul x y).val = Int.bmod (x.val * y.val) (2^ty.numBits) := by
  show (x.bv * y.bv).toInt = Int.bmod (x.bv.toInt * y.bv.toInt) (2^ty.numBits)
  rw [BitVec.toInt_mul]

iscalar @[simp, grind =] theorem «%S».wrapping_mul_val_eq (x y : «%S») :
  («%S».wrapping_mul x y).val = Int.bmod (x.val * y.val) (2^ %BitWidth) :=
  IScalar.wrapping_mul_val_eq x y

iscalar @[simp, grind =] theorem core.num.«%S».wrapping_mul_val_eq (x y : «%S») :
  (core.num.«%S».wrapping_mul x y).val = Int.bmod (x.val * y.val) (2^ %BitWidth) :=
  IScalar.wrapping_mul_val_eq x y

/-- Wrapping shift left: `x << (s % BITS)`. -/
def UScalar.wrapping_shl {ty} (x : UScalar ty) (s : U32) : UScalar ty :=
  ⟨ x.bv.shiftLeft (s.val % ty.numBits) ⟩

/-- Wrapping shift left: `x << (s % BITS)`. -/
def IScalar.wrapping_shl {ty} (x : IScalar ty) (s : U32) : IScalar ty :=
  ⟨ x.bv.shiftLeft (s.val % ty.numBits) ⟩

uscalar def «%S».wrapping_shl (x : «%S») (s : U32) : «%S» :=
  @UScalar.wrapping_shl UScalarTy.«%S» x s

iscalar def «%S».wrapping_shl (x : «%S») (s : U32) : «%S» :=
  @IScalar.wrapping_shl IScalarTy.«%S» x s

/- `core::num::{_}::wrapping_shl` -/
uscalar def core.num.«%S».wrapping_shl : «%S» → U32 → «%S» :=
  @UScalar.wrapping_shl UScalarTy.«%S»

/- `core::num::{_}::wrapping_shl` -/
iscalar def core.num.«%S».wrapping_shl : «%S» → U32 → «%S» :=
  @IScalar.wrapping_shl IScalarTy.«%S»

@[simp, grind =] theorem UScalar.wrapping_shl_bv_eq {ty} (x : UScalar ty) (s : U32) :
  (wrapping_shl x s).bv = x.bv.shiftLeft (s.val % ty.numBits) := by
  simp only [wrapping_shl]

uscalar @[simp, grind =] theorem «%S».wrapping_shl_bv_eq (x : «%S») (s : U32) :
  («%S».wrapping_shl x s).bv = x.bv.shiftLeft (s.val % %BitWidth) := by
  simp [«%S».wrapping_shl]

uscalar @[simp, grind =] theorem core.num.«%S».wrapping_shl_bv_eq (x : «%S») (s : U32) :
  (core.num.«%S».wrapping_shl x s).bv = x.bv.shiftLeft (s.val % %BitWidth) := by
  simp [core.num.«%S».wrapping_shl]

@[simp, grind =] theorem IScalar.wrapping_shl_bv_eq {ty} (x : IScalar ty) (s : U32) :
  (wrapping_shl x s).bv = x.bv.shiftLeft (s.val % ty.numBits) := by
  simp only [wrapping_shl]

iscalar @[simp, grind =] theorem «%S».wrapping_shl_bv_eq (x : «%S») (s : U32) :
  («%S».wrapping_shl x s).bv = x.bv.shiftLeft (s.val % %BitWidth) := by
  simp [«%S».wrapping_shl]

iscalar @[simp, grind =] theorem core.num.«%S».wrapping_shl_bv_eq (x : «%S») (s : U32) :
  (core.num.«%S».wrapping_shl x s).bv = x.bv.shiftLeft (s.val % %BitWidth) := by
  simp [core.num.«%S».wrapping_shl]

/-- Wrapping shift right: `x >> (s % BITS)`, logical on unsigned, arithmetic on signed. -/
def UScalar.wrapping_shr {ty} (x : UScalar ty) (s : U32) : UScalar ty :=
  ⟨ x.bv.ushiftRight (s.val % ty.numBits) ⟩

/-- Wrapping shift right: `x >> (s % BITS)`, logical on unsigned, arithmetic on signed. -/
def IScalar.wrapping_shr {ty} (x : IScalar ty) (s : U32) : IScalar ty :=
  ⟨ x.bv.sshiftRight (s.val % ty.numBits) ⟩

uscalar def «%S».wrapping_shr (x : «%S») (s : U32) : «%S» :=
  @UScalar.wrapping_shr UScalarTy.«%S» x s

iscalar def «%S».wrapping_shr (x : «%S») (s : U32) : «%S» :=
  @IScalar.wrapping_shr IScalarTy.«%S» x s

/- `core::num::{_}::wrapping_shr` -/
uscalar def core.num.«%S».wrapping_shr : «%S» → U32 → «%S» :=
  @UScalar.wrapping_shr UScalarTy.«%S»

/- `core::num::{_}::wrapping_shr` -/
iscalar def core.num.«%S».wrapping_shr : «%S» → U32 → «%S» :=
  @IScalar.wrapping_shr IScalarTy.«%S»

@[simp, grind =] theorem UScalar.wrapping_shr_bv_eq {ty} (x : UScalar ty) (s : U32) :
  (wrapping_shr x s).bv = x.bv.ushiftRight (s.val % ty.numBits) := by
  simp only [wrapping_shr]

uscalar @[simp, grind =] theorem «%S».wrapping_shr_bv_eq (x : «%S») (s : U32) :
  («%S».wrapping_shr x s).bv = x.bv.ushiftRight (s.val % %BitWidth) := by
  simp [«%S».wrapping_shr]

uscalar @[simp, grind =] theorem core.num.«%S».wrapping_shr_bv_eq (x : «%S») (s : U32) :
  (core.num.«%S».wrapping_shr x s).bv = x.bv.ushiftRight (s.val % %BitWidth) := by
  simp [core.num.«%S».wrapping_shr]

@[simp, grind =] theorem IScalar.wrapping_shr_bv_eq {ty} (x : IScalar ty) (s : U32) :
  (wrapping_shr x s).bv = x.bv.sshiftRight (s.val % ty.numBits) := by
  simp only [wrapping_shr]

iscalar @[simp, grind =] theorem «%S».wrapping_shr_bv_eq (x : «%S») (s : U32) :
  («%S».wrapping_shr x s).bv = x.bv.sshiftRight (s.val % %BitWidth) := by
  simp [«%S».wrapping_shr]

iscalar @[simp, grind =] theorem core.num.«%S».wrapping_shr_bv_eq (x : «%S») (s : U32) :
  (core.num.«%S».wrapping_shr x s).bv = x.bv.sshiftRight (s.val % %BitWidth) := by
  simp [core.num.«%S».wrapping_shr]

end Aeneas.Std

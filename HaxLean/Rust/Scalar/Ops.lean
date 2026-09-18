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
  backends/lean/Aeneas/Std/Scalar/Ops/Add.lean
  backends/lean/Aeneas/Std/Scalar/Ops/Sub.lean
  backends/lean/Aeneas/Std/Scalar/Ops/Mul.lean
  backends/lean/Aeneas/Std/Scalar/Ops/Div.lean
  backends/lean/Aeneas/Std/Scalar/Ops/Rem.lean
  backends/lean/Aeneas/Std/Scalar/Ops/Neg.lean
-/

module

public import HaxLean.Rust.Scalar.Misc
public import HaxLean.Rust.Scalar.Elab

/-!
# Checked arithmetic

`+ - * / %` and negation on scalars, in `RustM`: a panic on overflow, on a zero divisor,
on `MIN / -1` and on `MIN % -1` (Rust's debug profile). Signed division and remainder
truncate towards zero (`Int.tdiv`, `Int.tmod`).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Aeneas.Std

open RustM Error Arith ScalarElab WP

/-!
# Addition
-/

/-- Checked addition: a panic on overflow. -/
def UScalar.add {ty : UScalarTy} (x y : UScalar ty) : RustM (UScalar ty) :=
  UScalar.tryMk ty (x.val + y.val)

/-- Checked addition: a panic on overflow. -/
def IScalar.add {ty : IScalarTy} (x y : IScalar ty) : RustM (IScalar ty) :=
  IScalar.tryMk ty (x.val + y.val)

def UScalar.try_add {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofRustM (add x y)

def IScalar.try_add {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofRustM (add x y)

instance {ty} : HAdd (UScalar ty) (UScalar ty) (RustM (UScalar ty)) where
  hAdd x y := UScalar.add x y

instance {ty} : HAdd (IScalar ty) (IScalar ty) (RustM (IScalar ty)) where
  hAdd x y := IScalar.add x y

theorem UScalar.add_equiv {ty} (x y : UScalar ty) :
  match x + y with
  | ok z => x.val + y.val < 2^ty.numBits ∧
    z.val = x.val + y.val ∧
    z.bv = x.bv + y.bv
  | fail e => e = .panic ∧ ¬ (UScalar.inBounds ty (x.val + y.val))
  | _ => False := by
  have : x + y = add x y := by rfl
  rw [this]
  simp only [add, tryMk, tryMkOpt, RustM.ofOption]
  by_cases h : x.val + y.val < 2^ty.numBits
  · simp only [check_bounds, h, decide_true, ↓reduceDIte, ofNatCore_val_eq, true_and]
    apply BitVec.eq_of_toNat_eq
    simp only [ofNatCore, BitVec.toNat_add, BitVec.toNat_ofFin, UScalar.val] at h ⊢
    rw [Nat.mod_eq_of_lt h]
  · simp [h]

theorem IScalar.add_equiv {ty} (x y : IScalar ty) :
  match x + y with
  | ok z =>
    IScalar.inBounds ty (x.val + y.val) ∧
    z.val = x.val + y.val ∧
    z.bv = x.bv + y.bv
  | fail e => e = .panic ∧ ¬ (IScalar.inBounds ty (x.val + y.val))
  | _ => False := by
  have : x + y = add x y := by rfl
  rw [this]
  simp only [add, tryMk, tryMkOpt, RustM.ofOption]
  by_cases h : -2 ^ (ty.numBits - 1) ≤ x.val + y.val ∧ x.val + y.val < 2 ^ (ty.numBits - 1)
  · simp only [check_bounds, h, decide_true, ↓reduceDIte, ofInt_val_eq, inBounds, true_and]
    apply BitVec.eq_of_toInt_eq
    simp only [BitVec.toInt_add, bv_toInt_eq, ofInt_val_eq]
    rw [bmod_pow_numBits_eq_of_lt ty _ h.1 h.2]
  · simp [h]

theorem UScalar.add_bv_spec {ty} {x y : UScalar ty}
  (hmax : ↑x + ↑y ≤ UScalar.max ty) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ∧ z.bv = x.bv + y.bv ⦄ := by
  have h := @add_equiv ty x y
  have : 0 < 2^ty.numBits := Nat.two_pow_pos _
  simp only [max] at hmax
  rcases hxy : (x + y) with z | e | _ <;> rw [hxy] at h <;> dsimp only at h
  · exact (spec_ok _).2 ⟨h.2.1, h.2.2⟩
  · simp only [inBounds] at h; omega

theorem IScalar.add_bv_spec {ty}  {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x + ↑y)
  (hmax : ↑x + ↑y ≤ IScalar.max ty) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ∧ z.bv = x.bv + y.bv ⦄ := by
  have h := @add_equiv ty x y
  simp only [min, max] at hmin hmax
  rcases hxy : (x + y) with z | e | _ <;> rw [hxy] at h <;> dsimp only at h
  · exact (spec_ok _).2 ⟨h.2.1, h.2.2⟩
  · simp only [inBounds] at h; omega

uscalar theorem «%S».add_bv_spec {x y : «%S»} (hmax : x.val + y.val ≤ «%S».max) :
  x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ∧ z.bv = x.bv + y.bv ⦄ :=
  UScalar.add_bv_spec (by simpa [UScalar.max_USize_eq] using hmax)

iscalar theorem «%S».add_bv_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x + ↑y) (hmax : ↑x + ↑y ≤ «%S».max) :
  x + y ⦃ z => (↑z : Int) = ↑x + ↑y ∧ z.bv = x.bv + y.bv ⦄ :=
  IScalar.add_bv_spec (by simpa [IScalar.min_ISize_eq] using hmin)
    (by simpa [IScalar.max_ISize_eq] using hmax)

theorem UScalar.add_spec {ty} {x y : UScalar ty} :
    partialSpec (x + y)
      (fun z => (↑z : Nat) = ↑x + ↑y)
      (fun | .panic => ↑x + ↑y > UScalar.max ty | _ => False)
      False := by
  have h := @add_equiv ty x y
  have : 0 < 2^ty.numBits := Nat.two_pow_pos _
  rcases hxy : (x + y) with z | e | _ <;> rw [hxy] at h <;> dsimp only at h
  · exact h.2.1
  · obtain ⟨rfl, h⟩ := h
    simp only [partialSpec, inBounds, max] at h ⊢; omega

theorem IScalar.add_spec {ty} {x y : IScalar ty} :
    partialSpec (x + y)
      (fun z => (↑z : Int) = ↑x + ↑y)
      (fun | .panic => ↑x + ↑y < IScalar.min ty ∨ ↑x + ↑y > IScalar.max ty | _ => False)
      False := by
  have h := @add_equiv ty x y
  rcases hxy : (x + y) with z | e | _ <;> rw [hxy] at h <;> dsimp only at h
  · exact h.2.1
  · obtain ⟨rfl, h⟩ := h
    simp only [partialSpec, inBounds, min, max] at h ⊢; omega

uscalar theorem «%S».add_spec {x y : «%S»} :
    partialSpec (x + y)
      (fun z => (↑z : Nat) = ↑x + ↑y)
      (fun | .panic => ↑x + ↑y > «%S».max | _ => False)
      False := by
  have h := @UScalar.add_spec _ x y
  simpa [UScalar.max_USize_eq] using h

iscalar theorem «%S».add_spec {x y : «%S»} :
    partialSpec (x + y)
      (fun z => (↑z : Int) = ↑x + ↑y)
      (fun | .panic => ↑x + ↑y < «%S».min ∨ ↑x + ↑y > «%S».max | _ => False)
      False := by
  have h := @IScalar.add_spec _ x y
  simpa [IScalar.min_ISize_eq, IScalar.max_ISize_eq] using h

/-- Addition through a shared reference. -/
def SharedUScalar.Insts.CoreOpsArithAddUScalarUScalar.add
  {ty : UScalarTy} (x y : UScalar ty) : RustM (UScalar ty) :=
  x + y

theorem SharedUScalar.Insts.CoreOpsArithAddUScalarUScalar.add_spec {ty} {x y : UScalar ty} :
    partialSpec (SharedUScalar.Insts.CoreOpsArithAddUScalarUScalar.add x y)
      (fun z => (↑z : Nat) = ↑x + ↑y)
      (fun | .panic => ↑x + ↑y > UScalar.max ty | _ => False)
      False :=
  UScalar.add_spec

uscalar def «Shared'S».Insts.«CoreOpsArithAdd'S'S».add (x y : «%S») : RustM «%S» :=
  SharedUScalar.Insts.CoreOpsArithAddUScalarUScalar.add x y

uscalar theorem «Shared'S».Insts.«CoreOpsArithAdd'S'S».add_spec {x y : «%S»} :
    partialSpec («Shared'S».Insts.«CoreOpsArithAdd'S'S».add x y)
      (fun z => (↑z : Nat) = ↑x + ↑y)
      (fun | .panic => x.val + y.val > «%S».max | _ => False)
      False := by
  have h := @SharedUScalar.Insts.CoreOpsArithAddUScalarUScalar.add_spec _ x y
  simp only [UScalar.max_UScalarTy_U8_eq, UScalar.max_UScalarTy_U16_eq,
    UScalar.max_UScalarTy_U32_eq, UScalar.max_UScalarTy_U64_eq, UScalar.max_UScalarTy_U128_eq,
    UScalar.max_USize_eq] at h
  exact h

/-!
# Subtraction
-/

/-- Checked subtraction: a panic on underflow. -/
def UScalar.sub {ty : UScalarTy} (x y : UScalar ty) : RustM (UScalar ty) :=
  if x.val < y.val then fail .panic
  else ok ⟨ BitVec.ofNat _ (x.val - y.val) ⟩

/-- Checked subtraction: a panic on overflow. -/
def IScalar.sub {ty : IScalarTy} (x y : IScalar ty) : RustM (IScalar ty) :=
  IScalar.tryMk ty (x.val - y.val)

def UScalar.try_sub {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofRustM (sub x y)

def IScalar.try_sub {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofRustM (sub x y)

instance {ty} : HSub (UScalar ty) (UScalar ty) (RustM (UScalar ty)) where
  hSub x y := UScalar.sub x y

instance {ty} : HSub (IScalar ty) (IScalar ty) (RustM (IScalar ty)) where
  hSub x y := IScalar.sub x y

theorem UScalar.sub_equiv {ty} (x y : UScalar ty) :
  match x - y with
  | ok z =>
    y.val ≤ x.val ∧
    x.val = z.val + y.val ∧
    z.bv = x.bv - y.bv
  | fail e => e = .panic ∧ x.val < y.val
  | _ => False := by
  have : x - y = sub x y := by rfl
  rw [this]
  simp only [sub]
  by_cases h : x.val < y.val
  · simp [h]
  · have hx := x.hBounds
    have hy := y.hBounds
    simp only [h, ↓reduceIte]
    refine ⟨by omega, ?_, ?_⟩
    · simp only [val, BitVec.toNat_ofNat] at *
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · apply BitVec.eq_of_toNat_eq
      simp only [val, BitVec.toNat_ofNat, BitVec.toNat_sub] at *
      rw [Nat.mod_eq_of_lt (by omega)]
      have : 2 ^ ty.numBits - y.bv.toNat + x.bv.toNat = (x.bv.toNat - y.bv.toNat) + 2^ty.numBits := by
        omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem IScalar.sub_equiv {ty} (x y : IScalar ty) :
  match x - y with
  | ok z =>
    IScalar.inBounds ty (x.val - y.val) ∧
    z.val = x.val - y.val ∧
    z.bv = x.bv - y.bv
  | fail e => e = .panic ∧ ¬ (IScalar.inBounds ty (x.val - y.val))
  | _ => False := by
  have : x - y = sub x y := by rfl
  rw [this]
  simp only [sub, tryMk, tryMkOpt, RustM.ofOption]
  by_cases h : -2 ^ (ty.numBits - 1) ≤ x.val - y.val ∧ x.val - y.val < 2 ^ (ty.numBits - 1)
  · simp only [check_bounds, h, decide_true, ↓reduceDIte, ofInt_val_eq, inBounds, true_and]
    apply BitVec.eq_of_toInt_eq
    simp only [BitVec.toInt_sub, bv_toInt_eq, ofInt_val_eq]
    rw [bmod_pow_numBits_eq_of_lt ty _ h.1 h.2]
  · simp [h]

theorem UScalar.sub_bv_spec {ty} {x y : UScalar ty}
  (h : y.val ≤ x.val) :
  x - y ⦃ z => z.val = x.val - y.val ∧ y.val ≤ x.val ∧ z.bv = x.bv - y.bv ⦄ := by
  have h' := @sub_equiv ty x y
  rcases hxy : (x - y) with z | e | _ <;> rw [hxy] at h' <;> dsimp only at h'
  · exact (spec_ok _).2 ⟨by omega, h'.1, h'.2.2⟩
  · omega

theorem IScalar.sub_bv_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x - ↑y)
  (hmax : ↑x - ↑y ≤ IScalar.max ty) :
  x - y ⦃ z => (↑z : Int) = ↑x - ↑y ∧ z.bv = x.bv - y.bv ⦄ := by
  have h := @sub_equiv ty x y
  simp only [min, max] at hmin hmax
  rcases hxy : (x - y) with z | e | _ <;> rw [hxy] at h <;> dsimp only at h
  · exact (spec_ok _).2 ⟨h.2.1, h.2.2⟩
  · simp only [inBounds] at h; omega

uscalar theorem «%S».sub_bv_spec {x y : «%S»} (h : y.val ≤ x.val) :
  x - y ⦃ z => z.val = x.val - y.val ∧ y.val ≤ x.val ∧ z.bv = x.bv - y.bv ⦄ :=
  UScalar.sub_bv_spec h

iscalar theorem «%S».sub_bv_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x - ↑y) (hmax : ↑x - ↑y ≤ «%S».max) :
  x - y ⦃ z => (↑z : Int) = ↑x - ↑y ∧ z.bv = x.bv - y.bv ⦄ :=
  IScalar.sub_bv_spec (by simpa [IScalar.min_ISize_eq] using hmin)
    (by simpa [IScalar.max_ISize_eq] using hmax)

theorem UScalar.sub_spec {ty} {x y : UScalar ty} :
    partialSpec (x - y)
      (fun z => z.val = x.val - y.val ∧ y.val ≤ x.val)
      (fun | .panic => x.val < y.val | _ => False)
      False := by
  have h := @sub_equiv ty x y
  rcases hxy : (x - y) with z | e | _ <;> rw [hxy] at h <;> dsimp only at h
  · exact ⟨by omega, h.1⟩
  · obtain ⟨rfl, h⟩ := h
    exact h

theorem IScalar.sub_spec {ty} {x y : IScalar ty} :
    partialSpec (x - y)
      (fun z => (↑z : Int) = ↑x - ↑y)
      (fun | .panic => ↑x - ↑y < IScalar.min ty ∨ ↑x - ↑y > IScalar.max ty | _ => False)
      False := by
  have h := @sub_equiv ty x y
  rcases hxy : (x - y) with z | e | _ <;> rw [hxy] at h <;> dsimp only at h
  · exact h.2.1
  · obtain ⟨rfl, h⟩ := h
    simp only [partialSpec, inBounds, min, max] at h ⊢; omega

uscalar theorem «%S».sub_spec {x y : «%S»} :
    partialSpec (x - y)
      (fun z => z.val = x.val - y.val ∧ y.val ≤ x.val)
      (fun | .panic => x.val < y.val | _ => False)
      False :=
  @UScalar.sub_spec _ x y

iscalar theorem «%S».sub_spec {x y : «%S»} :
    partialSpec (x - y)
      (fun z => (↑z : Int) = ↑x - ↑y)
      (fun | .panic => ↑x - ↑y < «%S».min ∨ ↑x - ↑y > «%S».max | _ => False)
      False := by
  have h := @IScalar.sub_spec _ x y
  simpa [IScalar.min_ISize_eq, IScalar.max_ISize_eq] using h

/-!
# Multiplication
-/

/-- Checked multiplication: a panic on overflow. -/
def UScalar.mul {ty : UScalarTy} (x y : UScalar ty) : RustM (UScalar ty) :=
  UScalar.tryMk ty (x.val * y.val)

/-- Checked multiplication: a panic on overflow. -/
def IScalar.mul {ty : IScalarTy} (x y : IScalar ty) : RustM (IScalar ty) :=
  IScalar.tryMk ty (x.val * y.val)

def UScalar.try_mul {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofRustM (mul x y)

def IScalar.try_mul {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofRustM (mul x y)

instance {ty} : HMul (UScalar ty) (UScalar ty) (RustM (UScalar ty)) where
  hMul x y := UScalar.mul x y

instance {ty} : HMul (IScalar ty) (IScalar ty) (RustM (IScalar ty)) where
  hMul x y := IScalar.mul x y

theorem UScalar.mul_equiv {ty} (x y : UScalar ty) :
  match mul x y with
  | ok z => x.val * y.val ≤ UScalar.max ty ∧ (↑z : Nat) = ↑x * ↑y ∧ z.bv = x.bv * y.bv
  | fail e => e = .panic ∧ UScalar.max ty < x.val * y.val
  | .div => False := by
  have : 0 < 2^ty.numBits := Nat.two_pow_pos _
  simp only [mul, tryMk, tryMkOpt, RustM.ofOption, max]
  by_cases h : x.val * y.val < 2^ty.numBits
  · simp only [check_bounds, h, decide_true, ↓reduceDIte, ofNatCore_val_eq, true_and]
    refine ⟨by omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [ofNatCore, BitVec.toNat_mul, BitVec.toNat_ofFin, UScalar.val] at h ⊢
    rw [Nat.mod_eq_of_lt h]
  · simp [h]
    omega

theorem UScalar.mul_bv_spec {ty} {x y : UScalar ty}
  (hmax : ↑x * ↑y ≤ UScalar.max ty) :
  x * y ⦃ z => (↑z : Nat) = ↑x * ↑y ∧ z.bv = x.bv * y.bv ⦄ := by
  have h := mul_equiv x y
  show spec (mul x y) _
  rcases hxy : (mul x y) with z | e | _ <;> rw [hxy] at h <;> dsimp only at h
  · exact (spec_ok _).2 ⟨h.2.1, h.2.2⟩
  · omega

theorem IScalar.mul_equiv {ty} (x y : IScalar ty) :
  match mul x y with
  | ok z => IScalar.min ty ≤ x.val * y.val ∧ x.val * y.val ≤ IScalar.max ty ∧
    z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | fail e => e = .panic ∧ ¬(IScalar.min ty ≤ x.val * y.val ∧ x.val * y.val ≤ IScalar.max ty)
  | .div => False := by
  simp only [mul, tryMk, tryMkOpt, RustM.ofOption, min, max]
  by_cases h : -2 ^ (ty.numBits - 1) ≤ x.val * y.val ∧ x.val * y.val < 2 ^ (ty.numBits - 1)
  · simp only [check_bounds, h, decide_true, ↓reduceDIte, ofInt_val_eq, true_and]
    refine ⟨by omega, ?_⟩
    apply BitVec.eq_of_toInt_eq
    simp only [BitVec.toInt_mul, bv_toInt_eq, ofInt_val_eq]
    rw [bmod_pow_numBits_eq_of_lt ty _ h.1 h.2]
  · simp [h]
    omega

theorem IScalar.mul_bv_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ IScalar.max ty) :
  x * y ⦃ z => (↑z : Int) = ↑x * ↑y ∧ z.bv = x.bv * y.bv ⦄ := by
  have h := mul_equiv x y
  show spec (mul x y) _
  rcases hxy : (mul x y) with z | e | _ <;> rw [hxy] at h <;> dsimp only at h
  · exact (spec_ok _).2 ⟨h.2.2.1, h.2.2.2⟩
  · exact absurd ⟨hmin, hmax⟩ h.2

uscalar theorem «%S».mul_bv_spec {x y : «%S»} (hmax : x.val * y.val ≤ «%S».max) :
  x * y ⦃ z => (↑z : Nat) = ↑x * ↑y ∧ z.bv = x.bv * y.bv ⦄ :=
  UScalar.mul_bv_spec (by simpa [UScalar.max_USize_eq] using hmax)

iscalar theorem «%S».mul_bv_spec {x y : «%S»}
  (hmin : «%S».min ≤ ↑x * ↑y) (hmax : ↑x * ↑y ≤ «%S».max) :
  x * y ⦃ z => (↑z : Int) = ↑x * ↑y ∧ z.bv = x.bv * y.bv ⦄ :=
  IScalar.mul_bv_spec (by simpa [IScalar.min_ISize_eq] using hmin)
    (by simpa [IScalar.max_ISize_eq] using hmax)

theorem UScalar.mul_spec {ty} {x y : UScalar ty}
  (hmax : ↑x * ↑y ≤ UScalar.max ty) :
  x * y ⦃ z => (↑z : Nat) = ↑x * ↑y ⦄ :=
  spec_mono (mul_bv_spec hmax) (fun _ h => h.1)

theorem IScalar.mul_spec {ty} {x y : IScalar ty}
  (hmin : IScalar.min ty ≤ ↑x * ↑y)
  (hmax : ↑x * ↑y ≤ IScalar.max ty) :
  x * y ⦃ z => (↑z : Int) = ↑x * ↑y ⦄ :=
  spec_mono (mul_bv_spec hmin hmax) (fun _ h => h.1)

uscalar theorem «%S».mul_spec {x y : «%S»} :
    partialSpec (x * y)
      (fun z => (↑z : Nat) = ↑x * ↑y)
      (fun | .panic => ↑x * ↑y > «%S».max | _ => False)
      False := by
  show partialSpec (UScalar.mul x y) _ _ _
  have h := UScalar.mul_equiv x y
  simp only [UScalar.max_UScalarTy_U8_eq, UScalar.max_UScalarTy_U16_eq,
    UScalar.max_UScalarTy_U32_eq, UScalar.max_UScalarTy_U64_eq, UScalar.max_UScalarTy_U128_eq,
    UScalar.max_USize_eq] at h
  rcases hxy : (UScalar.mul x y) with z | e | _ <;> rw [hxy] at h <;> dsimp only at h
  · exact h.2.1
  · obtain ⟨rfl, h⟩ := h
    exact h

iscalar theorem «%S».mul_spec {x y : «%S»} :
    partialSpec (x * y)
      (fun z => (↑z : Int) = ↑x * ↑y)
      (fun | .panic => ↑x * ↑y < «%S».min ∨ ↑x * ↑y > «%S».max | _ => False)
      False := by
  show partialSpec (IScalar.mul x y) _ _ _
  have h := IScalar.mul_equiv x y
  simp only [IScalar.min_IScalarTy_I8_eq, IScalar.max_IScalarTy_I8_eq,
    IScalar.min_IScalarTy_I16_eq, IScalar.max_IScalarTy_I16_eq,
    IScalar.min_IScalarTy_I32_eq, IScalar.max_IScalarTy_I32_eq,
    IScalar.min_IScalarTy_I64_eq, IScalar.max_IScalarTy_I64_eq,
    IScalar.min_IScalarTy_I128_eq, IScalar.max_IScalarTy_I128_eq,
    IScalar.min_ISize_eq, IScalar.max_ISize_eq] at h
  rcases hxy : (IScalar.mul x y) with z | e | _ <;> rw [hxy] at h <;> dsimp only at h
  · exact h.2.2.1
  · obtain ⟨rfl, h⟩ := h
    show _ ∨ _
    omega

/-!
# Division

Division on signed integers truncates towards zero (`Int.tdiv`).
-/

/-- Checked unsigned division: a panic on a zero divisor. -/
def UScalar.div {ty : UScalarTy} (x y : UScalar ty) : RustM (UScalar ty) :=
  if y.bv != 0 then ok ⟨ BitVec.udiv x.bv y.bv ⟩ else fail panic

/-- Checked signed division: a panic on a zero divisor and on `MIN / -1`. -/
def IScalar.div {ty : IScalarTy} (x y : IScalar ty): RustM (IScalar ty) :=
  if y.val != 0 then
    if ¬ (x.val = IScalar.min ty && y.val = -1) then ok ⟨ BitVec.sdiv x.bv y.bv ⟩
    else fail panic
  else fail panic

def UScalar.try_div {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofRustM (div x y)

def IScalar.try_div {ty : IScalarTy} (x y : IScalar ty): Option (IScalar ty) :=
  Option.ofRustM (div x y)

instance {ty} : HDiv (UScalar ty) (UScalar ty) (RustM (UScalar ty)) where
  hDiv x y := UScalar.div x y

instance {ty} : HDiv (IScalar ty) (IScalar ty) (RustM (IScalar ty)) where
  hDiv x y := IScalar.div x y

theorem UScalar.div_bv_spec {ty} (x : UScalar ty) {y : UScalar ty}
  (hzero : y.val ≠ 0) :
  ∃ z, x / y = ok z ∧ (↑z : Nat) = ↑x / ↑y ∧ z.bv = x.bv / y.bv := by
  have hzero' : y.bv ≠ 0 := by
    intro h
    apply hzero
    show y.bv.toNat = 0
    rw [h]; rfl
  refine ⟨⟨BitVec.udiv x.bv y.bv⟩, ?_, ?_, BitVec.udiv_eq _ _⟩
  · show div x y = _
    simp only [div, bne_iff_ne, ne_eq, hzero', not_false_eq_true, ↓reduceIte]
  · show (BitVec.udiv x.bv y.bv).toNat = x.bv.toNat / y.bv.toNat
    rw [BitVec.udiv_eq, BitVec.toNat_udiv]

/-- `2^(n-1)` wraps to `-2^(n-1)` modulo `2^n`. -/
theorem Int.bmod_pow2_IScalarTy_numBits_minus_one (ty : IScalarTy) :
  Int.bmod (2 ^ (ty.numBits - 1)) (2 ^ ty.numBits) = - 2 ^ (ty.numBits - 1) := by
  have hn := ty.numBits_nonzero
  have hp : ((2 ^ ty.numBits : Nat) : Int) = 2 * (2 ^ (ty.numBits - 1) : Int) := by
    rw [Int.natCast_pow]
    have : ty.numBits = ty.numBits - 1 + 1 := by omega
    conv => lhs; rw [this]
    rw [Int.pow_succ]; simp [Int.mul_comm]
  have hpos : (0 : Int) < 2 ^ (ty.numBits - 1) := Int.pow_pos (by decide)
  rw [Int.bmod_def, hp, Int.emod_eq_of_lt (by omega) (by omega)]
  simp only [show ¬ ((2 : Int) ^ (ty.numBits - 1) < (2 * 2 ^ (ty.numBits - 1) + 1) / 2) by omega,
    ↓reduceIte]
  omega

theorem IScalar.div_bv_spec {ty} {x y : IScalar ty}
  (hzero : y.val ≠ 0) (hNoOverflow : ¬ (x.val = IScalar.min ty ∧ y.val = -1)) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = Int.tdiv ↑x ↑y ∧ z.bv = BitVec.sdiv x.bv y.bv := by
  refine ⟨⟨BitVec.sdiv x.bv y.bv⟩, ?_, ?_, rfl⟩
  · show div x y = _
    simp only [div, bne_iff_ne, ne_eq, hzero, not_false_eq_true, ↓reduceIte,
      Bool.and_eq_true, decide_eq_true_eq, hNoOverflow]
  · show (BitVec.sdiv x.bv y.bv).toInt = x.bv.toInt.tdiv y.bv.toInt
    rw [BitVec.toInt_sdiv]
    have hmin : IScalar.min ty = -2^(ty.numBits-1) := by rw [IScalar.min]
    have hzero : y.bv.toInt ≠ 0 := hzero
    have hNo : ¬ (x.bv.toInt = -2^(ty.numBits-1) ∧ y.bv.toInt = -1) := by
      rw [← hmin]; exact hNoOverflow
    have hx : -2^(ty.numBits-1) ≤ x.bv.toInt ∧ x.bv.toInt < 2^(ty.numBits-1) := IScalar.hBounds x
    generalize x.bv.toInt = a at *
    generalize y.bv.toInt = b at *
    have hq : (a.tdiv b).natAbs = a.natAbs / b.natAbs := Int.natAbs_tdiv a b
    have hP : (0:Int) < 2^(ty.numBits-1) := Int.pow_pos (by decide)
    have hcast : ((2 ^ (ty.numBits - 1) : Nat) : Int) = (2 : Int) ^ (ty.numBits - 1) := by simp
    have hd : 2 ≤ b.natAbs → a.natAbs / b.natAbs ≤ a.natAbs / 2 := fun h2 =>
      Nat.div_le_div_left h2 (by decide)
    clear hNoOverflow
    by_cases hb1 : b = 1
    · subst hb1; rw [Int.tdiv_one]; exact bmod_pow_numBits_eq_of_lt ty a hx.1 hx.2
    · by_cases hbm : b = -1
      · subst hbm; rw [Int.tdiv_neg, Int.tdiv_one]
        apply bmod_pow_numBits_eq_of_lt <;> omega
      · have := hd (by omega)
        apply bmod_pow_numBits_eq_of_lt <;> omega

uscalar theorem «%S».div_bv_spec (x : «%S») {y : «%S»} (hnz : ↑y ≠ (0 : Nat)) :
  x / y ⦃ z => (↑z : Nat) = ↑x / ↑y ∧ z.bv = x.bv / y.bv ⦄ :=
  exists_imp_spec (UScalar.div_bv_spec x hnz)

iscalar theorem «%S».div_bv_spec {x y : «%S»} (hnz : ↑y ≠ (0 : Int))
  (hNoOverflow : ¬ (x.val = «%S».min ∧ y.val = -1)) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = Int.tdiv ↑x ↑y ∧ z.bv = BitVec.sdiv x.bv y.bv :=
  IScalar.div_bv_spec hnz (by simpa [IScalar.min_ISize_eq] using hNoOverflow)

theorem UScalar.div_spec {ty} (x : UScalar ty) {y : UScalar ty}
  (hzero : y.val ≠ 0) :
  ∃ z, x / y = ok z ∧ (↑z : Nat) = ↑x / ↑y := by
  have ⟨ z, hz ⟩ := UScalar.div_bv_spec x hzero
  exact ⟨z, hz.1, hz.2.1⟩

theorem IScalar.div_spec {ty} {x y : IScalar ty}
  (hzero : y.val ≠ 0)
  (hNoOverflow : ¬ (x.val = IScalar.min ty ∧ y.val = -1)) :
  ∃ z, x / y = ok z ∧ (↑z : Int) = Int.tdiv ↑x ↑y := by
  have ⟨ z, hz ⟩ := IScalar.div_bv_spec hzero hNoOverflow
  exact ⟨z, hz.1, hz.2.1⟩

uscalar theorem «%S».div_spec (x : «%S») {y : «%S»} :
    partialSpec (x / y)
      (fun z => (↑z : Nat) = ↑x / ↑y)
      (fun | .panic => (↑y : Nat) = 0 | _ => False)
      False := by
  have hxy : (x / y : RustM _) = UScalar.div x y := rfl
  by_cases hy : y.val = 0
  · have hbv : y.bv = 0 := by
      apply BitVec.eq_of_toNat_eq; exact hy
    rw [hxy]
    simp only [partialSpec, UScalar.div, hbv, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte]
    exact hy
  · have ⟨ z, hz, hzVal ⟩ := UScalar.div_spec x hy
    rw [hz]
    simp [partialSpec, hzVal]

iscalar theorem «%S».div_spec {x y : «%S»} :
    partialSpec (x / y)
      (fun z => (↑z : Int) = Int.tdiv ↑x ↑y)
      (fun | .panic => ((↑y : Int) = 0) ∨ ((↑x : Int) = «%S».min ∧ (↑y : Int) = -1)
           | _ => False)
      False := by
  have hxy : (x / y : RustM _) = IScalar.div x y := rfl
  by_cases hy : y.val = 0
  · rw [hxy]; simp [partialSpec, IScalar.div, hy]
  · by_cases ho : x.val = IScalar.min (IScalarTy.«%S») ∧ y.val = -1
    · rw [hxy]
      simp [partialSpec, IScalar.div, ho.1, ho.2, IScalar.min_ISize_eq]
    · have ⟨ z, hz, hzVal ⟩ := IScalar.div_spec hy ho
      rw [hz]
      simp [partialSpec, hzVal]

/-!
# Remainder

The remainder on signed integers has the sign of the dividend (`Int.tmod`). A zero divisor
and `MIN % -1` panic.
-/

/-- Checked unsigned remainder: a panic on a zero divisor. -/
def UScalar.rem {ty : UScalarTy} (x y : UScalar ty) : RustM (UScalar ty) :=
  if y.val != 0 then ok ⟨ BitVec.umod x.bv y.bv ⟩ else fail panic

/-- Checked signed remainder: a panic on a zero divisor and on `MIN % -1`. -/
def IScalar.rem {ty : IScalarTy} (x y : IScalar ty) : RustM (IScalar ty) :=
  if y.val != 0 then
    if ¬ (x.val = IScalar.min ty && y.val = -1) then ok ⟨ BitVec.srem x.bv y.bv ⟩
    else fail panic
  else fail panic

def UScalar.try_rem {ty : UScalarTy} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofRustM (rem x y)

def IScalar.try_rem {ty : IScalarTy} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofRustM (rem x y)

instance {ty} : HMod (UScalar ty) (UScalar ty) (RustM (UScalar ty)) where
  hMod x y := UScalar.rem x y

instance {ty} : HMod (IScalar ty) (IScalar ty) (RustM (IScalar ty)) where
  hMod x y := IScalar.rem x y

theorem UScalar.rem_bv_spec {ty} (x : UScalar ty) {y : UScalar ty} (hzero : y.val ≠ 0) :
  x % y ⦃ z => (↑z : Nat) = ↑x % ↑y ∧ z.bv = x.bv % y.bv ⦄ := by
  have : x % y = rem x y := rfl
  rw [this]
  simp only [rem, bne_iff_ne, ne_eq, hzero, not_false_eq_true, ↓reduceIte, spec_ok]
  simp only [val, BitVec.umod_eq, BitVec.toNat_umod, and_self]

theorem IScalar.rem_bv_spec {ty} (x : IScalar ty) {y : IScalar ty} (hzero : y.val ≠ 0)
  (hNoOverflow : ¬ (x.val = IScalar.min ty ∧ y.val = -1)) :
  x % y ⦃ z => (↑z : Int) = Int.tmod ↑x ↑y ∧ z.bv = BitVec.srem x.bv y.bv ⦄ := by
  have : x % y = rem x y := rfl
  rw [this]
  simp only [spec_ok, rem, bne_iff_ne, ne_eq, hzero, not_false_eq_true, ↓reduceIte,
    Bool.and_eq_true, decide_eq_true_eq, hNoOverflow]
  simp only [val]
  simp only [BitVec.toInt_srem, and_true]

uscalar theorem «%S».rem_bv_spec (x : «%S») {y : «%S»} (hnz : y.val ≠ 0) :
  x % y ⦃ z => (↑z : Nat) = ↑x % ↑y ∧ z.bv = x.bv % y.bv ⦄ :=
  UScalar.rem_bv_spec x hnz

iscalar theorem «%S».rem_bv_spec (x : «%S») {y : «%S»} (hnz : y.val ≠ 0)
  (hNoOverflow : ¬ (x.val = «%S».min ∧ y.val = -1)) :
  x % y ⦃ z => (↑z : Int) = Int.tmod ↑x ↑y ∧ z.bv = BitVec.srem x.bv y.bv ⦄ :=
  IScalar.rem_bv_spec x hnz (by simpa [IScalar.min_ISize_eq] using hNoOverflow)

theorem UScalar.rem_spec {ty} (x : UScalar ty) {y : UScalar ty} (hzero : y.val ≠ 0) :
  x % y ⦃ z => (↑z : Nat) = ↑x % ↑y ⦄ := by
  apply spec_mono
  · apply rem_bv_spec x hzero
  · intros x' h
    exact h.1

theorem IScalar.rem_spec {ty} (x : IScalar ty) {y : IScalar ty} (hzero : y.val ≠ 0)
  (hNoOverflow : ¬ (x.val = IScalar.min ty ∧ y.val = -1)) :
  x % y ⦃ z => (↑z : Int) = Int.tmod ↑x ↑y ⦄ := by
  apply spec_mono
  · apply rem_bv_spec x hzero hNoOverflow
  · intros x' h
    exact h.1

uscalar theorem «%S».rem_spec (x : «%S») {y : «%S»} :
    partialSpec (x % y)
      (fun z => (↑z : Nat) = ↑x % ↑y)
      (fun | .panic => (↑y : Nat) = 0 | _ => False)
      False := by
  have hxy : (x % y : RustM _) = UScalar.rem x y := rfl
  by_cases hy : y.val = 0
  · rw [hxy]; simp [partialSpec, UScalar.rem, hy]
  · have ⟨z, hz, hzv⟩ := spec_imp_exists (UScalar.rem_spec x hy)
    rw [hz]
    simp [partialSpec, hzv]

iscalar theorem «%S».rem_spec (x : «%S») {y : «%S»} :
    partialSpec (x % y)
      (fun z => (↑z : Int) = Int.tmod ↑x ↑y)
      (fun | .panic => ((↑y : Int) = 0) ∨ ((↑x : Int) = «%S».min ∧ (↑y : Int) = -1)
           | _ => False)
      False := by
  have hxy : (x % y : RustM _) = IScalar.rem x y := rfl
  by_cases hy : y.val = 0
  · rw [hxy]; simp [partialSpec, IScalar.rem, hy]
  · by_cases ho : x.val = IScalar.min (IScalarTy.«%S») ∧ y.val = -1
    · rw [hxy]
      simp [partialSpec, IScalar.rem, ho.1, ho.2, IScalar.min_ISize_eq]
    · have ⟨z, hz, hzv⟩ := spec_imp_exists (IScalar.rem_spec x hy ho)
      rw [hz]
      simp [partialSpec, hzv]

/-!
# Negation
-/

/-- Checked negation: a panic on `MIN`. -/
def IScalar.neg {ty : IScalarTy} (x : IScalar ty) : RustM (IScalar ty) :=
  IScalar.tryMk ty (- x.val)

theorem IScalar.neg_step {ty} (x: IScalar ty) :
    partialSpec (IScalar.neg x)
      (fun r => r = -x.val)
      (fun | .panic => (x : Int) = IScalar.min ty | _ => False)
      False := by
  have := IScalar.hBounds x
  simp only [neg, tryMk, tryMkOpt, IScalar.min, check_bounds, decide_eq_true_eq]
  by_cases h : -2 ^ (ty.numBits - 1) ≤ -x.val ∧ -x.val < 2 ^ (ty.numBits - 1)
  · rw [dif_pos h]; simp [partialSpec]
  · rw [dif_neg h]; simp only [partialSpec, RustM.ofOption]; omega

/-- Heterogeneous negation: `-. a`. -/
class HNeg (α : Type u) (β : outParam (Type v)) where
  /-- `-. a` computes the negation of `a`. -/
  hNeg : α → β

/-- Heterogeneous negation notation. -/
prefix:75  "-."   => HNeg.hNeg

attribute [match_pattern] HNeg.hNeg

instance {ty} : HNeg (IScalar ty) (RustM (IScalar ty)) where hNeg x := IScalar.neg x

theorem HNeg.hNeg.step {ty} (x: IScalar ty) :
    partialSpec (HNeg.hNeg x : RustM (IScalar ty))
      (fun r => r = -x.val)
      (fun | .panic => (x : Int) = IScalar.min ty | _ => False)
      False := by
  show partialSpec (IScalar.neg x) _ _ _
  exact IScalar.neg_step x

end Aeneas.Std

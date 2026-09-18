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
  backends/lean/Aeneas/Std/Scalar/CheckedOps/Add.lean
  backends/lean/Aeneas/Std/Scalar/CheckedOps/Sub.lean
  backends/lean/Aeneas/Std/Scalar/CheckedOps/Mul.lean
  backends/lean/Aeneas/Std/Scalar/CheckedOps/Div.lean
  backends/lean/Aeneas/Std/Scalar/CheckedOps/Rem.lean
-/

module

public import HaxLean.Rust.Scalar.Ops
public import HaxLean.Rust.Scalar.Elab

/-!
# Checked arithmetic

`checked_add`, `checked_sub`, `checked_mul`, `checked_div` and `checked_rem`: `some` of
the result when the corresponding `RustM` operation succeeds, `none` otherwise.
-/

@[expose] public section

set_option autoImplicit false

namespace Aeneas.Std

open RustM Error Arith ScalarElab WP

/-- The bounds of the concrete scalar types in place of `UScalar.max .U8`, … -/
local macro "simp_scalar_bounds" : tactic =>
  `(tactic| simp only [UScalar.max_UScalarTy_U8_eq, UScalar.max_UScalarTy_U16_eq,
    UScalar.max_UScalarTy_U32_eq, UScalar.max_UScalarTy_U64_eq, UScalar.max_UScalarTy_U128_eq,
    UScalar.max_USize_eq,
    IScalar.min_IScalarTy_I8_eq, IScalar.max_IScalarTy_I8_eq,
    IScalar.min_IScalarTy_I16_eq, IScalar.max_IScalarTy_I16_eq,
    IScalar.min_IScalarTy_I32_eq, IScalar.max_IScalarTy_I32_eq,
    IScalar.min_IScalarTy_I64_eq, IScalar.max_IScalarTy_I64_eq,
    IScalar.min_IScalarTy_I128_eq, IScalar.max_IScalarTy_I128_eq,
    IScalar.min_ISize_eq, IScalar.max_ISize_eq] at *)

/-- Transfer a generic `match`-shaped specification `spec` of `e` to a concrete scalar type. -/
local macro "checked_transfer " spec:term ", " e:term : tactic =>
  `(tactic| (have h := $spec; revert h; generalize $e = r; cases r <;> intro h <;>
      dsimp only at h ⊢ <;> (try simp_scalar_bounds) <;> exact h))

/-!
# Checked addition
-/

/- [core::num::{T}::checked_add] -/
def core.num.checked_add_UScalar {ty} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofRustM (x + y)

uscalar def «%S».checked_add (x y : «%S») : Option «%S» := core.num.checked_add_UScalar x y

/- [core::num::{T}::checked_add] -/
def core.num.checked_add_IScalar {ty} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofRustM (x + y)

iscalar def «%S».checked_add (x y : «%S») : Option «%S» := core.num.checked_add_IScalar x y

theorem core.num.checked_add_UScalar_bv_spec {ty} (x y : UScalar ty) :
  match core.num.checked_add_UScalar x y with
  | some z => x.val + y.val ≤ UScalar.max ty ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => UScalar.max ty < x.val + y.val := by
  have h := UScalar.add_equiv x y
  have : 0 < 2^ty.numBits := Nat.two_pow_pos _
  simp only [checked_add_UScalar, UScalar.max]
  rcases hxy : (x + y) with z | e | _ <;> rw [hxy] at h <;> dsimp only at h <;>
    simp only [Option.ofRustM]
  · exact ⟨by omega, h.2.1, h.2.2⟩
  · simp only [UScalar.inBounds] at h; omega

uscalar theorem «%S».checked_add_bv_spec (x y : «%S») :
  match «%S».checked_add x y with
  | some z => x.val + y.val ≤ «%S».max ∧ z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => «%S».max < x.val + y.val := by
  simp only [«%S».checked_add]
  checked_transfer core.num.checked_add_UScalar_bv_spec x y, core.num.checked_add_UScalar x y

theorem core.num.checked_add_IScalar_bv_spec {ty} (x y : IScalar ty) :
  match core.num.checked_add_IScalar x y with
  | some z => IScalar.min ty ≤ x.val + y.val ∧ x.val + y.val ≤ IScalar.max ty ∧
    z.val = x.val + y.val ∧ z.bv = x.bv + y.bv
  | none => ¬ (IScalar.min ty ≤ x.val + y.val ∧ x.val + y.val ≤ IScalar.max ty) := by
  have h := IScalar.add_equiv x y
  simp only [checked_add_IScalar, IScalar.min, IScalar.max]
  rcases hxy : (x + y) with z | e | _ <;> rw [hxy] at h <;> dsimp only at h <;>
    simp only [Option.ofRustM]
  · simp only [IScalar.inBounds] at h; exact ⟨by omega, by omega, h.2.1, h.2.2⟩
  · simp only [IScalar.inBounds] at h; omega

iscalar theorem «%S».checked_add_bv_spec (x y : «%S») :
  match core.num.checked_add_IScalar x y with
  | some z => «%S».min ≤ x.val + y.val ∧ x.val + y.val ≤ «%S».max ∧ z.val = x.val + y.val ∧
    z.bv = x.bv + y.bv
  | none => ¬ («%S».min ≤ x.val + y.val ∧ x.val + y.val ≤ «%S».max) := by
  checked_transfer core.num.checked_add_IScalar_bv_spec x y, core.num.checked_add_IScalar x y

/-!
# Checked subtraction
-/

/- [core::num::{T}::checked_sub] -/
def core.num.checked_sub_UScalar {ty} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofRustM (x - y)

uscalar def «%S».checked_sub (x y : «%S») : Option «%S» := core.num.checked_sub_UScalar x y

/- [core::num::{T}::checked_sub] -/
def core.num.checked_sub_IScalar {ty} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofRustM (x - y)

iscalar def «%S».checked_sub (x y : «%S») : Option «%S» := core.num.checked_sub_IScalar x y

theorem core.num.checked_sub_UScalar_bv_spec {ty} (x y : UScalar ty) :
  match core.num.checked_sub_UScalar x y with
  | some z => y.val ≤ x.val ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv
  | none => x.val < y.val := by
  have h := UScalar.sub_equiv x y
  simp only [checked_sub_UScalar]
  rcases hxy : (x - y) with z | e | _ <;> rw [hxy] at h <;> dsimp only at h <;>
    simp only [Option.ofRustM]
  · exact ⟨h.1, by omega, h.2.2⟩
  · exact h.2

uscalar theorem «%S».checked_sub_bv_spec (x y : «%S») :
  match «%S».checked_sub x y with
  | some z => y.val ≤ x.val ∧ z.val = x.val - y.val ∧ z.bv = x.bv - y.bv
  | none => x.val < y.val := by
  simp only [«%S».checked_sub]
  checked_transfer core.num.checked_sub_UScalar_bv_spec x y, core.num.checked_sub_UScalar x y

theorem core.num.checked_sub_IScalar_bv_spec {ty} (x y : IScalar ty) :
  match core.num.checked_sub_IScalar x y with
  | some z => IScalar.min ty ≤ x.val - y.val ∧ x.val - y.val ≤ IScalar.max ty ∧
    z.val = x.val - y.val ∧ z.bv = x.bv - y.bv
  | none => ¬ (IScalar.min ty ≤ x.val - y.val ∧ x.val - y.val ≤ IScalar.max ty) := by
  have h := IScalar.sub_equiv x y
  simp only [checked_sub_IScalar, IScalar.min, IScalar.max]
  rcases hxy : (x - y) with z | e | _ <;> rw [hxy] at h <;> dsimp only at h <;>
    simp only [Option.ofRustM]
  · simp only [IScalar.inBounds] at h; exact ⟨by omega, by omega, h.2.1, h.2.2⟩
  · simp only [IScalar.inBounds] at h; omega

iscalar theorem «%S».checked_sub_bv_spec (x y : «%S») :
  match core.num.checked_sub_IScalar x y with
  | some z => «%S».min ≤ x.val - y.val ∧ x.val - y.val ≤ «%S».max ∧ z.val = x.val - y.val ∧
    z.bv = x.bv - y.bv
  | none => ¬ («%S».min ≤ x.val - y.val ∧ x.val - y.val ≤ «%S».max) := by
  checked_transfer core.num.checked_sub_IScalar_bv_spec x y, core.num.checked_sub_IScalar x y

/-!
# Checked multiplication
-/

/- [core::num::{T}::checked_mul] -/
def core.num.checked_mul_UScalar {ty} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofRustM (UScalar.mul x y)

uscalar def «%S».checked_mul (x y : «%S») : Option «%S» := core.num.checked_mul_UScalar x y

/- [core::num::{T}::checked_mul] -/
def core.num.checked_mul_IScalar {ty} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofRustM (IScalar.mul x y)

iscalar def «%S».checked_mul (x y : «%S») : Option «%S» := core.num.checked_mul_IScalar x y

theorem core.num.checked_mul_UScalar_bv_spec {ty} (x y : UScalar ty) :
  match core.num.checked_mul_UScalar x y with
  | some z => x.val * y.val ≤ UScalar.max ty ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => UScalar.max ty < x.val * y.val := by
  have h := UScalar.mul_equiv x y
  simp only [checked_mul_UScalar]
  rcases hxy : (UScalar.mul x y) with z | e | _ <;> rw [hxy] at h <;> dsimp only at h <;>
    simp only [Option.ofRustM]
  · exact h
  · exact h.2

uscalar theorem «%S».checked_mul_bv_spec (x y : «%S») :
  match «%S».checked_mul x y with
  | some z => x.val * y.val ≤ «%S».max ∧ z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => «%S».max < x.val * y.val := by
  simp only [«%S».checked_mul]
  checked_transfer core.num.checked_mul_UScalar_bv_spec x y, core.num.checked_mul_UScalar x y

theorem core.num.checked_mul_IScalar_bv_spec {ty} (x y : IScalar ty) :
  match core.num.checked_mul_IScalar x y with
  | some z => IScalar.min ty ≤ x.val * y.val ∧ x.val * y.val ≤ IScalar.max ty ∧
    z.val = x.val * y.val ∧ z.bv = x.bv * y.bv
  | none => ¬ (IScalar.min ty ≤ x.val * y.val ∧ x.val * y.val ≤ IScalar.max ty) := by
  have h := IScalar.mul_equiv x y
  simp only [checked_mul_IScalar]
  rcases hxy : (IScalar.mul x y) with z | e | _ <;> rw [hxy] at h <;> dsimp only at h <;>
    simp only [Option.ofRustM]
  · exact h
  · exact h.2

iscalar theorem «%S».checked_mul_bv_spec (x y : «%S») :
  match core.num.checked_mul_IScalar x y with
  | some z => «%S».min ≤ x.val * y.val ∧ x.val * y.val ≤ «%S».max ∧ z.val = x.val * y.val ∧
    z.bv = x.bv * y.bv
  | none => ¬ («%S».min ≤ x.val * y.val ∧ x.val * y.val ≤ «%S».max) := by
  checked_transfer core.num.checked_mul_IScalar_bv_spec x y, core.num.checked_mul_IScalar x y

/-!
# Checked division
-/

/- [core::num::{T}::checked_div] -/
def core.num.checked_div_UScalar {ty} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofRustM (UScalar.div x y)

uscalar def «%S».checked_div (x y : «%S») : Option «%S» := core.num.checked_div_UScalar x y

/- [core::num::{T}::checked_div] -/
def core.num.checked_div_IScalar {ty} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofRustM (IScalar.div x y)

iscalar def «%S».checked_div (x y : «%S») : Option «%S» := core.num.checked_div_IScalar x y

theorem core.num.checked_div_UScalar_bv_spec {ty} (x y : UScalar ty) :
  match core.num.checked_div_UScalar x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val / y.val ∧ z.bv = x.bv / y.bv
  | none => y.val = 0 := by
  simp only [checked_div_UScalar]
  by_cases hy : y.val = 0
  · have hbv : y.bv = 0 := BitVec.eq_of_toNat_eq hy
    simp only [UScalar.div, hbv, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      Option.ofRustM]
    exact hy
  · have ⟨z, hz, h1, h2⟩ := UScalar.div_bv_spec x hy
    have : x / y = UScalar.div x y := rfl
    rw [← this, hz]
    exact ⟨hy, h1, h2⟩

uscalar theorem «%S».checked_div_bv_spec (x y : «%S») :
  match «%S».checked_div x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val / y.val ∧ z.bv = x.bv / y.bv
  | none => y.val = 0 := by
  simp only [«%S».checked_div]
  checked_transfer core.num.checked_div_UScalar_bv_spec x y, core.num.checked_div_UScalar x y

theorem core.num.checked_div_IScalar_bv_spec {ty} (x y : IScalar ty) :
  match core.num.checked_div_IScalar x y with
  | some z => y.val ≠ 0 ∧ ¬ (x.val = IScalar.min ty ∧ y.val = -1) ∧
    z.val = Int.tdiv x.val y.val ∧ z.bv = BitVec.sdiv x.bv y.bv
  | none => y.val = 0 ∨ (x.val = IScalar.min ty ∧ y.val = -1) := by
  simp only [checked_div_IScalar]
  by_cases hy : y.val = 0
  · simp only [IScalar.div, hy, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      Option.ofRustM, true_or]
  · by_cases ho : x.val = IScalar.min ty ∧ y.val = -1
    · simp only [IScalar.div, ho.1, ho.2, bne_iff_ne, ne_eq, and_self, decide_true,
        Bool.and_self, not_true_eq_false, ↓reduceIte, Option.ofRustM, or_true]
      simp_all
    · have ⟨z, hz, h1, h2⟩ := IScalar.div_bv_spec hy ho
      have : x / y = IScalar.div x y := rfl
      rw [← this, hz]
      exact ⟨hy, ho, h1, h2⟩

iscalar theorem «%S».checked_div_bv_spec (x y : «%S») :
  match core.num.checked_div_IScalar x y with
  | some z => y.val ≠ 0 ∧ ¬ (x.val = «%S».min ∧ y.val = -1) ∧ z.val = Int.tdiv x.val y.val ∧
    z.bv = BitVec.sdiv x.bv y.bv
  | none => y.val = 0 ∨ (x.val = «%S».min ∧ y.val = -1) := by
  checked_transfer core.num.checked_div_IScalar_bv_spec x y, core.num.checked_div_IScalar x y

/-!
# Checked remainder
-/

/- [core::num::{T}::checked_rem] -/
def core.num.checked_rem_UScalar {ty} (x y : UScalar ty) : Option (UScalar ty) :=
  Option.ofRustM (UScalar.rem x y)

uscalar def «%S».checked_rem (x y : «%S») : Option «%S» := core.num.checked_rem_UScalar x y

/- [core::num::{T}::checked_rem] -/
def core.num.checked_rem_IScalar {ty} (x y : IScalar ty) : Option (IScalar ty) :=
  Option.ofRustM (IScalar.rem x y)

iscalar def «%S».checked_rem (x y : «%S») : Option «%S» := core.num.checked_rem_IScalar x y

theorem core.num.checked_rem_UScalar_bv_spec {ty} (x y : UScalar ty) :
  match core.num.checked_rem_UScalar x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val % y.val ∧ z.bv = x.bv % y.bv
  | none => y.val = 0 := by
  simp only [checked_rem_UScalar]
  by_cases hy : y.val = 0
  · simp only [UScalar.rem, hy, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      Option.ofRustM]
  · have ⟨z, hz, h1, h2⟩ := spec_imp_exists (UScalar.rem_bv_spec x hy)
    have : x % y = UScalar.rem x y := rfl
    rw [← this, hz]
    exact ⟨hy, h1, h2⟩

uscalar theorem «%S».checked_rem_bv_spec (x y : «%S») :
  match «%S».checked_rem x y with
  | some z => y.val ≠ 0 ∧ z.val = x.val % y.val ∧ z.bv = x.bv % y.bv
  | none => y.val = 0 := by
  simp only [«%S».checked_rem]
  checked_transfer core.num.checked_rem_UScalar_bv_spec x y, core.num.checked_rem_UScalar x y

theorem core.num.checked_rem_IScalar_bv_spec {ty} (x y : IScalar ty) :
  match core.num.checked_rem_IScalar x y with
  | some z => y.val ≠ 0 ∧ ¬ (x.val = IScalar.min ty ∧ y.val = -1) ∧
    z.val = Int.tmod x.val y.val ∧ z.bv = BitVec.srem x.bv y.bv
  | none => y.val = 0 ∨ (x.val = IScalar.min ty ∧ y.val = -1) := by
  simp only [checked_rem_IScalar]
  by_cases hy : y.val = 0
  · simp only [IScalar.rem, hy, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      Option.ofRustM, true_or]
  · by_cases ho : x.val = IScalar.min ty ∧ y.val = -1
    · simp only [IScalar.rem, ho.1, ho.2, bne_iff_ne, ne_eq, and_self, decide_true,
        Bool.and_self, not_true_eq_false, ↓reduceIte, Option.ofRustM, or_true]
      simp_all
    · have ⟨z, hz, h1, h2⟩ := spec_imp_exists (IScalar.rem_bv_spec x hy ho)
      have : x % y = IScalar.rem x y := rfl
      rw [← this, hz]
      exact ⟨hy, ho, h1, h2⟩

iscalar theorem «%S».checked_rem_bv_spec (x y : «%S») :
  match core.num.checked_rem_IScalar x y with
  | some z => y.val ≠ 0 ∧ ¬ (x.val = «%S».min ∧ y.val = -1) ∧ z.val = Int.tmod x.val y.val ∧
    z.bv = BitVec.srem x.bv y.bv
  | none => y.val = 0 ∨ (x.val = «%S».min ∧ y.val = -1) := by
  checked_transfer core.num.checked_rem_IScalar_bv_spec x y, core.num.checked_rem_IScalar x y

end Aeneas.Std

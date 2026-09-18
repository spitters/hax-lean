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
  backends/lean/Aeneas/Std/Scalar/OverflowingOps/Add.lean
  backends/lean/Aeneas/Std/Scalar/OverflowingOps/Sub.lean
  backends/lean/Aeneas/Std/Scalar/OverflowingOps/Mul.lean
  backends/lean/Aeneas/Std/Scalar/OverflowingOps/Div.lean
-/

module

public import HaxLean.Rust.Scalar.Ops
public import HaxLean.Rust.Scalar.Elab

/-!
# Overflowing arithmetic

The wrapped result together with a flag that is `true` exactly when the operation
overflowed.
-/

@[expose] public section

set_option autoImplicit false

namespace Aeneas.Std

open RustM Error ScalarElab

def UScalar.overflowing_add {ty} (x y : UScalar ty) : UScalar ty × Bool :=
  (⟨x.bv + y.bv⟩, BitVec.uaddOverflow x.bv y.bv)

def IScalar.overflowing_add {ty} (x y : IScalar ty) : IScalar ty × Bool :=
  (⟨x.bv + y.bv⟩, BitVec.saddOverflow x.bv y.bv)

uscalar def «%S».overflowing_add (x y : «%S») : «%S» × Bool :=
  @UScalar.overflowing_add .«%S» x y

iscalar def «%S».overflowing_add (x y : «%S») : «%S» × Bool :=
  @IScalar.overflowing_add .«%S» x y

/- [core::num::{_}::overflowing_add] -/
uscalar def core.num.«%S».overflowing_add := @UScalar.overflowing_add .«%S»

/- [core::num::{_}::overflowing_add] -/
iscalar def core.num.«%S».overflowing_add := @IScalar.overflowing_add .«%S»

theorem UScalar.overflowing_add_eq {ty} (x y : UScalar ty) :
  let z := overflowing_add x y
  if x.val + y.val > UScalar.max ty then
    z.fst.val + UScalar.size ty = x.val + y.val ∧
    z.snd = true
  else
    z.fst.val = x.val + y.val ∧
    z.snd = false
  := by
  have hx := x.hBounds
  have hy := y.hBounds
  have hz : (overflowing_add x y).fst.val = (x.val + y.val) % 2 ^ ty.numBits := by
    show (x.bv + y.bv).toNat = _
    rw [BitVec.toNat_add]; rfl
  have hf : (overflowing_add x y).snd = decide (x.val + y.val ≥ 2 ^ ty.numBits) := by
    show BitVec.uaddOverflow x.bv y.bv = _
    simp only [BitVec.uaddOverflow]; rfl
  simp only [max, size]
  split <;> rename_i h
  · refine ⟨?_, by simp [hf]; omega⟩
    rw [hz, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · refine ⟨?_, by simp [hf]; omega⟩
    rw [hz, Nat.mod_eq_of_lt (by omega)]

uscalar theorem core.num.«%S».overflowing_add_eq (x y : «%S») :
  let z := overflowing_add x y
  if x.val + y.val > UScalar.max .«%S» then
    z.fst.val + UScalar.size .«%S» = x.val + y.val ∧ z.snd = true
  else z.fst.val = x.val + y.val ∧ z.snd = false
  := UScalar.overflowing_add_eq x y

def UScalar.overflowing_sub {ty} (x y : UScalar ty) : UScalar ty × Bool :=
  (⟨ x.bv - y.bv ⟩, BitVec.usubOverflow x.bv y.bv)

def IScalar.overflowing_sub {ty} (x y : IScalar ty) : IScalar ty × Bool :=
  (⟨ x.bv - y.bv ⟩, BitVec.ssubOverflow x.bv y.bv)

uscalar def «%S».overflowing_sub (x y : «%S») : «%S» × Bool :=
  @UScalar.overflowing_sub .«%S» x y

iscalar def «%S».overflowing_sub (x y : «%S») : «%S» × Bool :=
  @IScalar.overflowing_sub .«%S» x y

/- [core::num::{_}::overflowing_sub] -/
uscalar def core.num.«%S».overflowing_sub := @UScalar.overflowing_sub .«%S»

/- [core::num::{_}::overflowing_sub] -/
iscalar def core.num.«%S».overflowing_sub := @IScalar.overflowing_sub .«%S»

theorem UScalar.overflowing_sub_eq {ty} (x y : UScalar ty) :
  let z := overflowing_sub x y
  if x.val < y.val then
    z.fst.val + y.val = x.val + UScalar.size ty ∧
    z.snd = true
  else
    z.fst.val = x.val - y.val ∧
    z.snd = false
  := by
  have hx := x.hBounds
  have hy := y.hBounds
  have hz : (overflowing_sub x y).fst.val = (2 ^ ty.numBits - y.val + x.val) % 2 ^ ty.numBits := by
    show (x.bv - y.bv).toNat = _
    rw [BitVec.toNat_sub]; rfl
  have hf : (overflowing_sub x y).snd = decide (x.val < y.val) := by
    show BitVec.usubOverflow x.bv y.bv = _
    simp only [BitVec.usubOverflow]; rfl
  simp only [size]
  split <;> rename_i h
  · refine ⟨?_, by simp [hf]; omega⟩
    rw [hz, Nat.mod_eq_of_lt (by omega)]
    omega
  · refine ⟨?_, by simp [hf]; omega⟩
    rw [hz, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

uscalar theorem core.num.«%S».overflowing_sub_eq (x y : «%S») :
  let z := overflowing_sub x y
  if x.val < y.val then z.fst.val + y.val = x.val + UScalar.size .«%S» ∧ z.snd = true
  else z.fst.val = x.val - y.val ∧ z.snd = false
  := UScalar.overflowing_sub_eq x y

def UScalar.overflowing_mul {ty} (x y : UScalar ty) : UScalar ty × Bool :=
  (⟨ x.bv * y.bv ⟩, BitVec.umulOverflow x.bv y.bv)

def IScalar.overflowing_mul {ty} (x y : IScalar ty) : IScalar ty × Bool :=
  (⟨ x.bv * y.bv ⟩, BitVec.smulOverflow x.bv y.bv)

uscalar def «%S».overflowing_mul (x y : «%S») : «%S» × Bool :=
  @UScalar.overflowing_mul .«%S» x y

iscalar def «%S».overflowing_mul (x y : «%S») : «%S» × Bool :=
  @IScalar.overflowing_mul .«%S» x y

/- [core::num::{_}::overflowing_mul] -/
uscalar def core.num.«%S».overflowing_mul := @UScalar.overflowing_mul .«%S»

/- [core::num::{_}::overflowing_mul] -/
iscalar def core.num.«%S».overflowing_mul := @IScalar.overflowing_mul .«%S»

theorem UScalar.overflowing_mul_eq {ty} (x y : UScalar ty) :
  let z := overflowing_mul x y
  if x.val * y.val > UScalar.max ty then
    z.fst.val = (x.val * y.val) % UScalar.size ty ∧
    z.snd = true
  else
    z.fst.val = x.val * y.val ∧
    z.snd = false
  := by
  have hz : (overflowing_mul x y).fst.val = (x.val * y.val) % 2 ^ ty.numBits := by
    show (x.bv * y.bv).toNat = _
    rw [BitVec.toNat_mul]; rfl
  have hf : (overflowing_mul x y).snd = decide (x.val * y.val ≥ 2 ^ ty.numBits) := by
    show BitVec.umulOverflow x.bv y.bv = _
    simp only [BitVec.umulOverflow]; rfl
  have : 0 < 2 ^ ty.numBits := Nat.two_pow_pos _
  simp only [max, size]
  split <;> rename_i h
  · exact ⟨hz, by simp [hf]; omega⟩
  · refine ⟨?_, by simp [hf]; omega⟩
    rw [hz, Nat.mod_eq_of_lt (by omega)]

uscalar theorem core.num.«%S».overflowing_mul_eq (x y : «%S») :
  let z := overflowing_mul x y
  if x.val * y.val > UScalar.max .«%S» then
    z.fst.val = (x.val * y.val) % UScalar.size .«%S» ∧ z.snd = true
  else z.fst.val = x.val * y.val ∧ z.snd = false
  := UScalar.overflowing_mul_eq x y

/-- Overflowing unsigned division: a panic on a zero divisor; the flag is always `false`. -/
def UScalar.overflowing_div {ty} (x y : UScalar ty) : RustM (UScalar ty × Bool) :=
  if y.bv != 0 then ok (⟨ BitVec.udiv x.bv y.bv ⟩, false) else fail panic

/-- Overflowing signed division: a panic on a zero divisor; `MIN / -1` is `(MIN, true)`. -/
def IScalar.overflowing_div {ty} (x y : IScalar ty) : RustM (IScalar ty × Bool) :=
  if y.val != 0 then ok (⟨ BitVec.sdiv x.bv y.bv ⟩, BitVec.sdivOverflow x.bv y.bv)
  else fail panic

uscalar def «%S».overflowing_div (x y : «%S») : RustM («%S» × Bool) :=
  @UScalar.overflowing_div .«%S» x y

iscalar def «%S».overflowing_div (x y : «%S») : RustM («%S» × Bool) :=
  @IScalar.overflowing_div .«%S» x y

/- [core::num::{_}::overflowing_div] -/
uscalar def core.num.«%S».overflowing_div := @UScalar.overflowing_div .«%S»

/- [core::num::{_}::overflowing_div] -/
iscalar def core.num.«%S».overflowing_div := @IScalar.overflowing_div .«%S»

theorem UScalar.overflowing_div_eq {ty} (x y : UScalar ty) :
  overflowing_div x y = (·, false) <$> UScalar.div x y := by
  simp only [overflowing_div, UScalar.div]
  split <;> rfl

uscalar theorem core.num.«%S».overflowing_div_eq (x y : «%S») :
  overflowing_div x y = (·, false) <$> UScalar.div x y
  := UScalar.overflowing_div_eq x y

end Aeneas.Std

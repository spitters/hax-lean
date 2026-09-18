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
  backends/lean/Aeneas/Std/Scalar/Rotate.lean
-/

module

public import HaxLean.Rust.Scalar.Core
public import HaxLean.Rust.Scalar.Elab

/-!
# Rotations

`rotate_left` and `rotate_right` on the bit vector of a scalar; the amount is taken
modulo the bit width.
-/

@[expose] public section

set_option autoImplicit false

namespace Aeneas.Std

open ScalarElab

/-- `rotate_left`: the shift amount is taken modulo the bit width. -/
def UScalar.rotate_left {ty} (x : UScalar ty) (shift : U32) : UScalar ty :=
  ⟨ x.bv.rotateLeft shift.val ⟩

/- `core::num::{_}::rotate_left` -/
uscalar def core.num.«%S».rotate_left : «%S» → U32 → «%S» := @UScalar.rotate_left .«%S»

/-- `rotate_left`: the shift amount is taken modulo the bit width. -/
def IScalar.rotate_left {ty} (x : IScalar ty) (shift : U32) : IScalar ty :=
  ⟨ x.bv.rotateLeft shift.val ⟩

/- `core::num::{_}::rotate_left` -/
iscalar def core.num.«%S».rotate_left : «%S» → U32 → «%S» := @IScalar.rotate_left .«%S»

/-- `rotate_right`: the shift amount is taken modulo the bit width. -/
def UScalar.rotate_right {ty} (x : UScalar ty) (shift : U32) : UScalar ty :=
  ⟨ x.bv.rotateRight shift.val ⟩

/- `core::num::{_}::rotate_right` -/
uscalar def core.num.«%S».rotate_right : «%S» → U32 → «%S» := @UScalar.rotate_right .«%S»

/-- `rotate_right`: the shift amount is taken modulo the bit width. -/
def IScalar.rotate_right {ty} (x : IScalar ty) (shift : U32) : IScalar ty :=
  ⟨ x.bv.rotateRight shift.val ⟩

/- `core::num::{_}::rotate_right` -/
iscalar def core.num.«%S».rotate_right : «%S» → U32 → «%S» := @IScalar.rotate_right .«%S»

end Aeneas.Std

/-
Copyright (c) the Aeneas contributors. Licensed under the Apache License,
Version 2.0 (the "License"); you may not use this file except in compliance with
the License. You may obtain a copy of the License at
http://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable law or
agreed to in writing, software distributed under the License is distributed on
an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and
limitations under the License.

The definitions of `UScalar.tryMk`, `IScalar.tryMk`, `add`, `sub`, `mul`, `div` and `rem` are
transcribed from
Source: AeneasVerif/aeneas at b08bf81f2524ee295a8c37444893acfc9c5f4dde,
  backends/lean/Aeneas/Std/Scalar/Core.lean (lines 601-610),
  backends/lean/Aeneas/Std/Scalar/Ops/Add.lean (lines 16-20),
  backends/lean/Aeneas/Std/Scalar/Ops/Sub.lean (lines 17-22),
  backends/lean/Aeneas/Std/Scalar/Ops/Mul.lean (lines 18-22),
  backends/lean/Aeneas/Std/Scalar/Ops/Div.lean (lines 17-25),
  backends/lean/Aeneas/Std/Scalar/Ops/Rem.lean (lines 16-21).
The agreement theorems are by the CatCrypt Contributors.
-/

module

public import HaxLean.Rust.ITree.Agree
public import HaxLean.Rust.Scalar

/-!
# Checked scalar arithmetic of upstream Aeneas over the interaction-tree result

The scalar types `UScalar ty` and `IScalar ty` of upstream Aeneas at `b08bf81` have the same
definitions as the vendored ones of `HaxLean.Rust.Scalar.Core` (the kinds `UScalarTy` and
`IScalarTy`, `numBits`, a structure over `BitVec ty.numBits`, `val`, the bounds, `ofNatCore`,
`ofIntCore`, `tryMkOpt`, the order instances), so both sides use the vendored types. The
pure operations (`wrapping_add`, `wrapping_sub`, `wrapping_mul`, the `core.num` aliases,
`and`, `or`, `xor`, `not`, `cast`) have the same definitions on both sides and are shared;
an occurrence `ok (op x y)` of them is related by `RustM.toITree_ok`.

The checked operations return a result and are transcribed here over `IResult`. Upstream
fails with `integerOverflow` or `divisionByZero` where the vendored operation fails with
`panic`. Each checked operation agrees with its upstream form in the sense of
`RustM.Agrees`, except signed `rem`: at `IScalar.min ty % -1` upstream `IScalar.rem` returns
`ok 0` (it checks only for a zero divisor), and the vendored one fails, as Rust's `%` panics
there. For signed `rem` the module proves the `ok` direction: a value of the vendored `rem`
is the value of the upstream one (`IScalar.rem_toITree_of_ok`).

## Main definitions

* `ITreeModel.UScalar.tryMk`, `ITreeModel.IScalar.tryMk`
* `ITreeModel.UScalar.add`, `sub`, `mul`, `div`, `rem` and the `IScalar` forms

## Main results

* `UScalar.add_agrees`, `UScalar.sub_agrees`, `UScalar.mul_agrees`, `UScalar.div_agrees`,
  `UScalar.rem_agrees`
* `IScalar.add_agrees`, `IScalar.sub_agrees`, `IScalar.mul_agrees`, `IScalar.div_agrees`
* `IScalar.rem_toITree_of_ok`
-/

@[expose] public section

set_option autoImplicit false

namespace Aeneas.Std.ITreeModel

/-- Upstream `UScalar.tryMk`: the scalar of value `x`, or `integerOverflow`. -/
def UScalar.tryMk (ty : UScalarTy) (x : Nat) : IResult (Std.UScalar ty) :=
  IResult.ofOption (Std.UScalar.tryMkOpt ty x) .integerOverflow

/-- Upstream `IScalar.tryMk`: the scalar of value `x`, or `integerOverflow`. -/
def IScalar.tryMk (ty : IScalarTy) (x : Int) : IResult (Std.IScalar ty) :=
  IResult.ofOption (Std.IScalar.tryMkOpt ty x) .integerOverflow

/-- Upstream checked unsigned addition. -/
def UScalar.add {ty : UScalarTy} (x y : Std.UScalar ty) : IResult (Std.UScalar ty) :=
  ITreeModel.UScalar.tryMk ty (x.val + y.val)

/-- Upstream checked signed addition. -/
def IScalar.add {ty : IScalarTy} (x y : Std.IScalar ty) : IResult (Std.IScalar ty) :=
  ITreeModel.IScalar.tryMk ty (x.val + y.val)

/-- Upstream checked unsigned subtraction. -/
def UScalar.sub {ty : UScalarTy} (x y : Std.UScalar ty) : IResult (Std.UScalar ty) :=
  if x.val < y.val then IResult.fail .integerOverflow
  else IResult.ok ⟨BitVec.ofNat _ (x.val - y.val)⟩

/-- Upstream checked signed subtraction. -/
def IScalar.sub {ty : IScalarTy} (x y : Std.IScalar ty) : IResult (Std.IScalar ty) :=
  ITreeModel.IScalar.tryMk ty (x.val - y.val)

/-- Upstream checked unsigned multiplication. -/
def UScalar.mul {ty : UScalarTy} (x y : Std.UScalar ty) : IResult (Std.UScalar ty) :=
  ITreeModel.UScalar.tryMk ty (x.val * y.val)

/-- Upstream checked signed multiplication. -/
def IScalar.mul {ty : IScalarTy} (x y : Std.IScalar ty) : IResult (Std.IScalar ty) :=
  ITreeModel.IScalar.tryMk ty (x.val * y.val)

/-- Upstream checked unsigned division. -/
def UScalar.div {ty : UScalarTy} (x y : Std.UScalar ty) : IResult (Std.UScalar ty) :=
  if y.bv != 0 then IResult.ok ⟨BitVec.udiv x.bv y.bv⟩ else IResult.fail .divisionByZero

/-- Upstream checked signed division: `divisionByZero` at a zero divisor, `integerOverflow`
at `IScalar.min ty / -1`. -/
def IScalar.div {ty : IScalarTy} (x y : Std.IScalar ty) : IResult (Std.IScalar ty) :=
  if y.val != 0 then
    if ¬ (x.val = Std.IScalar.min ty && y.val = -1) then IResult.ok ⟨BitVec.sdiv x.bv y.bv⟩
    else IResult.fail .integerOverflow
  else IResult.fail .divisionByZero

/-- Upstream checked unsigned remainder. -/
def UScalar.rem {ty : UScalarTy} (x y : Std.UScalar ty) : IResult (Std.UScalar ty) :=
  if y.val != 0 then IResult.ok ⟨BitVec.umod x.bv y.bv⟩ else IResult.fail .divisionByZero

/-- Upstream signed remainder: `divisionByZero` at a zero divisor and no other failure, so
`IScalar.min ty % -1` is `ok 0`. -/
def IScalar.rem {ty : IScalarTy} (x y : Std.IScalar ty) : IResult (Std.IScalar ty) :=
  if y.val != 0 then IResult.ok ⟨BitVec.srem x.bv y.bv⟩
  else IResult.fail .divisionByZero

end Aeneas.Std.ITreeModel

namespace Aeneas.Std

open RustM

/-- Checked construction agrees with upstream `UScalar.tryMk`. -/
theorem UScalar.tryMk_agrees (ty : UScalarTy) (x : Nat) :
    Agrees (UScalar.tryMk ty x) (ITreeModel.UScalar.tryMk ty x) :=
  agrees_ofOption _ _ _

/-- Checked construction agrees with upstream `IScalar.tryMk`. -/
theorem IScalar.tryMk_agrees (ty : IScalarTy) (x : Int) :
    Agrees (IScalar.tryMk ty x) (ITreeModel.IScalar.tryMk ty x) :=
  agrees_ofOption _ _ _

/-- Checked unsigned addition agrees with upstream. -/
theorem UScalar.add_agrees {ty : UScalarTy} (x y : UScalar ty) :
    Agrees (UScalar.add x y) (ITreeModel.UScalar.add x y) :=
  UScalar.tryMk_agrees _ _

/-- Checked signed addition agrees with upstream. -/
theorem IScalar.add_agrees {ty : IScalarTy} (x y : IScalar ty) :
    Agrees (IScalar.add x y) (ITreeModel.IScalar.add x y) :=
  IScalar.tryMk_agrees _ _

/-- Checked unsigned subtraction agrees with upstream. -/
theorem UScalar.sub_agrees {ty : UScalarTy} (x y : UScalar ty) :
    Agrees (UScalar.sub x y) (ITreeModel.UScalar.sub x y) := by
  unfold UScalar.sub ITreeModel.UScalar.sub
  split <;> first | rfl | exact agrees_fail _ _

/-- Checked signed subtraction agrees with upstream. -/
theorem IScalar.sub_agrees {ty : IScalarTy} (x y : IScalar ty) :
    Agrees (IScalar.sub x y) (ITreeModel.IScalar.sub x y) :=
  IScalar.tryMk_agrees _ _

/-- Checked unsigned multiplication agrees with upstream. -/
theorem UScalar.mul_agrees {ty : UScalarTy} (x y : UScalar ty) :
    Agrees (UScalar.mul x y) (ITreeModel.UScalar.mul x y) :=
  UScalar.tryMk_agrees _ _

/-- Checked signed multiplication agrees with upstream. -/
theorem IScalar.mul_agrees {ty : IScalarTy} (x y : IScalar ty) :
    Agrees (IScalar.mul x y) (ITreeModel.IScalar.mul x y) :=
  IScalar.tryMk_agrees _ _

/-- Checked unsigned division agrees with upstream. -/
theorem UScalar.div_agrees {ty : UScalarTy} (x y : UScalar ty) :
    Agrees (UScalar.div x y) (ITreeModel.UScalar.div x y) := by
  unfold UScalar.div ITreeModel.UScalar.div
  split <;> first | rfl | exact agrees_fail _ _

/-- Checked signed division agrees with upstream: both fail at a zero divisor and at
`IScalar.min ty / -1`. -/
theorem IScalar.div_agrees {ty : IScalarTy} (x y : IScalar ty) :
    Agrees (IScalar.div x y) (ITreeModel.IScalar.div x y) := by
  unfold IScalar.div ITreeModel.IScalar.div
  split
  · split <;> first | rfl | exact agrees_fail _ _
  · exact agrees_fail _ _

/-- Checked unsigned remainder agrees with upstream. -/
theorem UScalar.rem_agrees {ty : UScalarTy} (x y : UScalar ty) :
    Agrees (UScalar.rem x y) (ITreeModel.UScalar.rem x y) := by
  unfold UScalar.rem ITreeModel.UScalar.rem
  split <;> first | rfl | exact agrees_fail _ _

/-- A value of the vendored signed remainder is the value of upstream's. The converse fails
at `IScalar.min ty % -1`, where the vendored `rem` fails and upstream returns `ok 0`. -/
theorem IScalar.rem_toITree_of_ok {ty : IScalarTy} (x y z : IScalar ty)
    (h : IScalar.rem x y = .ok z) : ITreeModel.IScalar.rem x y = ITreeModel.IResult.ok z := by
  unfold IScalar.rem at h
  unfold ITreeModel.IScalar.rem
  split at h
  next hy =>
    split at h
    · cases h
      simp only [hy, ↓reduceIte]
    · cases h
  · cases h

end Aeneas.Std

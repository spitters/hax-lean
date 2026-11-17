/-
Copyright (c) the CatCrypt Contributors. Licensed under the Apache License,
Version 2.0 (the "License"); you may not use this file except in compliance with
the License. You may obtain a copy of the License at
http://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable law or
agreed to in writing, software distributed under the License is distributed on
an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and
limitations under the License.
-/
import HaxLean.Rust.Scalar.Ops

/-!
# `MIN / -1` and `MIN % -1` on signed scalars

The signed quotient and remainder panic when the dividend is the minimum of the type and the
divisor is `-1`, as Rust does, at every signed width (`I8` to `I128`, `Isize`).
-/

namespace Aeneas.Std

open RustM Error

/-- `MIN % -1` panics at every signed width. -/
theorem IScalar.rem_min_neg_one {ty : IScalarTy} (x y : IScalar ty)
    (hx : x.val = IScalar.min ty) (hy : y.val = -1) :
    IScalar.rem x y = RustM.fail Error.panic := by
  unfold IScalar.rem
  simp [hx, hy]

/-- `MIN / -1` panics at every signed width. -/
theorem IScalar.div_min_neg_one {ty : IScalarTy} (x y : IScalar ty)
    (hx : x.val = IScalar.min ty) (hy : y.val = -1) :
    IScalar.div x y = RustM.fail Error.panic := by
  unfold IScalar.div
  simp [hx, hy]

end Aeneas.Std

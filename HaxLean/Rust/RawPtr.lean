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
  backends/lean/Aeneas/Std/RawPtr.lean
-/

module

public import HaxLean.Rust.Scalar.Core

/-!
# Raw pointers

A raw pointer is modelled by the value it points to, tagged with its mutability.
-/

@[expose] public section

set_option autoImplicit false

namespace Aeneas.Std

/-- Mutability of a raw pointer. -/
inductive Mutability where
| Mut | Const

/-- A raw pointer, modelled by the value it points to. -/
structure RawPtr (T : Type) (M : Mutability) where
  v : T

abbrev MutRawPtr (T : Type) := RawPtr T .Mut
abbrev ConstRawPtr (T : Type) := RawPtr T .Const

/-- Signedness and width of a scalar type. -/
inductive ScalarKind where
| Signed (ty : IScalarTy)
| Unsigned (ty : UScalarTy)

/-- `T` is one of the scalar types. -/
class IsScalar (T : Type) where
  isScalar : (∃ ty, T = UScalar ty) ∨ (∃ ty, T = IScalar ty)

instance {ty} : IsScalar (UScalar ty) where
  isScalar := .inl ⟨ty, rfl⟩

instance {ty} : IsScalar (IScalar ty) where
  isScalar := .inr ⟨ty, rfl⟩

/-- A cast between raw pointers to scalars; the model fails with `undef`. -/
def RawPtr.cast_scalar {T} {M} (T' : Type) (M' : Mutability) [IsScalar T] [IsScalar T']
    (_ : RawPtr T M) :
  RustM (RawPtr T' M') :=
  .fail .undef

end Aeneas.Std

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
  backends/lean/Aeneas/Std/Alloc.lean
  backends/lean/Aeneas/Std/Core/Core.lean
  backends/lean/Aeneas/Std/Core/Default.lean
  backends/lean/Aeneas/Std/Core/Ops.lean
-/

module

public import HaxLean.Rust.WP

/-!
# `core` and `alloc` traits

The Rust traits `Clone`, `Copy`, `From`, `Default`, `Index`, `IndexMut`, `Deref`,
`DerefMut`, `Fn*`, `Try` as structures of methods in `RustM`, the builtin instances,
and the `Option` helpers used by extracted code.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Aeneas

namespace Std

open RustM

/-! ## `alloc` (source: `Alloc.lean`) -/

/-- The type of the global allocator. -/
inductive Global where | mk

/-- `Box::deref`. -/
def alloc.boxed.Box.deref {T : Type} (x : T) : T := x

/-- `Box::deref_mut`: the value and its write-back. -/
def alloc.boxed.Box.deref_mut {T : Type} (x : T) : (T × (T → T)) := (x, λ x => x)

/-- `Global::clone`. -/
def alloc.alloc.CloneGlobal.clone (_ : Global) : RustM Global := .ok .mk

/-! ## `core` (source: `Core/Core.lean`) -/

/-- `<Box<T> as AsMut<T>>::as_mut`. -/
def alloc.boxed.AsMutBox.as_mut {T : Type} (x : T) : T × (T → T) :=
  (x, fun x => x)

namespace core

/-- The trait `core::convert::From`. -/
structure convert.From (Self T : Type) where
  «from» : T → RustM Self

/-- The trait `core::clone::Clone`. -/
structure clone.Clone (Self : Type) where
  clone : Self → RustM Self
  clone_from : Self → Self → RustM Self := fun _ => clone

/-- The default method `Clone::clone_from`. -/
def clone.Clone.clone_from.default {Self : Type} (CloneInst : core.clone.Clone Self)
  (_self source : Self) : RustM Self :=
  CloneInst.clone source

@[reducible]
def clone.CloneGlobal : core.clone.Clone Global := {
  clone := alloc.alloc.CloneGlobal.clone
}

/-- `<bool as Clone>::clone`. -/
@[reducible, simp]
def clone.impls.CloneBool.clone (b : Bool) : Bool := b

@[reducible]
def clone.CloneBool : clone.Clone Bool := {
  clone := fun b => ok (clone.impls.CloneBool.clone b)
  clone_from := fun _ b => ok (clone.impls.CloneBool.clone b)
}

/-- `<Box<T> as Clone>::clone`. -/
def alloc.boxed.CloneBox.clone {T : Type} (cloneInst : core.clone.Clone T) : T → RustM T :=
  cloneInst.clone

@[reducible]
def clone.CloneBox {T : Type} (cloneInst : core.clone.Clone T) : core.clone.Clone T := {
  clone := alloc.boxed.CloneBox.clone cloneInst
}

/-- The trait `core::marker::Copy`. -/
structure marker.Copy (Self : Type) where
  cloneInst : core.clone.Clone Self

@[reducible]
def marker.CopyBool : core.marker.Copy Bool := {
  cloneInst := core.clone.CloneBool
}

/-- `core::mem::replace`: the old value of `dst`, and `src` as the new value. -/
@[simp]
def mem.replace {a : Type} (dst : a) (src : a) : a × a := (dst, src)

/-- `core::mem::swap`. -/
@[simp]
def mem.swap {T : Type} (a b : T): T × T := (b, a)

end core

/-- Builtin clone implementation (used for some builtin types) -/
def BuiltinClone (Self : Type) : core.clone.Clone Self where
  clone := .ok
  clone_from := fun _ x => .ok x

/-- Builtin copy implementation (used for some builtin types) -/
def BuiltinCopy (Self : Type) : core.marker.Copy Self where
  cloneInst := BuiltinClone Self

/-- `Option::unwrap`: panics on `none`. -/
def core.option.Option.unwrap {T : Type} (x : Option T) : RustM T :=
  RustM.ofOption x Error.panic

theorem core.option.Option.unwrap.spec {T : Type} (x : Option T) (h : x.isSome) :
  unwrap x ⦃ v => x = some v ⦄ := by
  cases x <;> simp_all [unwrap, RustM.ofOption]

/-- `Option::unwrap_or`. -/
def core.option.Option.unwrap_or {T : Type} (self : Option T) (default : T) : T :=
  match self with
  | none => default
  | some self => self

@[simp] theorem core.option.Option.unwrap_or_some {T : Type} (self default : T) :
  core.option.Option.unwrap_or (some self) default = self := by simp [unwrap_or]

@[simp] theorem core.option.Option.unwrap_or_none {T : Type} (default : T) :
  core.option.Option.unwrap_or none default = default := by simp [unwrap_or]

/-- `Option::take`: the value and `none` as the new value of the place. -/
@[simp]
def core.option.Option.take {T: Type} (self: Option T): Option T × Option T := (self, .none)

/-- `Option::is_none`. -/
@[simp]
def core.option.Option.is_none {T: Type} (self: Option T): Bool := self.isNone

/-- Returns `true` if the option is `some`. -/
@[simp]
def core.option.Option.is_some {T: Type} (self: Option T): Bool := self.isSome

/-- `core::ops::range::RangeFrom`. -/
structure core.ops.range.RangeFrom (Idx : Type) where
  start : Idx

/-- `core::panicking::AssertKind`. -/
inductive core.panicking.AssertKind where
| Eq : core.panicking.AssertKind
| Ne : core.panicking.AssertKind
| Match : core.panicking.AssertKind

/-- `<&T as Clone>::clone`. -/
def core.clone.impls.CloneShared.clone {T : Type} (x : T) : RustM T := .ok x

/-! ## `core::default` (source: `Core/Default.lean`) -/

/-- The trait `core::default::Default`. -/
structure core.default.Default (Self : Type u) where
  default : RustM Self

/-- `<bool as Default>::default`. -/
def core.default.DefaultBool.default : RustM Bool := .ok false

/-! ## `core::ops` (source: `Core/Ops.lean`) -/

/-- The trait `core::ops::index::Index`. -/
structure core.ops.index.Index (Self Idx Output : Type) where
  index : Self → Idx → RustM Output

/-- The trait `core::ops::index::IndexMut`. -/
structure core.ops.index.IndexMut (Self Idx Output : Type) where
  indexInst : core.ops.index.Index Self Idx Output
  index_mut : Self → Idx → RustM (Output × (Output → Self))

/-- The trait `core::ops::deref::Deref`. -/
structure core.ops.deref.Deref (Self Target : Type) where
  deref : Self → RustM Target

/-- The trait `core::ops::deref::DerefMut`. -/
structure core.ops.deref.DerefMut (Self Target : Type) where
  derefInst : core.ops.deref.Deref Self Target
  deref_mut : Self → RustM (Target × (Target → Self))

/-- `Deref` for `Box<T>`. -/
def core.ops.deref.DerefBoxInst (T : Type) :
  core.ops.deref.Deref T T := {
  deref x := ok (alloc.boxed.Box.deref x)
}

/-- `DerefMut` for `Box<T>`. -/
def core.ops.deref.DerefMutBoxInst (T : Type) :
  core.ops.deref.DerefMut T T := {
  derefInst := core.ops.deref.DerefBoxInst T
  deref_mut x := ok (alloc.boxed.Box.deref_mut x)
}

/-- The trait `core::ops::bit::BitAnd`. -/
structure core.ops.bit.BitAnd (Self : Type) (Rhs : Type) (Self_Output : Type) where
  bitand : Self → Rhs → RustM Self_Output

/-- The trait `core::ops::drop::Drop`. -/
structure core.ops.drop.Drop (Self : Type) where
  drop : Self → RustM Self

/-- The default method `Drop::drop`. -/
def core.ops.drop.Drop.drop.default {Self : Type}
    (DropInst : core.ops.drop.Drop Self) : Self → RustM Self :=
  fun s => DropInst.drop s

/-- The trait `core::ops::function::FnOnce`. -/
structure core.ops.function.FnOnce (Self : Type u) (Args : Type v) (Output : Type w) where
  call_once : Self → Args → RustM Output

/-- The trait `core::ops::function::FnMut`. -/
structure core.ops.function.FnMut (Self : Type u) (Args : Type v) (Output : Type w) where
  FnOnceInst : core.ops.function.FnOnce Self Args Output
  call_mut : Self → Args → RustM (Output × Self)

/-- The trait `core::ops::function::Fn`. -/
structure core.ops.function.Fn (Self : Type u) (Args : Type v) (Output : Type w) where
  FnMutInst : core.ops.function.FnMut Self Args Output
  call : Self → Args → RustM Output

/-- `FnOnce` for a monadic function. -/
def BuiltinFnOnce (Inputs : Type u) (Outputs : Type v) :
    core.ops.function.FnOnce (Inputs → RustM Outputs) Inputs Outputs := {
  call_once f x := f x
}

/-- `FnMut` for a monadic function. -/
def BuiltinFnMut (Inputs : Type u) (Outputs : Type v) :
    core.ops.function.FnMut (Inputs → RustM Outputs) Inputs Outputs := {
  FnOnceInst := BuiltinFnOnce Inputs Outputs
  call_mut f x :=
    match f x with
    | ok y => ok (y, f)
    | fail e => fail e
    | div => div
}

/-- `Fn` for a monadic function. -/
def BuiltinFn (Inputs : Type u) (Outputs : Type v) :
    core.ops.function.Fn (Inputs → RustM Outputs) Inputs Outputs := {
  FnMutInst := BuiltinFnMut Inputs Outputs
  call f x := f x
}

/-- The trait `core::ops::try_trait::FromResidual`. -/
structure core.ops.try_trait.FromResidual (Self : Type u) (R : Type v) where
  from_residual : R → RustM Self

/-- `core::ops::control_flow::ControlFlow`. -/
inductive core.ops.control_flow.ControlFlow (B : Type) (C : Type) where
| Continue : C → core.ops.control_flow.ControlFlow B C
| Break : B → core.ops.control_flow.ControlFlow B C

/-- The trait `core::ops::try_trait::Try`. -/
structure core.ops.try_trait.Try (Self Output Residual : Type) where
  FromResidualInst : core.ops.try_trait.FromResidual Self Residual
  from_output : Output → RustM Self
  branch : Self → RustM (core.ops.control_flow.ControlFlow Residual Output)

/-- The trait `core::ops::try_trait::Residual`. -/
structure core.ops.try_trait.Residual (Self O TryType: Type) where
  TryInst : core.ops.try_trait.Try TryType O Self

end Std

end Aeneas

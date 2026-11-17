/-
Copyright (c) the Aeneas contributors. Licensed under the Apache License,
Version 2.0 (the "License"); you may not use this file except in compliance with
the License. You may obtain a copy of the License at
http://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable law or
agreed to in writing, software distributed under the License is distributed on
an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and
limitations under the License.

The definitions of `IResult.ofOption`, `massert` and `lift` are transcribed from
Source: AeneasVerif/aeneas at b08bf81f2524ee295a8c37444893acfc9c5f4dde,
  backends/lean/Aeneas/Std/Primitives.lean (lines 250-257, 456).
The relation `RustM.Agrees` and the theorems about it are by the CatCrypt Contributors.
-/

module

public import HaxLean.Rust.ITreeResult

/-!
# Agreement of flat results with interaction-tree results

The vendored flat model `Aeneas.Std.RustM` has two error kinds (`panic`, `undef`); upstream
Aeneas has seven, and its operations fail with the kind of the fault (`integerOverflow`,
`divisionByZero`, `assertionFailure`, `arrayOutOfBounds`). The vendored operations fail with
`panic` at the same arguments. The map `RustM.toITree` of `HaxLean.Rust.ITreeResult` keeps
the error kind, so a vendored operation and its upstream form are related by `toITree` up
to the kind of a failure.

`RustM.Agrees x t` is that relation: `x = ok a` and `t = ok a`, or both fail (with any
kinds), or both diverge. It holds of `x` and `toITree x` (`agrees_toITree`), it is closed
under bind (`Agrees.bind`), and it determines the `ok` results (`Agrees.eq_ok_iff`). A value
`fn a = .ok y` that the compiler's Aeneas front certifies in the flat monad is therefore the
value `ok y` of the upstream `Result` computation agreeing with `fn a`.

The module transcribes the upstream combinators `Result.ofOption`, `massert` and `lift` over
`IResult` and relates them to the vendored ones.

## Main definitions

* `RustM.Agrees`: agreement up to the error kind
* `ITreeModel.IResult.ofOption`, `ITreeModel.massert`, `ITreeModel.lift`: upstream combinators

## Main results

* `RustM.agrees_toITree`, `RustM.Agrees.bind`, `RustM.Agrees.eq_ok_iff`
* `RustM.toITree_ofOption`, `RustM.agrees_massert`, `RustM.toITree_lift`
-/

@[expose] public section

set_option autoImplicit false

namespace Aeneas.Std.ITreeModel

open Aeneas.Data.Coinductive

universe u

/-- Upstream `Result.ofOption`: `ok` of the content of `some`, the failure `e` at `none`. -/
def IResult.ofOption {α : Type u} (x : Option α) (e : Error) : IResult α :=
  match x with
  | some x => IResult.ok x
  | none => IResult.fail e

/-- Upstream `massert`: `ok ()` when `b` holds, the failure `assertionFailure` otherwise. -/
def massert (b : Prop) [Decidable b] : IResult Unit :=
  if b then IResult.ok () else IResult.fail .assertionFailure

/-- Upstream `lift`: a pure value as a computation. -/
def lift {α : Type u} (x : α) : IResult α := IResult.ok x

/-- A failure is not a value. -/
theorem IResult.fail_ne_ok {α : Type u} (e : Error) (a : α) :
    (IResult.fail e : IResult α) ≠ IResult.ok a := by
  unfold IResult.fail IResult.vis IResult.ok
  exact fun h => not_vis_ret h.symm

/-- Divergence is not a value. -/
theorem IResult.div_ne_ok {α : Type u} (a : α) : (IResult.div : IResult α) ≠ IResult.ok a := by
  unfold IResult.div IResult.ok
  exact fun h => not_ret_div h.symm

/-- `ok` is injective. -/
theorem IResult.ok_inj {α : Type u} {a b : α} :
    (IResult.ok a : IResult α) = IResult.ok b ↔ a = b :=
  ret_inj

end Aeneas.Std.ITreeModel

namespace Aeneas.Std

open Aeneas.Data.Coinductive ITreeModel

universe u v

namespace RustM

/-- Agreement of a flat result and an interaction-tree result up to the error kind: the same
value, failures of any kinds, or divergence on both sides. -/
def Agrees {α : Type u} : RustM α → IResult α → Prop
  | .ok a, t => t = IResult.ok a
  | .fail _, t => ∃ e, t = IResult.fail e
  | .div, t => t = IResult.div

/-- A flat result agrees with its interaction tree. -/
theorem agrees_toITree {α : Type u} (x : RustM α) : Agrees x (toITree x) := by
  cases x with
  | ok a => rfl
  | fail e => exact ⟨_, rfl⟩
  | div => rfl

/-- Two computations that agree have the same `ok` results. -/
theorem Agrees.eq_ok_iff {α : Type u} {x : RustM α} {t : IResult α} (h : Agrees x t) (a : α) :
    x = .ok a ↔ t = IResult.ok a := by
  cases x with
  | ok b =>
    change t = IResult.ok b at h
    subst h
    grind [IResult.ok_inj]
  | fail e =>
    obtain ⟨e', rfl⟩ := h
    grind [IResult.fail_ne_ok]
  | div =>
    change t = IResult.div at h
    subst h
    grind [IResult.div_ne_ok]

/-- Agreement is closed under bind. -/
theorem Agrees.bind {α β : Type u} {x : RustM α} {t : IResult α} {f : α → RustM β}
    {g : α → IResult β} (hx : Agrees x t) (hf : ∀ a, Agrees (f a) (g a)) :
    Agrees (x >>= f) (t >>= g) := by
  cases x with
  | ok a =>
    change t = IResult.ok a at hx
    subst hx
    change Agrees (f a) (ITreeModel.bind (IResult.ok a) g)
    rw [ITreeModel.bind_ok]
    exact hf a
  | fail e =>
    obtain ⟨e', rfl⟩ := hx
    exact ⟨e', ITreeModel.bind_fail e' g⟩
  | div =>
    change t = IResult.div at hx
    subst hx
    exact ITreeModel.bind_div g

/-- A computation equal to the interaction tree of `x` agrees with `x`. -/
theorem agrees_of_toITree_eq {α : Type u} {x : RustM α} {t : IResult α} (h : toITree x = t) :
    Agrees x t :=
  h ▸ agrees_toITree x

/-- Agreement at a failure: any two failures agree. -/
theorem agrees_fail {α : Type u} (e : Error) (e' : ITreeModel.Error) :
    Agrees (.fail e : RustM α) (IResult.fail e') :=
  ⟨e', rfl⟩

/-- `ofOption` agrees with upstream `Result.ofOption` at any two error kinds. -/
theorem agrees_ofOption {α : Type u} (x : Option α) (e : Error) (e' : ITreeModel.Error) :
    Agrees (RustM.ofOption x e) (IResult.ofOption x e') := by
  cases x <;> first | exact agrees_fail _ _ | rfl

/-- `ofOption` at the error kind `e` is upstream `Result.ofOption` at the kind it names. -/
theorem toITree_ofOption {α : Type u} (x : Option α) (e : Error) :
    toITree (RustM.ofOption x e) = IResult.ofOption x (ITreeModel.Error.ofStd e) := by
  cases x <;> rfl

/-- `massert` agrees with upstream `massert`; the flat failure is `panic`, upstream's is
`assertionFailure`. -/
theorem agrees_massert (b : Prop) [Decidable b] :
    Agrees (Aeneas.Std.massert b) (ITreeModel.massert b) := by
  unfold Aeneas.Std.massert ITreeModel.massert
  split <;> first | rfl | exact agrees_fail _ _

/-- `lift` is upstream `lift`. -/
theorem toITree_lift {α : Type u} (x : α) : toITree (Aeneas.Std.lift x) = ITreeModel.lift x :=
  rfl

end RustM

end Aeneas.Std

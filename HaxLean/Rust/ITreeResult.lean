/-
Copyright (c) the Aeneas contributors. Licensed under the Apache License,
Version 2.0 (the "License"); you may not use this file except in compliance with
the License. You may obtain a copy of the License at
http://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable law or
agreed to in writing, software distributed under the License is distributed on
an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and
limitations under the License.

The definitions of `Error`, `RustEffect`, `IResult` (upstream `Result`), `ok`, `vis`,
`fail`, `div`, `bind`, the order instances and `loop` are transcribed from
Source: AeneasVerif/aeneas at b08bf81f2524ee295a8c37444893acfc9c5f4dde,
  backends/lean/Aeneas/Std/Primitives.lean (lines 65-115, 268-279, 352-363, 465-474).
The map `RustM.toITree` and the theorems about it are by the CatCrypt Contributors.
-/

module

public import HaxLean.Rust.Primitives
public import HaxLean.Rust.Data.Coinductive.ITree
import all Init.Internal.Order.Basic

/-!
# The interaction-tree result monad of Aeneas and the flat `RustM`

Upstream Aeneas types its generated Lean code against `Result α := ITree RustEffect α`, an
interaction tree whose leaves are values (`ok := ret`), whose only event is a failure
(`fail e`, a `vis` node with an empty answer type) and whose bottom is `div`. The vendored
model `Aeneas.Std.RustM` of `HaxLean.Rust.Primitives` is the flat inductive
`ok | fail | div`. This module transcribes the upstream monad as `IResult` under the
namespace `Aeneas.Std.ITreeModel` and relates the two by the map `RustM.toITree`:

* `toITree` is a monad morphism (`toITree_pure`, `toITree_bind`) that sends `fail` to `fail`
  (`toITree_fail`) and `div` to `div` (`toITree_div`), and it is injective
  (`toITree_injective`);
* `toITree x = ok y` holds exactly when `x = .ok y` (`toITree_eq_ok_iff`);
* an `ok` run of the flat `loop` is an `ok` run of the upstream `loop` on the image of the
  loop body (`loop_toITree_of_ok`).

The Aeneas front of the compiler certifies a function by `fn a = .ok y` in the flat monad.
By these theorems that certificate is the statement that the corresponding upstream
`Result` computation is the leaf `ok y`.
-/

@[expose] public section

namespace Aeneas.Std.ITreeModel

open Aeneas.Data.Coinductive

universe u v w

/-- Error kinds of a failing computation in upstream Aeneas. -/
inductive Error where
  | assertionFailure : Error
  | integerOverflow : Error
  | divisionByZero : Error
  | arrayOutOfBounds : Error
  | maximumSizeExceeded : Error
  | panic : Error
  | undef : Error
deriving Repr, BEq, DecidableEq

/-- The events of the result monad: a failure with its error kind. -/
inductive RustEffect.Input : Type where
  | fail : Error → RustEffect.Input

/-- The answer type of an event: a failure has no answer. -/
def RustEffect.Output (i : RustEffect.Input) : Type :=
  match i with
  | .fail _ => PEmpty

/-- The effect signature of the result monad. -/
def RustEffect : Effect := {
  I := RustEffect.Input
  O := RustEffect.Output
}

/-- The result monad of upstream Aeneas: interaction trees over `RustEffect`. -/
def IResult (α : Type u) : Type u := ITree RustEffect α

/-- A successful computation: the leaf `ret a`. -/
def IResult.ok {α : Type u} (a : α) : IResult α := ITree.ret a

/-- An event node with its continuation. -/
def IResult.vis {α : Type u} (eff : RustEffect.Input) (k : RustEffect.Output eff → IResult α) :
    IResult α :=
  ITree.vis eff k

/-- A failing computation: the event `fail e`, which has no continuation. -/
def IResult.fail {α : Type u} (e : Error) : IResult α := IResult.vis (.fail e) PEmpty.elim

/-- The diverging computation. -/
def IResult.div {α : Type u} : IResult α := ITree.div

/-- Sequential composition: the bind of interaction trees. -/
def bind {α : Type u} {β : Type v} (x : IResult α) (f : α → IResult β) : IResult β :=
  ITree.bind x f

instance : Monad IResult where
  pure := IResult.ok
  bind := bind

/-- Binding a value runs the continuation on it. -/
@[simp] theorem bind_ok {α : Type u} {β : Type v} (x : α) (f : α → IResult β) :
    bind (.ok x) f = f x :=
  itree_ret_bind x f

/-- A failure propagates through bind. -/
@[simp] theorem bind_fail {α : Type u} {β : Type v} (e : Error) (f : α → IResult β) :
    bind (.fail e) f = .fail e := by
  exact (itree_vis_bind (RustEffect.Input.fail e) PEmpty.elim f).trans
    (congrArg (ITree.vis _) (funext fun x => (show PEmpty from x).elim))

/-- Divergence propagates through bind. -/
@[simp] theorem bind_div {α : Type u} {β : Type v} (f : α → IResult β) :
    bind .div f = .div :=
  itree_div_bind f

section Order

open Lean.Order

instance {α : Type u} : PartialOrder (IResult α) :=
  inferInstanceAs (PartialOrder (ITree RustEffect α))
noncomputable instance {α : Type u} : CCPO (IResult α) :=
  inferInstanceAs (CCPO (ITree RustEffect α))

/-- `bind` is monotone in both arguments, for `partial_fixpoint`. -/
@[partial_fixpoint_monotone]
theorem bind_mono {R : Type u} {γ : Sort w} {S : Type v} [PartialOrder γ]
    (f : γ → IResult R) (g : γ → R → IResult S) :
    monotone f → monotone g → monotone (fun x => bind (f x) (g x)) :=
  Aeneas.Data.Coinductive.bind_mono f g

end Order

/-- `loop body x` iterates `body` from `x` until it returns `done`. -/
def loop {α : Type u} {β : Type v} (body : α → IResult (ControlFlow α β)) (x : α) :
    IResult β :=
  bind (body x) fun r =>
  match r with
  | ControlFlow.cont x => loop body x
  | ControlFlow.done x => IResult.ok x
partial_fixpoint

/-! ## The map from the flat monad -/

/-- The error kind of upstream Aeneas named by an error kind of the flat model. -/
def Error.ofStd : Aeneas.Std.Error → Error
  | .panic => .panic
  | .undef => .undef

/-- Distinct flat error kinds name distinct upstream error kinds. -/
theorem Error.ofStd_injective : Function.Injective Error.ofStd := by
  intro a b h
  cases a <;> cases b <;> first | rfl | cases h

end Aeneas.Std.ITreeModel

namespace Aeneas.Std

open Aeneas.Data.Coinductive ITreeModel

universe u v

/-- The interaction tree of a flat result: `ok` to a leaf, `fail` to a failure event,
`div` to `div`. -/
def RustM.toITree {α : Type u} : RustM α → IResult α
  | .ok a => IResult.ok a
  | .fail e => IResult.fail (ITreeModel.Error.ofStd e)
  | .div => IResult.div

namespace RustM

/-- Unfolding lemma of `toITree` at `pure`: `toITree` preserves the unit of the monad. -/
@[simp] theorem toITree_pure {α : Type u} (a : α) : toITree (pure a : RustM α) = pure a := rfl

/-- Unfolding lemma of `toITree` at `ok`. -/
@[simp] theorem toITree_ok {α : Type u} (a : α) : toITree (.ok a : RustM α) = IResult.ok a := rfl

/-- Unfolding lemma of `toITree` at `fail`: a flat failure is a failure event. -/
@[simp] theorem toITree_fail {α : Type u} (e : Error) :
    toITree (.fail e : RustM α) = IResult.fail (ITreeModel.Error.ofStd e) := rfl

/-- Unfolding lemma of `toITree` at `div`: flat divergence is `ITree.div`. -/
@[simp] theorem toITree_div {α : Type u} : toITree (.div : RustM α) = IResult.div := rfl

/-- `toITree` commutes with bind: it is a monad morphism. -/
theorem toITree_bind {α β : Type u} (x : RustM α) (f : α → RustM β) :
    toITree (x >>= f) = toITree x >>= fun a => toITree (f a) := by
  cases x
  · exact (ITreeModel.bind_ok _ (fun a => toITree (f a))).symm
  · exact (ITreeModel.bind_fail _ (fun a => toITree (f a))).symm
  · exact (ITreeModel.bind_div (fun a => toITree (f a))).symm

/-- Distinct flat results have distinct interaction trees. -/
theorem toITree_injective {α : Type u} : Function.Injective (toITree (α := α)) := by
  intro x y h
  cases x <;> cases y <;>
    simp only [toITree, IResult.ok, IResult.fail, IResult.vis, IResult.div] at h
  all_goals grind [ITreeModel.Error.ofStd_injective, vis_inj_effect]

/-- The interaction tree of a flat result is the leaf `ok y` exactly when the result is
`ok y`. -/
theorem toITree_eq_ok_iff {α : Type u} (x : RustM α) (y : α) :
    toITree x = IResult.ok y ↔ x = .ok y :=
  ⟨fun h => toITree_injective (h.trans (toITree_ok y).symm), fun h => h ▸ rfl⟩

/-- An `ok` run of the flat `loop` is an `ok` run of the upstream `loop` on the image of the
loop body. The proof is fixpoint induction on the flat `loop`; its motive is admissible
because the flat bottom `div` is not `ok`. -/
theorem loop_toITree_of_ok {α : Type u} {β : Type v} (body : α → RustM (ControlFlow α β))
    (s : α) (y : β) (h : Aeneas.Std.loop body s = .ok y) :
    ITreeModel.loop (fun a => toITree (body a)) s = IResult.ok y := by
  revert s y
  delta Aeneas.Std.loop
  refine Lean.Order.fix_induct (Aeneas.Std.loop._proof_1 body)
    (motive := fun g => ∀ s y, g s = .ok y →
      ITreeModel.loop (fun a => toITree (body a)) s = IResult.ok y) ?_ ?_
  · apply Lean.Order.admissible_pi; intro s
    apply Lean.Order.admissible_pi; intro y
    apply Lean.Order.admissible_apply (β := fun _ => RustM β)
      (P := fun s r => r = .ok y →
        ITreeModel.loop (fun a => toITree (body a)) s = IResult.ok y) s
    exact Lean.Order.admissible_flatOrder _ (by intro h; cases h)
  · intro g IH s y hg
    dsimp only at hg
    rw [ITreeModel.loop.eq_1]
    cases hbe : body s with
    | ok r =>
      rw [hbe] at hg
      cases r with
      | cont x =>
        rw [toITree_ok, ITreeModel.bind_ok]
        exact IH x y hg
      | done x =>
        cases hg
        rw [toITree_ok, ITreeModel.bind_ok]
    | fail e => rw [hbe] at hg; cases hg
    | div => rw [hbe] at hg; cases hg

end RustM

end Aeneas.Std

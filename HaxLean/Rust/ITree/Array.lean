/-
Copyright (c) the Aeneas contributors. Licensed under the Apache License,
Version 2.0 (the "License"); you may not use this file except in compliance with
the License. You may obtain a copy of the License at
http://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable law or
agreed to in writing, software distributed under the License is distributed on
an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and
limitations under the License.

The definitions of `ListN`, `Slice`, `Array` and their operations `toList`, `fromList`,
`val`, `from`, `make`, `index_usize`, `update`, `to_slice` are transcribed from
Source: AeneasVerif/aeneas at b08bf81f2524ee295a8c37444893acfc9c5f4dde,
  backends/lean/Aeneas/Data/ListN.lean (lines 42-55),
  backends/lean/Aeneas/Std/SliceDef.lean (lines 15-37),
  backends/lean/Aeneas/Std/Array/Array.lean (lines 28-42, 98-99, 159-162, 266-270),
  backends/lean/Aeneas/Std/Array/ArraySlice.lean (lines 23-24).
The value maps and the agreement theorems are by the CatCrypt Contributors.
-/

module

public import HaxLean.Rust.ITree.Agree
public import HaxLean.Rust.Array

/-!
# Arrays of upstream Aeneas over the interaction-tree result

The vendored `Aeneas.Std.Array α n` is the subtype of lists of length `n`, and the vendored
`Slice α` the subtype of lists of length at most `Usize.max`. Upstream Aeneas at `b08bf81`
defines both as structures over the length-indexed list `ListN` (so that inductive types may
use them in positive positions). The module transcribes `ListN`, the upstream `Slice` and
`Array` and the array operations the compiler's Aeneas front reads, under the namespace
`Aeneas.Std.ITreeModel`, and relates them to the vendored ones through the value maps
`Array.toUp` and `Slice.toUp`, which keep the list of elements (`Array.toUp_val`,
`Slice.toUp_val`):

* `make` and `to_slice` commute with the value maps (`Array.toUp_make`,
  `Array.toUp_to_slice`);
* `index_usize` agrees with upstream's on the image of the array
  (`Array.index_usize_agrees`), and `update` does after the value map
  (`Array.update_agrees`), in the sense of `RustM.Agrees`: the vendored operations fail with
  `panic` where upstream fails with `arrayOutOfBounds`.

## Main definitions

* `ITreeModel.ListN`, `ITreeModel.Slice`, `ITreeModel.Array`
* `ITreeModel.Array.make`, `index_usize`, `update`, `to_slice`
* `Array.toUp`, `Slice.toUp`: the value maps

## Main results

* `Array.toUp_make`, `Array.toUp_to_slice`, `Array.index_usize_agrees`, `Array.update_agrees`
-/

@[expose] public section

set_option autoImplicit false

namespace Aeneas.Std.ITreeModel

universe u

/-- Upstream `ListN`: lists indexed by their length. -/
inductive ListN (α : Type u) : Nat → Type u where
  | nil : ListN α 0
  | cons {n : Nat} : α → ListN α n → ListN α n.succ

/-- The list of a length-indexed list. -/
def ListN.toList {α : Type u} {n : Nat} (l : ListN α n) : List α :=
  match l with
  | .nil => .nil
  | .cons a l' => .cons a l'.toList

/-- A list as a list indexed by its length. -/
def ListN.fromList {α : Type u} (l : List α) : ListN α l.length :=
  match l with
  | .nil => .nil
  | .cons a l' => .cons a (ListN.fromList l')

/-- `toList` inverts `fromList`. -/
theorem ListN.toList_fromList {α : Type u} (l : List α) : (ListN.fromList l).toList = l := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (List.cons a) ih

/-- The list of a `ListN α n` has length `n`. -/
theorem ListN.length_toList {α : Type u} {n : Nat} (l : ListN α n) : l.toList.length = n := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg Nat.succ ih

/-- A cast along an equation of lengths keeps the list. -/
theorem ListN.toList_cast {α : Type u} {m k : Nat} (h : m = k) (x : ListN α m) :
    (cast (congrArg (ListN α) h) x).toList = x.toList := by
  subst h
  rfl

/-- Upstream `Slice`: a length bounded by `Usize.max` and a list of that length. -/
structure Slice (α : Type u) where
  /-- The length. -/
  leng : Nat
  /-- The elements. -/
  list : ListN α leng
  /-- The length is at most `Usize.max`. -/
  bound : leng ≤ Usize.max

/-- The list of elements of a slice. -/
def Slice.val {α : Type u} (s : Slice α) : List α := s.list.toList

/-- The slice of a list of length at most `Usize.max`. -/
def Slice.from {α : Type u} (l : List α) (h : l.length ≤ Usize.max) : Slice α :=
  { leng := l.length, list := .fromList l, bound := h }

/-- Upstream `Array`: a list of length `n.val`. -/
structure Array (α : Type u) (n : Usize) where
  /-- The elements. -/
  list : ListN α n.val

/-- The list of elements of an array. -/
def Array.val {α : Type u} {n : Usize} (a : Array α n) : List α := a.list.toList

/-- The array of a list of length `n.val`. -/
def Array.from {α : Type u} {n : Usize} (l : List α) (h : l.length = n.val) : Array α n :=
  { list := cast (congrArg (ListN α) h) (.fromList l) }

/-- Upstream `Array.make`: the array with elements `init`. -/
def Array.make {α : Type u} (n : Usize) (init : List α) (hl : init.length = n.val := by simp) :
    Array α n :=
  .from init hl

/-- The elements of `Slice.from l h` are `l`. -/
theorem Slice.from_val {α : Type u} (l : List α) (h : l.length ≤ Usize.max) :
    (Slice.from l h).val = l :=
  ListN.toList_fromList l

/-- The elements of `Array.from l h` are `l`. -/
theorem Array.from_val {α : Type u} {n : Usize} (l : List α) (h : l.length = n.val) :
    (Array.from l h : Array α n).val = l := by
  unfold Array.from Array.val
  rw [ListN.toList_cast h, ListN.toList_fromList]

/-- `Array.from` depends only on the list. -/
theorem Array.from_congr {α : Type u} {n : Usize} {l₁ l₂ : List α} (hl : l₁ = l₂)
    (h₁ : l₁.length = n.val) (h₂ : l₂.length = n.val) :
    (Array.from l₁ h₁ : Array α n) = Array.from l₂ h₂ := by
  subst hl
  rfl

/-- The length of an array is `n.val`. -/
theorem Array.property {α : Type u} {n : Usize} (a : Array α n) : a.val.length = n.val :=
  ListN.length_toList a.list

/-- Upstream `Array.index_usize`: the element at `i`, or `arrayOutOfBounds`. The match is
on `v.val[i.val]?`, the unfolding of upstream's `GetElem?` instance at `Usize`. -/
def Array.index_usize {α : Type u} {n : Usize} (v : Array α n) (i : Usize) : IResult α :=
  match v.val[i.val]? with
  | none => IResult.fail .arrayOutOfBounds
  | some x => IResult.ok x

/-- Upstream `Array.update`: the array with position `i` set to `x`, or
`arrayOutOfBounds`. -/
def Array.update {α : Type u} {n : Usize} (v : Array α n) (i : Usize) (x : α) :
    IResult (Array α n) :=
  match v.val[i.val]? with
  | none => IResult.fail .arrayOutOfBounds
  | some _ => IResult.ok (.from (v.val.set i.val x) (by rw [List.length_set, v.property]))

/-- Upstream `Array.to_slice`: the array as a slice. -/
def Array.to_slice {α : Type u} {n : Usize} (v : Array α n) : Slice α :=
  .from v.val (Aeneas.Std.Array.length_le_max ⟨v.val, v.property⟩)

end Aeneas.Std.ITreeModel

namespace Aeneas.Std

open RustM

universe u

/-- The upstream array with the elements of a vendored array. -/
def Array.toUp {α : Type u} {n : Usize} (a : Array α n) : ITreeModel.Array α n :=
  ITreeModel.Array.from a.val a.property

/-- The upstream slice with the elements of a vendored slice. -/
def Slice.toUp {α : Type u} (s : Slice α) : ITreeModel.Slice α :=
  ITreeModel.Slice.from s.val s.property

/-- `Array.toUp` keeps the elements. -/
theorem Array.toUp_val {α : Type u} {n : Usize} (a : Array α n) : a.toUp.val = a.val :=
  ITreeModel.Array.from_val _ _

/-- `Slice.toUp` keeps the elements. -/
theorem Slice.toUp_val {α : Type u} (s : Slice α) : s.toUp.val = s.val :=
  ITreeModel.Slice.from_val _ _

/-- `make` commutes with the value map. -/
theorem Array.toUp_make {α : Type u} (n : Usize) (init : List α) (hl : init.length = n.val) :
    (Array.make n init hl).toUp = ITreeModel.Array.make n init hl := by
  grind [Array.toUp, Array.make, ITreeModel.Array.make]

/-- `to_slice` commutes with the value maps. -/
theorem Array.toUp_to_slice {α : Type u} {n : Usize} (a : Array α n) :
    a.to_slice.toUp = a.toUp.to_slice := by
  unfold Slice.toUp ITreeModel.Array.to_slice
  grind only [val_to_slice, toUp_val]

/-- Indexing agrees with upstream on the image of the array. -/
theorem Array.index_usize_agrees {α : Type u} {n : Usize} (a : Array α n) (i : Usize) :
    Agrees (a.index_usize i) (a.toUp.index_usize i) := by
  unfold Array.index_usize ITreeModel.Array.index_usize
  rw [Array.toUp_val]
  grind only [agrees_of_toITree_eq, getElem?_Usize_eq, = getElem?_neg, = getElem?_pos,
    agrees_fail, toITree_eq_ok_iff]

/-- Update agrees with upstream after the value map. -/
theorem Array.update_agrees {α : Type u} {n : Usize} (a : Array α n) (i : Usize) (x : α) :
    Agrees (Array.toUp <$> a.update i x) (a.toUp.update i x) := by
  unfold Array.update ITreeModel.Array.update
  rw [show a.toUp.val[i.val]? = a.val[i.val]? by rw [Array.toUp_val], Array.getElem?_Usize_eq]
  split
  next hg =>
    simp only [hg]
    exact ⟨_, rfl⟩
  next hg =>
    simp only [hg]
    change ITreeModel.IResult.ok _ = ITreeModel.IResult.ok _
    congr 1
    exact ITreeModel.Array.from_congr (by rw [Array.toUp_val]) _ _

end Aeneas.Std

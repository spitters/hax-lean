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
  backends/lean/Aeneas/Std/Array/Array.lean
  backends/lean/Aeneas/Std/Array/ArraySlice.lean
-/

module

public import HaxLean.Rust.Slice
public import HaxLean.Rust.Core

/-!
# Arrays

`Array α n` is a list of length `n`, with indexing, update, cloning, the `Default` and
`Copy` instances, and the conversions to and from slices.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Aeneas.Std

open RustM Error WP

/-- A Rust array `[α; n]`: a list of length `n`. -/
def Array (α : Type u) (n : Usize) := { l : List α // l.length = n.val }

instance (α : Type u) (n : Usize) : CoeOut (Array α n) (List α) where
  coe := λ v => v.val

instance {α : Type u} {n : Usize} [BEq α] : BEq (Array α n) := SubtypeBEq _

instance {α : Type u} {n : Usize} [BEq α] [LawfulBEq α] : LawfulBEq (Array α n) :=
  SubtypeLawfulBEq _

instance {α : Type u} {n : Usize} [Inhabited α] : Inhabited (Array α n) :=
  ⟨ ⟨ List.replicate n.val default, by simp ⟩ ⟩

/-- The empty array. -/
def Array.empty (α : Type u) : Array α (Usize.ofNat 0) := ⟨ [], by simp ⟩

@[grind =]
theorem Array.length_eq {α : Type u} {n : Usize} (a : Array α n) : a.val.length = n.val :=
  a.property

@[simp]
abbrev Array.length {α : Type u} {n : Usize} (v : Array α n) : Nat := v.val.length

@[simp]
abbrev Array.v {α : Type u} {n : Usize} (v : Array α n) : List α := v.val

/-- The array with elements `init`. -/
def Array.make {α : Type u} (n : Usize) (init : List α) (hl : init.length = n.val := by simp) :
  Array α n := ⟨ init, by apply hl ⟩

instance {α : Type u} {n : Usize} : GetElem (Array α n) Nat α (fun a i => i < a.val.length) where
  getElem a i h := getElem a.val i h

@[simp, grind =]
theorem Array.getElem_Nat_eq {α : Type u} {n : Usize} (v : Array α n) (i : Nat)
    (h : i < v.val.length) :
    v[i] = v.val[i] := rfl

instance {α : Type u} {n : Usize} : GetElem? (Array α n) Nat α (fun a i => i < a.val.length) where
  getElem? a i := getElem? a.val i

@[simp, grind =]
theorem Array.getElem?_Nat_eq {α : Type u} {n : Usize} (v : Array α n) (i : Nat) :
    v[i]? = v.val[i]? := by rfl

@[simp]
theorem Array.getElem!_Nat_eq {α : Type u} [Inhabited α] {n : Usize} (v : Array α n) (i : Nat) :
    v[i]! = v.val[i]! := by
  simp only [getElem!_def]; rfl

instance {α : Type u} {n : Usize} : GetElem (Array α n) Usize α
    (fun a i => i.val < a.val.length) where
  getElem a i h := getElem a.val i.val h

@[simp, grind =]
theorem Array.getElem_Usize_eq {α : Type u} {n : Usize} (v : Array α n) (i : Usize)
    (h : i.val < v.val.length) :
    v[i]'h = v.val[i.val] := rfl

instance {α : Type u} {n : Usize} : GetElem? (Array α n) Usize α
    (fun a i => i.val < a.val.length) where
  getElem? a i := getElem? a.val i.val

@[simp, grind =]
theorem Array.getElem?_Usize_eq {α : Type u} {n : Usize} (v : Array α n) (i : Usize) :
    v[i]? = v.val[i.val]? := by rfl

@[simp]
theorem Array.getElem!_Usize_eq {α : Type u} [Inhabited α] {n : Usize} (v : Array α n)
    (i : Usize) : v[i]! = v.val[i.val]! := by
  simp only [getElem!_def]; rfl

@[simp] abbrev Array.get? {α : Type u} {n : Usize} (v : Array α n) (i : Nat) : Option α :=
  getElem? v i
@[simp] abbrev Array.get! {α : Type u} {n : Usize} [Inhabited α] (v : Array α n) (i : Nat) : α :=
  getElem! v i

@[simp]
abbrev Array.slice {α : Type u} {n : Usize} [Inhabited α] (v : Array α n) (i j : Nat) :
    List α :=
  v.val.slice i j

/-- Indexing: a panic when `i` is out of range. -/
def Array.index_usize {α : Type u} {n : Usize} (v: Array α n) (i: Usize) : RustM α :=
  match v[i]? with
  | none => fail .panic
  | some x => ok x

/-- `[x; n]`. -/
def Array.repeat {α : Type u} (n : Usize) (x : α) : Array α n :=
  ⟨ List.replicate n.val x, by simp_all ⟩

@[simp]
theorem Array.repeat_val {α : Type u} (n : Usize) (x : α) :
    (Array.repeat n x).val = List.replicate n.val x := by
  simp only [Array.repeat]

theorem Array.index_usize_spec {α : Type u} {n : Usize} (v: Array α n) (i: Usize) :
    partialSpec (v.index_usize i)
      (fun x => ∃ _ : i.val < v.length, x = v.val[i.val])
      (fun | .panic => i.val ≥ v.length | _ => False)
      False := by
  unfold index_usize
  by_cases h : i.val < v.val.length
  · simp [h]
  · have : v.val[i.val]? = none := List.getElem?_eq_none (by omega)
    simp only [getElem?_Usize_eq, this, partialSpec_fail, length]
    omega

/-- `v` with position `i` replaced by `x`. -/
def Array.set {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) : Array α n :=
  ⟨ v.val.set i.val x, by have := v.property; simp [*] ⟩

/-- `v` with position `i` replaced by the value of `x`, when `x` is `some`. -/
def Array.set_opt {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: Option α) :
    Array α n :=
  ⟨ v.val.set_opt i.val x, by have := v.property; simp [*] ⟩

@[simp, grind =]
theorem Array.set_val_eq {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) :
  (v.set i x).val = v.val.set i.val x := by
  simp [set]

@[simp, grind =]
theorem Array.set_opt_val_eq {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: Option α) :
  (v.set_opt i x).val = v.val.set_opt i.val x := by
  simp [set_opt]

@[grind =]
theorem Array.set_length {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) :
  (v.set i x).length = v.length := by simp

/-- Update: a panic when `i` is out of range. -/
def Array.update {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) :
    RustM (Array α n) :=
  match v[i]? with
  | none => fail .panic
  | some _ =>
    ok ⟨ v.val.set i.val x, by have := v.property; simp [*] ⟩

theorem Array.update_spec {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x : α) :
    partialSpec (v.update i x)
      (fun nv => nv = v.set i x)
      (fun | .panic => i.val ≥ v.length | _ => False)
      False
  := by
  unfold update
  by_cases h : i.val < v.val.length
  · simp only [getElem?_Usize_eq, List.getElem?_eq_getElem h]
    rfl
  · have : v.val[i.val]? = none := List.getElem?_eq_none (by omega)
    simp only [getElem?_Usize_eq, this, partialSpec_fail, length]
    omega

/-- Mutable indexing: the element and the write-back function. -/
def Array.index_mut_usize {α : Type u} {n : Usize} (v: Array α n) (i: Usize) :
  RustM (α × (α -> Array α n)) := do
  let x ← index_usize v i
  ok (x, set v i)

theorem Array.index_mut_usize_spec {α : Type u} {n : Usize} (v: Array α n) (i: Usize) :
    partialSpec (v.index_mut_usize i)
      (uncurry' fun x back => ∃ _ : i.val < v.length, x = v.val[i.val] ∧ back = set v i)
      (fun | .panic => i.val ≥ v.length | _ => False)
      False := by
  have h := index_usize_spec v i
  simp only [partialSpec, index_mut_usize, Bind.bind, bind, uncurry'] at h ⊢
  cases hres : v.index_usize i <;> simp_all

/-- Clones every element of `s`. -/
def Array.clone {α : Type u} {n : Usize} (clone : α → RustM α) (s : Array α n) :
    RustM (Array α n) := do
  let s' ← List.clone clone s.val
  ok ⟨ s', by have := s'.property; have := s.property; omega ⟩

/-- `<[T; N] as Clone>::clone`. -/
def core.array.CloneArray.clone
  {T : Type} {N : Usize} (cloneInst : core.clone.Clone T) (a : Array T N) :
    RustM (Array T N) :=
  Array.clone cloneInst.clone a

/-- `<[T; N] as Clone>::clone_from`. -/
def core.array.CloneArray.clone_from {T : Type} {N : Usize} (cloneInst : core.clone.Clone T)
  (_self source : Array T N) : RustM (Array T N) :=
  Array.clone cloneInst.clone source

@[reducible]
def core.clone.CloneArray {T : Type} (N : Usize)
  (cloneCloneInst : core.clone.Clone T) : core.clone.Clone (Array T N) := {
  clone := core.array.CloneArray.clone cloneCloneInst
  clone_from := core.array.CloneArray.clone_from cloneCloneInst
}

/-- `s` with its elements from position `i` onwards replaced by those of `s'`. -/
def Array.setSlice! {α : Type u} {n} (s : Array α n) (i : Nat) (s' : List α) : Array α n :=
  ⟨s.val.setSlice! i s', by rw [List.length_setSlice!]; exact s.property⟩

/-- `<[T; N] as Default>::default`. -/
def core.default.DefaultArray.default {T : Type} (N : Usize)
    (defaultInst : core.default.Default T) : RustM (Array T N) := do
  let x ← defaultInst.default
  .ok (Array.repeat N x)

@[reducible]
def core.default.DefaultArray {T : Type} (N : Usize)
  (defaultInst : core.default.Default T) : core.default.Default (Array T N) := {
  default := core.default.DefaultArray.default N defaultInst
}

/-- `<[T; 0] as Default>::default`. -/
def core.default.DefaultArrayEmpty.default (T : Type) : RustM (Array T (Usize.ofNat 0)) :=
  ok ⟨ [], by simp ⟩

@[reducible]
def core.default.DefaultArrayEmpty (T : Type) :
    core.default.Default (Array T (Usize.ofNat 0)) := {
  default := core.default.DefaultArrayEmpty.default T
}

@[reducible]
def Array.Insts.CoreMarkerCopy {T : Type} (N : Std.Usize)
  (markerCopyInst : core.marker.Copy T) : core.marker.Copy (Array T N) := {
  cloneInst := core.clone.CloneArray N markerCopyInst.cloneInst
}

/-! ## Arrays as slices -/

theorem Array.length_le_max {α : Type u} {n : Usize} (v : Array α n) :
    v.val.length ≤ Usize.max := by
  rw [v.property]
  have := n.hBounds
  simp only [Usize.max, Usize.numBits]
  omega

/-- The array as a slice. -/
def Array.to_slice {α : Type u} {n : Usize} (v : Array α n) : Slice α :=
  ⟨ v.val, Array.length_le_max v ⟩

/-- The array with the elements of `s` when the lengths agree, `a` otherwise. -/
def Array.from_slice {α : Type u} {n : Usize} (a : Array α n) (s : Slice α) : Array α n :=
  if h: s.val.length = n.val then
    ⟨ s.val, by simp [*] ⟩
  else a

@[simp]
theorem Array.from_slice_val {α : Type u} {n : Usize} (a : Array α n) (ns : Slice α)
    (h : ns.val.length = n.val) :
  (from_slice a ns).val = ns.val
  := by simp [from_slice, *]

/-- The array as a mutable slice, with the write-back. -/
def Array.to_slice_mut {α : Type u} {n : Usize} (a : Array α n) :
  Slice α × (Slice α → Array α n) :=
  (Array.to_slice a, Array.from_slice a)

/-- `a[r.start..r.end]`: a panic unless `r.start ≤ r.end ≤ n`. -/
def Array.subslice {α : Type u} {n : Usize} (a : Array α n) (r : core.ops.range.Range Usize) :
    RustM (Slice α) :=
  if r.start.val ≤ r.end.val ∧ r.end.val ≤ a.val.length then
    ok ⟨ a.val.slice r.start.val r.end.val,
          Nat.le_trans (List.slice_length_le _ _ _) (Array.length_le_max a) ⟩
  else
    fail panic

/-- Replaces `a[r.start..r.end]` by `s`: a panic unless the range is valid and `s` has its
length. -/
def Array.update_subslice {α : Type u} {n : Usize} (a : Array α n)
    (r : core.ops.range.Range Usize) (s : Slice α) : RustM (Array α n) :=
  if h: r.start.val ≤ r.end.val ∧ r.end.val ≤ a.length ∧
      s.val.length = r.end.val - r.start.val then
    ok ⟨ a.val.setSlice! r.start s.val, by rw [List.length_setSlice!]; exact a.property ⟩
  else
    fail panic

/-- `<[T; N] as Index<I>>::index`. -/
def core.array.Array.index
  {T I Output : Type} {N : Usize} (inst : core.ops.index.Index (Slice T) I Output)
  (a : Array T N) (i : I) : RustM Output :=
  inst.index a.to_slice i

/-- `<[T; N] as IndexMut<I>>::index_mut`. -/
def core.array.Array.index_mut
  {T I Output : Type} {N : Usize} (inst : core.ops.index.IndexMut (Slice T) I Output)
  (a : Array T N) (i : I) :
  RustM (Output × (Output → Array T N)) := do
  let (s, back) ← inst.index_mut a.to_slice i
  ok (s, fun o => Array.from_slice a (back o))

def core.ops.index.IndexArray {T I Output : Type} {N : Usize}
  (inst : core.ops.index.Index (Slice T) I Output) :
  core.ops.index.Index (Array T N) I Output := {
  index := core.array.Array.index inst
}

def core.ops.index.IndexMutArray {T I Output : Type} {N : Usize}
  (inst : core.ops.index.IndexMut (Slice T) I Output) :
  core.ops.index.IndexMut (Array T N) I Output := {
  indexInst := core.ops.index.IndexArray inst.indexInst
  index_mut := core.array.Array.index_mut inst
}

/-- `core::array::TryFromSliceError`. -/
@[reducible]
def core.array.TryFromSliceError := Unit

@[simp, grind =]
theorem Array.val_to_slice {α : Type u} {n : Usize} (a : Array α n) : a.to_slice.val = a.val := by
  simp only [Array.to_slice]

/-- `<[T; N]>::as_slice`. -/
def core.array.Array.as_slice {T : Type} {N : Usize} (a : Array T N) : RustM (Slice T) :=
  ok (⟨ a.val, Array.length_le_max a ⟩)

/-- `<[T; N] as AsRef<[T]>>::as_ref`. -/
def Array.Insts.CoreConvertAsRefSlice.as_ref
    {T : Type} {N : Usize} (a : Array T N) : RustM (Slice T) :=
  ok (⟨ a.val, Array.length_le_max a ⟩)

/-- `<[T; N] as AsMut<[T]>>::as_mut`: the slice and the write-back. -/
def Array.Insts.CoreConvertAsMutSlice.as_mut
    {T : Type} {N : Usize} (a : Array T N) :
    RustM ((Slice T) × (Slice T → Array T N)) :=
  let back (s : Slice T) : Array T N :=
    if h : s.length = N then ⟨ s.val, h ⟩
    else a
  ok (⟨ a.val, Array.length_le_max a ⟩, back)

/-- `<[T; N]>::as_mut_slice`: the slice and the write-back. -/
def core.array.Array.as_mut_slice
  {T : Type} {N : Usize} (a : Array T N) :
  RustM (Slice T × (Slice T → Array T N)) :=
  let back (s : Slice T) : Array T N :=
    if h: s.length = N then ⟨ s.val, h ⟩
    else a
  ok (⟨ a.val, Array.length_le_max a ⟩, back)

@[simp]
theorem Array.index_SliceIndexRangeUsizeSlice {T : Type} {N : Usize}
    (a : Array T N) (r : core.ops.range.Range Usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice T)) a r =
    core.slice.index.SliceIndexRangeUsizeSlice.index r a.to_slice := by rfl

@[simp]
theorem Array.index_SliceIndexRangeToUsizeSlice {T : Type} {N : Usize}
    (a : Array T N) (r : core.ops.range.RangeTo Usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice T)) a r =
    core.slice.index.SliceIndexRangeToUsizeSlice.index r a.to_slice := by rfl

@[simp]
theorem Array.index_SliceIndexRangeFromUsizeSlice {T : Type} {N : Usize}
    (a : Array T N) (r : core.ops.range.RangeFrom Usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice T)) a r =
    core.slice.index.SliceIndexRangeFromUsizeSlice.index r a.to_slice := by rfl

end Aeneas.Std

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
  backends/lean/Aeneas/Std/Vec.lean
-/

module

public import HaxLean.Rust.Array
public import HaxLean.Rust.Slice

/-!
# Vectors

`alloc.vec.Vec α` is a list whose length is at most `Usize.max`, with `push`, indexing,
update, `extend_from_slice`, `resize`, the `Deref` instances and the conversions from
arrays and slices.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Aeneas

namespace Std

open RustM Error WP

namespace alloc.vec

/-- `alloc::vec::Vec`: a list whose length is at most `Usize.max`. -/
def Vec (α : Type u) := { l : List α // l.length ≤ Usize.max }

instance (α : Type u) : CoeOut (Vec α) (List α) where
  coe := λ v => v.val

instance {α : Type u} [BEq α] : BEq (Vec α) := SubtypeBEq _

instance {α : Type u} [BEq α] [LawfulBEq α] : LawfulBEq (Vec α) := SubtypeLawfulBEq _

theorem Vec.len_ineq {α : Type u} (v : Vec α) : v.val.length ≤ Usize.max := v.property

@[simp]
abbrev Vec.length {α : Type u} (v : Vec α) : Nat := v.val.length

@[simp]
abbrev Vec.v {α : Type u} (v : Vec α) : List α := v.val

/-- `Vec::new`. -/
abbrev Vec.new (α : Type u): Vec α := ⟨ [], Nat.zero_le _ ⟩

instance (α : Type u) : Inhabited (Vec α) := ⟨Vec.new α⟩

/-- `Vec::len`. -/
@[simp]
abbrev Vec.len {α : Type u} (v : Vec α) : Usize :=
  Usize.ofNatCore v.val.length (Usize.lt_pow_numBits_of_le_max v.property)

@[simp]
theorem Vec.len_val {α : Type u} (v : Vec α) : (Vec.len v).val = v.length :=
  by simp

instance {α : Type u} : GetElem (Vec α) Nat α (fun a i => i < a.val.length) where
  getElem a i h := getElem a.val i h

@[simp, grind =]
theorem Vec.getElem_Nat_eq {α : Type u} (v : Vec α) (i : Nat) (h : i < v.val.length) :
    v[i]'h = v.val[i] := rfl

instance {α : Type u} : GetElem? (Vec α) Nat α (fun a i => i < a.val.length) where
  getElem? a i := getElem? a.val i
  getElem! a i := getElem! a.val i

@[simp, grind =]
theorem Vec.getElem?_Nat_eq {α : Type u} (v : Vec α) (i : Nat) : v[i]? = v.val[i]? := by rfl

@[simp, grind =]
theorem Vec.getElem!_Nat_eq {α : Type u} [Inhabited α] (v : Vec α) (i : Nat) :
    v[i]! = v.val[i]! := by rfl

instance {α : Type u} : GetElem (Vec α) Usize α (fun a i => i < a.val.length) where
  getElem a i h := getElem a.val i.val h

@[simp, grind =]
theorem Vec.getElem_Usize_eq {α : Type u} (v : Vec α) (i : Usize) (h : i.val < v.val.length) :
    v[i]'h = v.val[i.val] := rfl

instance {α : Type u} : GetElem? (Vec α) Usize α (fun a i => i < a.val.length) where
  getElem? a i := getElem? a.val i.val
  getElem! a i := getElem! a.val i.val

@[simp, grind =]
theorem Vec.getElem?_Usize_eq {α : Type u} (v : Vec α) (i : Usize) :
    v[i]? = v.val[i.val]? := by rfl

@[simp, grind =]
theorem Vec.getElem!_Usize_eq {α : Type u} [Inhabited α] (v : Vec α) (i : Usize) :
    v[i]! = v.val[i.val]! := by rfl

@[simp]
abbrev Vec.get? {α : Type u} (v : Vec α) (i : Nat) : Option α := getElem? v i

@[simp]
abbrev Vec.get! {α : Type u} [Inhabited α] (v : Vec α) (i : Nat) : α := getElem! v i

/-- `v` with position `i` replaced by `x`. -/
def Vec.set {α : Type u} (v: Vec α) (i: Usize) (x: α) : Vec α :=
  ⟨ v.val.set i.val x, by have := v.property; simp [*] ⟩

/-- `v` with position `i` replaced by the value of `x`, when `x` is `some`. -/
def Vec.set_opt {α : Type u} (v: Vec α) (i: Usize) (x: Option α) : Vec α :=
  ⟨ v.val.set_opt i.val x, by have := v.property; simp [*] ⟩

@[simp, grind =]
theorem Vec.set_val_eq {α : Type u} (v: Vec α) (i: Usize) (x: α) :
  v.set i x = v.val.set i.val x := by
  simp [set]

@[simp, grind =]
theorem Vec.set_opt_val_eq {α : Type u} (v: Vec α) (i: Usize) (x: Option α) :
  (v.set_opt i x) = v.val.set_opt i.val x := by
  simp [set_opt]

/-- `Vec::push`: a panic when the new length exceeds `Usize.max`. -/
@[irreducible]
def Vec.push {α : Type u} (v : Vec α) (x : α) : RustM (Vec α)
  :=
  let nlen := List.length v.val + 1
  if h : nlen ≤ U32.max || nlen ≤ Usize.max then
    ok ⟨ List.concat v.val x, by
      simp only [List.concat_eq_append, List.length_append, List.length_cons, List.length_nil]
      rcases Usize.bounds_eq with hu | hu <;>
      · simp only [Bool.or_eq_true, decide_eq_true_eq] at h
        have : U32.max ≤ U64.max := by rw [U32.max_eq, U64.max_eq]; decide
        omega ⟩
  else
    fail panic

theorem Vec.push_spec {α : Type u} (v : Vec α) (x : α) (h : v.val.length < Usize.max) :
  v.push x ⦃ v1 =>
  v1.val = v.val ++ [x] ⦄ := by
  unfold push
  have : v.val.length + 1 ≤ Usize.max := h
  simp only [this, decide_true, Bool.or_true, ↓reduceDIte]
  exact (spec_ok _).2 (List.concat_eq_append ..)

/-- Overwrites position `i` with `x`; a panic when `i ≥ v.len()`. Rust's `Vec::insert`
shifts the tail instead; this model keeps the length. -/
def Vec.insert {α : Type u} (v: Vec α) (i: Usize) (x: α) : RustM (Vec α) :=
  if i.val < v.length then
    ok ⟨ v.val.set i x, by have := v.property; simp [*] ⟩
  else
    fail panic

theorem Vec.insert_spec {α : Type u} (v: Vec α) (i: Usize) (x: α)
  (hbound : i.val < v.length) :
  v.insert i x ⦃ nv => nv.val = v.val.set i x ⦄ := by
  simp only [insert, hbound, ↓reduceIte]
  exact (spec_ok _).2 rfl

/-- Indexing: a panic when `i` is out of range. -/
def Vec.index_usize {α : Type u} (v: Vec α) (i: Usize) : RustM α :=
  match v[i.val]? with
  | none => fail .panic
  | some x => ok x

theorem Vec.index_usize_spec {α : Type u} (v: Vec α) (i: Usize)
  (hbound : i.val < v.length) :
  v.index_usize i ⦃ x => x = v.val[i.val] ⦄ := by
  simp only [index_usize, getElem?_Nat_eq, List.getElem?_eq_getElem hbound]
  exact (spec_ok _).2 rfl

/-- Update: a panic when `i` is out of range. -/
def Vec.update {α : Type u} (v: Vec α) (i: Usize) (x: α) : RustM (Vec α) :=
  match v.val[i.val]? with
  | none => fail .panic
  | some _ =>
    ok ⟨ v.val.set i x, by have := v.property; simp [*] ⟩

theorem Vec.update_spec {α : Type u} (v: Vec α) (i: Usize) (x : α)
  (hbound : i.val < v.length) :
  v.update i x ⦃ nv => nv = v.set i x ⦄ := by
  simp only [update, List.getElem?_eq_getElem hbound]
  exact (spec_ok _).2 rfl

@[grind =]
theorem Vec.set_length {α : Type u} (v: Vec α) (i: Usize) (x: α) :
  (v.set i x).length = v.length := by simp

/-- Mutable indexing: the element and the write-back function. -/
def Vec.index_mut_usize {α : Type u} (v: Vec α) (i: Usize) :
  RustM (α × (α → Vec α)) :=
  match Vec.index_usize v i with
  | ok x =>
    ok (x, Vec.set v i)
  | fail e => fail e
  | div => div

theorem Vec.index_mut_usize_spec {α : Type u} (v: Vec α) (i: Usize)
  (hbound : i.val < v.length) :
  v.index_mut_usize i ⦃ x y => x = v.val[i.val] ∧ y = v.set i ⦄ := by
  simp only [index_mut_usize]
  have ⟨ x, h, hx ⟩ := spec_imp_exists (index_usize_spec v i hbound)
  rw [h]
  exact (spec_ok _).2 ⟨hx, rfl⟩

/-- `<Vec<T> as Index<I>>::index`. -/
def Vec.index {T I Output : Type} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (self : Vec T) (i : I) : RustM Output :=
  inst.index i self

/-- `<Vec<T> as IndexMut<I>>::index_mut`. -/
def Vec.index_mut {T I Output : Type} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (self : Vec T) (i : I) :
  RustM (Output × (Output → Vec T)) :=
  inst.index_mut i self

@[reducible]
def Vec.Index {T I Output : Type}
  (inst : core.slice.index.SliceIndex I (Slice T) Output) :
  core.ops.index.Index (alloc.vec.Vec T) I Output := {
  index := Vec.index inst
}

@[reducible]
def Vec.IndexMut {T I Output : Type}
  (inst : core.slice.index.SliceIndex I (Slice T) Output) :
  core.ops.index.IndexMut (alloc.vec.Vec T) I Output := {
  indexInst := Vec.Index inst
  index_mut := Vec.index_mut inst
}

@[simp]
theorem Vec.index_slice_index {α : Type} (v : Vec α) (i : Usize) :
  Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i =
  Vec.index_usize v i := by
  rfl

@[simp]
theorem Vec.index_mut_slice_index {α : Type} (v : Vec α) (i : Usize) :
  Vec.index_mut (core.slice.index.SliceIndexUsizeSlice α) v i =
  index_mut_usize v i := by
  simp only [Vec.index_mut, Vec.index_mut_usize, core.slice.index.Usize.index_mut,
    Slice.index_mut_usize, Bind.bind]
  show Std.bind (Slice.index_usize v i) _ = _
  cases h : Slice.index_usize v i <;> cases h' : Vec.index_usize v i <;>
    simp only [Std.bind] <;>
    (have : Slice.index_usize v i = Vec.index_usize v i := rfl) <;> simp_all <;> rfl

end alloc.vec

/-- `<[T]>::to_vec`. -/
def alloc.slice.Slice.to_vec
  {T : Type} (cloneInst : core.clone.Clone T) (s : Slice T) : RustM (alloc.vec.Vec T) := do
  Slice.clone cloneInst.clone s

theorem alloc.slice.Slice.to_vec_spec {T : Type} (cloneInst : core.clone.Clone T) (s : Slice T)
  (h : ∀ x ∈ s.val, cloneInst.clone x = ok x) :
  alloc.slice.Slice.to_vec cloneInst s ⦃ s' => s = s'⦄ := by
  simp only [to_vec]
  exact (Slice.clone_spec h)

/-- `<[T]>::into_vec`. -/
def alloc.slice.Slice.into_vec
  {T : Type} (s: Slice T) : (alloc.vec.Vec T) := s

/-- `vec![x; n]`: `n` clones of `x`. -/
def alloc.vec.from_elem
  {T : Type} (cloneInst : core.clone.Clone T)
  (x : T) (n : Usize) : RustM (alloc.vec.Vec T) := do
  let l ← List.clone cloneInst.clone (List.replicate n.val x)
  ok ⟨ l.val, by
    have hl : l.val.length = n.val := l.property.trans (List.length_replicate ..)
    have hn := n.hBounds
    simp only [Usize.max, Usize.numBits]
    omega ⟩

/-- `Vec::with_capacity`: the capacity is not modelled. -/
def alloc.vec.Vec.with_capacity (T : Type) (_ : Usize) : alloc.vec.Vec T := alloc.vec.Vec.new T

/-- `Vec::extend_from_slice`: clones `s` onto the end of `v`; a panic when the new length
exceeds `Usize.max`. -/
def alloc.vec.Vec.extend_from_slice {T : Type} (cloneInst : core.clone.Clone T)
  (v : alloc.vec.Vec T) (s : Slice T) : RustM (alloc.vec.Vec T) :=
  if h : v.length + s.length ≤ Usize.max then do
    match h' : Slice.clone cloneInst.clone s with
    | ok s' =>
      ok ⟨ v.val ++ s'.val , by
        have := Slice.clone_length h'
        simp only [List.length_append]
        simp only [alloc.vec.Vec.length, Slice.length] at h this
        omega ⟩
    | fail e => fail e
    | div => div
  else fail .panic

/-- `<Vec<T> as Deref>::deref`. -/
def alloc.vec.Vec.deref {T : Type} (v : alloc.vec.Vec T) : Slice T :=
  ⟨ v.val, v.property ⟩

@[reducible]
def core.ops.deref.DerefVec {T : Type} : core.ops.deref.Deref (alloc.vec.Vec T) (Slice T) := {
  deref := fun v => ok (alloc.vec.Vec.deref v)
}

/-- `<Vec<T> as DerefMut>::deref_mut`: the slice and the write-back. -/
def alloc.vec.Vec.deref_mut {T : Type} (v :  alloc.vec.Vec T) :
   (Slice T) × (Slice T → alloc.vec.Vec T) :=
   (⟨ v.val, v.property ⟩, λ s => ⟨ s.val, s.property ⟩)

@[reducible]
def core.ops.deref.DerefMutVec {T : Type} :
  core.ops.deref.DerefMut (alloc.vec.Vec T) (Slice T):= {
  derefInst := core.ops.deref.DerefVec
  deref_mut v := ok (alloc.vec.Vec.deref_mut v)
}

/-- `Vec::resize`: clones `value` when the vector grows. -/
def alloc.vec.Vec.resize {T : Type} (cloneInst : core.clone.Clone T)
  (v : alloc.vec.Vec T) (new_len : Usize) (value : T) : RustM (alloc.vec.Vec T) := do
  if new_len.val < v.length then
    ok ⟨ v.val.resize new_len value, by
      rw [List.resize_length]
      have := new_len.hBounds
      simp only [Usize.max, Usize.numBits]
      omega ⟩
  else
    let value ← cloneInst.clone value
    ok ⟨ v.val.resize new_len value, by
      rw [List.resize_length]
      have := new_len.hBounds
      simp only [Usize.max, Usize.numBits]
      omega ⟩

/-- `<Vec<T> as From<[T; N]>>::from`. -/
def alloc.vec.FromVecArray.from
  {T : Type} {N : Std.Usize} (a: Array T N) : RustM (alloc.vec.Vec T) :=
  ok ⟨ a.val, Array.length_le_max a ⟩

@[reducible]
def core.convert.FromVecArray (T : Type) (N : Std.Usize) : core.convert.From
  (alloc.vec.Vec T) (Array T N) := {
  «from» := alloc.vec.FromVecArray.from
}

/-- `<Box<[T]> as From<Vec<T>>>::from`. -/
def alloc.vec.FromBoxSliceVec.from {T : Type} (v : alloc.vec.Vec T) : RustM (Slice T) := ok v

@[reducible]
def core.convert.FromBoxSliceVec (T : Type) :
  core.convert.From (Slice T) (alloc.vec.Vec T) := {
  «from» := alloc.vec.FromBoxSliceVec.from
}

/-- `v` with its elements from position `i` onwards replaced by those of `s'`. -/
def alloc.vec.Vec.setSlice! {α : Type u} (s : alloc.vec.Vec α) (i : Nat) (s' : List α) :
    alloc.vec.Vec α :=
  ⟨s.val.setSlice! i s', by rw [List.length_setSlice!]; exact s.property⟩

@[simp, grind =]
theorem alloc.vec.Vec.setSlice!_length {α : Type u} (s : alloc.vec.Vec α) (i : Nat)
    (s' : List α) :
  (s.setSlice! i s').length = s.length := by
  simp only [Vec.length, Vec.setSlice!, List.length_setSlice!]

/-- `<Vec<T> as Clone>::clone`. -/
def alloc.vec.CloneVec.clone {T : Type} (cloneInst : core.clone.Clone T)
  (v : alloc.vec.Vec T) : RustM (alloc.vec.Vec T) :=
  Slice.clone cloneInst.clone v

@[reducible]
def core.clone.CloneallocvecVec {T : Type} (cloneInst : core.clone.Clone T) :
  core.clone.Clone (alloc.vec.Vec T) := {
  clone := alloc.vec.CloneVec.clone cloneInst
}

end Std

end Aeneas

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
  backends/lean/Aeneas/Std/SliceDef.lean
  backends/lean/Aeneas/Std/Slice.lean
-/

module

public import HaxLean.Rust.Array.Core
public import HaxLean.Rust.Range
public import HaxLean.Rust.Core
public import HaxLean.Rust.RawPtr
public import HaxLean.Rust.Scalar.Core
public import HaxLean.Rust.WP

/-!
# Slices

`Slice α` is a list whose length is at most `Usize.max`, with indexing, update,
subslicing by ranges, the `SliceIndex` trait instances, `copy_from_slice`, `split_at` and
`swap`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Aeneas.Std

/-- A Rust slice `[α]`: a list whose length is at most `Usize.max`. -/
def Slice (α : Type u) := { l : List α // l.length ≤ Usize.max }

/-- A length bounded by `Usize.max` is below `2 ^ UScalarTy.Usize.numBits`. -/
theorem Usize.lt_pow_numBits_of_le_max {n : Nat} (h : n ≤ Usize.max) :
    n < 2 ^ UScalarTy.Usize.numBits := by
  have := Nat.two_pow_pos UScalarTy.Usize.numBits
  simp only [Usize.max, Usize.numBits] at h
  omega

open RustM Error core.ops.range WP

instance (α : Type u) : CoeOut (Slice α) (List α) where
  coe := λ v => v.val

instance {α : Type u} [BEq α] : BEq (Slice α) := SubtypeBEq _

instance {α : Type u} [BEq α] [LawfulBEq α] : LawfulBEq (Slice α) := SubtypeLawfulBEq _

instance {α : Type u} [DecidableEq α] : DecidableEq (Slice α) :=
  inferInstanceAs (DecidableEq { _l : List α // _ })

theorem Slice.length_ineq {α : Type u} (s : Slice α) : s.val.length ≤ Usize.max := s.property

@[simp]
abbrev Slice.length {α : Type u} (v : Slice α) : Nat := v.val.length

@[simp]
abbrev Slice.v {α : Type u} (v : Slice α) : List α := v.val

/-- The empty slice. -/
def Slice.new (α : Type u) : Slice α := ⟨ [], Nat.zero_le _ ⟩

/-- `<[T]>::len`. -/
abbrev Slice.len {α : Type u} (v : Slice α) : Usize :=
  Usize.ofNatCore v.val.length (Usize.lt_pow_numBits_of_le_max v.property)

@[simp]
theorem Slice.len_val {α : Type u} (v : Slice α) : (Slice.len v).val = v.length :=
  by simp

instance {α : Type u} : GetElem (Slice α) Nat α (fun a i => i < a.val.length) where
  getElem a i h := getElem a.val i h

@[simp, grind =]
theorem Slice.getElem_Nat_eq {α : Type u} (v : Slice α) (i : Nat) (h : i < v.val.length) :
    v[i] = v.val[i] := rfl

instance {α : Type u} : GetElem? (Slice α) Nat α (fun a i => i < a.val.length) where
  getElem? a i := getElem? a.val i

@[simp, grind =]
theorem Slice.getElem?_Nat_eq {α : Type u} (v : Slice α) (i : Nat) : v[i]? = v.val[i]? := by rfl

@[simp]
theorem Slice.getElem!_Nat_eq {α : Type u} [Inhabited α] (v : Slice α) (i : Nat) :
    v[i]! = v.val[i]! := by
  simp only [getElem!_def]; rfl

instance {α : Type u} : GetElem (Slice α) Usize α (fun a i => i.val < a.val.length) where
  getElem a i h := getElem a.val i.val h

@[simp, grind =]
theorem Slice.getElem_Usize_eq {α : Type u} (v : Slice α) (i : Usize) (h : i.val < v.val.length) :
    v[i]'h = v.val[i.val] := rfl

instance {α : Type u} : GetElem? (Slice α) Usize α (fun a i => i < a.val.length) where
  getElem? a i := getElem? a.val i.val

@[simp, grind =]
theorem Slice.getElem?_Usize_eq {α : Type u} (v : Slice α) (i : Usize) :
    v[i]? = v.val[i.val]? := by rfl

@[simp]
theorem Slice.getElem!_Usize_eq {α : Type u} [Inhabited α] (v : Slice α) (i : Usize) :
    v[i]! = v.val[i.val]! := by
  simp only [getElem!_def]; rfl

@[simp] abbrev Slice.get? {α : Type u} (v : Slice α) (i : Nat) : Option α := getElem? v i
@[simp] abbrev Slice.get! {α : Type u} [Inhabited α] (v : Slice α) (i : Nat) : α := getElem! v i

/-- `v` with position `i` replaced by `x`. -/
def Slice.setAtNat {α : Type u} (v: Slice α) (i: Nat) (x: α) : Slice α :=
  ⟨ v.val.set i x, by have := v.property; simp [*] ⟩

/-- `v` with position `i` replaced by `x`. -/
def Slice.set {α : Type u} (v: Slice α) (i: Usize) (x: α) : Slice α :=
  Slice.setAtNat v i.val x

/-- `v` with position `i` replaced by the value of `x`, when `x` is `some`. -/
def Slice.set_opt {α : Type u} (v: Slice α) (i: Usize) (x: Option α) : Slice α :=
  ⟨ v.val.set_opt i.val x, by have := v.property; simp [*] ⟩

/-- `s` without its first `i` elements. -/
def Slice.drop {α : Type u} (s : Slice α) (i : Usize) : Slice α :=
  ⟨ s.val.drop i.val, by have := s.property; simp only [List.length_drop]; omega ⟩

@[simp]
theorem Slice.getElem!_val_drop {T : Type u} (s : Slice T) (i : Usize) :
  (s.drop i).val = s.val.drop i := by
  simp [drop]

@[simp]
abbrev Slice.slice {α : Type u} [Inhabited α] (s : Slice α) (i j : Nat) : List α :=
  s.val.slice i j

/-- Indexing: a panic when `i` is out of range. -/
def Slice.index_usize {α : Type u} (v: Slice α) (i: Usize) : RustM α :=
  match v[i]? with
  | none => fail .panic
  | some x => ok x

theorem Slice.eq_iff {α : Type u} (s0 s1 : Slice α) : s0 = s1 ↔ s0.val = s1.val :=
  Subtype.ext_iff

/-- `<[T]>::is_empty`. -/
@[simp]
def core.slice.Slice.is_empty {T : Type} (s : Slice T) : RustM Bool := ok (s.length = 0)

theorem core.slice.Slice.is_empty_spec {T : Type} (s : Slice T) :
  core.slice.Slice.is_empty s ⦃ b => b = (s.length = 0) ⦄ := by
  simp [is_empty]

theorem Slice.index_usize_spec {α : Type u} (v: Slice α) (i: Usize) :
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

@[simp, grind =]
theorem Slice.set_val_eq {α : Type u} (v: Slice α) (i: Usize) (x: α) :
  (v.set i x) = v.val.set i.val x := by
  simp [set, setAtNat]

@[simp]
theorem Slice.set_opt_val_eq {α : Type u} (v: Slice α) (i: Usize) (x: Option α) :
  (v.set_opt i x) = v.val.set_opt i.val x := by
  simp [set_opt]

theorem Slice.getElem!_Usize_set_ne
  {α : Type u} [Inhabited α] (a: Slice α) (i j : Usize) (x: α)
  (h : i.val ≠ j.val) : (a.set i x)[j]! = a[j]!
  := by
  simp only [getElem!_Usize_eq, set_val_eq]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne h]

theorem Slice.getElem!_Usize_set_eq
  {α : Type u} [Inhabited α] (a: Slice α) (i i' : Usize) (x: α)
  (h : i = i' ∧ i'.val < a.length) : getElem! (a.set i x) i' = x
  := by
  obtain ⟨rfl, h⟩ := h
  simp only [getElem!_Usize_eq, set_val_eq]; simp [h]

theorem Slice.getElem!_Nat_set_ne
  {α : Type u} [Inhabited α] (a: Slice α) (i : Usize) (j : Nat) (x: α)
  (h : i.val ≠ j) : (a.set i x)[j]! = a[j]!
  := by
  simp only [getElem!_Nat_eq, set_val_eq]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_set_ne h]

theorem Slice.getElem!_Nat_set_eq
  {α : Type u} [Inhabited α] (a: Slice α) (i : Usize) (i' : Nat) (x: α)
  (h : i.val = i' ∧ i' < a.length) : getElem! (a.set i x) i' = x
  := by
  obtain ⟨rfl, h⟩ := h
  simp only [getElem!_Nat_eq, set_val_eq]; simp [h]

theorem Slice.Inhabited_getElem_eq_getElem! {α : Type u} [Inhabited α] (v : Slice α) (i : Nat)
    (hi : i < v.length) :
    v[i] = v[i]! := by
  rw [Slice.getElem!_Nat_eq]
  exact List.Inhabited_getElem_eq_getElem! v.val i hi

theorem Slice.ext_getElem {α : Type u} {s1 s2 : Slice α}
    (hlen : s1.length = s2.length)
    (hget : ∀ (i : Nat) (_ : i < s1.length) (_ : i < s2.length), s1[i] = s2[i]) :
    s1 = s2 := by
  apply Subtype.ext
  exact List.ext_getElem hlen fun i h1 h2 => hget i h1 h2

@[simp, grind =]
theorem Slice.set_length {α : Type u} (v: Slice α) (i: Usize) (x: α) :
  (v.set i x).length = v.length := by simp

@[simp, grind =]
theorem Slice.setAtNat_length {α : Type u} (v: Slice α) (i: Nat) (x: α) :
  (v.setAtNat i x).length = v.length := by simp [setAtNat, Slice.length]

/-- Update: a panic when `i` is out of range. -/
def Slice.update {α : Type u} (v: Slice α) (i: Usize) (x: α) : RustM (Slice α) :=
  match v.val[i.val]? with
  | none => fail .panic
  | some _ =>
    ok ⟨ v.val.set i.val x, by have := v.property; simp [*] ⟩

theorem Slice.update_spec {α : Type u} (v: Slice α) (i: Usize) (x : α) :
    partialSpec (v.update i x)
      (fun nv => i.val < v.length ∧ nv = v.set i x)
      (fun | .panic => i.val ≥ v.length | _ => False)
      False := by
  unfold update
  by_cases h : i.val < v.val.length
  · simp only [List.getElem?_eq_getElem h, length]
    exact ⟨h, rfl⟩
  · have : v.val[i.val]? = none := List.getElem?_eq_none (by omega)
    simp only [this, partialSpec_fail, length]
    omega

/-- Mutable indexing: the element and the write-back function. -/
def Slice.index_mut_usize {α : Type u} (v: Slice α) (i: Usize) :
  RustM (α × (α → Slice α)) := do
  let x ← Slice.index_usize v i
  ok (x, Slice.set v i)

theorem Slice.index_mut_usize_spec {α : Type u} (v: Slice α) (i: Usize) :
    partialSpec (v.index_mut_usize i)
      (uncurry' fun x back => ∃ _ : i.val < v.length, x = v.val[i.val] ∧ back = Slice.set v i)
      (fun | .panic => i.val ≥ v.length | _ => False)
      False := by
  have h := index_usize_spec v i
  simp only [partialSpec, index_mut_usize, Bind.bind, bind, uncurry'] at h ⊢
  cases hres : v.index_usize i <;> simp_all

@[simp]
theorem Slice.update_index_eq α [Inhabited α] (x : Slice α) (i : Usize)
    (h : i.val < x.val.length) :
  x.set i (x.val[i.val]'h) = x := by
  apply Subtype.ext
  simp

/-- `s[r.start..r.end]`: a panic unless `r.start ≤ r.end ≤ s.len()`. -/
def Slice.subslice {α : Type u} (s : Slice α) (r : Range Usize) : RustM (Slice α) :=
  if r.start.val ≤ r.end.val ∧ r.end.val ≤ s.length then
    ok ⟨ s.val.slice r.start.val r.end.val,
          by
            have := s.val.slice_length_le r.start.val r.end.val
            have := s.property
            omega ⟩
  else
    fail panic

theorem Slice.subslice_spec {α : Type u} [Inhabited α] (s : Slice α) (r : Range Usize) :
    partialSpec (subslice s r)
      (fun ns => ns.val = s.slice r.start.val r.end.val ∧
        ∃ _ : r.start.val ≤ r.end.val, ∃ _ : r.end.val ≤ s.val.length,
        ∃ _ : ns.val.length = r.end.val - r.start.val,
        (∀ i (_ : i + r.start.val < r.end.val), ns[i]! = s[r.start.val + i]!))
      (fun | .panic => (r.start.val > r.end.val ∨ r.end.val > s.val.length) | _ => False)
      False
  := by
  unfold subslice
  split <;> rename_i h
  · simp only [slice]
    refine ⟨rfl, h.1, h.2, ?_, ?_⟩
    · rw [List.slice_length]; simp only [length] at h; omega
    · intro i hi
      exact (Slice.getElem!_Nat_eq _ _).trans
        ((List.getElem!_slice r.start.val r.end.val i s.val ⟨h.2, by omega⟩).trans
          (Slice.getElem!_Nat_eq _ _).symm)
  · simp only [partialSpec_fail, length] at h ⊢; omega

/-- Replaces `s[r.start..r.end]` by `ss`: a panic unless the range is valid and `ss` has
its length. -/
def Slice.update_subslice {α : Type u} (s : Slice α) (r : Range Usize) (ss : Slice α) :
    RustM (Slice α) :=
  if h: r.start.val ≤ r.end.val ∧ r.end.val ≤ s.length ∧ ss.val.length = r.end.val - r.start.val
  then
    ok ⟨ s.val.setSlice! r.start.val ss.val, by
      have := s.property; simp only [List.length_setSlice!]; exact this ⟩
  else
    fail panic

/-- `<[T]>::reverse`. -/
def core.slice.Slice.reverse {T : Type} (s : Slice T) : Slice T :=
  ⟨ s.val.reverse, by have := s.property; simp only [List.length_reverse]; exact this ⟩

/-- The trait `core::slice::index::SliceIndex`. -/
structure core.slice.index.SliceIndex (Self T Output : Type) where
  get : Self → T → RustM (Option Output)
  get_mut : Self → T → RustM (Option Output × (Option Output → T))
  get_unchecked : Self → ConstRawPtr T → RustM (ConstRawPtr Output)
  get_unchecked_mut : Self → MutRawPtr T → RustM (MutRawPtr Output)
  index : Self → T → RustM Output
  index_mut : Self → T → RustM (Output × (Output → T))

/-- `<[T] as Index<I>>::index`. -/
def core.slice.index.Slice.index
  {T I Output : Type} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (slice : Slice T) (i : I) : RustM Output :=
  inst.index i slice

/-- `<[T]>::get`. -/
def core.slice.Slice.get
  {T I Output : Type} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (s : Slice T) (i : I) : RustM (Option Output) :=
  inst.get i s

/-- `<[T]>::get_unchecked`, left opaque. -/
noncomputable opaque core.slice.Slice.get_unchecked
  {T : Type} {I : Type} {Output : Type}
  (SliceIndexInst : core.slice.index.SliceIndex I (Slice T) Output)
  (s : Slice T) (i : I) : RustM Output

/-- `<[T]>::get_mut`. -/
def core.slice.Slice.get_mut
  {T I Output : Type} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (s : Slice T) (i : I) : RustM ((Option Output) × (Option Output → Slice T)) :=
  inst.get_mut i s

/-- A subslice of a slice has a length bounded by `Usize.max`. -/
theorem Slice.slice_length_le_max {T : Type} (s : Slice T) (i j : Nat) :
    (s.val.slice i j).length ≤ Usize.max :=
  Nat.le_trans (List.slice_length_le i j s.val) s.property

/-- `setSlice!` preserves the bound `Usize.max` on the length. -/
theorem Slice.setSlice!_length_le_max {T : Type} (s : Slice T) (i : Nat) (l : List T) :
    (s.val.setSlice! i l).length ≤ Usize.max := by
  rw [List.length_setSlice!]; exact s.property

/-- `SliceIndex<Range<usize>>::get`. -/
def core.slice.index.SliceIndexRangeUsizeSlice.get {T : Type} (r : Range Usize) (s : Slice T) :
  RustM (Option (Slice T)) :=
  if r.start ≤ r.end ∧ r.end ≤ s.length then
    ok (some ⟨ s.val.slice r.start r.end, Slice.slice_length_le_max s _ _⟩)
  else ok none

/-- `SliceIndex<Range<usize>>::get_mut`. -/
def core.slice.index.SliceIndexRangeUsizeSlice.get_mut
  {T : Type} (r : Range Usize) (s : Slice T) :
    RustM (Option (Slice T) × (Option (Slice T) → Slice T)) :=
  if r.start ≤ r.end ∧ r.end ≤ s.length then
    ok (some ⟨ s.val.slice r.start r.end, Slice.slice_length_le_max s _ _⟩,
        fun s' =>
        match s' with
        | none => s
        | some s' =>
          if _h: s'.length = r.end - r.start then
            ⟨ List.setSlice! s.val r.start s'.val, Slice.setSlice!_length_le_max s _ _ ⟩
          else s )
  else ok (none, fun _ => s)

/-- `SliceIndex<Range<usize>>::get_unchecked`; the model fails with `undef`. -/
def core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked {T : Type} :
  Range Usize → ConstRawPtr (Slice T) → RustM (ConstRawPtr (Slice T)) :=
  fun _ _ => fail .undef

/-- `SliceIndex<Range<usize>>::get_unchecked_mut`; the model fails with `undef`. -/
def core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked_mut {T : Type} :
  Range Usize → MutRawPtr (Slice T) → RustM (MutRawPtr (Slice T)) :=
  fun _ _ => fail .undef

/-- `SliceIndex<Range<usize>>::index`: a panic unless `r.start ≤ r.end ≤ s.len()`. -/
def core.slice.index.SliceIndexRangeUsizeSlice.index {T : Type} (r : Range Usize) (s : Slice T) :
    RustM (Slice T) :=
  if r.start ≤ r.end ∧ r.end ≤ s.length then
    ok (⟨ s.val.slice r.start r.end, Slice.slice_length_le_max s _ _⟩)
  else fail .panic

/-- `SliceIndex<Range<usize>>::index_mut`: the subslice and its write-back. -/
def core.slice.index.SliceIndexRangeUsizeSlice.index_mut {T : Type} (r : Range Usize)
    (s : Slice T) :
  RustM (Slice T × (Slice T → Slice T)) :=
  if r.start ≤ r.end ∧ r.end ≤ s.length then
    ok (⟨ s.val.slice r.start r.end, Slice.slice_length_le_max s _ _⟩,
        fun s' => ⟨ List.setSlice! s.val r.start s', Slice.setSlice!_length_le_max s _ _ ⟩)
  else fail .panic

/-- `<[T] as IndexMut<I>>::index_mut`. -/
def core.slice.index.Slice.index_mut
  {T I Output : Type} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (s : Slice T) (i : I) : RustM (Output × (Output → Slice T)) :=
  inst.index_mut i s

@[reducible]
def core.slice.index.SliceIndexRangeUsizeSlice (T : Type) :
  core.slice.index.SliceIndex (Range Usize) (Slice T) (Slice T) := {
  get := core.slice.index.SliceIndexRangeUsizeSlice.get
  get_mut := core.slice.index.SliceIndexRangeUsizeSlice.get_mut
  get_unchecked := core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked
  get_unchecked_mut := core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked_mut
  index := core.slice.index.SliceIndexRangeUsizeSlice.index
  index_mut := core.slice.index.SliceIndexRangeUsizeSlice.index_mut
}

/-- `SliceIndex<RangeTo<usize>>::get`. -/
def core.slice.index.SliceIndexRangeToUsizeSlice.get
  {T : Type} (r : core.ops.range.RangeTo Usize) (s : Slice T) : RustM (Option (Slice T)) :=
  if r.end ≤ s.length then
    ok (some ⟨ s.val.slice 0 r.end, Slice.slice_length_le_max s _ _⟩)
  else ok none

/-- `SliceIndex<RangeTo<usize>>::get_mut`. -/
def core.slice.index.SliceIndexRangeToUsizeSlice.get_mut
  {T : Type} (r : core.ops.range.RangeTo Usize) (s : Slice T) :
  RustM ((Option (Slice T)) × (Option (Slice T) → Slice T)) :=
  if r.end ≤ s.length then
    ok (some ⟨ s.val.slice 0 r.end, Slice.slice_length_le_max s _ _⟩,
        fun s' =>
        match s' with
        | none => s
        | some s' =>
          if _h: s'.length = r.end then
            ⟨ List.setSlice! s.val 0 s'.val, Slice.setSlice!_length_le_max s _ _ ⟩
          else s )
  else ok (none, fun _ => s)

/-- `SliceIndex<RangeTo<usize>>::get_unchecked`; the model fails with `undef`. -/
def core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked
  {T : Type} (_ : core.ops.range.RangeTo Usize) (_ : ConstRawPtr (Slice T)) :
    RustM (ConstRawPtr (Slice T)) :=
  fail .undef

/-- `SliceIndex<RangeTo<usize>>::get_unchecked_mut`; the model fails with `undef`. -/
def core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked_mut
  {T : Type} (_ : core.ops.range.RangeTo Usize) (_ : MutRawPtr (Slice T)) :
  RustM (MutRawPtr (Slice T)) :=
  fail .undef

/-- `SliceIndex<RangeTo<usize>>::index`: a panic unless `r.end ≤ s.len()`. -/
def core.slice.index.SliceIndexRangeToUsizeSlice.index
  {T : Type} (r : core.ops.range.RangeTo Usize) (s : Slice T) : RustM (Slice T) :=
  if r.end ≤ s.length then
    ok (⟨ s.val.slice 0 r.end, Slice.slice_length_le_max s _ _⟩)
  else fail .panic

/-- `SliceIndex<RangeTo<usize>>::index_mut`: the prefix and its write-back. -/
def core.slice.index.SliceIndexRangeToUsizeSlice.index_mut
  {T : Type} (r : core.ops.range.RangeTo Usize) (s : Slice T) :
  RustM ((Slice T) × (Slice T → Slice T)) :=
  if r.end ≤ s.length then
    ok (⟨ s.val.slice 0 r.end, Slice.slice_length_le_max s _ _⟩,
        fun s' => ⟨ List.setSlice! s.val 0 s'.val, Slice.setSlice!_length_le_max s _ _ ⟩)
  else fail .panic

@[reducible]
def core.slice.index.SliceIndexRangeToUsizeSlice (T : Type) :
  core.slice.index.SliceIndex (core.ops.range.RangeTo Usize) (Slice T) (Slice
  T) := {
  get := core.slice.index.SliceIndexRangeToUsizeSlice.get
  get_mut := core.slice.index.SliceIndexRangeToUsizeSlice.get_mut
  get_unchecked := core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked
  get_unchecked_mut := core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked_mut
  index := core.slice.index.SliceIndexRangeToUsizeSlice.index
  index_mut := core.slice.index.SliceIndexRangeToUsizeSlice.index_mut
}

/-! ## `SliceIndex<RangeFull, [T]>`: the whole slice. -/

@[simp]
abbrev core.slice.index.SliceIndexRangeFullSlice.get
  {T : Type} (_ : core.ops.range.RangeFull) (s : Slice T) : RustM (Option (Slice T)) :=
  ok (some s)

@[simp]
def core.slice.index.SliceIndexRangeFullSlice.get_mut
  {T : Type} (_ : core.ops.range.RangeFull) (s : Slice T) :
  RustM (Option (Slice T) × (Option (Slice T) → Slice T)) :=
  ok (some s, fun s' => match s' with | some updated => updated | none => s)

/-- `SliceIndex<RangeFull>::get_unchecked`, left opaque. -/
opaque core.slice.index.SliceIndexRangeFullSlice.get_unchecked
  {T : Type} (_ : core.ops.range.RangeFull) (s : ConstRawPtr (Slice T)) :
  RustM (ConstRawPtr (Slice T)) :=
  fail .undef

/-- `SliceIndex<RangeFull>::get_unchecked_mut`, left opaque. -/
opaque core.slice.index.SliceIndexRangeFullSlice.get_unchecked_mut
  {T : Type} (_ : core.ops.range.RangeFull) (s : MutRawPtr (Slice T)) :
  RustM (MutRawPtr (Slice T)) :=
  fail .undef

@[simp]
def core.slice.index.SliceIndexRangeFullSlice.index
  {T : Type} (_ : core.ops.range.RangeFull) (s : Slice T) : RustM (Slice T) :=
  ok s

@[simp]
def core.slice.index.SliceIndexRangeFullSlice.index_mut
  {T : Type} (_ : core.ops.range.RangeFull) (s : Slice T) :
  RustM (Slice T × (Slice T → Slice T)) :=
  ok (s, fun updated => updated)

@[reducible]
def core.slice.index.SliceIndexRangeFullSlice (T : Type) :
  core.slice.index.SliceIndex core.ops.range.RangeFull (Slice T) (Slice T) := {
  get := core.slice.index.SliceIndexRangeFullSlice.get
  get_mut := core.slice.index.SliceIndexRangeFullSlice.get_mut
  get_unchecked := core.slice.index.SliceIndexRangeFullSlice.get_unchecked
  get_unchecked_mut := core.slice.index.SliceIndexRangeFullSlice.get_unchecked_mut
  index := core.slice.index.SliceIndexRangeFullSlice.index
  index_mut := core.slice.index.SliceIndexRangeFullSlice.index_mut
}

/-- `Index<I>` for slices. -/
def core.ops.index.IndexSlice {T I Output : Type}
  (inst : core.slice.index.SliceIndex I (Slice T) Output) :
  core.ops.index.Index (Slice T) I Output := {
  index := core.slice.index.Slice.index inst
}

/-- `IndexMut<I>` for slices. -/
def core.ops.index.IndexMutSlice {T I Output : Type}
  (inst : core.slice.index.SliceIndex I (Slice T) Output) :
  core.ops.index.IndexMut (Slice T) I Output := {
  indexInst := core.ops.index.IndexSlice inst
  index_mut := core.slice.index.Slice.index_mut inst
}

@[simp]
abbrev core.slice.index.Usize.get
  {T : Type} (i : Usize) (s : Slice T) : RustM (Option T) :=
  ok s[i]?

@[simp]
abbrev core.slice.index.Usize.get_mut
  {T : Type} (i : Usize) (s : Slice T) : RustM (Option T × (Option T → Slice T)) :=
  ok (s[i]?, s.set_opt i)

/-- `SliceIndex<usize>::get_unchecked`; the model fails with `undef`. -/
def core.slice.index.Usize.get_unchecked
  {T : Type} : Usize → ConstRawPtr (Slice T) → RustM (ConstRawPtr T) :=
  fun _ _ => fail .undef

/-- `SliceIndex<usize>::get_unchecked_mut`; the model fails with `undef`. -/
def core.slice.index.Usize.get_unchecked_mut
  {T : Type} : Usize → MutRawPtr (Slice T) → RustM (MutRawPtr T) :=
  fun _ _ => fail .undef

@[simp]
abbrev core.slice.index.Usize.index {T : Type} (i : Usize) (s : Slice T) : RustM T :=
  Slice.index_usize s i

@[simp]
abbrev core.slice.index.Usize.index_mut {T : Type}
  (i : Usize) (s : Slice T) : RustM (T × (T → (Slice T))) :=
  Slice.index_mut_usize s i

@[reducible]
def core.slice.index.SliceIndexUsizeSlice (T : Type) :
  core.slice.index.SliceIndex Usize (Slice T) T := {
  get := core.slice.index.Usize.get
  get_mut := core.slice.index.Usize.get_mut
  get_unchecked := core.slice.index.Usize.get_unchecked
  get_unchecked_mut := core.slice.index.Usize.get_unchecked_mut
  index := core.slice.index.Usize.index
  index_mut := core.slice.index.Usize.index_mut
}

/-- `<[T]>::copy_from_slice`: a panic when the lengths differ. -/
def core.slice.Slice.copy_from_slice {T : Type} (_ : core.marker.Copy T)
  (s : Slice T) (src: Slice T) : RustM (Slice T) :=
  if s.len = src.len then ok src
  else fail panic

/-- `SliceIndex<RangeFrom<usize>>::get`. -/
def core.slice.index.SliceIndexRangeFromUsizeSlice.get {T : Type}
    (r : core.ops.range.RangeFrom Usize) (s : Slice T) : RustM (Option (Slice T)) :=
  if  r.start ≤ s.length then
    ok (some (s.drop r.start))
  else ok none

/-- `SliceIndex<RangeFrom<usize>>::get_mut`. -/
def core.slice.index.SliceIndexRangeFromUsizeSlice.get_mut
  {T : Type} (r : core.ops.range.RangeFrom Usize) (s : Slice T) :
  RustM ((Option (Slice T)) × (Option (Slice T) → Slice T)) :=
  if r.start ≤ s.length then
    ok (some (s.drop r.start),
        fun s' => match s' with
        | none => s
        | some s' =>
          if h: s'.length + s.length - r.start.val ≤ Usize.max then
            ⟨ s'.val ++ s.val.drop r.start.val, by
              have := s'.property
              simp only [List.length_append, List.length_drop]
              simp only [Slice.length] at h
              omega ⟩
          else s)
  else ok (none, fun _ => s)

/-- `SliceIndex<RangeFrom<usize>>::get_unchecked`; the model fails with `undef`. -/
def core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked {T : Type} :
  core.ops.range.RangeFrom Usize → ConstRawPtr (Slice T) → RustM (ConstRawPtr (Slice T)) :=
  fun _ _ => fail .undef

/-- `SliceIndex<RangeFrom<usize>>::get_unchecked_mut`; the model fails with `undef`. -/
def core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked_mut {T : Type} :
  core.ops.range.RangeFrom Usize → MutRawPtr (Slice T) → RustM (MutRawPtr (Slice T)) :=
  fun _ _ => fail .undef

/-- `SliceIndex<RangeFrom<usize>>::index`: fails with `undef` unless `r.start ≤ s.len()`. -/
def core.slice.index.SliceIndexRangeFromUsizeSlice.index {T : Type}
  (r : core.ops.range.RangeFrom Usize) (s : Slice T) : RustM (Slice T) :=
  if r.start.val ≤ s.length then
    ok (s.drop r.start)
  else fail .undef

/-- `SliceIndex<RangeFrom<usize>>::index_mut`: the suffix and its write-back. -/
def core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut {T : Type}
  (r : core.ops.range.RangeFrom Usize) (s : Slice T) :
    RustM ((Slice T) × (Slice T → Slice T)) :=
  if r.start ≤ s.length then
    let s1 := s.drop r.start
    ok ( s1,
         fun s2 => ⟨ s.val.setSlice! r.start s2, Slice.setSlice!_length_le_max s _ _ ⟩)
  else fail .panic

theorem _SliceIndexRangeFromUsizeSlice.index_mut.test {T : Type} (s : Slice T)
    (r : core.ops.range.RangeFrom Usize) (h : r.start ≤ s.length) :
  match core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut r s with
  | ok (s1, back) =>
    back s1 = s
  | _ => False := by
  unfold core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut
  simp only [h, ↓reduceIte]
  apply Subtype.ext
  show s.val.setSlice! r.start.val (s.val.drop r.start.val) = s.val
  apply List.ext_getElem?
  intro j
  by_cases hj : j < r.start.val
  · exact List.setSlice!_getElem?_prefix _ _ _ _ hj
  · by_cases hj2 : j < s.val.length
    · rw [List.setSlice!_getElem?_middle _ _ _ _ ⟨by omega, by simp; omega, hj2⟩,
        List.getElem?_drop]
      congr 1; omega
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

@[reducible]
def core.slice.index.SliceIndexRangeFromUsizeSlice (T : Type) :
  core.slice.index.SliceIndex (core.ops.range.RangeFrom Usize) (Slice T) (Slice T) := {
  get := core.slice.index.SliceIndexRangeFromUsizeSlice.get
  get_mut := core.slice.index.SliceIndexRangeFromUsizeSlice.get_mut
  get_unchecked :=
    core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked
  get_unchecked_mut :=
    core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked_mut
  index := core.slice.index.SliceIndexRangeFromUsizeSlice.index
  index_mut :=
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut
}

/-- Clones every element of `s`. -/
def Slice.clone {T : Type} (clone : T → RustM T) (s : Slice T) : RustM (Slice T) := do
  let s' ← List.clone clone s.val
  ok ⟨ s', by have := s'.property; have := s.property; omega ⟩

theorem Slice.clone_length {T : Type} {clone : T → RustM T} {s s' : Slice T}
    (h : Slice.clone clone s = ok s') :
  s'.length = s.length := by
  simp only [Slice.clone, Bind.bind] at h
  cases hc : List.clone clone s.val with
  | ok l =>
    rw [hc] at h
    simp only [bind_ok] at h
    cases h
    exact l.property
  | fail e => rw [hc] at h; cases h
  | div => rw [hc] at h; cases h

theorem Slice.clone_spec {T : Type} {clone : T → RustM T} {s : Slice T}
    (h : ∀ x ∈ s.val, clone x = ok x) :
  Slice.clone clone s ⦃ s' => s = s' ⦄ := by
  have ⟨ l, hl, h1, _ ⟩ := spec_imp_exists (List.clone_spec h)
  show spec (Std.bind (List.clone clone s.val) _) _
  rw [hl, bind_ok]
  refine (spec_ok _).2 ?_
  apply Subtype.ext
  exact h1.symm

/-- `<[T]>::split_at`: a panic when `n > s.len()`. -/
def core.slice.Slice.split_at {T : Type} (s : Slice T) (n : Usize) :
  RustM ((Slice T) × (Slice T)) :=
  if h0 : n ≤ s.length then
    let s0 := (s.val.splitAt n.val).fst
    let s1 := (s.val.splitAt n.val).snd
    let s0 : Slice T := ⟨ s0, by
      have := List.splitAt_length n.val s.val; have := s.property; simp +zetaDelta at *; omega ⟩
    let s1 : Slice T := ⟨ s1, by
      have := List.splitAt_length n.val s.val; have := s.property; simp +zetaDelta at *; omega ⟩
    ok (s0, s1)
  else fail .panic

/-- `<[T]>::split_at_mut`: the two halves and the write-back. -/
def core.slice.Slice.split_at_mut {T : Type} (s : Slice T) (n : Usize) :
  RustM (((Slice T) × (Slice T)) × (((Slice T) × (Slice T)) → Slice T)) :=
  if h0 : n ≤ s.length then
    let s0 := (s.val.splitAt n.val).fst
    let s1 := (s.val.splitAt n.val).snd
    let back (s' : Slice T × Slice T) : Slice T :=
      let s0' := s'.fst
      let s1' := s'.snd
      if h1 : s0'.length = s0.length ∧ s1'.length = s1.length then
        ⟨ s0'.val ++ s1'.val, by
          have := List.splitAt_length n.val s.val; have := s.property
          simp +zetaDelta at *; omega ⟩
      else s
    let s0 : Slice T := ⟨ s0, by
      have := List.splitAt_length n.val s.val; have := s.property; simp +zetaDelta at *; omega ⟩
    let s1 : Slice T := ⟨ s1, by
      have := List.splitAt_length n.val s.val; have := s.property; simp +zetaDelta at *; omega ⟩
    ok ((s0, s1), back)
  else fail .panic

/-- `<[T]>::swap`: panics when `a` or `b` is out of range. -/
def core.slice.Slice.swap {T : Type} (s : Slice T) (a b : Usize) : RustM (Slice T) := do
  let av ← Slice.index_usize s a
  let bv ← Slice.index_usize s b
  let s1 ← Slice.update s a bv
  Slice.update s1 b av

@[simp]
theorem Slice.index_mut_SliceIndexRangeUsizeSliceInst {α : Type} (s : Slice α)
    (r : core.ops.range.Range Usize) :
  core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice α) s r =
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut r s := by
  rfl

@[simp]
theorem Slice.index_SliceIndexRangeUsizeSliceInst {α : Type} (s : Slice α)
    (r : core.ops.range.Range Usize) :
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice α) s r =
    core.slice.index.SliceIndexRangeUsizeSlice.index r s := by
  rfl

/-- `s` with its elements from position `i` onwards replaced by those of `s'`. -/
def Slice.setSlice! {α : Type u} (s : Slice α) (i : Nat) (s' : List α) : Slice α :=
  ⟨s.val.setSlice! i s', by rw [List.length_setSlice!]; exact s.property⟩

@[simp, grind =]
theorem Slice.setSlice!_length {α : Type u} (s : Slice α) (i : Nat) (s' : List α) :
  (s.setSlice! i s').length = s.length := by
  simp only [Slice.length, Slice.setSlice!, List.length_setSlice!]

@[simp]
theorem Slice.setSlice!_val {α : Type u} (s : Slice α) (i : Nat) (s' : List α) :
  (s.setSlice! i s').val = s.val.setSlice! i s' := by
  simp only [setSlice!]

@[simp]
theorem Slice.index_mut_SliceIndexRangeToUsizeSliceInst {α : Type} (s : Slice α)
    (r : core.ops.range.RangeTo Usize) :
  core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice α) s r =
  core.slice.index.SliceIndexRangeToUsizeSlice.index_mut r s := by rfl

@[simp]
theorem Slice.index_SliceIndexRangeToUsizeSliceInst {α : Type} (s : Slice α)
    (r : core.ops.range.RangeTo Usize) :
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice α) s r =
  core.slice.index.SliceIndexRangeToUsizeSlice.index r s := by rfl

@[simp]
theorem Slice.index_mut_SliceIndexRangeFromUsizeSliceInst {α : Type} (s : Slice α)
    (r : core.ops.range.RangeFrom Usize) :
  core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeFromUsizeSlice α) s r =
  core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut r s := by rfl

@[simp]
theorem Slice.index_SliceIndexRangeFromUsizeSliceInst {α : Type} (s : Slice α)
    (r : core.ops.range.RangeFrom Usize) :
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice α) s r =
  core.slice.index.SliceIndexRangeFromUsizeSlice.index r s := by rfl

theorem core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec {α : Type}
    (r : core.ops.range.Range Usize) (s : Slice α) (h0 : r.start ≤ r.end)
    (h1 : r.end ≤ s.length) :
    core.slice.index.SliceIndexRangeUsizeSlice.index r s ⦃ (s1 : Slice α) =>
      s1.val = s.val.slice r.start r.end ∧
      s1.length = r.end - r.start ⦄ := by
  simp only [UScalar.le_equiv] at h0
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index, UScalar.le_equiv, h0, h1,
    and_self, ↓reduceIte]
  refine (spec_ok _).2 ⟨rfl, ?_⟩
  show (List.slice r.start.val r.end.val s.val).length = r.end.val - r.start.val
  rw [List.slice_length]; simp only [Slice.length] at h1; omega

theorem core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec {α : Type}
    (r : core.ops.range.RangeTo Usize) (s : Slice α) (h : r.end ≤ s.length) :
  core.slice.index.SliceIndexRangeToUsizeSlice.index r s
    ⦃ s1 =>
      s1.val = s.val.slice 0 r.end ∧
      s1.length = r.end ⦄ := by
  simp only [core.slice.index.SliceIndexRangeToUsizeSlice.index, h, ↓reduceIte]
  refine (spec_ok _).2 ⟨rfl, ?_⟩
  show (List.slice 0 r.end.val s.val).length = r.end.val
  rw [List.slice_length]; simp only [Slice.length] at h; omega

theorem core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec {α : Type}
    (r : core.ops.range.RangeFrom Usize) (s : Slice α) (h : r.start ≤ s.length) :
  core.slice.index.SliceIndexRangeFromUsizeSlice.index r s
    ⦃ s1 =>
      s1.val = s.val.drop r.start ∧
      s1.length = s.length - r.start.val ⦄ := by
  simp only [core.slice.index.SliceIndexRangeFromUsizeSlice.index, h, ↓reduceIte]
  exact (spec_ok _).2 ⟨rfl, List.length_drop⟩

theorem core.slice.Slice.copy_from_slice.step_spec {α : Type} (copyInst : core.marker.Copy α)
    (s0 s1 : Slice α)
  (h : s0.length = s1.length) :
  core.slice.Slice.copy_from_slice copyInst s0 s1 ⦃ s1' => s1' = s1 ⦄ := by
  have : s0.len = s1.len := by
    apply UScalar.eq_imp; simp only [Slice.len_val]; exact h
  simp only [copy_from_slice, this, ↓reduceIte, spec_ok]

/-- Applies `f` to every element, propagating failure and divergence. -/
def Slice.mapM {α β : Type} (f : α → RustM β) (x : Slice α) : RustM (Slice β) :=
  match h : x.val.mapM f with
  | ok xs  => ok ⟨xs, List.mapM_RustM_length h ▸ x.property⟩
  | fail e => fail e
  | div    => div

/-- `<[T]>::fill(v)`: every element replaced by a clone of `v`. -/
def core.slice.Slice.fill {T : Type} (cloneInst : core.clone.Clone T)
    (s : Slice T) (v : T) : RustM (Slice T) :=
  match h : s.val.mapM (fun _ => cloneInst.clone v) with
  | .ok val => .ok ⟨val, List.mapM_RustM_length h ▸ s.property⟩
  | .fail e => .fail e
  | .div => .div

end Aeneas.Std

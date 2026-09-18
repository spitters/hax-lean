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
  backends/lean/Aeneas/Data/List/List.lean
-/

module

public import HaxLean.Rust.Primitives

/-!
# List operations used by the slice, array and vector models

`set_opt`, `slice`, `resize`, `setSlice!` and their length and indexing lemmas.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace List

open Aeneas

section
variable {α : Type u} {β : Type v}

/-- `l` with position `i` replaced by the value of `x`, when `x` is `some`. -/
def set_opt (l : List α) (i : Nat) (x : Option α) : List α :=
  match l with
  | [] => l
  | hd :: tl => if i = 0 then Option.getD x hd :: tl else hd :: set_opt tl (i-1) x

@[simp]
theorem length_set_opt (l : List α) (i : Nat) (x : Option α):
  (l.set_opt i x).length = l.length := by
  induction l generalizing i with
  | nil => rfl
  | cons hd tl ih =>
    simp only [set_opt]
    split <;> simp [ih]

/-- The elements of `ls` at positions `start` to `end_ - 1`. -/
def slice (start end_ : Nat) (ls : List α) : List α :=
  (ls.drop start).take (end_ - start)

/-- `l` truncated or extended with copies of `x` to length `new_len`. -/
def resize (l : List α) (new_len : Nat) (x : α) : List α :=
  if new_len ≥ 0 then
    l.take new_len ++ replicate (new_len - l.length) x
  else []

@[simp, grind =]
theorem resize_length (l : List α) (new_len : Nat) (x : α) :
  (l.resize new_len x).length = new_len := by
  simp only [resize, Nat.zero_le, ↓reduceIte, length_append, length_take, length_replicate]
  omega

@[simp] theorem slice_zero_j (l : List α) (j : Nat) : l.slice 0 j = l.take j := by simp [slice]

theorem slice_length_le (i j : Nat) (ls : List α) : (ls.slice i j).length ≤ ls.length := by
  simp only [slice, length_take, length_drop]; omega

@[grind =]
theorem slice_length (i j : Nat) (ls : List α) :
    (ls.slice i j).length = min (ls.length - i) (j - i) := by
  simp only [slice, length_take, length_drop]; omega

@[simp, grind =]
theorem getElem?_slice (i j k : Nat) (ls : List α)
  (h : j ≤ ls.length ∧ i + k < j) :
  (ls.slice i j)[k]? = ls[i + k]? := by
  simp only [slice, getElem?_take, getElem?_drop]
  rw [if_pos (by omega)]

@[simp, grind =]
theorem getElem!_slice [Inhabited α] (i j k : Nat) (ls : List α)
  (h : j ≤ ls.length ∧ i + k < j) :
  (ls.slice i j)[k]! = ls[i + k]! := by
  simp only [getElem!_def, getElem?_slice i j k ls h]

@[simp]
theorem getElem_slice (i j k : Nat) (ls : List α)
  (h : j ≤ ls.length ∧ i + k < j) :
  (ls.slice i j)[k]'(by rw [slice_length]; omega) = ls[i + k]'(by omega) := by
  have hk : k < (ls.slice i j).length := by rw [slice_length]; omega
  have hik : i + k < ls.length := by omega
  have h1 := getElem?_slice i j k ls h
  rw [getElem?_eq_getElem hk, getElem?_eq_getElem hik] at h1
  exact Option.some.inj h1

theorem mapM_RustM_length {α : Type w} {β : Type u} {f : α → Std.RustM β} {l : List α}
  {l' : List β}
  (h : List.mapM f l = .ok l') :
  l'.length = l.length := by
  have hind (l : List α) (l' acc : List β) (h : List.mapM.loop f l acc = .ok l') :
      l'.length = l.length + acc.length := by
    induction l generalizing l' acc with
    | nil =>
      simp only [mapM.loop, pure] at h
      cases h; simp
    | cons hd tl ih =>
      simp only [mapM.loop, Bind.bind] at h
      cases hf : f hd with
      | ok v =>
        simp only [hf, Std.bind] at h
        have := ih _ _ h
        simp only [length_cons] at this ⊢
        omega
      | fail e => simp only [hf, Std.bind] at h; cases h
      | div => simp only [hf, Std.bind] at h; cases h
  have := hind l l' [] h
  simpa using this

theorem splitAt_length {α : Type u}  (n : Nat)  (l : List α) :
  (l.splitAt n).fst.length = min l.length n ∧ (l.splitAt n).snd.length = l.length - n := by
  simp [splitAt_eq]; omega

/-- `s` with the elements from position `i` onwards replaced by those of `s'`,
within the length of `s`. -/
def setSlice! {α} (s : List α) (i : Nat) (s' : List α) : List α :=
  let s0 := List.take i s
  let n := min s'.length (s.length - i)
  let s1 := List.take n s'
  let s2 := List.drop (i + n) s
  s0 ++ s1 ++ s2

@[simp, grind =]
theorem length_setSlice! {α} (s : List α) (i : Nat) (s' : List α) :
  (s.setSlice! i s').length = s.length := by
  simp only [setSlice!, append_assoc, length_append, length_take, length_drop]
  omega

theorem setSlice!_getElem?_prefix {α}
  (s : List α) (s' : List α) (i j : Nat) (h : j < i) :
  (s.setSlice! i s')[j]? = s[j]? := by
  simp only [setSlice!, append_assoc]
  by_cases hj : j < s.length
  · rw [getElem?_append_left (by simp only [length_take]; omega), getElem?_take]
    simp [h]
  · rw [getElem?_eq_none (by simp only [length_append, length_take, length_drop]; omega),
      getElem?_eq_none (by omega)]

theorem setSlice!_getElem?_middle {α}
  (s : List α) (s' : List α) (i j : Nat) (h : i ≤ j ∧ j - i < s'.length ∧ j < s.length) :
  (s.setSlice! i s')[j]? = s'[j - i]? := by
  simp only [setSlice!, append_assoc]
  rw [getElem?_append_right (by simp only [length_take]; omega),
    getElem?_append_left (by simp only [length_take]; omega), getElem?_take]
  simp only [length_take]
  rw [if_pos (by omega)]
  congr 1
  omega

theorem setSlice!_getElem?_suffix {α}
  (s : List α) (s' : List α) (i j : Nat) (h : i + s'.length ≤ j) :
  (s.setSlice! i s')[j]? = s[j]? := by
  simp only [setSlice!, append_assoc]
  by_cases hj : j < s.length
  · rw [getElem?_append_right (by simp only [length_take]; omega),
      getElem?_append_right (by simp only [length_take]; omega), getElem?_drop]
    simp only [length_take]
    congr 1
    omega
  · rw [getElem?_eq_none (by simp only [length_append, length_take, length_drop]; omega),
      getElem?_eq_none (by omega)]

theorem getElem_setSlice!_prefix {α}
  (s : List α) (s' : List α) (i j : Nat) (h : j < i ∧ j < s.length) :
  (s.setSlice! i s')[j]'(by simp only [length_setSlice!]; exact h.2) = s[j] := by
  have hj' : j < (s.setSlice! i s').length := by simp only [length_setSlice!]; exact h.2
  have h1 := setSlice!_getElem?_prefix s s' i j h.1
  rw [getElem?_eq_getElem hj', getElem?_eq_getElem h.2] at h1
  exact Option.some.inj h1

theorem getElem_setSlice!_middle {α}
  (s : List α) (s' : List α) (i j : Nat) (h : i ≤ j ∧ j - i < s'.length ∧ j < s.length) :
  (s.setSlice! i s')[j]'(by simp only [length_setSlice!]; exact h.2.2) = s'[j - i] := by
  have hj' : j < (s.setSlice! i s').length := by simp only [length_setSlice!]; exact h.2.2
  have h1 := setSlice!_getElem?_middle s s' i j h
  rw [getElem?_eq_getElem hj', getElem?_eq_getElem h.2.1] at h1
  exact Option.some.inj h1

theorem getElem_setSlice!_suffix {α}
  (s : List α) (s' : List α) (i j : Nat) (h : i + s'.length ≤ j ∧ j < s.length) :
  (s.setSlice! i s')[j]'(by simp only [length_setSlice!]; exact h.2) = s[j] := by
  have hj' : j < (s.setSlice! i s').length := by simp only [length_setSlice!]; exact h.2
  have h1 := setSlice!_getElem?_suffix s s' i j h.1
  rw [getElem?_eq_getElem hj', getElem?_eq_getElem h.2] at h1
  exact Option.some.inj h1

theorem Inhabited_getElem_eq_getElem! {α} [Inhabited α] (l : List α) (i : Nat)
    (hi : i < l.length) :
  l[i] = l[i]! := by
  simp only [getElem!_def, getElem?_eq_getElem hi]

end

end List

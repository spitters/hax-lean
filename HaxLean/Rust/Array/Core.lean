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
  backends/lean/Aeneas/Std/Array/Core.lean
-/

module

public import HaxLean.Rust.Scalar.Core
public import HaxLean.Rust.Data.List
public import HaxLean.Rust.WP

/-!
# List indexing by `Usize` and element-wise cloning
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Aeneas.Std

open RustM WP

instance {α : Type u} : GetElem (List α) Usize α (fun l i => i.val < l.length) where
  getElem l i h := getElem l i.val h

instance {α : Type u} : GetElem? (List α) Usize α (fun l i => i < l.length) where
  getElem? l i := getElem? l i.val

theorem List.mapM_clone_eq {T : Type u} {clone : T → RustM T} {l : List T}
  (h : ∀ x ∈ l, clone x = ok x) :
  List.mapM clone l = ok l := by
  have hind (l acc : List T) (h : ∀ x ∈ l, clone x = ok x) :
    List.mapM.loop clone l acc = ok (List.reverse acc ++ l) := by
    induction l generalizing acc with
    | nil => simp only [List.mapM.loop, pure, List.append_nil]
    | cons hd tl ih =>
      simp only [List.mapM.loop, Bind.bind]
      rw [h hd (by simp)]
      simp only [bind_ok]
      rw [ih _ (fun x hx => h x (by simp [hx]))]
      simp
  have := hind l [] h
  simp only [List.reverse_nil, List.nil_append] at this
  rw [← this]
  rfl

/-- Clones every element of `l`, propagating failure and divergence. -/
def List.clone {α : Type u} (clone : α → RustM α) (l : List α) :
    RustM ({ l' : List α // l'.length = l.length}) :=
  match h :List.mapM clone l with
  | ok v => ok ⟨ v, List.mapM_RustM_length h ⟩
  | fail e => fail e
  | div => div

theorem List.clone_spec {α : Type u} {clone : α → RustM α} {l : List α}
    (h : ∀ x ∈ l, clone x = ok x) :
  List.clone clone l ⦃ l' => l'.val = l ∧ l'.val.length = l.length ⦄ := by
  have := List.mapM_clone_eq h
  unfold List.clone
  split <;> simp_all

end Aeneas.Std

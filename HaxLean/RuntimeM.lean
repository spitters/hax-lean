/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import HaxLean.Runtime
public import HaxLean.Rust.Primitives
public import HaxLean.Rust.WP
public import Std.Tactic.BVDecide
public import Std.WP

/-!
# Guarded runtime operations in `RustM`

The operations of `HaxLean.Runtime` that panic in Rust (checked arithmetic, division and
remainder, shifts, indexing, slicing, `unwrap`, `assert`, `panic`) as computations in
`Aeneas.Std.RustM`. Each guarded operation `opM` is defined from the total operation `op` of
`Hax` as `if guard then pure (op args) else .fail .panic`, where `guard` is the condition
under which Rust does not panic. Every lemma about a total operation therefore applies to the
value of the guarded one.

The specifications are triples of the toolchain's `Std.WP` logic, the logic that `vcgen`
reads, with the guard as precondition (the form of Aeneas's `@[step]` specifications). The
module gives `RustM` its `Std.WP.WPMonad` interpretation: a value satisfies the normal
postcondition, a failure the exception postcondition, and divergence nothing (total
correctness).

## Main definitions

* `Aeneas.Std.RustM.instStdWPMonad`: `RustM` as a `Std.WP.WPMonad` over `Prop` with
  exception postcondition `Error → Prop`.
* `Hax.addM_w`, `Hax.subM_w`, `Hax.mulM_w`, `Hax.addM_iw`, `Hax.subM_iw`, `Hax.mulM_iw`:
  checked arithmetic at width `w`, unsigned and signed.
* `Hax.divM_w`, `Hax.remM_w`, `Hax.divM_iw`, `Hax.remM_iw`: division and remainder, failing
  on a zero divisor and, signed, on `MIN / -1`.
* `Hax.shlM_w`, `Hax.shrM_w`, `Hax.shlM_iw`, `Hax.shrM_iw`: shifts, failing when the
  amount is negative or at least the width.
* `Hax.indexM`, `Hax.array_updateM`, `Hax.vec_removeM`: element access within bounds.
* `Hax.slice_toM`, `Hax.slice_fromM`, `Hax.slice_rangeM`, `Hax.slice_updateM`,
  `Hax.copy_from_sliceM`: slicing within bounds and copying between slices of equal length.
* `Hax.unwrapM`, `Hax.expectM`, `Hax.assertM`, `Hax.assert_failedM`, `Hax.panicM`.
* `Hax.foldRangeM`, `Hax.forFoldM`: the counted loops of `Hax.foldRange` and `Hax.forFold`
  with a monadic body.
* `rust_vc`: `vcgen … with finish`, falling back to `vcgen` followed by `grind`, `omega` or
  `bv_decide` on each verification condition.

## Main results

* `Hax.opM_of_guard` for each operation: under the guard, `opM args = pure (op args)`.
* `Hax.opM_spec` for each operation: the `@[spec]` triple
  `Triple (opM args) guard (fun r => r = op args) epost`.
* `Hax.foldRangeM_spec`, `Hax.forFoldM_spec`: loop rules from an invariant indexed by the
  counter.
* `Hax.foldRangeM_id`: at `Id` with a pure body, `foldRangeM` is `Hax.foldRange`.

The examples at the end of the module are proved by `rust_vc`; a loop takes its invariant as
an argument of the loop rule, `rust_vc [foldRangeM_spec lo hi init f inv]`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Aeneas.Std

open _root_.Std.WP Lean.Order

/-- The `Std.WP` interpretation of `RustM α`: a value satisfies `post`, a failure `epost`,
and divergence no postcondition. -/
instance RustM.instStdWP {α : Type u} : _root_.Std.WP.WP (RustM α) α Prop (Error → Prop) where
  wpTrans x := ⟨fun post epost => match x with
    | .ok a => post a
    | .fail e => epost e
    | .div => False⟩
  wp_trans_monotone x := fun _ _ _ _ hepost hpost => by
    cases x with
    | ok a => exact hpost a
    | fail e => exact hepost e
    | div => exact id

/-- `RustM` as a `Std.WP.WPMonad` over `Prop` with exception postcondition `Error → Prop`. -/
instance RustM.instStdWPMonad : _root_.Std.WP.WPMonad RustM.{u} Prop (Error → Prop) where
  toWP _ := inferInstance
  pure_le_wp_pure _ _ _ := PartialOrder.rel_refl
  bind_le_wp_bind x _ := fun _ _ => by cases x <;> exact id

end Aeneas.Std

namespace Hax

open Aeneas.Std (RustM Error massert massert_ok)
open _root_.Std.WP Lean.Order

/-- A computation equal to `pure v` whenever `g` holds meets the guard triple: precondition
`g`, postcondition `r = v`. -/
theorem triple_of_guard {α : Type} {g : Prop} {x : RustM α} {v : α} {epost : Error → Prop}
    (h : g → x = pure v) : Triple x g (fun r => r = v) epost :=
  ⟨fun hg => by rw [h hg]; rfl⟩

/-! ### Checked arithmetic -/

/-- Unfolding lemma of `Hax.add` for `grind`. -/
@[grind =] theorem add_def (a b : Int) : add a b = a + b := rfl

/-- Unfolding lemma of `Hax.sub` for `grind`. -/
@[grind =] theorem sub_def (a b : Int) : sub a b = a - b := rfl

/-- Unfolding lemma of `Hax.mul` for `grind`. -/
@[grind =] theorem mul_def (a b : Int) : mul a b = a * b := rfl

/-- Checked unsigned addition at width `w`. -/
def addM_w (w : Nat) (a b : Int) : RustM Int :=
  if 0 ≤ a + b ∧ a + b < 2 ^ w then pure (add a b) else .fail .panic

/-- Without overflow, `addM_w` is `add`. -/
theorem addM_w_of_guard (w : Nat) (a b : Int) (h : 0 ≤ a + b ∧ a + b < 2 ^ w) :
    addM_w w a b = pure (add a b) := by
  simp [addM_w, h]

/-- Triple of `addM_w`: precondition no overflow. -/
@[spec]
theorem addM_w_spec (w : Nat) (a b : Int) {epost : Error → Prop} :
    Triple (addM_w w a b) (0 ≤ a + b ∧ a + b < 2 ^ w) (fun r => r = add a b) epost :=
  triple_of_guard (addM_w_of_guard w a b)

/-- Checked unsigned subtraction at width `w`. -/
def subM_w (w : Nat) (a b : Int) : RustM Int :=
  if 0 ≤ a - b ∧ a - b < 2 ^ w then pure (sub a b) else .fail .panic

/-- Without underflow, `subM_w` is `sub`. -/
theorem subM_w_of_guard (w : Nat) (a b : Int) (h : 0 ≤ a - b ∧ a - b < 2 ^ w) :
    subM_w w a b = pure (sub a b) := by
  rw [subM_w, ite_eq_left h]

/-- Triple of `subM_w`: precondition no underflow. -/
@[spec]
theorem subM_w_spec (w : Nat) (a b : Int) {epost : Error → Prop} :
    Triple (subM_w w a b) (0 ≤ a - b ∧ a - b < 2 ^ w) (fun r => r = sub a b) epost :=
  triple_of_guard (subM_w_of_guard w a b)

/-- Checked unsigned multiplication at width `w`. -/
def mulM_w (w : Nat) (a b : Int) : RustM Int :=
  if 0 ≤ a * b ∧ a * b < 2 ^ w then pure (mul a b) else .fail .panic

/-- Without overflow, `mulM_w` is `mul`. -/
theorem mulM_w_of_guard (w : Nat) (a b : Int) (h : 0 ≤ a * b ∧ a * b < 2 ^ w) :
    mulM_w w a b = pure (mul a b) := by
  simp [mulM_w, h]

/-- Triple of `mulM_w`: precondition no overflow. -/
@[spec]
theorem mulM_w_spec (w : Nat) (a b : Int) {epost : Error → Prop} :
    Triple (mulM_w w a b) (0 ≤ a * b ∧ a * b < 2 ^ w) (fun r => r = mul a b) epost :=
  triple_of_guard (mulM_w_of_guard w a b)

/-- Checked signed addition at width `w`. -/
def addM_iw (w : Nat) (a b : Int) : RustM Int :=
  if -2 ^ (w - 1) ≤ a + b ∧ a + b < 2 ^ (w - 1) then pure (add a b) else .fail .panic

/-- Without overflow, `addM_iw` is `add`. -/
theorem addM_iw_of_guard (w : Nat) (a b : Int)
    (h : -2 ^ (w - 1) ≤ a + b ∧ a + b < 2 ^ (w - 1)) : addM_iw w a b = pure (add a b) := by
  simp [addM_iw, h]

/-- Triple of `addM_iw`: precondition no overflow. -/
@[spec]
theorem addM_iw_spec (w : Nat) (a b : Int) {epost : Error → Prop} :
    Triple (addM_iw w a b) (-2 ^ (w - 1) ≤ a + b ∧ a + b < 2 ^ (w - 1))
      (fun r => r = add a b) epost :=
  triple_of_guard (addM_iw_of_guard w a b)

/-- Checked signed subtraction at width `w`. -/
def subM_iw (w : Nat) (a b : Int) : RustM Int :=
  if -2 ^ (w - 1) ≤ a - b ∧ a - b < 2 ^ (w - 1) then pure (sub a b) else .fail .panic

/-- Without overflow, `subM_iw` is `sub`. -/
theorem subM_iw_of_guard (w : Nat) (a b : Int)
    (h : -2 ^ (w - 1) ≤ a - b ∧ a - b < 2 ^ (w - 1)) : subM_iw w a b = pure (sub a b) := by
  simp [subM_iw, h]

/-- Triple of `subM_iw`: precondition no overflow. -/
@[spec]
theorem subM_iw_spec (w : Nat) (a b : Int) {epost : Error → Prop} :
    Triple (subM_iw w a b) (-2 ^ (w - 1) ≤ a - b ∧ a - b < 2 ^ (w - 1))
      (fun r => r = sub a b) epost :=
  triple_of_guard (subM_iw_of_guard w a b)

/-- Checked signed multiplication at width `w`. -/
def mulM_iw (w : Nat) (a b : Int) : RustM Int :=
  if -2 ^ (w - 1) ≤ a * b ∧ a * b < 2 ^ (w - 1) then pure (mul a b) else .fail .panic

/-- Without overflow, `mulM_iw` is `mul`. -/
theorem mulM_iw_of_guard (w : Nat) (a b : Int)
    (h : -2 ^ (w - 1) ≤ a * b ∧ a * b < 2 ^ (w - 1)) : mulM_iw w a b = pure (mul a b) := by
  simp [mulM_iw, h]

/-- Triple of `mulM_iw`: precondition no overflow. -/
@[spec]
theorem mulM_iw_spec (w : Nat) (a b : Int) {epost : Error → Prop} :
    Triple (mulM_iw w a b) (-2 ^ (w - 1) ≤ a * b ∧ a * b < 2 ^ (w - 1))
      (fun r => r = mul a b) epost :=
  triple_of_guard (mulM_iw_of_guard w a b)

/-! ### Division and remainder -/

/-- Unsigned division, failing on a zero divisor. -/
def divM_w (_w : Nat) (a b : Int) : RustM Int :=
  if b ≠ 0 then pure (div a b) else .fail .panic

/-- With a nonzero divisor, `divM_w` is `div`. -/
theorem divM_w_of_guard (w : Nat) (a b : Int) (h : b ≠ 0) : divM_w w a b = pure (div a b) := by
  simp [divM_w, h]

/-- Triple of `divM_w`: precondition a nonzero divisor. -/
@[spec]
theorem divM_w_spec (w : Nat) (a b : Int) {epost : Error → Prop} :
    Triple (divM_w w a b) (b ≠ 0) (fun r => r = div a b) epost :=
  triple_of_guard (divM_w_of_guard w a b)

/-- Unsigned remainder, failing on a zero divisor. -/
def remM_w (_w : Nat) (a b : Int) : RustM Int :=
  if b ≠ 0 then pure (rem a b) else .fail .panic

/-- With a nonzero divisor, `remM_w` is `rem`. -/
theorem remM_w_of_guard (w : Nat) (a b : Int) (h : b ≠ 0) : remM_w w a b = pure (rem a b) := by
  simp [remM_w, h]

/-- Triple of `remM_w`: precondition a nonzero divisor. -/
@[spec]
theorem remM_w_spec (w : Nat) (a b : Int) {epost : Error → Prop} :
    Triple (remM_w w a b) (b ≠ 0) (fun r => r = rem a b) epost :=
  triple_of_guard (remM_w_of_guard w a b)

/-- Signed truncating division at width `w`, failing on a zero divisor and on `MIN / -1`. -/
def divM_iw (w : Nat) (a b : Int) : RustM Int :=
  if b ≠ 0 ∧ ¬(a = -2 ^ (w - 1) ∧ b = -1) then pure (div_iw w a b) else .fail .panic

/-- With a nonzero divisor and no overflow, `divM_iw` is `div_iw`. -/
theorem divM_iw_of_guard (w : Nat) (a b : Int) (h : b ≠ 0 ∧ ¬(a = -2 ^ (w - 1) ∧ b = -1)) :
    divM_iw w a b = pure (div_iw w a b) := by
  rw [divM_iw, ite_eq_left h]

/-- Triple of `divM_iw`: precondition a nonzero divisor and not `MIN / -1`. -/
@[spec]
theorem divM_iw_spec (w : Nat) (a b : Int) {epost : Error → Prop} :
    Triple (divM_iw w a b) (b ≠ 0 ∧ ¬(a = -2 ^ (w - 1) ∧ b = -1))
      (fun r => r = div_iw w a b) epost :=
  triple_of_guard (divM_iw_of_guard w a b)

/-- Signed truncating remainder at width `w`, failing on a zero divisor and on `MIN % -1`. -/
def remM_iw (w : Nat) (a b : Int) : RustM Int :=
  if b ≠ 0 ∧ ¬(a = -2 ^ (w - 1) ∧ b = -1) then pure (rem_iw w a b) else .fail .panic

/-- With a nonzero divisor and no overflow, `remM_iw` is `rem_iw`. -/
theorem remM_iw_of_guard (w : Nat) (a b : Int) (h : b ≠ 0 ∧ ¬(a = -2 ^ (w - 1) ∧ b = -1)) :
    remM_iw w a b = pure (rem_iw w a b) := by
  rw [remM_iw, ite_eq_left h]

/-- Triple of `remM_iw`: precondition a nonzero divisor and not `MIN % -1`. -/
@[spec]
theorem remM_iw_spec (w : Nat) (a b : Int) {epost : Error → Prop} :
    Triple (remM_iw w a b) (b ≠ 0 ∧ ¬(a = -2 ^ (w - 1) ∧ b = -1))
      (fun r => r = rem_iw w a b) epost :=
  triple_of_guard (remM_iw_of_guard w a b)

/-! ### Shifts -/

/-- Unsigned left shift at width `w`, failing when the amount is not below `w`. -/
def shlM_w (w : Nat) (a b : Int) : RustM Int :=
  if 0 ≤ b ∧ b < w then pure (shl_w w a b) else .fail .panic

/-- With the amount below the width, `shlM_w` is `shl_w`. -/
theorem shlM_w_of_guard (w : Nat) (a b : Int) (h : 0 ≤ b ∧ b < w) :
    shlM_w w a b = pure (shl_w w a b) := by
  rw [shlM_w, ite_eq_left h]

/-- Triple of `shlM_w`: precondition the amount below the width. -/
@[spec]
theorem shlM_w_spec (w : Nat) (a b : Int) {epost : Error → Prop} :
    Triple (shlM_w w a b) (0 ≤ b ∧ b < w) (fun r => r = shl_w w a b) epost :=
  triple_of_guard (shlM_w_of_guard w a b)

/-- Unsigned right shift at width `w`, failing when the amount is not below `w`. -/
def shrM_w (w : Nat) (a b : Int) : RustM Int :=
  if 0 ≤ b ∧ b < w then pure (shr_w w a b) else .fail .panic

/-- With the amount below the width, `shrM_w` is `shr_w`. -/
theorem shrM_w_of_guard (w : Nat) (a b : Int) (h : 0 ≤ b ∧ b < w) :
    shrM_w w a b = pure (shr_w w a b) := by
  rw [shrM_w, ite_eq_left h]

/-- Triple of `shrM_w`: precondition the amount below the width. -/
@[spec]
theorem shrM_w_spec (w : Nat) (a b : Int) {epost : Error → Prop} :
    Triple (shrM_w w a b) (0 ≤ b ∧ b < w) (fun r => r = shr_w w a b) epost :=
  triple_of_guard (shrM_w_of_guard w a b)

/-- Signed left shift at width `w`, failing when the amount is not below `w`. -/
def shlM_iw (w : Nat) (a b : Int) : RustM Int :=
  if 0 ≤ b ∧ b < w then pure (shl_iw w a b) else .fail .panic

/-- With the amount below the width, `shlM_iw` is `shl_iw`. -/
theorem shlM_iw_of_guard (w : Nat) (a b : Int) (h : 0 ≤ b ∧ b < w) :
    shlM_iw w a b = pure (shl_iw w a b) := by
  rw [shlM_iw, ite_eq_left h]

/-- Triple of `shlM_iw`: precondition the amount below the width. -/
@[spec]
theorem shlM_iw_spec (w : Nat) (a b : Int) {epost : Error → Prop} :
    Triple (shlM_iw w a b) (0 ≤ b ∧ b < w) (fun r => r = shl_iw w a b) epost :=
  triple_of_guard (shlM_iw_of_guard w a b)

/-- Signed (arithmetic) right shift at width `w`, failing when the amount is not below `w`. -/
def shrM_iw (w : Nat) (a b : Int) : RustM Int :=
  if 0 ≤ b ∧ b < w then pure (shr_iw w a b) else .fail .panic

/-- With the amount below the width, `shrM_iw` is `shr_iw`. -/
theorem shrM_iw_of_guard (w : Nat) (a b : Int) (h : 0 ≤ b ∧ b < w) :
    shrM_iw w a b = pure (shr_iw w a b) := by
  rw [shrM_iw, ite_eq_left h]

/-- Triple of `shrM_iw`: precondition the amount below the width. -/
@[spec]
theorem shrM_iw_spec (w : Nat) (a b : Int) {epost : Error → Prop} :
    Triple (shrM_iw w a b) (0 ≤ b ∧ b < w) (fun r => r = shr_iw w a b) epost :=
  triple_of_guard (shrM_iw_of_guard w a b)

/-! ### Indexing -/

/-- `a[i]`, failing when `i` is out of bounds. -/
def indexM {α : Type} [Inhabited α] (a : Array α) (i : Int) : RustM α :=
  if 0 ≤ i ∧ i < a.size then pure (index a i) else .fail .panic

/-- Within bounds, `indexM` is `index`. -/
theorem indexM_of_guard {α : Type} [Inhabited α] (a : Array α) (i : Int)
    (h : 0 ≤ i ∧ i < a.size) : indexM a i = pure (index a i) := by
  rw [indexM, ite_eq_left h]

/-- Triple of `indexM`: precondition the index within bounds. -/
@[spec]
theorem indexM_spec {α : Type} [Inhabited α] (a : Array α) (i : Int) {epost : Error → Prop} :
    Triple (indexM a i) (0 ≤ i ∧ i < a.size) (fun r => r = index a i) epost :=
  triple_of_guard (indexM_of_guard a i)

/-- `a[i] = v`, failing when `i` is out of bounds. -/
def array_updateM {α : Type} (a : Array α) (i : Int) (v : α) : RustM (Array α) :=
  if 0 ≤ i ∧ i < a.size then pure (array_update a i v) else .fail .panic

/-- Within bounds, `array_updateM` is `array_update`. -/
theorem array_updateM_of_guard {α : Type} (a : Array α) (i : Int) (v : α)
    (h : 0 ≤ i ∧ i < a.size) : array_updateM a i v = pure (array_update a i v) := by
  rw [array_updateM, ite_eq_left h]

/-- Triple of `array_updateM`: precondition the index within bounds. -/
@[spec]
theorem array_updateM_spec {α : Type} (a : Array α) (i : Int) (v : α)
    {epost : Error → Prop} :
    Triple (array_updateM a i v) (0 ≤ i ∧ i < a.size) (fun r => r = array_update a i v)
      epost :=
  triple_of_guard (array_updateM_of_guard a i v)

/-- `Vec::remove`, failing when `i` is out of bounds. -/
def vec_removeM {α : Type} [Inhabited α] (a : Array α) (i : Int) : RustM (α × Array α) :=
  if 0 ≤ i ∧ i < a.size then pure (vec_remove a i) else .fail .panic

/-- Within bounds, `vec_removeM` is `vec_remove`. -/
theorem vec_removeM_of_guard {α : Type} [Inhabited α] (a : Array α) (i : Int)
    (h : 0 ≤ i ∧ i < a.size) : vec_removeM a i = pure (vec_remove a i) := by
  rw [vec_removeM, ite_eq_left h]

/-- Triple of `vec_removeM`: precondition the index within bounds. -/
@[spec]
theorem vec_removeM_spec {α : Type} [Inhabited α] (a : Array α) (i : Int)
    {epost : Error → Prop} :
    Triple (vec_removeM a i) (0 ≤ i ∧ i < a.size) (fun r => r = vec_remove a i) epost :=
  triple_of_guard (vec_removeM_of_guard a i)

/-! ### Slicing -/

/-- `a[..n]`, failing unless `0 ≤ n ≤ a.len()`. -/
def slice_toM {α : Type} (a : Array α) (n : Int) : RustM (Array α) :=
  if 0 ≤ n ∧ n ≤ a.size then pure (slice_to a n) else .fail .panic

/-- Within bounds, `slice_toM` is `slice_to`. -/
theorem slice_toM_of_guard {α : Type} (a : Array α) (n : Int) (h : 0 ≤ n ∧ n ≤ a.size) :
    slice_toM a n = pure (slice_to a n) := by
  rw [slice_toM, ite_eq_left h]

/-- Triple of `slice_toM`: precondition the end within bounds. -/
@[spec]
theorem slice_toM_spec {α : Type} (a : Array α) (n : Int) {epost : Error → Prop} :
    Triple (slice_toM a n) (0 ≤ n ∧ n ≤ a.size) (fun r => r = slice_to a n) epost :=
  triple_of_guard (slice_toM_of_guard a n)

/-- `a[n..]`, failing unless `0 ≤ n ≤ a.len()`. -/
def slice_fromM {α : Type} (a : Array α) (n : Int) : RustM (Array α) :=
  if 0 ≤ n ∧ n ≤ a.size then pure (slice_from a n) else .fail .panic

/-- Within bounds, `slice_fromM` is `slice_from`. -/
theorem slice_fromM_of_guard {α : Type} (a : Array α) (n : Int) (h : 0 ≤ n ∧ n ≤ a.size) :
    slice_fromM a n = pure (slice_from a n) := by
  rw [slice_fromM, ite_eq_left h]

/-- Triple of `slice_fromM`: precondition the start within bounds. -/
@[spec]
theorem slice_fromM_spec {α : Type} (a : Array α) (n : Int) {epost : Error → Prop} :
    Triple (slice_fromM a n) (0 ≤ n ∧ n ≤ a.size) (fun r => r = slice_from a n) epost :=
  triple_of_guard (slice_fromM_of_guard a n)

/-- `a[lo..hi]`, failing unless `0 ≤ lo ≤ hi ≤ a.len()`. -/
def slice_rangeM {α : Type} (a : Array α) (lo hi : Int) : RustM (Array α) :=
  if 0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ a.size then pure (slice_range a lo hi) else .fail .panic

/-- Within bounds, `slice_rangeM` is `slice_range`. -/
theorem slice_rangeM_of_guard {α : Type} (a : Array α) (lo hi : Int)
    (h : 0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ a.size) :
    slice_rangeM a lo hi = pure (slice_range a lo hi) := by
  rw [slice_rangeM, ite_eq_left h]

/-- Triple of `slice_rangeM`: precondition `0 ≤ lo ≤ hi ≤ a.len()`. -/
@[spec]
theorem slice_rangeM_spec {α : Type} (a : Array α) (lo hi : Int) {epost : Error → Prop} :
    Triple (slice_rangeM a lo hi) (0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ a.size)
      (fun r => r = slice_range a lo hi) epost :=
  triple_of_guard (slice_rangeM_of_guard a lo hi)

/-- `a[lo..hi].copy_from_slice(src)`, failing unless `0 ≤ lo ≤ hi ≤ a.len()` and
`hi - lo = src.len()`. -/
def slice_updateM {α : Type} (a : Array α) (lo hi : Int) (src : Array α) : RustM (Array α) :=
  if 0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ a.size ∧ hi - lo = src.size then
    pure (slice_update a lo hi src)
  else .fail .panic

/-- Within bounds and at equal lengths, `slice_updateM` is `slice_update`. -/
theorem slice_updateM_of_guard {α : Type} (a : Array α) (lo hi : Int) (src : Array α)
    (h : 0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ a.size ∧ hi - lo = src.size) :
    slice_updateM a lo hi src = pure (slice_update a lo hi src) := by
  rw [slice_updateM, ite_eq_left h]

/-- Triple of `slice_updateM`: precondition the range within bounds and of the length of
`src`. -/
@[spec]
theorem slice_updateM_spec {α : Type} (a : Array α) (lo hi : Int) (src : Array α)
    {epost : Error → Prop} :
    Triple (slice_updateM a lo hi src)
      (0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ a.size ∧ hi - lo = src.size)
      (fun r => r = slice_update a lo hi src) epost :=
  triple_of_guard (slice_updateM_of_guard a lo hi src)

/-- `dst.copy_from_slice(src)`, failing unless the lengths are equal. -/
def copy_from_sliceM {α : Type} (dst src : Array α) : RustM (Array α) :=
  if dst.size = src.size then pure (copy_from_slice dst src) else .fail .panic

/-- At equal lengths, `copy_from_sliceM` is `copy_from_slice`. -/
theorem copy_from_sliceM_of_guard {α : Type} (dst src : Array α) (h : dst.size = src.size) :
    copy_from_sliceM dst src = pure (copy_from_slice dst src) := by
  rw [copy_from_sliceM, ite_eq_left h]

/-- Triple of `copy_from_sliceM`: precondition equal lengths. -/
@[spec]
theorem copy_from_sliceM_spec {α : Type} (dst src : Array α) {epost : Error → Prop} :
    Triple (copy_from_sliceM dst src) (dst.size = src.size)
      (fun r => r = copy_from_slice dst src) epost :=
  triple_of_guard (copy_from_sliceM_of_guard dst src)

/-! ### `unwrap`, `expect`, `assert`, `panic` -/

/-- `Option::unwrap`, failing on `none`. -/
def unwrapM {α : Type} (o : Option α) : RustM α :=
  if h : o.isSome then pure (o.get h) else .fail .panic

/-- On `some`, `unwrapM` is `Option.get`. -/
theorem unwrapM_of_guard {α : Type} (o : Option α) (h : o.isSome) :
    unwrapM o = pure (o.get h) := by
  rw [unwrapM, dite_eq_left h]

/-- Triple of `unwrapM`: precondition `o.isSome`; the result is the content of `o`. -/
@[spec]
theorem unwrapM_spec {α : Type} (o : Option α) {epost : Error → Prop} :
    Triple (unwrapM o) (o.isSome = true) (fun r => o = some r) epost :=
  ⟨fun h => by rw [unwrapM_of_guard o h]; exact (Option.some_get h).symm⟩

/-- `Option::expect`, failing on `none`; the message is not modelled. -/
def expectM {α β : Type} (o : Option α) (_msg : β) : RustM α :=
  if h : o.isSome then pure (o.get h) else .fail .panic

/-- On `some`, `expectM` is `Option.get`. -/
theorem expectM_of_guard {α β : Type} (o : Option α) (msg : β) (h : o.isSome) :
    expectM o msg = pure (o.get h) := by
  rw [expectM, dite_eq_left h]

/-- Triple of `expectM`: precondition `o.isSome`; the result is the content of `o`. -/
@[spec]
theorem expectM_spec {α β : Type} (o : Option α) (msg : β) {epost : Error → Prop} :
    Triple (expectM o msg) (o.isSome = true) (fun r => o = some r) epost :=
  ⟨fun h => by rw [expectM_of_guard o msg h]; exact (Option.some_get h).symm⟩

/-- `assert!(b)`: `massert`, failing when `b` is false. -/
def assertM (b : Bool) : RustM Unit :=
  massert (b = true)

/-- When `b` holds, `assertM b` is `pure ()`. -/
theorem assertM_of_guard (b : Bool) (h : b = true) : assertM b = pure () :=
  (massert_ok _).2 h

/-- Triple of `assertM`: precondition `b`. -/
@[spec]
theorem assertM_spec (b : Bool) {epost : Error → Prop} :
    Triple (assertM b) (b = true) (fun r => r = ()) epost :=
  triple_of_guard (assertM_of_guard b)

/-- A failed assertion (`Hax.assert_failed`): a panic. -/
def assert_failedM {α β γ δ : Type} (_kind : α) (_left : β) (_right : γ) (_msg : δ) :
    RustM Unit :=
  .fail .panic

/-- Triple of `assert_failedM`: it establishes the exception postcondition at `panic`. -/
@[spec]
theorem assert_failedM_spec {α β γ δ : Type} (kind : α) (left : β) (right : γ) (msg : δ)
    {post : Unit → Prop} {epost : Error → Prop} :
    Triple (assert_failedM kind left right msg) (epost .panic) post epost :=
  ⟨fun h => h⟩

/-- `panic!()`: a panic at any result type. -/
def panicM {α : Type} : RustM α :=
  .fail .panic

/-- Triple of `panicM`: it establishes the exception postcondition at `panic`. -/
@[spec]
theorem panicM_spec {α : Type} {post : α → Prop} {epost : Error → Prop} :
    Triple (panicM (α := α)) (epost .panic) post epost :=
  ⟨fun h => h⟩

/-! ### Counted loops with a monadic body -/

/-- Monadic fold over `[lo, hi)`, structurally recursive on the trip count `(hi - lo).toNat`;
the monadic form of `Hax.foldRange`. -/
def foldRangeM {m : Type → Type} [Monad m] {α : Type} (lo hi : Int) (init : α)
    (f : Int → α → m α) : m α :=
  go (hi - lo).toNat lo init
where
  /-- `n` trips of the fold from the counter value `i`. -/
  go : Nat → Int → α → m α
    | 0, _, acc => pure acc
    | n + 1, i, acc => f i acc >>= fun acc' => go n (i + 1) acc'

/-- Loop rule of `foldRangeM`: an invariant `inv i acc` indexed by the counter, preserved by
each trip `i ∈ [lo, hi)`, holds at the exit value `max lo hi` of the counter. -/
@[spec]
theorem foldRangeM_spec {m : Type → Type} [Monad m] {Pred EPred : Type} [Assertion Pred]
    [Assertion EPred] [WPMonad m Pred EPred] {α : Type} (lo hi : Int) (init : α)
    (f : Int → α → m α) {epost : EPred} (inv : Int → α → Pred)
    (step : ∀ i acc, lo ≤ i → i < hi →
      Triple (f i acc) (inv i acc) (fun acc' => inv (i + 1) acc') epost) :
    Triple (foldRangeM lo hi init f) (inv lo init) (fun r => inv (max lo hi) r) epost := by
  have key : ∀ (n : Nat) i acc, lo ≤ i → i + n = max lo hi →
      Triple (foldRangeM.go f n i acc) (inv i acc) (fun r => inv (max lo hi) r) epost := by
    intro n
    induction n with
    | zero =>
      intro i acc _ heq
      have hi' : i = max lo hi := by omega
      subst hi'
      exact Triple.pure acc PartialOrder.rel_refl
    | succ n ih =>
      intro i acc hlo heq
      exact Triple.bind _ _ (fun acc' => inv (i + 1) acc') (step i acc hlo (by omega))
        (fun acc' => ih (i + 1) acc' (by omega) (by omega))
  exact key (hi - lo).toNat lo init (Int.le_refl lo) (by omega)

/-- At `Id` with a pure body, `foldRangeM` is `Hax.foldRange`. -/
theorem foldRangeM_id {α : Type} (lo hi : Int) (init : α) (f : Int → α → α) :
    Id.run (foldRangeM (m := Id) lo hi init (fun i a => pure (f i a))) =
      foldRange lo hi init f := by
  have key : ∀ n i acc, Id.run (foldRangeM.go (m := Id) (fun i a => pure (f i a)) n i acc) =
      foldRange.go f n i acc := by
    intro n
    induction n with
    | zero => intro i acc; rfl
    | succ n ih => intro i acc; exact ih (i + 1) (f i acc)
  rw [foldRangeM, foldRange]
  exact key (hi - lo).toNat lo init

/-- Monadic fold over `[lo, hi)` whose body may break out of the loop with
`ControlFlow.Break`; the monadic form of `Hax.forFold`. -/
def forFoldM {m : Type → Type} [Monad m] {α β : Type} (lo hi : Int) (init : α)
    (f : Int → α → m (ControlFlow β α)) : m (ControlFlow β α) :=
  go (hi - lo).toNat lo init
where
  /-- `n` trips of the loop from the counter value `i`. -/
  go : Nat → Int → α → m (ControlFlow β α)
    | 0, _, acc => pure (.Continue acc)
    | n + 1, i, acc => f i acc >>= fun r => match r with
      | .Break v => pure (.Break v)
      | .Continue acc' => go n (i + 1) acc'

/-- Loop rule of `forFoldM`: an invariant `inv i acc` indexed by the counter, preserved by each
trip that continues; a trip that breaks establishes `brk`. -/
@[spec]
theorem forFoldM_spec {m : Type → Type} [Monad m] {Pred EPred : Type} [Assertion Pred]
    [Assertion EPred] [WPMonad m Pred EPred] {α β : Type} (lo hi : Int) (init : α)
    (f : Int → α → m (ControlFlow β α)) {epost : EPred} (inv : Int → α → Pred)
    (brk : β → Pred)
    (step : ∀ i acc, lo ≤ i → i < hi →
      Triple (f i acc) (inv i acc)
        (fun r => match r with
          | .Break v => brk v
          | .Continue acc' => inv (i + 1) acc') epost) :
    Triple (forFoldM lo hi init f) (inv lo init)
      (fun r => match r with
        | .Break v => brk v
        | .Continue acc => inv (max lo hi) acc) epost := by
  have key : ∀ (n : Nat) i acc, lo ≤ i → i + n = max lo hi →
      Triple (forFoldM.go f n i acc) (inv i acc)
        (fun r => match r with
          | .Break v => brk v
          | .Continue acc => inv (max lo hi) acc) epost := by
    intro n
    induction n with
    | zero =>
      intro i acc _ heq
      have hi' : i = max lo hi := by omega
      subst hi'
      exact Triple.pure (ControlFlow.Continue acc) PartialOrder.rel_refl
    | succ n ih =>
      intro i acc hlo heq
      refine Triple.bind _ _ _ (step i acc hlo (by omega)) (fun r => ?_)
      cases r with
      | Break v => exact Triple.pure (ControlFlow.Break v) PartialOrder.rel_refl
      | Continue acc' => exact ih (i + 1) acc' (by omega) (by omega)
  exact key (hi - lo).toNat lo init (Int.le_refl lo) (by omega)

end Hax

/-! ### The `rust_vc` tactic -/

/-- `rust_vc` proves a `Std.WP` triple about a `RustM` program: `vcgen` with the `@[spec]`
triples of the guarded operations, discharging the verification conditions by `finish`; if
that fails, `vcgen` followed by `grind`, `omega` or `bv_decide` on each condition.
`rust_vc [l₁, …]` passes the lemmas `lᵢ` to `vcgen`. -/
syntax (name := rustVc) "rust_vc"
  (" [" withoutPosition((Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|>
    Lean.Parser.Tactic.simpLemma),*,?) "]")? : tactic

macro_rules
  | `(tactic| rust_vc) => `(tactic|
      set_option experimental.vcgen true in
      first
        | vcgen with finish
        | (vcgen <;> first | grind | omega | bv_decide))
  | `(tactic| rust_vc [$ts,*]) => `(tactic|
      set_option experimental.vcgen true in
      first
        | vcgen [$ts,*] with finish
        | (vcgen [$ts,*] <;> first | grind | omega | bv_decide))

namespace Hax.RuntimeMExamples

open Aeneas.Std (RustM Error)
open _root_.Std.WP Lean.Order

/-- A checked increment followed by an index read: no panic when the incremented index is in
bounds. -/
example (a : Array Int) (x : Int) :
    ⦃a.size = 4 ∧ 0 ≤ x ∧ x < 3⦄
      (do let j ← addM_w 64 x 1; indexM a j)
    ⦃fun r => r = index a (x + 1)⦄ := by
  rust_vc

/-- Division and remainder by a nonzero divisor. -/
example (a b : Int) :
    ⦃b ≠ 0⦄
      (do let q ← divM_w 64 a b; let r ← remM_w 64 a b; pure (q, r))
    ⦃fun p => p = (div a b, rem a b)⦄ := by
  rust_vc

/-- A checked shift by an amount below the width, then an assertion on the amount. -/
example (a s : Int) :
    ⦃0 ≤ s ∧ s < 32⦄
      (do let r ← shlM_w 32 a s; assertM (decide (s < 32)); pure r)
    ⦃fun r => r = shl_w 32 a s⦄ := by
  rust_vc

/-- A counted loop reading `a[i]` for `i ∈ [0, n)` does not panic when `n ≤ a.len()`; the
loop rule is given its invariant as an argument. -/
example (a : Array Int) (n : Int) (hn : n ≤ a.size) :
    ⦃True⦄
      foldRangeM 0 n (0 : Int) (fun i acc => do let x ← indexM a i; pure (acc + x))
    ⦃fun _ => True⦄ := by
  rust_vc [foldRangeM_spec 0 n (0 : Int) _ (fun _ _ => True)]

/-- A loop that sums `n` bounded elements with checked additions: the invariant bounds the
accumulator by `255 * i`. -/
example (a : Array Int) (n : Int) (hn : n ≤ a.size) (hn' : n ≤ 1000)
    (ha : ∀ i, 0 ≤ i → i < a.size → 0 ≤ index a i ∧ index a i < 256) :
    ⦃True⦄
      foldRangeM 0 n (0 : Int) (fun i acc => do let x ← indexM a i; addM_w 32 acc x)
    ⦃fun r => 0 ≤ r⦄ := by
  rust_vc [foldRangeM_spec 0 n (0 : Int) _ (fun i acc => 0 ≤ acc ∧ acc ≤ 255 * i)]

end Hax.RuntimeMExamples

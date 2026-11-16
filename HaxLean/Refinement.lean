/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Semantics
public import HaxLean.RuntimeM

/-!
# Value refinement and exact agreement on partial results

The refinement order on `Option` results of the hax reference semantics, in the sense of
CompCert's `Val.lessdef` (Leroy, CACM 52(7), 2009) and LLVM poison refinement (`isRefinedBy`
of lean-mlir, Bhat et al., ITP 2024): `none` is refined by every result, and a defined result
is refined only by itself.

## Main definitions

* `LessDef a b` — every value `a` defines is the value of `b`.
* `RefinesBy R a b` — every value `a` defines is related by `R` to the total target `b`.
* `Defined bi f args` — the call `f args` of the builtin table `bi` has a value.
* `Builtins.LessDefOn N bi bi'` — on the names satisfying `N`, every call of `bi` is
  refined by the same call of `bi'`.
* `ExactAgree enc a m` — the partial result `a` and the `RustM` computation `m` agree
  exactly: `a = some (enc v)` when `m = ok v`, and `a = none` when `m` fails by a panic.

The literal semantics and the guarded operations of `HaxLean.RuntimeM` are related by
`ExactAgree`: a call of the literal is undefined exactly where Rust panics. `LessDef`
remains the order between two partial tables.

## Main statements

* `LessDef.refl`, `LessDef.trans`, `LessDef.none_left`, `LessDef.some_iff`.
* `LessDef.getD` — `a` is refined by `some (a.getD d)`, so an equation `x = a.getD d`
  gives `LessDef a (some x)`.
* `LessDef.bind`, `LessDef.map` — monotonicity under `Option.bind` and `Option.map`.
* `RefinesBy.of_lessDef`, `refinesBy_ite_iff`.
* `hax64Builtins_lessDef_hax64WordOps`, `defined_hax64Builtins_of_hax64WordOps` — a call
  that `hax64WordOps` defines is defined by `hax64Builtins` with the same value.
* `ExactAgree.eq_some_of_ok`, `ExactAgree.eq_none_iff`, `ExactAgree.lessDef_of_ok`.
* `widthArithOps_add_exactAgree` and its siblings for `sub`, `mul`, `div`, `rem`: the
  unsigned arithmetic of the literal agrees exactly with `Hax.addM_w`, … at `w.bits`.
* `panicOps_panic_exactAgree`, `panicOps_assert_exactAgree`: the heads `panic` and
  `assert` agree exactly with `Hax.panicM` and `Hax.assertM`.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax

/-- `LessDef a b`: `a` is less defined than `b`. Every value `a` defines is the value of `b`,
    and `none` is refined by every result. -/
def LessDef {α : Type _} (a b : Option α) : Prop := ∀ v, a = some v → b = some v

/-- The relational form of `LessDef` for a total target of another type: every value `a`
    defines is related by `R` to `b`. -/
def RefinesBy {α β : Type _} (R : α → β → Prop) (a : Option α) (b : β) : Prop :=
  ∀ v, a = some v → R v b

/-- Definedness of the call `f args` of the builtin table `bi`. -/
def Defined (bi : Builtins) (f : String) (args : List Value) : Prop := (bi f args).isSome

/-- Table refinement on the names satisfying `N`: every call of `bi` at such a name is
    refined by the same call of `bi'`. -/
def Builtins.LessDefOn (N : String → Prop) (bi bi' : Builtins) : Prop :=
  ∀ f, N f → ∀ args, LessDef (bi f args) (bi' f args)

namespace LessDef

variable {α β : Type _}

@[refl]
theorem refl (a : Option α) : LessDef a a := fun _ h => h

theorem trans {a b c : Option α} (hab : LessDef a b) (hbc : LessDef b c) : LessDef a c :=
  fun v h => hbc v (hab v h)

@[simp]
theorem none_left (b : Option α) : LessDef none b := fun _ h => by cases h

@[simp]
theorem some_iff (x : α) (b : Option α) : LessDef (some x) b ↔ b = some x :=
  ⟨fun h => h x rfl, fun h v hv => by cases hv; exact h⟩

/-- A refinement of a defined result is that result. -/
theorem eq_of_isSome {a b : Option α} (h : LessDef a b) (ha : a.isSome) : b = a := by
  cases a with
  | none => cases ha
  | some x => exact h x rfl

/-- Two results refining each other are equal. -/
theorem antisymm {a b : Option α} (hab : LessDef a b) (hba : LessDef b a) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some y => exact hba y rfl
  | some x => exact (hab x rfl).symm

/-- `a` is refined by its totalisation at any default. -/
theorem getD (a : Option α) (d : α) : LessDef a (some (a.getD d)) := by
  intro v h
  rw [h]
  rfl

/-- An equation `x = a.getD d` gives `LessDef a (some x)`. -/
theorem of_eq_getD {a : Option α} {d x : α} (h : x = a.getD d) : LessDef a (some x) :=
  h ▸ getD a d

theorem isSome {a b : Option α} (h : LessDef a b) (ha : a.isSome) : b.isSome := by
  rw [h.eq_of_isSome ha]
  exact ha

/-- Monotonicity under `Option.bind`. -/
theorem bind {a a' : Option α} {f f' : α → Option β} (ha : LessDef a a')
    (hf : ∀ x, LessDef (f x) (f' x)) : LessDef (a.bind f) (a'.bind f') := by
  intro v h
  cases a with
  | none => cases h
  | some x =>
    rw [ha x rfl]
    exact hf x v h

/-- Monotonicity under `Option.map`. -/
theorem map {a a' : Option α} (f : α → β) (ha : LessDef a a') :
    LessDef (a.map f) (a'.map f) := by
  intro v h
  cases a with
  | none => cases h
  | some x =>
    rw [ha x rfl]
    exact h

end LessDef

namespace RefinesBy

variable {α β : Type _}

/-- `LessDef` is `RefinesBy` at equality. -/
theorem lessDef_iff (a b : Option α) : LessDef a b ↔ RefinesBy (fun v w => w = some v) a b :=
  Iff.rfl

/-- A refinement followed by a relational refinement is a relational refinement. -/
theorem of_lessDef {R : α → β → Prop} {a a' : Option α} {b : β} (ha : LessDef a a')
    (h : RefinesBy R a' b) : RefinesBy R a b :=
  fun v hv => h v (ha v hv)

@[simp]
theorem none_left (R : α → β → Prop) (b : β) : RefinesBy R none b := fun _ h => by cases h

@[simp]
theorem some_iff (R : α → β → Prop) (x : α) (b : β) : RefinesBy R (some x) b ↔ R x b :=
  ⟨fun h => h x rfl, fun h v hv => by cases hv; exact h⟩

/-- Weakening of the relation. -/
theorem mono {R S : α → β → Prop} {a : Option α} {b : β} (hRS : ∀ x y, R x y → S x y)
    (h : RefinesBy R a b) : RefinesBy S a b :=
  fun v hv => hRS v b (h v hv)

end RefinesBy

/-- A guarded result `if p then some x else none` is refined relationally by `b` exactly
    when `R x b` holds under the guard. -/
theorem refinesBy_ite_iff {α β : Type _} (R : α → β → Prop) (p : Prop) [Decidable p]
    (x : α) (b : β) :
    RefinesBy R (if p then some x else none) b ↔ (p → R x b) := by
  by_cases hp : p <;> simp [hp]

namespace Builtins.LessDefOn

theorem refl (N : String → Prop) (bi : Builtins) : LessDefOn N bi bi :=
  fun _ _ _ => LessDef.refl _

theorem trans {N : String → Prop} {bi bi' bi'' : Builtins} (h₁ : LessDefOn N bi bi')
    (h₂ : LessDefOn N bi' bi'') : LessDefOn N bi bi'' :=
  fun f hf args => (h₁ f hf args).trans (h₂ f hf args)

/-- Restriction to a smaller set of names. -/
theorem mono {N M : String → Prop} {bi bi' : Builtins} (hNM : ∀ f, M f → N f)
    (h : LessDefOn N bi bi') : LessDefOn M bi bi' :=
  fun f hf args => h f (hNM f hf) args

/-- A refining table keeps every defined call. -/
theorem defined {N : String → Prop} {bi bi' : Builtins} (h : LessDefOn N bi bi')
    {f : String} (hf : N f) {args : List Value} (hd : Defined bi f args) :
    Defined bi' f args :=
  (h f hf args).isSome hd

end Builtins.LessDefOn

/-- Every call that `hax64WordOps` defines has the same value in `hax64Builtins`. -/
theorem hax64Builtins_lessDef_hax64WordOps (f : String) (args : List Value) :
    LessDef (hax64WordOps f args) (hax64Builtins f args) := by
  intro v h
  unfold hax64Builtins
  rw [h]
  rfl

/-- A call that `hax64WordOps` defines is defined in `hax64Builtins`. -/
theorem defined_hax64Builtins_of_hax64WordOps {f : String} {args : List Value}
    (h : (hax64WordOps f args).isSome) : Defined hax64Builtins f args :=
  (hax64Builtins_lessDef_hax64WordOps f args).isSome h

/-- A call to which `hax64WordOps` gives the value `v` is defined in `hax64Builtins`. -/
theorem defined_hax64Builtins_of_eq {f : String} {args : List Value} {v : Value}
    (h : hax64WordOps f args = some v) : Defined hax64Builtins f args :=
  defined_hax64Builtins_of_hax64WordOps (by rw [h]; rfl)

/-! ### Exact agreement with the guarded runtime -/

open Aeneas.Std (RustM Error)

/-- `ExactAgree enc a m`: the partial result `a` and the computation `m` agree exactly.
    `RustM.ofOption a .panic` is `enc <$> m`, so `a = some (enc v)` when `m = ok v` and
    `a = none` when `m = fail panic`; neither side diverges or fails otherwise. -/
def ExactAgree {α β : Type} (enc : β → α) (a : Option α) (m : RustM β) : Prop :=
  RustM.ofOption a .panic = enc <$> m

namespace ExactAgree

variable {α β : Type} {enc : β → α} {a : Option α} {m : RustM β}

/-- A computation returning `v` gives the defined result `enc v`. -/
theorem eq_some_of_ok (h : ExactAgree enc a m) {v : β} (hm : m = .ok v) : a = some (enc v) := by
  subst hm; cases a <;> simp_all [ExactAgree, Functor.map, pure] <;> cases h <;> rfl

/-- The result is undefined exactly when the computation panics. -/
theorem eq_none_iff (h : ExactAgree enc a m) : a = none ↔ m = .fail .panic := by
  cases a <;> cases m <;> simp_all [ExactAgree, Functor.map, pure] <;> cases h

/-- Exact agreement gives the refinement of the result by the computation's value. -/
theorem lessDef_of_ok (h : ExactAgree enc a m) {v : β} (hm : m = .ok v) :
    LessDef a (some (enc v)) := by
  rw [h.eq_some_of_ok hm]

end ExactAgree

/-- The unsigned word read as an integer result. -/
abbrev uintOfInt (w : IntWidth) (r : Int) : Value := .uint w r.toNat

/-- Unsigned `add` of the literal is checked addition `addM_w`. -/
theorem widthArithOps_add_exactAgree (w w' : IntWidth) (a b : Nat) :
    ExactAgree (uintOfInt w) (widthArithOps "add" [.uint w a, .uint w' b])
      (addM_w w.bits a b) := by
  have hp : (2 : Int) ^ w.bits = ((2 ^ w.bits : Nat) : Int) := by simp
  simp only [ExactAgree, widthArithOps, addM_w]
  split <;> split <;> rename_i h1 h2 <;> rw [hp] at h2 <;>
    simp only [IntWidth.modulus] at h1 <;> generalize 2 ^ w.bits = M at h1 h2 <;>
    first | rfl | (exfalso; omega)

/-- Unsigned `sub` of the literal is checked subtraction `subM_w`. -/
theorem widthArithOps_sub_exactAgree (w w' : IntWidth) (a b : Nat) :
    ExactAgree (uintOfInt w) (widthArithOps "sub" [.uint w a, .uint w' b])
      (subM_w w.bits a b) := by
  have hp : (2 : Int) ^ w.bits = ((2 ^ w.bits : Nat) : Int) := by simp
  simp only [ExactAgree, widthArithOps, subM_w]
  split <;> split <;> rename_i h1 h2 <;> rw [hp] at h2 <;>
    simp only [IntWidth.modulus] at h1 <;> generalize 2 ^ w.bits = M at h1 h2 <;>
    first | rfl | (exfalso; omega) | skip
  change RustM.ok _ = RustM.ok _
  simp only [sub, uintOfInt, RustM.ok.injEq, Value.uint.injEq, true_and]
  omega

/-- Unsigned `mul` of the literal is checked multiplication `mulM_w`. -/
theorem widthArithOps_mul_exactAgree (w w' : IntWidth) (a b : Nat) :
    ExactAgree (uintOfInt w) (widthArithOps "mul" [.uint w a, .uint w' b])
      (mulM_w w.bits a b) := by
  have hp : (2 : Int) ^ w.bits = ((2 ^ w.bits : Nat) : Int) := by simp
  simp only [ExactAgree, widthArithOps, mulM_w]
  split <;> split <;> rename_i h1 h2 <;> rw [hp] at h2 <;>
    simp only [IntWidth.modulus] at h1 <;> generalize 2 ^ w.bits = M at h1 h2 <;>
    first | rfl | (exfalso; omega)

/-- Unsigned `div` of the literal is `divM_w`, failing on a zero divisor. -/
theorem widthArithOps_div_exactAgree (w w' : IntWidth) (a b : Nat) :
    ExactAgree (uintOfInt w) (widthArithOps "div" [.uint w a, .uint w' b])
      (divM_w w.bits a b) := by
  simp only [ExactAgree, widthArithOps, divM_w]
  split <;> split <;> first | rfl | omega

/-- Unsigned `rem` of the literal is `remM_w`, failing on a zero divisor. -/
theorem widthArithOps_rem_exactAgree (w w' : IntWidth) (a b : Nat) :
    ExactAgree (uintOfInt w) (widthArithOps "rem" [.uint w a, .uint w' b])
      (remM_w w.bits a b) := by
  simp only [ExactAgree, widthArithOps, remM_w]
  split <;> split <;> first | rfl | omega

/-- The head `panic` is `panicM` at every argument list. -/
theorem panicOps_panic_exactAgree (args : List Value) :
    ExactAgree id (panicOps "panic" args) (panicM (α := Value)) := by
  simp only [ExactAgree, panicOps]; rfl

/-- The head `assert` is `assertM`. -/
theorem panicOps_assert_exactAgree (b : Bool) :
    ExactAgree (fun _ : Unit => Value.unit) (panicOps "assert" [.bool b]) (assertM b) := by
  cases b <;> rfl

end Hax

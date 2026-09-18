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
  backends/lean/Aeneas/Std/Primitives.lean
-/

module

public import Std.Do
public meta import Lean
import all Init.Internal.Order.Basic

/-!
# The `RustM` monad

`RustM α` is the outcome of a Rust computation: a value (`ok`), a failure
(`fail`, with the error kinds `panic` and `undef`), or divergence (`div`).
The module gives its monad structure, the flat order with `div` as bottom used
by `partial_fixpoint`, its registration with `Std.Do` (`RustM.instWP`), and the
loop combinator `loop` with its `mvcgen` rule `loop_spec`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace Aeneas

namespace Std

/-!
# Results and Monadic Combinators
-/

/-- Error kinds of a failing Rust computation. -/
inductive Error where
   | panic: Error
   | undef: Error
deriving Repr, BEq

open Error

/-- The outcome of a Rust computation: a value, a failure, or divergence. -/
inductive RustM (α : Type u) where
  | ok (v: α): RustM α
  | fail (e: Error): RustM α
  | div
deriving Repr, BEq

open RustM

instance RustM_Inhabited (α : Type u) : Inhabited (RustM α) :=
  Inhabited.mk (fail panic)

instance RustM_Nonempty (α : Type u) : Nonempty (RustM α) :=
  Nonempty.intro div

/-!
# Helpers
-/

/-- `ok? r` holds when `r` is a value. -/
def ok? {α: Type u} (r: RustM α): Bool :=
  match r with
  | ok _ => true
  | fail _ | div => false

/-- `div? r` holds when `r` diverges. -/
def div? {α: Type u} (r: RustM α): Bool :=
  match r with
  | div => true
  | ok _ | fail _ => false

/-- `massert b` is `ok ()` when `b` holds and a panic otherwise. -/
def massert (b : Prop) [Decidable b] : RustM Unit :=
  if b then ok () else fail panic

/-- The value of a computation known to succeed. -/
def eval_global {α: Type u} (x: RustM α) (_: ok? x := by decide) : α :=
  match x with
  | fail _ | div => by contradiction
  | ok x => x

/-- `ofOption x e` is `ok v` on `some v` and `fail e` on `none`. -/
@[simp]
def RustM.ofOption {a : Type u} (x : Option a) (e : Error) : RustM a :=
  match x with
  | some x => ok x
  | none => fail e

@[simp] abbrev liftFun1 {α : Sort _} {β : Type _} (f : α → β) : α → RustM β := fun x => ok (f x)
@[simp] abbrev liftFun2 {α β γ : Type} (f : α → β → γ) : α → β → RustM γ := fun x y => ok (f x y)
@[simp] abbrev liftFun3 {α β γ : Sort _} {δ : Type _} (f : α → β → γ → δ) :
    α → β → γ → RustM δ :=
  fun x y z => ok (f x y z)
@[simp] abbrev liftFun4 {α β γ δ : Sort _} {ε : Type _} (f : α → β → γ → δ → ε) :
    α → β → γ → δ → RustM ε := fun x y z a => ok (f x y z a)

/-!
# Do-DSL Support
-/

/-- Sequential composition: failure and divergence propagate. -/
def bind {α : Type u} {β : Type v} (x: RustM α) (f: α → RustM β) : RustM β :=
  match x with
  | ok v  => f v
  | fail v => fail v
  | div => div

instance : Bind RustM where
  bind := bind

instance : Pure RustM where
  pure := fun x => ok x

@[simp] theorem bind_ok {α : Type u} {β : Type v} (x : α) (f : α → RustM β) :
    bind (.ok x) f = f x := by
  simp [bind]
@[simp] theorem bind_fail {α : Type u} {β : Type v} (x : Error) (f : α → RustM β) :
    bind (.fail x) f = .fail x := by simp [bind]
@[simp] theorem bind_div {α : Type u} {β : Type v} (f : α → RustM β) : bind .div f = .div := by
  simp [bind]

@[simp] theorem bind_tc_ok {α β : Type u} (x : α) (f : α → RustM β) :
  (do let y ← .ok x; f y) = f x := by simp [Bind.bind, bind]

@[simp] theorem bind_tc_fail {α β : Type u} (x : Error) (f : α → RustM β) :
  (do let y ← fail x; f y) = fail x := by simp [Bind.bind, bind]

@[simp] theorem bind_tc_div {α β : Type u} (f : α → RustM β) :
  (do let y ← div; f y) = div := by simp [Bind.bind, bind]

@[simp] theorem bind_assoc_eq {a b c : Type u}
  (e : RustM a) (g :  a → RustM b) (h : b → RustM c) :
  (Bind.bind (Bind.bind e g) h) =
  (Bind.bind e (λ x => Bind.bind (g x) h)) := by
  simp [Bind.bind]
  cases e <;> simp [bind]

@[simp]
theorem bind_eq_iff {α β : Type} (x : RustM α) (y y' : α → RustM β) :
  ((Bind.bind x y) = (Bind.bind x y')) ↔
  ∀ v, x = ok v → y v = y' v := by
  cases x <;> simp_all [Bind.bind, bind]

instance : Monad RustM where

/-!
# Partial Fixpoint
-/

section Order

open Lean.Order

instance {α : Type u} : PartialOrder (RustM α) := inferInstanceAs (PartialOrder (FlatOrder .div))
noncomputable instance {α : Type u} : CCPO (RustM α) where
  has_csup hc := FlatOrder.instCCPO (b := RustM.div).has_csup hc
noncomputable instance : MonoBind RustM where
  bind_mono_left h := by
    cases h
    · exact FlatOrder.rel.bot
    · exact FlatOrder.rel.refl
  bind_mono_right h := by
    cases ‹RustM _›
    · exact h _
    · exact FlatOrder.rel.refl
    · exact FlatOrder.rel.refl

end Order

/-- `Function.uncurry` for tuple destructuring in bind continuations. -/
@[inline, spec] def uncurry {α β : Type _} {γ : Sort _} (f : α → β → γ) : α × β → γ :=
  fun (a, b) => f a b

@[simp, grind =] theorem uncurry_apply_pair {α β : Type _} {γ : Sort _} (f : α → β → γ) (a : α)
    (b : β) :
    uncurry f (a, b) = f a b :=
  id rfl

/-- `uncurry` applied to a proposition-valued function. -/
theorem uncurry_eq_prop {α β : Type _} (x : α × β) (p : α → β → Prop) :
    uncurry p x = p x.fst x.snd := by cases x; rfl

/-- `uncurry` applied to a function returning a proposition-valued function. -/
theorem uncurry_eq_prop_arrow {α β σ : Type _} (x : α × β) (p : α → β → σ → Prop) :
    uncurry p x = p x.fst x.snd := by cases x; rfl

section
open Lean.Order

@[partial_fixpoint_monotone]
theorem monotone_uncurry
    {α : Type u} {β : Type v} {φ : Sort w} [PartialOrder φ]
    {γ : Sort z} [PartialOrder γ]
    (f : γ → α → β → φ)
    (hmono : monotone f) :
    monotone (fun x => uncurry (f x)) := by
  intro x y hxy p
  simp [uncurry]
  exact monotone_apply p.2 _ (monotone_apply p.1 _ hmono) x y hxy

@[partial_fixpoint_monotone]
theorem monotone_uncurry_applied
    {α : Type u} {β : Type v} {φ : Sort w} [PartialOrder φ]
    {γ : Sort z} [PartialOrder γ]
    (f : γ → α → β → φ) (p : α × β)
    (hmono : monotone f) :
    monotone (fun x => uncurry (f x) p) := by
  intro x y hxy
  simp [uncurry]
  exact monotone_apply p.2 _ (monotone_apply p.1 _ hmono) x y hxy

end

attribute [simp, grind =] Function.uncurry_apply_pair

/-!
# Lift
-/

/-- `lift x` is `ok x`; it marks a call to a pure library function inside a monadic
program. It is not reducible, so a `let z ← lift (f x)` binding stays in the term. -/
def lift {α : Type u} (x : α) : RustM α := RustM.ok x

/-!
# Registration of `RustM` with `Std.Do`
-/

section
open _root_.Std.Do

/-- The postcondition shape of `RustM`: one component for values, one for errors, one for
divergence. -/
abbrev RustM.postShape : PostShape := (.except (ULift Error) (.except PUnit .pure))

/-- Weakest-precondition interpretation of `RustM` for `Std.Do` and `mvcgen`. -/
instance RustM.instWP : WP RustM.{u} postShape where
  wp x := {
    trans Q := match x with | .ok a => Q.1 a | .fail e => Q.2.1 (ULift.up e) | .div => Q.2.2.1 .unit
    conjunctiveRaw Q₁ Q₂ := by
      apply SPred.bientails.of_eq
      cases x <;> simp
  }

abbrev PostCond.okAssertion {α : Type u} (Q : PostCond α RustM.postShape) (r : α) :
    Assertion postShape :=
  Q.1 r

abbrev PostCond.ok {α : Type u} (Q : PostCond α RustM.postShape) (r : α) : Prop :=
  (Q.1 r).down

abbrev PostCond.failAssertion {α : Type u} (Q : PostCond α RustM.postShape) (e : ULift Error) :
    Assertion postShape :=
  Q.2.1 e

abbrev PostCond.fail {α : Type u} (Q : PostCond α RustM.postShape) (e : Error) : Prop :=
  (Q.2.1 (.up e)).down

abbrev PostCond.divAssertion {α : Type u} (Q : PostCond α RustM.postShape) :
    PUnit → Assertion postShape :=
  Q.2.2.1

abbrev PostCond.div {α : Type u} (Q : PostCond α RustM.postShape) : Prop :=
  (Q.2.2.1 .unit).down

end

/-!
# Loops
-/

/-- Outcome of one loop iteration: continue with a new state, or exit with a result. -/
inductive ControlFlow (α : Type u) (β : Type v) where
  | cont (v : α)
  | done (v : β)
deriving Repr, BEq

/-- `loop body x` iterates `body` from `x` until it returns `done`; a run that never
returns `done` is `div`. -/
def loop {α : Type u} {β : Type v} (body : α → RustM (ControlFlow α β)) (x : α) : RustM β := do
  match body x with
  | ok r =>
    match r with
    | ControlFlow.cont x => loop body x
    | ControlFlow.done x => ok x
  | fail e => fail e
  | div => div
partial_fixpoint

section
open _root_.Std.Do

/-- `mvcgen` rule for `loop`: an invariant, a well-founded relation and a measure.
When the postcondition admits divergence the rule holds by fixpoint induction and the
measure is not used. -/
@[spec]
theorem loop_spec
  {α β γ : Type}
  {P : PostCond β (PostShape.except (ULift Error) (PostShape.except PUnit.{1} PostShape.pure))}
  {body : α → RustM (ControlFlow α β)} {init : α}
  (inv : α → Prop)
  (rel : γ → γ → Prop)
  (termination : α → γ)
  (hwf : WellFounded rel)
  (h_inv_init : inv init)
  (h_body : ∀ x, inv x → ⦃ ⌜ True ⌝ ⦄ body x ⦃ post⟨
    fun cf => match cf with
      | .cont r => ⌜ inv r ∧ (rel (termination r) (termination x) ∨ PostCond.div P) ⌝
      | .done r => PostCond.okAssertion P r,
    PostCond.failAssertion P, PostCond.divAssertion P⟩ ⦄) :
  ⦃ ⌜ True ⌝ ⦄ loop body init ⦃ P ⦄ := by
  suffices h : ∀ x, inv x → (wp⟦loop body x⟧ P).down by
    unfold Triple
    intro _
    exact h init h_inv_init
  by_cases hdiv : PostCond.div P
  case pos =>
    intro x hinv
    delta loop
    refine Lean.Order.fix_induct (loop._proof_1 body)
      (motive := fun g => ∀ x, inv x → (wp⟦g x⟧ P).down) ?_ ?_ x hinv
    · apply Lean.Order.admissible_pi
      intro y
      apply Lean.Order.admissible_pi
      intro _
      apply Lean.Order.admissible_apply (β := fun _ => RustM β)
        (P := fun y r => (wp⟦r⟧ P).down) y
      exact Lean.Order.admissible_flatOrder _ hdiv
    · intro g IH y hinvy
      simp only []
      have hb : (wp⟦body y⟧ _).down := h_body y hinvy trivial
      cases hbe : body y with
      | ok cf =>
        rw [hbe] at hb
        cases cf with
        | cont r => exact IH r hb.1
        | done r => exact hb
      | fail e => rw [hbe] at hb; exact hb
      | div => rw [hbe] at hb; exact hb
  case neg =>
    intro x hinv
    induction hg : termination x using hwf.induction generalizing x
    rename_i g IH
    have hb : (wp⟦body x⟧ _).down := h_body x hinv trivial
    rw [loop.eq_1]
    cases hbe : body x with
    | ok cf =>
      rw [hbe] at hb
      cases cf with
      | cont r =>
        obtain ⟨hinvr, hrel | hd⟩ := hb
        · subst hg
          exact IH (termination r) hrel r hinvr rfl
        · exact absurd hd hdiv
      | done r => exact hb
    | fail e => rw [hbe] at hb; exact hb
    | div => rw [hbe] at hb; exact hb

end

/-!
# Misc
-/

/-- The Rust never type `!`. -/
inductive Never where

instance SubtypeBEq {α : Type _} [BEq α] (p : α → Prop) : BEq (Subtype p) where
  beq v0 v1 := v0.val == v1.val

instance SubtypeLawfulBEq {α : Type _} [BEq α] (p : α → Prop) [LawfulBEq α] :
    LawfulBEq (Subtype p) where
  eq_of_beq {a b} h := by cases a; cases b; simp_all [BEq.beq]
  rfl := by intro a; cases a; simp [BEq.beq]

/-- `some v` on `ok v`, `none` on failure and divergence. -/
def Option.ofRustM {a : Type u} (x : RustM a) :
  Option a :=
  match x with
  | ok x => some x
  | _ => none

/-- A trait object: a type, an instance of the trait at that type, and a value. -/
structure Dyn (Trait : Type u → Type v) where
  /-- The type Self -/
  self : Type u
  /-- The trait instance -/
  inst : Trait self
  /-- The value itself -/
  value : self

end Std

end Aeneas

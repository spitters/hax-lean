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
  backends/lean/Aeneas/Std/WP.lean
  backends/lean/Aeneas/Std/PrimitivesLemmas.lean
-/

module

public import HaxLean.Rust.Primitives
public meta import Lean
import all Init.Internal.Order.Basic

/-!
# Specifications over `RustM`

`spec x p` (total correctness), `dspec x p` (divergence allowed) and
`partialSpec x p_ok p_fail p_div` (one postcondition per outcome), the Hoare-triple
notation `x ⦃ z => P ⦄`, the bridges to `Std.Do` triples (`spec_to_mvcgen`,
`partialSpec_to_mvcgen`), `LawfulMonad RustM`, `WPMonad RustM`, and the rules for
`loop` and `massert`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Aeneas.Std.WP

open Aeneas.Std RustM

section
variable {α : Type u} {β : Type v}

/-- Postconditions over values of type `α`. -/
abbrev Post (α : Type u) := (α -> Prop)
/-- Preconditions. -/
def Pre := Prop

/-- Predicate transformers over `α`. -/
def Wp (α : Type u) := Post α → Pre

/-- The predicate transformer of a value. -/
def wp_return (x:α) : Wp α := fun p => p x

/-- Total-correctness predicate transformer: failure and divergence satisfy nothing. -/
def theta (m:RustM α) : Wp α :=
  match m with
  | ok x => wp_return x
  | fail _ => fun _ => False
  | div => fun _ => False

/-- `spec x p`: `x` returns a value, and the value satisfies `p`. -/
def spec {α} (x:RustM α) (p:Post α) :=
  theta x p

/-- `dspec x p`: `x` returns a value satisfying `p`, or diverges. -/
def dspec {α} (x:RustM α) (p:Post α) :=
  match x with
  | ok x => p x
  | fail _ => False
  | div => True

theorem spec_dspec (α) (x : RustM α) (p: Post α) : spec x p → dspec x p := by
  intros s
  simp [spec, dspec] at *
  cases x <;> simp [theta, wp_return] at * <;> assumption

theorem dspec_admissible {α} (p : Post α )
  : Lean.Order.admissible (fun x => dspec x p) := by
  apply Lean.Order.admissible_flatOrder
  simp [dspec, Lean.Order.FlatOrder.mk]

/-- `uncurry'` decomposes a pair in a postcondition into two binders. -/
def uncurry' {α β} (p : α → β → Prop) : α × β → Prop :=
  fun (x, y) => p x y

@[simp] theorem uncurry'_pair (x : α) (y : β) (p : α → β → Prop) : uncurry' p (x, y) = p x y := by
  simp [uncurry']
theorem uncurry'_eq (x : α × β) (p : α → β → Prop) : uncurry' p x = p x.fst x.snd := by
  simp [uncurry']

@[simp, grind =]
theorem spec_ok {p : Post α} (x : α) : spec (ok x) p ↔ p x := by simp [spec, theta, wp_return]

@[simp, grind =]
theorem spec_fail {p : Post α} (e : Error) : spec (fail e) p ↔ False := by simp [spec, theta]

@[simp, grind =]
theorem spec_div {p : Post α} : spec div p ↔ False := by simp [spec, theta]

@[simp, grind =]
theorem spec_ok_pair {α β} (a : α) (b : β) (f : α → β → Prop) :
    spec (ok (a, b)) (uncurry f) ↔ f a b := Iff.rfl

@[simp, grind =]
theorem spec_fail_pair (e : Error) (f : α → β → Prop) :
    spec (fail e) (uncurry f) ↔ False := Iff.rfl

@[simp, grind =]
theorem spec_div_pair (f : α → β → Prop) :
    spec div (uncurry f) ↔ False := Iff.rfl

theorem spec_mono {α} {P₁ : Post α} {m : RustM α} {P₀ : Post α} (h : spec m P₀):
  (∀ x, P₀ x → P₁ x) → spec m P₁ := by
  intros HMonPost
  revert h
  unfold spec theta wp_return
  cases m <;> grind

theorem spec_bind {α β} {k : α -> RustM β} {Pₖ : Post β} {m : RustM α} {Pₘ : Post α} :
  spec m Pₘ →
  (forall x, Pₘ x → spec (k x) Pₖ) →
  spec (Std.bind m k) Pₖ := by
  intro Hm Hk
  cases m
  · simp
    apply Hk
    simpa using Hm
  · simp at Hm
  · simp at Hm

/-- Currying of a function on pairs. -/
def curry {α β γ} (f : α × β → γ) (x : α) : β → γ := fun y => f (x, y)

/-- Implication -/
def imp (P Q : Prop) : Prop := P → Q

@[simp]
theorem imp_and_iff (P0 P1 Q : Prop) : imp (P0 ∧ P1) Q ↔ P0 → imp P1 Q := by simp [imp]

/-- Implication with quantifier -/
def qimp {α} (P₀ P₁ : Post α) : Prop := ∀ x, P₀ x → P₁ x

/-- `qimp` of an `uncurry'` postcondition as a sequence of universal quantifiers. -/
@[simp]
theorem qimp_uncurry' {α₀ α₁} (P : α₀ → α₁ → Prop) (Q : α₀ × α₁ → Prop) :
  qimp (uncurry' P) Q ↔ ∀ x, qimp (P x) (curry Q x) := by
  simp [qimp, curry, uncurry']

theorem qimp_iff {α} (P₀ P₁ : Post α) : qimp P₀ P₁ ↔ ∀ x, imp (P₀ x) (P₁ x) := by simp [qimp, imp]

/-- `spec_mono` with the implication packaged as `qimp`. -/
theorem spec_mono' {α} {P₁ : Post α} {m : RustM α} {P₀ : Post α} (h : spec m P₀):
  qimp P₀ P₁ → spec m P₁ := by
  intros HMonPost
  revert h
  unfold spec theta wp_return
  cases m <;> grind [qimp]

/-- Implication of a `spec` predicate with quantifier -/
def qimp_spec {α β} (P : α → Prop) (k : α → RustM β) (Q : β → Prop) : Prop :=
  ∀ x, P x → spec (k x) Q

/-- `spec_bind` with the continuation hypothesis packaged as `qimp_spec`. -/
theorem spec_bind' {α β} {k : α -> RustM β} {Pₖ : Post β} {m : RustM α} {Pₘ : Post α} :
  spec m Pₘ →
  (qimp_spec Pₘ k Pₖ) →
  spec (Std.bind m k) Pₖ := by
  intro Hm Hk
  cases m
  · simp
    apply Hk
    simpa using Hm
  · simp at Hm
  · simp at Hm

/-- `qimp_spec` of an `uncurry'` postcondition as a sequence of universal quantifiers. -/
@[simp]
theorem qimp_spec_uncurry' {α₀ α₁ β} (P : α₀ → α₁ → Prop) (k : α₀ × α₁ → RustM β) (Q : β → Prop) :
  qimp_spec (uncurry' P) k Q ↔ ∀ x, qimp_spec (P x) (curry k x) Q := by
  simp [qimp_spec, curry, uncurry']

theorem qimp_spec_iff {α β} (P : α → Prop) (k : α → RustM β) (Q : β → Prop) :
  qimp_spec P k Q ↔ ∀ x, imp (P x) (spec (k x) Q) := by
  simp [qimp_spec, imp]

@[simp]
theorem qimp_exists {α β} (P₀ : β → Post α) (P₁ : Post α) :
  qimp (fun x => ∃ y, P₀ y x) P₁ ↔ ∀ x, qimp (P₀ x) P₁ := by
  simp only [qimp, forall_exists_index]; grind

@[simp]
theorem qimp_spec_exists {α β γ} (P : γ → α → Prop) (k : α → RustM β) (Q : β → Prop) :
  qimp_spec (fun x => ∃ y, P y x) k Q ↔ ∀ x, qimp_spec (P x) k Q := by
  simp only [qimp_spec]; grind

theorem spec_equiv_exists (m:RustM α) (P:Post α) :
  spec m P ↔ (∃ y, m = ok y ∧ P y) := by
  cases m <;> simp [spec, theta, wp_return]

theorem spec_imp_exists {m:RustM α} {P:Post α} :
  spec m P → (∃ y, m = ok y ∧ P y) := by
  exact (spec_equiv_exists m P).1

theorem exists_imp_spec {m:RustM α} {P:Post α} :
  (∃ y, m = ok y ∧ P y) → spec m P := by
  exact (spec_equiv_exists m P).2

theorem dspec_mono' {α} {P₁ : Post α} {m : RustM α} {P₀ : Post α} (h : dspec m P₀):
  qimp P₀ P₁ → dspec m P₁ := by
  intros HMonPost
  revert h
  unfold dspec
  cases m <;> grind [qimp]

/-- Implication of a `dspec` predicate with quantifier -/
def qimp_dspec {α β} (P : α → Prop) (k : α → RustM β) (Q : β → Prop) : Prop :=
  ∀ x, P x → dspec (k x) Q

theorem dspec_bind' {α β} {k : α -> RustM β} {Pₖ : Post β} {m : RustM α} {Pₘ : Post α} :
  dspec m Pₘ →
  (qimp_dspec Pₘ k Pₖ) →
  dspec (Std.bind m k) Pₖ := by
  intro Hm Hk
  cases m
  · simp
    apply Hk
    simpa [dspec] using Hm
  · simp [dspec] at Hm
  · simp [dspec]

@[simp]
theorem qimp_dspec_uncurry' {α₀ α₁ β} (P : α₀ → α₁ → Prop) (k : α₀ × α₁ → RustM β)
    (Q : β → Prop) :
  qimp_dspec (uncurry' P) k Q ↔ ∀ x, qimp_dspec (P x) (curry k x) Q := by
  simp [qimp_dspec, curry, uncurry']

@[simp]
theorem qimp_dspec_unit {α} (P : Unit → Prop) (k : Unit → RustM α) (Q : α → Prop) :
  qimp_dspec P k Q ↔ (P () → dspec (k ()) Q) := by
  grind [qimp_dspec]

@[simp]
theorem qimp_dspec_exists {α β γ} (P : γ → α → Prop) (k : α → RustM β) (Q : β → Prop) :
  qimp_dspec (fun x => ∃ y, P y x) k Q ↔ ∀ x, qimp_dspec (P x) k Q := by
  simp only [qimp_dspec, forall_exists_index]; grind

theorem qimp_dspec_iff {α β} (P : α → Prop) (k : α → RustM β) (Q : β → Prop) :
  qimp_dspec P k Q ↔ ∀ x, imp (P x) (dspec (k x) Q) := by
  simp [qimp_dspec, imp]

@[simp, grind =]
theorem dspec_ok {p : Post α} (x : α) : dspec (ok x) p ↔ p x := by simp [dspec]

theorem dspec_imp_forall {m:RustM α} {P:Post α} :
  dspec m P → (∀ y, m = ok y → P y) := by
  intro h y hy
  subst hy
  simpa [dspec] using h

/-- Partial-correctness specification with one postcondition per outcome:
`p_ok` on a value, `p_fail` on a failure, `p_div` on divergence. -/
def partialSpec {α} (x : RustM α)
    (p_ok : α → Prop) (p_fail : Error → Prop) (p_div : Prop) : Prop :=
  match x with
  | ok a   => p_ok a
  | fail e => p_fail e
  | div    => p_div

@[simp, grind =]
theorem partialSpec_ok (a : α) (p_ok : α → Prop) (p_fail : Error → Prop) (p_div : Prop) :
    partialSpec (ok a) p_ok p_fail p_div ↔ p_ok a := by
  simp [partialSpec]

@[simp, grind =]
theorem partialSpec_fail (e : Error) (p_ok : α → Prop) (p_fail : Error → Prop) (p_div : Prop) :
    partialSpec (α := α) (fail e) p_ok p_fail p_div ↔ p_fail e := by
  simp [partialSpec]

@[simp, grind =]
theorem partialSpec_div (p_ok : α → Prop) (p_fail : Error → Prop) (p_div : Prop) :
    partialSpec div p_ok p_fail p_div ↔ p_div := by
  simp [partialSpec]

/-- A total-correctness `spec` from a `partialSpec` whose failure and divergence
postconditions are refutable. -/
theorem spec_of_partialSpec
    {α} {x : RustM α} {p_ok : α → Prop} {p_fail : Error → Prop} {p_div : Prop}
    (h : partialSpec x p_ok p_fail p_div)
    (h_fail : ∀ e, ¬ p_fail e) (h_div : ¬ p_div) :
    spec x p_ok := by
  cases x <;> simp_all [partialSpec, spec, theta, wp_return]

end

end Aeneas.Std.WP

namespace Aeneas

open Aeneas.Std WP RustM

/-!
# Hoare triple notation

`x ⦃ z => P ⦄` is `spec x (fun z => P)`, `x ⦃ y z => P ⦄` is
`spec x (uncurry' fun y => fun z => P)`, a tuple binder `(a, b)` is expanded through
`Std.uncurry`, and the `⦄div` variants produce `dspec`.
-/

scoped syntax:54 term:55 " ⦃ " term+ " => " term " ⦄" : term
scoped syntax:54 term:55 " ⦃ " term " ⦄" : term

scoped syntax:54 term:55 " ⦃ " term+ " => " term " ⦄div" : term
scoped syntax:54 term:55 " ⦃ " term " ⦄div" : term

open Lean

/-- The `Std.uncurry` chain wrapping a curried lambda over the binders `xs`. -/
meta partial def buildUncurryLam (xs : List (TSyntax `term)) (body : TSyntax `term) :
    MacroM (TSyntax `term) := do
  let uncurryIdent := mkIdent ``Std.uncurry
  match xs with
  | [] => pure body
  | [x] => `(fun $x => $body)
  | [a, b] => `($uncurryIdent (fun $a $b => $body))
  | a :: rest =>
    let inner ← buildUncurryLam rest body
    `($uncurryIdent (fun $a => $inner))

/-- `binder => body` for a binder that may be a nested tuple. -/
meta partial def mkBinderFun (depth : Nat) (binder : Term) (body : Term) : MacroM Term := do
  match binder with
  | `( ($a, $bs,*) ) =>
    let xs : List Term := a :: bs.getElems.toList
    let mut leafIdents : List Term := []
    let mut wrappedBody := body
    for (x, idx) in xs.zipIdx.reverse do
      match x with
      | `( ($_, $_,*) ) =>
        let freshIdent := mkIdent $ .mkSimple s!"_p_{depth}_{idx}"
        let inner ← mkBinderFun (depth + 1) x wrappedBody
        wrappedBody ← `($inner $freshIdent)
        leafIdents := freshIdent :: leafIdents
      | _ =>
        leafIdents := x :: leafIdents
    buildUncurryLam leafIdents wrappedBody
  | _ => `(fun $binder => $body)

/-- The postcondition function for the binders `xs` and the body `p`. -/
meta def mk_function_syntax (p : TSyntax `term) (depth : Nat) (xs : List Term) : MacroM Term := do
  match xs with
  | [] => `($p)
  | [x] => mkBinderFun depth x p
  | x :: xs =>
    let xs ← mk_function_syntax p (depth + 1) xs
    let inner ← mkBinderFun depth x xs
    `(uncurry' $inner)

/-- The identifiers of a binder group `a b c`, or `none` for any other term. -/
meta partial def binderGroupIdents? (stx : Syntax) : Option (Array Term) :=
  if stx.isIdent then some #[⟨stx⟩]
  else if stx.getKind == ``Lean.Parser.Term.app || stx.getKind == Lean.nullKind then
    stx.getArgs.foldlM (init := (#[] : Array Term)) fun acc s =>
      (binderGroupIdents? s).map (acc ++ ·)
  else none

/-- `(a b c : T)` as the binders `(a : T)`, `(b : T)`, `(c : T)`; any other binder unchanged. -/
meta def expandGroupedBinder (binder : Term) : MacroM (List Term) := do
  match binder with
  | `(($e : $t)) =>
    match binderGroupIdents? e.raw with
    | some ids =>
      if ids.size ≤ 1 then pure [binder]
      else ids.toList.mapM fun id => `(($id : $t))
    | none => pure [binder]
  | _ => pure [binder]

/-- `expandGroupedBinder` over a list of binders. -/
meta def expandBinders (xs : List Term) : MacroM (List Term) := do
  let mut out : Array Term := #[]
  for x in xs do
    out := out ++ (← expandGroupedBinder x).toArray
  pure out.toList

/-- The postcondition term for `⦃ xs => p ⦄`. -/
meta def mkPost (p : Term) (xs : List Term) : MacroM Term := do
  mk_function_syntax p 0 (← expandBinders xs)

macro_rules
  | `($e ⦃ $x => $p ⦄) => do
    let post ← mkPost p [x]
    `(Aeneas.Std.WP.spec $e $post)
  | `($e ⦃ $x => $p ⦄div) => do
    let post ← mkPost p [x]
    `(Aeneas.Std.WP.dspec $e $post)

macro_rules
  | `($e ⦃ $x $xs:term* => $p ⦄) => do
    let post ← mkPost p (x :: xs.toList)
    `(Aeneas.Std.WP.spec $e $post)
  | `($e ⦃ $x $xs:term* => $p ⦄div) => do
    let post ← mkPost p (x :: xs.toList)
    `(Aeneas.Std.WP.dspec $e $post)

macro_rules
  | `($e ⦃ $p ⦄) => do `(_root_.Aeneas.Std.WP.spec $e $p)
  | `($e ⦃ $p ⦄div) => do `(_root_.Aeneas.Std.WP.dspec $e $p)

end Aeneas

namespace Aeneas.Std.WP

open Aeneas.Std RustM

section
variable {α : Type u}

@[simp]
theorem qimp_spec_unit {α} (P : Unit → Prop) (k : Unit → RustM α) (Q : α → Prop) :
  qimp_spec P k Q ↔ (P () → k () ⦃ Q ⦄) := by
  grind [qimp_spec]

@[simp]
theorem qimp_unit (P Q : Unit → Prop) :
  qimp P Q ↔ (P () → Q ()) := by
  grind [qimp]

@[simp]
theorem imp_exists_iff {α} (P : α → Prop) (Q : Prop) :
  imp (∃ x, P x) Q ↔ (∀ x, imp (P x) Q) := by
  simp only [imp, forall_exists_index]

end

end Aeneas.Std.WP

namespace Aeneas.Std.WP

/-!
# `mvcgen`
-/

open Aeneas.Std RustM
open _root_.Std.Do

instance : LawfulMonad RustM where
    map_const := by intros; rfl
    id_map := by intros _ x; cases x <;> rfl
    seqLeft_eq := by intros _ _ x y; cases x <;> cases y <;> rfl
    seqRight_eq := by intros _ _ x y; cases x <;> cases y <;> rfl
    pure_seq := by intros _ _ _ x; cases x <;> rfl
    pure_bind := by intros; rfl
    bind_pure_comp := by intros; rfl
    bind_map := by intros; rfl
    bind_assoc := by intros _ _ _ x _ _; cases x <;> rfl

instance RustM.instWPMonad : WPMonad RustM (.except (ULift Error) (.except PUnit .pure)) where
  wp_pure a := by apply PredTrans.ext; intro Q; simp [PredTrans.apply, wp, WP.wp]; rfl
  wp_bind x f := by
    apply PredTrans.ext; intro Q; simp [PredTrans.apply, wp, WP.wp]; cases x <;> rfl

theorem RustM.of_wp {α : Type u} {x : RustM α} (P : RustM α → Prop) :
    (⊢ₛ wp⟦x⟧ (fun a => ⌜P (.ok a)⌝,
                  fun e => ⌜P (.fail e.down)⌝,
                  fun .unit => ⌜P .div⌝, .unit)) → P x := by
  intro hspec
  simp only [WP.wp, PredTrans.apply] at hspec
  split at hspec <;> simp_all

/-- A `spec` as an `mvcgen` triple. -/
theorem spec_to_mvcgen {α : Type u} {x : RustM α} {Q : α → Prop}
    (h : spec x Q) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ Q r ⌝ ⦄ := by
  obtain ⟨v, hx, hQv⟩ := spec_imp_exists h
  subst hx
  simp [Triple, WP.wp, PredTrans.apply, hQv]

/-- A `dspec` as an `mvcgen` triple under the precondition that `x` does not diverge. -/
theorem dspec_to_mvcgen {α : Type u} {x : RustM α} {Q : α → Prop}
    (h : dspec x Q) :
    ⦃ ⌜ ¬ x = .div ⌝ ⦄ x ⦃ ⇓ r => ⌜ Q r ⌝ ⦄ := by
  simp [Triple, WP.wp, PredTrans.apply, SPred.pure]
  cases x <;> simp [*, dspec] at * <;> trivial

/-- A `partialSpec` as an `mvcgen` triple. -/
theorem partialSpec_to_mvcgen {α : Type u} {x : RustM α}
    {p_ok : α → Prop} {p_fail : Error → Prop} {p_div : Prop}
    (h : partialSpec x p_ok p_fail p_div)
    {Q : PostCond α RustM.postShape}
    (h_ok   : ∀ r, p_ok r → PostCond.ok Q r)
    (h_fail : ∀ e, p_fail e → PostCond.fail Q e)
    (h_div  : p_div → PostCond.div Q) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ Q ⦄ := by
  cases x
    <;> simp only [partialSpec] at h
    <;> simp [Triple, WP.wp, PredTrans.apply, h_ok, h_fail, h_div, h]

@[spec]
theorem RustM.ok_spec {α : Type} {a : α} {Q : PostCond α RustM.postShape} (hQ : (Q.1 a).down) :
  ⦃ ⌜ True ⌝ ⦄ RustM.ok a ⦃ Q ⦄ := by simpa [Triple]

@[spec]
theorem RustM.fail_spec {α : Type} {e : Error} {Q : PostCond α RustM.postShape}
    (hQ : (Q.2.1 (ULift.up e)).down) :
  ⦃ ⌜ True ⌝ ⦄ (RustM.fail e : RustM α) ⦃ Q ⦄ := by simpa [Triple]

/-- A triple with postcondition `r = v` holds exactly when the program is `.ok v`. -/
theorem triple_post_eq_iff_eq {α : Type} {x : RustM α} {v : α} :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ r = v ⌝ ⦄ ↔ x = .ok v := by
  cases x <;> simp_all [Triple, WP.wp, PredTrans.apply]

/-- On a program equal to `.ok v`, a triple is its postcondition at `v`. -/
theorem triple_iff_post_of_eq_ok {α : Type} {x : RustM α} {v : α} {P : α → Prop}
    (hx : x = .ok v) : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ ↔ P v := by
  simp_all [Triple, WP.wp, PredTrans.apply]

/-- A triple holds exactly when the program is `.ok a` for an `a` satisfying the postcondition. -/
theorem triple_iff_exists_ok {α : Type} {x : RustM α} {P : α → Prop} :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ ↔ ∃ a, x = .ok a ∧ P a := by
  cases x <;> simp_all [Triple, WP.wp, PredTrans.apply]

/-- A triple whose postcondition also records the triple `x = .ok r`. -/
theorem triple_with_self {α : Type} {x : RustM α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ∧ ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r' => ⌜ r' = r ⌝ ⦄ ⌝ ⦄ := by
  obtain ⟨a, hx, hPa⟩ := triple_iff_exists_ok.1 h
  exact (triple_iff_post_of_eq_ok hx).2 ⟨hPa, triple_post_eq_iff_eq.2 hx⟩

/-- Modus ponens between a total triple and a partial triple on the same program. -/
theorem triple_in_hypothesis {α : Type} {f : RustM α} {Q : α → Assertion RustM.postShape}
    (p : Prop)
    (h : ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓ r => Q r ⦄)
    (hp : ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓? r => Q r → ⌜ p ⌝ ⦄) :
    p := by
  cases f <;> simp_all [Triple, WP.wp, PredTrans.apply]

end Aeneas.Std.WP

namespace Aeneas.Std

open WP

/-!
# Loops
-/

/-- Total-correctness rule for `loop` with an invariant and a well-founded measure. -/
theorem loop.spec {α : Type u} {β : Type v} {γ : Type w}
  (measure : α → γ)
  [wf : WellFoundedRelation γ]
  (inv : α → Prop)
  (post : β → Prop)
  (body : α → RustM (ControlFlow α β)) (x : α)
  (hBody :
    ∀ x, inv x → body x ⦃ r =>
      match r with
      | .done y => post y
      | .cont x' => inv x' ∧ wf.rel (measure x') (measure x) ⦄)
  (hInv : inv x) :
  loop body x ⦃ post ⦄ := by
  suffices ∀ x' x, measure x = x' → inv x → loop body x ⦃ post ⦄
    by apply this <;> first | rfl | assumption
  apply @wf.wf.fix γ (fun x' =>
    ∀ x, measure x = x' →
    inv x → loop body x ⦃ post ⦄)
  intro x' ih x0 hx0 hinv0
  obtain ⟨r, hr, hpost⟩ := spec_imp_exists (hBody x0 hinv0)
  rw [loop.eq_1, hr]
  cases r with
  | done y => exact (spec_ok (p := post) y).2 hpost
  | cont x1 =>
    obtain ⟨hinv1, hrel⟩ := hpost
    exact ih (measure x1) (hx0 ▸ hrel) x1 rfl hinv1

/-- `loop.spec` with a natural-number measure. -/
theorem loop.spec_decr_nat {α : Type u} {β : Type v}
  (measure : α → Nat)
  (inv : α → Prop)
  (post : β → Prop)
  (body : α → RustM (ControlFlow α β)) (x : α)
  (hBody :
    ∀ x, inv x → body x ⦃ r =>
      match r with
      | .done y => post y
      | .cont x' => inv x' ∧ measure x' < measure x ⦄)
  (hInv : inv x) :
  loop body x ⦃ post ⦄ := by
  have := loop.spec measure inv post body x hBody hInv
  apply this

end Aeneas.Std

namespace Aeneas.Std.WP

/-- `(Unit → p) ↔ p`. -/
theorem forall_unit {p : Prop} : (Unit → p) ↔ p := by simp

end Aeneas.Std.WP

/-! ## `massert` (source: `PrimitivesLemmas.lean`) -/

namespace Aeneas.Std

open RustM WP

theorem massert_spec (b : Prop) [Decidable b] :
    partialSpec (massert b)
      (fun _ => b)
      (fun | .panic => ¬ b | _ => False)
      False := by
  unfold massert
  split <;> simp_all [partialSpec]

@[simp]
theorem massert_ok (b : Prop) [Decidable b] : massert b = ok () ↔ b := by simp [massert]

@[simp]
theorem spec_massert (b : Prop) [Decidable b] {P : Post Unit} :
    Std.WP.spec (massert b) P ↔ (b ∧ P ()) := by
  simp [massert]
  split <;> simp <;> grind

@[simp] theorem massert_True : massert True = ok () := by simp [massert]
@[simp] theorem massert_False : massert False = fail .panic := by simp [massert]

end Aeneas.Std

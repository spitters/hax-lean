/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Phase.ContinueFlag

/-!
# Function-level early returns as branches

In a function body, a `cfBreak p` at a statement position outside every loop returns
from the function: `denote'` passes the value `controlFlow true v` through `seq`,
`letBind` and `ifThenElse`, and the statements after it do not run. `ere` expresses
the same control by moving the rest of the body into the branches: a
`seq (ifThenElse c t e) b` whose branches return becomes
`ifThenElse c (seq t b) (seq e b)` with each branch rewritten, a `seq` after a
`letBind` whose body returns moves into the body, and a returning `cfBreak p` followed
by statements becomes `p`, which ends the function with the value of `p`.

The rewritten body has no function-level `cfBreak`; loops are left as they are, so a
`cfBreak` in a loop body, and the return of a `forFoldReturn`, keep their meaning.

**Agreement.** A run of the body that ends in a value is matched by a run of the
rewritten body from the same environment, ending in the same environment, whose outcome
is the same or, where the body returned `controlFlow true v` at function level, the
value `v` (`RetRel`).

## Main definitions

* `hasRet`: a `cfBreak` at a statement position outside every loop
* `ereSeq`: a statement followed by the rewritten rest of the body
* `ere`: the rewriting of a function body

## Main results

* `seq_assoc_run`: `seq (seq a₁ a₂) b` and `seq a₁ (seq a₂ b)` have the same runs
* `ereSeq_rel`: `seq a b` and `ereSeq a k` are related when `b` and `k` are
* `ere_rel`: a body and its rewriting are related (`ERel`)
* `ere_run`: the run of `ere e` from the environment of a run of `e` ending in a value
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.EarlyReturnElim

open Hax.ContinueFlag (seq_run ifThenElse_run letBind_run cfBreak_run)

/-! ## The rewriting -/

/-- Whether `e` has a `cfBreak` at a statement position outside every loop. -/
def hasRet : ImpExpr → Bool
  | .cfBreak _ => true
  | .letBind _ _ b => hasRet b
  | .seq a b => hasRet a || hasRet b
  | .ifThenElse _ t e => hasRet t || hasRet e
  | _ => false

/-- The statement `a` followed by the rewritten rest `k` of a function body: a returning
    `cfBreak p` is `p`; a `ifThenElse`, `letBind` or `seq` that returns carries `k` into
    its branches, its body or its second statement; any other statement is `seq a k`. -/
def ereSeq : ImpExpr → ImpExpr → ImpExpr
  | .cfBreak p, _ => p
  | .ifThenElse c t e, k =>
      if hasRet t || hasRet e then .ifThenElse c (ereSeq t k) (ereSeq e k)
      else .seq (.ifThenElse c t e) k
  | .letBind n v b, k =>
      if hasRet b then .letBind n v (ereSeq b k) else .seq (.letBind n v b) k
  | .seq a₁ a₂, k =>
      if hasRet a₁ || hasRet a₂ then ereSeq a₁ (ereSeq a₂ k) else .seq (.seq a₁ a₂) k
  | a, k => .seq a k

/-- The function body `e` with its function-level returns moved into branches: a tail
    `cfBreak p` is `p`, and a `seq a b` is `ereSeq a` of the rewritten `b`. -/
def ere : ImpExpr → ImpExpr
  | .cfBreak p => p
  | .letBind n v b => .letBind n v (ere b)
  | .seq a b => ereSeq a (ere b)
  | .ifThenElse c t e => .ifThenElse c (ere t) (ere e)
  | e => e

/-! ## The relation between runs -/

/-- The outcome `o'` of the rewritten body against the outcome `o` of the body: the same
    outcome, or the value `v`, not a control-flow value, where the body returned
    `controlFlow true v`. -/
def RetRel (o o' : Outcome) : Prop :=
  o' = o ∨ ∃ v, v.isControlFlow = false ∧ o = .val (.controlFlow true v) ∧ o' = .val v

/-- Every run of `x` ending in a value is matched by a run of `y` from the same
    environment, ending in the same environment, with a related outcome. -/
def ERel (bi : Builtins) (fuel : Nat) (x y : ImpExpr) : Prop :=
  ∀ env o env', (denote' bi fuel x).run env = (o, env') → (∃ v, o = .val v) →
    ∃ o', (denote' bi fuel y).run env = (o', env') ∧ RetRel o o'

section Runs

variable {bi : Builtins} {fuel : Nat}

theorem ERel.refl (x : ImpExpr) : ERel bi fuel x x :=
  fun _ o _ h _ => ⟨o, h, Or.inl rfl⟩

theorem ERel.of_run_eq {x y : ImpExpr} (h : ∀ env, (denote' bi fuel x).run env =
    (denote' bi fuel y).run env) : ERel bi fuel x y :=
  fun env o _ hx _ => ⟨o, (h env).symm.trans hx, Or.inl rfl⟩

theorem ERel.trans_eq {x y z : ImpExpr} (h : ∀ env, (denote' bi fuel x).run env =
    (denote' bi fuel y).run env) (hyz : ERel bi fuel y z) : ERel bi fuel x z :=
  fun env o env' hx hv => hyz env o env' ((h env).symm.trans hx) hv

/-- `seq (seq a₁ a₂) b` and `seq a₁ (seq a₂ b)` have the same runs. -/
theorem seq_assoc_run (a₁ a₂ b : ImpExpr) (env : Env) :
    (denote' bi fuel (.seq (.seq a₁ a₂) b)).run env =
      (denote' bi fuel (.seq a₁ (.seq a₂ b))).run env := by
  rw [seq_run, seq_run, seq_run]
  rcases h1 : (denote' bi fuel a₁).run env with ⟨o1, e1⟩
  rcases o1 with v | _ | _ | _ | _
  · cases v with
    | controlFlow k w => rfl
    | _ =>
      simp only
      rw [seq_run]
  all_goals rfl

/-- `seq a b` and `seq a k` are related when `b` and `k` are. -/
theorem seq_congr {a b k : ImpExpr} (h : ERel bi fuel b k) : ERel bi fuel (.seq a b) (.seq a k) := by
  intro env o env' hr hv
  rw [seq_run] at hr ⊢
  rcases h1 : (denote' bi fuel a).run env with ⟨o1, e1⟩
  rw [h1] at hr
  rcases o1 with v | _ | _ | _ | _
  · cases v with
    | controlFlow k w => exact ⟨o, hr, Or.inl rfl⟩
    | _ => exact h e1 o env' hr hv
  all_goals exact ⟨o, hr, Or.inl rfl⟩

/-- `seq a b` and `ereSeq a k` are related when `b` and `k` are. -/
theorem ereSeq_rel (a : ImpExpr) : ∀ (b k : ImpExpr), ERel bi fuel b k →
    ERel bi fuel (.seq a b) (ereSeq a k) := by
  induction a using ImpExpr.ind with
  | cfBreak p _ =>
    intro b k _ env o env' hr hv
    simp only [ereSeq]
    rw [seq_run, cfBreak_run] at hr
    rcases hp : (denote' bi fuel p).run env with ⟨o1, e1⟩
    rw [hp] at hr
    rcases o1 with v | _ | _ | _ | _
    · cases v with
      | controlFlow kk w =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
        exact ⟨_, rfl, Or.inl rfl⟩
      | _ =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
        exact ⟨_, rfl, Or.inr ⟨_, rfl, rfl, rfl⟩⟩
    all_goals
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
      obtain ⟨_, h⟩ := hv
      cases h
  | ifThenElse c t e _ iht ihe =>
    intro b k hbk
    simp only [ereSeq]
    split
    · intro env o env' hr hv
      rw [seq_run, ifThenElse_run] at hr
      rw [ifThenElse_run]
      rcases hc : (denote' bi fuel c).run env with ⟨oc, e1⟩
      rw [hc] at hr
      rcases oc with v | _ | _ | _ | _
      · cases v with
        | controlFlow kk w => exact ⟨o, hr, Or.inl rfl⟩
        | bool bb =>
          cases bb
          · exact ihe b k hbk e1 o env' (by rw [seq_run]; exact hr) hv
          · exact iht b k hbk e1 o env' (by rw [seq_run]; exact hr) hv
        | _ => exact ⟨o, hr, Or.inl rfl⟩
      all_goals exact ⟨o, hr, Or.inl rfl⟩
    · exact seq_congr hbk
  | letBind n v body _ ihb =>
    intro b k hbk
    simp only [ereSeq]
    split
    · intro env o env' hr hv
      rw [seq_run, letBind_run] at hr
      rw [letBind_run]
      rcases hv1 : (denote' bi fuel v).run env with ⟨o1, e1⟩
      rw [hv1] at hr
      rcases o1 with w | _ | _ | _ | _
      · cases w with
        | controlFlow kk w => exact ⟨o, hr, Or.inl rfl⟩
        | _ => exact ihb b k hbk _ o env' (by rw [seq_run]; exact hr) hv
      all_goals exact ⟨o, hr, Or.inl rfl⟩
    · exact seq_congr hbk
  | seq a₁ a₂ ih₁ ih₂ =>
    intro b k hbk
    simp only [ereSeq]
    split
    · exact ERel.trans_eq (seq_assoc_run a₁ a₂ b) (ih₁ _ _ (ih₂ b k hbk))
    · exact seq_congr hbk
  | _ => intro b k hbk; exact seq_congr hbk

/-- A function body and its rewriting `ere` are related. -/
theorem ere_rel (e : ImpExpr) : ERel bi fuel e (ere e) := by
  induction e using ImpExpr.ind with
  | cfBreak p _ =>
    intro env o env' hr hv
    simp only [ere]
    rw [cfBreak_run] at hr
    rcases hp : (denote' bi fuel p).run env with ⟨o1, e1⟩
    rw [hp] at hr
    rcases o1 with v | _ | _ | _ | _
    · cases v with
      | controlFlow kk w =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
        exact ⟨_, rfl, Or.inl rfl⟩
      | _ =>
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
        exact ⟨_, rfl, Or.inr ⟨_, rfl, rfl, rfl⟩⟩
    all_goals
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
      obtain ⟨_, h⟩ := hv
      cases h
  | letBind n v body _ ihb =>
    intro env o env' hr hv
    simp only [ere]
    rw [letBind_run] at hr ⊢
    rcases hv1 : (denote' bi fuel v).run env with ⟨o1, e1⟩
    rw [hv1] at hr
    rcases o1 with w | _ | _ | _ | _
    · cases w with
      | controlFlow kk w => exact ⟨o, hr, Or.inl rfl⟩
      | _ => exact ihb _ o env' hr hv
    all_goals exact ⟨o, hr, Or.inl rfl⟩
  | seq a b _ ihb =>
    simp only [ere]
    exact ereSeq_rel a b (ere b) ihb
  | ifThenElse c t e _ iht ihe =>
    intro env o env' hr hv
    simp only [ere]
    rw [ifThenElse_run] at hr ⊢
    rcases hc : (denote' bi fuel c).run env with ⟨oc, e1⟩
    rw [hc] at hr
    rcases oc with v | _ | _ | _ | _
    · cases v with
      | controlFlow kk w => exact ⟨o, hr, Or.inl rfl⟩
      | bool bb =>
        cases bb
        · exact ihe e1 o env' hr hv
        · exact iht e1 o env' hr hv
      | _ => exact ⟨o, hr, Or.inl rfl⟩
    all_goals exact ⟨o, hr, Or.inl rfl⟩
  | _ => exact ERel.refl _

/-- **The rewriting preserves the runs of a function body.** From the environment of a
    run of `e` that ends in a value, `ere e` ends in the same environment, with the same
    outcome or, where `e` returned `controlFlow true v` at function level, the value `v`. -/
theorem ere_run (e : ImpExpr) (env env' : Env) (o : Outcome)
    (h : (denote' bi fuel e).run env = (o, env')) (hv : ∃ v, o = .val v) :
    ∃ o', (denote' bi fuel (ere e)).run env = (o', env') ∧ RetRel o o' :=
  ere_rel e env o env' h hv

end Runs

end Hax.EarlyReturnElim

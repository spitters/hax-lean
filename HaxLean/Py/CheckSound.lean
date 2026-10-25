/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import HaxLean.Py.Check

/-!
# Soundness of the checker against the typing rules

A module accepted by `pyCheck` is well typed: every function whose body is
checked satisfies `FnOk` in the environment it is checked in, and every
function the conditions `fnSigOk` on its name, its signature and its call
depth.

* `inferExpr_sound` — `inferExpr env Γ e = .ok τ` gives `HasTy env Γ e τ`.
* `checkStmts_sound` — `checkStmts env top Γ ss = .ok Γ'` gives
  `StmtsOk env top Γ ss Γ'`.
* `checkBody_sound`, `checkFn_wellTyped` — a checked body satisfies `FnOk`;
  a checked function definition is well typed.
* `pyCheck_wellTyped` — `pyCheck m = .ok cm` gives `cm.WellTyped`.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Py

theorem bind_eq_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

theorem liftK_eq_ok {α : Type} {p : Pos} {ns : List String} {x : Except RefusalKind α} {a : α} :
    liftK p ns x = .ok a ↔ x = .ok a := by
  cases x <;> simp [liftK]

theorem refuse_ne_ok {α : Type} {p : Pos} {k : RefusalKind} {ns : List String} {a : α} :
    refuse p k ns ≠ .ok a := by
  simp [refuse]

mutual

/-- Soundness of `inferExpr`: an inferred type is a derivable type. -/
theorem inferExpr_sound (env : ModEnv) (Γ : Ctx) :
    (e : PyExpr) → (τ : PyTy) → inferExpr env Γ e = .ok τ → HasTy env Γ e τ
  | .name p x, τ, h => by
      simp only [inferExpr, liftK_eq_ok] at h
      exact .name h
  | .const p c, τ, h => by
      simp only [inferExpr, liftK_eq_ok] at h
      exact .const h
  | .binOp p l op r, τ, h => by
      simp only [inferExpr, bind_eq_ok, liftK_eq_ok] at h
      obtain ⟨τl, hl, τr, hr, h⟩ := h
      exact .binOp (inferExpr_sound env Γ l τl hl) (inferExpr_sound env Γ r τr hr) h
  | .unaryOp p op e, τ, h => by
      simp only [inferExpr, bind_eq_ok, liftK_eq_ok] at h
      obtain ⟨τe, he, h⟩ := h
      exact .unaryOp (inferExpr_sound env Γ e τe he) h
  | .boolOp p op vs, τ, h => by
      simp only [inferExpr, bind_eq_ok, liftK_eq_ok] at h
      obtain ⟨τs, hs, h⟩ := h
      exact .boolOp (inferExprs_sound env Γ vs τs hs) h
  | .compare p l ops cs, τ, h => by
      simp only [inferExpr, bind_eq_ok, liftK_eq_ok] at h
      obtain ⟨τl, hl, τs, hs, h⟩ := h
      exact .compare (inferExpr_sound env Γ l τl hl) (inferExprs_sound env Γ cs τs hs) h
  | .ifExp p c t e, τ, h => by
      simp only [inferExpr, bind_eq_ok, liftK_eq_ok] at h
      obtain ⟨τc, hc, τt, ht, τe, he, h⟩ := h
      exact .ifExp (inferExpr_sound env Γ c τc hc) (inferExpr_sound env Γ t τt ht)
        (inferExpr_sound env Γ e τe he) h
  | .call p func args kws, τ, h => by
      match kws, func with
      | _ :: _, _ => simp [inferExpr, refuse] at h
      | [], .attribute q recv m =>
          simp only [inferExpr, bind_eq_ok] at h
          obtain ⟨τr, hr, h⟩ := h
          by_cases hm : m = "cast"
          · subst hm
            simp only [ite_true, liftK_eq_ok] at h
            exact .cast (inferExpr_sound env Γ recv τr hr) h
          · simp only [hm, ite_false, bind_eq_ok, liftK_eq_ok] at h
            obtain ⟨τs, hs, h⟩ := h
            exact .method hm (inferExpr_sound env Γ recv τr hr) (inferExprs_sound env Γ args τs hs) h
      | [], .name q f =>
          simp only [inferExpr, bind_eq_ok, liftK_eq_ok] at h
          obtain ⟨τs, hs, h⟩ := h
          exact .callName (inferExprs_sound env Γ args τs hs) h
      | [], .const .. | [], .binOp .. | [], .unaryOp .. | [], .boolOp .. | [], .compare ..
      | [], .ifExp .. | [], .call .. | [], .subscript .. | [], .tuple .. =>
          simp [inferExpr, refuse] at h
  | .attribute p e a, τ, h => by simp [inferExpr, refuse] at h
  | .subscript p a i, τ, h => by
      simp only [inferExpr, bind_eq_ok, liftK_eq_ok] at h
      obtain ⟨τa, ha, τi, hi, h⟩ := h
      exact .subscript (inferExpr_sound env Γ a τa ha) (inferExpr_sound env Γ i τi hi) h
  | .tuple p es, τ, h => by
      simp only [inferExpr, bind_eq_ok, liftK_eq_ok] at h
      obtain ⟨τs, hs, h⟩ := h
      exact .tuple (inferExprs_sound env Γ es τs hs) h

/-- Soundness of `inferExprs`. -/
theorem inferExprs_sound (env : ModEnv) (Γ : Ctx) :
    (es : List PyExpr) → (τs : List PyTy) → inferExprs env Γ es = .ok τs → HasTys env Γ es τs
  | [], τs, h => by
      simp only [inferExprs, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact .nil
  | e :: es, τs, h => by
      simp only [inferExprs, bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨τ, he, τs', hs, rfl⟩ := h
      exact .cons (inferExpr_sound env Γ e τ he) (inferExprs_sound env Γ es τs' hs)

end

mutual

/-- Soundness of `checkStmt`. -/
theorem checkStmt_sound (env : ModEnv) (top : Bool) (Γ : Ctx) :
    (s : PyStmt) → (Γ' : Ctx) → checkStmt env top Γ s = .ok Γ' → StmtOk env top Γ s Γ'
  | .pass p, Γ', h => by
      simp only [checkStmt, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact .pass
  | .expr p v, Γ', h => by
      simp only [checkStmt] at h
      split at h
      · rename_i hd
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact .doc hd
      · exact absurd h refuse_ne_ok
  | .assign p targets v, Γ', h => by
      simp only [checkStmt, bind_eq_ok, liftK_eq_ok] at h
      obtain ⟨τ, hv, h⟩ := h
      exact .assign (inferExpr_sound env Γ v τ hv) h
  | .annAssign p target ann (some v) simple, Γ', h => by
      simp only [checkStmt, bind_eq_ok, liftK_eq_ok] at h
      obtain ⟨τ, hv, h⟩ := h
      exact .annAssign (inferExpr_sound env Γ v τ hv) h
  | .annAssign p target ann none simple, Γ', h => by
      simp only [checkStmt] at h
      exact absurd h refuse_ne_ok
  | .forStmt p target iter body orelse, Γ', h => by
      simp only [checkStmt, bind_eq_ok, liftK_eq_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨Γ₀, h₀, Γb, hb, rfl⟩ := h
      exact .forStmt h₀ (checkStmts_sound env true Γ₀ body Γb hb)
  | .ifStmt p c body orelse, Γ', h => by
      simp only [checkStmt, bind_eq_ok, liftK_eq_ok] at h
      obtain ⟨τ, hc, u, hu, Γ₁, h₁, h₂⟩ := h
      exact .ifStmt (inferExpr_sound env Γ c τ hc) hu (checkStmts_sound env false Γ body Γ₁ h₁)
        (checkStmts_sound env false Γ₁ orelse Γ' h₂)
  | .ret p v, Γ', h => by
      simp only [checkStmt] at h
      exact absurd h refuse_ne_ok
  | .functionDef p n ps body ds r, Γ', h => by
      simp only [checkStmt] at h
      exact absurd h refuse_ne_ok
  | .importFrom p m ns l, Γ', h => by
      simp only [checkStmt] at h
      exact absurd h refuse_ne_ok

/-- Soundness of `checkStmts`. -/
theorem checkStmts_sound (env : ModEnv) (top : Bool) (Γ : Ctx) :
    (ss : List PyStmt) → (Γ' : Ctx) → checkStmts env top Γ ss = .ok Γ' →
      StmtsOk env top Γ ss Γ'
  | [], Γ', h => by
      simp only [checkStmts, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact .nil
  | s :: ss, Γ', h => by
      simp only [checkStmts, bind_eq_ok] at h
      obtain ⟨Γ₁, h₁, h₂⟩ := h
      exact .cons (checkStmt_sound env top Γ s Γ₁ h₁) (checkStmts_sound env top Γ₁ ss Γ' h₂)

end

/-- Soundness of `checkBlock`: a checked block is a complete body. -/
theorem checkBlock_sound (env : ModEnv) (τ : PyTy) (pos : Pos) :
    (Γ : Ctx) → (ss : List PyStmt) → (u : Unit) → checkBlock env τ pos Γ ss = .ok u →
      BodyOk env Γ τ ss
  | Γ, [], u, h => by
      rw [checkBlock] at h
      exact absurd h refuse_ne_ok
  | Γ, s :: rest, u, h => by
      rw [checkBlock.eq_def] at h
      simp only at h
      split at h
      · simp only [bind_eq_ok] at h
        obtain ⟨τe, he, h⟩ := h
        split at h
        · subst_vars
          exact .ret (inferExpr_sound env Γ _ _ he)
        · exact absurd h refuse_ne_ok
      · rename_i p c body orelse
        split at h
        · simp only [bind_eq_ok, liftK_eq_ok] at h
          obtain ⟨τc, hc, uc, hcond, h⟩ := h
          have hc' := inferExpr_sound env Γ c τc hc
          split at h
          · simp only [bind_eq_ok] at h
            obtain ⟨ub, hb, h⟩ := h
            have hb' := checkBlock_sound env τ pos Γ body ub hb
            split at h
            · split at h
              · exact .ifBoth hc' hcond hb' (checkBlock_sound env τ pos Γ orelse u h)
              · exact absurd h refuse_ne_ok
            · simp only [bind_eq_ok] at h
              obtain ⟨Γ₁, h₁, h₂⟩ := h
              exact .ifThen hc' hcond hb' (checkStmts_sound env false Γ orelse Γ₁ h₁)
                (checkBlock_sound env τ pos Γ₁ rest u h₂)
          · simp only [bind_eq_ok] at h
            obtain ⟨Γ₁, h₁, uo, ho, h₂⟩ := h
            exact .ifElse hc' hcond (checkStmts_sound env false Γ body Γ₁ h₁)
              (checkBlock_sound env τ pos Γ orelse uo ho) (checkBlock_sound env τ pos Γ₁ rest u h₂)
        · simp only [bind_eq_ok] at h
          obtain ⟨Γ₁, h₁, h₂⟩ := h
          exact .cons (checkStmt_sound env true Γ _ Γ₁ h₁) (checkBlock_sound env τ pos Γ₁ rest u h₂)
      · simp only [bind_eq_ok] at h
        obtain ⟨Γ₁, h₁, h₂⟩ := h
        exact .cons (checkStmt_sound env true Γ _ Γ₁ h₁) (checkBlock_sound env τ pos Γ₁ _ u h₂)
termination_by _ ss => sizeOf ss

/-- Soundness of `checkBody`: a checked body satisfies `FnOk`. -/
theorem checkBody_sound {env : ModEnv} {Γ₀ : Ctx} {τ : PyTy} {pos : Pos} {body : List PyStmt}
    {u : Unit} (h : checkBody env Γ₀ τ pos body = .ok u) : FnOk env Γ₀ τ body := by
  unfold checkBody at h
  split at h
  · exact checkBlock_sound env τ pos Γ₀ body u h
  · exact absurd h refuse_ne_ok

/-- A checked function definition is well typed. -/
theorem checkFn_wellTyped {env : ModEnv} {pos : Pos} {name : String} {params : List PyArg}
    {body : List PyStmt} {decorators : List PyExpr} {returns : Option PyExpr} {f : CheckedFn}
    (h : checkFn env pos name params body decorators returns = .ok f) : f.WellTyped := by
  unfold checkFn at h
  simp only [bind_eq_ok, liftK_eq_ok] at h
  obtain ⟨sig, -, u, hok, h⟩ := h
  split at h
  · rename_i hl
    simp only [bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨u, hb, rfl⟩ := h
    exact ⟨hok, rfl, fun _ => checkBody_sound hb⟩
  · rename_i hl
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hok, rfl, fun hn => absurd (Option.isNone_iff_eq_none.2 hn) hl⟩

/-- A module-level statement keeps every checked function well typed. -/
theorem checkTopStmt_wellTyped {st st' : ModEnv × List CheckedFn} {s : PyStmt}
    (hst : ∀ f ∈ st.2, f.WellTyped) (h : checkTopStmt st s = .ok st') :
    ∀ f ∈ st'.2, f.WellTyped := by
  match s with
  | .importFrom p m names level =>
      simp only [checkTopStmt, bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨env, -, rfl⟩ := h
      exact hst
  | .annAssign p target ann val simple =>
      simp only [checkTopStmt, bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨env, -, rfl⟩ := h
      exact hst
  | .assign p targets v =>
      simp only [checkTopStmt, bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨env, -, rfl⟩ := h
      exact hst
  | .functionDef p name params body decorators returns =>
      simp only [checkTopStmt, bind_eq_ok, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨f, hf, rfl⟩ := h
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact hst g hg
      · rw [List.mem_singleton.1 hg]
        exact checkFn_wellTyped hf
  | .forStmt .. | .ifStmt .. | .ret .. | .expr .. | .pass .. =>
      simp only [checkTopStmt] at h
      exact absurd h refuse_ne_ok

/-- The module-level statements keep every checked function well typed. -/
theorem checkTop_wellTyped : (st : ModEnv × List CheckedFn) → (ss : List PyStmt) →
    {st' : ModEnv × List CheckedFn} → (∀ f ∈ st.2, f.WellTyped) → checkTop st ss = .ok st' →
      ∀ f ∈ st'.2, f.WellTyped
  | st, [], st', hst, h => by
      simp only [checkTop, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact hst
  | st, s :: ss, st', hst, h => by
      simp only [checkTop, bind_eq_ok] at h
      obtain ⟨st₁, h₁, h₂⟩ := h
      exact checkTop_wellTyped st₁ ss (checkTopStmt_wellTyped hst h₁) h₂

/-- **Soundness of the checker.** A module accepted by `pyCheck` is well
typed: every function whose body is checked satisfies the typing rules
`HasTy`/`StmtsOk` (`FnOk`) in the environment of the definitions before it,
and every function the conditions `fnSigOk` at the call depth of its body. -/
theorem pyCheck_wellTyped {m : PyModule} {cm : CheckedModule} (h : pyCheck m = .ok cm) :
    cm.WellTyped := by
  unfold pyCheck at h
  split at h
  · split at h
    · simp only [bind_eq_ok] at h
      obtain ⟨st, hst, h⟩ := h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact checkTop_wellTyped _ _ (by simp) hst
      · simp at h
    · simp at h
  · simp at h
  · simp at h

end Hax.Py

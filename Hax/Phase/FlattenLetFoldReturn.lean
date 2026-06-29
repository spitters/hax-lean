/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.AST
import Hax.Semantics

/-!
# Untyped twin: `flattenLetFoldReturn` rewrite identities

`Hax/TPhase/FlattenLetFoldReturn.lean` defines the typed render-time
normalisation `tFlattenLetFoldReturn`, built from four `letBind "_"`
rewrites (A/B/C/D — see that file's module docstring). This file
mechanises the *denotation preservation* of each rewrite on the untyped
`ImpExpr` semantics (`Hax.denote`).

## The `"_"` discard convention and its freshness side-condition

`letBind "_" v body` evaluates `v`, binds the result to the slot `"_"`
in the environment, then evaluates `body`. The pipeline uses `"_"` as
the *universal discard binding*: it is never read back (`denote` of a
later `.var "_"` would observe it, but the surface program never emits
one). Two of the four rewrites depend on this:

| # | Rewrite | Side-condition |
|---|---------|----------------|
| **A** | `letBind "_" .unitVal rest ≡ rest` | `"_"` not referenced in `rest` |
| **B** | `letBind "_" (letBind "_" v₁ b₁) b₂ ≡ letBind "_" v₁ (letBind "_" b₁ b₂)` | none |
| **C** | `letBind "_" (ifThenElse c t e) rest ≡ ifThenElse c (letBind "_" t rest) (letBind "_" e rest)` | none |
| **D** | `letBind "_" e rest ≡ seq e rest` | `"_"` not referenced in `rest` |

* **B** and **C** are *unconditional*: both sides bind `"_"` to the same
  value before running the tail, so the two `StateM Env Outcome`
  functions are equal on the nose (`flattenB_denote`, `flattenC_denote`).
* **A** and **D** change the `"_"` slot of the environment (A drops a
  `()` binding; D replaces a `letBind "_"` by `seq`, which does *not*
  bind `"_"`). The resulting `Outcome` is preserved only when `rest`
  never reads `"_"`, and the final environments then agree *except* at
  the `"_"` slot (`flattenA_denote`, `flattenD_denote`). The freshness
  predicate is `noVarRef "_"` and the env equivalence is
  `Env.AgreeExcept "_"`.

The supporting fact is `denote_agreeExcept`: `denote` of a
`noVarRef n`-expression maps `AgreeExcept n`-related inputs to equal
outcomes and `AgreeExcept n`-related outputs.

## Scope

This file proves the four rewrites individually. The *whole pass*
`tFlattenLetFoldReturn` is a `partial def` (its B/C recursions cross the
structural boundary), so Lean exposes no equational lemmas for it and
neither its erase-commutation nor its end-to-end denotation preservation
can be reduced to these identities until it is reformulated as a total
(fuel-bounded) function. See the report in
`Hax/TPhase/FlattenLetFoldReturn.lean`.
-/

namespace Hax

/-! ## Freshness predicate: `n` is never referenced as a variable -/

/-- `noVarRef n e` is `true` iff `e` never references `n` via a `.var n`
    node. Conservative: it also forbids *shadowed* occurrences (a
    `.var n` under a pattern that rebinds `n`), which only strengthens
    the predicate and is sound for the rewrites below. -/
def noVarRef (n : String) : ImpExpr → Bool
  | .var m => m != n
  | .lit _ => true
  | .unitVal => true
  | .continue_ => true
  | .break_ none => true
  | .letBind _ v b => noVarRef n v && noVarRef n b
  | .lam _ b => noVarRef n b
  | .app _ args => allExpr n args
  | .tuple es => allExpr n es
  | .proj e _ => noVarRef n e
  | .ifThenElse c t e => noVarRef n c && noVarRef n t && noVarRef n e
  | .match_ s arms => noVarRef n s && allArms n arms
  | .seq a b => noVarRef n a && noVarRef n b
  | .borrow e => noVarRef n e
  | .deref e => noVarRef n e
  | .assign _ rhs => noVarRef n rhs
  | .forLoop _ lo hi b => noVarRef n lo && noVarRef n hi && noVarRef n b
  | .forLoopRev _ lo hi b => noVarRef n lo && noVarRef n hi && noVarRef n b
  | .whileLoop c b => noVarRef n c && noVarRef n b
  | .break_ (some e) => noVarRef n e
  | .earlyReturn e => noVarRef n e
  | .questionMark e => noVarRef n e
  | .forFold _ lo hi b => noVarRef n lo && noVarRef n hi && noVarRef n b
  | .forFoldRev _ lo hi b => noVarRef n lo && noVarRef n hi && noVarRef n b
  | .whileFold c b => noVarRef n c && noVarRef n b
  | .forFoldReturn _ lo hi b => noVarRef n lo && noVarRef n hi && noVarRef n b
  | .forFoldRevReturn _ lo hi b => noVarRef n lo && noVarRef n hi && noVarRef n b
  | .whileFoldReturn c b => noVarRef n c && noVarRef n b
  | .cfBreak e => noVarRef n e
  | .cfContinue e => noVarRef n e
  | .cfBreakContinue e => noVarRef n e
  | .typeAscription e _ => noVarRef n e
where
  allExpr (n : String) : List ImpExpr → Bool
    | [] => true
    | e :: es => noVarRef n e && allExpr n es
  allArms (n : String) : List (ImpPat × ImpExpr) → Bool
    | [] => true
    | (_, e) :: rest => noVarRef n e && allArms n rest

/-! ## Rewrite B: associativity of discarded binds (unconditional) -/

/-- One-step unfolding of `denote` at a `letBind`, as a `StateM` bind. -/
theorem denote_letBind (bi : Builtins) (fuel : Nat) (n : String) (v b : ImpExpr) :
    denote bi fuel (.letBind n v b)
      = (denote bi fuel v >>= fun rv =>
          match rv with
          | .val w => (modify (Env.extend · n w) >>= fun _ => denote bi fuel b)
          | other => pure other) := by
  simp only [denote]
  rfl

/-- One-step unfolding of `denote` at a `seq`. -/
theorem denote_seq (bi : Builtins) (fuel : Nat) (a b : ImpExpr) :
    denote bi fuel (.seq a b)
      = (denote bi fuel a >>= fun r =>
          match r with
          | .val _ => denote bi fuel b
          | other => pure other) := by
  simp only [denote]
  rfl

/-- **Rewrite B** — discarded-bind associativity. Unconditional: both
    sides evaluate `v₁`, then `b₁`, then `b₂`, binding `"_"` to the same
    values in the same order. -/
theorem flattenB_denote (bi : Builtins) (fuel : Nat) (v₁ b₁ b₂ : ImpExpr) :
    denote bi fuel (.letBind "_" (.letBind "_" v₁ b₁) b₂)
      = denote bi fuel (.letBind "_" v₁ (.letBind "_" b₁ b₂)) := by
  simp only [denote_letBind, bind_assoc]
  congr 1
  funext rv
  cases rv <;> simp only [pure_bind, bind_assoc]

/-! ## Rewrite C: distribute the tail into both `if` branches (unconditional) -/

/-- **Rewrite C** — push the discarded tail into both branches of an
    `ifThenElse`. Unconditional: exactly one branch runs, then the tail,
    binding `"_"` identically on both sides. -/
theorem flattenC_denote (bi : Builtins) (fuel : Nat) (c t e rest : ImpExpr) :
    denote bi fuel (.letBind "_" (.ifThenElse c t e) rest)
      = denote bi fuel (.ifThenElse c (.letBind "_" t rest) (.letBind "_" e rest)) := by
  simp only [denote_letBind, denote, bind_assoc]
  congr 1
  funext rc
  split <;> simp only [pure_bind]

/-! ## Environment equivalence ignoring one slot -/

/-- Two environments agree except possibly at the slot `n`. -/
def Env.AgreeExcept (n : String) (s₁ s₂ : Env) : Prop :=
  ∀ m, m ≠ n → s₁ m = s₂ m

theorem Env.AgreeExcept.rfl' (n : String) (s : Env) : Env.AgreeExcept n s s :=
  fun _ _ => rfl

theorem Env.AgreeExcept.extend {n : String} {s₁ s₂ : Env}
    (h : Env.AgreeExcept n s₁ s₂) (m : String) (v : Value) :
    Env.AgreeExcept n (s₁.extend m v) (s₂.extend m v) := by
  intro k hk
  by_cases hkm : k = m
  · subst hkm; simp only [Env.extend_same]
  · rw [Env.extend_other _ _ _ _ hkm, Env.extend_other _ _ _ _ hkm]; exact h k hk

/-- Extending one side at the ignored slot `n` keeps the envs related. -/
theorem Env.AgreeExcept.extend_left {n : String} {s₁ s₂ : Env}
    (h : Env.AgreeExcept n s₁ s₂) (v : Value) :
    Env.AgreeExcept n (s₁.extend n v) s₂ := by
  intro k hk
  rw [Env.extend_other _ _ _ _ hk]; exact h k hk

/-! ## Pointwise reduction of `denote` applied to an environment -/

theorem stateM_bind_apply {σ α β : Type} (m : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (m >>= f) s = (f (m s).1) (m s).2 := rfl

theorem stateM_pure_apply {σ α : Type} (a : α) (s : σ) :
    (pure a : StateM σ α) s = (a, s) := rfl

theorem stateM_modify_apply {σ : Type} (g : σ → σ) (s : σ) :
    (modify g : StateM σ PUnit) s = (PUnit.unit, g s) := rfl

theorem stateM_get_apply {σ : Type} (s : σ) :
    (get : StateM σ σ) s = (s, s) := rfl

/-! ## The relation transported by `denote`

`Rel n m₁ m₂` says: run on any two `AgreeExcept n`-related states, `m₁`
and `m₂` produce equal results and `AgreeExcept n`-related output states.
`denote` of a `noVarRef n`-expression is `Rel n`-related to itself. -/

/-- The logical relation: equal result, output states still agree except at `n`. -/
def Rel (n : String) {α : Type} (m₁ m₂ : StateM Env α) : Prop :=
  ∀ s₁ s₂, Env.AgreeExcept n s₁ s₂ →
    (m₁ s₁).1 = (m₂ s₂).1 ∧ Env.AgreeExcept n (m₁ s₁).2 (m₂ s₂).2

theorem Rel.pure {n : String} {α : Type} (a : α) : Rel n (pure a) (pure a) := by
  intro s₁ s₂ hs
  refine ⟨rfl, ?_⟩
  exact hs

theorem Rel.bind {n : String} {α β : Type} {m₁ m₂ : StateM Env α}
    {f₁ f₂ : α → StateM Env β}
    (hm : Rel n m₁ m₂) (hf : ∀ o, Rel n (f₁ o) (f₂ o)) :
    Rel n (m₁ >>= f₁) (m₂ >>= f₂) := by
  intro s₁ s₂ hs
  rw [stateM_bind_apply, stateM_bind_apply]
  obtain ⟨ho, hst⟩ := hm s₁ s₂ hs
  rw [ho]
  exact hf (m₂ s₂).1 (m₁ s₁).2 (m₂ s₂).2 hst

theorem stateM_set_apply {σ : Type} (e s : σ) :
    (set e : StateM σ PUnit) s = (PUnit.unit, e) := rfl

/-- `modify`ing both states with the *same* write keeps them related. -/
theorem Rel.modify_extend (n k : String) (w : Value) :
    Rel n (modify (Env.extend · k w)) (modify (Env.extend · k w)) := by
  intro s₁ s₂ hs
  rw [stateM_modify_apply, stateM_modify_apply]
  exact ⟨rfl, hs.extend k w⟩

/-! ## Loop / argument-list / match-arm helper relations -/

theorem denoteForLoop_rel (bi : Builtins) (n var : String) (body : ImpExpr)
    (Hb : ∀ fuel, Rel n (denote bi fuel body) (denote bi fuel body)) :
    ∀ fuel lo hi, Rel n (denoteForLoop bi fuel var lo hi body)
      (denoteForLoop bi fuel var lo hi body) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi
    unfold denoteForLoop
    split
    · exact Rel.pure _
    · split
      · exact Rel.pure _
      · exact absurd rfl ‹_›
  | succ k ih =>
    intro lo hi
    unfold denoteForLoop
    split
    · exact Rel.pure _
    · split
      · exact Rel.pure _
      · apply Rel.bind (Rel.modify_extend n var (.int lo))
        intro _
        apply Rel.bind (Hb (k + 1))
        intro rb
        cases rb <;>
          first
            | (simp only [Nat.add_sub_cancel]; exact ih (lo + 1) hi)
            | exact Rel.pure _

theorem denoteForLoopRev_rel (bi : Builtins) (n var : String) (body : ImpExpr)
    (Hb : ∀ fuel, Rel n (denote bi fuel body) (denote bi fuel body)) :
    ∀ fuel lo hi, Rel n (denoteForLoopRev bi fuel var lo hi body)
      (denoteForLoopRev bi fuel var lo hi body) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi
    unfold denoteForLoopRev
    split
    · exact Rel.pure _
    · split
      · exact Rel.pure _
      · exact absurd rfl ‹_›
  | succ k ih =>
    intro lo hi
    unfold denoteForLoopRev
    split
    · exact Rel.pure _
    · split
      · exact Rel.pure _
      · apply Rel.bind (Rel.modify_extend n var (.int (hi - 1)))
        intro _
        apply Rel.bind (Hb (k + 1))
        intro rb
        cases rb <;>
          first
            | (simp only [Nat.add_sub_cancel]; exact ih lo (hi - 1))
            | exact Rel.pure _

theorem denoteWhile_rel (bi : Builtins) (n : String) (cond body : ImpExpr)
    (Hc : ∀ fuel, Rel n (denote bi fuel cond) (denote bi fuel cond))
    (Hb : ∀ fuel, Rel n (denote bi fuel body) (denote bi fuel body)) :
    ∀ fuel, Rel n (denoteWhile bi fuel cond body) (denoteWhile bi fuel cond body) := by
  intro fuel
  induction fuel with
  | zero =>
    unfold denoteWhile
    split
    · exact Rel.pure _
    · exact absurd rfl ‹_›
  | succ k ih =>
    unfold denoteWhile
    split
    · exact Rel.pure _
    · apply Rel.bind (Hc (k + 1))
      intro rc
      split <;>
        try exact Rel.pure _
      · apply Rel.bind (Hb (k + 1))
        intro rb
        split <;>
          first
            | (simp only [Nat.add_sub_cancel]; exact ih)
            | exact Rel.pure _

theorem denoteArgs_rel (bi : Builtins) (n : String) (fuel : Nat) :
    ∀ (es : List ImpExpr),
      (∀ e ∈ es, Rel n (denote bi fuel e) (denote bi fuel e)) →
      Rel n (denoteArgs bi fuel es) (denoteArgs bi fuel es) := by
  intro es
  induction es with
  | nil => intro _; simp only [denoteArgs]; exact Rel.pure _
  | cons e es ih =>
    intro hall
    simp only [denoteArgs]
    apply Rel.bind (hall e (List.mem_cons_self ..))
    intro r
    cases r <;>
      first
        | (apply Rel.bind (ih (fun e' he' => hall e' (List.mem_cons_of_mem _ he')))
           intro rest
           exact Rel.pure _)
        | exact Rel.pure _

/-! ## `matchPat` is insensitive to the ignored slot -/

/-- Two `Option Env` results agree: both `none`, or both `some` with
    `AgreeExcept n`-related environments. -/
def OptAgree (n : String) : Option Env → Option Env → Prop
  | some e₁, some e₂ => Env.AgreeExcept n e₁ e₂
  | none, none => True
  | _, _ => False

/-- Pattern matching only *extends* the environment (its success and the
    added bindings depend on the pattern and value, not on the env's
    existing contents), so it maps `AgreeExcept n`-related envs to
    `OptAgree n`-related results. -/
theorem matchPat_agree (n : String) (pat : ImpPat) (v : Value) (e₁ : Env) :
    ∀ e₂, Env.AgreeExcept n e₁ e₂ → OptAgree n (matchPat pat v e₁) (matchPat pat v e₂) := by
  induction pat, v, e₁ using matchPat.induct (motive_1 := fun pats vs e₁ =>
      ∀ e₂, Env.AgreeExcept n e₁ e₂ →
        OptAgree n (matchPat.matchPatList pats vs e₁) (matchPat.matchPatList pats vs e₂)) with
  | case6 pats vs env hlen ih1 => intro e₂ hs; simp only [matchPat, hlen]; exact ih1 e₂ hs
  | case8 pats vs env hlen ih1 => intro e₂ hs; simp only [matchPat, hlen]; exact ih1 e₂ hs
  | case9 p v env ih2 => intro e₂ hs; simp only [matchPat]; exact ih2 e₂ hs
  | case11 p v env ih2 => intro e₂ hs; simp only [matchPat]; exact ih2 e₂ hs
  | case12 p v env ih2 => intro e₂ hs; simp only [matchPat]; exact ih2 e₂ hs
  | case15 p ps v vs env ih2 ih1 =>
      rename_i e₂ hs
      have h2 := ih2 e₂ hs
      simp only [matchPat.matchPatList]
      cases hp1 : matchPat p v env <;> cases hp2 : matchPat p v e₂ <;>
        simp only [hp1, hp2, OptAgree] at h2 ⊢ <;>
        first | exact h2.elim | trivial | exact ih1 _ _ h2
  | case16 t x env h1 h2 =>
      rename_i e₂ hs
      cases t <;> cases x <;> simp_all [matchPat.matchPatList, OptAgree]
  | _ =>
      intros <;>
        simp_all [matchPat, matchPat.matchPatList, OptAgree, Env.AgreeExcept, Env.extend]

theorem denoteMatchArms_rel (bi : Builtins) (n : String) (fuel : Nat) (v : Value) :
    ∀ (arms : List (ImpPat × ImpExpr)),
      (∀ pa ∈ arms, Rel n (denote bi fuel pa.2) (denote bi fuel pa.2)) →
      Rel n (denoteMatchArms bi fuel v arms) (denoteMatchArms bi fuel v arms) := by
  intro arms
  induction arms with
  | nil => intro _; simp only [denoteMatchArms]; exact Rel.pure _
  | cons pa rest ih =>
    obtain ⟨pat, body⟩ := pa
    intro hall s₁ s₂ hs
    simp only [denoteMatchArms, stateM_bind_apply, stateM_get_apply]
    have hmp := matchPat_agree n pat v s₁ s₂ hs
    cases hp1 : matchPat pat v s₁ <;> cases hp2 : matchPat pat v s₂ <;>
      simp only [hp1, hp2, OptAgree] at hmp
    · -- both `none`: fall through to the remaining arms
      exact ih (fun pa' hpa' => hall pa' (List.mem_cons_of_mem _ hpa')) s₁ s₂ hs
    · -- both matched: `set` the matched envs and denote the body
      simp only [stateM_bind_apply, stateM_set_apply]
      exact hall (pat, body) (List.mem_cons_self ..) _ _ hmp

/-- Reading a variable `m ≠ n` is insensitive to the slot `n`. -/
theorem Rel.var (bi : Builtins) (fuel : Nat) (n m : String) (h : m ≠ n) :
    Rel n (denote bi fuel (.var m)) (denote bi fuel (.var m)) := by
  intro s₁ s₂ hs
  simp only [denote, stateM_bind_apply, stateM_get_apply]
  rw [hs m h]
  cases s₂ m <;> exact ⟨rfl, hs⟩

theorem noVarRef_allExpr_mem {n : String} {args : List ImpExpr}
    (h : noVarRef.allExpr n args = true) : ∀ a ∈ args, noVarRef n a = true := by
  induction args with
  | nil => intro a ha; cases ha
  | cons e es ih =>
    simp only [noVarRef.allExpr, Bool.and_eq_true] at h
    intro a ha
    cases ha with
    | head => exact h.1
    | tail _ ht => exact ih h.2 a ht

theorem noVarRef_allArms_mem {n : String} {arms : List (ImpPat × ImpExpr)}
    (h : noVarRef.allArms n arms = true) : ∀ pa ∈ arms, noVarRef n pa.2 = true := by
  induction arms with
  | nil => intro pa ha; cases ha
  | cons pa rest ih =>
    obtain ⟨p, e⟩ := pa
    simp only [noVarRef.allArms, Bool.and_eq_true] at h
    intro qa hqa
    cases hqa with
    | head => exact h.1
    | tail _ ht => exact ih h.2 qa ht

/-! ## Main congruence: `denote` is insensitive to the ignored slot -/

/-- If `n` is never read by `e` (`noVarRef n e`), then `denote bi fuel e`
    maps `AgreeExcept n`-related states to equal outcomes and
    `AgreeExcept n`-related output states. -/
theorem denote_agreeExcept (bi : Builtins) (n : String) (e : ImpExpr) :
    ∀ fuel, noVarRef n e = true → Rel n (denote bi fuel e) (denote bi fuel e) := by
  induction e using ImpExpr.ind with
  | lit => intro fuel _; simp only [denote]; exact Rel.pure _
  | var m => intro fuel h; simp only [noVarRef, bne_iff_ne, ne_eq] at h; exact Rel.var bi fuel n m h
  | unitVal => intro fuel _; simp only [denote]; exact Rel.pure _
  | continue_ => intro fuel _; simp only [denote]; exact Rel.pure _
  | break_none => intro fuel _; simp only [denote]; exact Rel.pure _
  | break_some e ih =>
    intro fuel h; simp only [noVarRef] at h; simp only [denote]
    apply Rel.bind (ih fuel h); intro r; split <;> exact Rel.pure _
  | earlyReturn e ih =>
    intro fuel h; simp only [noVarRef] at h; simp only [denote]
    apply Rel.bind (ih fuel h); intro r; split <;> exact Rel.pure _
  | questionMark e ih =>
    intro fuel h; simp only [noVarRef] at h; simp only [denote]
    apply Rel.bind (ih fuel h); intro r; split <;> exact Rel.pure _
  | proj e i ih =>
    intro fuel h; simp only [noVarRef] at h; simp only [denote]
    apply Rel.bind (ih fuel h); intro r; split <;> (try split) <;> exact Rel.pure _
  | borrow e ih => intro fuel h; simp only [noVarRef] at h; simp only [denote]; exact ih fuel h
  | deref e ih => intro fuel h; simp only [noVarRef] at h; simp only [denote]; exact ih fuel h
  | typeAscription e s ih =>
    intro fuel h; simp only [noVarRef] at h; simp only [denote]; exact ih fuel h
  | assign name rhs ih =>
    intro fuel h; simp only [noVarRef] at h; simp only [denote]
    apply Rel.bind (ih fuel h); intro r
    cases r <;>
      first
        | (apply Rel.bind (Rel.modify_extend n name _); intro _; exact Rel.pure _)
        | exact Rel.pure _
  | letBind name v b ih1 ih2 =>
    intro fuel h
    simp only [noVarRef, Bool.and_eq_true] at h
    simp only [denote]
    apply Rel.bind (ih1 fuel h.1); intro rv
    cases rv <;>
      first
        | (apply Rel.bind (Rel.modify_extend n name _); intro _; exact ih2 fuel h.2)
        | exact Rel.pure _
  | seq a b ih1 ih2 =>
    intro fuel h
    simp only [noVarRef, Bool.and_eq_true] at h
    simp only [denote]
    apply Rel.bind (ih1 fuel h.1); intro r
    split <;> first | exact ih2 fuel h.2 | exact Rel.pure _
  | ifThenElse c t e ih1 ih2 ih3 =>
    intro fuel h
    simp only [noVarRef, Bool.and_eq_true] at h
    obtain ⟨⟨hc, ht⟩, he⟩ := h
    simp only [denote]
    apply Rel.bind (ih1 fuel hc); intro rc
    split <;> first | exact ih2 fuel ht | exact ih3 fuel he | exact Rel.pure _
  | app f args ih =>
    intro fuel h
    simp only [noVarRef] at h
    simp only [denote]
    apply Rel.bind (denoteArgs_rel bi n fuel args
      (fun a ha => ih a ha fuel (noVarRef_allExpr_mem h a ha)))
    intro mvals
    split <;> (try split) <;> exact Rel.pure _
  | tuple elems ih =>
    intro fuel h
    simp only [noVarRef] at h
    simp only [denote]
    apply Rel.bind (denoteArgs_rel bi n fuel elems
      (fun a ha => ih a ha fuel (noVarRef_allExpr_mem h a ha)))
    intro mvals
    split <;> exact Rel.pure _
  | match_ scrut arms ih1 ih2 =>
    intro fuel h
    simp only [noVarRef, Bool.and_eq_true] at h
    simp only [denote]
    apply Rel.bind (ih1 fuel h.1); intro rs
    split
    · exact denoteMatchArms_rel bi n fuel _ arms
        (fun pa hpa => ih2 pa hpa fuel (noVarRef_allArms_mem h.2 pa hpa))
    · exact Rel.pure _
  | forLoop var lo hi body ih1 ih2 ih3 =>
    intro fuel h
    simp only [noVarRef, Bool.and_eq_true] at h
    obtain ⟨⟨hlo, hhi⟩, hbody⟩ := h
    simp only [denote]
    apply Rel.bind (ih1 fuel hlo); intro rlo
    apply Rel.bind (ih2 fuel hhi); intro rhi
    split <;>
      first
        | exact denoteForLoop_rel bi n var body (fun f => ih3 f hbody) _ _ _
        | exact Rel.pure _
  | forLoopRev var lo hi body ih1 ih2 ih3 =>
    intro fuel h
    simp only [noVarRef, Bool.and_eq_true] at h
    obtain ⟨⟨hlo, hhi⟩, hbody⟩ := h
    simp only [denote]
    apply Rel.bind (ih1 fuel hlo); intro rlo
    apply Rel.bind (ih2 fuel hhi); intro rhi
    split <;>
      first
        | exact denoteForLoopRev_rel bi n var body (fun f => ih3 f hbody) _ _ _
        | exact Rel.pure _
  | whileLoop c body ih1 ih2 =>
    intro fuel h
    simp only [noVarRef, Bool.and_eq_true] at h
    simp only [denote]
    exact denoteWhile_rel bi n c body (fun f => ih1 f h.1) (fun f => ih2 f h.2) fuel
  | lam params body _ => intro fuel _; simp only [denote]; exact Rel.pure _
  | forFold v lo hi body _ _ _ => intro fuel _; simp only [denote]; exact Rel.pure _
  | forFoldRev v lo hi body _ _ _ => intro fuel _; simp only [denote]; exact Rel.pure _
  | whileFold c body _ _ => intro fuel _; simp only [denote]; exact Rel.pure _
  | forFoldReturn v lo hi body _ _ _ => intro fuel _; simp only [denote]; exact Rel.pure _
  | forFoldRevReturn v lo hi body _ _ _ => intro fuel _; simp only [denote]; exact Rel.pure _
  | whileFoldReturn c body _ _ => intro fuel _; simp only [denote]; exact Rel.pure _
  | cfBreak e _ => intro fuel _; simp only [denote]; exact Rel.pure _
  | cfContinue e _ => intro fuel _; simp only [denote]; exact Rel.pure _
  | cfBreakContinue e _ => intro fuel _; simp only [denote]; exact Rel.pure _

/-! ## Rewrites A and D (conditional on `"_"`-freshness of the tail)

These two rewrites change the `"_"` slot of the environment, so they are
denotation-preserving only when the tail `rest` never reads `"_"`. The
statements fix the initial state and conclude: equal outcome, and output
states agreeing except at `"_"` — exactly what the post-pipeline renderer
needs, since downstream never reads `"_"`. -/

/-- **Rewrite A** — discarding `()` is a no-op, provided `rest` does not
    read `"_"`. -/
theorem flattenA_denote (bi : Builtins) (fuel : Nat) (rest : ImpExpr)
    (hrest : noVarRef "_" rest = true) (s : Env) :
    (denote bi fuel (.letBind "_" .unitVal rest) s).1 = (denote bi fuel rest s).1 ∧
    Env.AgreeExcept "_" (denote bi fuel (.letBind "_" .unitVal rest) s).2
      (denote bi fuel rest s).2 := by
  rw [denote_letBind, stateM_bind_apply]
  simp only [denote, stateM_pure_apply, stateM_bind_apply, stateM_modify_apply]
  exact denote_agreeExcept bi "_" rest fuel hrest _ _
    (Env.AgreeExcept.extend_left (Env.AgreeExcept.rfl' "_" s) .unit)

/-- **Rewrite D** — replace a discarded `letBind "_"` by `seq` (which does
    not bind `"_"`), provided `rest` does not read `"_"`. -/
theorem flattenD_denote (bi : Builtins) (fuel : Nat) (e rest : ImpExpr)
    (hrest : noVarRef "_" rest = true) (s : Env) :
    (denote bi fuel (.letBind "_" e rest) s).1 = (denote bi fuel (.seq e rest) s).1 ∧
    Env.AgreeExcept "_" (denote bi fuel (.letBind "_" e rest) s).2
      (denote bi fuel (.seq e rest) s).2 := by
  rw [denote_letBind, denote_seq, stateM_bind_apply, stateM_bind_apply]
  cases ho : (denote bi fuel e s).1 with
  | val w =>
    simp only [stateM_bind_apply, stateM_modify_apply]
    exact denote_agreeExcept bi "_" rest fuel hrest _ _
      (Env.AgreeExcept.extend_left (Env.AgreeExcept.rfl' "_" _) w)
  | earlyRet w => exact ⟨rfl, Env.AgreeExcept.rfl' _ _⟩
  | broke w => exact ⟨rfl, Env.AgreeExcept.rfl' _ _⟩
  | continued => exact ⟨rfl, Env.AgreeExcept.rfl' _ _⟩
  | err m => exact ⟨rfl, Env.AgreeExcept.rfl' _ _⟩

end Hax

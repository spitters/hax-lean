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

This file proves the four rewrites individually, then provides the
**total** `fuel`-bounded twin `flattenLetFoldReturn : Nat → ImpExpr →
ImpExpr` of the (now also total) typed pass `tFlattenLetFoldReturn`, plus
the composable infrastructure for the whole-pass result: `Rel "_"` as a
partial equivalence (`Rel.symm`/`Rel.trans`/`Rel.bind`) and the
two-environment forms of A and D (`flattenA_rel`, `flattenD_rel`).

The end-to-end statement `flattenLetFoldReturn_denote`,
`noVarRef "_" e → Rel "_" (denote (flattenLetFoldReturn k e)) (denote e)`,
is **proved**: a heterogeneous structural congruence (relating each
`denote`-helper on the flattened subterms to the original, via
`flatten_noVarRef` and the `*_rel_het` helpers) composed with the four
rewrite identities through the `Rel` partial equivalence. See the report
in `Hax/TPhase/FlattenLetFoldReturn.lean`.
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

/-! ## `Rel` is a partial equivalence; two-env forms of A and D

The whole-pass composition needs `Rel` as a (symmetric, transitive)
relation and the A/D rewrites in *two-environment* form (so they compose
with the structural congruence). The two-env forms hold once *both* the
discarded value and the tail are `"_"`-fresh — which is the case under a
whole-program `noVarRef "_"` invariant. -/

theorem Env.AgreeExcept.symm {n : String} {s₁ s₂ : Env}
    (h : Env.AgreeExcept n s₁ s₂) : Env.AgreeExcept n s₂ s₁ :=
  fun m hm => (h m hm).symm

theorem Env.AgreeExcept.trans {n : String} {s₁ s₂ s₃ : Env}
    (h₁ : Env.AgreeExcept n s₁ s₂) (h₂ : Env.AgreeExcept n s₂ s₃) :
    Env.AgreeExcept n s₁ s₃ :=
  fun m hm => (h₁ m hm).trans (h₂ m hm)

theorem Rel.symm {n : String} {α : Type} {m₁ m₂ : StateM Env α}
    (h : Rel n m₁ m₂) : Rel n m₂ m₁ := by
  intro s₁ s₂ hs
  obtain ⟨ho, hst⟩ := h s₂ s₁ hs.symm
  exact ⟨ho.symm, hst.symm⟩

theorem Rel.trans {n : String} {α : Type} {a b c : StateM Env α}
    (hab : Rel n a b) (hbc : Rel n b c) : Rel n a c := by
  intro s₁ s₃ hs
  obtain ⟨ho₁, hst₁⟩ := hab s₁ s₁ (Env.AgreeExcept.rfl' n s₁)
  obtain ⟨ho₂, hst₂⟩ := hbc s₁ s₃ hs
  exact ⟨ho₁.trans ho₂, hst₁.trans hst₂⟩

/-- **Rewrite A**, two-environment form: under `noVarRef "_" rest`, the
    discarded `()`-bind and `rest` are `Rel "_"`-related. -/
theorem flattenA_rel (bi : Builtins) (fuel : Nat) (rest : ImpExpr)
    (hrest : noVarRef "_" rest = true) :
    Rel "_" (denote bi fuel (.letBind "_" .unitVal rest)) (denote bi fuel rest) := by
  intro s₁ s₂ hs
  rw [denote_letBind, stateM_bind_apply]
  simp only [denote, stateM_pure_apply, stateM_bind_apply, stateM_modify_apply]
  exact denote_agreeExcept bi "_" rest fuel hrest _ _
    (Env.AgreeExcept.extend_left hs .unit)

/-- **Rewrite D**, two-environment form: under `noVarRef "_" e` and
    `noVarRef "_" rest`, the discarded `letBind "_"` and `seq` are
    `Rel "_"`-related. -/
theorem flattenD_rel (bi : Builtins) (fuel : Nat) (e rest : ImpExpr)
    (he : noVarRef "_" e = true) (hrest : noVarRef "_" rest = true) :
    Rel "_" (denote bi fuel (.letBind "_" e rest)) (denote bi fuel (.seq e rest)) := by
  intro s₁ s₂ hs
  rw [denote_letBind, denote_seq, stateM_bind_apply, stateM_bind_apply]
  obtain ⟨ho, hst⟩ := denote_agreeExcept bi "_" e fuel he s₁ s₂ hs
  rw [ho]
  cases hw : (denote bi fuel e s₂).1 with
  | val w =>
    simp only [stateM_bind_apply, stateM_modify_apply]
    exact denote_agreeExcept bi "_" rest fuel hrest _ _
      (Env.AgreeExcept.extend_left hst w)
  | earlyRet w => exact ⟨rfl, hst⟩
  | broke w => exact ⟨rfl, hst⟩
  | continued => exact ⟨rfl, hst⟩
  | err m => exact ⟨rfl, hst⟩

/-- Structural node count (compilable; the derived `sizeOf` instance has
    no LCNF signature for these ASTs). Used to size the flattening fuel. -/
def ImpExpr.nodeCount : ImpExpr → Nat
  | .lit _ => 1
  | .var _ => 1
  | .unitVal => 1
  | .continue_ => 1
  | .break_ none => 1
  | .break_ (some e) => 1 + e.nodeCount
  | .letBind _ v b => 1 + v.nodeCount + b.nodeCount
  | .lam _ b => 1 + b.nodeCount
  | .app _ args => 1 + nodeCountList args
  | .tuple es => 1 + nodeCountList es
  | .proj e _ => 1 + e.nodeCount
  | .ifThenElse c t e => 1 + c.nodeCount + t.nodeCount + e.nodeCount
  | .match_ s arms => 1 + s.nodeCount + nodeCountArms arms
  | .seq a b => 1 + a.nodeCount + b.nodeCount
  | .borrow e => 1 + e.nodeCount
  | .deref e => 1 + e.nodeCount
  | .assign _ r => 1 + r.nodeCount
  | .forLoop _ lo hi b => 1 + lo.nodeCount + hi.nodeCount + b.nodeCount
  | .forLoopRev _ lo hi b => 1 + lo.nodeCount + hi.nodeCount + b.nodeCount
  | .whileLoop c b => 1 + c.nodeCount + b.nodeCount
  | .earlyReturn e => 1 + e.nodeCount
  | .questionMark e => 1 + e.nodeCount
  | .forFold _ lo hi b => 1 + lo.nodeCount + hi.nodeCount + b.nodeCount
  | .forFoldRev _ lo hi b => 1 + lo.nodeCount + hi.nodeCount + b.nodeCount
  | .whileFold c b => 1 + c.nodeCount + b.nodeCount
  | .forFoldReturn _ lo hi b => 1 + lo.nodeCount + hi.nodeCount + b.nodeCount
  | .forFoldRevReturn _ lo hi b => 1 + lo.nodeCount + hi.nodeCount + b.nodeCount
  | .whileFoldReturn c b => 1 + c.nodeCount + b.nodeCount
  | .cfBreak e => 1 + e.nodeCount
  | .cfContinue e => 1 + e.nodeCount
  | .cfBreakContinue e => 1 + e.nodeCount
  | .typeAscription e _ => 1 + e.nodeCount
where
  nodeCountList : List ImpExpr → Nat
    | [] => 0
    | e :: es => e.nodeCount + nodeCountList es
  nodeCountArms : List (ImpPat × ImpExpr) → Nat
    | [] => 0
    | (_, e) :: rest => e.nodeCount + nodeCountArms rest

/-! ## Total, fuel-bounded untyped twin of `tFlattenLetFoldReturn`

The typed pass is reformulated as a total `fuel`-bounded function (no
`partial`): every recursive call decrements `fuel`, and `fuel = 0`
returns the input unchanged. This file's untyped twin mirrors the typed
pass on the erased AST, enabling the erase-commutation lemma and the
end-to-end denotation-preservation. With `fuel` larger than the (finite)
recursion depth the partial version uses, the output is unchanged. -/

/-- Detect, at the body surface, a function-level early-return (`cfBreak`).
    Stops at inner loop bodies (their `cfBreak`s belong to them). -/
def bodyHasSurfaceCfBreak : ImpExpr → Bool
  | .cfBreak _ => true
  | .ifThenElse _ t e => bodyHasSurfaceCfBreak t || bodyHasSurfaceCfBreak e
  | .letBind _ _ b => bodyHasSurfaceCfBreak b
  | .seq a b => bodyHasSurfaceCfBreak a || bodyHasSurfaceCfBreak b
  | .match_ _ arms => bodyAnyArms arms
  | .forFold _ _ _ _ | .forFoldRev _ _ _ _ | .forFoldReturn _ _ _ _
  | .forFoldRevReturn _ _ _ _ | .whileFold _ _ | .whileFoldReturn _ _ => false
  | _ => false
where
  bodyAnyArms : List (ImpPat × ImpExpr) → Bool
    | [] => false
    | (_, b) :: rest => bodyHasSurfaceCfBreak b || bodyAnyArms rest

/-- Whether `e` contains a `*FoldReturn` whose body has a surface
    function-return. Mirrors the typed `tHasNestedFoldWithReturn`. -/
def hasNestedFoldWithReturn : ImpExpr → Bool
  | .forFoldReturn _ _ _ b => bodyHasSurfaceCfBreak b || hasNestedFoldWithReturn b
  | .forFoldRevReturn _ _ _ b => bodyHasSurfaceCfBreak b || hasNestedFoldWithReturn b
  | .whileFoldReturn _ b => bodyHasSurfaceCfBreak b || hasNestedFoldWithReturn b
  | .letBind _ v body => hasNestedFoldWithReturn v || hasNestedFoldWithReturn body
  | .seq a b => hasNestedFoldWithReturn a || hasNestedFoldWithReturn b
  | .ifThenElse _ t e => hasNestedFoldWithReturn t || hasNestedFoldWithReturn e
  | .match_ _ arms => nestedAnyArms arms
  | _ => false
where
  nestedAnyArms : List (ImpPat × ImpExpr) → Bool
    | [] => false
    | (_, b) :: rest => hasNestedFoldWithReturn b || nestedAnyArms rest

/-- Total, fuel-bounded flattening pass on the untyped AST. Mirrors the
    typed `tFlattenLetFoldReturn` on erased expressions: rules A/B/C/D at
    each discarded `letBind "_"`, plus the seq-if distribution (C′). -/
def flattenLetFoldReturn : Nat → ImpExpr → ImpExpr
  | 0, e => e
  | _ + 1, .lit v => .lit v
  | _ + 1, .var n => .var n
  | _ + 1, .unitVal => .unitVal
  | _ + 1, .continue_ => .continue_
  | _ + 1, .break_ none => .break_ none
  | fuel + 1, .break_ (some e) => .break_ (some (flattenLetFoldReturn fuel e))
  | fuel + 1, .lam ps body => .lam ps (flattenLetFoldReturn fuel body)
  | fuel + 1, .app f args => .app f (args.map (flattenLetFoldReturn fuel))
  | fuel + 1, .tuple es => .tuple (es.map (flattenLetFoldReturn fuel))
  | fuel + 1, .proj e i => .proj (flattenLetFoldReturn fuel e) i
  | fuel + 1, .ifThenElse c t e =>
      .ifThenElse (flattenLetFoldReturn fuel c) (flattenLetFoldReturn fuel t)
        (flattenLetFoldReturn fuel e)
  | fuel + 1, .match_ scrut arms =>
      .match_ (flattenLetFoldReturn fuel scrut)
        (arms.map (fun pe => (pe.1, flattenLetFoldReturn fuel pe.2)))
  | fuel + 1, .seq a b =>
      let a' := flattenLetFoldReturn fuel a
      let b' := flattenLetFoldReturn fuel b
      match a' with
      | .ifThenElse c t e =>
        if hasNestedFoldWithReturn t || hasNestedFoldWithReturn e then
          .ifThenElse c (flattenLetFoldReturn fuel (.seq t b'))
            (flattenLetFoldReturn fuel (.seq e b'))
        else .seq a' b'
      | _ => .seq a' b'
  | fuel + 1, .borrow e => .borrow (flattenLetFoldReturn fuel e)
  | fuel + 1, .deref e => .deref (flattenLetFoldReturn fuel e)
  | fuel + 1, .assign n rhs => .assign n (flattenLetFoldReturn fuel rhs)
  | fuel + 1, .forLoop v lo hi body =>
      .forLoop v (flattenLetFoldReturn fuel lo) (flattenLetFoldReturn fuel hi)
        (flattenLetFoldReturn fuel body)
  | fuel + 1, .forLoopRev v lo hi body =>
      .forLoopRev v (flattenLetFoldReturn fuel lo) (flattenLetFoldReturn fuel hi)
        (flattenLetFoldReturn fuel body)
  | fuel + 1, .whileLoop c body =>
      .whileLoop (flattenLetFoldReturn fuel c) (flattenLetFoldReturn fuel body)
  | fuel + 1, .earlyReturn e => .earlyReturn (flattenLetFoldReturn fuel e)
  | fuel + 1, .questionMark e => .questionMark (flattenLetFoldReturn fuel e)
  | fuel + 1, .forFold v lo hi body =>
      .forFold v (flattenLetFoldReturn fuel lo) (flattenLetFoldReturn fuel hi)
        (flattenLetFoldReturn fuel body)
  | fuel + 1, .forFoldRev v lo hi body =>
      .forFoldRev v (flattenLetFoldReturn fuel lo) (flattenLetFoldReturn fuel hi)
        (flattenLetFoldReturn fuel body)
  | fuel + 1, .whileFold c body =>
      .whileFold (flattenLetFoldReturn fuel c) (flattenLetFoldReturn fuel body)
  | fuel + 1, .forFoldReturn v lo hi body =>
      .forFoldReturn v (flattenLetFoldReturn fuel lo) (flattenLetFoldReturn fuel hi)
        (flattenLetFoldReturn fuel body)
  | fuel + 1, .forFoldRevReturn v lo hi body =>
      .forFoldRevReturn v (flattenLetFoldReturn fuel lo) (flattenLetFoldReturn fuel hi)
        (flattenLetFoldReturn fuel body)
  | fuel + 1, .whileFoldReturn c body =>
      .whileFoldReturn (flattenLetFoldReturn fuel c) (flattenLetFoldReturn fuel body)
  | fuel + 1, .cfBreak e => .cfBreak (flattenLetFoldReturn fuel e)
  | fuel + 1, .cfContinue e => .cfContinue (flattenLetFoldReturn fuel e)
  | fuel + 1, .cfBreakContinue e => .cfBreakContinue (flattenLetFoldReturn fuel e)
  | fuel + 1, .typeAscription e ty => .typeAscription (flattenLetFoldReturn fuel e) ty
  | fuel + 1, .letBind n val body =>
      let val' := flattenLetFoldReturn fuel val
      let body' := flattenLetFoldReturn fuel body
      if n == "_" then
        match val' with
        | .unitVal => body'
        | .forFoldReturn v lo hi b => .seq (.forFoldReturn v lo hi b) body'
        | .forFoldRevReturn v lo hi b => .seq (.forFoldRevReturn v lo hi b) body'
        | .whileFoldReturn c b => .seq (.whileFoldReturn c b) body'
        | .letBind "_" innerVal innerBody =>
          flattenLetFoldReturn fuel (.letBind "_" innerVal (.letBind "_" innerBody body'))
        | .seq innerA innerB =>
          flattenLetFoldReturn fuel (.letBind "_" innerA (.letBind "_" innerB body'))
        | .ifThenElse c t e =>
          if hasNestedFoldWithReturn t || hasNestedFoldWithReturn e then
            .ifThenElse c (flattenLetFoldReturn fuel (.letBind "_" t body'))
              (flattenLetFoldReturn fuel (.letBind "_" e body'))
          else .letBind n val' body'
        | _ => .letBind n val' body'
      else .letBind n val' body'

/-! ## The flattening pass preserves `"_"`-freshness

`flattenLetFoldReturn` only rearranges discarded binds; it never
introduces a `.var "_"`. So the whole-program invariant `noVarRef "_"` is
preserved, which is the side-condition under which rewrites A/D (hence
the whole pass) are denotation-preserving. -/

theorem allExpr_map_flatten (k : Nat)
    (ih : ∀ a, noVarRef "_" a = true → noVarRef "_" (flattenLetFoldReturn k a) = true) :
    ∀ args, noVarRef.allExpr "_" args = true →
      noVarRef.allExpr "_" (args.map (flattenLetFoldReturn k)) = true := by
  intro args
  induction args with
  | nil => intro _; rfl
  | cons a as iha =>
    intro h
    simp only [noVarRef.allExpr, Bool.and_eq_true] at h
    simp only [List.map_cons, noVarRef.allExpr, Bool.and_eq_true]
    exact ⟨ih a h.1, iha h.2⟩

theorem allArms_map_flatten (k : Nat)
    (ih : ∀ a, noVarRef "_" a = true → noVarRef "_" (flattenLetFoldReturn k a) = true) :
    ∀ arms, noVarRef.allArms "_" arms = true →
      noVarRef.allArms "_" (arms.map (fun pe => (pe.1, flattenLetFoldReturn k pe.2))) = true := by
  intro arms
  induction arms with
  | nil => intro _; rfl
  | cons pa as iha =>
    obtain ⟨p, e⟩ := pa
    intro h
    simp only [noVarRef.allArms, Bool.and_eq_true] at h
    simp only [List.map_cons, noVarRef.allArms, Bool.and_eq_true]
    exact ⟨ih e h.1, iha h.2⟩

/-- `flattenLetFoldReturn` preserves the `noVarRef "_"` invariant. -/
theorem flatten_noVarRef :
    ∀ (k : Nat) (e : ImpExpr), noVarRef "_" e = true →
      noVarRef "_" (flattenLetFoldReturn k e) = true := by
  intro k
  induction k with
  | zero => intro e he; simpa only [flattenLetFoldReturn] using he
  | succ k ih =>
    intro e
    induction e using ImpExpr.ind with
    | lit | var | unitVal | continue_ | break_none =>
      intro he; simpa only [flattenLetFoldReturn] using he
    | break_some e _ | borrow e _ | deref e _ | earlyReturn e _ | questionMark e _
    | cfBreak e _ | cfContinue e _ | cfBreakContinue e _ =>
      intro he; simp only [flattenLetFoldReturn, noVarRef] at he ⊢; exact ih _ he
    | proj e i _ | lam _ e _ | assign _ e _ | typeAscription e _ _ =>
      intro he; simp only [flattenLetFoldReturn, noVarRef] at he ⊢; exact ih _ he
    | app f args _ | tuple args _ =>
      intro he; simp only [flattenLetFoldReturn, noVarRef] at he ⊢
      exact allExpr_map_flatten k ih _ he
    | match_ scrut arms _ _ =>
      intro he; simp only [flattenLetFoldReturn, noVarRef, Bool.and_eq_true] at he ⊢
      exact ⟨ih _ he.1, allArms_map_flatten k ih _ he.2⟩
    | ifThenElse c t e _ _ _ =>
      intro he; simp only [flattenLetFoldReturn, noVarRef, Bool.and_eq_true] at he ⊢
      exact ⟨⟨ih _ he.1.1, ih _ he.1.2⟩, ih _ he.2⟩
    | forLoop _ lo hi body _ _ _ | forLoopRev _ lo hi body _ _ _
    | forFold _ lo hi body _ _ _ | forFoldRev _ lo hi body _ _ _
    | forFoldReturn _ lo hi body _ _ _ | forFoldRevReturn _ lo hi body _ _ _ =>
      intro he; simp only [flattenLetFoldReturn, noVarRef, Bool.and_eq_true] at he ⊢
      exact ⟨⟨ih _ he.1.1, ih _ he.1.2⟩, ih _ he.2⟩
    | whileLoop c body _ _ | whileFold c body _ _ | whileFoldReturn c body _ _ =>
      intro he; simp only [flattenLetFoldReturn, noVarRef, Bool.and_eq_true] at he ⊢
      exact ⟨ih _ he.1, ih _ he.2⟩
    | seq a b _ _ =>
      intro he
      simp only [noVarRef, Bool.and_eq_true] at he
      obtain ⟨ha, hb⟩ := he
      have hfa := ih a ha
      have hfb := ih b hb
      simp only [flattenLetFoldReturn]
      split
      · next c t e heq =>
        have hfa' := hfa; rw [heq] at hfa'; simp only [noVarRef, Bool.and_eq_true] at hfa'
        split
        · simp only [noVarRef, Bool.and_eq_true]
          exact ⟨⟨hfa'.1.1, ih _ (by simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfa'.1.2, hfb⟩)⟩,
                 ih _ (by simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfa'.2, hfb⟩)⟩
        · simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfa, hfb⟩
      · simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfa, hfb⟩
    | letBind n val body _ _ =>
      intro he
      simp only [noVarRef, Bool.and_eq_true] at he
      obtain ⟨hv, hb⟩ := he
      have hfv := ih val hv
      have hfb := ih body hb
      simp only [flattenLetFoldReturn]
      split
      · -- n = "_"
        split
        · exact hfb
        · next v lo hi b heq =>
          rw [heq] at hfv; simp only [noVarRef, Bool.and_eq_true] at hfv ⊢; exact ⟨hfv, hfb⟩
        · next v lo hi b heq =>
          rw [heq] at hfv; simp only [noVarRef, Bool.and_eq_true] at hfv ⊢; exact ⟨hfv, hfb⟩
        · next c b heq =>
          rw [heq] at hfv; simp only [noVarRef, Bool.and_eq_true] at hfv ⊢; exact ⟨hfv, hfb⟩
        · next innerVal innerBody heq =>
          rw [heq] at hfv; simp only [noVarRef, Bool.and_eq_true] at hfv
          exact ih _ (by simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfv.1, hfv.2, hfb⟩)
        · next innerA innerB heq =>
          rw [heq] at hfv; simp only [noVarRef, Bool.and_eq_true] at hfv
          exact ih _ (by simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfv.1, hfv.2, hfb⟩)
        · next c t e heq =>
          have hfv' := hfv; rw [heq] at hfv'; simp only [noVarRef, Bool.and_eq_true] at hfv'
          split
          · simp only [noVarRef, Bool.and_eq_true]
            exact ⟨⟨hfv'.1.1, ih _ (by simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfv'.1.2, hfb⟩)⟩,
                   ih _ (by simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfv'.2, hfb⟩)⟩
          · simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfv, hfb⟩
        · simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfv, hfb⟩
      · simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfv, hfb⟩

/-! ## Heterogeneous helper congruences

The whole-pass theorem needs each `denote`-helper, run on the *flattened*
subterms, to be `Rel`-related to the same helper on the originals. These
mirror the homogeneous `denote*_rel` lemmas but relate two distinct
bodies/argument lists given a pointwise `Rel`. -/

theorem denoteForLoop_rel_het (bi : Builtins) (n var : String) (body body' : ImpExpr)
    (Hb : ∀ df, Rel n (denote bi df body') (denote bi df body)) :
    ∀ df lo hi, Rel n (denoteForLoop bi df var lo hi body')
      (denoteForLoop bi df var lo hi body) := by
  intro df
  induction df with
  | zero =>
    intro lo hi; unfold denoteForLoop
    split
    · exact Rel.pure _
    · split
      · exact Rel.pure _
      · exact absurd rfl ‹_›
  | succ k ih =>
    intro lo hi; unfold denoteForLoop
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

theorem denoteForLoopRev_rel_het (bi : Builtins) (n var : String) (body body' : ImpExpr)
    (Hb : ∀ df, Rel n (denote bi df body') (denote bi df body)) :
    ∀ df lo hi, Rel n (denoteForLoopRev bi df var lo hi body')
      (denoteForLoopRev bi df var lo hi body) := by
  intro df
  induction df with
  | zero =>
    intro lo hi; unfold denoteForLoopRev
    split
    · exact Rel.pure _
    · split
      · exact Rel.pure _
      · exact absurd rfl ‹_›
  | succ k ih =>
    intro lo hi; unfold denoteForLoopRev
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

theorem denoteWhile_rel_het (bi : Builtins) (n : String) (cond cond' body body' : ImpExpr)
    (Hc : ∀ df, Rel n (denote bi df cond') (denote bi df cond))
    (Hb : ∀ df, Rel n (denote bi df body') (denote bi df body)) :
    ∀ df, Rel n (denoteWhile bi df cond' body') (denoteWhile bi df cond body) := by
  intro df
  induction df with
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

theorem denoteArgs_rel_het (bi : Builtins) (n : String) (df : Nat) (f : ImpExpr → ImpExpr) :
    ∀ (es : List ImpExpr),
      (∀ e ∈ es, Rel n (denote bi df (f e)) (denote bi df e)) →
      Rel n (denoteArgs bi df (es.map f)) (denoteArgs bi df es) := by
  intro es
  induction es with
  | nil => intro _; simp only [List.map_nil, denoteArgs]; exact Rel.pure _
  | cons e es ih =>
    intro hall
    simp only [List.map_cons, denoteArgs]
    apply Rel.bind (hall e (List.mem_cons_self ..))
    intro r
    cases r <;>
      first
        | (apply Rel.bind (ih (fun e' he' => hall e' (List.mem_cons_of_mem _ he')))
           intro rest
           exact Rel.pure _)
        | exact Rel.pure _

theorem denoteMatchArms_rel_het (bi : Builtins) (n : String) (df : Nat) (v : Value)
    (f : ImpExpr → ImpExpr) :
    ∀ (arms : List (ImpPat × ImpExpr)),
      (∀ pa ∈ arms, Rel n (denote bi df (f pa.2)) (denote bi df pa.2)) →
      Rel n (denoteMatchArms bi df v (arms.map (fun pe => (pe.1, f pe.2))))
        (denoteMatchArms bi df v arms) := by
  intro arms
  induction arms with
  | nil => intro _; simp only [List.map_nil, denoteMatchArms]; exact Rel.pure _
  | cons pa rest ih =>
    obtain ⟨pat, body⟩ := pa
    intro hall s₁ s₂ hs
    simp only [List.map_cons, denoteMatchArms, stateM_bind_apply, stateM_get_apply]
    have hmp := matchPat_agree n pat v s₁ s₂ hs
    cases hp1 : matchPat pat v s₁ <;> cases hp2 : matchPat pat v s₂ <;>
      simp only [hp1, hp2, OptAgree] at hmp
    · exact ih (fun pa' hpa' => hall pa' (List.mem_cons_of_mem _ hpa')) s₁ s₂ hs
    · simp only [stateM_bind_apply, stateM_set_apply]
      exact hall (pat, body) (List.mem_cons_self ..) _ _ hmp

/-- Heterogeneous `letBind` congruence: relate `letBind` on flattened
    pieces to `letBind` on the originals. -/
theorem denote_letBind_rel_het (bi : Builtins) (n name : String) (df : Nat)
    (v v' b b' : ImpExpr)
    (Hv : Rel n (denote bi df v') (denote bi df v))
    (Hb : ∀ d, Rel n (denote bi d b') (denote bi d b)) :
    Rel n (denote bi df (.letBind name v' b')) (denote bi df (.letBind name v b)) := by
  simp only [denote_letBind]
  apply Rel.bind Hv
  intro rv
  cases rv <;>
    first
      | (apply Rel.bind (Rel.modify_extend n name _); intro _; exact Hb df)
      | exact Rel.pure _

/-- The seq-form B′ identity: a discarded `seq` head re-associates into a
    nested `seq`/`letBind "_"`. A clean `denote` equality (no freshness):
    `seq` does not bind `"_"`, so the `"_"` slot is set once, after the
    inner expression, on both sides. -/
theorem flattenBseq_eq (bi : Builtins) (df : Nat) (iA iB body' : ImpExpr) :
    denote bi df (.letBind "_" (.seq iA iB) body')
      = denote bi df (.seq iA (.letBind "_" iB body')) := by
  simp only [denote_letBind, denote_seq, bind_assoc]
  congr 1
  funext r
  cases r <;> first | rfl | simp only [pure_bind]

/-- Heterogeneous `seq` congruence. -/
theorem denote_seq_rel_het (bi : Builtins) (n : String) (df : Nat) (a a' b b' : ImpExpr)
    (Ha : Rel n (denote bi df a') (denote bi df a))
    (Hb : ∀ d, Rel n (denote bi d b') (denote bi d b)) :
    Rel n (denote bi df (.seq a' b')) (denote bi df (.seq a b)) := by
  simp only [denote_seq]
  apply Rel.bind Ha
  intro r
  split <;> first | exact Hb df | exact Rel.pure _

/-- Heterogeneous `ifThenElse` congruence. -/
theorem denote_ite_rel_het (bi : Builtins) (n : String) (df : Nat) (c c' t t' e e' : ImpExpr)
    (Hc : Rel n (denote bi df c') (denote bi df c))
    (Ht : Rel n (denote bi df t') (denote bi df t))
    (He : Rel n (denote bi df e') (denote bi df e)) :
    Rel n (denote bi df (.ifThenElse c' t' e')) (denote bi df (.ifThenElse c t e)) := by
  simp only [denote]
  apply Rel.bind Hc
  intro rc
  split <;> first | exact Ht | exact He | exact Rel.pure _

/-- The seq-form C′ identity: distribute a discarded `seq` over an `if`.
    A clean `denote` equality. -/
theorem flattenCseq_eq (bi : Builtins) (df : Nat) (c t e b' : ImpExpr) :
    denote bi df (.seq (.ifThenElse c t e) b')
      = denote bi df (.ifThenElse c (.seq t b') (.seq e b')) := by
  simp only [denote_seq, denote, bind_assoc]
  congr 1
  funext rc
  split <;> simp only [pure_bind]

/-! ## Whole-pass denotation preservation

Under the `noVarRef "_"` invariant, the total fuel-bounded pass
`flattenLetFoldReturn` preserves denotation up to the `"_"` slot
(`Rel "_"`). The structural cases are heterogeneous congruences (via the
`ih` at fuel `k`); the discarded-`letBind`/`seq` cases compose the four
rewrite identities (`flattenA_rel`/`flattenB_denote`/`flattenC_denote`/
`flattenD_rel`, plus the seq-form `flattenBseq_eq`/`flattenCseq_eq`)
through the `Rel` partial equivalence. -/
theorem flattenLetFoldReturn_denote (bi : Builtins) :
    ∀ (k : Nat) (e : ImpExpr), noVarRef "_" e = true →
      ∀ df, Rel "_" (denote bi df (flattenLetFoldReturn k e)) (denote bi df e) := by
  intro k
  induction k with
  | zero => intro e he df; simp only [flattenLetFoldReturn]; exact denote_agreeExcept bi "_" e df he
  | succ k ih =>
    intro e
    induction e using ImpExpr.ind with
    | lit | var | unitVal | continue_ | break_none =>
      intro he df; simp only [flattenLetFoldReturn]; exact denote_agreeExcept bi "_" _ df he
    | lam _ body _ =>
      intro _ df; simp only [flattenLetFoldReturn, denote]; exact Rel.pure _
    | borrow e _ | deref e _ =>
      intro he df; simp only [noVarRef] at he; simp only [flattenLetFoldReturn, denote]
      exact ih e he df
    | typeAscription e _ _ =>
      intro he df; simp only [noVarRef] at he; simp only [flattenLetFoldReturn, denote]
      exact ih e he df
    | break_some e _ | earlyReturn e _ | questionMark e _ =>
      intro he df; simp only [noVarRef] at he; simp only [flattenLetFoldReturn, denote]
      apply Rel.bind (ih e he df); intro r; split <;> exact Rel.pure _
    | proj e i _ =>
      intro he df; simp only [noVarRef] at he; simp only [flattenLetFoldReturn, denote]
      apply Rel.bind (ih e he df); intro r; split <;> (try split) <;> exact Rel.pure _
    | cfBreak e _ | cfContinue e _ | cfBreakContinue e _ =>
      intro _ df; simp only [flattenLetFoldReturn, denote]; exact Rel.pure _
    | assign name rhs _ =>
      intro he df; simp only [noVarRef] at he; simp only [flattenLetFoldReturn, denote]
      apply Rel.bind (ih rhs he df); intro r
      cases r <;>
        first
          | (apply Rel.bind (Rel.modify_extend "_" name _); intro _; exact Rel.pure _)
          | exact Rel.pure _
    | app f args _ =>
      intro he df; simp only [noVarRef] at he; simp only [flattenLetFoldReturn, denote]
      apply Rel.bind (denoteArgs_rel_het bi "_" df (flattenLetFoldReturn k) args
        (fun a ha => ih a (noVarRef_allExpr_mem he a ha) df))
      intro mvals; split <;> (try split) <;> exact Rel.pure _
    | tuple args _ =>
      intro he df; simp only [noVarRef] at he; simp only [flattenLetFoldReturn, denote]
      apply Rel.bind (denoteArgs_rel_het bi "_" df (flattenLetFoldReturn k) args
        (fun a ha => ih a (noVarRef_allExpr_mem he a ha) df))
      intro mvals; split <;> exact Rel.pure _
    | match_ scrut arms _ _ =>
      intro he df; simp only [noVarRef, Bool.and_eq_true] at he
      simp only [flattenLetFoldReturn, denote]
      apply Rel.bind (ih scrut he.1 df); intro rs
      split
      · exact denoteMatchArms_rel_het bi "_" df _ (flattenLetFoldReturn k) arms
          (fun pa hpa => ih pa.2 (noVarRef_allArms_mem he.2 pa hpa) df)
      · exact Rel.pure _
    | ifThenElse c t e _ _ _ =>
      intro he df; simp only [noVarRef, Bool.and_eq_true] at he
      simp only [flattenLetFoldReturn]
      exact denote_ite_rel_het bi "_" df c _ t _ e _ (ih c he.1.1 df) (ih t he.1.2 df) (ih e he.2 df)
    | forLoop var lo hi body _ _ _ =>
      intro he df; simp only [noVarRef, Bool.and_eq_true] at he
      simp only [flattenLetFoldReturn, denote]
      apply Rel.bind (ih lo he.1.1 df); intro rlo
      apply Rel.bind (ih hi he.1.2 df); intro rhi
      split <;>
        first
          | exact denoteForLoop_rel_het bi "_" var body _ (fun d => ih body he.2 d) _ _ _
          | exact Rel.pure _
    | forLoopRev var lo hi body _ _ _ =>
      intro he df; simp only [noVarRef, Bool.and_eq_true] at he
      simp only [flattenLetFoldReturn, denote]
      apply Rel.bind (ih lo he.1.1 df); intro rlo
      apply Rel.bind (ih hi he.1.2 df); intro rhi
      split <;>
        first
          | exact denoteForLoopRev_rel_het bi "_" var body _ (fun d => ih body he.2 d) _ _ _
          | exact Rel.pure _
    | whileLoop c body _ _ =>
      intro he df; simp only [noVarRef, Bool.and_eq_true] at he
      simp only [flattenLetFoldReturn, denote]
      exact denoteWhile_rel_het bi "_" c _ body _ (fun d => ih c he.1 d) (fun d => ih body he.2 d) df
    | forFold _ _ _ _ _ _ _ | forFoldRev _ _ _ _ _ _ _ | whileFold _ _ _ _
    | forFoldReturn _ _ _ _ _ _ _ | forFoldRevReturn _ _ _ _ _ _ _ | whileFoldReturn _ _ _ _ =>
      intro he df; simp only [flattenLetFoldReturn, denote]; exact Rel.pure _
    | seq a b _ _ =>
      intro he df
      simp only [noVarRef, Bool.and_eq_true] at he
      obtain ⟨ha, hb⟩ := he
      have hfb := flatten_noVarRef k b hb
      have seqCong := denote_seq_rel_het bi "_" df a (flattenLetFoldReturn k a) b
        (flattenLetFoldReturn k b) (ih a ha df) (fun d => ih b hb d)
      simp only [flattenLetFoldReturn]
      split
      · next c t e heq =>
        have hfa := flatten_noVarRef k a ha
        rw [heq] at hfa; simp only [noVarRef, Bool.and_eq_true] at hfa
        split
        · refine (denote_ite_rel_het bi "_" df _ _ _ _ _ _
                    (denote_agreeExcept bi "_" c df hfa.1.1)
                    (ih (.seq t (flattenLetFoldReturn k b)) ?_ df)
                    (ih (.seq e (flattenLetFoldReturn k b)) ?_ df)).trans ?_
          · simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfa.1.2, hfb⟩
          · simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfa.2, hfb⟩
          · rw [← flattenCseq_eq, ← heq]; exact seqCong
        · exact seqCong
      · exact seqCong
    | letBind n val body _ _ =>
      intro he df
      simp only [noVarRef, Bool.and_eq_true] at he
      obtain ⟨hv, hb⟩ := he
      have hfv := flatten_noVarRef k val hv
      have hfb := flatten_noVarRef k body hb
      have letCong := denote_letBind_rel_het bi "_" n df val (flattenLetFoldReturn k val) body
        (flattenLetFoldReturn k body) (ih val hv df) (fun d => ih body hb d)
      simp only [flattenLetFoldReturn]
      split
      · next hn =>
        obtain rfl : n = "_" := eq_of_beq hn
        split
        · next heq =>
          rw [heq] at letCong
          exact ((flattenA_rel bi df _ hfb).symm).trans letCong
        · next v lo hi b heq =>
          rw [heq] at hfv letCong
          exact ((flattenD_rel bi df _ _ hfv hfb).symm).trans letCong
        · next v lo hi b heq =>
          rw [heq] at hfv letCong
          exact ((flattenD_rel bi df _ _ hfv hfb).symm).trans letCong
        · next c b heq =>
          rw [heq] at hfv letCong
          exact ((flattenD_rel bi df _ _ hfv hfb).symm).trans letCong
        · next iv ib heq =>
          rw [heq] at hfv letCong
          simp only [noVarRef, Bool.and_eq_true] at hfv
          refine (ih _ ?_ df).trans ?_
          · simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfv.1, hfv.2, hfb⟩
          · rw [← flattenB_denote]; exact letCong
        · next iA iB heq =>
          rw [heq] at hfv letCong
          simp only [noVarRef, Bool.and_eq_true] at hfv
          refine (ih _ ?_ df).trans
            ((flattenD_rel bi df iA (.letBind "_" iB (flattenLetFoldReturn k body)) hfv.1 ?_).trans ?_)
          · simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfv.1, hfv.2, hfb⟩
          · simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfv.2, hfb⟩
          · rw [← flattenBseq_eq]; exact letCong
        · next c t e heq =>
          have hfv' := hfv; rw [heq] at hfv'; simp only [noVarRef, Bool.and_eq_true] at hfv'
          split
          · refine (denote_ite_rel_het bi "_" df _ _ _ _ _ _
                      (denote_agreeExcept bi "_" c df hfv'.1.1)
                      (ih (.letBind "_" t (flattenLetFoldReturn k body)) ?_ df)
                      (ih (.letBind "_" e (flattenLetFoldReturn k body)) ?_ df)).trans ?_
            · simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfv'.1.2, hfb⟩
            · simp only [noVarRef, Bool.and_eq_true]; exact ⟨hfv'.2, hfb⟩
            · rw [← flattenC_denote, ← heq]; exact letCong
          · exact letCong
        · exact letCong
      · exact letCong

end Hax

/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.SemanticsCF
import SSProve.Hax.Phase.FunctionalizeLoops

/-!
# Phase 3 Correctness: Functionalize Loops

Proves that `functionalizeLoops` preserves denotational semantics
up to `Outcome.encodeCF3` encoding (broke/continued → controlFlow values).

## Main results

* `FL_combined` — simulation + env invariant for all expressions

## Refactored design

With dedicated AST constructors (`forFold`, `whileFold`, `cfBreak`, `cfContinue`),
the `NoReservedApps` predicate is no longer needed. The `denote'` interpreter
dispatches on these constructors directly, eliminating the string-matching in
`denoteApp'`. This simplifies both the proof obligations and the proof structure:
- No need to unfold `denoteApp'` and match on 7 string equalities
- Constructor cases in `FL_combined` directly invoke `denote'` cases
- `denoteApp'` is now just the regular function call case
- `NoCFConstructors` replaces `NoReservedApps`: the 6 dedicated constructors
  cannot appear in pre-pipeline expressions (denote gives error for them).

## Design note: the `nested` parameter

`functionalizeLoopsAux` takes a `nested : Bool` parameter that controls how
`break_` is translated:
- `nested = false` → `cfBreak` (single-wrapped: `controlFlow true v`)
- `nested = true` → `cfBreakContinue` (double-wrapped: `controlFlow true (controlFlow false v)`)

The double-wrapping is used when a loop body contains `earlyReturn`, so that
`denoteForLoop'Return` can distinguish loop breaks from early returns:
- `val (controlFlow true (controlFlow false v))` → loop break
- `val (controlFlow true v)` (non-Continue) → early return

This couples two concerns (loop functionalization + nested earlyReturn handling)
into one recursive traversal. As a consequence, the correctness proof must be
generalized over `nested`:
- `FL_combined_gen` proves `FLInvGen nested` for all `nested : Bool`
- `FL_combined` is the corollary with `nested = false`

The encoding function `Outcome.encodeFL nested` parameterizes the outcome
mapping: it agrees with `encodeCF3` on all outcomes except `broke`, where
`nested = true` adds an extra `controlFlow false` wrapper.

### Possible future simplification

The `nested` parameter could be eliminated by:
1. **Splitting Phase 3** into sub-phases (uniform break→CF, then add nesting)
2. **Always double-wrapping** break (use forFoldReturn everywhere)
3. **Deferring earlyReturn** to Phase 4 entirely

Any of these would yield a simpler correctness proof at the cost of refactoring
the AST constructors and `denote'` match arms.
-/

namespace SSProve.Hax

/-! ### NoCFConstructors predicate -/

/-- An expression contains none of the dedicated Phase 3/4 output constructors
    (`forFold`, `whileFold`, `forFoldReturn`, `whileFoldReturn`, `cfBreak`, `cfContinue`).
    This holds for all pre-pipeline expressions. `denote` returns an error for these
    constructors, so FLInv cannot hold if they appear in the source. -/
inductive NoCFConstructors : ImpExpr → Prop where
  | lit {v} : NoCFConstructors (.lit v)
  | var {n} : NoCFConstructors (.var n)
  | letBind {n val body} : NoCFConstructors val → NoCFConstructors body →
      NoCFConstructors (.letBind n val body)
  | app {f args} : (∀ a, a ∈ args → NoCFConstructors a) →
      NoCFConstructors (.app f args)
  | tuple {elems} : (∀ a, a ∈ elems → NoCFConstructors a) →
      NoCFConstructors (.tuple elems)
  | proj {e i} : NoCFConstructors e → NoCFConstructors (.proj e i)
  | ifThenElse {c t e} : NoCFConstructors c → NoCFConstructors t → NoCFConstructors e →
      NoCFConstructors (.ifThenElse c t e)
  | match_ {scrut arms} : NoCFConstructors scrut →
      (∀ pa, pa ∈ arms → NoCFConstructors pa.2) →
      NoCFConstructors (.match_ scrut arms)
  | unitVal : NoCFConstructors .unitVal
  | seq {e1 e2} : NoCFConstructors e1 → NoCFConstructors e2 →
      NoCFConstructors (.seq e1 e2)
  | borrow {e} : NoCFConstructors e → NoCFConstructors (.borrow e)
  | deref {e} : NoCFConstructors e → NoCFConstructors (.deref e)
  | assign {n rhs} : NoCFConstructors rhs → NoCFConstructors (.assign n rhs)
  | forLoop {v lo hi body} : NoCFConstructors lo → NoCFConstructors hi →
      NoCFConstructors body → NoCFConstructors (.forLoop v lo hi body)
  | whileLoop {c body} : NoCFConstructors c → NoCFConstructors body →
      NoCFConstructors (.whileLoop c body)
  | break_none : NoCFConstructors (.break_ none)
  | break_some {e} : NoCFConstructors e → NoCFConstructors (.break_ (some e))
  | continue_ : NoCFConstructors .continue_
  | earlyReturn {e} : NoCFConstructors e → NoCFConstructors (.earlyReturn e)
  | questionMark {e} : NoCFConstructors e → NoCFConstructors (.questionMark e)

theorem NoCFConstructors.not_forFold {v : String} {lo hi body : ImpExpr} :
    ¬NoCFConstructors (.forFold v lo hi body) := by intro h; cases h
theorem NoCFConstructors.not_whileFold {c body : ImpExpr} :
    ¬NoCFConstructors (.whileFold c body) := by intro h; cases h
theorem NoCFConstructors.not_forFoldReturn {v : String} {lo hi body : ImpExpr} :
    ¬NoCFConstructors (.forFoldReturn v lo hi body) := by intro h; cases h
theorem NoCFConstructors.not_whileFoldReturn {c body : ImpExpr} :
    ¬NoCFConstructors (.whileFoldReturn c body) := by intro h; cases h
theorem NoCFConstructors.not_cfBreak {e : ImpExpr} :
    ¬NoCFConstructors (.cfBreak e) := by intro h; cases h
theorem NoCFConstructors.not_cfContinue {e : ImpExpr} :
    ¬NoCFConstructors (.cfContinue e) := by intro h; cases h
theorem NoCFConstructors.not_cfBreakContinue {e : ImpExpr} :
    ¬NoCFConstructors (.cfBreakContinue e) := by intro h; cases h

/-! ### Combined invariant -/

/-- Generalized combined invariant, parametric in `nested`.
    When `nested = false`: uses `functionalizeLoops` and `encodeCF3`.
    When `nested = true`: uses `functionalizeLoopsAux true` and `encodeCF3nested`.

    The first 3 components (env, val deepNoControlFlow, broke deepNoControlFlow)
    are properties of `denote` and don't depend on the transformation. Only
    the simulation (part 4) depends on `nested`. -/
private abbrev FLInvGen (nested : Bool) (bi : Builtins) (e : ImpExpr) : Prop :=
  ∀ fuel env, Env.NoControlFlow env →
    (denote bi fuel e env).2.NoControlFlow ∧
    (∀ v, (denote bi fuel e env).1 = .val v → v.deepNoControlFlow = true) ∧
    (∀ v, (denote bi fuel e env).1 = .broke v → v.deepNoControlFlow = true) ∧
    denote' bi fuel (functionalizeLoopsAux nested e) env =
      (Outcome.encodeCF3gen nested (denote bi fuel e env).1, (denote bi fuel e env).2)

/-- The combined invariant (non-nested). -/
private abbrev FLInv (bi : Builtins) (e : ImpExpr) : Prop :=
  ∀ fuel env, Env.NoControlFlow env →
    (denote bi fuel e env).2.NoControlFlow ∧
    (∀ v, (denote bi fuel e env).1 = .val v → v.deepNoControlFlow = true) ∧
    (∀ v, (denote bi fuel e env).1 = .broke v → v.deepNoControlFlow = true) ∧
    denote' bi fuel (functionalizeLoops e) env =
      (Outcome.encodeCF3 (denote bi fuel e env).1, (denote bi fuel e env).2)

/-- `FLInvGen false` implies `FLInv` (and vice versa, since `encodeCF3gen false = encodeCF3`
    and `functionalizeLoopsAux false = functionalizeLoops`). -/
private theorem FLInvGen_false_eq_FLInv (bi : Builtins) (e : ImpExpr) :
    FLInvGen false bi e ↔ FLInv bi e := by
  simp only [FLInvGen, FLInv, functionalizeLoops, Outcome.encodeCF3gen_false_eq]

/-! ### matchPat preserves NoControlFlow -/

private def matchPat_preserves_ncf_impl :
    (pat : ImpPat) → ∀ (v : Value) (env env' : Env),
      env.NoControlFlow → v.deepNoControlFlow = true →
      matchPat pat v env = some env' → env'.NoControlFlow :=
  @ImpPat.rec
    (fun pat => ∀ (v : Value) (env env' : Env),
      env.NoControlFlow → v.deepNoControlFlow = true →
      matchPat pat v env = some env' → env'.NoControlFlow)
    (fun pats => ∀ (vs : List Value) (env env' : Env),
      env.NoControlFlow → (∀ v ∈ vs, v.deepNoControlFlow = true) →
      matchPat.matchPatList pats vs env = some env' → env'.NoControlFlow)
    (fun v env env' henv _ hm => by simp [matchPat] at hm; subst hm; exact henv)
    (fun l v env env' henv _ hm => by
      simp only [matchPat] at hm
      cases h : (Value.ofLit l == v) <;> simp [h] at hm <;> subst hm <;> exact henv)
    (fun name v env env' henv hv hm => by
      simp only [matchPat] at hm; cases hm; exact henv.extend hv)
    (fun pats ih_pats v env env' henv hv hm => by
      cases v with
      | tuple vs =>
        simp only [matchPat] at hm; split at hm
        · cases hm
        · exact ih_pats vs env env' henv
            (fun v hv' => Value.deepNoControlFlow_tuple_mem hv hv') hm
      | array vs =>
        simp only [matchPat] at hm; split at hm
        · cases hm
        · exact ih_pats vs env env' henv
            (fun v hv' => Value.deepNoControlFlow_array_mem hv hv') hm
      | _ => simp [matchPat] at hm)
    (fun p ih v env env' henv hv hm => by
      cases v with
      | option o =>
        cases o with
        | some v' =>
          simp only [matchPat] at hm
          exact ih v' env env' henv (by simp [Value.deepNoControlFlow] at hv; exact hv) hm
        | none => simp [matchPat] at hm
      | _ => simp [matchPat] at hm)
    (fun v env env' henv _ hm => by
      cases v with
      | option o =>
        cases o with
        | none => simp [matchPat] at hm; subst hm; exact henv
        | some => simp [matchPat] at hm
      | _ => simp [matchPat] at hm)
    (fun p ih v env env' henv hv hm => by
      cases v with
      | result ok payload =>
        cases ok with
        | true =>
          simp only [matchPat] at hm
          exact ih payload env env' henv (by simp [Value.deepNoControlFlow] at hv; exact hv) hm
        | false => simp [matchPat] at hm
      | _ => simp [matchPat] at hm)
    (fun p ih v env env' henv hv hm => by
      cases v with
      | result ok payload =>
        cases ok with
        | false =>
          simp only [matchPat] at hm
          exact ih payload env env' henv (by simp [Value.deepNoControlFlow] at hv; exact hv) hm
        | true => simp [matchPat] at hm
      | _ => simp [matchPat] at hm)
    (fun vs env env' henv hvs hm => by
      cases vs with
      | nil => simp [matchPat.matchPatList] at hm; subst hm; exact henv
      | cons => simp [matchPat.matchPatList] at hm)
    (fun head tail ih_head ih_tail vs env env' henv hvs hm => by
      cases vs with
      | nil => simp [matchPat.matchPatList] at hm
      | cons v vs =>
        simp only [matchPat.matchPatList, Option.bind_eq_bind, Option.bind_eq_some_iff] at hm
        obtain ⟨env_mid, hm1, hm2⟩ := hm
        exact ih_tail vs env_mid env'
          (ih_head v env env_mid henv (hvs v (.head _)) hm1)
          (fun w hw => hvs w (.tail _ hw)) hm2)

private theorem matchPat_preserves_noControlFlow {pat : ImpPat} {v : Value}
    {env env' : Env} (henv : env.NoControlFlow)
    (hv : v.deepNoControlFlow = true)
    (hm : matchPat pat v env = some env') :
    env'.NoControlFlow :=
  matchPat_preserves_ncf_impl pat v env env' henv hv hm

/-! ### StateM bind congruence -/

/-- If two state monads agree at a point, their binds with the same continuation agree. -/
private theorem stateM_bind_congr {σ α β : Type} (ma mb : StateM σ α)
    (f : α → StateM σ β) (s : σ) (h : ma s = mb s) :
    StateT.bind ma f s = StateT.bind mb f s := by
  simp only [StateT.bind, h]

/-! ### Helper: deepNoControlFlowList from pointwise -/

private theorem deepNoControlFlowList_of_forall (vals : List Value)
    (h : ∀ v ∈ vals, v.deepNoControlFlow = true) :
    Value.deepNoControlFlow.deepNoControlFlowList vals = true := by
  induction vals with
  | nil => rfl
  | cons v vs ih =>
    simp [Value.deepNoControlFlow.deepNoControlFlowList, Bool.and_eq_true]
    exact ⟨h v (.head _), ih (fun w hw => h w (.tail _ hw))⟩

/-! ### Tactics for error/broke branches -/

/-- Close the env + val + broke + sim goals when the outcome is earlyRet/continued/err. -/
macro "fl_error_branch" henv:ident : tactic =>
  `(tactic| (refine ⟨$henv, ?_, ?_, ?_⟩ <;>
    simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_val,
      Outcome.encodeCF3gen_earlyRet, Outcome.encodeCF3gen_err,
      Outcome.encodeCF3gen_continued]))

/-- Close goals when broke propagates from a sub-expression via `pure other`.
    Non-generalized version using `encodeCF3`. -/
macro "fl_broke_propagate" henv:ident hbrk:ident : tactic =>
  `(tactic| exact ⟨$henv,
    fun v h => by simp [pure, Pure.pure, StateT.pure] at h,
    fun v h => by
      simp only [pure, Pure.pure, StateT.pure, Outcome.broke.injEq] at h; subst h
      exact $hbrk _ rfl,
    by simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]⟩)

/-- Close goals when broke propagates, generalized version with `nested` parameter. -/
macro "fl_broke_propagate_gen" henv:ident hbrk:ident nested:ident : tactic =>
  `(tactic| exact ⟨$henv,
    fun v h => by simp [pure, Pure.pure, StateT.pure] at h,
    fun v h => by
      simp only [pure, Pure.pure, StateT.pure, Outcome.broke.injEq] at h; subst h
      exact $hbrk _ rfl,
    Bool.casesOn $nested
      (by simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3])
      (by simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3nested])⟩)

/-! ### denoteArgs combined -/

private theorem denoteArgs_combined (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (fuel : Nat) (es : List ImpExpr) (hih : ∀ e ∈ es, FLInv bi e) :
    ∀ env, Env.NoControlFlow env →
      (denoteArgs bi fuel es env).2.NoControlFlow ∧
      (∀ vals, (denoteArgs bi fuel es env).1 = some vals →
        ∀ v ∈ vals, v.deepNoControlFlow = true) ∧
      denoteArgs' bi fuel (es.map functionalizeLoops) env =
        ((denoteArgs bi fuel es env).1, (denoteArgs bi fuel es env).2) := by
  induction es with
  | nil =>
    intro env henv
    refine ⟨?_, ?_, ?_⟩
    · unfold denoteArgs; exact henv
    · intro vals h v hv
      unfold denoteArgs at h
      simp only [pure, Pure.pure, StateT.pure, Option.some.injEq] at h
      subst h; cases hv
    · simp only [List.map_nil]; unfold denoteArgs' denoteArgs; rfl
  | cons e es ih_es =>
    intro env henv
    simp only [List.map_cons]
    unfold denoteArgs denoteArgs'
    simp only [bind, StateT.bind]
    obtain ⟨henv_e, hnc_e, _, hsim_e⟩ := hih e (.head _) fuel env henv
    generalize hpe : denote bi fuel e env = pe at henv_e hnc_e hsim_e ⊢
    obtain ⟨re, enve⟩ := pe; simp only [functionalizeLoops] at *
    rw [hsim_e]
    cases re with
    | val v =>
      simp only [Outcome.encodeCF3]
      have hv := hnc_e v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | _ =>
        simp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure] at ⊢
        have hih_es' : ∀ e' ∈ es, FLInv bi e' := fun e' he' => hih e' (.tail _ he')
        obtain ⟨henv_es, hnc_es, hsim_es⟩ := ih_es hih_es' enve henv_e
        generalize hpes : denoteArgs bi fuel es enve = pes at henv_es hnc_es hsim_es ⊢
        obtain ⟨mes, enves⟩ := pes; simp only [functionalizeLoops] at *
        rw [hsim_es]; simp only []
        refine ⟨henv_es, fun vals hvals w hw => ?_, trivial⟩
        cases mes with
        | none => simp [Option.map] at hvals
        | some vs =>
          simp [Option.map] at hvals; subst hvals
          cases hw with
          | head => exact hv
          | tail _ hw => exact hnc_es vs rfl w hw
    | earlyRet =>
      simp only [Outcome.encodeCF3]
      exact ⟨henv_e, fun vals h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩
    | broke v =>
      simp only [Outcome.encodeCF3]
      refine ⟨henv_e, fun vals h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩
    | continued =>
      simp only [Outcome.encodeCF3]
      refine ⟨henv_e, fun vals h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩
    | err =>
      simp only [Outcome.encodeCF3]
      exact ⟨henv_e, fun vals h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩

/-! ### denoteMatchArms combined -/

private theorem denoteMatchArms_combined (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (fuel : Nat) (v : Value) (hv : v.deepNoControlFlow = true)
    (arms : List (ImpPat × ImpExpr)) (hih : ∀ pa ∈ arms, FLInv bi pa.2) :
    ∀ env, Env.NoControlFlow env →
      (denoteMatchArms bi fuel v arms env).2.NoControlFlow ∧
      (∀ w, (denoteMatchArms bi fuel v arms env).1 = .val w →
        w.deepNoControlFlow = true) ∧
      (∀ w, (denoteMatchArms bi fuel v arms env).1 = .broke w →
        w.deepNoControlFlow = true) ∧
      denoteMatchArms' bi fuel v (arms.map fun (p, e) => (p, functionalizeLoops e)) env =
        (Outcome.encodeCF3 (denoteMatchArms bi fuel v arms env).1,
         (denoteMatchArms bi fuel v arms env).2) := by
  induction arms with
  | nil =>
    intro env henv
    unfold denoteMatchArms denoteMatchArms'
    refine ⟨henv, ?_, ?_, ?_⟩ <;> simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
  | cons arm arms ih_arms =>
    intro env henv
    obtain ⟨pat, body⟩ := arm
    simp only [List.map_cons]
    unfold denoteMatchArms denoteMatchArms'
    simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
    cases hm : matchPat pat v env with
    | none =>
      simp only [hm]
      exact ih_arms (fun pa hpa => hih pa (.tail _ hpa)) env henv
    | some env' =>
      simp only [hm, set, StateT.set, modify, modifyGet, MonadStateOf.modifyGet]
      have henv' : env'.NoControlFlow := matchPat_preserves_noControlFlow henv hv hm
      exact hih ⟨pat, body⟩ (.head _) fuel env' henv'

/-! ### Generalized denoteArgs/denoteMatchArms combined (parametric in nested) -/

private theorem denoteArgs_combined_gen (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (nested : Bool)
    (fuel : Nat) (es : List ImpExpr) (hih : ∀ e ∈ es, FLInvGen nested bi e) :
    ∀ env, Env.NoControlFlow env →
      (denoteArgs bi fuel es env).2.NoControlFlow ∧
      (∀ vals, (denoteArgs bi fuel es env).1 = some vals →
        ∀ v ∈ vals, v.deepNoControlFlow = true) ∧
      denoteArgs' bi fuel (es.map (functionalizeLoopsAux nested)) env =
        ((denoteArgs bi fuel es env).1, (denoteArgs bi fuel es env).2) := by
  induction es with
  | nil =>
    intro env henv
    refine ⟨?_, ?_, ?_⟩
    · unfold denoteArgs; exact henv
    · intro vals h v hv
      unfold denoteArgs at h
      simp only [pure, Pure.pure, StateT.pure, Option.some.injEq] at h
      subst h; cases hv
    · simp only [List.map_nil]; unfold denoteArgs' denoteArgs; rfl
  | cons e es ih_es =>
    intro env henv
    simp only [List.map_cons]
    unfold denoteArgs denoteArgs'
    simp only [bind, StateT.bind]
    obtain ⟨henv_e, hnc_e, _, hsim_e⟩ := hih e (.head _) fuel env henv
    generalize hpe : denote bi fuel e env = pe at henv_e hnc_e hsim_e ⊢
    obtain ⟨re, enve⟩ := pe
    rw [hsim_e]
    cases re with
    | val v =>
      simp only [Outcome.encodeCF3gen_val]
      have hv := hnc_e v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | _ =>
        simp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure] at ⊢
        have hih_es' : ∀ e' ∈ es, FLInvGen nested bi e' := fun e' he' => hih e' (.tail _ he')
        obtain ⟨henv_es, hnc_es, hsim_es⟩ := ih_es hih_es' enve henv_e
        generalize hpes : denoteArgs bi fuel es enve = pes at henv_es hnc_es hsim_es ⊢
        obtain ⟨mes, enves⟩ := pes
        rw [hsim_es]; simp only []
        refine ⟨henv_es, fun vals hvals w hw => ?_, trivial⟩
        cases mes with
        | none => simp [Option.map] at hvals
        | some vs =>
          simp [Option.map] at hvals; subst hvals
          cases hw with
          | head => exact hv
          | tail _ hw => exact hnc_es vs rfl w hw
    | earlyRet =>
      simp only [Outcome.encodeCF3gen_earlyRet]
      exact ⟨henv_e, fun vals h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩
    | broke v =>
      cases nested <;> simp only [Outcome.encodeCF3gen_broke_false, Outcome.encodeCF3gen_broke_true]
      all_goals exact ⟨henv_e, fun vals h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩
    | continued =>
      simp only [Outcome.encodeCF3gen_continued]
      refine ⟨henv_e, fun vals h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩
    | err =>
      simp only [Outcome.encodeCF3gen_err]
      exact ⟨henv_e, fun vals h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩

private theorem denoteMatchArms_combined_gen (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (nested : Bool)
    (fuel : Nat) (v : Value) (hv : v.deepNoControlFlow = true)
    (arms : List (ImpPat × ImpExpr)) (hih : ∀ pa ∈ arms, FLInvGen nested bi pa.2) :
    ∀ env, Env.NoControlFlow env →
      (denoteMatchArms bi fuel v arms env).2.NoControlFlow ∧
      (∀ w, (denoteMatchArms bi fuel v arms env).1 = .val w →
        w.deepNoControlFlow = true) ∧
      (∀ w, (denoteMatchArms bi fuel v arms env).1 = .broke w →
        w.deepNoControlFlow = true) ∧
      denoteMatchArms' bi fuel v
          (arms.map fun (p, e) => (p, functionalizeLoopsAux nested e)) env =
        (Outcome.encodeCF3gen nested (denoteMatchArms bi fuel v arms env).1,
         (denoteMatchArms bi fuel v arms env).2) := by
  induction arms with
  | nil =>
    intro env henv
    unfold denoteMatchArms denoteMatchArms'
    refine ⟨henv, ?_, ?_, ?_⟩ <;>
      simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_err]
  | cons arm arms ih_arms =>
    intro env henv
    obtain ⟨pat, body⟩ := arm
    simp only [List.map_cons]
    unfold denoteMatchArms denoteMatchArms'
    simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
    cases hm : matchPat pat v env with
    | none =>
      simp only [hm]
      exact ih_arms (fun pa hpa => hih pa (.tail _ hpa)) env henv
    | some env' =>
      simp only [hm, set, StateT.set, modify, modifyGet, MonadStateOf.modifyGet]
      have henv' : env'.NoControlFlow := matchPat_preserves_noControlFlow henv hv hm
      exact hih ⟨pat, body⟩ (.head _) fuel env' henv'

/-! ### denoteForLoop + denoteWhile combined correctness -/

private theorem denoteForLoop_combined (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (body : ImpExpr) (hbody : FLInv bi body) :
    ∀ fuel var_name lo_val hi_val env, Env.NoControlFlow env →
      (denoteForLoop bi fuel var_name lo_val hi_val body env).2.NoControlFlow ∧
      (∀ w, (denoteForLoop bi fuel var_name lo_val hi_val body env).1 = .val w →
        w.deepNoControlFlow = true) ∧
      (∀ w, (denoteForLoop bi fuel var_name lo_val hi_val body env).1 = .broke w →
        w.deepNoControlFlow = true) ∧
      denoteForLoop' bi fuel var_name lo_val hi_val (functionalizeLoops body) env =
        (Outcome.encodeCF3 (denoteForLoop bi fuel var_name lo_val hi_val body env).1,
         (denoteForLoop bi fuel var_name lo_val hi_val body env).2) := by
  intro fuel; induction fuel with
  | zero =>
    intro var_name lo_val hi_val env henv
    unfold denoteForLoop denoteForLoop'
    split
    · exact ⟨henv, fun v h => by
        simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at h; subst h; rfl,
        fun v h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩
    · split
      · exact ⟨henv, fun v h => by simp [pure, Pure.pure, StateT.pure] at h,
          fun v h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩
      · omega
  | succ n ih =>
    intro var_name lo_val hi_val env henv
    unfold denoteForLoop denoteForLoop'
    by_cases hge : lo_val ≥ hi_val
    · simp only [if_pos hge]
      exact ⟨henv, fun v h => by
        simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at h; subst h; rfl,
        fun v h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩
    · have hfuel : ¬(n + 1 = 0) := by omega
      simp only [if_neg hge, if_neg hfuel]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      have hint : (Value.int lo_val).deepNoControlFlow = true := rfl
      have henv' : (Env.extend env var_name (.int lo_val)).NoControlFlow := henv.extend hint
      obtain ⟨henvb, hncb, hbrkb, hsimb⟩ :=
        hbody (n + 1) (Env.extend env var_name (.int lo_val)) henv'
      generalize hpb : denote bi (n + 1) body (Env.extend env var_name (.int lo_val)) = pb
        at henvb hncb hbrkb hsimb ⊢
      obtain ⟨rb, envb⟩ := pb; simp only [functionalizeLoops] at *
      rw [hsimb]; simp only [Outcome.encodeCF3]
      cases rb with
      | val v =>
        have hv := hncb v rfl
        cases v with
        | controlFlow => simp [Value.deepNoControlFlow] at hv
        | _ =>
          simp only [show n + 1 - 1 = n from rfl]
          exact ih var_name (lo_val + 1) hi_val envb henvb
      | continued =>
        simp only [show n + 1 - 1 = n from rfl]
        exact ih var_name (lo_val + 1) hi_val envb henvb
      | broke w =>
        exact ⟨henvb, fun v h => by
          simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at h
          subst h; exact hbrkb w rfl,
          fun v h => by simp [pure, Pure.pure, StateT.pure] at h,
          by simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]⟩
      | earlyRet =>
        exact ⟨henvb, fun v h => by simp [pure, Pure.pure, StateT.pure] at h,
          fun v h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩
      | err =>
        exact ⟨henvb, fun v h => by simp [pure, Pure.pure, StateT.pure] at h,
          fun v h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩

/-- Generalized while-loop simulation, parametric in `nested` for the condition encoding.
    Uses `FLInvGen nested bi cond` for the condition and `FLInv bi body` for the body.
    Concludes with `encodeCF3gen nested` for the overall result. -/
private theorem denoteWhile_combined_gen (nested : Bool)
    (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (cond body : ImpExpr)
    (hcond : FLInvGen nested bi cond) (hbody : FLInv bi body) :
    ∀ fuel env, Env.NoControlFlow env →
      (denoteWhile bi fuel cond body env).2.NoControlFlow ∧
      (∀ w, (denoteWhile bi fuel cond body env).1 = .val w →
        w.deepNoControlFlow = true) ∧
      (∀ w, (denoteWhile bi fuel cond body env).1 = .broke w →
        w.deepNoControlFlow = true) ∧
      denoteWhile' bi fuel (functionalizeLoopsAux nested cond) (functionalizeLoops body) env =
        (Outcome.encodeCF3gen nested (denoteWhile bi fuel cond body env).1,
         (denoteWhile bi fuel cond body env).2) := by
  intro fuel; induction fuel with
  | zero =>
    intro env henv
    unfold denoteWhile denoteWhile'
    refine ⟨henv, ?_, ?_, ?_⟩ <;>
      simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_err]
  | succ n ih =>
    intro env henv
    unfold denoteWhile denoteWhile'
    have hfuel : ¬(n + 1 = 0) := by omega
    simp only [if_neg hfuel]
    simp only [bind, StateT.bind]
    obtain ⟨henvc, hncc, hbrkc, hsimc⟩ := hcond (n + 1) env henv
    generalize hpc : denote bi (n + 1) cond env = pc at henvc hncc hbrkc hsimc ⊢
    obtain ⟨rc, envc⟩ := pc
    rw [hsimc]
    cases rc with
    | val v =>
      simp only [Outcome.encodeCF3gen_val]
      have hv := hncc v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | bool b =>
        cases b with
        | true =>
          -- Evaluate body
          simp only [bind, StateT.bind]
          obtain ⟨henvb, hncb, hbrkb, hsimb⟩ := hbody (n + 1) envc henvc
          generalize hpb : denote bi (n + 1) body envc = pb at henvb hncb hbrkb hsimb ⊢
          obtain ⟨rb, envb⟩ := pb; simp only [functionalizeLoops] at *
          rw [hsimb]; simp only [Outcome.encodeCF3]
          cases rb with
          | val w =>
            have hw := hncb w rfl
            cases w with
            | controlFlow => simp [Value.deepNoControlFlow] at hw
            | _ =>
              simp only [show n + 1 - 1 = n from rfl]
              exact ih envb henvb
          | continued =>
            simp only [show n + 1 - 1 = n from rfl]
            exact ih envb henvb
          | broke w =>
            exact ⟨henvb, fun v h => by
              simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at h
              subst h; exact hbrkb w rfl,
              fun v h => by simp [pure, Pure.pure, StateT.pure] at h,
              by simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_val]⟩
          | earlyRet | err =>
            refine ⟨henvb, ?_, ?_, ?_⟩ <;>
              simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_earlyRet,
                Outcome.encodeCF3gen_err]
        | false =>
          refine ⟨henvc, fun v h => by
            simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at h; subst h; rfl,
            ?_, ?_⟩ <;>
            simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_val,
              Outcome.encodeCF3gen_err]
      | _ =>
        refine ⟨henvc, ?_, ?_, ?_⟩ <;>
          simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_err]
    | earlyRet | continued | err => fl_error_branch henvc
    | broke w => fl_broke_propagate_gen henvc hbrkc nested

private theorem denoteWhile_combined (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (cond body : ImpExpr)
    (hcond : FLInv bi cond) (hbody : FLInv bi body) :
    ∀ fuel env, Env.NoControlFlow env →
      (denoteWhile bi fuel cond body env).2.NoControlFlow ∧
      (∀ w, (denoteWhile bi fuel cond body env).1 = .val w →
        w.deepNoControlFlow = true) ∧
      (∀ w, (denoteWhile bi fuel cond body env).1 = .broke w →
        w.deepNoControlFlow = true) ∧
      denoteWhile' bi fuel (functionalizeLoops cond) (functionalizeLoops body) env =
        (Outcome.encodeCF3 (denoteWhile bi fuel cond body env).1,
         (denoteWhile bi fuel cond body env).2) := by
  have h := denoteWhile_combined_gen false bi hbi cond body
    ((FLInvGen_false_eq_FLInv bi cond).mpr hcond) hbody
  simp only [Outcome.encodeCF3gen_false_eq, functionalizeLoops] at h
  exact h

/-! ### denoteForLoop never returns broke/continued -/

private theorem denoteForLoop_never_broke (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) (env : Env) (w : Value) :
    (denoteForLoop bi fuel var lo hi body env).1 ≠ .broke w := by
  induction fuel generalizing lo env with
  | zero =>
    unfold denoteForLoop; split
    · simp [pure, Pure.pure, StateT.pure]
    · simp [pure, Pure.pure, StateT.pure]
  | succ n ih =>
    unfold denoteForLoop
    by_cases hge : lo ≥ hi
    · simp only [if_pos hge, pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [if_neg hge, show ¬(n + 1 = 0) from by omega, ↓reduceIte]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      generalize denote bi (n + 1) body (Env.extend env var (.int lo)) = pb
      obtain ⟨rb, envb⟩ := pb
      cases rb with
      | val _ => simp only [show n + 1 - 1 = n from rfl]; exact ih (lo + 1) envb
      | continued => simp only [show n + 1 - 1 = n from rfl]; exact ih (lo + 1) envb
      | broke _ => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | earlyRet _ => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | err _ => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h

private theorem denoteForLoop_never_continued (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) (env : Env) :
    (denoteForLoop bi fuel var lo hi body env).1 ≠ .continued := by
  induction fuel generalizing lo env with
  | zero =>
    unfold denoteForLoop; split
    · simp [pure, Pure.pure, StateT.pure]
    · simp [pure, Pure.pure, StateT.pure]
  | succ n ih =>
    unfold denoteForLoop
    by_cases hge : lo ≥ hi
    · simp only [if_pos hge, pure, Pure.pure, StateT.pure]; intro h; exact Outcome.noConfusion h
    · simp only [if_neg hge, show ¬(n + 1 = 0) from by omega, ↓reduceIte]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      generalize denote bi (n + 1) body (Env.extend env var (.int lo)) = pb
      obtain ⟨rb, envb⟩ := pb
      cases rb with
      | val _ => simp only [show n + 1 - 1 = n from rfl]; exact ih (lo + 1) envb
      | continued => simp only [show n + 1 - 1 = n from rfl]; exact ih (lo + 1) envb
      | broke _ => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | earlyRet _ => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h
      | err _ => simp only [StateT.pure]; intro h; exact Outcome.noConfusion h

private theorem denoteForLoop_encodeCF3_id (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) (env : Env) :
    Outcome.encodeCF3 (denoteForLoop bi fuel var lo hi body env).1 =
      (denoteForLoop bi fuel var lo hi body env).1 := by
  cases h : (denoteForLoop bi fuel var lo hi body env).1 with
  | val => rfl
  | earlyRet => rfl
  | err => rfl
  | broke w => exact absurd h (denoteForLoop_never_broke bi fuel var lo hi body env w)
  | continued => exact absurd h (denoteForLoop_never_continued bi fuel var lo hi body env)

/-! ### denoteForLoop + denoteWhile combined correctness for Return variants -/

/-- Same as `denoteForLoop_encodeCF3_id` but for `encodeCF3gen nested`. -/
private theorem denoteForLoop_encodeCF3gen_id (bi : Builtins) (fuel : Nat) (nested : Bool)
    (var : String) (lo hi : Int) (body : ImpExpr) (env : Env) :
    Outcome.encodeCF3gen nested (denoteForLoop bi fuel var lo hi body env).1 =
      (denoteForLoop bi fuel var lo hi body env).1 := by
  cases h : (denoteForLoop bi fuel var lo hi body env).1 with
  | val => simp only [Outcome.encodeCF3gen_val]
  | earlyRet => simp only [Outcome.encodeCF3gen_earlyRet]
  | err => simp only [Outcome.encodeCF3gen_err]
  | broke w => exact absurd h (denoteForLoop_never_broke bi fuel var lo hi body env w)
  | continued => exact absurd h (denoteForLoop_never_continued bi fuel var lo hi body env)

/-- For-loop combined correctness for the Return variant.
    Relates `denoteForLoop` (original semantics) to `denoteForLoop'Return`
    (CF-aware semantics for loops with earlyReturn in body).
    The body uses `FLInvGen true` (nested encoding). -/
private theorem denoteForLoop_combined_return (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (body : ImpExpr) (hbody : FLInvGen true bi body) :
    ∀ fuel var_name lo_val hi_val env, Env.NoControlFlow env →
      (denoteForLoop bi fuel var_name lo_val hi_val body env).2.NoControlFlow ∧
      (∀ w, (denoteForLoop bi fuel var_name lo_val hi_val body env).1 = .val w →
        w.deepNoControlFlow = true) ∧
      (∀ w, (denoteForLoop bi fuel var_name lo_val hi_val body env).1 = .broke w →
        w.deepNoControlFlow = true) ∧
      denoteForLoop'Return bi fuel var_name lo_val hi_val
          (functionalizeLoopsAux true body) env =
        (Outcome.encodeCF3 (denoteForLoop bi fuel var_name lo_val hi_val body env).1,
         (denoteForLoop bi fuel var_name lo_val hi_val body env).2) := by
  intro fuel; induction fuel with
  | zero =>
    intro var_name lo_val hi_val env henv
    unfold denoteForLoop denoteForLoop'Return
    split
    · exact ⟨henv, fun v h => by
        simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at h; subst h; rfl,
        fun v h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩
    · split
      · exact ⟨henv, fun v h => by simp [pure, Pure.pure, StateT.pure] at h,
          fun v h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩
      · omega
  | succ n ih =>
    intro var_name lo_val hi_val env henv
    unfold denoteForLoop denoteForLoop'Return
    by_cases hge : lo_val ≥ hi_val
    · simp only [if_pos hge]
      exact ⟨henv, fun v h => by
        simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at h; subst h; rfl,
        fun v h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩
    · have hfuel : ¬(n + 1 = 0) := by omega
      simp only [if_neg hge, if_neg hfuel]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      have hint : (Value.int lo_val).deepNoControlFlow = true := rfl
      have henv' : (Env.extend env var_name (.int lo_val)).NoControlFlow := henv.extend hint
      obtain ⟨henvb, hncb, hbrkb, hsimb⟩ :=
        hbody (n + 1) (Env.extend env var_name (.int lo_val)) henv'
      generalize hpb : denote bi (n + 1) body (Env.extend env var_name (.int lo_val)) = pb
        at henvb hncb hbrkb hsimb ⊢
      obtain ⟨rb, envb⟩ := pb
      simp only [Outcome.encodeCF3gen_true_eq] at hsimb
      rw [hsimb]; simp only [Outcome.encodeCF3nested]
      cases rb with
      | val v =>
        have hv := hncb v rfl
        cases v with
        | controlFlow => simp [Value.deepNoControlFlow] at hv
        | _ =>
          -- val (non-CF) → denoteForLoop'Return sees val (non-CF) → continue iterating
          simp only [show n + 1 - 1 = n from rfl]
          exact ih var_name (lo_val + 1) hi_val envb henvb
      | continued =>
        -- continued → encodeCF3nested: val (CF false unit) → denoteForLoop'Return: continue
        simp only [show n + 1 - 1 = n from rfl]
        exact ih var_name (lo_val + 1) hi_val envb henvb
      | broke w =>
        -- broke w → encodeCF3nested: val (CF true (CF false w))
        -- denoteForLoop'Return: loop break → val w
        have hbw := hbrkb w rfl
        exact ⟨henvb, fun v h => by
          simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at h
          subst h; exact hbw,
          fun v h => by simp [pure, Pure.pure, StateT.pure] at h,
          by simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]⟩
      | earlyRet v =>
        -- earlyRet v → encodeCF3nested: earlyRet v
        -- denoteForLoop'Return: other → pure other → earlyRet v
        exact ⟨henvb, fun v h => by simp [pure, Pure.pure, StateT.pure] at h,
          fun v h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩
      | err =>
        exact ⟨henvb, fun v h => by simp [pure, Pure.pure, StateT.pure] at h,
          fun v h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩

/-- Generalized while-loop simulation for the Return variant.
    Uses `FLInvGen nested bi cond` for the condition and `FLInvGen true bi body` for the body.
    Concludes with `encodeCF3gen nested` for the overall result. -/
private theorem denoteWhile_combined_return (nested : Bool)
    (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (cond body : ImpExpr)
    (hcond : FLInvGen nested bi cond) (hbody : FLInvGen true bi body) :
    ∀ fuel env, Env.NoControlFlow env →
      (denoteWhile bi fuel cond body env).2.NoControlFlow ∧
      (∀ w, (denoteWhile bi fuel cond body env).1 = .val w →
        w.deepNoControlFlow = true) ∧
      (∀ w, (denoteWhile bi fuel cond body env).1 = .broke w →
        w.deepNoControlFlow = true) ∧
      denoteWhile'Return bi fuel (functionalizeLoopsAux nested cond)
          (functionalizeLoopsAux true body) env =
        (Outcome.encodeCF3gen nested (denoteWhile bi fuel cond body env).1,
         (denoteWhile bi fuel cond body env).2) := by
  intro fuel; induction fuel with
  | zero =>
    intro env henv
    unfold denoteWhile denoteWhile'Return
    refine ⟨henv, ?_, ?_, ?_⟩ <;>
      simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_err]
  | succ n ih =>
    intro env henv
    unfold denoteWhile denoteWhile'Return
    have hfuel : ¬(n + 1 = 0) := by omega
    simp only [if_neg hfuel]
    simp only [bind, StateT.bind]
    obtain ⟨henvc, hncc, hbrkc, hsimc⟩ := hcond (n + 1) env henv
    generalize hpc : denote bi (n + 1) cond env = pc at henvc hncc hbrkc hsimc ⊢
    obtain ⟨rc, envc⟩ := pc
    rw [hsimc]
    cases rc with
    | val v =>
      simp only [Outcome.encodeCF3gen_val]
      have hv := hncc v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | bool b =>
        cases b with
        | true =>
          -- Evaluate body
          simp only [bind, StateT.bind]
          obtain ⟨henvb, hncb, hbrkb, hsimb⟩ := hbody (n + 1) envc henvc
          generalize hpb : denote bi (n + 1) body envc = pb at henvb hncb hbrkb hsimb ⊢
          obtain ⟨rb, envb⟩ := pb
          simp only [Outcome.encodeCF3gen_true_eq] at hsimb
          rw [hsimb]; simp only [Outcome.encodeCF3nested]
          cases rb with
          | val w =>
            have hw := hncb w rfl
            cases w with
            | controlFlow => simp [Value.deepNoControlFlow] at hw
            | _ =>
              simp only [show n + 1 - 1 = n from rfl]
              exact ih envb henvb
          | continued =>
            simp only [show n + 1 - 1 = n from rfl]
            exact ih envb henvb
          | broke w =>
            have hbw := hbrkb w rfl
            exact ⟨henvb, fun v h => by
              simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at h
              subst h; exact hbw,
              fun v h => by simp [pure, Pure.pure, StateT.pure] at h,
              by simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_val]⟩
          | earlyRet | err =>
            refine ⟨henvb, ?_, ?_, ?_⟩ <;>
              simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_earlyRet,
                Outcome.encodeCF3gen_err]
        | false =>
          refine ⟨henvc, fun v h => by
            simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at h; subst h; rfl,
            ?_, ?_⟩ <;>
            simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_val,
              Outcome.encodeCF3gen_err]
      | _ =>
        refine ⟨henvc, ?_, ?_, ?_⟩ <;>
          simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_err]
    | earlyRet | continued | err => fl_error_branch henvc
    | broke w => fl_broke_propagate_gen henvc hbrkc nested

/-! ### Main theorem

The key simplification from dedicated constructors: `FL_combined` no longer
needs `NoReservedApps`. For the `app` case, since `app` in the source can only
have non-reserved names (reserved names use dedicated constructors), `denote'`
dispatches to `denoteApp'` which is now just the regular builtin call.

For the `forLoop`/`whileLoop` cases, `functionalizeLoopsAux` produces
`.forFold`/`.whileFold` constructors, and `denote'` dispatches to
`denoteForLoop'`/`denoteWhile'` directly — no string matching needed.

The `NoCFConstructors` precondition ensures the 6 dedicated constructors
(forFold, whileFold, forFoldReturn, whileFoldReturn, cfBreak, cfContinue)
don't appear in the source. This is needed because `denote` returns errors
for them, but `denote'` gives real semantics, making FLInv unprovable. -/

/-- Generalized Phase 3 simulation: `functionalizeLoopsAux nested` preserves semantics
    up to `encodeCF3gen nested` on the result, with identical env.

    When `nested = false`: this is the standard `FLInv` (broke → CF true v).
    When `nested = true`: broke → CF true (CF false v) (nested encoding for earlyReturn-in-loops). -/
private theorem FL_combined_gen (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (e : ImpExpr) (hncf : NoCFConstructors e) (nested : Bool) : FLInvGen nested bi e := by
  induction e using ImpExpr.ind generalizing nested with
  | lit v =>
    intro fuel env henv
    simp only [functionalizeLoopsAux]; unfold denote denote'
    refine ⟨henv, fun w hw => ?_, fun w hw => ?_, ?_⟩
    · simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at hw
      subst hw; exact Value.ofLit_deepNoControlFlow v
    · simp [pure, Pure.pure, StateT.pure] at hw
    · simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_val]
  | var n =>
    intro fuel env henv
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold denote; simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
      cases env n <;> simp [pure, Pure.pure, StateT.pure] <;> exact henv
    · unfold denote; simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
      intro w; cases hx : env n with
      | some v =>
        simp [pure, Pure.pure, StateT.pure, Outcome.val.injEq]; intro hw; subst hw
        exact henv n v hx
      | none => simp [pure, Pure.pure, StateT.pure]
    · unfold denote; simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
      intro w; cases env n <;> simp [pure, Pure.pure, StateT.pure]
    · show denote' bi fuel (.var n) env = _; unfold denote denote'
      simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
      cases env n <;> simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_val,
        Outcome.encodeCF3gen_err]
  | unitVal =>
    intro fuel env henv
    simp only [functionalizeLoopsAux]; unfold denote denote'
    refine ⟨henv, fun w hw => ?_, fun w hw => ?_, ?_⟩
    · simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at hw; subst hw; rfl
    · simp [pure, Pure.pure, StateT.pure] at hw
    · simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_val]
  | borrow e ih =>
    intro fuel env henv
    simp only [functionalizeLoopsAux]; unfold denote denote'
    cases hncf with | borrow h => exact ih h nested fuel env henv
  | deref e ih =>
    intro fuel env henv
    simp only [functionalizeLoopsAux]; unfold denote denote'
    cases hncf with | deref h => exact ih h nested fuel env henv
  | letBind name val body ih_val ih_body =>
    cases hncf with | letBind hval hbody =>
    intro fuel env henv
    simp only [functionalizeLoopsAux]; unfold denote denote'
    simp only [bind, StateT.bind]
    obtain ⟨henv_v, hnc_v, hbrk_v, hsim_v⟩ := ih_val hval nested fuel env henv
    generalize hpv : denote bi fuel val env = pv at henv_v hnc_v hbrk_v hsim_v ⊢
    obtain ⟨rv, envv⟩ := pv
    rw [hsim_v]
    cases rv with
    | val v =>
      simp only [Outcome.encodeCF3gen_val]
      have hv := hnc_v v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | _ =>
        simp only [modify, modifyGet, MonadStateOf.modifyGet]
        exact ih_body hbody nested fuel (Env.extend envv name _) (henv_v.extend hv)
    | earlyRet | continued | err => fl_error_branch henv_v
    | broke w => fl_broke_propagate_gen henv_v hbrk_v nested
  | seq e1 e2 ih1 ih2 =>
    cases hncf with | seq h1 h2 =>
    intro fuel env henv
    simp only [functionalizeLoopsAux]; unfold denote denote'
    simp only [bind, StateT.bind]
    obtain ⟨henv1, hnc1, hbrk1, hsim1⟩ := ih1 h1 nested fuel env henv
    generalize hp1 : denote bi fuel e1 env = p1 at henv1 hnc1 hbrk1 hsim1 ⊢
    obtain ⟨r1, env1⟩ := p1
    rw [hsim1]
    cases r1 with
    | val v =>
      simp only [Outcome.encodeCF3gen_val]
      have hv := hnc1 v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | _ => exact ih2 h2 nested fuel env1 henv1
    | earlyRet | continued | err => fl_error_branch henv1
    | broke w => fl_broke_propagate_gen henv1 hbrk1 nested
  | proj e i ih =>
    cases hncf with | proj he =>
    intro fuel env henv
    simp only [functionalizeLoopsAux]; unfold denote denote'
    simp only [bind, StateT.bind]
    obtain ⟨henv_e, hnc_e, hbrk_e, hsim_e⟩ := ih he nested fuel env henv
    generalize hpe : denote bi fuel e env = pe at henv_e hnc_e hbrk_e hsim_e ⊢
    obtain ⟨re, enve⟩ := pe
    rw [hsim_e]
    cases re with
    | val v =>
      simp only [Outcome.encodeCF3gen_val]
      have hv := hnc_e v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | _ =>
        simp only []
        cases hp : Value.projIdx _ i with
        | some vi =>
          refine ⟨henv_e, fun w hw => ?_, fun w hw => ?_,
            by simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_val]⟩
          · simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at hw
            subst hw; exact Value.deepNoControlFlow_projIdx hv hp
          · simp [pure, Pure.pure, StateT.pure] at hw
        | none =>
          refine ⟨henv_e, ?_, ?_, ?_⟩ <;>
            simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_err]
    | earlyRet | continued | err => fl_error_branch henv_e
    | broke w => fl_broke_propagate_gen henv_e hbrk_e nested
  | ifThenElse c t el ih_c ih_t ih_e =>
    cases hncf with | ifThenElse hc ht hel =>
    intro fuel env henv
    simp only [functionalizeLoopsAux]; unfold denote denote'
    simp only [bind, StateT.bind]
    obtain ⟨henv_c, hnc_c, hbrk_c, hsim_c⟩ := ih_c hc nested fuel env henv
    generalize hpc : denote bi fuel c env = pc at henv_c hnc_c hbrk_c hsim_c ⊢
    obtain ⟨rc, envc⟩ := pc
    rw [hsim_c]
    cases rc with
    | val v =>
      simp only [Outcome.encodeCF3gen_val]
      have hv := hnc_c v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | bool b => cases b with
        | true => exact ih_t ht nested fuel envc henv_c
        | false => exact ih_e hel nested fuel envc henv_c
      | _ =>
        refine ⟨henv_c, ?_, ?_, ?_⟩ <;>
          simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_err]
    | earlyRet | continued | err => fl_error_branch henv_c
    | broke w => fl_broke_propagate_gen henv_c hbrk_c nested
  | match_ scrut arms ih_scrut ih_arms =>
    cases hncf with | match_ hs harms_ncf =>
    intro fuel env henv
    simp only [functionalizeLoopsAux, functionalizeLoopsAux.mapArms_eq]
    unfold denote denote'
    simp only [bind, StateT.bind]
    obtain ⟨henv_s, hnc_s, hbrk_s, hsim_s⟩ := ih_scrut hs nested fuel env henv
    generalize hps : denote bi fuel scrut env = ps at henv_s hnc_s hbrk_s hsim_s ⊢
    obtain ⟨rs, envs⟩ := ps
    rw [hsim_s]
    cases rs with
    | val v =>
      simp only [Outcome.encodeCF3gen_val]
      have hv := hnc_s v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | _ =>
        exact denoteMatchArms_combined_gen bi hbi nested fuel _ hv arms
          (fun pa hpa => ih_arms pa hpa (harms_ncf pa hpa) nested) envs henv_s
    | earlyRet | continued | err => fl_error_branch henv_s
    | broke w => fl_broke_propagate_gen henv_s hbrk_s nested
  | assign name rhs ih =>
    cases hncf with | assign hrhs =>
    intro fuel env henv
    simp only [functionalizeLoopsAux]; unfold denote denote'
    simp only [bind, StateT.bind]
    obtain ⟨henv_r, hnc_r, hbrk_r, hsim_r⟩ := ih hrhs nested fuel env henv
    generalize hpr : denote bi fuel rhs env = pr at henv_r hnc_r hbrk_r hsim_r ⊢
    obtain ⟨rr, envr⟩ := pr
    rw [hsim_r]
    cases rr with
    | val v =>
      simp only [Outcome.encodeCF3gen_val]
      have hv := hnc_r v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | _ =>
        dsimp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
        exact ⟨henv_r.extend hv,
          fun w hw => by simp only [Outcome.val.injEq] at hw; cases hw; rfl,
          fun w hw => by simp at hw,
          by simp [Outcome.encodeCF3gen_val]⟩
    | earlyRet | continued | err => fl_error_branch henv_r
    | broke w => fl_broke_propagate_gen henv_r hbrk_r nested
  | earlyReturn e ih =>
    cases hncf with | earlyReturn he =>
    intro fuel env henv
    simp only [functionalizeLoopsAux]; unfold denote denote'
    simp only [bind, StateT.bind]
    obtain ⟨henv_e, hnc_e, hbrk_e, hsim_e⟩ := ih he nested fuel env henv
    generalize hpe : denote bi fuel e env = pe at henv_e hnc_e hbrk_e hsim_e ⊢
    obtain ⟨re, enve⟩ := pe
    rw [hsim_e]
    cases re with
    | val v =>
      simp only [Outcome.encodeCF3gen_val]
      have hv := hnc_e v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | _ =>
        refine ⟨henv_e, ?_, ?_, ?_⟩ <;>
          simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_earlyRet]
    | earlyRet | continued | err => fl_error_branch henv_e
    | broke w => fl_broke_propagate_gen henv_e hbrk_e nested
  | questionMark e ih =>
    cases hncf with | questionMark he =>
    intro fuel env henv
    simp only [functionalizeLoopsAux]; unfold denote denote'
    simp only [bind, StateT.bind]
    obtain ⟨henv_e, hnc_e, hbrk_e, hsim_e⟩ := ih he nested fuel env henv
    generalize hpe : denote bi fuel e env = pe at henv_e hnc_e hbrk_e hsim_e ⊢
    obtain ⟨re, enve⟩ := pe
    rw [hsim_e]
    cases re with
    | val v =>
      simp only [Outcome.encodeCF3gen_val]
      have hv := hnc_e v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | result ok payload =>
        cases ok with
        | true =>
          refine ⟨henv_e, fun w hw => ?_, fun w hw => ?_,
            by simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_val]⟩
          · simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at hw
            subst hw; simp [Value.deepNoControlFlow] at hv; exact hv
          · simp [pure, Pure.pure, StateT.pure] at hw
        | false =>
          refine ⟨henv_e, ?_, ?_, ?_⟩ <;>
            simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_earlyRet]
      | _ =>
        refine ⟨henv_e, ?_, ?_, ?_⟩ <;>
          simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_err]
    | earlyRet | continued | err => fl_error_branch henv_e
    | broke w => fl_broke_propagate_gen henv_e hbrk_e nested
  | app f args ih =>
    cases hncf with | app hargs_ncf =>
    intro fuel env henv
    simp only [functionalizeLoopsAux, functionalizeLoopsAux.mapExpr_eq]
    unfold denote; unfold denote'; unfold denoteApp'
    simp only [bind, StateT.bind]
    have hih : ∀ e ∈ args, FLInvGen nested bi e :=
      fun e he => ih e he (hargs_ncf e he) nested
    obtain ⟨henv_a, hnc_a, hsim_a⟩ := denoteArgs_combined_gen bi hbi nested fuel args hih env henv
    generalize hpa : denoteArgs bi fuel args env = pa at henv_a hnc_a hsim_a ⊢
    obtain ⟨ma, enva⟩ := pa
    rw [hsim_a]; simp only []
    cases ma with
    | some vals =>
      simp only []
      have hvals := hnc_a vals rfl
      cases hb : bi f vals with
      | some v =>
        simp only [hb]
        refine ⟨henv_a, fun w hw => ?_, fun w hw => ?_, ?_⟩
        · simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at hw
          cases hw; exact hbi f vals v hb hvals
        · simp [pure, Pure.pure, StateT.pure] at hw
        · simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_val]
      | none =>
        simp only [hb]
        refine ⟨henv_a, ?_, ?_, ?_⟩ <;>
          simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_err]
    | none =>
      simp only []
      refine ⟨henv_a, ?_, ?_, ?_⟩ <;>
        simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_err]
  | tuple elems ih =>
    cases hncf with | tuple helems_ncf =>
    intro fuel env henv
    simp only [functionalizeLoopsAux, functionalizeLoopsAux.mapExpr_eq]
    unfold denote denote'
    simp only [bind, StateT.bind]
    have hih : ∀ e ∈ elems, FLInvGen nested bi e :=
      fun e he => ih e he (helems_ncf e he) nested
    obtain ⟨henv_a, hnc_a, hsim_a⟩ :=
      denoteArgs_combined_gen bi hbi nested fuel elems hih env henv
    generalize hpa : denoteArgs bi fuel elems env = pa at henv_a hnc_a hsim_a ⊢
    obtain ⟨ma, enva⟩ := pa
    rw [hsim_a]
    cases ma with
    | some vals =>
      refine ⟨henv_a, fun w hw => ?_, fun w hw => ?_,
        by simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_val]⟩
      · simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at hw
        subst hw; simp [Value.deepNoControlFlow]
        exact deepNoControlFlowList_of_forall vals (hnc_a vals rfl)
      · simp [pure, Pure.pure, StateT.pure] at hw
    | none =>
      refine ⟨henv_a, ?_, ?_, ?_⟩ <;>
        simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_err]
  | forLoop v lo hi body ih_lo ih_hi ih_body =>
    cases hncf with | forLoop hlo hhi hbody_ncf =>
    intro fuel env henv
    by_cases hee : checkNoEarlyExit body = true
    · -- No early exit: forFold case
      have hfl : functionalizeLoopsAux nested (.forLoop v lo hi body) =
          .forFold v (functionalizeLoopsAux nested lo) (functionalizeLoopsAux nested hi)
            (functionalizeLoopsAux false body) := by
        simp [functionalizeLoopsAux, hee]
      rw [hfl]
      -- Unfold denote (for .forLoop) and denote' (for .forFold)
      unfold denote denote'
      simp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure]
      -- Evaluate lo via IH
      obtain ⟨henv_lo, hnc_lo, hbrk_lo, hsim_lo⟩ := ih_lo hlo nested fuel env henv
      generalize hplo : denote bi fuel lo env = plo at henv_lo hnc_lo hbrk_lo hsim_lo ⊢
      obtain ⟨rlo, envlo⟩ := plo; simp only [] at *
      rw [hsim_lo]
      -- Evaluate hi via IH (denote evaluates both unconditionally)
      obtain ⟨henv_hi, hnc_hi, hbrk_hi, hsim_hi⟩ := ih_hi hhi nested fuel envlo henv_lo
      generalize hphi : denote bi fuel hi envlo = phi at henv_hi hnc_hi hbrk_hi hsim_hi ⊢
      obtain ⟨rhi, envhi⟩ := phi; simp only [] at *
      rw [hsim_hi]
      -- Case split on rlo
      cases rlo with
      | val vlo =>
        have hvlo := hnc_lo vlo rfl
        cases vlo with
        | controlFlow => simp [Value.deepNoControlFlow] at hvlo
        | int lo_val =>
          -- rlo = val (int lo_val), now case split on rhi
          simp only [Outcome.encodeCF3gen_val]
          cases rhi with
          | val vhi =>
            have hvhi := hnc_hi vhi rfl
            cases vhi with
            | controlFlow => simp [Value.deepNoControlFlow] at hvhi
            | int hi_val =>
              -- Both int: denote' dispatches to denoteForLoop' directly
              simp only [Outcome.encodeCF3gen_val, StateT.pure]
              have hbody_inv : FLInv bi body :=
                (FLInvGen_false_eq_FLInv bi body).mp (ih_body hbody_ncf false)
              obtain ⟨henvfl, hncfl, _, hsimfl⟩ :=
                denoteForLoop_combined bi hbi body hbody_inv
                  fuel v lo_val hi_val envhi henv_hi
              simp only [functionalizeLoops] at hsimfl
              rw [hsimfl]
              exact ⟨henvfl, hncfl,
                fun w hw => absurd hw (denoteForLoop_never_broke bi fuel v lo_val hi_val body envhi w),
                by rw [denoteForLoop_encodeCF3_id, denoteForLoop_encodeCF3gen_id]⟩
            | _ =>
              -- hi = val (non-int, non-CF) → err on both sides
              simp only [Outcome.encodeCF3gen_val]
              dsimp only [StateT.pure, pure, Pure.pure]
              exact ⟨henv_hi,
                fun w hw => by simp [Outcome.val.injEq] at hw,
                fun w hw => by simp [Outcome.val.injEq] at hw,
                by simp [Outcome.encodeCF3gen_val]⟩
          | earlyRet | err =>
            simp only [Outcome.encodeCF3gen_val, Outcome.encodeCF3gen_earlyRet,
              Outcome.encodeCF3gen_err]
            dsimp only [StateT.pure, pure, Pure.pure]
            exact ⟨henv_hi,
              fun w hw => by simp only [Outcome.val.injEq] at hw; subst hw; rfl,
              fun w hw => Outcome.noConfusion hw,
              by simp [Outcome.encodeCF3gen_val]⟩
          | broke w =>
            -- rlo = val (int lo_val), rhi = broke w
            -- denote returns pure rlo = val (int lo_val), denote' sees CF value from encodeCF3gen
            simp only [Outcome.encodeCF3gen_val]
            dsimp only [pure, Pure.pure, StateT.pure]
            refine ⟨henv_hi, fun w' hw => ?_, fun w' hw => ?_, ?_⟩
            · simp only [Outcome.val.injEq] at hw; subst hw; exact hvlo
            · exact Outcome.noConfusion hw
            · cases nested <;>
                simp [Outcome.encodeCF3_broke, Outcome.encodeCF3nested_broke,
                  Outcome.encodeCF3gen_broke_false, Outcome.encodeCF3gen_broke_true,
                  StateT.pure, pure, Pure.pure, Outcome.encodeCF3gen_val]
          | continued =>
            simp only [Outcome.encodeCF3gen_val, Outcome.encodeCF3gen_continued]
            dsimp only [StateT.pure, pure, Pure.pure]
            exact ⟨henv_hi,
              fun w' hw => by simp only [Outcome.val.injEq] at hw; subst hw; rfl,
              fun w' hw => Outcome.noConfusion hw,
              by simp [Outcome.encodeCF3gen_val]⟩
        | _ =>
          -- lo = val (non-int, non-CF): case split on rhi
          simp only [Outcome.encodeCF3gen_val]
          cases rhi with
          | val vhi =>
            have hvhi := hnc_hi vhi rfl
            cases vhi with
            | controlFlow => simp [Value.deepNoControlFlow] at hvhi
            | _ =>
              simp only [Outcome.encodeCF3gen_val]
              dsimp only [StateT.pure, pure, Pure.pure]
              exact ⟨henv_hi,
                fun w hw => by simp at hw,
                fun w hw => by simp at hw,
                by simp [Outcome.encodeCF3gen_val]⟩
          | broke w =>
            -- rlo = val (non-int, non-CF), rhi = broke w
            refine ⟨henv_hi, fun w' hw => ?_, fun w' hw => ?_, ?_⟩
            · cases nested <;> simp [Outcome.encodeCF3_broke, Outcome.encodeCF3nested_broke,
                StateT.pure, pure, Pure.pure] at hw <;> subst hw <;> exact hvlo
            · cases nested <;> simp [Outcome.encodeCF3_broke, Outcome.encodeCF3nested_broke,
                StateT.pure, pure, Pure.pure] at hw
            · cases nested <;>
                simp [Outcome.encodeCF3_val, Outcome.encodeCF3_broke,
                  Outcome.encodeCF3nested_val, Outcome.encodeCF3nested_broke,
                  Outcome.encodeCF3gen_broke_false, Outcome.encodeCF3gen_broke_true,
                  StateT.pure, pure, Pure.pure, Outcome.encodeCF3gen_val]
          | continued =>
            simp only [Outcome.encodeCF3gen_val, Outcome.encodeCF3gen_continued]
            dsimp only [StateT.pure, pure, Pure.pure]
            exact ⟨henv_hi,
              fun w' hw => Outcome.val.inj hw ▸ hvlo,
              fun w' hw => Outcome.noConfusion hw,
              by simp [Outcome.encodeCF3gen_val]⟩
          | earlyRet | err =>
            simp only [Outcome.encodeCF3gen_val, Outcome.encodeCF3gen_earlyRet,
              Outcome.encodeCF3gen_err]
            dsimp only [StateT.pure, pure, Pure.pure]
            exact ⟨henv_hi,
              fun w' hw => Outcome.val.inj hw ▸ hvlo,
              fun w' hw => Outcome.noConfusion hw,
              by simp [Outcome.encodeCF3gen_val, Outcome.encodeCF3gen_earlyRet,
                Outcome.encodeCF3gen_err]⟩
      | earlyRet | err =>
        -- rlo = earlyRet/err: denote returns rlo, denote' returns rlo
        refine ⟨henv_hi, fun w hw => Outcome.noConfusion hw,
          fun w hw => Outcome.noConfusion hw, ?_⟩
        cases rhi with
        | val w =>
          cases w <;> simp [Outcome.encodeCF3gen_earlyRet, Outcome.encodeCF3gen_err,
            Outcome.encodeCF3gen_val, StateT.pure, pure, Pure.pure]
        | _ =>
          cases nested <;> simp [Outcome.encodeCF3, Outcome.encodeCF3nested,
            Outcome.encodeCF3gen_earlyRet, Outcome.encodeCF3gen_err,
            Outcome.encodeCF3gen_broke_false, Outcome.encodeCF3gen_broke_true,
            Outcome.encodeCF3gen_continued, StateT.pure, pure, Pure.pure]
      | broke w =>
        -- rlo = broke w: denote returns broke w, denote' sees CF-encoded value
        refine ⟨henv_hi, fun w' hw => ?_, fun w' hw => ?_, ?_⟩
        · cases nested <;>
            simp [Outcome.encodeCF3_broke, Outcome.encodeCF3nested_broke,
              StateT.pure, pure, Pure.pure] at hw
        · cases nested <;>
            simp only [Outcome.encodeCF3_broke, Outcome.encodeCF3nested_broke,
              StateT.pure, pure, Pure.pure, Outcome.broke.injEq] at hw <;>
            subst hw <;> exact hbrk_lo _ rfl
        · cases nested <;>
            simp [Outcome.encodeCF3_broke, Outcome.encodeCF3nested_broke,
              Outcome.encodeCF3gen_broke_false, Outcome.encodeCF3gen_broke_true,
              StateT.pure, pure, Pure.pure]
      | continued =>
        simp only [Outcome.encodeCF3gen_continued]
        dsimp only [StateT.pure, pure, Pure.pure]
        refine ⟨henv_hi, fun w hw => Outcome.noConfusion hw,
          fun w hw => Outcome.noConfusion hw, ?_⟩
        cases nested <;> simp [Outcome.encodeCF3gen_continued, StateT.pure, pure, Pure.pure]
    · -- Early exit in body: forFoldReturn case
      have hee' : checkNoEarlyExit body = false := by
        cases h : checkNoEarlyExit body <;> simp_all
      have hfl : functionalizeLoopsAux nested (.forLoop v lo hi body) =
          .forFoldReturn v (functionalizeLoopsAux nested lo) (functionalizeLoopsAux nested hi)
            (functionalizeLoopsAux true body) := by
        simp [functionalizeLoopsAux, hee']
      rw [hfl]
      -- Unfold denote (for .forLoop) and denote' (for .forFoldReturn)
      unfold denote denote'
      simp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure]
      -- Evaluate lo via IH
      obtain ⟨henv_lo, hnc_lo, hbrk_lo, hsim_lo⟩ := ih_lo hlo nested fuel env henv
      generalize hplo : denote bi fuel lo env = plo at henv_lo hnc_lo hbrk_lo hsim_lo ⊢
      obtain ⟨rlo, envlo⟩ := plo; simp only [] at *
      rw [hsim_lo]
      -- Evaluate hi via IH
      obtain ⟨henv_hi, hnc_hi, hbrk_hi, hsim_hi⟩ := ih_hi hhi nested fuel envlo henv_lo
      generalize hphi : denote bi fuel hi envlo = phi at henv_hi hnc_hi hbrk_hi hsim_hi ⊢
      obtain ⟨rhi, envhi⟩ := phi; simp only [] at *
      rw [hsim_hi]
      -- Case split on rlo
      cases rlo with
      | val vlo =>
        have hvlo := hnc_lo vlo rfl
        cases vlo with
        | controlFlow => simp [Value.deepNoControlFlow] at hvlo
        | int lo_val =>
          simp only [Outcome.encodeCF3gen_val]
          cases rhi with
          | val vhi =>
            have hvhi := hnc_hi vhi rfl
            cases vhi with
            | controlFlow => simp [Value.deepNoControlFlow] at hvhi
            | int hi_val =>
              simp only [Outcome.encodeCF3gen_val, StateT.pure]
              obtain ⟨henvfl, hncfl, _, hsimfl⟩ :=
                denoteForLoop_combined_return bi hbi body (ih_body hbody_ncf true)
                  fuel v lo_val hi_val envhi henv_hi
              rw [hsimfl]
              exact ⟨henvfl, hncfl,
                fun w hw => absurd hw
                  (denoteForLoop_never_broke bi fuel v lo_val hi_val body envhi w),
                by rw [denoteForLoop_encodeCF3_id, denoteForLoop_encodeCF3gen_id]⟩
            | _ =>
              simp only [Outcome.encodeCF3gen_val]
              dsimp only [StateT.pure, pure, Pure.pure]
              exact ⟨henv_hi,
                fun w hw => by simp [Outcome.val.injEq] at hw,
                fun w hw => by simp [Outcome.val.injEq] at hw,
                by simp [Outcome.encodeCF3gen_val]⟩
          | earlyRet | err =>
            simp only [Outcome.encodeCF3gen_val, Outcome.encodeCF3gen_earlyRet,
              Outcome.encodeCF3gen_err]
            dsimp only [StateT.pure, pure, Pure.pure]
            exact ⟨henv_hi,
              fun w hw => by simp only [Outcome.val.injEq] at hw; subst hw; rfl,
              fun w hw => Outcome.noConfusion hw,
              by simp [Outcome.encodeCF3gen_val]⟩
          | broke w =>
            simp only [Outcome.encodeCF3gen_val]
            dsimp only [pure, Pure.pure, StateT.pure]
            refine ⟨henv_hi, fun w' hw => ?_, fun w' hw => ?_, ?_⟩
            · simp only [Outcome.val.injEq] at hw; subst hw; exact hvlo
            · exact Outcome.noConfusion hw
            · cases nested <;>
                simp [Outcome.encodeCF3_broke, Outcome.encodeCF3nested_broke,
                  Outcome.encodeCF3gen_broke_false, Outcome.encodeCF3gen_broke_true,
                  StateT.pure, pure, Pure.pure, Outcome.encodeCF3gen_val]
          | continued =>
            simp only [Outcome.encodeCF3gen_val, Outcome.encodeCF3gen_continued]
            dsimp only [StateT.pure, pure, Pure.pure]
            exact ⟨henv_hi,
              fun w' hw => by simp only [Outcome.val.injEq] at hw; subst hw; rfl,
              fun w' hw => Outcome.noConfusion hw,
              by simp [Outcome.encodeCF3gen_val]⟩
        | _ =>
          simp only [Outcome.encodeCF3gen_val]
          cases rhi with
          | val vhi =>
            have hvhi := hnc_hi vhi rfl
            cases vhi with
            | controlFlow => simp [Value.deepNoControlFlow] at hvhi
            | _ =>
              simp only [Outcome.encodeCF3gen_val]
              dsimp only [StateT.pure, pure, Pure.pure]
              exact ⟨henv_hi,
                fun w hw => by simp at hw,
                fun w hw => by simp at hw,
                by simp [Outcome.encodeCF3gen_val]⟩
          | broke w =>
            refine ⟨henv_hi, fun w' hw => ?_, fun w' hw => ?_, ?_⟩
            · cases nested <;> simp [Outcome.encodeCF3_broke, Outcome.encodeCF3nested_broke,
                StateT.pure, pure, Pure.pure] at hw <;> subst hw <;> exact hvlo
            · cases nested <;> simp [Outcome.encodeCF3_broke, Outcome.encodeCF3nested_broke,
                StateT.pure, pure, Pure.pure] at hw
            · cases nested <;>
                simp [Outcome.encodeCF3_val, Outcome.encodeCF3_broke,
                  Outcome.encodeCF3nested_val, Outcome.encodeCF3nested_broke,
                  Outcome.encodeCF3gen_broke_false, Outcome.encodeCF3gen_broke_true,
                  StateT.pure, pure, Pure.pure, Outcome.encodeCF3gen_val]
          | continued =>
            simp only [Outcome.encodeCF3gen_val, Outcome.encodeCF3gen_continued]
            dsimp only [StateT.pure, pure, Pure.pure]
            exact ⟨henv_hi,
              fun w' hw => Outcome.val.inj hw ▸ hvlo,
              fun w' hw => Outcome.noConfusion hw,
              by simp [Outcome.encodeCF3gen_val]⟩
          | earlyRet | err =>
            simp only [Outcome.encodeCF3gen_val, Outcome.encodeCF3gen_earlyRet,
              Outcome.encodeCF3gen_err]
            dsimp only [StateT.pure, pure, Pure.pure]
            exact ⟨henv_hi,
              fun w' hw => Outcome.val.inj hw ▸ hvlo,
              fun w' hw => Outcome.noConfusion hw,
              by simp [Outcome.encodeCF3gen_val, Outcome.encodeCF3gen_earlyRet,
                Outcome.encodeCF3gen_err]⟩
      | earlyRet | err =>
        refine ⟨henv_hi, fun w hw => Outcome.noConfusion hw,
          fun w hw => Outcome.noConfusion hw, ?_⟩
        cases rhi with
        | val w =>
          cases w <;> simp [Outcome.encodeCF3gen_earlyRet, Outcome.encodeCF3gen_err,
            Outcome.encodeCF3gen_val, StateT.pure, pure, Pure.pure]
        | _ =>
          cases nested <;> simp [Outcome.encodeCF3, Outcome.encodeCF3nested,
            Outcome.encodeCF3gen_earlyRet, Outcome.encodeCF3gen_err,
            Outcome.encodeCF3gen_broke_false, Outcome.encodeCF3gen_broke_true,
            Outcome.encodeCF3gen_continued, StateT.pure, pure, Pure.pure]
      | broke w =>
        refine ⟨henv_hi, fun w' hw => ?_, fun w' hw => ?_, ?_⟩
        · cases nested <;>
            simp [Outcome.encodeCF3_broke, Outcome.encodeCF3nested_broke,
              StateT.pure, pure, Pure.pure] at hw
        · cases nested <;>
            simp only [Outcome.encodeCF3_broke, Outcome.encodeCF3nested_broke,
              StateT.pure, pure, Pure.pure, Outcome.broke.injEq] at hw <;>
            subst hw <;> exact hbrk_lo _ rfl
        · cases nested <;>
            simp [Outcome.encodeCF3_broke, Outcome.encodeCF3nested_broke,
              Outcome.encodeCF3gen_broke_false, Outcome.encodeCF3gen_broke_true,
              StateT.pure, pure, Pure.pure]
      | continued =>
        simp only [Outcome.encodeCF3gen_continued]
        dsimp only [StateT.pure, pure, Pure.pure]
        refine ⟨henv_hi, fun w hw => Outcome.noConfusion hw,
          fun w hw => Outcome.noConfusion hw, ?_⟩
        cases nested <;> simp [Outcome.encodeCF3gen_continued, StateT.pure, pure, Pure.pure]
  | whileLoop c body ih_c ih_b =>
    cases hncf with | whileLoop hc hb =>
    intro fuel env henv
    by_cases hee : checkNoEarlyExit body = true
    · -- No early exit: whileFold case
      have hfl : functionalizeLoopsAux nested (.whileLoop c body) =
          .whileFold (functionalizeLoopsAux nested c) (functionalizeLoopsAux false body) := by
        simp [functionalizeLoopsAux, hee]
      rw [hfl]; unfold denote
      -- Unfold denote' side: .whileFold dispatches to denoteWhile' directly
      unfold denote'
      have hb_inv : FLInv bi body := (FLInvGen_false_eq_FLInv bi body).mp (ih_b hb false)
      obtain ⟨henvw, hncw, hbrkw, hsimw⟩ :=
        denoteWhile_combined_gen nested bi hbi c body (ih_c hc nested) hb_inv fuel env henv
      simp only [functionalizeLoops] at hsimw
      rw [hsimw]
      exact ⟨henvw, hncw, hbrkw, rfl⟩
    · -- Early exit in body: whileFoldReturn case
      have hee' : checkNoEarlyExit body = false := by
        cases h : checkNoEarlyExit body <;> simp_all
      have hfl : functionalizeLoopsAux nested (.whileLoop c body) =
          .whileFoldReturn (functionalizeLoopsAux nested c) (functionalizeLoopsAux true body) := by
        simp [functionalizeLoopsAux, hee']
      rw [hfl]; unfold denote
      -- Unfold denote' side: .whileFoldReturn dispatches to denoteWhile'Return directly
      unfold denote'
      obtain ⟨henvw, hncw, hbrkw, hsimw⟩ :=
        denoteWhile_combined_return nested bi hbi c body (ih_c hc nested) (ih_b hb true)
          fuel env henv
      rw [hsimw]
      exact ⟨henvw, hncw, hbrkw, rfl⟩
  | break_some e ih =>
    cases hncf with | break_some he =>
    intro fuel env henv
    unfold denote
    cases nested with
    | false =>
      -- nested=false: FL false (break_ (some e)) = .cfBreak (FL false e)
      have hfl : functionalizeLoopsAux false (.break_ (some e)) =
          .cfBreak (functionalizeLoopsAux false e) := by
        simp [functionalizeLoopsAux]
      rw [hfl]; unfold denote'
      simp only [bind, StateT.bind]
      obtain ⟨henv_e, hnc_e, hbrk_e, hsim_e⟩ := ih he false fuel env henv
      generalize hpe : denote bi fuel e env = pe at henv_e hnc_e hbrk_e hsim_e ⊢
      obtain ⟨re, enve⟩ := pe; simp only [] at *
      rw [hsim_e]; simp only [Outcome.encodeCF3gen_false_eq, Outcome.encodeCF3]
      cases re with
      | val v =>
        have hv := hnc_e v rfl
        cases v with
        | controlFlow => simp [Value.deepNoControlFlow] at hv
        | _ =>
          refine ⟨henv_e, ?_, fun w hw => ?_, ?_⟩
          · intro w hw; simp [pure, Pure.pure, StateT.pure] at hw
          · simp only [pure, Pure.pure, StateT.pure, Outcome.broke.injEq] at hw
            subst hw; exact hv
          · simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
      | earlyRet | continued | err =>
        refine ⟨henv_e, fun w hw => ?_, fun w hw => ?_, ?_⟩ <;>
          simp_all [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
      | broke w =>
        refine ⟨henv_e, fun w' hw => ?_, fun w' hw => ?_, ?_⟩
        · simp [pure, Pure.pure, StateT.pure] at hw
        · simp only [pure, Pure.pure, StateT.pure, Outcome.broke.injEq] at hw
          subst hw; exact hbrk_e _ rfl
        · simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
    | true =>
      -- nested=true: FL true (break_ (some e)) = .cfBreakContinue (FL true e)
      have hfl : functionalizeLoopsAux true (.break_ (some e)) =
          .cfBreakContinue (functionalizeLoopsAux true e) := by
        simp [functionalizeLoopsAux]
      rw [hfl]; unfold denote'
      simp only [bind, StateT.bind]
      obtain ⟨henv_e, hnc_e, hbrk_e, hsim_e⟩ := ih he true fuel env henv
      generalize hpe : denote bi fuel e env = pe at henv_e hnc_e hbrk_e hsim_e ⊢
      obtain ⟨re, enve⟩ := pe; simp only [] at *
      rw [hsim_e]; simp only [Outcome.encodeCF3gen_true_eq, Outcome.encodeCF3nested]
      cases re with
      | val v =>
        have hv := hnc_e v rfl
        cases v with
        | controlFlow => simp [Value.deepNoControlFlow] at hv
        | _ =>
          refine ⟨henv_e, ?_, fun w hw => ?_, ?_⟩
          · intro w hw; simp [pure, Pure.pure, StateT.pure] at hw
          · simp only [pure, Pure.pure, StateT.pure, Outcome.broke.injEq] at hw
            subst hw; exact hv
          · simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3nested]
      | earlyRet | continued | err =>
        refine ⟨henv_e, fun w hw => ?_, fun w hw => ?_, ?_⟩ <;>
          simp_all [pure, Pure.pure, StateT.pure, Outcome.encodeCF3nested]
      | broke w =>
        refine ⟨henv_e, fun w' hw => ?_, fun w' hw => ?_, ?_⟩
        · simp [pure, Pure.pure, StateT.pure] at hw
        · simp only [pure, Pure.pure, StateT.pure, Outcome.broke.injEq] at hw
          subst hw; exact hbrk_e _ rfl
        · simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3nested]
  | break_none =>
    intro fuel env henv
    unfold denote
    cases nested with
    | false =>
      have hfl : functionalizeLoopsAux false (.break_ none) = .cfBreak .unitVal := by
        simp [functionalizeLoopsAux]
      rw [hfl]; unfold denote'
      simp only [bind, StateT.bind, denote']
      refine ⟨henv, ?_, fun w hw => ?_, ?_⟩
      · intro w hw; simp_all [pure, Pure.pure, StateT.pure]
      · simp only [pure, Pure.pure, StateT.pure, Outcome.broke.injEq] at hw; subst hw; rfl
      · simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
    | true =>
      have hfl : functionalizeLoopsAux true (.break_ none) = .cfBreakContinue .unitVal := by
        simp [functionalizeLoopsAux]
      rw [hfl]; unfold denote'
      simp only [bind, StateT.bind, denote']
      refine ⟨henv, ?_, fun w hw => ?_, ?_⟩
      · intro w hw; simp_all [pure, Pure.pure, StateT.pure]
      · simp only [pure, Pure.pure, StateT.pure, Outcome.broke.injEq] at hw; subst hw; rfl
      · simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3nested]
  | continue_ =>
    intro fuel env henv
    -- functionalizeLoopsAux nested .continue_ = .cfContinue .unitVal (same for all nested)
    simp only [functionalizeLoopsAux]; unfold denote
    show _ ∧ _ ∧ _ ∧ denote' bi fuel (.cfContinue .unitVal) env = _
    unfold denote'
    simp only [bind, StateT.bind, denote']
    refine ⟨henv, ?_, ?_, ?_⟩
    · intro w hw; simp [pure, Pure.pure, StateT.pure] at hw
    · intro w hw; simp [pure, Pure.pure, StateT.pure] at hw
    · simp only [pure, Pure.pure, StateT.pure, Outcome.encodeCF3gen_continued]
  -- Dedicated Phase 3/4 constructors: impossible by NoCFConstructors
  | forFold => exact absurd hncf NoCFConstructors.not_forFold
  | whileFold => exact absurd hncf NoCFConstructors.not_whileFold
  | forFoldReturn => exact absurd hncf NoCFConstructors.not_forFoldReturn
  | whileFoldReturn => exact absurd hncf NoCFConstructors.not_whileFoldReturn
  | cfBreak => exact absurd hncf NoCFConstructors.not_cfBreak
  | cfContinue => exact absurd hncf NoCFConstructors.not_cfContinue
  | cfBreakContinue => exact absurd hncf NoCFConstructors.not_cfBreakContinue

/-- Phase 3 simulation: `functionalizeLoops` preserves semantics up to
    `Outcome.encodeCF3` on the result, with identical env.

    Requires `NoCFConstructors` because `denote` returns errors for
    dedicated Phase 3/4 constructors while `denote'` evaluates them. -/
theorem FL_combined (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (e : ImpExpr) (hncf : NoCFConstructors e) : FLInv bi e :=
  FL_combined_gen bi hbi e hncf false

end SSProve.Hax

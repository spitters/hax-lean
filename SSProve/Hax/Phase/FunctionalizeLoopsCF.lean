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
-/

namespace SSProve.Hax

/-! ### denoteApp' unfolding lemmas -/

private theorem denoteApp'_break (bi : Builtins) (fuel : Nat) (e : ImpExpr) :
    denoteApp' bi fuel "ControlFlow.Break" [e] = (do
      let r ← denote' bi fuel e
      match r with
      | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
      | .val v => pure (.val (.controlFlow true v))
      | other => pure other) := by
  unfold denoteApp'; simp; rfl

private theorem denoteApp'_continue (bi : Builtins) (fuel : Nat) (e : ImpExpr) :
    denoteApp' bi fuel "ControlFlow.Continue" [e] = (do
      let r ← denote' bi fuel e
      match r with
      | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
      | .val v => pure (.val (.controlFlow false v))
      | other => pure other) := by
  unfold denoteApp'; simp; rfl

private theorem denoteApp'_regular (bi : Builtins) (fuel : Nat) (f : String)
    (args : List ImpExpr)
    (hf1 : f ≠ "for_fold") (hf2 : f ≠ "while_fold")
    (hf3 : f ≠ "ControlFlow.Break") (hf4 : f ≠ "ControlFlow.Continue") :
    denoteApp' bi fuel f args = (do
      let mvals ← denoteArgs' bi fuel args
      match mvals with
      | some vals => match bi f vals with
        | some v => pure (.val v)
        | none => pure (.err s!"unknown function or bad args: {f}")
      | none => pure (.err "non-value in function arguments")) := by
  unfold denoteApp'; simp [hf1, hf2, hf3, hf4]; rfl

private theorem denoteApp'_for_fold (bi : Builtins) (fuel : Nat)
    (v : String) (lo hi body : ImpExpr) (env : Env) :
    denoteApp' bi fuel "for_fold" [.var v, lo, hi, body] env =
    (let plo := denote' bi fuel lo env
     let phi := denote' bi fuel hi plo.2
     match plo.1, phi.1 with
     | .val (.int lo_val), .val (.int hi_val) =>
       denoteForLoop' bi fuel v lo_val hi_val body phi.2
     | .val (.controlFlow _ _), _ => (plo.1, phi.2)
     | _, .val (.controlFlow _ _) => (plo.1, phi.2)
     | .val _, .val _ => (.err "for loop bounds must be integers", phi.2)
     | other, _ => (other, phi.2)) := by
  unfold denoteApp'
  simp only [decide_true, ite_true, String.reduceEq, decide_false, ite_false,
    bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure]
  generalize denote' bi fuel lo env = plo
  obtain ⟨rlo, envlo⟩ := plo; simp only []
  generalize denote' bi fuel hi envlo = phi
  obtain ⟨rhi, envhi⟩ := phi; simp only []
  cases rlo with
  | val v' => cases v' with
    | int => cases rhi with | val w => cases w <;> rfl | _ => rfl
    | controlFlow => rfl
    | _ => cases rhi with | val w => cases w <;> rfl | _ => rfl
  | _ => cases rhi with | val w => cases w <;> rfl | _ => rfl

private theorem denoteApp'_while_fold (bi : Builtins) (fuel : Nat)
    (cond body : ImpExpr) :
    denoteApp' bi fuel "while_fold" [cond, body] =
      denoteWhile' bi fuel cond body := by
  unfold denoteApp'; simp only [String.reduceEq, decide_false, ite_false, decide_true, ite_true]

/-! ### NoReservedApps predicate -/

/-- An expression doesn't use reserved function names introduced by functionalizeLoops.
    This holds for all well-formed Rust programs extracted by hax. -/
inductive NoReservedApps : ImpExpr → Prop where
  | lit {l : ImpLit} : NoReservedApps (.lit l)
  | var {n : String} : NoReservedApps (.var n)
  | letBind {n : String} {val body : ImpExpr} :
      NoReservedApps val → NoReservedApps body →
      NoReservedApps (.letBind n val body)
  | app {f : String} {args : List ImpExpr} :
      f ≠ "for_fold" → f ≠ "while_fold" → f ≠ "ControlFlow.Break" →
      f ≠ "ControlFlow.Continue" → (∀ a ∈ args, NoReservedApps a) →
      NoReservedApps (.app f args)
  | tuple {elems : List ImpExpr} :
      (∀ a ∈ elems, NoReservedApps a) → NoReservedApps (.tuple elems)
  | proj {e : ImpExpr} {i : Nat} :
      NoReservedApps e → NoReservedApps (.proj e i)
  | ifThenElse {c t el : ImpExpr} :
      NoReservedApps c → NoReservedApps t → NoReservedApps el →
      NoReservedApps (.ifThenElse c t el)
  | match_ {scrut : ImpExpr} {arms : List (ImpPat × ImpExpr)} :
      NoReservedApps scrut → (∀ pa ∈ arms, NoReservedApps pa.2) →
      NoReservedApps (.match_ scrut arms)
  | unitVal : NoReservedApps .unitVal
  | seq {e1 e2 : ImpExpr} :
      NoReservedApps e1 → NoReservedApps e2 → NoReservedApps (.seq e1 e2)
  | borrow {e : ImpExpr} : NoReservedApps e → NoReservedApps (.borrow e)
  | deref {e : ImpExpr} : NoReservedApps e → NoReservedApps (.deref e)
  | assign {n : String} {rhs : ImpExpr} :
      NoReservedApps rhs → NoReservedApps (.assign n rhs)
  | forLoop {v : String} {lo hi body : ImpExpr} :
      NoReservedApps lo → NoReservedApps hi →
      NoReservedApps body → NoReservedApps (.forLoop v lo hi body)
  | whileLoop {c body : ImpExpr} :
      NoReservedApps c → NoReservedApps body →
      NoReservedApps (.whileLoop c body)
  | break_some {e : ImpExpr} :
      NoReservedApps e → NoReservedApps (.break_ (some e))
  | break_none : NoReservedApps (.break_ none)
  | continue_ : NoReservedApps .continue_
  | earlyReturn {e : ImpExpr} :
      NoReservedApps e → NoReservedApps (.earlyReturn e)
  | questionMark {e : ImpExpr} :
      NoReservedApps e → NoReservedApps (.questionMark e)

/-! ### Combined invariant -/

/-- The combined invariant: env preservation + deepNoControlFlow + broke + simulation. -/
private abbrev FLInv (bi : Builtins) (e : ImpExpr) : Prop :=
  ∀ fuel env, Env.NoControlFlow env →
    (denote bi fuel e env).2.NoControlFlow ∧
    (∀ v, (denote bi fuel e env).1 = .val v → v.deepNoControlFlow = true) ∧
    (∀ v, (denote bi fuel e env).1 = .broke v → v.deepNoControlFlow = true) ∧
    denote' bi fuel (functionalizeLoops e) env =
      (Outcome.encodeCF3 (denote bi fuel e env).1, (denote bi fuel e env).2)

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

private theorem matchPat_preserves_ncf (pat : ImpPat) (v : Value) (env env' : Env)
    (henv : env.NoControlFlow) (hv : v.deepNoControlFlow = true)
    (hm : matchPat pat v env = some env') : env'.NoControlFlow :=
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
    simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]))

/-- Close goals when broke propagates from a sub-expression via `pure other`. -/
macro "fl_broke_propagate" henv:ident hbrk:ident : tactic =>
  `(tactic| exact ⟨$henv,
    fun v h => by simp [pure, Pure.pure, StateT.pure] at h,
    fun v h => by
      simp only [pure, Pure.pure, StateT.pure, Outcome.broke.injEq] at h; subst h
      exact $hbrk _ rfl,
    by simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]⟩)

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
    obtain ⟨re, enve⟩ := pe; simp only [] at *
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
        obtain ⟨mes, enves⟩ := pes; simp only [] at *
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
      have henv' : env'.NoControlFlow := matchPat_preserves_ncf pat v env env' henv hv hm
      exact hih ⟨pat, body⟩ (.head _) fuel env' henv'

/-! ### Loop simulations -/

private theorem denoteForLoop_combined (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (body : ImpExpr) (hbody : FLInv bi body) :
    ∀ fuel var lo hi env, Env.NoControlFlow env →
      (denoteForLoop bi fuel var lo hi body env).2.NoControlFlow ∧
      (∀ v, (denoteForLoop bi fuel var lo hi body env).1 = .val v →
        v.deepNoControlFlow = true) ∧
      denoteForLoop' bi fuel var lo hi (functionalizeLoops body) env =
        ((denoteForLoop bi fuel var lo hi body env).1,
         (denoteForLoop bi fuel var lo hi body env).2) := by
  intro fuel; induction fuel with
  | zero =>
    intro var lo hi env henv
    unfold denoteForLoop denoteForLoop'
    split
    · exact ⟨henv, fun v h => by
        simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at h; subst h; rfl, rfl⟩
    · split
      · exact ⟨henv, fun v h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩
      · omega
  | succ n ih =>
    intro var lo hi env henv
    unfold denoteForLoop denoteForLoop'
    by_cases hge : lo ≥ hi
    · simp only [if_pos hge]
      exact ⟨henv, fun v h => by
        simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at h; subst h; rfl, rfl⟩
    · have hfuel : ¬(n + 1 = 0) := by omega
      simp only [if_neg hge, if_neg hfuel]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      have hint : (Value.int lo).deepNoControlFlow = true := rfl
      have henv' : (Env.extend env var (.int lo)).NoControlFlow := henv.extend hint
      obtain ⟨henvb, hncb, hbrkb, hsimb⟩ :=
        hbody (n + 1) (Env.extend env var (.int lo)) henv'
      generalize hpb : denote bi (n + 1) body (Env.extend env var (.int lo)) = pb
        at henvb hncb hbrkb hsimb ⊢
      obtain ⟨rb, envb⟩ := pb; simp only [] at *
      rw [hsimb]; simp only [Outcome.encodeCF3]
      cases rb with
      | val v =>
        have hv := hncb v rfl
        cases v with
        | controlFlow => simp [Value.deepNoControlFlow] at hv
        | _ =>
          simp only [show n + 1 - 1 = n from rfl]
          exact ih var (lo + 1) hi envb henvb
      | continued =>
        simp only [show n + 1 - 1 = n from rfl]
        exact ih var (lo + 1) hi envb henvb
      | broke w =>
        exact ⟨henvb, fun v h => by
          simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at h
          subst h; exact hbrkb w rfl, rfl⟩
      | earlyRet =>
        exact ⟨henvb, fun v h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩
      | err =>
        exact ⟨henvb, fun v h => by simp [pure, Pure.pure, StateT.pure] at h, rfl⟩

private theorem denoteWhile_combined (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (cond body : ImpExpr)
    (hcond : FLInv bi cond) (hbody : FLInv bi body) :
    ∀ fuel env, Env.NoControlFlow env →
      (denoteWhile bi fuel cond body env).2.NoControlFlow ∧
      (∀ v, (denoteWhile bi fuel cond body env).1 = .val v →
        v.deepNoControlFlow = true) ∧
      (∀ v, (denoteWhile bi fuel cond body env).1 = .broke v →
        v.deepNoControlFlow = true) ∧
      denoteWhile' bi fuel (functionalizeLoops cond) (functionalizeLoops body) env =
        (Outcome.encodeCF3 (denoteWhile bi fuel cond body env).1,
         (denoteWhile bi fuel cond body env).2) := by
  intro fuel; induction fuel with
  | zero =>
    intro env henv
    unfold denoteWhile denoteWhile'
    refine ⟨henv, ?_, ?_, ?_⟩ <;> simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
  | succ n ih =>
    intro env henv
    unfold denoteWhile denoteWhile'
    have hfuel : ¬(n + 1 = 0) := by omega
    simp only [if_neg hfuel]
    simp only [bind, StateT.bind]
    obtain ⟨henvc, hncc, hbrkc, hsimc⟩ := hcond (n + 1) env henv
    generalize hpc : denote bi (n + 1) cond env = pc at henvc hncc hbrkc hsimc ⊢
    obtain ⟨rc, envc⟩ := pc; simp only [] at *
    rw [hsimc]; simp only [Outcome.encodeCF3]
    cases rc with
    | val v =>
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
          obtain ⟨rb, envb⟩ := pb; simp only [] at *
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
              by simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]⟩
          | earlyRet | err =>
            refine ⟨henvb, ?_, ?_, ?_⟩ <;>
              simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
        | false =>
          refine ⟨henvc, fun v h => by
            simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at h; subst h; rfl,
            ?_, ?_⟩ <;> simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
      | _ =>
        refine ⟨henvc, ?_, ?_, ?_⟩ <;>
          simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
    | earlyRet | continued | err => fl_error_branch henvc
    | broke w => fl_broke_propagate henvc hbrkc

/-! ### denoteForLoop never returns broke -/

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

/-! ### Main theorem -/

theorem FL_combined (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (e : ImpExpr) (hnr : NoReservedApps e) : FLInv bi e := by
  induction e using ImpExpr.ind with
  | lit v =>
    intro fuel env henv
    simp only [functionalizeLoops]; unfold denote denote'
    refine ⟨henv, fun w hw => ?_, fun w hw => ?_, ?_⟩
    · simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at hw
      subst hw; exact Value.ofLit_deepNoControlFlow v
    · simp [pure, Pure.pure, StateT.pure] at hw
    · rfl
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
    · simp only [functionalizeLoops]; unfold denote denote'
      simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
      cases env n <;> simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
  | unitVal =>
    intro fuel env henv
    simp only [functionalizeLoops]; unfold denote denote'
    refine ⟨henv, fun w hw => ?_, fun w hw => ?_, ?_⟩
    · simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at hw; subst hw; rfl
    · simp [pure, Pure.pure, StateT.pure] at hw
    · rfl
  | borrow e ih =>
    intro fuel env henv
    simp only [functionalizeLoops]; unfold denote denote'
    cases hnr with | borrow h => exact ih h fuel env henv
  | deref e ih =>
    intro fuel env henv
    simp only [functionalizeLoops]; unfold denote denote'
    cases hnr with | deref h => exact ih h fuel env henv
  | letBind name val body ih_val ih_body =>
    cases hnr with | letBind hval hbody =>
    intro fuel env henv
    simp only [functionalizeLoops]; unfold denote denote'
    simp only [bind, StateT.bind]
    obtain ⟨henv_v, hnc_v, hbrk_v, hsim_v⟩ := ih_val hval fuel env henv
    generalize hpv : denote bi fuel val env = pv at henv_v hnc_v hbrk_v hsim_v ⊢
    obtain ⟨rv, envv⟩ := pv; simp only [] at *
    rw [hsim_v]; simp only [Outcome.encodeCF3]
    cases rv with
    | val v =>
      have hv := hnc_v v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | _ =>
        simp only [modify, modifyGet, MonadStateOf.modifyGet]
        exact ih_body hbody fuel (Env.extend envv name _) (henv_v.extend hv)
    | earlyRet | continued | err => fl_error_branch henv_v
    | broke w => fl_broke_propagate henv_v hbrk_v
  | seq e1 e2 ih1 ih2 =>
    cases hnr with | seq h1 h2 =>
    intro fuel env henv
    simp only [functionalizeLoops]; unfold denote denote'
    simp only [bind, StateT.bind]
    obtain ⟨henv1, hnc1, hbrk1, hsim1⟩ := ih1 h1 fuel env henv
    generalize hp1 : denote bi fuel e1 env = p1 at henv1 hnc1 hbrk1 hsim1 ⊢
    obtain ⟨r1, env1⟩ := p1; simp only [] at *
    rw [hsim1]; simp only [Outcome.encodeCF3]
    cases r1 with
    | val v =>
      have hv := hnc1 v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | _ => exact ih2 h2 fuel env1 henv1
    | earlyRet | continued | err => fl_error_branch henv1
    | broke w => fl_broke_propagate henv1 hbrk1
  | proj e i ih =>
    cases hnr with | proj he =>
    intro fuel env henv
    simp only [functionalizeLoops]; unfold denote denote'
    simp only [bind, StateT.bind]
    obtain ⟨henv_e, hnc_e, hbrk_e, hsim_e⟩ := ih he fuel env henv
    generalize hpe : denote bi fuel e env = pe at henv_e hnc_e hbrk_e hsim_e ⊢
    obtain ⟨re, enve⟩ := pe; simp only [] at *
    rw [hsim_e]; simp only [Outcome.encodeCF3]
    cases re with
    | val v =>
      have hv := hnc_e v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | _ =>
        simp only []
        cases hp : Value.projIdx _ i with
        | some vi =>
          refine ⟨henv_e, fun w hw => ?_, fun w hw => ?_, rfl⟩
          · simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at hw
            subst hw; exact Value.deepNoControlFlow_projIdx hv hp
          · simp [pure, Pure.pure, StateT.pure] at hw
        | none =>
          refine ⟨henv_e, ?_, ?_, ?_⟩ <;>
            simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
    | earlyRet | continued | err => fl_error_branch henv_e
    | broke w => fl_broke_propagate henv_e hbrk_e
  | ifThenElse c t el ih_c ih_t ih_e =>
    cases hnr with | ifThenElse hc ht hel =>
    intro fuel env henv
    simp only [functionalizeLoops]; unfold denote denote'
    simp only [bind, StateT.bind]
    obtain ⟨henv_c, hnc_c, hbrk_c, hsim_c⟩ := ih_c hc fuel env henv
    generalize hpc : denote bi fuel c env = pc at henv_c hnc_c hbrk_c hsim_c ⊢
    obtain ⟨rc, envc⟩ := pc; simp only [] at *
    rw [hsim_c]; simp only [Outcome.encodeCF3]
    cases rc with
    | val v =>
      have hv := hnc_c v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | bool b => cases b with
        | true => exact ih_t ht fuel envc henv_c
        | false => exact ih_e hel fuel envc henv_c
      | _ =>
        refine ⟨henv_c, ?_, ?_, ?_⟩ <;>
          simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
    | earlyRet | continued | err => fl_error_branch henv_c
    | broke w => fl_broke_propagate henv_c hbrk_c
  | match_ scrut arms ih_scrut ih_arms =>
    cases hnr with | match_ hs harms_nr =>
    intro fuel env henv
    simp only [functionalizeLoops, functionalizeLoops.mapArms_eq]; unfold denote denote'
    simp only [bind, StateT.bind]
    obtain ⟨henv_s, hnc_s, hbrk_s, hsim_s⟩ := ih_scrut hs fuel env henv
    generalize hps : denote bi fuel scrut env = ps at henv_s hnc_s hbrk_s hsim_s ⊢
    obtain ⟨rs, envs⟩ := ps; simp only [] at *
    rw [hsim_s]; simp only [Outcome.encodeCF3]
    cases rs with
    | val v =>
      have hv := hnc_s v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | _ =>
        exact denoteMatchArms_combined bi hbi fuel _ hv arms
          (fun pa hpa => ih_arms pa hpa (harms_nr pa hpa)) envs henv_s
    | earlyRet | continued | err => fl_error_branch henv_s
    | broke w => fl_broke_propagate henv_s hbrk_s
  | assign name rhs ih =>
    cases hnr with | assign hrhs =>
    intro fuel env henv
    simp only [functionalizeLoops]; unfold denote denote'
    simp only [bind, StateT.bind]
    obtain ⟨henv_r, hnc_r, hbrk_r, hsim_r⟩ := ih hrhs fuel env henv
    generalize hpr : denote bi fuel rhs env = pr at henv_r hnc_r hbrk_r hsim_r ⊢
    obtain ⟨rr, envr⟩ := pr; simp only [] at *
    rw [hsim_r]; simp only [Outcome.encodeCF3]
    cases rr with
    | val v =>
      have hv := hnc_r v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | _ =>
        dsimp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
        exact ⟨henv_r.extend hv,
          fun w hw => by simp only [Outcome.val.injEq] at hw; cases hw; rfl,
          fun w hw => by simp at hw,
          rfl⟩
    | earlyRet | continued | err => fl_error_branch henv_r
    | broke w => fl_broke_propagate henv_r hbrk_r
  | earlyReturn e ih =>
    cases hnr with | earlyReturn he =>
    intro fuel env henv
    simp only [functionalizeLoops]; unfold denote denote'
    simp only [bind, StateT.bind]
    obtain ⟨henv_e, hnc_e, hbrk_e, hsim_e⟩ := ih he fuel env henv
    generalize hpe : denote bi fuel e env = pe at henv_e hnc_e hbrk_e hsim_e ⊢
    obtain ⟨re, enve⟩ := pe; simp only [] at *
    rw [hsim_e]; simp only [Outcome.encodeCF3]
    cases re with
    | val v =>
      have hv := hnc_e v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | _ =>
        refine ⟨henv_e, ?_, ?_, ?_⟩ <;>
          simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
    | earlyRet | continued | err => fl_error_branch henv_e
    | broke w => fl_broke_propagate henv_e hbrk_e
  | questionMark e ih =>
    cases hnr with | questionMark he =>
    intro fuel env henv
    simp only [functionalizeLoops]; unfold denote denote'
    simp only [bind, StateT.bind]
    obtain ⟨henv_e, hnc_e, hbrk_e, hsim_e⟩ := ih he fuel env henv
    generalize hpe : denote bi fuel e env = pe at henv_e hnc_e hbrk_e hsim_e ⊢
    obtain ⟨re, enve⟩ := pe; simp only [] at *
    rw [hsim_e]; simp only [Outcome.encodeCF3]
    cases re with
    | val v =>
      have hv := hnc_e v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | result ok payload =>
        cases ok with
        | true =>
          refine ⟨henv_e, fun w hw => ?_, fun w hw => ?_, rfl⟩
          · simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at hw
            subst hw; simp [Value.deepNoControlFlow] at hv; exact hv
          · simp [pure, Pure.pure, StateT.pure] at hw
        | false =>
          refine ⟨henv_e, ?_, ?_, ?_⟩ <;>
            simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
      | _ =>
        refine ⟨henv_e, ?_, ?_, ?_⟩ <;>
          simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
    | earlyRet | continued | err => fl_error_branch henv_e
    | broke w => fl_broke_propagate henv_e hbrk_e
  | app f args ih =>
    cases hnr with | app hf1 hf2 hf3 hf4 hargs_nr =>
    intro fuel env henv
    simp only [functionalizeLoops, functionalizeLoops.mapExpr_eq]
    unfold denote; unfold denote'
    rw [denoteApp'_regular bi fuel f (args.map functionalizeLoops) hf1 hf2 hf3 hf4]
    simp only [bind, StateT.bind]
    have hih : ∀ e ∈ args, FLInv bi e := fun e he => ih e he (hargs_nr e he)
    obtain ⟨henv_a, hnc_a, hsim_a⟩ := denoteArgs_combined bi hbi fuel args hih env henv
    generalize hpa : denoteArgs bi fuel args env = pa at henv_a hnc_a hsim_a ⊢
    obtain ⟨ma, enva⟩ := pa; simp only [] at *
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
        · simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
      | none =>
        simp only [hb]
        refine ⟨henv_a, ?_, ?_, ?_⟩ <;>
          simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
    | none =>
      simp only []
      refine ⟨henv_a, ?_, ?_, ?_⟩ <;>
        simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
  | tuple elems ih =>
    cases hnr with | tuple helems_nr =>
    intro fuel env henv
    simp only [functionalizeLoops, functionalizeLoops.mapExpr_eq]
    unfold denote denote'
    simp only [bind, StateT.bind]
    have hih : ∀ e ∈ elems, FLInv bi e := fun e he => ih e he (helems_nr e he)
    obtain ⟨henv_a, hnc_a, hsim_a⟩ := denoteArgs_combined bi hbi fuel elems hih env henv
    generalize hpa : denoteArgs bi fuel elems env = pa at henv_a hnc_a hsim_a ⊢
    obtain ⟨ma, enva⟩ := pa; simp only [] at *
    rw [hsim_a]
    cases ma with
    | some vals =>
      refine ⟨henv_a, fun w hw => ?_, fun w hw => ?_, rfl⟩
      · simp only [pure, Pure.pure, StateT.pure, Outcome.val.injEq] at hw
        subst hw; simp [Value.deepNoControlFlow]
        exact deepNoControlFlowList_of_forall vals (hnc_a vals rfl)
      · simp [pure, Pure.pure, StateT.pure] at hw
    | none =>
      refine ⟨henv_a, ?_, ?_, ?_⟩ <;>
        simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
  | forLoop v lo hi body ih_lo ih_hi ih_body =>
    cases hnr with | forLoop hlo hhi hbody_nr =>
    intro fuel env henv
    simp only [functionalizeLoops]
    -- Unfold denote (for .forLoop) and denote' (for .app) but NOT denoteApp'
    unfold denote denote'
    simp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure]
    -- Apply denoteApp'_for_fold to get clean match form on 4th component LHS
    rw [denoteApp'_for_fold]
    -- Evaluate lo via IH
    obtain ⟨henv_lo, hnc_lo, hbrk_lo, hsim_lo⟩ := ih_lo hlo fuel env henv
    generalize hplo : denote bi fuel lo env = plo at henv_lo hnc_lo hbrk_lo hsim_lo ⊢
    obtain ⟨rlo, envlo⟩ := plo; simp only [] at *
    rw [hsim_lo]
    -- Evaluate hi via IH (denote evaluates both unconditionally)
    obtain ⟨henv_hi, hnc_hi, hbrk_hi, hsim_hi⟩ := ih_hi hhi fuel envlo henv_lo
    generalize hphi : denote bi fuel hi envlo = phi at henv_hi hnc_hi hbrk_hi hsim_hi ⊢
    obtain ⟨rhi, envhi⟩ := phi; simp only [] at *
    rw [hsim_hi]
    -- Case split on rlo — use cf3_simp to reduce encodeCF3 + match iota-reduction
    -- after each terminal case to get clean goals
    have cf3_simp := @Outcome.encodeCF3_val
    have cf3_simp2 := @Outcome.encodeCF3_earlyRet
    have cf3_simp3 := @Outcome.encodeCF3_err
    have cf3_simp4 := @Outcome.encodeCF3_broke
    have cf3_simp5 := @Outcome.encodeCF3_continued
    cases rlo with
    | val vlo =>
      have hvlo := hnc_lo vlo rfl
      cases vlo with
      | controlFlow => simp [Value.deepNoControlFlow] at hvlo
      | int lo_val =>
        -- rlo = val (int lo_val), now case split on rhi
        cases rhi with
        | val vhi =>
          have hvhi := hnc_hi vhi rfl
          cases vhi with
          | controlFlow => simp [Value.deepNoControlFlow] at hvhi
          | int hi_val =>
            -- Both int: reduce encodeCF3 and force match iota-reduction
            simp only [Outcome.encodeCF3_val, StateT.pure]
            -- Both matches now have known constructors and reduce
            obtain ⟨henvfl, hncfl, hsimfl⟩ :=
              denoteForLoop_combined bi hbi body (ih_body hbody_nr)
                fuel v lo_val hi_val envhi henv_hi
            rw [hsimfl]
            exact ⟨henvfl, hncfl,
              fun w hw => absurd hw (denoteForLoop_never_broke bi fuel v lo_val hi_val body envhi w),
              by rw [denoteForLoop_encodeCF3_id]⟩
          | _ =>
            -- hi = val (non-int, non-CF) → err on both sides
            simp only [Outcome.encodeCF3_val]
            dsimp only [StateT.pure, pure, Pure.pure]
            exact ⟨henv_hi,
              fun w hw => by simp [Outcome.val.injEq] at hw,
              fun w hw => by simp [Outcome.val.injEq] at hw,
              rfl⟩
        | earlyRet | err =>
          -- denote-side: match (.val (.int lo_val), non-val rhi) falls to (other, _)
          -- result is (.val (.int lo_val), envhi) on both sides
          simp only [Outcome.encodeCF3_val, Outcome.encodeCF3_earlyRet, Outcome.encodeCF3_err]
          dsimp only [StateT.pure, pure, Pure.pure]
          exact ⟨henv_hi,
            fun w hw => by simp only [Outcome.val.injEq] at hw; subst hw; rfl,
            fun w hw => Outcome.noConfusion hw,
            rfl⟩
        | broke w =>
          simp only [Outcome.encodeCF3_val, Outcome.encodeCF3_broke]
          dsimp only [StateT.pure, pure, Pure.pure]
          exact ⟨henv_hi,
            fun w' hw => by simp only [Outcome.val.injEq] at hw; subst hw; rfl,
            fun w' hw => Outcome.noConfusion hw,
            rfl⟩
        | continued =>
          simp only [Outcome.encodeCF3_val, Outcome.encodeCF3_continued]
          dsimp only [StateT.pure, pure, Pure.pure]
          exact ⟨henv_hi,
            fun w' hw => by simp only [Outcome.val.injEq] at hw; subst hw; rfl,
            fun w' hw => Outcome.noConfusion hw,
            rfl⟩
      | _ =>
        -- lo = val (non-int, non-CF): case split on rhi
        cases rhi with
        | val vhi =>
          have hvhi := hnc_hi vhi rfl
          cases vhi with
          | controlFlow => simp [Value.deepNoControlFlow] at hvhi
          | _ =>
            simp only [Outcome.encodeCF3_val]
            dsimp only [StateT.pure, pure, Pure.pure]
            exact ⟨henv_hi,
              fun w hw => by simp at hw,
              fun w hw => by simp at hw,
              rfl⟩
        | broke w =>
          simp only [Outcome.encodeCF3_val, Outcome.encodeCF3_broke, StateT.pure]
          refine ⟨henv_hi, fun w' hw => ?_, fun w' hw => ?_, rfl⟩
          · exact Outcome.val.inj hw ▸ hvlo
          · exact Outcome.noConfusion hw
        | continued =>
          simp only [Outcome.encodeCF3_val, Outcome.encodeCF3_continued, StateT.pure]
          refine ⟨henv_hi, fun w' hw => ?_, fun w' hw => ?_, rfl⟩
          · exact Outcome.val.inj hw ▸ hvlo
          · exact Outcome.noConfusion hw
        | earlyRet | err =>
          simp only [Outcome.encodeCF3_val, Outcome.encodeCF3_earlyRet, Outcome.encodeCF3_err,
            StateT.pure]
          refine ⟨henv_hi, fun w' hw => ?_, fun w' hw => ?_, rfl⟩
          · exact Outcome.val.inj hw ▸ hvlo
          · exact Outcome.noConfusion hw
    | earlyRet | err =>
      -- encodeCF3 preserves earlyRet/err; denote-side match reduces (branch 3: other, _)
      -- but denote'-side match gets stuck at branch (_, .val (.controlFlow _ _)) without knowing rhi
      simp only [Outcome.encodeCF3_earlyRet, Outcome.encodeCF3_err]
      refine ⟨henv_hi, fun w hw => Outcome.noConfusion hw,
        fun w hw => Outcome.noConfusion hw, ?_⟩
      -- Case-split on rhi so encodeCF3 rhi reduces and the denote' match can fire
      cases rhi with
      | val w => cases w <;> rfl
      | _ => rfl
    | broke w =>
      -- encodeCF3(broke w) = val(CF true w)
      simp only [Outcome.encodeCF3_broke, StateT.pure]
      refine ⟨henv_hi, fun w' hw => ?_, fun w' hw => ?_, rfl⟩
      · exact Outcome.noConfusion hw
      · exact Outcome.broke.inj hw ▸ (hbrk_lo _ rfl)
    | continued =>
      simp only [Outcome.encodeCF3_continued, StateT.pure]
      refine ⟨henv_hi, fun w hw => ?_, fun w hw => ?_, rfl⟩
      · exact Outcome.noConfusion hw
      · exact Outcome.noConfusion hw
  | whileLoop c body ih_c ih_b =>
    cases hnr with | whileLoop hc hb =>
    intro fuel env henv
    simp only [functionalizeLoops]; unfold denote
    -- Unfold denote' side: app "while_fold" → denoteApp' → denoteWhile'
    have hexp : denote' bi fuel (ImpExpr.app "while_fold"
        [functionalizeLoops c, functionalizeLoops body]) =
        denoteWhile' bi fuel (functionalizeLoops c) (functionalizeLoops body) := by
      unfold denote'; rw [denoteApp'_while_fold]
    rw [hexp]
    exact denoteWhile_combined bi hbi c body (ih_c hc) (ih_b hb) fuel env henv
  | break_some e ih =>
    cases hnr with | break_some he =>
    intro fuel env henv
    simp only [functionalizeLoops]
    unfold denote; unfold denote'
    rw [denoteApp'_break]
    simp only [bind, StateT.bind]
    obtain ⟨henv_e, hnc_e, hbrk_e, hsim_e⟩ := ih he fuel env henv
    generalize hpe : denote bi fuel e env = pe at henv_e hnc_e hbrk_e hsim_e ⊢
    obtain ⟨re, enve⟩ := pe; simp only [] at *
    rw [hsim_e]; simp only [Outcome.encodeCF3]
    cases re with
    | val v =>
      have hv := hnc_e v rfl
      cases v with
      | controlFlow => simp [Value.deepNoControlFlow] at hv
      | _ =>
        -- denote: break_ (some e) with val v → broke v
        -- denote': ControlFlow.Break with val v → val (controlFlow true v)
        -- encodeCF3 (broke v) = val (controlFlow true v) ✓
        refine ⟨henv_e, ?_, fun w hw => ?_, ?_⟩
        · intro w hw; simp [pure, Pure.pure, StateT.pure] at hw
        · simp only [pure, Pure.pure, StateT.pure, Outcome.broke.injEq] at hw
          subst hw; exact hv
        · simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
    | earlyRet | continued | err => fl_error_branch henv_e
    | broke w => fl_broke_propagate henv_e hbrk_e
  | break_none =>
    intro fuel env henv
    simp only [functionalizeLoops]; unfold denote
    show _ ∧ _ ∧ _ ∧ denote' bi fuel (ImpExpr.app "ControlFlow.Break" [.unitVal]) env = _
    unfold denote'
    rw [denoteApp'_break]
    simp only [bind, StateT.bind, denote']
    refine ⟨henv, ?_, fun w hw => ?_, ?_⟩
    · intro w hw; simp [pure, Pure.pure, StateT.pure] at hw
    · simp only [pure, Pure.pure, StateT.pure, Outcome.broke.injEq] at hw; subst hw; rfl
    · simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]
  | continue_ =>
    intro fuel env henv
    simp only [functionalizeLoops]; unfold denote
    show _ ∧ _ ∧ _ ∧ denote' bi fuel (ImpExpr.app "ControlFlow.Continue" [.unitVal]) env = _
    unfold denote'
    rw [denoteApp'_continue]
    simp only [bind, StateT.bind, denote']
    refine ⟨henv, ?_, ?_, ?_⟩ <;> simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF3]

end SSProve.Hax

/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.SemanticsCF
import SSProve.Hax.Phase.CfIntoMonads
import SSProve.Hax.Phase.FunctionalizeLoopsCF

/-!
# Phase 4 Correctness: Control Flow into Monads

Proves that `cfIntoMonads` preserves denotational semantics (under `denote'`)
up to `Outcome.encodeCF4` encoding (`earlyRet v` → `val (controlFlow true v)`).

## Main results

* `CF4_combined` — simulation theorem for all expressions

## Preconditions

* `NoLoops e` — no `forLoop`, `whileLoop`, `break_`, or `continue_`
* `NoQuestionMark e` — no `questionMark` subexpressions
* `NoReservedApps e` — no `for_fold`/`while_fold`/`ControlFlow.Break`/`Continue` apps
-/

namespace SSProve.Hax

/-- `pure x s = (x, s)` for `StateM Env Outcome`. -/
@[simp] private theorem stateM_pure_apply (o : Outcome) (s : Env) :
    @Pure.pure (StateM Env) _ Outcome o s = (o, s) := rfl

@[simp] private theorem stateM_pure_apply' (o : Outcome) (s : Env) :
    @StateT.pure Env Id _ Outcome o s = (o, s) := rfl

/-- If `encodeCF4` is identity on the outcome component, the pair is unchanged. -/
private theorem pair_eq_encodeCF4 (p : Outcome × Env) (h : p.1.encodeCF4 = p.1) :
    p = (p.1.encodeCF4, p.2) := by rw [h, Prod.eta]

/-! ### NoQuestionMark predicate -/

/-- An expression contains no `questionMark` nodes. -/
inductive NoQuestionMark : ImpExpr → Prop where
  | lit {v} : NoQuestionMark (.lit v)
  | var {n} : NoQuestionMark (.var n)
  | letBind {n val body} : NoQuestionMark val → NoQuestionMark body →
      NoQuestionMark (.letBind n val body)
  | app {f args} : (∀ a, a ∈ args → NoQuestionMark a) →
      NoQuestionMark (.app f args)
  | tuple {elems} : (∀ a, a ∈ elems → NoQuestionMark a) →
      NoQuestionMark (.tuple elems)
  | proj {e i} : NoQuestionMark e → NoQuestionMark (.proj e i)
  | ifThenElse {c t e} : NoQuestionMark c → NoQuestionMark t → NoQuestionMark e →
      NoQuestionMark (.ifThenElse c t e)
  | match_ {scrut arms} : NoQuestionMark scrut →
      (∀ pa, pa ∈ arms → NoQuestionMark pa.2) →
      NoQuestionMark (.match_ scrut arms)
  | unitVal : NoQuestionMark .unitVal
  | seq {e1 e2} : NoQuestionMark e1 → NoQuestionMark e2 →
      NoQuestionMark (.seq e1 e2)
  | borrow {e} : NoQuestionMark e → NoQuestionMark (.borrow e)
  | deref {e} : NoQuestionMark e → NoQuestionMark (.deref e)
  | assign {n rhs} : NoQuestionMark rhs → NoQuestionMark (.assign n rhs)
  | forLoop {v lo hi body} : NoQuestionMark lo → NoQuestionMark hi →
      NoQuestionMark body → NoQuestionMark (.forLoop v lo hi body)
  | whileLoop {c body} : NoQuestionMark c → NoQuestionMark body →
      NoQuestionMark (.whileLoop c body)
  | break_some {e} : NoQuestionMark e → NoQuestionMark (.break_ (some e))
  | break_none : NoQuestionMark (.break_ none)
  | continue_ : NoQuestionMark .continue_
  | earlyReturn {e} : NoQuestionMark e → NoQuestionMark (.earlyReturn e)

theorem NoQuestionMark.not_questionMark {e : ImpExpr} :
    ¬NoQuestionMark (.questionMark e) := by intro h; cases h

/-! ### Helper: denoteArgs' congruence under cfIntoMonads

When each argument satisfies the simulation equation, `denoteArgs'` on
the mapped arguments gives exactly the same result as on the originals. -/

theorem denoteArgs'_cfIntoMonads_eq (bi : Builtins) (fuel : Nat)
    (es : List ImpExpr)
    (hsim : ∀ e, e ∈ es → ∀ env : Env,
      denote' bi fuel (cfIntoMonads e) env =
        (Outcome.encodeCF4 (denote' bi fuel e env).1, (denote' bi fuel e env).2)) :
    ∀ env, denoteArgs' bi fuel (es.map cfIntoMonads) env =
      denoteArgs' bi fuel es env := by
  induction es with
  | nil => intro env; rfl
  | cons hd tl ih_tl =>
    intro env
    simp only [List.map_cons]
    unfold denoteArgs'
    simp only [bind, Bind.bind, StateT.bind]
    rw [hsim hd (List.mem_cons_self) env]
    generalize denote' bi fuel hd env = phd
    obtain ⟨rhd, envhd⟩ := phd; simp only []
    cases rhd with
    | val v =>
      simp only [Outcome.encodeCF4_val]
      cases v with
      | controlFlow b w => simp only [pure, Pure.pure, StateT.pure]
      | _ =>
        simp only [bind, Bind.bind, StateT.bind]
        rw [ih_tl (fun e he => hsim e (List.mem_cons_of_mem hd he)) envhd]
    | earlyRet v =>
      simp only [Outcome.encodeCF4_earlyRet, pure, Pure.pure, StateT.pure]
    | err msg =>
      simp only [Outcome.encodeCF4_err, pure, Pure.pure, StateT.pure]
    | broke v =>
      simp only [Outcome.encodeCF4_broke, pure, Pure.pure, StateT.pure]
    | continued =>
      simp only [Outcome.encodeCF4_continued, pure, Pure.pure, StateT.pure]

/-! ### Helper: denoteMatchArms' simulation under cfIntoMonads -/

theorem denoteMatchArms'_cfIntoMonads_sim (bi : Builtins) (fuel : Nat)
    (v : Value) (arms : List (ImpPat × ImpExpr))
    (hsim : ∀ pa, pa ∈ arms → ∀ env : Env,
      denote' bi fuel (cfIntoMonads pa.2) env =
        (Outcome.encodeCF4 (denote' bi fuel pa.2 env).1, (denote' bi fuel pa.2 env).2)) :
    ∀ env, denoteMatchArms' bi fuel v (arms.map fun (p, e) => (p, cfIntoMonads e)) env =
      (Outcome.encodeCF4 (denoteMatchArms' bi fuel v arms env).1,
       (denoteMatchArms' bi fuel v arms env).2) := by
  induction arms with
  | nil =>
    intro env; unfold denoteMatchArms'
    simp only [List.map_nil, pure, Pure.pure, StateT.pure, Outcome.encodeCF4_err]
  | cons arm rest ih_rest =>
    intro env
    obtain ⟨pat, body⟩ := arm
    simp only [List.map_cons]
    unfold denoteMatchArms'
    simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
    cases hm : matchPat pat v env with
    | some env' =>
      simp only [hm, set, StateT.set, modify, modifyGet, MonadStateOf.modifyGet]
      exact hsim (pat, body) (List.mem_cons_self) env'
    | none =>
      simp only [hm]
      exact ih_rest (fun pa hpa => hsim pa (List.mem_cons_of_mem _ hpa)) env

/-! ### Main theorem -/

/-- Phase 4 simulation: `cfIntoMonads` preserves `denote'` semantics
    up to `Outcome.encodeCF4` on the result, with identical env. -/
theorem CF4_combined (bi : Builtins) (fuel : Nat) (e : ImpExpr)
    (hnl : NoLoops e) (hnq : NoQuestionMark e) (hnr : NoReservedApps e) :
    ∀ env, denote' bi fuel (cfIntoMonads e) env =
      (Outcome.encodeCF4 (denote' bi fuel e env).1, (denote' bi fuel e env).2) := by
  induction e using ImpExpr.ind with
  -- Absurd cases
  | forLoop => exact absurd hnl NoLoops.not_forLoop
  | whileLoop => exact absurd hnl NoLoops.not_whileLoop
  | break_none => exact absurd hnl NoLoops.not_break
  | break_some => exact absurd hnl NoLoops.not_break
  | continue_ => exact absurd hnl NoLoops.not_continue
  | questionMark => exact absurd hnq NoQuestionMark.not_questionMark
  -- Trivial cases
  | lit v =>
    intro env
    simp only [cfIntoMonads, denote', pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
  | var n =>
    intro env
    simp only [cfIntoMonads, denote', bind, StateT.bind,
      get, getThe, MonadStateOf.get, StateT.get]
    cases env n <;>
      simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val, Outcome.encodeCF4_err]
  | unitVal =>
    intro env
    simp only [cfIntoMonads, denote', pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
  -- Pass-through
  | borrow e ih =>
    cases hnl with | borrow hl => cases hnq with | borrow hq => cases hnr with | borrow hr =>
    intro env; simp only [cfIntoMonads, denote']; exact ih hl hq hr env
  | deref e ih =>
    cases hnl with | deref hl => cases hnq with | deref hq => cases hnr with | deref hr =>
    intro env; simp only [cfIntoMonads, denote']; exact ih hl hq hr env
  -- EarlyReturn: the main interesting case
  | earlyReturn e ih =>
    cases hnl with | earlyReturn hl =>
    cases hnq with | earlyReturn hq =>
    cases hnr with | earlyReturn hr =>
    intro env
    -- cfIntoMonads (.earlyReturn e) = .app "ControlFlow.Break" [cfIntoMonads e]
    -- denote' (.app ...) unfolds via denoteApp', earlyReturn unfolds directly
    simp only [cfIntoMonads, denote']
    unfold denoteApp'
    simp only [String.reduceEq, ite_true, ite_false,
      bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure]
    rw [ih hl hq hr env]
    generalize denote' bi fuel e env = pe
    obtain ⟨re, enve⟩ := pe; simp only []
    cases re with
    | val v =>
      simp only [Outcome.encodeCF4_val]
      cases v with
      | controlFlow b w =>
        simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
      | _ => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4_earlyRet]
    | earlyRet v =>
      simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4_earlyRet, Outcome.encodeCF4_val]
    | err msg => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4_err]
    | broke v => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4_broke]
    | continued => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4_continued]
  -- LetBind
  | letBind name val body ih_val ih_body =>
    cases hnl with | letBind hl1 hl2 =>
    cases hnq with | letBind hq1 hq2 =>
    cases hnr with | letBind hr1 hr2 =>
    intro env
    simp only [cfIntoMonads, denote', bind, Bind.bind, StateT.bind]
    rw [ih_val hl1 hq1 hr1 env]
    generalize hpv : denote' bi fuel val env = pv
    obtain ⟨rv, envv⟩ := pv; simp only []
    cases rv with
    | val v =>
      simp only [Outcome.encodeCF4_val]
      cases v with
      | controlFlow b w =>
        simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
      | _ =>
        simp only [modify, MonadState.modifyGet, StateT.modifyGet]
        exact ih_body hl2 hq2 hr2 (envv.extend name _)
    | earlyRet v =>
      simp [Outcome.encodeCF4_earlyRet, pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
    | err msg => simp [Outcome.encodeCF4_err, pure, Pure.pure, StateT.pure]
    | broke v => simp [Outcome.encodeCF4_broke, pure, Pure.pure, StateT.pure]
    | continued => simp [Outcome.encodeCF4_continued, pure, Pure.pure, StateT.pure]
  -- Seq
  | seq e1 e2 ih1 ih2 =>
    cases hnl with | seq hl1 hl2 =>
    cases hnq with | seq hq1 hq2 =>
    cases hnr with | seq hr1 hr2 =>
    intro env
    simp only [cfIntoMonads, denote', bind, Bind.bind, StateT.bind]
    rw [ih1 hl1 hq1 hr1 env]
    generalize hp1 : denote' bi fuel e1 env = p1
    obtain ⟨r1, env1⟩ := p1; simp only []
    cases r1 with
    | val v =>
      simp only [Outcome.encodeCF4_val]
      cases v with
      | controlFlow b w =>
        simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
      | _ => exact ih2 hl2 hq2 hr2 env1
    | earlyRet v =>
      simp [Outcome.encodeCF4_earlyRet, pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
    | err msg => simp [Outcome.encodeCF4_err, pure, Pure.pure, StateT.pure]
    | broke v => simp [Outcome.encodeCF4_broke, pure, Pure.pure, StateT.pure]
    | continued => simp [Outcome.encodeCF4_continued, pure, Pure.pure, StateT.pure]
  -- Proj
  | proj e i ih =>
    cases hnl with | proj hl =>
    cases hnq with | proj hq =>
    cases hnr with | proj hr =>
    intro env
    simp only [cfIntoMonads, denote', bind, Bind.bind, StateT.bind]
    rw [ih hl hq hr env]
    generalize hpe : denote' bi fuel e env = pe
    obtain ⟨re, enve⟩ := pe; simp only []
    cases re with
    | val v =>
      simp only [Outcome.encodeCF4_val]
      cases v with
      | controlFlow b w =>
        simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
      | tuple vs =>
        cases hp : Value.projIdx (Value.tuple vs) i with
        | some w => simp [hp, pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
        | none => simp [hp, pure, Pure.pure, StateT.pure, Outcome.encodeCF4_err]
      | _ =>
        apply pair_eq_encodeCF4
        simp [Value.projIdx, Outcome.encodeCF4]
    | earlyRet v =>
      simp [Outcome.encodeCF4_earlyRet, pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
    | err msg => simp [Outcome.encodeCF4_err, pure, Pure.pure, StateT.pure]
    | broke v => simp [Outcome.encodeCF4_broke, pure, Pure.pure, StateT.pure]
    | continued => simp [Outcome.encodeCF4_continued, pure, Pure.pure, StateT.pure]
  -- IfThenElse
  | ifThenElse c t el ih_c ih_t ih_e =>
    cases hnl with | ifThenElse hl1 hl2 hl3 =>
    cases hnq with | ifThenElse hq1 hq2 hq3 =>
    cases hnr with | ifThenElse hr1 hr2 hr3 =>
    intro env
    simp only [cfIntoMonads, denote', bind, Bind.bind, StateT.bind]
    rw [ih_c hl1 hq1 hr1 env]
    generalize hpc : denote' bi fuel c env = pc
    obtain ⟨rc, envc⟩ := pc; simp only []
    cases rc with
    | val v =>
      simp only [Outcome.encodeCF4_val]
      cases v with
      | controlFlow b w =>
        simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
      | bool b => cases b with
        | true => exact ih_t hl2 hq2 hr2 envc
        | false => exact ih_e hl3 hq3 hr3 envc
      | _ => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4_err]
    | earlyRet v =>
      simp [Outcome.encodeCF4_earlyRet, pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
    | err msg => simp [Outcome.encodeCF4_err, pure, Pure.pure, StateT.pure]
    | broke v => simp [Outcome.encodeCF4_broke, pure, Pure.pure, StateT.pure]
    | continued => simp [Outcome.encodeCF4_continued, pure, Pure.pure, StateT.pure]
  -- Assign
  | assign name rhs ih =>
    cases hnl with | assign hl =>
    cases hnq with | assign hq =>
    cases hnr with | assign hr =>
    intro env
    simp only [cfIntoMonads, denote', bind, Bind.bind, StateT.bind]
    rw [ih hl hq hr env]
    generalize hpr : denote' bi fuel rhs env = pr
    obtain ⟨rr, envr⟩ := pr; simp only []
    cases rr with
    | val v =>
      simp only [Outcome.encodeCF4_val]
      cases v with
      | controlFlow b w =>
        simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
      | _ =>
        simp [bind, Bind.bind, StateT.bind, modify, modifyGet,
          MonadState.modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
    | earlyRet v =>
      simp [Outcome.encodeCF4_earlyRet, pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
    | err msg => simp [Outcome.encodeCF4_err, pure, Pure.pure, StateT.pure]
    | broke v => simp [Outcome.encodeCF4_broke, pure, Pure.pure, StateT.pure]
    | continued => simp [Outcome.encodeCF4_continued, pure, Pure.pure, StateT.pure]
  -- Match
  | match_ scrut arms ih_s ih_a =>
    cases hnl with | match_ hls hla =>
    cases hnq with | match_ hqs hqa =>
    cases hnr with | match_ hrs hra =>
    intro env
    simp only [cfIntoMonads, cfIntoMonads.mapArms_eq, denote', bind, Bind.bind, StateT.bind]
    rw [ih_s hls hqs hrs env]
    generalize hps : denote' bi fuel scrut env = ps
    obtain ⟨rs, envs⟩ := ps; simp only []
    cases rs with
    | val v =>
      simp only [Outcome.encodeCF4_val]
      cases v with
      | controlFlow b w =>
        simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
      | _ =>
        -- Non-CF value: dispatch to denoteMatchArms'
        exact denoteMatchArms'_cfIntoMonads_sim bi fuel _ arms
          (fun pa hpa env' => ih_a pa hpa (hla pa hpa) (hqa pa hpa) (hra pa hpa) env') envs
    | earlyRet v =>
      simp [Outcome.encodeCF4_earlyRet, pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
    | err msg => simp [Outcome.encodeCF4_err, pure, Pure.pure, StateT.pure]
    | broke v => simp [Outcome.encodeCF4_broke, pure, Pure.pure, StateT.pure]
    | continued => simp [Outcome.encodeCF4_continued, pure, Pure.pure, StateT.pure]
  -- App (NoReservedApps ensures non-special dispatch)
  | app f args ih_a =>
    cases hnl with | app hla =>
    cases hnq with | app hqa =>
    cases hnr with | app hf1 hf2 hf3 hf4 hra =>
    intro env
    simp only [cfIntoMonads, cfIntoMonads.mapExpr_eq, denote']
    -- Both sides go through denoteApp'. Since f is not reserved, both use the regular path.
    unfold denoteApp'
    simp only [if_neg hf1, if_neg hf2, if_neg hf3, if_neg hf4,
      bind, Bind.bind, StateT.bind]
    -- Both use denoteArgs'. By congruence, mapped args give same result.
    rw [denoteArgs'_cfIntoMonads_eq bi fuel args
      (fun a ha env' => ih_a a ha (hla a ha) (hqa a ha) (hra a ha) env') env]
    -- Now both sides are identical
    generalize denoteArgs' bi fuel args env = result
    obtain ⟨mvals, envA⟩ := result
    cases mvals with
    | some vals =>
      cases hbi : bi f vals with
      | some v => simp [hbi, pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
      | none => simp [hbi, pure, Pure.pure, StateT.pure, Outcome.encodeCF4_err]
    | none => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4_err]
  -- Tuple
  | tuple elems ih =>
    cases hnl with | tuple hla =>
    cases hnq with | tuple hqa =>
    cases hnr with | tuple hra =>
    intro env
    simp only [cfIntoMonads, cfIntoMonads.mapExpr_eq, denote', bind, Bind.bind, StateT.bind]
    rw [denoteArgs'_cfIntoMonads_eq bi fuel elems
      (fun a ha env' => ih a ha (hla a ha) (hqa a ha) (hra a ha) env') env]
    generalize denoteArgs' bi fuel elems env = result
    obtain ⟨mvals, envA⟩ := result
    cases mvals with
    | some vals => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4_val]
    | none => simp [pure, Pure.pure, StateT.pure, Outcome.encodeCF4_err]

end SSProve.Hax

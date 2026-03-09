/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.SemanticsCF
import SSProve.Hax.Phase.ExplicitMonadic
import SSProve.Hax.Phase.CfIntoMonadsCF
import SSProve.Hax.Phase.FunctionalizeLoopsCF
import SSProve.Hax.Pipeline
import SSProve.Hax.PipelineCF

/-!
# Phase 5 Correctness: Explicit Monadic Encoding

Proves that `explicitMonadic` preserves denotational semantics under `denote'`.

## Main results

* `wrapReturns_denote'_wrapContinue` — `wrapReturns` wraps outcomes via `Outcome.wrapContinue`
* `denoteForLoop'_wrapReturns` — wrapping a fold body doesn't change fold behavior
* `explicitMonadic_correct` — `denote'` of `explicitMonadic e` equals `denote'` of `e`
* `pipelineExt_full_correct` — end-to-end 5-phase pipeline theorem

## Proof strategy

`wrapReturns` walks the return spine and wraps leaf positions in `cfContinue`.
The key helper `cfContinue_denote'_wrapContinue` shows `denote'` for `cfContinue e`
equals `Outcome.wrapContinue` applied to `denote' e`. The main theorem follows
by induction on `ImpExpr` — leaf cases use the helper, return-spine cases use IH,
and identity cases (cfBreak/cfContinue/cfBreakContinue) show wrapContinue is fixed.

## Sorry-free

All theorems in this file are fully proven with no axioms or sorrys.
-/

namespace SSProve.Hax

/-! ## Outcome transformation for wrapReturns -/

/-- Transform an outcome by wrapping non-CF values in Continue. -/
def Outcome.wrapContinue : Outcome → Outcome
  | .val (.controlFlow b v) => .val (.controlFlow b v)
  | .val v => .val (.controlFlow false v)
  | o => o

@[simp] theorem Outcome.wrapContinue_val_cf (b : Bool) (v : Value) :
    Outcome.wrapContinue (.val (.controlFlow b v)) = .val (.controlFlow b v) := rfl
@[simp] theorem Outcome.wrapContinue_err (msg : String) :
    Outcome.wrapContinue (.err msg) = .err msg := rfl
@[simp] theorem Outcome.wrapContinue_earlyRet (v : Value) :
    Outcome.wrapContinue (.earlyRet v) = .earlyRet v := rfl
@[simp] theorem Outcome.wrapContinue_broke (v : Value) :
    Outcome.wrapContinue (.broke v) = .broke v := rfl
@[simp] theorem Outcome.wrapContinue_continued :
    Outcome.wrapContinue .continued = .continued := rfl

/-! ## wrapReturns semantic theorem -/

/-- `denote'` for `cfContinue e` equals `Outcome.wrapContinue` applied to `denote' e`. -/
private theorem cfContinue_denote'_wrapContinue (bi : Builtins) (fuel : Nat)
    (e : ImpExpr) :
    ∀ env, denote' bi fuel (.cfContinue e) env =
      let (r, env') := denote' bi fuel e env
      (Outcome.wrapContinue r, env') := by
  intro env
  generalize hm : denote' bi fuel e = m
  unfold denote'
  rw [hm]
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  generalize m env = p
  obtain ⟨r, env'⟩ := p
  cases r with
  | val v => cases v <;> rfl
  | err => rfl
  | earlyRet => rfl
  | broke => rfl
  | continued => rfl

/-- `denoteMatchArms'` with `wrapReturns`-mapped arms produces `wrapContinue`
    of the original result. -/
private theorem denoteMatchArms'_wrapReturns_wrapContinue
    (bi : Builtins) (fuel : Nat) (v : Value)
    (arms : List (ImpPat × ImpExpr))
    (ih : ∀ pa, pa ∈ arms → ∀ env, denote' bi fuel (wrapReturns pa.2) env =
      let (r, env') := denote' bi fuel pa.2 env
      (Outcome.wrapContinue r, env')) :
    ∀ env, denoteMatchArms' bi fuel v (arms.map fun (p, e) => (p, wrapReturns e)) env =
      let (r, env') := denoteMatchArms' bi fuel v arms env
      (Outcome.wrapContinue r, env') := by
  induction arms with
  | nil =>
    intro env
    simp only [List.map_nil]
    unfold denoteMatchArms'
    rfl
  | cons pa rest ih_rest =>
    intro env
    obtain ⟨pat, body⟩ := pa
    simp only [List.map_cons]
    unfold denoteMatchArms'
    simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
    cases hm : matchPat pat v env with
    | some env' =>
      simp only [set, StateT.set, bind, StateT.bind]
      exact ih (pat, body) (.head _) env'
    | none =>
      exact ih_rest (fun pa' hpa' => ih pa' (.tail _ hpa')) env

/-- `wrapReturns` transforms `denote'` outcomes by wrapping non-CF values
    in `controlFlow false` while preserving the environment. -/
theorem wrapReturns_denote'_wrapContinue (bi : Builtins) (fuel : Nat)
    (e : ImpExpr) :
    ∀ env, denote' bi fuel (wrapReturns e) env =
      let (r, env') := denote' bi fuel e env
      (Outcome.wrapContinue r, env') := by
  induction e using ImpExpr.ind with
  -- Leaf cases: wrapReturns e = cfContinue e (catch-all)
  | lit v => exact cfContinue_denote'_wrapContinue bi fuel (.lit v)
  | var n => exact cfContinue_denote'_wrapContinue bi fuel (.var n)
  | unitVal => exact cfContinue_denote'_wrapContinue bi fuel .unitVal
  | app f args _ => exact cfContinue_denote'_wrapContinue bi fuel (.app f args)
  | tuple elems _ => exact cfContinue_denote'_wrapContinue bi fuel (.tuple elems)
  | proj e i _ => exact cfContinue_denote'_wrapContinue bi fuel (.proj e i)
  | borrow e _ => exact cfContinue_denote'_wrapContinue bi fuel (.borrow e)
  | deref e _ => exact cfContinue_denote'_wrapContinue bi fuel (.deref e)
  | assign n rhs _ => exact cfContinue_denote'_wrapContinue bi fuel (.assign n rhs)
  | forLoop v lo hi body _ _ _ =>
    exact cfContinue_denote'_wrapContinue bi fuel (.forLoop v lo hi body)
  | whileLoop c body _ _ =>
    exact cfContinue_denote'_wrapContinue bi fuel (.whileLoop c body)
  | break_none => exact cfContinue_denote'_wrapContinue bi fuel (.break_ none)
  | break_some e _ =>
    exact cfContinue_denote'_wrapContinue bi fuel (.break_ (some e))
  | continue_ => exact cfContinue_denote'_wrapContinue bi fuel .continue_
  | earlyReturn e _ =>
    exact cfContinue_denote'_wrapContinue bi fuel (.earlyReturn e)
  | questionMark e _ =>
    exact cfContinue_denote'_wrapContinue bi fuel (.questionMark e)
  | forFold v lo hi body _ _ _ =>
    exact cfContinue_denote'_wrapContinue bi fuel (.forFold v lo hi body)
  | whileFold c body _ _ =>
    exact cfContinue_denote'_wrapContinue bi fuel (.whileFold c body)
  | forFoldReturn v lo hi body _ _ _ =>
    exact cfContinue_denote'_wrapContinue bi fuel (.forFoldReturn v lo hi body)
  | whileFoldReturn c body _ _ =>
    exact cfContinue_denote'_wrapContinue bi fuel (.whileFoldReturn c body)
  -- Identity cases: wrapReturns e = e, output is wrapContinue-fixed
  | cfBreak e _ =>
    intro env; simp only [wrapReturns]
    unfold denote'
    dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
    generalize denote' bi fuel e env = p
    obtain ⟨r, env'⟩ := p
    cases r with
    | val v => cases v <;> rfl
    | err => rfl | earlyRet => rfl | broke => rfl | continued => rfl
  | cfContinue e _ =>
    intro env; simp only [wrapReturns]
    unfold denote'
    dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
    generalize denote' bi fuel e env = p
    obtain ⟨r, env'⟩ := p
    cases r with
    | val v => cases v <;> rfl
    | err => rfl | earlyRet => rfl | broke => rfl | continued => rfl
  | cfBreakContinue e _ =>
    intro env; simp only [wrapReturns]
    unfold denote'
    dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
    generalize denote' bi fuel e env = p
    obtain ⟨r, env'⟩ := p
    cases r with
    | val v => cases v <;> rfl
    | err => rfl | earlyRet => rfl | broke => rfl | continued => rfl
  -- Return spine: letBind (only body is wrapped)
  | letBind n val body _ ih_body =>
    intro env
    simp only [wrapReturns]
    unfold denote'
    simp only [bind, StateT.bind]
    generalize denote' bi fuel val env = pv
    obtain ⟨rv, envv⟩ := pv
    cases rv with
    | val v =>
      cases v with
      | controlFlow => rfl
      | _ =>
        simp only [modify, modifyGet, MonadStateOf.modifyGet]
        exact ih_body _
    | err => rfl | earlyRet => rfl | broke => rfl | continued => rfl
  -- Return spine: ifThenElse (both branches wrapped)
  | ifThenElse c t e _ ih_t ih_e =>
    intro env
    simp only [wrapReturns]
    unfold denote'
    simp only [bind, StateT.bind]
    generalize denote' bi fuel c env = pc
    obtain ⟨rc, envc⟩ := pc
    cases rc with
    | val v =>
      cases v with
      | controlFlow => rfl
      | bool b => cases b with
        | true => exact ih_t _
        | false => exact ih_e _
      | _ => rfl
    | err => rfl | earlyRet => rfl | broke => rfl | continued => rfl
  -- Return spine: seq (only tail wrapped)
  | seq e1 e2 _ ih2 =>
    intro env
    simp only [wrapReturns]
    unfold denote'
    simp only [bind, StateT.bind]
    generalize denote' bi fuel e1 env = p1
    obtain ⟨r1, env1⟩ := p1
    cases r1 with
    | val v =>
      cases v with
      | controlFlow => rfl
      | _ => exact ih2 _
    | err => rfl | earlyRet => rfl | broke => rfl | continued => rfl
  -- Return spine: match_ (arms wrapped)
  | match_ scrut arms _ ih_arms =>
    intro env
    simp only [wrapReturns, wrapReturns.wrapReturnsArms_eq]
    unfold denote'
    simp only [bind, StateT.bind]
    generalize denote' bi fuel scrut env = ps
    obtain ⟨rs, envs⟩ := ps
    cases rs with
    | val v =>
      cases v with
      | controlFlow => rfl
      | _ => exact denoteMatchArms'_wrapReturns_wrapContinue bi fuel _ arms ih_arms _
    | err => rfl | earlyRet => rfl | broke => rfl | continued => rfl

/-! ## Fold neutrality lemmas

The core results: `wrapReturns` does not change fold behavior because
`denoteForLoop'` dispatches identically on `val v` and `val (controlFlow false v)`:
```
| .val (.controlFlow true v)  => break
| .val (.controlFlow false _) => continue
| .val _                      => continue  ← same behavior
```
-/

private theorem forLoop_body_neutral (bi : Builtins) (fuel : Nat)
    (var : String) (_lo hi : Int) (body : ImpExpr) :
    ∀ n : Nat, ∀ lo' : Int, ∀ env,
      n ≤ fuel →
      denoteForLoop' bi n var lo' hi (wrapReturns body) env =
        denoteForLoop' bi n var lo' hi body env := by
  intro n; induction n with
  | zero =>
    intro lo' env _
    unfold denoteForLoop'
    split
    · rfl
    · split
      · rfl
      · omega
  | succ n ih =>
    intro lo' env hn
    unfold denoteForLoop'
    by_cases hge : lo' ≥ hi
    · simp only [if_pos hge]
    · have hfuel : ¬(n + 1 = 0) := by omega
      simp only [if_neg hge, if_neg hfuel]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      rw [wrapReturns_denote'_wrapContinue bi (n + 1) body
            (Env.extend env var (.int lo'))]
      generalize denote' bi (n + 1) body (Env.extend env var (.int lo')) = pb
      obtain ⟨r, envb⟩ := pb
      cases r with
      | val v =>
        cases v with
        | controlFlow b w =>
          simp only [Outcome.wrapContinue, show n + 1 - 1 = n from rfl]
          cases b with
          | true => rfl
          | false => exact ih (lo' + 1) envb (by omega)
        | _ =>
          simp only [Outcome.wrapContinue, show n + 1 - 1 = n from rfl]
          exact ih (lo' + 1) envb (by omega)
      | _ => rfl

/-- `wrapReturns` is neutral within `denoteForLoop'`. -/
theorem denoteForLoop'_wrapReturns (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) :
    ∀ env, denoteForLoop' bi fuel var lo hi (wrapReturns body) env =
      denoteForLoop' bi fuel var lo hi body env :=
  fun env => forLoop_body_neutral bi fuel var lo hi body fuel lo env (Nat.le_refl _)

private theorem whileLoop_body_neutral (bi : Builtins) (fuel : Nat)
    (cond body : ImpExpr) :
    ∀ n : Nat, ∀ env, n ≤ fuel →
      denoteWhile' bi n cond (wrapReturns body) env =
        denoteWhile' bi n cond body env := by
  intro n; induction n with
  | zero =>
    intro env _
    unfold denoteWhile'
    split
    · rfl
    · omega
  | succ n ih =>
    intro env hn
    unfold denoteWhile'
    have hfuel : ¬(n + 1 = 0) := by omega
    simp only [if_neg hfuel]
    dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
    generalize denote' bi (n + 1) cond env = pc
    obtain ⟨rc, envc⟩ := pc
    cases rc with
    | val v =>
      cases v with
      | controlFlow => rfl
      | bool b =>
        cases b with
        | true =>
          dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure,
            StateT.pure, Id.run]
          rw [wrapReturns_denote'_wrapContinue bi (n + 1) body envc]
          generalize denote' bi (n + 1) body envc = pb
          obtain ⟨rb, envb⟩ := pb
          cases rb with
          | val w =>
            cases w with
            | controlFlow b' _ =>
              simp only [Outcome.wrapContinue, show n + 1 - 1 = n from rfl]
              cases b' with
              | true => rfl
              | false => exact ih envb (by omega)
            | _ =>
              simp only [Outcome.wrapContinue, show n + 1 - 1 = n from rfl]
              exact ih envb (by omega)
          | _ => rfl
        | false => rfl
      | _ => rfl
    | _ => rfl

/-- `wrapReturns` is neutral within `denoteWhile'`. -/
theorem denoteWhile'_wrapReturns (bi : Builtins) (fuel : Nat)
    (cond body : ImpExpr) :
    ∀ env, denoteWhile' bi fuel cond (wrapReturns body) env =
      denoteWhile' bi fuel cond body env :=
  fun env => whileLoop_body_neutral bi fuel cond body fuel env (Nat.le_refl _)

private theorem forLoopReturn_body_neutral (bi : Builtins) (fuel : Nat)
    (var : String) (_lo hi : Int) (body : ImpExpr) :
    ∀ n : Nat, ∀ lo' : Int, ∀ env, n ≤ fuel →
      denoteForLoop'Return bi n var lo' hi (wrapReturns body) env =
        denoteForLoop'Return bi n var lo' hi body env := by
  intro n; induction n with
  | zero =>
    intro lo' env _
    unfold denoteForLoop'Return
    split
    · rfl
    · split
      · rfl
      · omega
  | succ n ih =>
    intro lo' env hn
    unfold denoteForLoop'Return
    by_cases hge : lo' ≥ hi
    · simp only [if_pos hge]
    · have hfuel : ¬(n + 1 = 0) := by omega
      simp only [if_neg hge, if_neg hfuel]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      rw [wrapReturns_denote'_wrapContinue bi (n + 1) body
            (Env.extend env var (.int lo'))]
      generalize denote' bi (n + 1) body (Env.extend env var (.int lo')) = pb
      obtain ⟨r, envb⟩ := pb
      cases r with
      | val v =>
        cases v with
        | controlFlow b w =>
          simp only [Outcome.wrapContinue, show n + 1 - 1 = n from rfl]
          cases b with
          | true =>
            -- Need to distinguish loop break (w = controlFlow false _)
            -- from early return (other w). Both sides match identically.
            cases w with
            | controlFlow b'' _ => cases b'' <;> rfl
            | _ => rfl
          | false => exact ih (lo' + 1) envb (by omega)
        | _ =>
          simp only [Outcome.wrapContinue, show n + 1 - 1 = n from rfl]
          exact ih (lo' + 1) envb (by omega)
      | _ => rfl

/-- `wrapReturns` is neutral within `denoteForLoop'Return`. -/
theorem denoteForLoop'Return_wrapReturns (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) :
    ∀ env, denoteForLoop'Return bi fuel var lo hi (wrapReturns body) env =
      denoteForLoop'Return bi fuel var lo hi body env :=
  fun env => forLoopReturn_body_neutral bi fuel var lo hi body fuel lo env (Nat.le_refl _)

private theorem whileLoopReturn_body_neutral (bi : Builtins) (fuel : Nat)
    (cond body : ImpExpr) :
    ∀ n : Nat, ∀ env, n ≤ fuel →
      denoteWhile'Return bi n cond (wrapReturns body) env =
        denoteWhile'Return bi n cond body env := by
  intro n; induction n with
  | zero =>
    intro env _
    unfold denoteWhile'Return
    split
    · rfl
    · omega
  | succ n ih =>
    intro env hn
    unfold denoteWhile'Return
    have hfuel : ¬(n + 1 = 0) := by omega
    simp only [if_neg hfuel]
    dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
    generalize denote' bi (n + 1) cond env = pc
    obtain ⟨rc, envc⟩ := pc
    cases rc with
    | val v =>
      cases v with
      | controlFlow => rfl
      | bool b =>
        cases b with
        | true =>
          dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure,
            StateT.pure, Id.run]
          rw [wrapReturns_denote'_wrapContinue bi (n + 1) body envc]
          generalize denote' bi (n + 1) body envc = pb
          obtain ⟨rb, envb⟩ := pb
          cases rb with
          | val w =>
            cases w with
            | controlFlow b' w' =>
              simp only [Outcome.wrapContinue, show n + 1 - 1 = n from rfl]
              cases b' with
              | true =>
                cases w' with
                | controlFlow b'' _ => cases b'' <;> rfl
                | _ => rfl
              | false => exact ih envb (by omega)
            | _ =>
              simp only [Outcome.wrapContinue, show n + 1 - 1 = n from rfl]
              exact ih envb (by omega)
          | _ => rfl
        | false => rfl
      | _ => rfl
    | _ => rfl

/-- `wrapReturns` is neutral within `denoteWhile'Return`. -/
theorem denoteWhile'Return_wrapReturns (bi : Builtins) (fuel : Nat)
    (cond body : ImpExpr) :
    ∀ env, denoteWhile'Return bi fuel cond (wrapReturns body) env =
      denoteWhile'Return bi fuel cond body env :=
  fun env => whileLoopReturn_body_neutral bi fuel cond body fuel env (Nat.le_refl _)

/-! ## Fold body congruence lemmas -/

private theorem denoteForLoop'_body_congr (bi : Builtins)
    (var : String) (body1 body2 : ImpExpr)
    (h : ∀ fuel env, denote' bi fuel body1 env = denote' bi fuel body2 env) :
    ∀ fuel : Nat, ∀ lo hi : Int, ∀ env,
      denoteForLoop' bi fuel var lo hi body1 env =
        denoteForLoop' bi fuel var lo hi body2 env := by
  intro fuel; induction fuel with
  | zero =>
    intro lo hi env; unfold denoteForLoop'
    split
    · rfl
    · split
      · rfl
      · omega
  | succ n ih =>
    intro lo hi env
    unfold denoteForLoop'
    by_cases hge : lo ≥ hi
    · simp only [if_pos hge]
    · have hfuel : ¬(n + 1 = 0) := by omega
      simp only [if_neg hge, if_neg hfuel]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      rw [h (n + 1) (Env.extend env var (.int lo))]
      generalize denote' bi (n + 1) body2 (Env.extend env var (.int lo)) = pb
      obtain ⟨r, envb⟩ := pb
      cases r with
      | val v =>
        cases v with
        | controlFlow b w =>
          simp only [show n + 1 - 1 = n from rfl]
          cases b with
          | true => rfl
          | false => exact ih (lo + 1) hi envb
        | _ => simp only [show n + 1 - 1 = n from rfl]; exact ih (lo + 1) hi envb
      | _ => rfl

private theorem denoteWhile'_congr (bi : Builtins)
    (cond1 cond2 body1 body2 : ImpExpr)
    (hc : ∀ fuel env, denote' bi fuel cond1 env = denote' bi fuel cond2 env)
    (h : ∀ fuel env, denote' bi fuel body1 env = denote' bi fuel body2 env) :
    ∀ fuel : Nat, ∀ env,
      denoteWhile' bi fuel cond1 body1 env =
        denoteWhile' bi fuel cond2 body2 env := by
  intro fuel; induction fuel with
  | zero =>
    intro env; unfold denoteWhile'
    split
    · rfl
    · omega
  | succ n ih =>
    intro env
    unfold denoteWhile'
    have hfuel : ¬(n + 1 = 0) := by omega
    simp only [if_neg hfuel]
    dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
    rw [hc (n + 1) env]
    generalize denote' bi (n + 1) cond2 env = pc
    obtain ⟨rc, envc⟩ := pc
    cases rc with
    | val v =>
      cases v with
      | controlFlow => rfl
      | bool b =>
        cases b with
        | true =>
          dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
          rw [h (n + 1) envc]
          generalize denote' bi (n + 1) body2 envc = pb
          obtain ⟨rb, envb⟩ := pb
          cases rb with
          | val w =>
            cases w with
            | controlFlow b' _ =>
              simp only [show n + 1 - 1 = n from rfl]
              cases b' with
              | true => rfl
              | false => exact ih envb
            | _ => simp only [show n + 1 - 1 = n from rfl]; exact ih envb
          | _ => rfl
        | false => rfl
      | _ => rfl
    | _ => rfl

private theorem denoteForLoop'Return_body_congr (bi : Builtins)
    (var : String) (body1 body2 : ImpExpr)
    (h : ∀ fuel env, denote' bi fuel body1 env = denote' bi fuel body2 env) :
    ∀ fuel : Nat, ∀ lo hi : Int, ∀ env,
      denoteForLoop'Return bi fuel var lo hi body1 env =
        denoteForLoop'Return bi fuel var lo hi body2 env := by
  intro fuel; induction fuel with
  | zero =>
    intro lo hi env; unfold denoteForLoop'Return
    split
    · rfl
    · split
      · rfl
      · omega
  | succ n ih =>
    intro lo hi env
    unfold denoteForLoop'Return
    by_cases hge : lo ≥ hi
    · simp only [if_pos hge]
    · have hfuel : ¬(n + 1 = 0) := by omega
      simp only [if_neg hge, if_neg hfuel]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
      rw [h (n + 1) (Env.extend env var (.int lo))]
      generalize denote' bi (n + 1) body2 (Env.extend env var (.int lo)) = pb
      obtain ⟨r, envb⟩ := pb
      cases r with
      | val v =>
        cases v with
        | controlFlow b w =>
          simp only [show n + 1 - 1 = n from rfl]
          cases b with
          | true =>
            cases w with
            | controlFlow b'' _ => cases b'' <;> rfl
            | _ => rfl
          | false => exact ih (lo + 1) hi envb
        | _ => simp only [show n + 1 - 1 = n from rfl]; exact ih (lo + 1) hi envb
      | _ => rfl

private theorem denoteWhile'Return_congr (bi : Builtins)
    (cond1 cond2 body1 body2 : ImpExpr)
    (hc : ∀ fuel env, denote' bi fuel cond1 env = denote' bi fuel cond2 env)
    (h : ∀ fuel env, denote' bi fuel body1 env = denote' bi fuel body2 env) :
    ∀ fuel : Nat, ∀ env,
      denoteWhile'Return bi fuel cond1 body1 env =
        denoteWhile'Return bi fuel cond2 body2 env := by
  intro fuel; induction fuel with
  | zero =>
    intro env; unfold denoteWhile'Return
    split
    · rfl
    · omega
  | succ n ih =>
    intro env
    unfold denoteWhile'Return
    have hfuel : ¬(n + 1 = 0) := by omega
    simp only [if_neg hfuel]
    dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet, pure, Pure.pure, Id.run]
    rw [hc (n + 1) env]
    generalize denote' bi (n + 1) cond2 env = pc
    obtain ⟨rc, envc⟩ := pc
    cases rc with
    | val v =>
      cases v with
      | controlFlow => rfl
      | bool b =>
        cases b with
        | true =>
          dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
          rw [h (n + 1) envc]
          generalize denote' bi (n + 1) body2 envc = pb
          obtain ⟨rb, envb⟩ := pb
          cases rb with
          | val w =>
            cases w with
            | controlFlow b' w' =>
              simp only [show n + 1 - 1 = n from rfl]
              cases b' with
              | true =>
                cases w' with
                | controlFlow b'' _ => cases b'' <;> rfl
                | _ => rfl
              | false => exact ih envb
            | _ => simp only [show n + 1 - 1 = n from rfl]; exact ih envb
          | _ => rfl
        | false => rfl
      | _ => rfl
    | _ => rfl

/-! ## Helper: denoteArgs' with identity-transformed args -/

private theorem denoteArgs'_explicitMonadic (bi : Builtins) (fuel : Nat)
    (args : List ImpExpr)
    (ih : ∀ a, a ∈ args → ∀ fuel env,
      denote' bi fuel (explicitMonadic a) env = denote' bi fuel a env) :
    ∀ env, denoteArgs' bi fuel (args.map explicitMonadic) env =
      denoteArgs' bi fuel args env := by
  induction args with
  | nil => intro env; rfl
  | cons e es ih_es =>
    intro env
    simp only [List.map_cons]
    unfold denoteArgs'
    simp only [bind, StateT.bind]
    rw [ih e (.head _) fuel env]
    generalize denote' bi fuel e env = pe
    obtain ⟨re, enve⟩ := pe
    cases re with
    | val v =>
      cases v with
      | controlFlow => rfl
      | _ =>
        have h : denoteArgs' bi fuel (es.map explicitMonadic) = denoteArgs' bi fuel es :=
          funext fun env' => ih_es (fun a ha => ih a (.tail _ ha)) env'
        rw [h]
    | err => rfl
    | earlyRet => rfl
    | broke => rfl
    | continued => rfl

/-! ## Helper: denoteMatchArms' with identity-transformed arms -/

private theorem denoteMatchArms'_explicitMonadic (bi : Builtins) (fuel : Nat)
    (v : Value) (arms : List (ImpPat × ImpExpr))
    (ih : ∀ pa, pa ∈ arms → ∀ fuel env,
      denote' bi fuel (explicitMonadic pa.2) env = denote' bi fuel pa.2 env) :
    ∀ env, denoteMatchArms' bi fuel v (arms.map fun (p, e) => (p, explicitMonadic e)) env =
      denoteMatchArms' bi fuel v arms env := by
  induction arms with
  | nil => intro env; unfold denoteMatchArms'; rfl
  | cons pa rest ih_rest =>
    intro env
    obtain ⟨pat, body⟩ := pa
    simp only [List.map_cons]
    unfold denoteMatchArms'
    simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get]
    cases hm : matchPat pat v env with
    | some env' =>
      simp only [set, StateT.set, bind, StateT.bind]
      exact ih (pat, body) (.head _) fuel env'
    | none =>
      exact ih_rest (fun pa' hpa' => ih pa' (.tail _ hpa')) env

/-! ## Main theorem -/

/-- `explicitMonadic` preserves `denote'` semantics for `FullyFunctional`
    expressions. -/
theorem explicitMonadic_correct (bi : Builtins) (e : ImpExpr)
    (hff : FullyFunctional e) :
    ∀ fuel env, denote' bi fuel (explicitMonadic e) env =
      denote' bi fuel e env := by
  obtain ⟨hnr, hnm, hnl, hne⟩ := hff
  induction e using ImpExpr.ind with
  -- Trivial identity cases
  | lit v => intro fuel env; simp only [explicitMonadic]
  | var n => intro fuel env; simp only [explicitMonadic]
  | unitVal => intro fuel env; simp only [explicitMonadic]
  -- Structural: letBind
  | letBind n val body ih_val ih_body =>
    cases hnr with | letBind hr1 hr2 =>
    cases hnm with | letBind hm1 hm2 =>
    cases hnl with | letBind hl1 hl2 =>
    cases hne with | letBind he1 he2 =>
    intro fuel env
    simp only [explicitMonadic]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih_val hr1 hm1 hl1 he1 fuel env]
    generalize denote' bi fuel val env = pv
    obtain ⟨rv, envv⟩ := pv
    cases rv with
    | val v =>
      cases v with
      | controlFlow => rfl
      | _ =>
        simp only [modify, modifyGet, MonadStateOf.modifyGet]
        exact ih_body hr2 hm2 hl2 he2 fuel _
    | err => rfl | earlyRet => rfl | broke => rfl | continued => rfl
  -- Structural: seq
  | seq e1 e2 ih1 ih2 =>
    cases hnr with | seq hr1 hr2 =>
    cases hnm with | seq hm1 hm2 =>
    cases hnl with | seq hl1 hl2 =>
    cases hne with | seq he1 he2 =>
    intro fuel env
    simp only [explicitMonadic]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih1 hr1 hm1 hl1 he1 fuel env]
    generalize denote' bi fuel e1 env = p1
    obtain ⟨r1, env1⟩ := p1
    cases r1 with
    | val v =>
      cases v with
      | controlFlow => rfl
      | _ => exact ih2 hr2 hm2 hl2 he2 fuel _
    | err => rfl | earlyRet => rfl | broke => rfl | continued => rfl
  -- Structural: proj
  | proj e i ih =>
    cases hnr with | proj he =>
    cases hnm with | proj hme =>
    cases hnl with | proj hle =>
    cases hne with | proj hee =>
    intro fuel env
    simp only [explicitMonadic]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih he hme hle hee fuel env]
  -- Structural: ifThenElse
  | ifThenElse c t el ih_c ih_t ih_e =>
    cases hnr with | ifThenElse hrc hrt hre =>
    cases hnm with | ifThenElse hmc hmt hme =>
    cases hnl with | ifThenElse hlc hlt hle =>
    cases hne with | ifThenElse hec het hee =>
    intro fuel env
    simp only [explicitMonadic]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih_c hrc hmc hlc hec fuel env]
    generalize denote' bi fuel c env = pc
    obtain ⟨rc, envc⟩ := pc
    cases rc with
    | val v =>
      cases v with
      | controlFlow => rfl
      | bool b =>
        cases b with
        | true => exact ih_t hrt hmt hlt het fuel _
        | false => exact ih_e hre hme hle hee fuel _
      | _ => rfl
    | err => rfl | earlyRet => rfl | broke => rfl | continued => rfl
  -- App: uses denoteArgs' helper
  | app f args ih =>
    cases hnr with | app hrargs =>
    cases hnm with | app hmargs =>
    cases hnl with | app hlargs =>
    cases hne with | app heargs =>
    intro fuel env
    simp only [explicitMonadic, explicitMonadic.mapExpr_eq]
    unfold denote'; unfold denoteApp'
    simp only [bind, StateT.bind]
    have := denoteArgs'_explicitMonadic bi fuel args
      (fun a ha fuel env => ih a ha (hrargs a ha) (hmargs a ha) (hlargs a ha) (heargs a ha) fuel env) env
    rw [this]
  -- Tuple: uses denoteArgs' helper
  | tuple elems ih =>
    cases hnr with | tuple hrelems =>
    cases hnm with | tuple hmelems =>
    cases hnl with | tuple hlelems =>
    cases hne with | tuple heelems =>
    intro fuel env
    simp only [explicitMonadic, explicitMonadic.mapExpr_eq]
    unfold denote'
    simp only [bind, StateT.bind]
    have := denoteArgs'_explicitMonadic bi fuel elems
      (fun a ha fuel env => ih a ha (hrelems a ha) (hmelems a ha) (hlelems a ha) (heelems a ha) fuel env) env
    rw [this]
  -- Match_: uses denoteMatchArms' helper
  | match_ scrut arms ih_scrut ih_arms =>
    cases hnr with | match_ hrs hrarms =>
    cases hnm with | match_ hms hmarms =>
    cases hnl with | match_ hls hlarms =>
    cases hne with | match_ hes hearms =>
    intro fuel env
    simp only [explicitMonadic, explicitMonadic.mapArms_eq]
    unfold denote'
    simp only [bind, StateT.bind]
    rw [ih_scrut hrs hms hls hes fuel env]
    generalize denote' bi fuel scrut env = ps
    obtain ⟨rs, envs⟩ := ps
    cases rs with
    | val v =>
      cases v with
      | controlFlow => rfl
      | _ =>
        exact denoteMatchArms'_explicitMonadic bi fuel _ arms
          (fun pa hpa fuel env => ih_arms pa hpa
            (hrarms pa hpa) (hmarms pa hpa) (hlarms pa hpa) (hearms pa hpa) fuel env) envs
    | err => rfl | earlyRet => rfl | broke => rfl | continued => rfl
  -- Fold cases: neutrality + congruence
  | forFold v lo hi body ih_lo ih_hi ih_body =>
    cases hnr with | forFold hr1 hr2 hr3 =>
    cases hnm with | forFold hm1 hm2 hm3 =>
    cases hnl with | forFold hl1 hl2 hl3 =>
    cases hne with | forFold he1 he2 he3 =>
    intro fuel env
    simp only [explicitMonadic]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih_lo hr1 hm1 hl1 he1 fuel env]
    generalize denote' bi fuel lo env = plo
    obtain ⟨rlo, envlo⟩ := plo
    dsimp only []
    rw [ih_hi hr2 hm2 hl2 he2 fuel envlo]
    generalize denote' bi fuel hi envlo = phi
    obtain ⟨rhi, envhi⟩ := phi
    dsimp only []
    cases rlo with
    | val vlo =>
      cases rhi with
      | val vhi =>
        cases vlo with
        | int lo_val =>
          cases vhi with
          | int hi_val =>
            dsimp only []
            rw [denoteForLoop'_wrapReturns]
            exact denoteForLoop'_body_congr bi v (explicitMonadic body) body
              (fun fuel env => ih_body hr3 hm3 hl3 he3 fuel env)
              fuel lo_val hi_val envhi
          | controlFlow => rfl
          | _ => rfl
        | controlFlow => rfl
        | _ => cases vhi with | controlFlow => rfl | _ => rfl
      | err => cases vlo with | controlFlow => rfl | _ => rfl
      | earlyRet => cases vlo with | controlFlow => rfl | _ => rfl
      | broke => cases vlo with | controlFlow => rfl | _ => rfl
      | continued => cases vlo with | controlFlow => rfl | _ => rfl
    | err =>
      cases rhi with
      | val v => cases v with | controlFlow => rfl | _ => rfl
      | _ => rfl
    | earlyRet =>
      cases rhi with
      | val v => cases v with | controlFlow => rfl | _ => rfl
      | _ => rfl
    | broke =>
      cases rhi with
      | val v => cases v with | controlFlow => rfl | _ => rfl
      | _ => rfl
    | continued =>
      cases rhi with
      | val v => cases v with | controlFlow => rfl | _ => rfl
      | _ => rfl
  | whileFold c body ih_c ih_body =>
    cases hnr with | whileFold hr1 hr2 =>
    cases hnm with | whileFold hm1 hm2 =>
    cases hnl with | whileFold hl1 hl2 =>
    cases hne with | whileFold he1 he2 =>
    intro fuel env
    simp only [explicitMonadic]; unfold denote'
    rw [show denoteWhile' bi fuel (explicitMonadic c) (wrapReturns (explicitMonadic body)) env =
        denoteWhile' bi fuel c body env from by
      rw [denoteWhile'_wrapReturns]
      exact denoteWhile'_congr bi (explicitMonadic c) c (explicitMonadic body) body
        (fun fuel env => ih_c hr1 hm1 hl1 he1 fuel env)
        (fun fuel env => ih_body hr2 hm2 hl2 he2 fuel env) fuel env]
  | forFoldReturn v lo hi body ih_lo ih_hi ih_body =>
    cases hnr with | forFoldReturn hr1 hr2 hr3 =>
    cases hnm with | forFoldReturn hm1 hm2 hm3 =>
    cases hnl with | forFoldReturn hl1 hl2 hl3 =>
    cases hne with | forFoldReturn he1 he2 he3 =>
    intro fuel env
    simp only [explicitMonadic]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih_lo hr1 hm1 hl1 he1 fuel env]
    generalize denote' bi fuel lo env = plo
    obtain ⟨rlo, envlo⟩ := plo
    dsimp only []
    rw [ih_hi hr2 hm2 hl2 he2 fuel envlo]
    generalize denote' bi fuel hi envlo = phi
    obtain ⟨rhi, envhi⟩ := phi
    dsimp only []
    cases rlo with
    | val vlo =>
      cases rhi with
      | val vhi =>
        cases vlo with
        | int lo_val =>
          cases vhi with
          | int hi_val =>
            dsimp only []
            rw [denoteForLoop'Return_wrapReturns]
            exact denoteForLoop'Return_body_congr bi v (explicitMonadic body) body
              (fun fuel env => ih_body hr3 hm3 hl3 he3 fuel env)
              fuel lo_val hi_val envhi
          | controlFlow => rfl
          | _ => rfl
        | controlFlow => rfl
        | _ => cases vhi with | controlFlow => rfl | _ => rfl
      | err => cases vlo with | controlFlow => rfl | _ => rfl
      | earlyRet => cases vlo with | controlFlow => rfl | _ => rfl
      | broke => cases vlo with | controlFlow => rfl | _ => rfl
      | continued => cases vlo with | controlFlow => rfl | _ => rfl
    | err =>
      cases rhi with
      | val v => cases v with | controlFlow => rfl | _ => rfl
      | _ => rfl
    | earlyRet =>
      cases rhi with
      | val v => cases v with | controlFlow => rfl | _ => rfl
      | _ => rfl
    | broke =>
      cases rhi with
      | val v => cases v with | controlFlow => rfl | _ => rfl
      | _ => rfl
    | continued =>
      cases rhi with
      | val v => cases v with | controlFlow => rfl | _ => rfl
      | _ => rfl
  | whileFoldReturn c body ih_c ih_body =>
    cases hnr with | whileFoldReturn hr1 hr2 =>
    cases hnm with | whileFoldReturn hm1 hm2 =>
    cases hnl with | whileFoldReturn hl1 hl2 =>
    cases hne with | whileFoldReturn he1 he2 =>
    intro fuel env
    simp only [explicitMonadic]; unfold denote'
    rw [show denoteWhile'Return bi fuel (explicitMonadic c)
        (wrapReturns (explicitMonadic body)) env =
        denoteWhile'Return bi fuel c body env from by
      rw [denoteWhile'Return_wrapReturns]
      exact denoteWhile'Return_congr bi (explicitMonadic c) c (explicitMonadic body) body
        (fun fuel env => ih_c hr1 hm1 hl1 he1 fuel env)
        (fun fuel env => ih_body hr2 hm2 hl2 he2 fuel env) fuel env]
  -- CF constructors: recurse
  | cfBreak e ih =>
    cases hnr with | cfBreak hr =>
    cases hnm with | cfBreak hm =>
    cases hnl with | cfBreak hl =>
    cases hne with | cfBreak he =>
    intro fuel env
    simp only [explicitMonadic]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih hr hm hl he fuel env]
  | cfContinue e ih =>
    cases hnr with | cfContinue hr =>
    cases hnm with | cfContinue hm =>
    cases hnl with | cfContinue hl =>
    cases hne with | cfContinue he =>
    intro fuel env
    simp only [explicitMonadic]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih hr hm hl he fuel env]
  | cfBreakContinue e ih =>
    cases hnr with | cfBreakContinue hr =>
    cases hnm with | cfBreakContinue hm =>
    cases hnl with | cfBreakContinue hl =>
    cases hne with | cfBreakContinue he =>
    intro fuel env
    simp only [explicitMonadic]; unfold denote'
    simp only [bind, StateT.bind]
    rw [ih hr hm hl he fuel env]
  -- Absurd cases: eliminated by FullyFunctional
  | borrow => exact absurd hnr NoReferences.not_borrow
  | deref => exact absurd hnr NoReferences.not_deref
  | assign => exact absurd hnm NoMutation.not_assign
  | forLoop => exact absurd hnl NoLoops.not_forLoop
  | whileLoop => exact absurd hnl NoLoops.not_whileLoop
  | break_none => exact absurd hnl NoLoops.not_break
  | break_some => exact absurd hnl NoLoops.not_break
  | continue_ => exact absurd hnl NoLoops.not_continue
  | earlyReturn => exact absurd hne NoEarlyExit.not_earlyReturn
  | questionMark => exact absurd hne NoEarlyExit.not_questionMark

/-! ## Pipeline connection -/

/-- The extended 5-phase pipeline preserves semantics for well-scoped programs.

    Composes `pipeline_full_correct` with `explicitMonadic_correct`:
    ```
    denote' (pipelineExt e) env
      = denote' (explicitMonadic (pipeline e)) env     -- unfold pipelineExt
      = denote' (pipeline e) env                       -- explicitMonadic_correct
      = (encodeCF (denote e env).1, (denote e env).2)  -- pipeline_full_correct
    ``` -/
theorem pipelineExt_full_correct (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (e : ImpExpr) (hls : LoopScoped e) (hnq : NoQuestionMark e)
    (hncf : NoCFConstructors e) :
    ∀ fuel env, Env.NoControlFlow env →
      denote' bi fuel (pipelineExt e) env =
        (Outcome.encodeCF (denote bi fuel e env).1, (denote bi fuel e env).2) := by
  intro fuel env henv
  unfold pipelineExt
  rw [explicitMonadic_correct bi (pipeline e) (pipeline_fullyFunctional e) fuel env]
  exact pipeline_full_correct bi hbi e hls hnq hncf fuel env henv

end SSProve.Hax

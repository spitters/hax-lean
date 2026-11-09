/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Range.Check

/-!
# Soundness of the range checker

`check_sound`: a term the checker `Hax.Range.check` accepts runs under `denote'` with the
guarded builtin table `guardBi g bi` exactly as with `bi`, from every environment in the
abstract environment that holds no control-flow value, so no guard `g` fails on any run; its
value and final environment lie in the abstract ones (`Post`). The hypotheses are `Sound g H
bi`: the transfer functions of `H` prove the guards `g`, describe the results of `bi`, and the
comparison heads of `bi` answer with the truth of their relation.

## Main definitions

* `cfBind`: the continuation of `denote'` after a subterm, which passes control-flow values
  and other outcomes through.
* `Post`: the postcondition of a checked term.

## Main results

* `denoteForLoop'_sound`: a loop body that keeps the invariant gives a loop that keeps it.
* `check_sound`, `checkArgs_sound`, `checkArms_sound`: soundness of the checker.
* `checkT_sound`: soundness for a `TExpr` literal through `TExpr.erase`.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Range

open CatCrypt.Crypto.SecureCompilation.RangeDomain

/-! ## Environments -/

theorem lookup_cons_self (Γ : AEnv) (x : String) (a : AV) :
    ((x, a) :: Γ).lookup x = some a := by
  simp [List.lookup]

theorem lookup_cons_ne (Γ : AEnv) {x y : String} (a : AV) (h : y ≠ x) :
    ((x, a) :: Γ).lookup y = Γ.lookup y := by
  have hb : (y == x) = false := by simpa using h
  simp [List.lookup, hb]

theorem Sat.cons {Γ : AEnv} {env : Env} {x : String} {a : AV} {v : Value} (h : Sat Γ env)
    (hv : a.Mem v) : Sat ((x, a) :: Γ) (Env.extend env x v) := by
  intro y b hy
  by_cases hyx : y = x
  · subst hyx
    rw [lookup_cons_self] at hy
    cases hy
    exact ⟨v, Env.extend_same _ _ _, hv⟩
  · rw [lookup_cons_ne _ _ hyx] at hy
    rw [Env.extend_other _ _ _ _ hyx]
    exact h y b hy

theorem Sat.cons_of_get {Γ : AEnv} {env : Env} {x : String} {a : AV} {v : Value}
    (h : Sat Γ env) (hx : env x = some v) (hv : a.Mem v) : Sat ((x, a) :: Γ) env := by
  intro y b hy
  by_cases hyx : y = x
  · subst hyx
    rw [lookup_cons_self] at hy
    cases hy
    exact ⟨v, hx, hv⟩
  · rw [lookup_cons_ne _ _ hyx] at hy
    exact h y b hy

theorem Sat.get {Γ : AEnv} {env : Env} {x : String} {v : Value} (h : Sat Γ env)
    (hx : env x = some v) : (Γ.get x).Mem v := by
  unfold AEnv.get
  rcases hl : Γ.lookup x with _ | a
  · trivial
  · obtain ⟨v', hv', hm⟩ := h x a hl
    rw [hx] at hv'
    cases hv'
    exact hm

theorem lookup_drop (xs : List String) (Γ : AEnv) (y : String) :
    (AEnv.drop xs Γ).lookup y = if y ∈ xs then none else Γ.lookup y := by
  induction Γ with
  | nil => simp [AEnv.drop, List.lookup]
  | cons p Γ ih =>
    obtain ⟨z, a⟩ := p
    unfold AEnv.drop at ih ⊢
    by_cases hz : z ∈ xs
    · rw [List.filter_cons_of_neg (by simp [hz]), ih]
      by_cases hyz : y = z
      · subst hyz; simp [hz]
      · rw [lookup_cons_ne _ _ hyz]
    · rw [List.filter_cons_of_pos (by simp [hz])]
      by_cases hyz : y = z
      · subst hyz; simp [hz]
      · rw [lookup_cons_ne _ _ hyz, ih, lookup_cons_ne _ _ hyz]

theorem Sat.drop {Γ : AEnv} {env env' : Env} {xs : List String} (h : Sat Γ env)
    (hag : ∀ y, y ∉ xs → env' y = env y) : Sat (AEnv.drop xs Γ) env' := by
  intro y a hy
  rw [lookup_drop] at hy
  split at hy
  · cases hy
  · rename_i hc
    rw [hag y hc]
    exact h y a hy

theorem lookup_join (Γ1 Γ2 : AEnv) (x : String) :
    (AEnv.join Γ1 Γ2).lookup x =
      (Γ1.lookup x).bind fun a => (Γ2.lookup x).map fun b => a.join b := by
  induction Γ1 with
  | nil => simp [AEnv.join, List.lookup]
  | cons p Γ1 ih =>
    obtain ⟨z, a⟩ := p
    unfold AEnv.join at ih ⊢
    rw [List.filterMap_cons]
    rcases hz : Γ2.lookup z with _ | b
    · simp only [Option.map_none]
      rw [ih]
      by_cases hxz : x = z
      · subst hxz; simp [hz]
      · rw [lookup_cons_ne _ _ hxz]
    · simp only [Option.map_some]
      by_cases hxz : x = z
      · subst hxz; simp [hz]
      · rw [lookup_cons_ne _ _ hxz, lookup_cons_ne _ _ hxz, ih]

theorem Sat.join_left {Γ1 Γ2 : AEnv} {env : Env} (h : Sat Γ1 env) :
    Sat (AEnv.join Γ1 Γ2) env := by
  intro x c hx
  rw [lookup_join] at hx
  rcases h1 : Γ1.lookup x with _ | a <;> rw [h1] at hx
  · cases hx
  rcases h2 : Γ2.lookup x with _ | b <;> simp [h2] at hx
  subst hx
  obtain ⟨v, hv, hm⟩ := h x a h1
  exact ⟨v, hv, hm.join_left⟩

theorem Sat.join_right {Γ1 Γ2 : AEnv} {env : Env} (h : Sat Γ2 env) :
    Sat (AEnv.join Γ1 Γ2) env := by
  intro x c hx
  rw [lookup_join] at hx
  rcases h1 : Γ1.lookup x with _ | a <;> rw [h1] at hx
  · cases hx
  rcases h2 : Γ2.lookup x with _ | b <;> simp [h2] at hx
  subst hx
  obtain ⟨v, hv, hm⟩ := h x b h2
  exact ⟨v, hv, hm.join_right⟩

theorem mem_of_lookup {J : AEnv} {x : String} {a : AV} (h : J.lookup x = some a) :
    (x, a) ∈ J := by
  induction J with
  | nil => simp [List.lookup] at h
  | cons p J ih =>
    obtain ⟨z, b⟩ := p
    by_cases hxz : x = z
    · subst hxz
      rw [lookup_cons_self] at h
      cases h
      exact List.mem_cons_self
    · rw [lookup_cons_ne _ _ hxz] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem Sat.entails {Γ J : AEnv} {env : Env} (h : Sat Γ env) (he : entails Γ J = true) :
    Sat J env := by
  intro x a hx
  have hm := List.all_eq_true.1 he (x, a) (mem_of_lookup hx)
  simp only at hm
  rcases hl : Γ.lookup x with _ | b <;> rw [hl] at hm
  · cases hm
  obtain ⟨v, hv, hb⟩ := h x b hl
  exact ⟨v, hv, hb.le hm⟩

/-! ## Patterns -/

mutual

/-- A pattern match changes the environment at the pattern's variables only. -/
theorem matchPat_agree : ∀ (p : ImpPat) (v : Value) (env env' : Env),
    matchPat p v env = some env' → ∀ y, (patVars p).contains y = false → env' y = env y
  | .wildcard, _, env, env', h, _, _ => by simp [matchPat] at h; subst h; rfl
  | .litPat l, v, env, env', h, _, _ => by
    simp only [matchPat] at h
    split at h
    · cases h; rfl
    · cases h
  | .varPat n, v, env, env', h, y, hy => by
    simp only [matchPat, Option.some.injEq] at h
    subst h
    have : y ≠ n := by simpa [patVars] using hy
    exact Env.extend_other _ _ _ _ this
  | .tuplePat ps, v, env, env', h, y, hy => by
    cases v with
    | tuple vs =>
      simp only [matchPat] at h
      split at h
      · cases h
      · exact matchPatList_agree ps vs env env' h y (by simpa [patVars] using hy)
    | array vs =>
      simp only [matchPat] at h
      split at h
      · cases h
      · exact matchPatList_agree ps vs env env' h y (by simpa [patVars] using hy)
    | _ => simp [matchPat] at h
  | .somePat p, v, env, env', h, y, hy => by
    cases v with
    | option o =>
      cases o with
      | some u =>
        simp only [matchPat] at h
        exact matchPat_agree p u env env' h y (by simpa [patVars] using hy)
      | none => simp [matchPat] at h
    | _ => simp [matchPat] at h
  | .nonePat, v, env, env', h, _, _ => by
    cases v with
    | option o => cases o <;> simp [matchPat] at h; subst h; rfl
    | _ => simp [matchPat] at h
  | .okPat p, v, env, env', h, y, hy => by
    cases v with
    | result ok u =>
      cases ok
      · simp [matchPat] at h
      · simp only [matchPat] at h
        exact matchPat_agree p u env env' h y (by simpa [patVars] using hy)
    | _ => simp [matchPat] at h
  | .errPat p, v, env, env', h, y, hy => by
    cases v with
    | result ok u =>
      cases ok
      · simp only [matchPat] at h
        exact matchPat_agree p u env env' h y (by simpa [patVars] using hy)
      · simp [matchPat] at h
    | _ => simp [matchPat] at h
  | .ctorPat _ _, v, env, env', h, _, _ => by cases v <;> simp [matchPat] at h

/-- A list of pattern matches changes the environment at the patterns' variables only. -/
theorem matchPatList_agree : ∀ (ps : List ImpPat) (vs : List Value) (env env' : Env),
    matchPat.matchPatList ps vs env = some env' →
      ∀ y, (patVarsList ps).contains y = false → env' y = env y
  | [], [], env, env', h, _, _ => by
    simp only [matchPat.matchPatList, Option.some.injEq] at h; subst h; rfl
  | [], _ :: _, _, _, h, _, _ => by simp [matchPat.matchPatList] at h
  | _ :: _, [], _, _, h, _, _ => by simp [matchPat.matchPatList] at h
  | p :: ps, v :: vs, env, env', h, y, hy => by
    simp only [matchPat.matchPatList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨env1, h1, h2⟩ := h
    simp only [patVarsList, List.contains_append, Bool.or_eq_false_iff] at hy
    rw [matchPatList_agree ps vs env1 env' h2 y hy.2, matchPat_agree p v env env1 h1 y hy.1]

end

/-! ## The continuation of a subterm -/

/-- The continuation `K` of `denote'` after a subterm with result `r`: a value that is not a
    control-flow value goes to `K`; a control-flow value and every other outcome pass. -/
def cfBind (r : Outcome × Env) (K : Value → Env → Outcome × Env) : Outcome × Env :=
  match r with
  | (.val v, e) => if v.isControlFlow then (.val v, e) else K v e
  | (o, e) => (o, e)

/-- The payload of a control-flow value; the value itself otherwise. -/
def Value.cfPayload : Value → Value
  | .controlFlow _ u => u
  | v => v

/-- The postcondition of a term checked at `(a, Γ')` under the loop invariant `J`: a value
    that is not a control-flow value lies in `a` with its environment in `Γ'`; a control-flow
    value has its environment in `J`; both leave an environment and a value with no
    control-flow value inside. -/
def Post (J Γ' : AEnv) (a : AV) : Outcome × Env → Prop
  | (.val v, e) => Env.NoControlFlow e ∧ (Value.cfPayload v).deepNoControlFlow = true ∧
      (if v.isControlFlow then Sat J e else a.Mem v ∧ Sat Γ' e)
  | _ => True

theorem post_val {J Γ' : AEnv} {a : AV} {v : Value} {e : Env} (hN : Env.NoControlFlow e)
    (hd : v.deepNoControlFlow = true) (hm : a.Mem v) (hS : Sat Γ' e) :
    Post J Γ' a (.val v, e) := by
  have hcf := Value.deepNoControlFlow_implies_isControlFlow_false hd
  have hp : Value.cfPayload v = v := by cases v <;> first | rfl | simp at hcf
  refine ⟨hN, by rw [hp]; exact hd, ?_⟩
  rw [hcf]
  exact ⟨hm, hS⟩

theorem post_cf {J Γ' : AEnv} {a : AV} {b : Bool} {u : Value} {e : Env}
    (hN : Env.NoControlFlow e) (hd : u.deepNoControlFlow = true) (hS : Sat J e) :
    Post J Γ' a (.val (.controlFlow b u), e) :=
  ⟨hN, hd, by simpa using hS⟩

/-- The facts `Post` gives about a value that is not a control-flow value. -/
theorem Post.of_val {J Γ' : AEnv} {a : AV} {v : Value} {e : Env}
    (h : Post J Γ' a (.val v, e)) (hcf : v.isControlFlow = false) :
    Env.NoControlFlow e ∧ v.deepNoControlFlow = true ∧ a.Mem v ∧ Sat Γ' e := by
  obtain ⟨hN, hd, hr⟩ := h
  have hp : Value.cfPayload v = v := by cases v <;> first | rfl | simp at hcf
  rw [hcf] at hr
  exact ⟨hN, by rw [← hp]; exact hd, hr.1, hr.2⟩

/-- A step through `cfBind`: equal subterm runs and continuations that agree and keep the
    postcondition on the subterm's values give equal runs that keep it. -/
theorem cfBind_step {J Γ1 Γ2 : AEnv} {a1 a2 : AV} {r r' : Outcome × Env}
    {K K' : Value → Env → Outcome × Env} (hrr : r' = r) (hr : Post J Γ1 a1 r)
    (hK : ∀ v e, r = (.val v, e) → Env.NoControlFlow e → v.deepNoControlFlow = true →
      a1.Mem v → Sat Γ1 e → K' v e = K v e ∧ Post J Γ2 a2 (K v e)) :
    cfBind r' K' = cfBind r K ∧ Post J Γ2 a2 (cfBind r K) := by
  rw [hrr]
  obtain ⟨o, e⟩ := r
  cases o with
  | val v =>
    by_cases hcf : v.isControlFlow = true
    · have e1 : cfBind (.val v, e) K' = (.val v, e) := by simp [cfBind, hcf]
      have e2 : cfBind (.val v, e) K = (.val v, e) := by simp [cfBind, hcf]
      rw [e1, e2]
      obtain ⟨hN, hd, hJ⟩ := hr
      rw [hcf] at hJ
      exact ⟨rfl, hN, hd, by simpa [hcf] using hJ⟩
    · have hcf' : v.isControlFlow = false := by simpa using hcf
      obtain ⟨hN, hd, hm, hS⟩ := hr.of_val hcf'
      simp only [cfBind, hcf', Bool.false_eq_true, ↓reduceIte]
      exact hK v e rfl hN hd hm hS
  | _ => exact ⟨rfl, by simp [cfBind, Post]⟩

/-- Weakening of the final environment and value of a postcondition. -/
theorem Post.weaken {J Γ Γ' : AEnv} {a a' : AV} {r : Outcome × Env} (h : Post J Γ a r)
    (hΓ : ∀ e, Sat Γ e → Sat Γ' e) (ha : ∀ v, a.Mem v → a'.Mem v) : Post J Γ' a' r := by
  obtain ⟨o, e⟩ := r
  cases o with
  | val v =>
    obtain ⟨hN, hd, hr⟩ := h
    refine ⟨hN, hd, ?_⟩
    rcases Bool.eq_false_or_eq_true v.isControlFlow with hc | hc <;>
      simp only [hc, ↓reduceIte, Bool.false_eq_true] at hr ⊢
    · exact hr
    · exact ⟨ha v hr.1, hΓ e hr.2⟩
  | _ => trivial

/-! ## Unfolding `denote'` -/

theorem denote'_letBind_cf (bi : Builtins) (fuel : Nat) (n : String) (v b : ImpExpr)
    (env : Env) :
    denote' bi fuel (.letBind n v b) env =
      cfBind (denote' bi fuel v env) (fun w e => denote' bi fuel b (Env.extend e n w)) := by
  rw [denote'_letBind_run]
  unfold cfBind
  rcases denote' bi fuel v env with ⟨o, e⟩
  cases o <;> try rfl
  rename_i w; cases w <;> rfl

theorem denote'_seq_cf (bi : Builtins) (fuel : Nat) (a b : ImpExpr) (env : Env) :
    denote' bi fuel (.seq a b) env =
      cfBind (denote' bi fuel a env) (fun _ e => denote' bi fuel b e) := by
  rw [denote'_seq_run]
  unfold cfBind
  rcases denote' bi fuel a env with ⟨o, e⟩
  cases o <;> try rfl
  rename_i w; cases w <;> rfl

theorem denote'_assign_cf (bi : Builtins) (fuel : Nat) (n : String) (v : ImpExpr)
    (env : Env) :
    denote' bi fuel (.assign n v) env =
      cfBind (denote' bi fuel v env) (fun w e => (.val .unit, Env.extend e n w)) := by
  rw [denote'_assign_run]
  unfold cfBind
  rcases denote' bi fuel v env with ⟨o, e⟩
  cases o <;> try rfl
  rename_i w; cases w <;> rfl

/-- The branch continuation of an `if`. -/
def ifK (bi : Builtins) (fuel : Nat) (t e : ImpExpr) (w : Value) (env : Env) :
    Outcome × Env :=
  match w with
  | .bool true => denote' bi fuel t env
  | .bool false => denote' bi fuel e env
  | _ => (.err "if condition not a bool", env)

theorem denote'_ifThenElse_cf (bi : Builtins) (fuel : Nat) (c t e : ImpExpr) (env : Env) :
    denote' bi fuel (.ifThenElse c t e) env =
      cfBind (denote' bi fuel c env) (ifK bi fuel t e) := by
  rw [denote'_ifThenElse_run]
  unfold cfBind ifK
  rcases denote' bi fuel c env with ⟨o, e⟩
  cases o <;> try rfl
  rename_i w; cases w <;> try rfl
  rename_i b; cases b <;> rfl

theorem denote'_match_cf (bi : Builtins) (fuel : Nat) (s : ImpExpr)
    (arms : List (ImpPat × ImpExpr)) (env : Env) :
    denote' bi fuel (.match_ s arms) env =
      cfBind (denote' bi fuel s env) (fun v e => denoteMatchArms' bi fuel v arms e) := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  unfold cfBind
  rcases denote' bi fuel s env with ⟨o, e⟩
  cases o <;> try rfl
  rename_i w; cases w <;> rfl

theorem denote'_cfBreak_cf (bi : Builtins) (fuel : Nat) (x : ImpExpr) (env : Env) :
    denote' bi fuel (.cfBreak x) env =
      cfBind (denote' bi fuel x env) (fun v e => (.val (.controlFlow true v), e)) := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  unfold cfBind
  rcases denote' bi fuel x env with ⟨o, e⟩
  cases o <;> try rfl
  rename_i w; cases w <;> rfl

theorem denote'_cfContinue_cf (bi : Builtins) (fuel : Nat) (x : ImpExpr) (env : Env) :
    denote' bi fuel (.cfContinue x) env =
      cfBind (denote' bi fuel x env) (fun v e => (.val (.controlFlow false v), e)) := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  unfold cfBind
  rcases denote' bi fuel x env with ⟨o, e⟩
  cases o <;> try rfl
  rename_i w; cases w <;> rfl

theorem denote'_borrow_run (bi : Builtins) (fuel : Nat) (x : ImpExpr) (env : Env) :
    denote' bi fuel (.borrow x) env = denote' bi fuel x env := by
  conv => lhs; unfold denote'

theorem denote'_deref_run (bi : Builtins) (fuel : Nat) (x : ImpExpr) (env : Env) :
    denote' bi fuel (.deref x) env = denote' bi fuel x env := by
  conv => lhs; unfold denote'

/-- The bounds continuation of a counted loop. -/
def forK (bi : Builtins) (fuel : Nat) (x : String) (hi body : ImpExpr) (vlo : Value)
    (env : Env) : Outcome × Env :=
  cfBind (denote' bi fuel hi env) fun vhi e =>
    match vlo.loopBound, vhi.loopBound with
    | some l, some h => denoteForLoop' bi fuel x l h body e
    | _, _ => (.err "for loop bounds must be integers", e)

theorem denote'_forFold_cf (bi : Builtins) (fuel : Nat) (x : String) (lo hi body : ImpExpr)
    (env : Env) :
    denote' bi fuel (.forFold x lo hi body) env =
      cfBind (denote' bi fuel lo env) (forK bi fuel x hi body) := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  unfold cfBind forK cfBind
  rcases denote' bi fuel lo env with ⟨o, e⟩
  cases o <;> try rfl
  rename_i w
  cases w <;> try rfl
  all_goals
    dsimp only [StateT.bind]
    rcases denote' bi fuel hi e with ⟨o2, e2⟩
    cases o2 <;> try rfl
    rename_i w2
    cases w2 <;> rfl

/-- The continuation of `denoteArgs'` after an argument: a value that is not a control-flow
    value goes to `K`; every other outcome gives no argument list. -/
def argsCons (r : Outcome × Env) (K : Value → Env → Option (List Value) × Env) :
    Option (List Value) × Env :=
  match r with
  | (.val v, e) => if v.isControlFlow then (none, e) else K v e
  | (_, e) => (none, e)

theorem denoteArgs'_cons_cf (bi : Builtins) (fuel : Nat) (x : ImpExpr) (xs : List ImpExpr)
    (env : Env) :
    denoteArgs' bi fuel (x :: xs) env =
      argsCons (denote' bi fuel x env) fun v e =>
        ((denoteArgs' bi fuel xs e).1.map (v :: ·), (denoteArgs' bi fuel xs e).2) := by
  conv => lhs; unfold denoteArgs'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  unfold argsCons
  rcases denote' bi fuel x env with ⟨o, e⟩
  cases o <;> try rfl
  rename_i w; cases w <;> rfl

/-- A step through `argsCons`, as `cfBind_step`. -/
theorem argsCons_step {J Γ1 : AEnv} {a1 : AV} {r r' : Outcome × Env}
    {K K' : Value → Env → Option (List Value) × Env}
    {P : Option (List Value) × Env → Prop} (hrr : r' = r) (hr : Post J Γ1 a1 r)
    (hnone : ∀ e, P (none, e))
    (hK : ∀ v e, Env.NoControlFlow e → v.deepNoControlFlow = true → a1.Mem v → Sat Γ1 e →
      K' v e = K v e ∧ P (K v e)) :
    argsCons r' K' = argsCons r K ∧ P (argsCons r K) := by
  rw [hrr]
  obtain ⟨o, e⟩ := r
  cases o with
  | val v =>
    by_cases hcf : v.isControlFlow = true
    · simp only [argsCons, hcf, ↓reduceIte]
      exact ⟨by trivial, hnone e⟩
    · have hcf' : v.isControlFlow = false := by simpa using hcf
      obtain ⟨hN, hd, hm, hS⟩ := hr.of_val hcf'
      simp only [argsCons, hcf', Bool.false_eq_true, ↓reduceIte]
      exact hK v e hN hd hm hS
  | _ => exact ⟨rfl, hnone e⟩

theorem denote'_app_cf (bi : Builtins) (fuel : Nat) (f : String) (args : List ImpExpr)
    (env : Env) :
    denote' bi fuel (.app f args) env =
      match denoteArgs' bi fuel args env with
      | (some vs, e) =>
        match bi f vs with
        | some v => (.val v, e)
        | none => (.err s!"unknown function or bad args: {f}", e)
      | (none, e) => (.err "non-value in function arguments", e) := by
  conv => lhs; unfold denote'
  unfold denoteApp'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  rcases denoteArgs' bi fuel args env with ⟨r, e⟩
  cases r <;> try rfl
  rename_i vs
  dsimp only
  cases bi f vs <;> rfl

theorem denoteMatchArms'_nil (bi : Builtins) (fuel : Nat) (v : Value) (env : Env) :
    denoteMatchArms' bi fuel v [] env = (.err "no matching pattern", env) := by
  unfold denoteMatchArms'; rfl

theorem denoteMatchArms'_cons (bi : Builtins) (fuel : Nat) (v : Value) (p : ImpPat)
    (b : ImpExpr) (rest : List (ImpPat × ImpExpr)) (env : Env) :
    denoteMatchArms' bi fuel v ((p, b) :: rest) env =
      match matchPat p v env with
      | some env' => denote' bi fuel b env'
      | none => denoteMatchArms' bi fuel v rest env := by
  conv => lhs; unfold denoteMatchArms'
  dsimp only [bind, Bind.bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, set,
    MonadStateOf.set, StateT.set, pure, Pure.pure, StateT.pure, Id.run]
  cases matchPat p v env <;> rfl

theorem denoteForLoop'_run (bi : Builtins) (fuel : Nat) (x : String) (lo hi : Int)
    (body : ImpExpr) (env : Env) :
    denoteForLoop' bi fuel x lo hi body env =
      if lo ≥ hi then (.val .unit, env)
      else if fuel = 0 then (.err "out of fuel", env)
      else match denote' bi fuel body (Env.extend env x (.int lo)) with
        | (.val (.controlFlow true v), e) => (.val v, e)
        | (.val _, e) => denoteForLoop' bi (fuel - 1) x (lo + 1) hi body e
        | (o, e) => (o, e) := by
  rw [denoteForLoop']
  split
  · rfl
  split
  · rfl
  dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, pure, Pure.pure, StateT.pure, Id.run]
  rcases denote' bi fuel body (Env.extend env x (.int lo)) with ⟨o, e⟩
  cases o <;> try rfl
  rename_i w
  cases w <;> try rfl
  rename_i b u
  cases b <;> rfl

/-! ## Atoms and refinement -/

/-- The value of an atom in an environment. -/
def atomVal (env : Env) : ImpExpr → Option Value
  | .var x => env x
  | .lit l => some (Value.ofLit l)
  | _ => none

theorem atomAV_mem {Γ : AEnv} {env : Env} (h : Sat Γ env) {A : ImpExpr} {av : AV}
    {v : Value} (ha : atomAV Γ A = some av) (hv : atomVal env A = some v) : av.Mem v := by
  cases A <;> simp only [atomAV, atomVal, Option.some.injEq, reduceCtorEq] at ha hv
  · subst ha; subst hv; exact litAV_mem _
  · subst ha; exact h.get hv

/-- An atom evaluates to its value without changing the environment. -/
theorem denote'_atom {bi : Builtins} {fuel : Nat} {env : Env} {A : ImpExpr} {o : Outcome}
    {e : Env} (hA : isAtom A = true) (h : denote' bi fuel A env = (o, e)) :
    e = env ∧ ∀ v, o = .val v → atomVal env A = some v := by
  cases A <;> simp [isAtom] at hA
  · rw [denote'_lit_run] at h
    cases h
    exact ⟨rfl, fun v hv => by cases hv; rfl⟩
  · rw [denote'_var_run] at h
    rcases hx : env _ with _ | w <;> rw [hx] at h <;> cases h
    · exact ⟨rfl, fun v hv => by cases hv⟩
    · exact ⟨rfl, fun v hv => by cases hv; exact hx⟩

/-- An atom with a value evaluates to it. -/
theorem denote'_atom_val {bi : Builtins} {fuel : Nat} {env : Env} {A : ImpExpr} {v : Value}
    (hA : isAtom A = true) (hv : atomVal env A = some v) :
    denote' bi fuel A env = (.val v, env) := by
  cases A <;> simp [isAtom] at hA
  · simp only [atomVal, Option.some.injEq] at hv
    subst hv
    exact denote'_lit_run _ _ _ _
  · simp only [atomVal] at hv
    rw [denote'_var_run, hv]

/-- An atom without a value evaluates to an error. -/
theorem denote'_atom_none {bi : Builtins} {fuel : Nat} {env : Env} {A : ImpExpr}
    (hA : isAtom A = true) (hv : atomVal env A = none) :
    ∃ s, denote' bi fuel A env = (.err s, env) := by
  cases A <;> simp [isAtom] at hA
  · simp [atomVal] at hv
  · simp only [atomVal] at hv
    rw [denote'_var_run, hv]
    exact ⟨_, rfl⟩

/-- A comparison of two atoms that evaluates to a Boolean reads the atoms' values and leaves
    the environment. -/
theorem denote'_cmp_atoms {bi : Builtins} {fuel : Nat} {env e : Env} {op : String}
    {l r : ImpExpr} {b : Bool} (hl : isAtom l = true) (hr : isAtom r = true)
    (h : denote' bi fuel (.app op [l, r]) env = (.val (.bool b), e)) :
    e = env ∧ ∃ vl vr, atomVal env l = some vl ∧ atomVal env r = some vr ∧
      bi op [vl, vr] = some (.bool b) := by
  have hne : ∀ s e', ((Outcome.err s, e') : Outcome × Env) ≠ (.val (.bool b), e) := by
    intro s e' h'; cases h'
  rw [denote'_app_cf] at h
  rcases hvl : atomVal env l with _ | vl
  · obtain ⟨s, hs⟩ := denote'_atom_none (bi := bi) (fuel := fuel) hl hvl
    rw [denoteArgs'_cons_cf, hs] at h
    exact absurd h (hne _ _)
  rw [denoteArgs'_cons_cf, denote'_atom_val hl hvl] at h
  by_cases hc : vl.isControlFlow = true
  · simp only [argsCons, hc, ↓reduceIte] at h
    exact absurd h (hne _ _)
  simp only [argsCons, hc, Bool.false_eq_true, ↓reduceIte] at h
  rcases hvr : atomVal env r with _ | vr
  · obtain ⟨s, hs⟩ := denote'_atom_none (bi := bi) (fuel := fuel) hr hvr
    rw [denoteArgs'_cons_cf, hs] at h
    exact absurd h (hne _ _)
  rw [denoteArgs'_cons_cf, denote'_atom_val hr hvr] at h
  by_cases hc' : vr.isControlFlow = true
  · simp only [argsCons, hc', ↓reduceIte] at h
    exact absurd h (hne _ _)
  simp only [argsCons, hc', Bool.false_eq_true, ↓reduceIte, Total.denoteArgs'_nil_run,
    Option.map_some] at h
  rcases hb : bi op [vl, vr] with _ | w <;> rw [hb] at h
  · exact absurd h (hne _ _)
  cases h
  exact ⟨rfl, vl, vr, rfl, rfl, hb⟩

theorem refineUpper_sound {Γ0 Γ : AEnv} {env : Env} {A B : ImpExpr} {d : Int}
    {va vb : Value} (h0 : Sat Γ0 env) (h : Sat Γ env) (hA : atomVal env A = some va)
    (hB : atomVal env B = some vb)
    (hrel : ∀ m n, va.toInt = some m → vb.toInt = some n → m + d ≤ n) :
    Sat (refineUpper Γ0 A B d Γ) env := by
  cases A with
  | var x =>
    simp only [refineUpper]
    rcases hb : atomAV Γ0 B with _ | ab
    · exact h
    rcases hx : Γ0.get x with _ | ix | _
    · cases ab <;> exact h
    · cases ab with
      | num ib =>
        have hxv : env x = some va := hA
        obtain ⟨m, hm, hmi⟩ : (AV.num ix).Mem va := hx ▸ h0.get hxv
        obtain ⟨n, hn, hni⟩ : (AV.num ib).Mem vb := atomAV_mem h0 hb hB
        have := hrel m n hm hn
        refine h.cons_of_get hxv ⟨m, hm, hmi.meet ⟨hmi.1, ?_⟩⟩
        have := hni.2
        omega
      | _ => exact h
    · cases ab <;> exact h
  | _ => exact h

theorem refineLower_sound {Γ0 Γ : AEnv} {env : Env} {A B : ImpExpr} {d : Int}
    {va vb : Value} (h0 : Sat Γ0 env) (h : Sat Γ env) (hA : atomVal env A = some va)
    (hB : atomVal env B = some vb)
    (hrel : ∀ m n, va.toInt = some m → vb.toInt = some n → m + d ≤ n) :
    Sat (refineLower Γ0 A B d Γ) env := by
  cases B with
  | var y =>
    simp only [refineLower]
    rcases ha : atomAV Γ0 A with _ | aa
    · exact h
    rcases hy : Γ0.get y with _ | iy | _
    · cases aa <;> exact h
    · cases aa with
      | num ia =>
        have hyv : env y = some vb := hB
        obtain ⟨n, hn, hni⟩ : (AV.num iy).Mem vb := hy ▸ h0.get hyv
        obtain ⟨m, hm, hmi⟩ : (AV.num ia).Mem va := atomAV_mem h0 ha hA
        have := hrel m n hm hn
        refine h.cons_of_get hyv ⟨n, hn, hni.meet ⟨?_, hni.2⟩⟩
        have := hmi.1
        omega
      | _ => exact h
    · cases aa <;> exact h
  | _ => exact h

/-- The refinement by `A < B` (`strict`) or `A ≤ B` is sound. -/
theorem refineLt_sound {Γ : AEnv} {env : Env} {A B : ImpExpr} {s : Bool} {va vb : Value}
    (h : Sat Γ env) (hA : atomVal env A = some va) (hB : atomVal env B = some vb)
    (hrel : ∀ m n, va.toInt = some m → vb.toInt = some n → m + (if s then 1 else 0) ≤ n) :
    Sat (refineLt Γ A B s) env :=
  refineLower_sound h (refineUpper_sound h h hA hB hrel) hA hB hrel

/-- The refinement by a comparison of two atoms that evaluated to `b` is sound. -/
theorem refineCond_sound {g : String → List Value → Bool} {H : Spec} {bi : Builtins}
    (hS : Sound g H bi) {fuel : Nat} {c : ImpExpr} {b : Bool} {Γ : AEnv} {env e : Env}
    (hc : denote' bi fuel c env = (.val (.bool b), e)) (hΓ : Sat Γ e) :
    Sat (refineCond c b Γ) e := by
  cases c with
  | app op args =>
    match args, hc with
    | [l, r], hc =>
      unfold refineCond
      by_cases hat : (isAtom l && isAtom r) = true
      · simp only [hat, ↓reduceIte]
        simp only [Bool.and_eq_true] at hat
        obtain ⟨rfl, vl, vr, hvl, hvr, hb⟩ := denote'_cmp_atoms hat.1 hat.2 hc
        rcases hop : cmpOf op with _ | ⟨strict, swapped⟩
        · exact hΓ
        simp only
        have key := fun m n hm hn => hS.cmp op strict swapped vl vr b m n hop hb hm hn
        by_cases hps : b = swapped
        · simp only [hps, ↓reduceIte]
          refine refineLt_sound hΓ hvr hvl fun n m hn hm => ?_
          have := key m n hm hn
          subst hps
          revert this
          cases b <;> cases strict <;> simp [cmpRel] <;> omega
        · simp only [hps, ↓reduceIte]
          refine refineLt_sound hΓ hvl hvr fun m n hm hn => ?_
          have := key m n hm hn
          revert this hps
          cases b <;> cases swapped <;> cases strict <;> simp [cmpRel] <;> omega
      · simp only [Bool.not_eq_true] at hat
        simp only [hat]
        exact hΓ
    | [], _ => simpa [refineCond] using hΓ
    | [_], _ => simpa [refineCond] using hΓ
    | _ :: _ :: _ :: _, _ => simpa [refineCond] using hΓ
  | _ => simpa [refineCond] using hΓ

/-- A loop bound is the integer of the value. -/
theorem Value.toInt_of_loopBound {v : Value} {n : Int} (h : v.loopBound = some n) :
    v.toInt = some n := by
  cases v <;> simp [Value.loopBound] at h <;> subst h <;> rfl

/-! ## Loops -/

/-- A loop body that keeps the invariant `inv` from every counter value in `c` gives a loop
    that keeps it, and runs the same under the guarded table. -/
theorem denoteForLoop'_sound {g : String → List Value → Bool} {bi : Builtins} {x : String}
    {body : ImpExpr} {inv J : AEnv} {c : Iv}
    (hb : ∀ fuel (n : Int) env, c.Has n → Sat inv env → Env.NoControlFlow env →
      denote' (guardBi g bi) fuel body (Env.extend env x (.int n)) =
        denote' bi fuel body (Env.extend env x (.int n)) ∧
      Post inv inv .top (denote' bi fuel body (Env.extend env x (.int n)))) :
    ∀ fuel (lo hi : Int) env, c.1 ≤ lo → hi - 1 ≤ c.2 → Sat inv env →
      Env.NoControlFlow env →
      denoteForLoop' (guardBi g bi) fuel x lo hi body env =
        denoteForLoop' bi fuel x lo hi body env ∧
      Post J inv .top (denoteForLoop' bi fuel x lo hi body env) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi env _ _ hS hN
    rw [denoteForLoop'_run, denoteForLoop'_run]
    by_cases hge : lo ≥ hi
    · simp only [hge, ↓reduceIte]
      exact ⟨by trivial, post_val hN rfl trivial hS⟩
    · simp only [hge, ↓reduceIte]
      exact ⟨by trivial, trivial⟩
  | succ k ih =>
    intro lo hi env hlo hhi hS hN
    rw [denoteForLoop'_run, denoteForLoop'_run]
    by_cases hge : lo ≥ hi
    · simp only [hge, ↓reduceIte]
      exact ⟨by trivial, post_val hN rfl trivial hS⟩
    simp only [hge, ↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
    obtain ⟨heq, hpost⟩ := hb (k + 1) lo env ⟨hlo, by omega⟩ hS hN
    rw [heq]
    rcases hr : denote' bi (k + 1) body (Env.extend env x (.int lo)) with ⟨o, e⟩
    rw [hr] at hpost
    cases o
    case val w =>
      cases w
      case controlFlow bb u =>
        obtain ⟨hNe, hdu, hJ⟩ := hpost
        simp only [Value.isControlFlow, ↓reduceIte] at hJ
        cases bb
        · exact ih (lo + 1) hi e (by omega) hhi hJ hNe
        · exact ⟨rfl, post_val hNe hdu trivial hJ⟩
      all_goals
        obtain ⟨hNe, -, -, hSe⟩ := hpost.of_val rfl
        exact ih (lo + 1) hi e (by omega) hhi hSe hNe
    all_goals exact ⟨rfl, trivial⟩

/-! ## The checker -/

mutual

/-- Soundness of the checker: a term accepted at `(a, Γ')` from `Γ` under the loop
    invariant `J` runs under `denote'` with the guarded table `guardBi g bi` exactly as with
    `bi`, from every environment in `Γ` with no control-flow value, and its outcome satisfies
    `Post J Γ' a`. -/
theorem check_sound {g : String → List Value → Bool} {H : Spec} {bi : Builtins}
    (hS : Sound g H bi) :
    ∀ (e : ImpExpr) (J Γ : AEnv) (a : AV) (Γ' : AEnv), check H J Γ e = some (a, Γ') →
      ∀ fuel env, Sat Γ env → Env.NoControlFlow env →
      denote' (guardBi g bi) fuel e env = denote' bi fuel e env ∧
        Post J Γ' a (denote' bi fuel e env)
  | .lit l, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    simp only [check, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [denote'_lit_run, denote'_lit_run]
    exact ⟨rfl, post_val hN (Value.ofLit_deepNoControlFlow l) (litAV_mem l) hΓ⟩
  | .var x, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    simp only [check, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [denote'_var_run, denote'_var_run]
    rcases hx : env x with _ | v
    · exact ⟨by trivial, trivial⟩
    · exact ⟨rfl, post_val hN (hN x v hx) (hΓ.get hx) hΓ⟩
  | .unitVal, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    simp only [check, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [denote'_unitVal_run, denote'_unitVal_run]
    exact ⟨rfl, post_val hN rfl trivial hΓ⟩
  | .letBind x v b, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    rcases hv : check H J Γ v with _ | ⟨av, Γ1⟩ <;> simp only [check, hv, reduceCtorEq] at h
    have ihv := check_sound hS v J Γ av Γ1 hv fuel env hΓ hN
    rw [denote'_letBind_cf, denote'_letBind_cf]
    exact cfBind_step ihv.1 ihv.2 fun w e _ hNe hdw hmw hSe =>
      check_sound hS b J _ a Γ' h fuel _ (hSe.cons hmw) (hNe.extend hdw)
  | .seq x y, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    rcases hx : check H J Γ x with _ | ⟨ax, Γ1⟩ <;> simp only [check, hx, reduceCtorEq] at h
    have ihx := check_sound hS x J Γ ax Γ1 hx fuel env hΓ hN
    rw [denote'_seq_cf, denote'_seq_cf]
    exact cfBind_step ihx.1 ihx.2 fun _ e _ hNe _ _ hSe =>
      check_sound hS y J Γ1 a Γ' h fuel e hSe hNe
  | .assign x r, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    rcases hr : check H J Γ r with _ | ⟨ar, Γ1⟩ <;>
      simp only [check, hr, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ihr := check_sound hS r J Γ ar Γ1 hr fuel env hΓ hN
    rw [denote'_assign_cf, denote'_assign_cf]
    exact cfBind_step ihr.1 ihr.2 fun w e _ hNe hdw hmw hSe =>
      ⟨rfl, post_val (hNe.extend hdw) rfl trivial (hSe.cons hmw)⟩
  | .typeAscription x s, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    simp only [check] at h
    rw [Total.denote'_typeAscription_run, Total.denote'_typeAscription_run]
    exact check_sound hS x J Γ a Γ' h fuel env hΓ hN
  | .borrow x, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    simp only [check] at h
    rw [denote'_borrow_run, denote'_borrow_run]
    exact check_sound hS x J Γ a Γ' h fuel env hΓ hN
  | .deref x, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    simp only [check] at h
    rw [denote'_deref_run, denote'_deref_run]
    exact check_sound hS x J Γ a Γ' h fuel env hΓ hN
  | .app f args, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    rcases ha : checkArgs H J Γ args with _ | ⟨avs, Γ1⟩ <;>
      simp only [check, ha, reduceCtorEq] at h
    rcases hx : H.xfer f avs with _ | a0 <;>
      simp only [hx, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq,
        Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨heq, hpost⟩ := checkArgs_sound hS args J Γ avs Γ1 ha fuel env hΓ hN
    rw [denote'_app_cf, denote'_app_cf, heq]
    rcases hr : denoteArgs' bi fuel args env with ⟨_ | vs, e⟩
    · exact ⟨by trivial, trivial⟩
    · obtain ⟨hml, hdl, hSe, hNe⟩ := hpost vs e hr
      have hg : guardBi g bi f vs = bi f vs := by
        simp [guardBi, hS.guard f avs a0 vs hx hml]
      simp only [hg]
      rcases hb : bi f vs with _ | w
      · exact ⟨by trivial, trivial⟩
      · exact ⟨by trivial, post_val hNe (hS.deep f vs w hb hdl)
          (hS.result f avs a0 vs w hx hml hb) hSe⟩
  | .ifThenElse c t el, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    rcases hc : check H J Γ c with _ | ⟨ac, Γ1⟩ <;> simp only [check, hc, reduceCtorEq] at h
    rcases ht : check H J (refineCond c true Γ1) t with _ | ⟨at', Γt⟩ <;>
      rcases he : check H J (refineCond c false Γ1) el with _ | ⟨ae, Γe⟩ <;>
      simp only [ht, he, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ihc := check_sound hS c J Γ ac Γ1 hc fuel env hΓ hN
    rw [denote'_ifThenElse_cf, denote'_ifThenElse_cf]
    refine cfBind_step ihc.1 ihc.2 fun w e hr hNe hdw hmw hSe => ?_
    cases w
    case bool bb =>
      have hR := refineCond_sound hS hr hSe
      cases bb
      · obtain ⟨h1, h2⟩ := check_sound hS el J _ ae Γe he fuel e hR hNe
        exact ⟨h1, h2.weaken (fun _ hs => hs.join_right) (fun _ hm => hm.join_right)⟩
      · obtain ⟨h1, h2⟩ := check_sound hS t J _ at' Γt ht fuel e hR hNe
        exact ⟨h1, h2.weaken (fun _ hs => hs.join_left) (fun _ hm => hm.join_left)⟩
    all_goals exact ⟨by trivial, trivial⟩
  | .match_ s arms, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    rcases hs : check H J Γ s with _ | ⟨as, Γ1⟩ <;> simp only [check, hs, reduceCtorEq] at h
    have ihs := check_sound hS s J Γ as Γ1 hs fuel env hΓ hN
    rw [denote'_match_cf, denote'_match_cf]
    exact cfBind_step ihs.1 ihs.2 fun v e _ hNe hdv _ hSe =>
      checkArms_sound hS arms J Γ1 a Γ' h fuel v e hSe hNe hdv
  | .forFold x lo hi body, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    rcases hlo : check H J Γ lo with _ | ⟨al, Γ1⟩ <;> simp only [check, hlo, reduceCtorEq] at h
    cases al with
    | num il =>
      rcases hhi : check H J Γ1 hi with _ | ⟨ah, Γ2⟩ <;> simp only [hhi, reduceCtorEq] at h
      cases ah with
      | num ih =>
        dsimp only at h
        generalize hI : loopInv H.ann x body Γ2 = inv at h
        by_cases he1 : entails Γ2 inv = true <;> simp only [he1, ↓reduceIte, reduceCtorEq] at h
        rcases hb : check H inv ((x, .num (il.1, ih.2 - 1)) :: inv) body with _ | ⟨ab, Γb⟩ <;>
          simp only [hb, reduceCtorEq] at h
        by_cases he2 : entails Γb inv = true <;>
          simp only [he2, ↓reduceIte, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have ihlo := check_sound hS lo J Γ (.num il) Γ1 hlo fuel env hΓ hN
        rw [denote'_forFold_cf, denote'_forFold_cf]
        refine cfBind_step ihlo.1 ihlo.2 fun vlo e1 _ hN1 _ hm1 hS1 => ?_
        unfold forK
        have ihhi := check_sound hS hi J Γ1 (.num ih) Γ2 hhi fuel e1 hS1 hN1
        refine cfBind_step ihhi.1 ihhi.2 fun vhi e2 _ hN2 _ hm2 hS2 => ?_
        rcases hl : vlo.loopBound with _ | l
        · exact ⟨by trivial, trivial⟩
        rcases hh : vhi.loopBound with _ | hv
        · exact ⟨by trivial, trivial⟩
        obtain ⟨m, hm, hmi⟩ := hm1
        obtain ⟨n, hn, hni⟩ := hm2
        rw [Value.toInt_of_loopBound hl, Option.some.injEq] at hm
        rw [Value.toInt_of_loopBound hh, Option.some.injEq] at hn
        subst hm hn
        refine denoteForLoop'_sound (c := (il.1, ih.2 - 1)) (fun fuel' k env' hk hinv hNk => ?_)
          fuel l hv e2 hmi.1 (by have := hni.2; simp only; omega) (hS2.entails he1) hN2
        obtain ⟨q1, q2⟩ := check_sound hS body inv _ ab Γb hb fuel' (Env.extend env' x (.int k))
          (hinv.cons ⟨k, rfl, hk⟩) (hNk.extend rfl)
        exact ⟨q1, q2.weaken (fun _ hs => hs.entails he2) (fun _ _ => trivial)⟩
      | _ => simp only [reduceCtorEq] at h
    | _ => simp only [reduceCtorEq] at h
  | .cfBreak y, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    rcases hy : check H J Γ y with _ | ⟨ay, Γ1⟩ <;> simp only [check, hy, reduceCtorEq] at h
    by_cases he : entails Γ1 J = true <;>
      simp only [he, ↓reduceIte, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ihy := check_sound hS y J Γ ay Γ1 hy fuel env hΓ hN
    rw [denote'_cfBreak_cf, denote'_cfBreak_cf]
    exact cfBind_step ihy.1 ihy.2 fun _ e _ hNe hdv _ hSe =>
      ⟨rfl, post_cf hNe hdv (hSe.entails he)⟩
  | .cfContinue y, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    rcases hy : check H J Γ y with _ | ⟨ay, Γ1⟩ <;> simp only [check, hy, reduceCtorEq] at h
    by_cases he : entails Γ1 J = true <;>
      simp only [he, ↓reduceIte, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ihy := check_sound hS y J Γ ay Γ1 hy fuel env hΓ hN
    rw [denote'_cfContinue_cf, denote'_cfContinue_cf]
    exact cfBind_step ihy.1 ihy.2 fun _ e _ hNe hdv _ hSe =>
      ⟨rfl, post_cf hNe hdv (hSe.entails he)⟩
  | .lam _ _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .tuple _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .proj _ _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .forLoop _ _ _ _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .forLoopRev _ _ _ _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .whileLoop _ _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .break_ _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .continue_, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .earlyReturn _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .questionMark _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .forFoldRev _ _ _ _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .whileFold _ _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .forFoldReturn _ _ _ _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .forFoldRevReturn _ _ _ _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .whileFoldReturn _ _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .cfBreakContinue _, _, _, _, _, h, _, _, _, _ => by simp [check] at h

/-- Soundness of the checker on call arguments: the guarded table evaluates them as `bi`
    does, and their values lie in the abstract values, in order. -/
theorem checkArgs_sound {g : String → List Value → Bool} {H : Spec} {bi : Builtins}
    (hS : Sound g H bi) :
    ∀ (args : List ImpExpr) (J Γ : AEnv) (avs : List AV) (Γ' : AEnv),
      checkArgs H J Γ args = some (avs, Γ') → ∀ fuel env, Sat Γ env →
      Env.NoControlFlow env →
      denoteArgs' (guardBi g bi) fuel args env = denoteArgs' bi fuel args env ∧
        ∀ vs e, denoteArgs' bi fuel args env = (some vs, e) →
          MemList avs vs ∧ (∀ v ∈ vs, v.deepNoControlFlow = true) ∧ Sat Γ' e ∧
            Env.NoControlFlow e
  | [], J, Γ, avs, Γ', h, fuel, env, hΓ, hN => by
    simp only [checkArgs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [Total.denoteArgs'_nil_run, Total.denoteArgs'_nil_run]
    refine ⟨rfl, fun vs e he => ?_⟩
    cases he
    exact ⟨trivial, by simp, hΓ, hN⟩
  | x :: xs, J, Γ, avs, Γ', h, fuel, env, hΓ, hN => by
    rcases hx : check H J Γ x with _ | ⟨ax, Γ1⟩ <;> simp only [checkArgs, hx, reduceCtorEq] at h
    rcases hxs : checkArgs H J Γ1 xs with _ | ⟨axs, Γ2⟩ <;>
      simp only [hxs, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ihx := check_sound hS x J Γ ax Γ1 hx fuel env hΓ hN
    rw [denoteArgs'_cons_cf, denoteArgs'_cons_cf]
    refine argsCons_step (P := fun res => ∀ vs e, res = (some vs, e) →
        MemList (ax :: axs) vs ∧ (∀ v ∈ vs, v.deepNoControlFlow = true) ∧ Sat Γ2 e ∧
          Env.NoControlFlow e) ihx.1 ihx.2 (fun e vs e' he => by cases he)
      fun w e1 hN1 hd1 hm1 hS1 => ?_
    obtain ⟨heq, hpost⟩ := checkArgs_sound hS xs J Γ1 axs Γ2 hxs fuel e1 hS1 hN1
    rw [heq]
    refine ⟨rfl, fun vs e he => ?_⟩
    rcases hr2 : denoteArgs' bi fuel xs e1 with ⟨_ | ws, e2⟩ <;> rw [hr2] at he <;>
      simp only [Option.map_none, Option.map_some] at he
    · cases he
    · cases he
      obtain ⟨hml, hdl, hS2, hN2⟩ := hpost ws e hr2
      refine ⟨by simp only [MemList]; exact ⟨hm1, hml⟩, fun v hv => ?_, hS2, hN2⟩
      rcases List.mem_cons.1 hv with rfl | hv
      · exact hd1
      · exact hdl v hv

/-- Soundness of the checker on the arms of a `match` on a value with no control-flow
    value. -/
theorem checkArms_sound {g : String → List Value → Bool} {H : Spec} {bi : Builtins}
    (hS : Sound g H bi) :
    ∀ (arms : List (ImpPat × ImpExpr)) (J Γ : AEnv) (a : AV) (Γ' : AEnv),
      checkArms H J Γ arms = some (a, Γ') → ∀ fuel v env, Sat Γ env →
      Env.NoControlFlow env → v.deepNoControlFlow = true →
      denoteMatchArms' (guardBi g bi) fuel v arms env = denoteMatchArms' bi fuel v arms env ∧
        Post J Γ' a (denoteMatchArms' bi fuel v arms env)
  | [], J, Γ, a, Γ', _, fuel, v, env, _, _, _ => by
    rw [denoteMatchArms'_nil, denoteMatchArms'_nil]
    exact ⟨by trivial, trivial⟩
  | [(p, b)], J, Γ, a, Γ', h, fuel, v, env, hΓ, hN, hv => by
    simp only [checkArms] at h
    rw [denoteMatchArms'_cons (guardBi g bi) fuel v p b, denoteMatchArms'_cons bi fuel v p b]
    rcases hm : matchPat p v env with _ | env'
    · rw [denoteMatchArms'_nil, denoteMatchArms'_nil]
      exact ⟨by trivial, trivial⟩
    · exact check_sound hS b J _ a Γ' h fuel env'
        (hΓ.drop fun y hy => matchPat_agree p v env env' hm y (by simpa using hy))
        (matchPat_preserves_noControlFlow hN hv hm)
  | (p, b) :: arm :: rest, J, Γ, a, Γ', h, fuel, v, env, hΓ, hN, hv => by
    rcases hb : check H J (AEnv.drop (patVars p) Γ) b with _ | ⟨a1, Γ1⟩ <;>
      rcases hr : checkArms H J Γ (arm :: rest) with _ | ⟨a2, Γ2⟩ <;>
      simp only [checkArms, hb, hr, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [denoteMatchArms'_cons (guardBi g bi) fuel v p b, denoteMatchArms'_cons bi fuel v p b]
    rcases hm : matchPat p v env with _ | env'
    · obtain ⟨h1, h2⟩ := checkArms_sound hS (arm :: rest) J Γ a2 Γ2 hr fuel v env hΓ hN hv
      exact ⟨h1, h2.weaken (fun _ hs => hs.join_right) (fun _ hm => hm.join_right)⟩
    · obtain ⟨h1, h2⟩ := check_sound hS b J _ a1 Γ1 hb fuel env'
        (hΓ.drop fun y hy => matchPat_agree p v env env' hm y (by simpa using hy))
        (matchPat_preserves_noControlFlow hN hv hm)
      exact ⟨h1, h2.weaken (fun _ hs => hs.join_left) (fun _ hm => hm.join_left)⟩

end

/-- Soundness of the checker on a typed literal: if `checkT H Γ e = some (a, Γ')`, then from
    every environment in `Γ` with no control-flow value and at every fuel, `denote'` runs
    `e.erase` with the guarded table `guardBi g bi` exactly as with `bi` (no guard `g` fails),
    and a value that is not a control-flow value lies in `a`. -/
theorem checkT_sound {g : String → List Value → Bool} {H : Spec} {bi : Builtins}
    (hS : Sound g H bi) {e : TExpr} {Γ Γ' : AEnv} {a : AV} (h : checkT H Γ e = some (a, Γ'))
    (fuel : Nat) {env : Env} (hΓ : Sat Γ env) (hN : Env.NoControlFlow env) :
    denote' (guardBi g bi) fuel e.erase env = denote' bi fuel e.erase env ∧
      ∀ v env', denote' bi fuel e.erase env = (.val v, env') → v.isControlFlow = false →
        a.Mem v := by
  obtain ⟨h1, h2⟩ := check_sound hS e.erase [] Γ a Γ' h fuel env hΓ hN
  refine ⟨h1, fun v env' hr hcf => ?_⟩
  rw [hr] at h2
  exact (h2.of_val hcf).2.2.1

end Hax.Range

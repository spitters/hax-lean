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
bi`: the transfer functions of `H` prove the guards `g`, describe the results of `bi`, the
comparison heads of `bi` answer with the truth of their relation, `len` answers with the
length of an array, and, when `H.logic`, the Boolean and equality heads answer as `LogicSem`
says.

A relational fact of the abstract environment holds in the environment (`Sat`): a binding of
a variable drops the facts on it (`Sat.cons`), a guard comparing a variable with the length of
an array sets one (`addLen_sound`), a counted loop over `[lo, len s)` whose body binds no `s`
keeps `s` across its iterations (`denote'_keep`, from the frame of
`HaxLean/Phase/InlineLocalClosures.lean`), so its counter lies below the length of `s`
(`ctrAVLen_sat`), and the facts between the arguments of a call read in place hold of their
values (`relArgs_of_argRels`).

## Main definitions

* `cfBind`: the continuation of `denote'` after a subterm, which passes control-flow values
  and other outcomes through.
* `Post`: the postcondition of a checked term.
* `CmpVal`: the value of an operand of a comparison.
* `paramEnv`: the environment of a function body on its arguments.

## Main results

* `condOk_env`: a `condOk` condition that answers a Boolean leaves the environment.
* `refineAtoms_sound`, `refineLen_sound`, `refineCond_sound_of`, `refineCond_sound`:
  soundness of the refinement by a guard.
* `denote'_keep`: a body that binds no `s` keeps the value of `s`.
* `relArgs_of_argRels`: the facts between arguments read in place hold of their values.
* `denoteForLoop'_sound`: a loop body that keeps the invariant gives a loop that keeps it.
* `check_sound`, `checkArgs_sound`, `checkArms_sound`: soundness of the checker.
* `checkT_sound`: soundness for a `TExpr` literal through `TExpr.erase`.
* `mem_of_body`: a checked function body returns a value in its abstract value.
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

theorem lookup_map_snd (Γ : AEnv) (f : AV → AV) (y : String) :
    (Γ.map fun p => (p.1, f p.2)).lookup y = (Γ.lookup y).map f := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    obtain ⟨z, a⟩ := p
    by_cases hyz : y = z
    · subst hyz
      simp only [List.map_cons]
      rw [lookup_cons_self, lookup_cons_self]
      rfl
    · simp only [List.map_cons]
      rw [lookup_cons_ne _ _ hyz, lookup_cons_ne _ _ hyz, ih]

theorem AV.Mem.forget {a : AV} {v : Value} (xs : List String) (h : a.Mem v) :
    (a.forget xs).Mem v := by
  cases a <;> exact h

/-- The facts of `a` not on the arrays of `xs` hold in an environment that agrees with `env`
    off `xs`. -/
theorem AV.RelIn.forget {a : AV} {env env' : Env} {v : Value} {xs : List String}
    (h : a.RelIn env v) (hag : ∀ y, y ∉ xs → env' y = env y) : (a.forget xs).RelIn env' v := by
  intro p hp
  cases a with
  | idx lo hi rs =>
    simp only [AV.forget, AV.rels, List.mem_filter, Bool.not_eq_true'] at hp
    have hnot : p.1 ∉ xs := by simpa using hp.2
    obtain ⟨k, hk, w, n, hw, hn, hlt⟩ := h p hp.1
    exact ⟨k, hk, w, n, by rw [hag _ hnot]; exact hw, hn, hlt⟩
  | _ => cases hp

theorem Sat.cons {Γ : AEnv} {env : Env} {x : String} {a : AV} {v : Value} (h : Sat Γ env)
    (hv : a.Mem v) (hr : a.RelIn (Env.extend env x v) v) :
    Sat ((x, a) :: AEnv.kill x Γ) (Env.extend env x v) := by
  intro y b hy
  by_cases hyx : y = x
  · subst hyx
    rw [lookup_cons_self] at hy
    cases hy
    exact ⟨v, Env.extend_same _ _ _, hv, hr⟩
  · rw [lookup_cons_ne _ _ hyx, AEnv.kill, lookup_map_snd] at hy
    obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hy
    obtain ⟨w, hw, hm, hr0⟩ := h y b0 hb0
    refine ⟨w, by rw [Env.extend_other _ _ _ _ hyx]; exact hw, hm.forget _, hr0.forget ?_⟩
    intro z hz
    exact Env.extend_other _ _ _ _ (by simpa using hz)

theorem Sat.cons_of_get {Γ : AEnv} {env : Env} {x : String} {a : AV} {v : Value}
    (h : Sat Γ env) (hx : env x = some v) (hv : a.Mem v) (hr : a.RelIn env v) :
    Sat ((x, a) :: Γ) env := by
  intro y b hy
  by_cases hyx : y = x
  · subst hyx
    rw [lookup_cons_self] at hy
    cases hy
    exact ⟨v, hx, hv, hr⟩
  · rw [lookup_cons_ne _ _ hyx] at hy
    exact h y b hy

theorem Sat.get {Γ : AEnv} {env : Env} {x : String} {v : Value} (h : Sat Γ env)
    (hx : env x = some v) : (Γ.get x).Mem v := by
  unfold AEnv.get
  rcases hl : Γ.lookup x with _ | a
  · trivial
  · obtain ⟨v', hv', hm, -⟩ := h x a hl
    rw [hx] at hv'
    cases hv'
    exact hm

theorem Sat.getRel {Γ : AEnv} {env : Env} {x : String} {v : Value} (h : Sat Γ env)
    (hx : env x = some v) : (Γ.get x).RelIn env v := by
  unfold AEnv.get
  rcases hl : Γ.lookup x with _ | a
  · intro p hp; cases hp
  · obtain ⟨v', hv', -, hr⟩ := h x a hl
    rw [hx] at hv'
    cases hv'
    exact hr

theorem lookup_drop (xs : List String) (Γ : AEnv) (y : String) :
    (AEnv.drop xs Γ).lookup y = if y ∈ xs then none else (Γ.lookup y).map (AV.forget xs) := by
  unfold AEnv.drop
  rw [lookup_map_snd]
  induction Γ with
  | nil => simp [List.lookup]
  | cons p Γ ih =>
    obtain ⟨z, a⟩ := p
    by_cases hz : z ∈ xs
    · rw [List.filter_cons_of_neg (by simp [hz]), ih]
      by_cases hyz : y = z
      · subst hyz; simp [hz]
      · rw [lookup_cons_ne _ _ hyz]
    · rw [List.filter_cons_of_pos (by simp [hz])]
      by_cases hyz : y = z
      · subst hyz; simp [hz, List.lookup]
      · rw [lookup_cons_ne _ _ hyz, ih, lookup_cons_ne _ _ hyz]

theorem Sat.drop {Γ : AEnv} {env env' : Env} {xs : List String} (h : Sat Γ env)
    (hag : ∀ y, y ∉ xs → env' y = env y) : Sat (AEnv.drop xs Γ) env' := by
  intro y a hy
  rw [lookup_drop] at hy
  split at hy
  · cases hy
  · rename_i hc
    obtain ⟨b0, hb0, rfl⟩ := Option.map_eq_some_iff.1 hy
    obtain ⟨w, hw, hm, hr⟩ := h y b0 hb0
    exact ⟨w, by rw [hag y hc]; exact hw, hm.forget _, hr.forget hag⟩

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
  obtain ⟨v, hv, hm, hr⟩ := h x a h1
  exact ⟨v, hv, hm.join_left, hr.join_left⟩

theorem Sat.join_right {Γ1 Γ2 : AEnv} {env : Env} (h : Sat Γ2 env) :
    Sat (AEnv.join Γ1 Γ2) env := by
  intro x c hx
  rw [lookup_join] at hx
  rcases h1 : Γ1.lookup x with _ | a <;> rw [h1] at hx
  · cases hx
  rcases h2 : Γ2.lookup x with _ | b <;> simp [h2] at hx
  subst hx
  obtain ⟨v, hv, hm, hr⟩ := h x b h2
  exact ⟨v, hv, hm.join_right, hr.join_right⟩

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

/-- A fact that `Γ` entails at the bound `h` holds of every integer at most `h`. -/
theorem LenGt.of_lenEntails {Γ : AEnv} {env : Env} {h k : Int} {p : String × Int}
    (hs : Sat Γ env) (hk : k ≤ h) (he : lenEntails Γ h p = true) : AV.LenGt env k p := by
  unfold lenEntails at he
  split at he
  · rename_i l hl
    obtain ⟨w, hw, ⟨n, hn, h1, -⟩, -⟩ := hs _ _ hl
    simp only [decide_eq_true_eq] at he
    exact ⟨w, n, hw, hn, by omega⟩
  · cases he

/-- Inclusion in an environment of `Γ` keeps membership and the facts. -/
theorem AV.leIn_sat {Γ : AEnv} {env : Env} {a b : AV} {v : Value} (hs : Sat Γ env)
    (hm : a.Mem v) (hr : a.RelIn env v) (hab : a.leIn Γ b = true) :
    b.Mem v ∧ b.RelIn env v := by
  unfold AV.leIn at hab
  rcases Bool.or_eq_true_iff.1 hab with hle | hab
  · exact ⟨hm.le hle, hr.le hle⟩
  cases b with
  | idx lo hi rs =>
    cases a with
    | num i =>
      obtain ⟨n, hn, h1, h2⟩ := hm
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hab
      obtain ⟨⟨hlo, hhi⟩, hrs⟩ := hab
      refine ⟨⟨n, hn, by omega, fun h' hh => ?_⟩, fun p hp => ⟨n, hn, ?_⟩⟩
      · subst hh; simp only [hiLe, decide_eq_true_eq] at hhi; omega
      · exact LenGt.of_lenEntails hs h2 (hrs p hp)
    | idx lo' hi' ra =>
      cases hi' with
      | none => simp at hab
      | some h' =>
        obtain ⟨n, hn, h1, h2⟩ := hm
        have h2' := h2 h' rfl
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at hab
        obtain ⟨⟨hlo, hhi⟩, hrs⟩ := hab
        refine ⟨⟨n, hn, by omega, fun h'' hh => ?_⟩, fun p hp => ?_⟩
        · subst hh; simp only [hiLe, decide_eq_true_eq] at hhi; omega
        · rcases hrs p hp with hq | hq
          · have hq' : AV.le (.idx lo' (some h') ra) (.idx lo' (some h') [p]) = true := by
              simp [AV.le, hiLe, hq]
            exact hr.le hq' p (by simp [AV.rels])
          · exact ⟨n, hn, LenGt.of_lenEntails hs h2' hq⟩
    | _ => simp at hab
  | _ => cases a <;> simp at hab

theorem Sat.entails {Γ J : AEnv} {env : Env} (h : Sat Γ env) (he : entails Γ J = true) :
    Sat J env := by
  intro x a hx
  have hm := List.all_eq_true.1 he (x, a) (mem_of_lookup hx)
  simp only at hm
  rcases hl : Γ.lookup x with _ | b <;> rw [hl] at hm
  · cases hm
  obtain ⟨v, hv, hb, hr⟩ := h x b hl
  obtain ⟨h1, h2⟩ := AV.leIn_sat h hb hr hm
  exact ⟨v, hv, h1, h2⟩

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

/-- The literal `false` runs to the value `false`. -/
theorem isFalseLit_run {bi : Builtins} {fuel : Nat} {c : ImpExpr} {env e : Env} {w : Value}
    (hf : isFalseLit c = true) (hr : denote' bi fuel c env = (.val w, e)) :
    w = .bool false := by
  match c, hf with
  | .lit (.bool false), _ =>
    simp only [denote', Value.ofLit] at hr
    change (Outcome.val (Value.bool false), env) = (Outcome.val w, e) at hr
    simp only [Prod.mk.injEq, Outcome.val.injEq] at hr
    exact hr.1.symm

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


/-- The projection continuation. -/
def projK (i : Nat) (v : Value) (e : Env) : Outcome × Env :=
  match v.projIdx i with
  | some vi => (.val vi, e)
  | none => (.err s!"projection index {i} out of range", e)

theorem denote'_proj_cf (bi : Builtins) (fuel : Nat) (x : ImpExpr) (i : Nat) (env : Env) :
    denote' bi fuel (.proj x i) env = cfBind (denote' bi fuel x env) (projK i) := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  unfold cfBind projK
  rcases denote' bi fuel x env with ⟨o, e⟩
  cases o <;> try rfl
  rename_i w; cases w <;> try rfl
  all_goals
    simp only [Value.isControlFlow, Bool.false_eq_true, ↓reduceIte]
    split <;> rename_i hh <;> simp only [hh] <;> rfl

theorem denote'_earlyReturn_cf (bi : Builtins) (fuel : Nat) (x : ImpExpr) (env : Env) :
    denote' bi fuel (.earlyReturn x) env =
      cfBind (denote' bi fuel x env) (fun v e => (.earlyRet v, e)) := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  unfold cfBind
  rcases denote' bi fuel x env with ⟨o, e⟩
  cases o <;> try rfl
  rename_i w; cases w <;> rfl

/-- The continuation of `?`. -/
def qmK (v : Value) (e : Env) : Outcome × Env :=
  match v with
  | .result true u => (.val u, e)
  | .result false u => (.earlyRet (.result false u), e)
  | _ => (.err "? operator on non-Result", e)

theorem denote'_questionMark_cf (bi : Builtins) (fuel : Nat) (x : ImpExpr) (env : Env) :
    denote' bi fuel (.questionMark x) env = cfBind (denote' bi fuel x env) qmK := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  unfold cfBind qmK
  rcases denote' bi fuel x env with ⟨o, e⟩
  cases o <;> try rfl
  rename_i w; cases w <;> try rfl
  rename_i ok u; cases ok <;> rfl

theorem denote'_tuple_run (bi : Builtins) (fuel : Nat) (xs : List ImpExpr) (env : Env) :
    denote' bi fuel (.tuple xs) env =
      match denoteArgs' bi fuel xs env with
      | (some vs, e) => (.val (.tuple vs), e)
      | (none, e) => (.err "non-value in tuple elements", e) := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  rcases denoteArgs' bi fuel xs env with ⟨r, e⟩
  cases r <;> rfl

theorem deepNoControlFlow_tuple_of {vs : List Value}
    (h : ∀ v ∈ vs, v.deepNoControlFlow = true) : (Value.tuple vs).deepNoControlFlow = true := by
  simp only [Value.deepNoControlFlow]
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [Value.deepNoControlFlow_list_cons, Bool.and_eq_true]
    exact ⟨h v (List.mem_cons_self), ih fun w hw => h w (List.mem_cons_of_mem _ hw)⟩

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
  · subst ha; exact (h.get hv).strip

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
    have hxv : env x = some va := hA
    rcases hx : Γ0.get x with _ | ix | _ | ⟨lo, hi, rs⟩
    · cases ab <;> exact h
    · cases ab with
      | num ib =>
        obtain ⟨m, hm, hmi⟩ : (AV.num ix).Mem va := hx ▸ h0.get hxv
        obtain ⟨n, hn, hni⟩ : (AV.num ib).Mem vb := atomAV_mem h0 hb hB
        have := hrel m n hm hn
        refine h.cons_of_get hxv ⟨m, hm, hmi.meet ⟨hmi.1, ?_⟩⟩ (fun p hp => by cases hp)
        have := hni.2
        omega
      | _ => exact h
    · cases ab <;> exact h
    · cases ab with
      | num ib =>
        obtain ⟨m, hm, hm1, hm2⟩ : (AV.idx lo hi rs).Mem va := hx ▸ h0.get hxv
        have hr : (AV.idx lo hi rs).RelIn env va := hx ▸ h0.getRel hxv
        obtain ⟨n, hn, hni⟩ : (AV.num ib).Mem vb := atomAV_mem h0 hb hB
        have := hrel m n hm hn
        have := hni.2
        refine h.cons_of_get hxv ⟨m, hm, hm1, fun h' hh => ?_⟩ hr
        cases hi with
        | none => simp only [hiMin, Option.some.injEq] at hh; omega
        | some a => simp only [hiMin, Option.some.injEq] at hh; have := hm2 a rfl; omega
      | _ => exact h
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
    have hyv : env y = some vb := hB
    rcases hy : Γ0.get y with _ | iy | _ | ⟨lo, hi, rs⟩
    · cases aa <;> exact h
    · cases aa with
      | num ia =>
        obtain ⟨n, hn, hni⟩ : (AV.num iy).Mem vb := hy ▸ h0.get hyv
        obtain ⟨m, hm, hmi⟩ : (AV.num ia).Mem va := atomAV_mem h0 ha hA
        have := hrel m n hm hn
        refine h.cons_of_get hyv ⟨n, hn, hni.meet ⟨?_, hni.2⟩⟩ (fun p hp => by cases hp)
        have := hmi.1
        omega
      | _ => exact h
    · cases aa <;> exact h
    · cases aa with
      | num ia =>
        obtain ⟨n, hn, hn1, hn2⟩ : (AV.idx lo hi rs).Mem vb := hy ▸ h0.get hyv
        have hr : (AV.idx lo hi rs).RelIn env vb := hy ▸ h0.getRel hyv
        obtain ⟨m, hm, hmi⟩ : (AV.num ia).Mem va := atomAV_mem h0 ha hA
        have := hrel m n hm hn
        have := hmi.1
        exact h.cons_of_get hyv ⟨n, hn, by omega, hn2⟩ hr
      | _ => exact h
  | _ => exact h

/-- The refinement by `A < B` (`strict`) or `A ≤ B` is sound. -/
theorem refineLt_sound {Γ : AEnv} {env : Env} {A B : ImpExpr} {s : Bool} {va vb : Value}
    (h : Sat Γ env) (hA : atomVal env A = some va) (hB : atomVal env B = some vb)
    (hrel : ∀ m n, va.toInt = some m → vb.toInt = some n → m + (if s then 1 else 0) ≤ n) :
    Sat (refineLt Γ A B s) env :=
  refineLower_sound h (refineUpper_sound h h hA hB hrel) hA hB hrel

/-- The refinement by a call of a head on two atoms that answered `b` is sound, for a table
    whose comparison heads answer as `cmp` says and, with `lg`, whose Boolean heads answer
    as `LogicSem` says. -/
theorem refineAtoms_sound {bi : Builtins} {lg : Bool}
    (hcmp : ∀ op strict swapped vl vr b m n, cmpOf op = some (strict, swapped) →
      bi op [vl, vr] = some (.bool b) → vl.toInt = some m → vr.toInt = some n →
      (b = true ↔ cmpRel strict swapped m n))
    (hL : lg = true → LogicSem bi) {op : String} {l r : ImpExpr} {b : Bool} {Γ : AEnv}
    {env : Env} {vl vr : Value} (hΓ : Sat Γ env) (hvl : atomVal env l = some vl)
    (hvr : atomVal env r = some vr) (hb : bi op [vl, vr] = some (.bool b)) :
    Sat (refineAtoms lg op l r b Γ) env := by
  unfold refineAtoms
  rcases hop : cmpOf op with _ | ⟨strict, swapped⟩
  · rcases hq : eqOf op with _ | q
    · exact hΓ
    · by_cases hc : (lg && b == q) = true
      · simp only [hc, ↓reduceIte]
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        have key := fun m n hm hn => ((hL hc.1).eq op q vl vr b m n hq hb hm hn).1 hc.2
        refine refineLt_sound (refineLt_sound hΓ hvl hvr fun m n hm hn => ?_) hvr hvl
          fun n m hn hm => ?_
        · have := key m n hm hn
          simp only [Bool.false_eq_true, ↓reduceIte]
          omega
        · have := key m n hm hn
          simp only [Bool.false_eq_true, ↓reduceIte]
          omega
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        exact hΓ
  · have key := fun m n hm hn => hcmp op strict swapped vl vr b m n hop hb hm hn
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

/-- A call that evaluates to a value evaluated its arguments to a list on which the table
    answers with that value. -/
theorem denote'_app_val {bi : Builtins} {fuel : Nat} {op : String} {args : List ImpExpr}
    {env e : Env} {w : Value} (h : denote' bi fuel (.app op args) env = (.val w, e)) :
    ∃ vs, denoteArgs' bi fuel args env = (some vs, e) ∧ bi op vs = some w := by
  rw [denote'_app_cf] at h
  rcases hr : denoteArgs' bi fuel args env with ⟨_ | vs, e'⟩ <;> rw [hr] at h
  · cases h
  · rcases hb : bi op vs with _ | w' <;> simp only [hb] at h
    · cases h
    · cases h; exact ⟨vs, rfl, hb⟩

/-- Arguments that evaluate to a list evaluate their first element to a value. -/
theorem denoteArgs'_cons_val {bi : Builtins} {fuel : Nat} {x : ImpExpr} {xs : List ImpExpr}
    {env e : Env} {vs : List Value} (h : denoteArgs' bi fuel (x :: xs) env = (some vs, e)) :
    ∃ v e1 ws, denote' bi fuel x env = (.val v, e1) ∧
      denoteArgs' bi fuel xs e1 = (some ws, e) ∧ vs = v :: ws := by
  rw [denoteArgs'_cons_cf] at h
  rcases hx : denote' bi fuel x env with ⟨o, e1⟩
  rw [hx] at h
  cases o with
  | val v =>
    by_cases hc : v.isControlFlow = true
    · simp only [argsCons, hc, ↓reduceIte] at h; cases h
    · simp only [argsCons, hc, Bool.false_eq_true, ↓reduceIte] at h
      rcases hr : denoteArgs' bi fuel xs e1 with ⟨_ | ws, e2⟩ <;> rw [hr] at h
      · cases h
      · simp only [Option.map_some] at h
        cases h
        exact ⟨v, e1, ws, rfl, hr, rfl⟩
  | _ => simp only [argsCons] at h; cases h

/-- The empty argument list evaluates to the empty list in the same environment. -/
theorem denoteArgs'_nil_val {bi : Builtins} {fuel : Nat} {env e : Env} {vs : List Value}
    (h : denoteArgs' bi fuel [] env = (some vs, e)) : vs = [] ∧ e = env := by
  rw [Total.denoteArgs'_nil_run] at h
  cases h; exact ⟨rfl, rfl⟩

/-- A call of two arguments that evaluates to a value. -/
theorem denote'_app2_val {bi : Builtins} {fuel : Nat} {op : String} {l r : ImpExpr}
    {env e : Env} {w : Value} (h : denote' bi fuel (.app op [l, r]) env = (.val w, e)) :
    ∃ vl vr e1, denote' bi fuel l env = (.val vl, e1) ∧ denote' bi fuel r e1 = (.val vr, e) ∧
      bi op [vl, vr] = some w := by
  obtain ⟨vs, ha1, hb⟩ := denote'_app_val h
  obtain ⟨vl, e1, ws, hl, ha2, rfl⟩ := denoteArgs'_cons_val ha1
  obtain ⟨vr, e2, us, hr, ha3, rfl⟩ := denoteArgs'_cons_val ha2
  obtain ⟨rfl, rfl⟩ := denoteArgs'_nil_val ha3
  exact ⟨vl, vr, e1, hl, hr, hb⟩

/-- A call of one argument that evaluates to a value. -/
theorem denote'_app1_val {bi : Builtins} {fuel : Nat} {op : String} {c : ImpExpr}
    {env e : Env} {w : Value} (h : denote' bi fuel (.app op [c]) env = (.val w, e)) :
    ∃ v, denote' bi fuel c env = (.val v, e) ∧ bi op [v] = some w := by
  obtain ⟨vs, ha1, hb⟩ := denote'_app_val h
  obtain ⟨v, e1, ws, hc, ha2, rfl⟩ := denoteArgs'_cons_val ha1
  obtain ⟨rfl, rfl⟩ := denoteArgs'_nil_val ha2
  exact ⟨v, hc, hb⟩

/-- A term that reads a variable in place evaluates, when to a value, to the variable's value
    and leaves the environment. -/
theorem denote'_argVar_val {bi : Builtins} {fuel : Nat} {env : Env} :
    ∀ (a : ImpExpr) {s : String} {v : Value} {e : Env}, argVar a = some s →
      denote' bi fuel a env = (.val v, e) → e = env ∧ env s = some v
  | .var x, s, v, e, hs, h => by
    simp only [argVar, Option.some.injEq] at hs
    subst hs
    rw [denote'_var_run] at h
    rcases hx : env x with _ | w <;> rw [hx] at h <;> cases h
    exact ⟨rfl, rfl⟩
  | .borrow a, s, v, e, hs, h => by
    rw [denote'_borrow_run] at h
    exact denote'_argVar_val a hs h
  | .deref a, s, v, e, hs, h => by
    rw [denote'_deref_run] at h
    exact denote'_argVar_val a hs h
  | .typeAscription a _, s, v, e, hs, h => by
    rw [Total.denote'_typeAscription_run] at h
    exact denote'_argVar_val a hs h
  | .lit _, _, _, _, hs, _ | .unitVal, _, _, _, hs, _ | .letBind _ _ _, _, _, _, hs, _
  | .seq _ _, _, _, _, hs, _ | .assign _ _, _, _, _, hs, _ | .app _ _, _, _, _, hs, _
  | .ifThenElse _ _ _, _, _, _, hs, _ | .match_ _ _, _, _, _, hs, _
  | .forFold _ _ _ _, _, _, _, hs, _ | .whileFold _ _, _, _, _, hs, _
  | .tuple _, _, _, _, hs, _ | .proj _ _, _, _, _, hs, _ | .earlyReturn _, _, _, _, hs, _
  | .questionMark _, _, _, _, hs, _ | .cfBreak _, _, _, _, hs, _
  | .cfContinue _, _, _, _, hs, _ | .lam _ _, _, _, _, hs, _ | .forLoop _ _ _ _, _, _, _, hs, _
  | .forLoopRev _ _ _ _, _, _, _, hs, _ | .whileLoop _ _, _, _, _, hs, _
  | .break_ _, _, _, _, hs, _ | .continue_, _, _, _, hs, _ | .forFoldRev _ _ _ _, _, _, _, hs, _
  | .forFoldReturn _ _ _ _, _, _, _, hs, _ | .forFoldRevReturn _ _ _ _, _, _, _, hs, _
  | .whileFoldReturn _ _, _, _, _, hs, _ | .cfBreakContinue _, _, _, _, hs, _ => by
    simp [argVar] at hs

/-- The value of an operand of a comparison: an atom's value, or the answer of `len` on the
    value of the array variable. -/
def CmpVal (bi : Builtins) (env : Env) (e : ImpExpr) (v : Value) : Prop :=
  atomVal env e = some v ∨ ∃ s w, lenVar e = some s ∧ env s = some w ∧ bi "len" [w] = some v

theorem lenVar_eq_some {A : ImpExpr} {s : String} (h : lenVar A = some s) :
    ∃ a, A = .app "len" [a] ∧ argVar a = some s := by
  unfold lenVar at h
  split at h
  · exact ⟨_, rfl, h⟩
  · cases h

/-- An operand of a comparison that evaluates to a value leaves the environment. -/
theorem denote'_cmpArg_val {bi : Builtins} {fuel : Nat} {env e : Env} {A : ImpExpr}
    {v : Value} (hA : isCmpArg A = true) (h : denote' bi fuel A env = (.val v, e)) :
    e = env ∧ CmpVal bi env A v := by
  by_cases hat : isAtom A = true
  · obtain ⟨he, hv⟩ := denote'_atom hat h
    exact ⟨he, .inl (hv v rfl)⟩
  · have hl : (lenVar A).isSome = true := by simpa [isCmpArg, hat] using hA
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hl
    obtain ⟨a, rfl, ha⟩ := lenVar_eq_some hs
    obtain ⟨w, h1, hb⟩ := denote'_app1_val h
    obtain ⟨rfl, hw⟩ := denote'_argVar_val a ha h1
    exact ⟨rfl, .inr ⟨s, w, hs, hw, hb⟩⟩

/-- A `condOk` condition that answers a Boolean leaves the environment. -/
theorem condOk_env {bi : Builtins} (hL : LogicSem bi) (c : ImpExpr) (hc : condOk c = true)
    {fuel : Nat} {env e : Env} {b : Bool} (h : denote' bi fuel c env = (.val (.bool b), e)) :
    e = env := by
  cases c with
  | var _ => exact (denote'_atom rfl h).1
  | lit _ => exact (denote'_atom rfl h).1
  | app op args =>
    match args, hc, h with
    | [l, r], hc, h =>
      by_cases hat : (isCmpArg l && isCmpArg r) = true
      · simp only [Bool.and_eq_true] at hat
        obtain ⟨vl, vr, e1, h1, h2, -⟩ := denote'_app2_val h
        rw [(denote'_cmpArg_val hat.2 h2).1, (denote'_cmpArg_val hat.1 h1).1]
      · simp only [condOk, hat, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true] at hc
        obtain ⟨⟨hop, hl⟩, hr⟩ := hc
        obtain ⟨vl, vr, e1, h1, h2, hb⟩ := denote'_app2_val h
        obtain ⟨x, y, rfl, rfl⟩ : ∃ x y, vl = .bool x ∧ vr = .bool y := by
          rcases hop with hop | hop
          · obtain ⟨x, y, h1, h2, -⟩ := hL.and_ op vl vr _ hop hb; exact ⟨x, y, h1, h2⟩
          · obtain ⟨x, y, h1, h2, -⟩ := hL.or_ op vl vr _ hop hb; exact ⟨x, y, h1, h2⟩
        rw [condOk_env hL r hr h2, condOk_env hL l hl h1]
    | [c], hc, h =>
      simp only [condOk, Bool.and_eq_true] at hc
      obtain ⟨v, h1, hb⟩ := denote'_app1_val h
      obtain ⟨x, rfl, -⟩ := hL.not_ op v _ hc.1 hb
      exact condOk_env hL c hc.2 h1
    | [], hc, _ => simp [condOk] at hc
    | _ :: _ :: _ :: _, hc, _ => simp [condOk] at hc
  | _ => simp [condOk] at hc

/-- An abstract value with a fact that holds of its value keeps its meaning. -/
theorem AV.addRel_sat {a : AV} {env : Env} {v : Value} {p : String × Int} (hm : a.Mem v)
    (hr : a.RelIn env v) (hp : ∀ m, v.toInt = some m → LenGt env m p) :
    (a.addRel p).Mem v ∧ (a.addRel p).RelIn env v := by
  cases a with
  | num i =>
    obtain ⟨n, hn, hi⟩ := hm
    refine ⟨⟨n, hn, hi.1, fun h hh => by cases hh; exact hi.2⟩, fun q hq => ?_⟩
    simp only [addRel, rels, List.mem_singleton] at hq
    subst hq
    exact ⟨n, hn, hp n hn⟩
  | idx lo hi rs =>
    obtain ⟨n, hn, -⟩ := id hm
    refine ⟨hm, fun q hq => ?_⟩
    simp only [addRel, rels, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨n, hn, hp n hn⟩
    · exact hr q hq
  | _ => exact ⟨hm, hr⟩

/-- Adding the fact `A < len s` (`strict`) or `A ≤ len s` is sound when it holds. -/
theorem addLen_sound {bi : Builtins}
    (hlen : ∀ arr v, bi "len" [arr] = some v → ∃ n, arr.arrayLen = some n ∧ v.toInt = some n)
    {Γ : AEnv} {env : Env} {A B : ImpExpr} {s : Bool} {va vb : Value} (h : Sat Γ env)
    (hA : CmpVal bi env A va) (hB : CmpVal bi env B vb)
    (hrel : ∀ m n, va.toInt = some m → vb.toInt = some n → m + (if s then 1 else 0) ≤ n) :
    Sat (addLen Γ A B s) env := by
  unfold addLen
  split
  · rename_i x arr hl
    have hxv : env x = some va := by
      rcases hA with hA | ⟨_, _, hA, _⟩
      · exact hA
      · simp [lenVar] at hA
    rcases hB with hB | ⟨arr', w, hB', hw, hb⟩
    · obtain ⟨a, rfl, -⟩ := lenVar_eq_some hl
      simp [atomVal] at hB
    rw [hl, Option.some.injEq] at hB'
    subst hB'
    obtain ⟨n, hn, hvn⟩ := hlen w vb hb
    obtain ⟨hm, hr⟩ := AV.addRel_sat (p := (arr, if s then 0 else -1)) (h.get hxv)
      (h.getRel hxv) fun m hm => ⟨w, n, hw, hn, by
        have := hrel m n hm hvn
        cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] at this ⊢ <;> omega⟩
    exact h.cons_of_get hxv hm hr
  · exact h

/-- The refinement by a comparison of an atom and the length of an array that answered `b`
    is sound. -/
theorem refineLen_sound {bi : Builtins}
    (hcmp : ∀ op strict swapped vl vr b m n, cmpOf op = some (strict, swapped) →
      bi op [vl, vr] = some (.bool b) → vl.toInt = some m → vr.toInt = some n →
      (b = true ↔ cmpRel strict swapped m n))
    (hlen : ∀ arr v, bi "len" [arr] = some v → ∃ n, arr.arrayLen = some n ∧ v.toInt = some n)
    {op : String} {l r : ImpExpr} {b : Bool} {Γ : AEnv} {env : Env} {vl vr : Value}
    (hΓ : Sat Γ env) (hvl : CmpVal bi env l vl) (hvr : CmpVal bi env r vr)
    (hb : bi op [vl, vr] = some (.bool b)) :
    Sat (refineLen op l r b Γ) env := by
  unfold refineLen
  rcases hop : cmpOf op with _ | ⟨strict, swapped⟩
  · exact hΓ
  · have key := fun m n hm hn => hcmp op strict swapped vl vr b m n hop hb hm hn
    by_cases hps : b = swapped
    · simp only [hps, ↓reduceIte]
      refine addLen_sound hlen hΓ hvr hvl fun n m hn hm => ?_
      have := key m n hm hn
      subst hps
      revert this
      cases b <;> cases strict <;> simp [cmpRel] <;> omega
    · simp only [hps, ↓reduceIte]
      refine addLen_sound hlen hΓ hvl hvr fun m n hm hn => ?_
      have := key m n hm hn
      revert this hps
      cases b <;> cases swapped <;> cases strict <;> simp [cmpRel] <;> omega

/-- The refinement by a condition that answered `b` is sound, for a table whose comparison
    heads answer as `cmp` says, whose `len` answers with the length of an array, and, with
    `lg`, whose Boolean heads answer as `LogicSem` says. -/
theorem refineCond_sound_of {bi : Builtins} {lg : Bool}
    (hcmp : ∀ op strict swapped vl vr b m n, cmpOf op = some (strict, swapped) →
      bi op [vl, vr] = some (.bool b) → vl.toInt = some m → vr.toInt = some n →
      (b = true ↔ cmpRel strict swapped m n))
    (hlen : ∀ arr v, bi "len" [arr] = some v → ∃ n, arr.arrayLen = some n ∧ v.toInt = some n)
    (hL : lg = true → LogicSem bi) (c : ImpExpr) (b : Bool) (Γ : AEnv) {fuel : Nat}
    {env e : Env} (hc : denote' bi fuel c env = (.val (.bool b), e)) (hΓ : Sat Γ e) :
    Sat (refineCond lg c b Γ) e := by
  cases c with
  | app op args =>
    match args, hc with
    | [l, r], hc =>
      simp only [refineCond]
      by_cases hat : (isAtom l && isAtom r) = true
      · simp only [hat, ↓reduceIte]
        have hat' := hat
        simp only [Bool.and_eq_true] at hat'
        obtain ⟨rfl, vl, vr, hvl, hvr, hb⟩ := denote'_cmp_atoms hat'.1 hat'.2 hc
        exact refineAtoms_sound hcmp hL hΓ hvl hvr hb
      simp only [hat, Bool.false_eq_true, ↓reduceIte]
      by_cases hcm : (isCmpArg l && isCmpArg r) = true
      · simp only [hcm, ↓reduceIte]
        simp only [Bool.and_eq_true] at hcm
        obtain ⟨vl, vr, e1, h1, h2, hb⟩ := denote'_app2_val hc
        obtain ⟨rfl, hvl⟩ := denote'_cmpArg_val hcm.1 h1
        obtain ⟨rfl, hvr⟩ := denote'_cmpArg_val hcm.2 h2
        exact refineLen_sound hcmp hlen hΓ hvl hvr hb
      simp only [hcm, Bool.false_eq_true, ↓reduceIte]
      by_cases hand : (lg && isAnd op && condOk l && condOk r) = true
      · simp only [hand, ↓reduceIte]
        simp only [Bool.and_eq_true] at hand
        obtain ⟨⟨⟨hlg, hop⟩, hl⟩, hr⟩ := hand
        cases b
        · exact hΓ
        obtain ⟨vl, vr, e1, h1, h2, hb⟩ := denote'_app2_val hc
        obtain ⟨x, y, rfl, rfl, hxy⟩ := (hL hlg).and_ op vl vr true hop hb
        obtain ⟨rfl, rfl⟩ : x = true ∧ y = true := by
          simpa only [Bool.and_eq_true] using hxy.symm
        have he2 := condOk_env (hL hlg) r hr h2
        subst he2
        have he1 := condOk_env (hL hlg) l hl h1
        subst he1
        exact refineCond_sound_of hcmp hlen hL r true _ h2
          (refineCond_sound_of hcmp hlen hL l true Γ h1 hΓ)
      simp only [hand, Bool.false_eq_true, ↓reduceIte]
      by_cases hor : (lg && isOr op && condOk l && condOk r) = true
      · simp only [hor, ↓reduceIte]
        simp only [Bool.and_eq_true] at hor
        obtain ⟨⟨⟨hlg, hop⟩, hl⟩, hr⟩ := hor
        cases b
        · obtain ⟨vl, vr, e1, h1, h2, hb⟩ := denote'_app2_val hc
          obtain ⟨x, y, rfl, rfl, hxy⟩ := (hL hlg).or_ op vl vr false hop hb
          obtain ⟨rfl, rfl⟩ : x = false ∧ y = false := by
            simpa only [Bool.or_eq_false_iff] using hxy.symm
          have he2 := condOk_env (hL hlg) r hr h2
          subst he2
          have he1 := condOk_env (hL hlg) l hl h1
          subst he1
          exact refineCond_sound_of hcmp hlen hL r false _ h2
            (refineCond_sound_of hcmp hlen hL l false Γ h1 hΓ)
        · exact hΓ
      simp only [hor, Bool.false_eq_true, ↓reduceIte]
      exact hΓ
    | [c], hc =>
      simp only [refineCond]
      by_cases hn : (lg && isNot op) = true
      · simp only [hn, ↓reduceIte]
        simp only [Bool.and_eq_true] at hn
        obtain ⟨v, h1, hb⟩ := denote'_app1_val hc
        obtain ⟨x, rfl, rfl⟩ := (hL hn.1).not_ op v b hn.2 hb
        simpa using refineCond_sound_of hcmp hlen hL c x Γ h1 hΓ
      · simp only [hn, Bool.false_eq_true, ↓reduceIte]
        exact hΓ
    | [], _ => simpa [refineCond] using hΓ
    | _ :: _ :: _ :: _, _ => simpa [refineCond] using hΓ
  | _ => simpa [refineCond] using hΓ

/-- The refinement by a condition that evaluated to `b` is sound under `Sound`. -/
theorem refineCond_sound {g : String → List Value → Bool} {H : Spec} {bi : Builtins}
    (hS : Sound g H bi) {fuel : Nat} {c : ImpExpr} {b : Bool} {Γ : AEnv} {env e : Env}
    (hc : denote' bi fuel c env = (.val (.bool b), e)) (hΓ : Sat Γ e) :
    Sat (refineCond H.logic c b Γ) e :=
  refineCond_sound_of hS.cmp hS.len hS.logic c b Γ hc hΓ

/-- A loop bound is the integer of the value. -/
theorem Value.toInt_of_loopBound {v : Value} {n : Int} (h : v.loopBound = some n) :
    v.toInt = some n := by
  cases v <;> simp [Value.loopBound] at h <;> subst h <;> rfl

/-! ## Loops -/

/-- A body that binds no `s` keeps the value of `s` on every run that does not end in an
    error. -/
theorem denote'_keep {bi : Builtins} {s : String} {body : ImpExpr}
    (hf : InlineLocalClosures.frameOk (fun _ => true) (fun n => n != s) (fun _ => true) body =
      true)
    (fuel : Nat) {env e : Env} {o : Outcome} (h : denote' bi fuel body env = (o, e))
    (ho : ¬ InlineLocalClosures.IsErr o) : e s = env s := by
  have hfr := InlineLocalClosures.denote'_frame (R := fun e₁ e₂ => e₁ = e₂ ∧ e₂ s = env s)
    (bi₁ := bi) (bi₂ := bi) id (fun _ => true) (fun n => n != s) (fun _ => true)
    (fun e₁ e₂ x hR _ => by rw [hR.1]; rfl)
    (fun e₁ e₂ n w hR hn => ⟨by rw [hR.1], by
      rw [Env.extend_other _ _ _ _ (fun hs => by subst hs; simp at hn)]; exact hR.2⟩)
    (fun _ _ => rfl) body hf fuel
  rw [InlineLocalClosures.renameReads_id body
    (InlineLocalClosures.frameOk_mono (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) body
      hf)] at hfr
  obtain ⟨s1, -, hR⟩ := hfr env env ⟨rfl, rfl⟩ o e h ho
  exact hR.2

/-- A loop body that keeps the invariant `inv` and the property `P` of the environment from
    every counter value in `c` gives a loop that keeps them, and runs the same under the
    guarded table. -/
theorem denoteForLoop'_sound {g : String → List Value → Bool} {bi : Builtins} {x : String}
    {body : ImpExpr} {inv J : AEnv} {c : Iv} {P : Env → Prop}
    (hb : ∀ fuel (n : Int) env, c.Has n → Sat inv env → P env → Env.NoControlFlow env →
      denote' (guardBi g bi) fuel body (Env.extend env x (.int n)) =
        denote' bi fuel body (Env.extend env x (.int n)) ∧
      Post inv inv .top (denote' bi fuel body (Env.extend env x (.int n))))
    (hP : ∀ fuel (n : Int) env o e, P env →
      denote' bi fuel body (Env.extend env x (.int n)) = (o, e) →
      ¬ InlineLocalClosures.IsErr o → P e) :
    ∀ fuel (lo hi : Int) env, c.1 ≤ lo → hi - 1 ≤ c.2 → Sat inv env → P env →
      Env.NoControlFlow env →
      denoteForLoop' (guardBi g bi) fuel x lo hi body env =
        denoteForLoop' bi fuel x lo hi body env ∧
      Post J inv .top (denoteForLoop' bi fuel x lo hi body env) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi env _ _ hS _ hN
    rw [denoteForLoop'_run, denoteForLoop'_run]
    by_cases hge : lo ≥ hi
    · simp only [hge, ↓reduceIte]
      exact ⟨by trivial, post_val hN rfl trivial hS⟩
    · simp only [hge, ↓reduceIte]
      exact ⟨by trivial, trivial⟩
  | succ k ih =>
    intro lo hi env hlo hhi hS hPe hN
    rw [denoteForLoop'_run, denoteForLoop'_run]
    by_cases hge : lo ≥ hi
    · simp only [hge, ↓reduceIte]
      exact ⟨by trivial, post_val hN rfl trivial hS⟩
    simp only [hge, ↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
    obtain ⟨heq, hpost⟩ := hb (k + 1) lo env ⟨hlo, by omega⟩ hS hPe hN
    rw [heq]
    rcases hr : denote' bi (k + 1) body (Env.extend env x (.int lo)) with ⟨o, e⟩
    rw [hr] at hpost
    cases o
    case val w =>
      have hPe' := hP (k + 1) lo env _ e hPe hr fun ⟨_, hm⟩ => by cases hm
      cases w
      case controlFlow bb u =>
        obtain ⟨hNe, hdu, hJ⟩ := hpost
        simp only [Value.isControlFlow, ↓reduceIte] at hJ
        cases bb
        · exact ih (lo + 1) hi e (by omega) hhi hJ hPe' hNe
        · exact ⟨rfl, post_val hNe hdu trivial hJ⟩
      all_goals
        obtain ⟨hNe, -, -, hSe⟩ := hpost.of_val rfl
        exact ih (lo + 1) hi e (by omega) hhi hSe hPe' hNe
    all_goals exact ⟨rfl, trivial⟩


/-- A `while` loop whose condition, checked at `Γc` from the invariant `inv`, keeps the
    invariant when it fails, and whose body, from the condition's refinement, keeps the
    invariant, runs the same under the guarded table and keeps the invariant. -/
theorem denoteWhile'_sound {g : String → List Value → Bool} {H : Spec} {bi : Builtins}
    (hS : Sound g H bi) {c body : ImpExpr} {inv J Γc : AEnv} {ac : AV}
    (hc : ∀ fuel env, Sat inv env → Env.NoControlFlow env →
      denote' (guardBi g bi) fuel c env = denote' bi fuel c env ∧
        Post J Γc ac (denote' bi fuel c env))
    (hci : entails Γc inv = true)
    (hb : ∀ fuel env, Sat (refineCond H.logic c true Γc) env → Env.NoControlFlow env →
      denote' (guardBi g bi) fuel body env = denote' bi fuel body env ∧
        Post inv inv .top (denote' bi fuel body env)) :
    ∀ fuel env, Sat inv env → Env.NoControlFlow env →
      denoteWhile' (guardBi g bi) fuel c body env = denoteWhile' bi fuel c body env ∧
        Post J inv .top (denoteWhile' bi fuel c body env) := by
  intro fuel
  induction fuel with
  | zero =>
    intro env _ _
    unfold denoteWhile'
    simp only [↓reduceIte]
    exact ⟨by trivial, trivial⟩
  | succ k ih =>
    intro env hS0 hN
    rw [denoteWhile'_succ_run, denoteWhile'_succ_run]
    obtain ⟨hceq, hcp⟩ := hc (k + 1) env hS0 hN
    rw [hceq]
    rcases hr : denote' bi (k + 1) c env with ⟨o, e1⟩
    rw [hr] at hcp
    cases o
    case val w =>
      cases w
      case controlFlow bb u =>
        obtain ⟨hN1, hdu, hJ⟩ := hcp
        exact ⟨rfl, hN1, hdu, hJ⟩
      case bool bb =>
        obtain ⟨hN1, -, -, hS1⟩ := hcp.of_val rfl
        cases bb
        · exact ⟨rfl, post_val hN1 rfl trivial (hS1.entails hci)⟩
        · have hR := refineCond_sound hS hr hS1
          obtain ⟨hbeq, hbp⟩ := hb (k + 1) e1 hR hN1
          simp only
          rw [hbeq]
          rcases hr2 : denote' bi (k + 1) body e1 with ⟨o2, e2⟩
          rw [hr2] at hbp
          cases o2
          case val w2 =>
            cases w2
            case controlFlow b2 u2 =>
              obtain ⟨hN2, hdu2, hJ2⟩ := hbp
              simp only [Value.isControlFlow, ↓reduceIte] at hJ2
              cases b2
              · exact ih e2 hJ2 hN2
              · exact ⟨rfl, post_val hN2 hdu2 trivial hJ2⟩
            all_goals
              obtain ⟨hN2, -, -, hS2⟩ := hbp.of_val rfl
              exact ih e2 hS2 hN2
          all_goals exact ⟨rfl, trivial⟩
      all_goals exact ⟨rfl, trivial⟩
    all_goals exact ⟨rfl, trivial⟩

/-! ## Facts between arguments -/

/-- An argument read in place evaluates, when to a value, to the value of the variable it
    reads and leaves the environment. -/
theorem denote'_pureArg_val {bi : Builtins} {fuel : Nat} {env e : Env} {a : ImpExpr}
    {v : Value} (ha : pureArg a = true) (h : denote' bi fuel a env = (.val v, e)) :
    e = env ∧ ∀ s, argVar a = some s → env s = some v := by
  by_cases hat : isAtom a = true
  · obtain ⟨he, hv⟩ := denote'_atom hat h
    refine ⟨he, fun s hs => ?_⟩
    have := hv v rfl
    cases a <;> simp [isAtom] at hat
    · simp [argVar] at hs
    · simp only [argVar, Option.some.injEq] at hs
      subst hs
      exact this
  · obtain ⟨s0, hs0⟩ := Option.isSome_iff_exists.1 (by simpa [pureArg, hat] using ha)
    obtain ⟨he, hv⟩ := denote'_argVar_val a hs0 h
    refine ⟨he, fun s hs => ?_⟩
    rw [hs0, Option.some.injEq] at hs
    exact hs ▸ hv

/-- Arguments read in place evaluate, when to a list, to the values of the variables they
    read, and leave the environment. -/
theorem denoteArgs'_pure {bi : Builtins} {fuel : Nat} :
    ∀ (args : List ImpExpr) {env e : Env} {vs : List Value}, args.all pureArg = true →
      denoteArgs' bi fuel args env = (some vs, e) → e = env ∧
        ∀ (i : Nat) s, ((args.map argVar)[i]?).join = some s →
          ∃ w, vs[i]? = some w ∧ env s = some w
  | [], env, e, vs, _, h => by
    obtain ⟨rfl, rfl⟩ := denoteArgs'_nil_val h
    exact ⟨rfl, fun i s hi => by simp at hi⟩
  | a :: as, env, e, vs, hp, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hp
    obtain ⟨v, e1, ws, h1, h2, rfl⟩ := denoteArgs'_cons_val h
    obtain ⟨rfl, hv⟩ := denote'_pureArg_val hp.1 h1
    obtain ⟨rfl, hws⟩ := denoteArgs'_pure as hp.2 h2
    refine ⟨rfl, fun i s hi => ?_⟩
    cases i with
    | zero =>
      simp only [List.map_cons, List.getElem?_cons_zero, Option.join_some] at hi
      exact ⟨v, rfl, hv s hi⟩
    | succ i =>
      simp only [List.map_cons, List.getElem?_cons_succ] at hi
      simpa using hws i s hi

/-- The facts `argRels` gives between arguments read in place hold of their values. -/
theorem relArgs_of_argRels {bi : Builtins} {fuel : Nat} {Γ : AEnv} {env e : Env}
    {args : List ImpExpr} {vs : List Value} (hΓ : Sat Γ env)
    (h : denoteArgs' bi fuel args env = (some vs, e)) : RelArgs (argRels Γ args) vs := by
  intro r hr
  unfold argRels at hr
  split at hr
  · rename_i hall
    obtain ⟨-, hvs⟩ := denoteArgs'_pure args hall h
    simp only [List.mem_flatMap, List.mem_range] at hr
    obtain ⟨i, -, hi⟩ := hr
    split at hi
    · rename_i x hx
      simp only [List.mem_flatMap, List.mem_filterMap, List.mem_range] at hi
      obtain ⟨p, hp, j, -, hj⟩ := hi
      split at hj
      · rename_i hjs
        simp only [Option.some.injEq] at hj
        subst hj
        obtain ⟨w, hw1, hw2⟩ := hvs i x hx
        obtain ⟨w', hw1', hw2'⟩ := hvs j p.1 hjs
        obtain ⟨k, hk, w'', n, hw'', hn, hlt⟩ := hΓ.getRel hw2 p hp
        rw [hw2', Option.some.injEq] at hw''
        subst hw''
        refine ⟨k, n, ?_, ?_, hlt⟩
        · simp only [hw1, Option.bind_some]; exact hk
        · simp only [hw1', Option.bind_some]; exact hn
      · cases hj
    · cases hi
  · cases hr

/-! ## Loop counters -/

theorem ctrAV_sat {al ah : AV} {vlo vhi : Value} {l hv k : Int} (hm1 : al.Mem vlo)
    (hm2 : ah.Mem vhi) (hl : vlo.loopBound = some l) (hh : vhi.loopBound = some hv)
    (hk : l ≤ k ∧ k ≤ hv - 1) :
    (ctrAV al ah).Mem (.int k) ∧ ∀ env, (ctrAV al ah).RelIn env (.int k) := by
  refine ⟨?_, fun env p hp => ?_⟩
  · cases al with
    | num il =>
      cases ah with
      | num ih =>
        obtain ⟨m, hm, hmi⟩ := hm1
        obtain ⟨n, hn, hni⟩ := hm2
        rw [Value.toInt_of_loopBound hl, Option.some.injEq] at hm
        rw [Value.toInt_of_loopBound hh, Option.some.injEq] at hn
        subst hm hn
        obtain ⟨hk1, hk2⟩ := hk
        obtain ⟨hm1', -⟩ := hmi
        obtain ⟨-, hn2⟩ := hni
        refine ⟨k, rfl, ?_, ?_⟩ <;> simp only at hk1 hk2 hm1' hn2 ⊢ <;> omega
      | _ => trivial
    | _ => trivial
  · cases al <;> cases ah <;> simp [ctrAV, AV.rels] at hp

/-- The counter of a loop over `[lo, len s)` lies in `ctrAVLen` with its fact, at an
    iteration whose environment holds the array `s` of the loop's start. -/
theorem ctrAVLen_sat {bi : Builtins} {fuel : Nat}
    (hlen : ∀ arr v, bi "len" [arr] = some v → ∃ n, arr.arrayLen = some n ∧ v.toInt = some n)
    {x : String} {hi body : ImpExpr} {al ah : AV} {vlo vhi : Value} {l hv k : Int}
    {e1 e2 env' : Env} (hm1 : al.Mem vlo) (hm2 : ah.Mem vhi) (hl : vlo.loopBound = some l)
    (hh : vhi.loopBound = some hv) (hhi : denote' bi fuel hi e1 = (.val vhi, e2))
    (hP : ∀ s, lenVar hi = some s → s ≠ x →
      InlineLocalClosures.frameOk (fun _ => true) (fun n => n != s) (fun _ => true) body =
        true → env' s = e2 s)
    (hk : l ≤ k ∧ k ≤ hv - 1) :
    (ctrAVLen x hi body al ah).Mem (.int k) ∧
      (ctrAVLen x hi body al ah).RelIn (env'.extend x (.int k)) (.int k) := by
  have hc0 := ctrAV_sat hm1 hm2 hl hh hk
  unfold ctrAVLen
  split
  · rename_i _ s il hs
    by_cases hc : (s != x && InlineLocalClosures.frameOk (fun _ => true) (fun n => n != s)
        (fun _ => true) body) = true
    · simp only [hc, ↓reduceIte]
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
      obtain ⟨m, hm, hmi⟩ := hm1
      rw [Value.toInt_of_loopBound hl, Option.some.injEq] at hm
      subst hm
      obtain ⟨a, rfl, ha⟩ := lenVar_eq_some hs
      obtain ⟨w, h1, hb⟩ := denote'_app1_val hhi
      obtain ⟨rfl, hw⟩ := denote'_argVar_val a ha h1
      obtain ⟨n, hn, hvn⟩ := hlen w vhi hb
      rw [Value.toInt_of_loopBound hh] at hvn
      have hvn' : hv = (n : Int) := by simpa using hvn
      subst hvn'
      refine ⟨⟨k, rfl, by have := hmi.1; omega, fun h' hh' => ?_⟩, fun p hp => ?_⟩
      · cases ah with
        | num ih =>
          simp only [AV.num?, Option.map_some, Option.some.injEq] at hh'
          subst hh'
          obtain ⟨n', hn', hni⟩ := hm2
          rw [Value.toInt_of_loopBound hh, Option.some.injEq] at hn'
          subst hn'
          have := hni.2
          omega
        | _ => simp [AV.num?] at hh'
      · simp only [AV.rels, List.mem_singleton] at hp
        subst hp
        refine ⟨k, rfl, w, n, ?_, hn, by simp only; omega⟩
        rw [Env.extend_other _ _ _ _ hc.1, hP s hs hc.1 hc.2]
        exact hw
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      exact ⟨hc0.1, hc0.2 _⟩
  · exact ⟨hc0.1, hc0.2 _⟩

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
    · exact ⟨rfl, post_val hN (hN x v hx) (hΓ.get hx).strip hΓ⟩
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
      check_sound hS b J _ a Γ' h fuel _ (hSe.cons hmw.strip (AV.RelIn.strip _ _ _))
        (hNe.extend hdw)
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
      ⟨rfl, post_val (hNe.extend hdw) rfl trivial (hSe.cons hmw.strip (AV.RelIn.strip _ _ _))⟩
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
    obtain ⟨heq, hpost⟩ := checkArgs_sound hS args J Γ avs Γ1 ha fuel env hΓ hN
    rw [denote'_app_cf, denote'_app_cf, heq]
    rcases hr : denoteArgs' bi fuel args env with ⟨_ | vs, e⟩
    · exact ⟨by trivial, trivial⟩
    obtain ⟨hml, hdl, hSe, hNe⟩ := hpost vs e hr
    have key : Γ' = Γ1 ∧ g f vs = true ∧ ∀ w, bi f vs = some w → a.Mem w := by
      rcases hx : H.xfer f avs with _ | a0 <;> simp only [hx] at h
      · rcases hy : H.xrel f avs (argRels Γ args) with _ | a0 <;>
          simp only [hy, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq,
            Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hR := relArgs_of_argRels hΓ hr
        exact ⟨rfl, hS.relGuard f avs _ _ vs hy hml hR,
          fun w hb => hS.relResult f avs _ _ vs w hy hml hR hdl hb⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hS.guard f avs _ vs hx hml, fun w hb => hS.result f avs _ vs w hx hml hdl hb⟩
    obtain ⟨rfl, hg0, hres⟩ := key
    have hg : guardBi g bi f vs = bi f vs := by simp [guardBi, hg0]
    simp only [hg]
    rcases hb : bi f vs with _ | w
    · exact ⟨by trivial, trivial⟩
    · exact ⟨by trivial, post_val hNe (hS.deep f vs w hb hdl) (hres w hb) hSe⟩
  | .ifThenElse c t el, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    rcases hc : check H J Γ c with _ | ⟨ac, Γ1⟩ <;> simp only [check, hc, reduceCtorEq] at h
    rcases ht : (if isFalseLit c then some (.top, Γ1)
        else check H J (refineCond H.logic c true Γ1) t) with _ | ⟨at', Γt⟩ <;>
      rcases he : check H J (refineCond H.logic c false Γ1) el with _ | ⟨ae, Γe⟩ <;>
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
      · by_cases hf : isFalseLit c = true
        · exact absurd (isFalseLit_run hf hr) (by simp)
        · simp only [hf, Bool.false_eq_true, ↓reduceIte] at ht
          obtain ⟨h1, h2⟩ := check_sound hS t J _ at' Γt ht fuel e hR hNe
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
    rcases hhi : check H J Γ1 hi with _ | ⟨ah, Γ2⟩ <;> simp only [hhi, reduceCtorEq] at h
    generalize hI : loopInv (loopAnn H.ann ((x, ctrAV al ah) :: Γ2) body) x body Γ2 = inv at h
    by_cases he1 : entails Γ2 inv = true <;> simp only [he1, ↓reduceIte, reduceCtorEq] at h
    rcases hb : check H inv ((x, ctrAVLen x hi body al ah) :: AEnv.kill x inv) body with
      _ | ⟨ab, Γb⟩ <;> simp only [hb, reduceCtorEq] at h
    by_cases he2 : entails Γb inv = true <;>
      simp only [he2, ↓reduceIte, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ihlo := check_sound hS lo J Γ al Γ1 hlo fuel env hΓ hN
    rw [denote'_forFold_cf, denote'_forFold_cf]
    refine cfBind_step ihlo.1 ihlo.2 fun vlo e1 _ hN1 _ hm1 hS1 => ?_
    unfold forK
    have ihhi := check_sound hS hi J Γ1 ah Γ2 hhi fuel e1 hS1 hN1
    refine cfBind_step ihhi.1 ihhi.2 fun vhi e2 hr2 hN2 _ hm2 hS2 => ?_
    rcases hl : vlo.loopBound with _ | l
    · exact ⟨rfl, trivial⟩
    rcases hh : vhi.loopBound with _ | hv
    · exact ⟨rfl, trivial⟩
    refine denoteForLoop'_sound (c := (l, hv - 1))
      (P := fun env' => ∀ s, lenVar hi = some s → s ≠ x →
        InlineLocalClosures.frameOk (fun _ => true) (fun n => n != s) (fun _ => true) body =
          true → env' s = e2 s)
      (fun fuel' k env' hk hinv hPk hNk => ?_)
      (fun fuel' n env' o e hPe hrun ho s hs hsx hf => by
        rw [denote'_keep hf fuel' hrun ho, Env.extend_other _ _ _ _ hsx]
        exact hPe s hs hsx hf)
      fuel l hv e2 (Int.le_refl _) (by simp only; omega) (hS2.entails he1)
      (fun _ _ _ _ => rfl) hN2
    have hctr := ctrAVLen_sat hS.len hm1 hm2 hl hh hr2 hPk hk
    obtain ⟨q1, q2⟩ := check_sound hS body inv _ ab Γb hb fuel' (Env.extend env' x (.int k))
      (hinv.cons hctr.1 hctr.2) (hNk.extend rfl)
    exact ⟨q1, q2.weaken (fun _ hs => hs.entails he2) (fun _ _ => trivial)⟩
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
  | .whileFold c body, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    simp only [check] at h
    generalize hI : loopInv (loopAnn H.ann Γ body) "" body Γ = inv at h
    by_cases he1 : entails Γ inv = true <;> simp only [he1, ↓reduceIte, reduceCtorEq] at h
    rcases hc : check H J inv c with _ | ⟨ac, Γc⟩ <;> simp only [hc, reduceCtorEq] at h
    by_cases he2 : entails Γc inv = true <;> simp only [he2, ↓reduceIte, reduceCtorEq] at h
    rcases hb : check H inv (refineCond H.logic c true Γc) body with _ | ⟨ab, Γb⟩ <;>
      simp only [hb, reduceCtorEq] at h
    by_cases he3 : entails Γb inv = true <;>
      simp only [he3, ↓reduceIte, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [denote'_whileFold, denote'_whileFold]
    exact denoteWhile'_sound hS
      (fun fuel' env' hs hn => check_sound hS c J inv ac Γc hc fuel' env' hs hn) he2
      (fun fuel' env' hs hn => by
        obtain ⟨q1, q2⟩ := check_sound hS body inv _ ab Γb hb fuel' env' hs hn
        exact ⟨q1, q2.weaken (fun _ hs' => hs'.entails he3) (fun _ _ => trivial)⟩)
      fuel env (hΓ.entails he1) hN
  | .tuple xs, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    rcases ha : checkArgs H J Γ xs with _ | ⟨avs, Γ1⟩ <;>
      simp only [check, ha, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨heq, hpost⟩ := checkArgs_sound hS xs J Γ avs Γ1 ha fuel env hΓ hN
    rw [denote'_tuple_run, denote'_tuple_run, heq]
    rcases hr : denoteArgs' bi fuel xs env with ⟨_ | vs, e⟩
    · exact ⟨by trivial, trivial⟩
    · obtain ⟨-, hdl, hSe, hNe⟩ := hpost vs e hr
      exact ⟨by trivial, post_val hNe (deepNoControlFlow_tuple_of hdl) trivial hSe⟩
  | .proj x i, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    rcases hx : check H J Γ x with _ | ⟨ax, Γ1⟩ <;>
      simp only [check, hx, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ihx := check_sound hS x J Γ ax Γ1 hx fuel env hΓ hN
    rw [denote'_proj_cf, denote'_proj_cf]
    refine cfBind_step ihx.1 ihx.2 fun v e _ hNe hdv _ hSe => ?_
    unfold projK
    rcases hp : v.projIdx i with _ | vi
    · exact ⟨rfl, trivial⟩
    · exact ⟨rfl, post_val hNe (Value.deepNoControlFlow_projIdx hdv hp) trivial hSe⟩
  | .earlyReturn x, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    rcases hx : check H J Γ x with _ | ⟨ax, Γ1⟩ <;>
      simp only [check, hx, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ihx := check_sound hS x J Γ ax Γ1 hx fuel env hΓ hN
    rw [denote'_earlyReturn_cf, denote'_earlyReturn_cf]
    exact cfBind_step ihx.1 ihx.2 fun _ _ _ _ _ _ _ => ⟨rfl, trivial⟩
  | .questionMark x, J, Γ, a, Γ', h, fuel, env, hΓ, hN => by
    rcases hx : check H J Γ x with _ | ⟨ax, Γ1⟩ <;>
      simp only [check, hx, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ihx := check_sound hS x J Γ ax Γ1 hx fuel env hΓ hN
    rw [denote'_questionMark_cf, denote'_questionMark_cf]
    refine cfBind_step ihx.1 ihx.2 fun v e hr hNe hdv _ hSe => ?_
    clear hr
    unfold qmK
    rcases v with _ | _ | _ | _ | _ | _ | _ | _ | ⟨ok, u⟩ | _
    all_goals try exact ⟨rfl, trivial⟩
    cases ok
    · exact ⟨rfl, trivial⟩
    · exact ⟨rfl, post_val hNe (by simpa [Value.deepNoControlFlow] using hdv) trivial hSe⟩
  | .lam _ _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .forLoop _ _ _ _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .forLoopRev _ _ _ _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .whileLoop _ _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .break_ _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .continue_, _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .forFoldRev _ _ _ _, _, _, _, _, h, _, _, _, _ => by simp [check] at h
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

/-! ## Function bodies -/

/-- The environment of a function body: the parameters `ps` bound to the values `vs`, a
    parameter repeated in the list taking the value of its first position. -/
def paramEnv : List String → List Value → Env
  | p :: ps, v :: vs => Env.extend (paramEnv ps vs) p v
  | _, _ => Env.empty

/-- A binding in an abstract environment without facts drops nothing. -/
theorem AEnv.kill_of_rels {x : String} {Γ : AEnv} (h : ∀ p ∈ Γ, p.2.rels = []) :
    AEnv.kill x Γ = Γ := by
  unfold AEnv.kill
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    obtain ⟨y, a⟩ := p
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, ih fun q hq => h q (List.mem_cons_of_mem _ hq)⟩
    have := h _ List.mem_cons_self
    cases a <;> simp_all [AV.forget, AV.rels]

/-- Arguments in the abstract values `pre` give a parameter environment in
    `ps.zip (pre.map AV.strip)`. -/
theorem sat_paramEnv : ∀ (ps : List String) (pre : List AV) (vs : List Value),
    MemList pre vs → Sat (ps.zip (pre.map AV.strip)) (paramEnv ps vs)
  | [], _, _, _ => fun x a h => by simp at h
  | _ :: _, [], _, _ => fun x a h => by simp at h
  | p :: ps, a :: pre, [], hm => absurd hm id
  | p :: ps, a :: pre, v :: vs, hm => by
    simp only [List.map_cons, List.zip_cons_cons, paramEnv]
    have := (sat_paramEnv ps pre vs hm.2).cons (x := p) hm.1.strip (AV.RelIn.strip _ _ _)
    rwa [AEnv.kill_of_rels fun q hq => ?_] at this
    obtain ⟨-, hq2⟩ := List.of_mem_zip hq
    obtain ⟨b, -, hb⟩ := List.mem_map.1 hq2
    rw [← hb]
    exact AV.rels_strip b

/-- Arguments free of control flow give a parameter environment free of control flow. -/
theorem paramEnv_noControlFlow : ∀ (ps : List String) (vs : List Value),
    (∀ w ∈ vs, w.deepNoControlFlow = true) → Env.NoControlFlow (paramEnv ps vs)
  | [], _, _ => by simpa [paramEnv] using Env.NoControlFlow.empty
  | _ :: _, [], _ => by simpa [paramEnv] using Env.NoControlFlow.empty
  | p :: ps, v :: vs, hd => by
    simp only [paramEnv]
    exact (paramEnv_noControlFlow ps vs fun w hw => hd w (List.mem_cons_of_mem _ hw)).extend
      (hd v (List.mem_cons_self))

/-- A function body the checker accepts at `a` from its parameters at `pre` returns, on
    arguments in `pre` free of control flow, a value in `a`. -/
theorem mem_of_body {g : String → List Value → Bool} {H : Spec} {bi : Builtins}
    (hS : Sound g H bi) {ps : List String} {pre : List AV} {body : ImpExpr} {a : AV}
    {Γ' : AEnv} (hc : check H [] (ps.zip (pre.map AV.strip)) body = some (a, Γ'))
    {vs : List Value}
    {v : Value} (hm : MemList pre vs) (hd : ∀ w ∈ vs, w.deepNoControlFlow = true) {fuel : Nat}
    {e : Env} (hr : denote' bi fuel body (paramEnv ps vs) = (.val v, e))
    (hv : v.isControlFlow = false) : a.Mem v := by
  have h2 := (check_sound hS body [] _ a Γ' hc fuel _ (sat_paramEnv ps pre vs hm)
    (paramEnv_noControlFlow ps vs hd)).2
  rw [hr] at h2
  exact (h2.of_val hv).2.2.1

end Hax.Range

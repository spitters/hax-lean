/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.SemanticsCF
public import HaxLean.AnfLowCT

/-!
# Totality of `denote'` on a checked class of terms

A Boolean-style checker `KindSig.check` assigns kinds to the terms built from literals,
variables, `unitVal`, `letBind`, `seq`, `assign`, `typeAscription`, calls of heads that
the signature `KindSig.sig` types, and `forFold` loops whose bounds have kinds with an
integer range. The checker also returns a fuel bound. Under a builtin table that
answers every typed head with a value of the result kind (`KindSig.Sound`), a checked
term evaluates under `denote'` to a value from every environment that binds the
context's variables to values of their kinds, at every fuel at least the bound.

Array reads and writes (`index`, `array_update`) are ordinary heads: their in-bounds
condition is part of the signature's soundness, so a kind system that carries index
ranges and array lengths discharges it from the counter range `KindSig.ctr`.

## Main definitions

* `Value.loopBound` — the integer a counted-loop bound denotes
* `KindSig` — literal kinds, head signatures, kind ranges and counter kinds
* `KindSig.Sound` — the signature's soundness for a value predicate and a builtin table
* `KindSig.check` — the kind and fuel bound of a term, or `none`
* `KindSig.EnvOK` — an environment binds the context's variables to values of their kinds

## Main results

* `denoteForLoop'_total` — a counted loop whose body lands on a value runs to `unit`
* `KindSig.check_sound` — a checked term lands on a value of its kind
* `KindSig.denote'_run_val_of_check` — the same result in `.run` form
-/

@[expose] public section

set_option autoImplicit false

namespace Hax

/-- The integer a counted-loop bound denotes: an integer, or an unsigned word read as
    its natural number. -/
def Value.loopBound : Value → Option Int
  | .int n => some n
  | .uint _ n => some n
  | _ => none

namespace Total

/-! ## One-step evaluation lemmas -/

theorem denote'_letBind_of_val {bi : Builtins} {fuel : Nat} {x : String}
    {v b : ImpExpr} {env env1 : Env} {w : Value}
    (hv : denote' bi fuel v env = (.val w, env1)) (hw : w.isControlFlow = false) :
    denote' bi fuel (.letBind x v b) env = denote' bi fuel b (Env.extend env1 x w) := by
  rw [denote'_letBind_run, hv]
  cases w <;> first | rfl | simp [Value.isControlFlow] at hw

theorem denote'_seq_of_val {bi : Builtins} {fuel : Nat} {a b : ImpExpr}
    {env env1 : Env} {w : Value}
    (ha : denote' bi fuel a env = (.val w, env1)) (hw : w.isControlFlow = false) :
    denote' bi fuel (.seq a b) env = denote' bi fuel b env1 := by
  rw [denote'_seq_run, ha]
  cases w <;> first | rfl | simp [Value.isControlFlow] at hw

theorem denote'_assign_of_val {bi : Builtins} {fuel : Nat} {x : String} {r : ImpExpr}
    {env env1 : Env} {w : Value}
    (hr : denote' bi fuel r env = (.val w, env1)) (hw : w.isControlFlow = false) :
    denote' bi fuel (.assign x r) env = (.val .unit, Env.extend env1 x w) := by
  rw [denote'_assign_run, hr]
  cases w <;> first | rfl | simp [Value.isControlFlow] at hw

theorem denote'_typeAscription_run (bi : Builtins) (fuel : Nat) (e : ImpExpr) (s : String)
    (env : Env) :
    denote' bi fuel (.typeAscription e s) env = denote' bi fuel e env := by
  conv => lhs; unfold denote'

theorem denoteArgs'_nil_run (bi : Builtins) (fuel : Nat) (env : Env) :
    denoteArgs' bi fuel [] env = (some [], env) := by
  unfold denoteArgs'; rfl

theorem denoteArgs'_cons_of_val {bi : Builtins} {fuel : Nat} {e : ImpExpr}
    {es : List ImpExpr} {env env1 env2 : Env} {w : Value} {ws : List Value}
    (he : denote' bi fuel e env = (.val w, env1)) (hw : w.isControlFlow = false)
    (hes : denoteArgs' bi fuel es env1 = (some ws, env2)) :
    denoteArgs' bi fuel (e :: es) env = (some (w :: ws), env2) := by
  conv => lhs; unfold denoteArgs'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  rw [he]
  cases w <;> first | (dsimp only [StateT.bind]; rw [hes]; rfl) | simp [Value.isControlFlow] at hw

theorem denote'_app_of_args {bi : Builtins} {fuel : Nat} {f : String}
    {args : List ImpExpr} {env env1 : Env} {vs : List Value} {w : Value}
    (ha : denoteArgs' bi fuel args env = (some vs, env1)) (hf : bi f vs = some w) :
    denote' bi fuel (.app f args) env = (.val w, env1) := by
  conv => lhs; unfold denote'
  unfold denoteApp'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  rw [ha]
  dsimp only
  rw [hf]
  rfl

theorem denote'_forFold_of_bounds {bi : Builtins} {fuel : Nat} {x : String}
    {lo hi body : ImpExpr} {env env1 env2 : Env} {vlo vhi : Value} {l h : Int}
    (hlo : denote' bi fuel lo env = (.val vlo, env1)) (hl : vlo.loopBound = some l)
    (hhi : denote' bi fuel hi env1 = (.val vhi, env2)) (hh : vhi.loopBound = some h) :
    denote' bi fuel (.forFold x lo hi body) env =
      denoteForLoop' bi fuel x l h body env2 := by
  conv => lhs; unfold denote'
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  rw [hlo]
  cases vlo <;> simp only [Value.loopBound, reduceCtorEq, Option.some.injEq] at hl <;>
    (subst hl; dsimp only [StateT.bind]; rw [hhi]) <;>
    cases vhi <;> simp only [Value.loopBound, reduceCtorEq, Option.some.injEq] at hh <;>
    (subst hh; rfl)

/-! ## Counted loops -/

/-- A counted loop over `[lo, hi)` inside `[a, c)` whose body, at every fuel at least
    `fb`, lands on a non-control-flow value and preserves the invariant `Q`, runs to
    `unit` at every fuel at least the trip bound plus `fb`. -/
theorem denoteForLoop'_total {Q : Env → Prop} {bi : Builtins} {x : String}
    {body : ImpExpr} {a c : Int} {fb : Nat}
    (hb : ∀ fuel, fb ≤ fuel → ∀ (n : Int) (env : Env), a ≤ n → n < c → Q env →
      ∃ v env', denote' bi fuel body (Env.extend env x (.int n)) = (.val v, env') ∧
        v.isControlFlow = false ∧ Q env') :
    ∀ (t : Nat) (lo hi : Int) (fuel : Nat) (env : Env), (hi - lo).toNat ≤ t →
      t + fb ≤ fuel → a ≤ lo → hi ≤ c → Q env →
      ∃ env', denoteForLoop' bi fuel x lo hi body env = (.val .unit, env') ∧ Q env' := by
  intro t
  induction t with
  | zero =>
    intro lo hi fuel env ht _ _ _ hQ
    refine ⟨env, ?_, hQ⟩
    rw [denoteForLoop', if_pos (by omega)]
    rfl
  | succ t ih =>
    intro lo hi fuel env ht hf hlo hhi hQ
    by_cases hlh : lo ≥ hi
    · refine ⟨env, ?_, hQ⟩
      rw [denoteForLoop', if_pos hlh]
      rfl
    · obtain ⟨v, env1, hv, hcf, hQ1⟩ :=
        hb fuel (by omega) lo env hlo (by omega) hQ
      obtain ⟨env2, hrun, hQ2⟩ :=
        ih (lo + 1) hi (fuel - 1) env1 (by omega) (by omega) (by omega) hhi hQ1
      refine ⟨env2, ?_, hQ2⟩
      rw [denoteForLoop', if_neg hlh, if_neg (by omega)]
      dsimp only [bind, Bind.bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, Pure.pure, StateT.pure, Id.run]
      rw [hv]
      cases v <;> first | exact hrun | simp [Value.isControlFlow] at hcf

/-! ## Kind signatures -/

/-- A kind signature over kinds `K`: the kind of a literal, the result kind of a head
    on argument kinds, the integer range of a kind used as a loop bound, and the kind
    given to the counter of a loop over a range. -/
structure KindSig (K : Type) where
  /-- The kind of a literal, when it has one. -/
  lit : ImpLit → Option K
  /-- The result kind of a head on argument kinds; `none` outside the typed heads. -/
  sig : String → List K → Option K
  /-- The closed integer range of the values of a kind, when it is a bound kind. -/
  range : K → Option (Int × Int)
  /-- The kind of the counter of a loop from the range's lower end `a` up to `c`. -/
  ctr : Int → Int → K

namespace KindSig

variable {K : Type} [DecidableEq K]

/-- Each value of a list has the kind at its position in a list of kinds of the same
    length. -/
def KindsOK (ofKind : K → Value → Prop) : List K → List Value → Prop
  | [], [] => True
  | k :: ks, v :: vs => ofKind k v ∧ KindsOK ofKind ks vs
  | _, _ => False

/-- The signature's soundness for the kind predicate `ofKind` and the builtin table
    `bi`: kinds hold no control-flow value, literal kinds hold their literals, each
    typed head answers with a value of its result kind on arguments of its argument
    kinds, a bound kind holds integers or words in its range, and a counter kind holds
    the integers of its range. -/
structure Sound (S : KindSig K) (ofKind : K → Value → Prop) (bi : Builtins) : Prop where
  noCF : ∀ k v, ofKind k v → v.isControlFlow = false
  lit : ∀ l k, S.lit l = some k → ofKind k (Value.ofLit l)
  sig : ∀ f ks k, S.sig f ks = some k → ∀ vs, KindsOK ofKind ks vs →
    ∃ v, bi f vs = some v ∧ ofKind k v
  range : ∀ k a b, S.range k = some (a, b) → ∀ v, ofKind k v →
    ∃ n, v.loopBound = some n ∧ a ≤ n ∧ n ≤ b
  ctr : ∀ a c n, a ≤ n → n < c → ofKind (S.ctr a c) (.int n)

/-- A binding of `x` at kind `k` agrees with the context: `x` is unbound in `Γ` or bound
    at `k`. -/
def ctxOK (Γ : List (String × K)) (x : String) (k : K) : Bool :=
  match Γ.lookup x with
  | none => true
  | some k' => decide (k' = k)

mutual

/-- The kind (`none` for a value of no tracked kind) and the fuel bound of a term in the
    context `Γ`, or `none` when the term is outside the checked class. -/
def check (S : KindSig K) : List (String × K) → ImpExpr → Option (Option K × Nat)
  | _, .lit l => some (S.lit l, 0)
  | Γ, .var x => (Γ.lookup x).map fun k => (some k, 0)
  | _, .unitVal => some (none, 0)
  | Γ, .letBind x v b =>
    match check S Γ v with
    | some (some k, fv) =>
      if ctxOK Γ x k then (check S ((x, k) :: Γ) b).map fun r => (r.1, max fv r.2)
      else none
    | _ => none
  | Γ, .seq a b =>
    match check S Γ a, check S Γ b with
    | some (_, fa), some (kb, fb) => some (kb, max fa fb)
    | _, _ => none
  | Γ, .assign x r =>
    match check S Γ r with
    | some (some k, fr) => if ctxOK Γ x k then some (none, fr) else none
    | _ => none
  | Γ, .typeAscription e _ => check S Γ e
  | Γ, .app f args =>
    match checkArgs S Γ args with
    | some (ks, fa) => (S.sig f ks).map fun k => (some k, fa)
    | none => none
  | Γ, .forFold x lo hi b =>
    match check S Γ lo, check S Γ hi with
    | some (some kl, flo), some (some kh, fhi) =>
      match S.range kl, S.range kh with
      | some (a, _), some (_, c) =>
        if ctxOK Γ x (S.ctr a c) then
          match check S ((x, S.ctr a c) :: Γ) b with
          | some (_, fb) => some (none, max (max flo fhi) ((c - a).toNat + fb))
          | none => none
        else none
      | _, _ => none
    | _, _ => none
  | _, _ => none

/-- The kinds and the fuel bound of a list of call arguments, each of a tracked kind. -/
def checkArgs (S : KindSig K) (Γ : List (String × K)) :
    List ImpExpr → Option (List K × Nat)
  | [] => some ([], 0)
  | e :: es =>
    match check S Γ e, checkArgs S Γ es with
    | some (some k, f), some (ks, fs) => some (k :: ks, max f fs)
    | _, _ => none

end

/-- The environment binds every variable of the context `Γ` to a value of its kind. -/
def EnvOK (ofKind : K → Value → Prop) (Γ : List (String × K)) (env : Env) : Prop :=
  ∀ x k, Γ.lookup x = some k → ∃ v, env x = some v ∧ ofKind k v

omit [DecidableEq K] in
theorem envOK_extend {ofKind : K → Value → Prop} {Γ : List (String × K)} {env : Env}
    {x : String} {k : K} {v : Value} (hE : EnvOK ofKind Γ env) (hv : ofKind k v) :
    EnvOK ofKind ((x, k) :: Γ) (Env.extend env x v) := by
  intro y k' hy
  rw [List.lookup_cons] at hy
  by_cases hyx : y = x
  · subst hyx
    simp only [beq_self_eq_true, Option.some.injEq] at hy
    subst hy
    exact ⟨v, Env.extend_same _ _ _, hv⟩
  · have hb : (y == x) = false := by simpa using hyx
    rw [hb] at hy
    simp only at hy
    rw [Env.extend_other _ _ _ _ hyx]
    exact hE y k' hy

theorem envOK_of_cons {ofKind : K → Value → Prop} {Γ : List (String × K)} {env : Env}
    {x : String} {k : K} (hc : ctxOK Γ x k = true)
    (hE : EnvOK ofKind ((x, k) :: Γ) env) : EnvOK ofKind Γ env := by
  intro y k' hy
  by_cases hyx : y = x
  · subst hyx
    unfold ctxOK at hc
    rw [hy] at hc
    have hk : k' = k := of_decide_eq_true hc
    subst hk
    exact hE y k' (by simp)
  · have hb : (y == x) = false := by simpa using hyx
    exact hE y k' (by rw [List.lookup_cons, hb]; simpa using hy)

mutual

/-- A checked term lands on a value: from an environment that binds the context, at
    every fuel at least the checker's bound, `denote'` returns a non-control-flow value
    of the checked kind and an environment that still binds the context. -/
theorem check_sound {S : KindSig K} {ofKind : K → Value → Prop} {bi : Builtins}
    (hS : S.Sound ofKind bi) :
    ∀ (e : ImpExpr) (Γ : List (String × K)) (ko : Option K) (f : Nat),
      S.check Γ e = some (ko, f) → ∀ fuel, f ≤ fuel → ∀ env, EnvOK ofKind Γ env →
      ∃ v env', denote' bi fuel e env = (.val v, env') ∧ v.isControlFlow = false ∧
        (∀ k, ko = some k → ofKind k v) ∧ EnvOK ofKind Γ env'
  | .lit l, Γ, ko, f, h, fuel, _, env, hE => by
    simp only [check, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨_, env, denote'_lit_run bi fuel l env, ?_, fun k hk => hS.lit l k hk, hE⟩
    cases l <;> rfl
  | .var x, Γ, ko, f, h, fuel, _, env, hE => by
    rcases hl : Γ.lookup x with _ | k <;>
      simp only [check, hl, Option.map_none, Option.map_some, reduceCtorEq,
        Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨v, hv, hk⟩ := hE x k hl
    refine ⟨v, env, ?_, hS.noCF k v hk, fun k' hk' => by cases hk'; exact hk, hE⟩
    rw [denote'_var_run, hv]
  | .unitVal, Γ, ko, f, h, fuel, _, env, hE => by
    simp only [check, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.unit, env, denote'_unitVal_run bi fuel env, rfl, by simp, hE⟩
  | .letBind x v b, Γ, ko, f, h, fuel, hf, env, hE => by
    rcases hv : S.check Γ v with _ | ⟨_ | kv, fv⟩ <;>
      simp only [check, hv, reduceCtorEq] at h
    by_cases hc : ctxOK Γ x kv = true <;> simp only [hc, ↓reduceIte, reduceCtorEq] at h
    rcases hb : S.check ((x, kv) :: Γ) b with _ | ⟨kb, fb⟩ <;>
      simp only [hb, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq,
        Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨w, env1, hw, hcf, hk, hE1⟩ :=
      check_sound hS v Γ (some kv) fv hv fuel (by omega) env hE
    obtain ⟨u, env2, hu, hcf2, hk2, hE2⟩ :=
      check_sound hS b ((x, kv) :: Γ) _ fb hb fuel (by omega) _
        (envOK_extend hE1 (hk kv rfl))
    refine ⟨u, env2, ?_, hcf2, hk2, envOK_of_cons hc hE2⟩
    rw [denote'_letBind_of_val hw hcf, hu]
  | .seq a b, Γ, ko, f, h, fuel, hf, env, hE => by
    rcases ha : S.check Γ a with _ | ⟨ka, fa⟩ <;> rcases hb : S.check Γ b with _ | ⟨kb, fb⟩ <;>
      simp only [check, ha, hb, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨w, env1, hw, hcf, -, hE1⟩ := check_sound hS a Γ ka fa ha fuel (by omega) env hE
    obtain ⟨u, env2, hu, hcf2, hk2, hE2⟩ :=
      check_sound hS b Γ _ fb hb fuel (by omega) env1 hE1
    refine ⟨u, env2, ?_, hcf2, hk2, hE2⟩
    rw [denote'_seq_of_val hw hcf, hu]
  | .assign x r, Γ, ko, f, h, fuel, hf, env, hE => by
    rcases hr : S.check Γ r with _ | ⟨_ | kr, fr⟩ <;>
      simp only [check, hr, reduceCtorEq] at h
    by_cases hc : ctxOK Γ x kr = true <;>
      simp only [hc, ↓reduceIte, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨w, env1, hw, hcf, hk, hE1⟩ := check_sound hS r Γ (some kr) _ hr fuel hf env hE
    exact ⟨.unit, _, denote'_assign_of_val hw hcf, rfl, by simp,
      envOK_of_cons hc (envOK_extend hE1 (hk kr rfl))⟩
  | .typeAscription e s, Γ, ko, f, h, fuel, hf, env, hE => by
    simp only [check] at h
    rw [denote'_typeAscription_run]
    exact check_sound hS e Γ ko f h fuel hf env hE
  | .app g args, Γ, ko, f, h, fuel, hf, env, hE => by
    rcases ha : S.checkArgs Γ args with _ | ⟨ks, fa⟩ <;>
      simp only [check, ha, reduceCtorEq] at h
    rcases hs : S.sig g ks with _ | k <;>
      simp only [hs, Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq,
        Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨vs, env1, hargs, hks, hE1⟩ := checkArgs_sound hS args Γ ks fa ha fuel hf env hE
    obtain ⟨w, hw, hkw⟩ := hS.sig g ks k hs vs hks
    exact ⟨w, env1, denote'_app_of_args hargs hw, hS.noCF k w hkw,
      fun k' hk' => by cases hk'; exact hkw, hE1⟩
  | .forFold x lo hi b, Γ, ko, f, h, fuel, hf, env, hE => by
    rcases hlo : S.check Γ lo with _ | ⟨_ | kl, flo⟩ <;>
      rcases hhi : S.check Γ hi with _ | ⟨_ | kh, fhi⟩ <;>
      simp only [check, hlo, hhi, reduceCtorEq] at h
    rcases hrl : S.range kl with _ | ⟨a, b1⟩ <;> rcases hrh : S.range kh with _ | ⟨a2, c⟩ <;>
      simp only [hrl, hrh, reduceCtorEq] at h
    by_cases hc : ctxOK Γ x (S.ctr a c) = true <;>
      simp only [hc, ↓reduceIte, reduceCtorEq] at h
    rcases hbd : S.check ((x, S.ctr a c) :: Γ) b with _ | ⟨kb, fb⟩ <;>
      simp only [hbd, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨vlo, env1, hvlo, -, hk1, hE1⟩ :=
      check_sound hS lo Γ (some kl) flo hlo fuel (by omega) env hE
    obtain ⟨l, hl, hal, -⟩ := hS.range kl a b1 hrl vlo (hk1 kl rfl)
    obtain ⟨vhi, env2, hvhi, -, hk2, hE2⟩ :=
      check_sound hS hi Γ (some kh) fhi hhi fuel (by omega) env1 hE1
    obtain ⟨hh, hhb, -, hhc⟩ := hS.range kh a2 c hrh vhi (hk2 kh rfl)
    rw [denote'_forFold_of_bounds hvlo hl hvhi hhb]
    obtain ⟨env3, hrun, hE3⟩ := denoteForLoop'_total (Q := EnvOK ofKind Γ)
      (fun fuel' hf' n env' han hnc hQ => by
        obtain ⟨u, env'', hu, hcf, -, hE''⟩ := check_sound hS b _ kb fb hbd fuel' hf' _
          (envOK_extend hQ (hS.ctr a c n han hnc))
        exact ⟨u, env'', hu, hcf, envOK_of_cons hc hE''⟩)
      ((c - a).toNat) l hh fuel env2 (by omega) (by omega) hal hhc hE2
    exact ⟨.unit, env3, hrun, rfl, by simp, hE3⟩
  | .lam _ _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .tuple _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .proj _ _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .ifThenElse _ _ _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .match_ _ _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .borrow _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .deref _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .forLoop _ _ _ _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .forLoopRev _ _ _ _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .whileLoop _ _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .break_ _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .continue_, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .earlyReturn _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .questionMark _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .forFoldRev _ _ _ _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .whileFold _ _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .forFoldReturn _ _ _ _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .forFoldRevReturn _ _ _ _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .whileFoldReturn _ _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .cfBreak _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .cfContinue _, _, _, _, h, _, _, _, _ => by simp [check] at h
  | .cfBreakContinue _, _, _, _, h, _, _, _, _ => by simp [check] at h

/-- Checked arguments land on values of their kinds, in order, at every fuel at least
    the checker's bound. -/
theorem checkArgs_sound {S : KindSig K} {ofKind : K → Value → Prop} {bi : Builtins}
    (hS : S.Sound ofKind bi) :
    ∀ (args : List ImpExpr) (Γ : List (String × K)) (ks : List K) (f : Nat),
      S.checkArgs Γ args = some (ks, f) → ∀ fuel, f ≤ fuel → ∀ env, EnvOK ofKind Γ env →
      ∃ vs env', denoteArgs' bi fuel args env = (some vs, env') ∧ KindsOK ofKind ks vs ∧
        EnvOK ofKind Γ env'
  | [], Γ, ks, f, h, fuel, _, env, hE => by
    simp only [checkArgs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], env, denoteArgs'_nil_run bi fuel env, trivial, hE⟩
  | e :: es, Γ, ks, f, h, fuel, hf, env, hE => by
    rcases he : S.check Γ e with _ | ⟨_ | k, fe⟩ <;>
      rcases hes : S.checkArgs Γ es with _ | ⟨ks', fs⟩ <;>
      simp only [checkArgs, he, hes, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨w, env1, hw, hcf, hk, hE1⟩ :=
      check_sound hS e Γ (some k) fe he fuel (by omega) env hE
    obtain ⟨ws, env2, hws, hks, hE2⟩ :=
      checkArgs_sound hS es Γ ks' fs hes fuel (by omega) env1 hE1
    exact ⟨w :: ws, env2, denoteArgs'_cons_of_val hw hcf hws, ⟨hk k rfl, hks⟩, hE2⟩

end

/-- Totality of `denote'` in `.run` form: a term the checker accepts in the context `Γ`
    with fuel bound `f` evaluates to a value from every environment binding `Γ`, at
    every fuel at least `f`. -/
theorem denote'_run_val_of_check {S : KindSig K} {ofKind : K → Value → Prop}
    {bi : Builtins} (hS : S.Sound ofKind bi) {Γ : List (String × K)} {e : ImpExpr}
    {ko : Option K} {f fuel : Nat} (hc : S.check Γ e = some (ko, f)) (hf : f ≤ fuel)
    {env : Env} (hE : EnvOK ofKind Γ env) :
    ∃ v env', (denote' bi fuel e).run env = (.val v, env') := by
  obtain ⟨v, env', h, -⟩ := check_sound hS e Γ ko f hc fuel hf env hE
  exact ⟨v, env', h⟩

end KindSig

end Total

end Hax

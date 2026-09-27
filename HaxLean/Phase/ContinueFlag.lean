/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.SemanticsCF

/-!
# `continue` as a flag in a loop body

In the body of a `forFold` or `forFoldReturn`, a `cfContinue e` at a statement
position ends the trip: `denote'` passes the value `controlFlow false v` through `seq`
and `letBind`, and the loop starts its next trip. `contLoopBody c body` expresses the
same control with a boolean program variable `c`, the continue flag:

* the trip starts by binding `c` to `false` (`setFlag c false`);
* `cfContinue e` evaluates `e` and binds `c` to `true`;
* in `seq a b` with a continue in `a`, the statement `b` runs only when `c` is
  `false` (`guardRest`).

The rewritten body has no `cfContinue`; its statements are `letBind`s of a boolean
literal, `seq` and `ifThenElse` on a variable, so a lowering that accepts those
constructors accepts it.

**Fragment.** `bodyOk c` admits `letBind` of an atom or of an application to atoms,
`seq`, `ifThenElse` on a variable, `cfContinue` and `cfBreak` of an atom, and an
atom; an atom is a literal, `unitVal` or a variable other than `c`, and no `letBind`
binds `c`.

**Agreement.** Runs of the body and of the rewritten body are compared on
environments that agree off `c` (`AgreeOff c`), from an environment holding no
control-flow value (`EnvPlain`) and a builtin table that returns none
(`BuiltinsPlain`). `contNorm` reads a continue outcome as the value `unit`.

## Main results

* `contBody_run`: the rewritten body ends in `contNorm` of the outcome of the body,
  in an environment agreeing off `c`, with the flag set exactly when the body
  continued
* `contLoop_forFold_run`, `contLoop_forFoldReturn_run`: `denoteForLoop'` and
  `denoteForLoop'Return` over the rewritten body end in the outcome of the loop over
  the body, in an environment agreeing off `c`
* `denote'_contLoop_forFold`, `denote'_contLoop_forFoldReturn`: the same for the
  `forFold` and `forFoldReturn` expressions with atomic bounds
* `contFn_run`, `contFn_run_same`: `contFn c`, which rewrites the body of every loop
  of a function body of `fnOk c`, preserves the outcome of the function body
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.ContinueFlag

/-! ## The rewriting -/

/-- An atom: a literal, `unitVal`, or a variable other than `c`. -/
def atomOk (c : String) : ImpExpr → Bool
  | .var x => x != c
  | .lit _ => true
  | .unitVal => true
  | _ => false

/-- The right-hand side of a `letBind` in the fragment: an atom, or an application
    to atoms. -/
def rhsOk (c : String) : ImpExpr → Bool
  | .app _ args => args.all (atomOk c)
  | e => atomOk c e

/-- Whether `e` has a `cfContinue` at a statement position. -/
def hasCont : ImpExpr → Bool
  | .cfContinue _ => true
  | .letBind _ _ b => hasCont b
  | .seq a b => hasCont a || hasCont b
  | .ifThenElse _ t e => hasCont t || hasCont e
  | _ => false

/-- The loop bodies the rewriting covers, for the flag `c`. -/
def bodyOk (c : String) : ImpExpr → Bool
  | .letBind n v b => n != c && rhsOk c v && bodyOk c b
  | .seq a b => bodyOk c a && bodyOk c b
  | .ifThenElse (.var x) t e => x != c && bodyOk c t && bodyOk c e
  | .cfContinue e => atomOk c e
  | .cfBreak e => atomOk c e
  | e => atomOk c e

/-- Bind the flag `c` to the boolean `b`, then run `k`. -/
def setFlag (c : String) (b : Bool) (k : ImpExpr) : ImpExpr := .letBind c (.lit (.bool b)) k

/-- Run `k` only when the flag `c` is `false`. -/
def guardRest (c : String) (k : ImpExpr) : ImpExpr := .ifThenElse (.var c) .unitVal k

/-- The body with each `cfContinue e` replaced by setting the flag `c`, and each
    statement after a statement that may continue guarded by the flag. -/
def contBody (c : String) : ImpExpr → ImpExpr
  | .letBind n v b => .letBind n v (contBody c b)
  | .seq a b =>
      if hasCont a then .seq (contBody c a) (guardRest c (contBody c b))
      else .seq (contBody c a) (contBody c b)
  | .ifThenElse cnd t e => .ifThenElse cnd (contBody c t) (contBody c e)
  | .cfContinue e => .seq e (setFlag c true .unitVal)
  | e => e

/-- The loop body with the flag `c`: reset the flag, then run `contBody c body`. -/
def contLoopBody (c : String) (body : ImpExpr) : ImpExpr := setFlag c false (contBody c body)

/-! ## Outcomes and environments -/

/-- Whether an outcome is a continue, `val (controlFlow false v)`. -/
def isCont : Outcome → Bool
  | .val (.controlFlow false _) => true
  | _ => false

/-- A continue outcome read as the value `unit`; every other outcome unchanged. -/
def contNorm : Outcome → Outcome
  | .val (.controlFlow false _) => .val .unit
  | o => o

/-- Two environments agree off the name `c`. -/
def AgreeOff (c : String) (e1 e2 : Env) : Prop := ∀ x, x ≠ c → e1 x = e2 x

/-- An environment holding no control-flow value. -/
def EnvPlain (env : Env) : Prop := ∀ x v, env x = some v → v.isControlFlow = false

/-- A builtin table returning no control-flow value. -/
def BuiltinsPlain (bi : Builtins) : Prop :=
  ∀ f args v, bi f args = some v → v.isControlFlow = false

theorem contNorm_of_not_isCont {o : Outcome} (h : isCont o = false) : contNorm o = o := by
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v with
  | controlFlow k w => cases k <;> simp_all [isCont, contNorm]
  | _ => rfl

theorem AgreeOff.extend {c : String} {e1 e2 : Env} (h : AgreeOff c e1 e2) (n : String)
    (v : Value) : AgreeOff c (e1.extend n v) (e2.extend n v) := by
  intro x hx
  simp only [Env.extend]
  split
  · rfl
  · exact h x hx

theorem AgreeOff.extend_right {c : String} {e1 e2 : Env} (h : AgreeOff c e1 e2) (v : Value) :
    AgreeOff c e1 (e2.extend c v) := by
  intro x hx
  simp only [Env.extend]
  rw [if_neg (by simpa using hx)]
  exact h x hx

theorem EnvPlain.extend {env : Env} (h : EnvPlain env) {n : String} {v : Value}
    (hv : v.isControlFlow = false) : EnvPlain (env.extend n v) := by
  intro x w hw
  simp only [Env.extend] at hw
  split at hw
  · cases hw; exact hv
  · exact h x w hw

theorem extend_ne {env : Env} {n x : String} (v : Value) (h : x ≠ n) :
    (env.extend n v) x = env x := by
  simp only [Env.extend]
  rw [if_neg (by simpa using h)]

/-! ## One step of `denote'` -/

section Steps

variable (bi : Builtins) (fuel : Nat)

theorem var_run (x : String) (env : Env) :
    (denote' bi fuel (.var x)).run env =
      match env x with
      | some v => (.val v, env)
      | none => (.err s!"undefined variable: {x}", env) := by
  simp only [denote']
  cases h : env x <;>
    simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, h]

theorem lit_run (l : ImpLit) (env : Env) :
    (denote' bi fuel (.lit l)).run env = (.val (Value.ofLit l), env) := by
  simp only [denote']; rfl

theorem unitVal_run (env : Env) :
    (denote' bi fuel .unitVal).run env = (.val .unit, env) := by
  simp only [denote']; rfl

theorem letBind_run (n : String) (val body : ImpExpr) (env : Env) :
    (denote' bi fuel (.letBind n val body)).run env =
      match (denote' bi fuel val).run env with
      | (.val (.controlFlow b v), e1) => (.val (.controlFlow b v), e1)
      | (.val v, e1) => (denote' bi fuel body).run (e1.extend n v)
      | (o, e1) => (o, e1) := by
  simp only [denote', StateT.run, bind, StateT.bind, pure, modify, modifyGet,
    MonadStateOf.modifyGet]
  rcases (denote' bi fuel val) env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v <;> rfl

theorem seq_run (a b : ImpExpr) (env : Env) :
    (denote' bi fuel (.seq a b)).run env =
      match (denote' bi fuel a).run env with
      | (.val (.controlFlow k v), e1) => (.val (.controlFlow k v), e1)
      | (.val _, e1) => (denote' bi fuel b).run e1
      | (o, e1) => (o, e1) := by
  simp only [denote', StateT.run, bind, StateT.bind, pure]
  rcases (denote' bi fuel a) env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v <;> rfl

theorem ifThenElse_run (c t e : ImpExpr) (env : Env) :
    (denote' bi fuel (.ifThenElse c t e)).run env =
      match (denote' bi fuel c).run env with
      | (.val (.controlFlow k v), e1) => (.val (.controlFlow k v), e1)
      | (.val (.bool true), e1) => (denote' bi fuel t).run e1
      | (.val (.bool false), e1) => (denote' bi fuel e).run e1
      | (.val _, e1) => (.err "if condition not a bool", e1)
      | (o, e1) => (o, e1) := by
  simp only [denote', StateT.run, bind, StateT.bind, pure]
  rcases (denote' bi fuel c) env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v with
  | bool b => cases b <;> rfl
  | _ => rfl

theorem cfBreak_run (e : ImpExpr) (env : Env) :
    (denote' bi fuel (.cfBreak e)).run env =
      match (denote' bi fuel e).run env with
      | (.val (.controlFlow k v), e1) => (.val (.controlFlow k v), e1)
      | (.val v, e1) => (.val (.controlFlow true v), e1)
      | (o, e1) => (o, e1) := by
  simp only [denote', StateT.run, bind, StateT.bind, pure]
  rcases (denote' bi fuel e) env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v <;> rfl

theorem cfContinue_run (e : ImpExpr) (env : Env) :
    (denote' bi fuel (.cfContinue e)).run env =
      match (denote' bi fuel e).run env with
      | (.val (.controlFlow k v), e1) => (.val (.controlFlow k v), e1)
      | (.val v, e1) => (.val (.controlFlow false v), e1)
      | (o, e1) => (o, e1) := by
  simp only [denote', StateT.run, bind, StateT.bind, pure]
  rcases (denote' bi fuel e) env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v <;> rfl

theorem app_run (f : String) (args : List ImpExpr) (env : Env) :
    (denote' bi fuel (.app f args)).run env =
      match (denoteArgs' bi fuel args).run env with
      | (some vals, e1) =>
          match bi f vals with
          | some v => (.val v, e1)
          | none => (.err s!"unknown function or bad args: {f}", e1)
      | (none, e1) => (.err "non-value in function arguments", e1) := by
  simp only [denote', denoteApp', StateT.run, bind, StateT.bind, pure]
  rcases (denoteArgs' bi fuel args) env with ⟨o, e1⟩
  rcases o with _ | vals
  · rfl
  · cases h : bi f vals <;> simp only [h] <;> rfl

theorem args_nil_run (env : Env) :
    (denoteArgs' bi fuel []).run env = (some [], env) := by
  simp only [denoteArgs']; rfl

theorem args_cons_run (e : ImpExpr) (es : List ImpExpr) (env : Env) :
    (denoteArgs' bi fuel (e :: es)).run env =
      match (denote' bi fuel e).run env with
      | (.val (.controlFlow _ _), e1) => (none, e1)
      | (.val v, e1) =>
          (((denoteArgs' bi fuel es).run e1).1.map (v :: ·),
            ((denoteArgs' bi fuel es).run e1).2)
      | (_, e1) => (none, e1) := by
  simp only [denoteArgs', StateT.run, bind, StateT.bind, pure]
  rcases (denote' bi fuel e) env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v <;> rfl

end Steps

/-! ## Atoms and right-hand sides -/

section Atoms

variable {bi : Builtins} {fuel : Nat} {c : String}

theorem ofLit_not_cf (l : ImpLit) : (Value.ofLit l).isControlFlow = false := by
  cases l <;> rfl

/-- An atom evaluates to the same outcome in environments agreeing off `c`, and leaves
    each environment unchanged. -/
theorem atom_run {a : ImpExpr} (ha : atomOk c a = true) {env1 env2 : Env}
    (hag : AgreeOff c env1 env2) :
    ((denote' bi fuel a).run env1).1 = ((denote' bi fuel a).run env2).1 ∧
      ((denote' bi fuel a).run env1).2 = env1 ∧ ((denote' bi fuel a).run env2).2 = env2 := by
  cases a with
  | var x =>
    have hx : x ≠ c := by simpa [atomOk] using ha
    rw [var_run, var_run, hag x hx]
    cases env2 x <;> exact ⟨rfl, rfl, rfl⟩
  | lit l => rw [lit_run, lit_run]; exact ⟨rfl, rfl, rfl⟩
  | unitVal => rw [unitVal_run, unitVal_run]; exact ⟨rfl, rfl, rfl⟩
  | _ => simp [atomOk] at ha

/-- An atom in an environment holding no control-flow value ends in a value that is
    not control-flow-tagged, or in an error. -/
theorem atom_plain {a : ImpExpr} (ha : atomOk c a = true) {env : Env} (hp : EnvPlain env) :
    (∃ v, ((denote' bi fuel a).run env).1 = .val v ∧ v.isControlFlow = false) ∨
      ∃ m, ((denote' bi fuel a).run env).1 = .err m := by
  cases a with
  | var x =>
    rw [var_run]
    cases h : env x with
    | none => exact .inr ⟨_, rfl⟩
    | some v => exact .inl ⟨v, rfl, hp x v h⟩
  | lit l => rw [lit_run]; exact .inl ⟨_, rfl, ofLit_not_cf l⟩
  | unitVal => rw [unitVal_run]; exact .inl ⟨_, rfl, rfl⟩
  | _ => simp [atomOk] at ha

/-- A list of atoms evaluates to the same result in environments agreeing off `c`,
    and leaves each environment unchanged. -/
theorem args_run {args : List ImpExpr} (hs : args.all (atomOk c) = true) {env1 env2 : Env}
    (hag : AgreeOff c env1 env2) :
    ((denoteArgs' bi fuel args).run env1).1 = ((denoteArgs' bi fuel args).run env2).1 ∧
      ((denoteArgs' bi fuel args).run env1).2 = env1 ∧
      ((denoteArgs' bi fuel args).run env2).2 = env2 := by
  induction args with
  | nil => rw [args_nil_run, args_nil_run]; exact ⟨rfl, rfl, rfl⟩
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hs
    obtain ⟨h1, h2, h3⟩ := atom_run (bi := bi) (fuel := fuel) hs.1 hag
    obtain ⟨i1, i2, i3⟩ := ih hs.2
    rw [args_cons_run, args_cons_run]
    rcases hr1 : (denote' bi fuel a).run env1 with ⟨o1, e1⟩
    rcases hr2 : (denote' bi fuel a).run env2 with ⟨o2, e2⟩
    simp only [hr1, hr2] at h1 h2 h3
    subst h1 h2 h3
    rcases o1 with v | _ | _ | _ | _
    · cases v with
      | controlFlow => exact ⟨rfl, rfl, rfl⟩
      | _ => dsimp only; exact ⟨by rw [i1], i2, i3⟩
    all_goals exact ⟨rfl, rfl, rfl⟩

/-- A right-hand side of the fragment evaluates to the same outcome in environments
    agreeing off `c`, and leaves each environment unchanged. -/
theorem rhs_run {v : ImpExpr} (hv : rhsOk c v = true) {env1 env2 : Env}
    (hag : AgreeOff c env1 env2) :
    ((denote' bi fuel v).run env1).1 = ((denote' bi fuel v).run env2).1 ∧
      ((denote' bi fuel v).run env1).2 = env1 ∧ ((denote' bi fuel v).run env2).2 = env2 := by
  cases v with
  | app f args =>
    obtain ⟨h1, h2, h3⟩ := args_run (bi := bi) (fuel := fuel) (by simpa [rhsOk] using hv) hag
    rw [app_run, app_run]
    rcases hr1 : (denoteArgs' bi fuel args).run env1 with ⟨o1, e1⟩
    rcases hr2 : (denoteArgs' bi fuel args).run env2 with ⟨o2, e2⟩
    simp only [hr1, hr2] at h1 h2 h3
    subst h1 h2 h3
    rcases o1 with _ | vals
    · exact ⟨rfl, rfl, rfl⟩
    · dsimp only; split <;> exact ⟨rfl, rfl, rfl⟩
  | _ => exact atom_run (by simpa [rhsOk] using hv) hag

/-- A right-hand side of the fragment, in an environment holding no control-flow value
    and under a builtin table returning none, ends in a value that is not
    control-flow-tagged, or in an outcome that is not a value. -/
theorem rhs_plain (hbi : BuiltinsPlain bi) {v : ImpExpr} (hv : rhsOk c v = true) {env : Env}
    (hp : EnvPlain env) :
    ∀ w, ((denote' bi fuel v).run env).1 = .val w → w.isControlFlow = false := by
  intro w hw
  cases v with
  | app f args =>
    rw [app_run] at hw
    rcases hr : (denoteArgs' bi fuel args).run env with ⟨o, e⟩
    rw [hr] at hw
    rcases o with _ | vals
    · cases hw
    · rcases hb : bi f vals with _ | u
      · simp only [hb] at hw; cases hw
      · simp only [hb, Outcome.val.injEq] at hw
        subst hw; exact hbi f vals u hb
  | _ =>
    rcases atom_plain (bi := bi) (fuel := fuel) (by simpa [rhsOk] using hv) hp with
      ⟨u, hu, hcf⟩ | ⟨m, hm⟩
    · rw [hu, Outcome.val.injEq] at hw; subst hw; exact hcf
    · rw [hm] at hw; cases hw

end Atoms

/-! ## The body -/

/-- The relation between a run `r1` of the body `b` from `env1` and a run `r2` of its
    rewriting: `r2` ends in `contNorm` of the outcome of `r1`, in an environment
    agreeing with that of `r1` off `c`, with the flag `c` set exactly when `r1`
    continued; `r1` leaves `c` unchanged, binds no control-flow value, and does not
    continue when `b` has no `cfContinue`. -/
structure BodyRel (c : String) (env1 : Env) (b : ImpExpr) (r1 r2 : Outcome × Env) : Prop where
  out : r2.1 = contNorm r1.1
  agree : AgreeOff c r1.2 r2.2
  keep : r1.2 c = env1 c
  flag : r2.2 c = some (.bool (isCont r1.1))
  plain : EnvPlain r1.2
  noCont : hasCont b = false → isCont r1.1 = false

section Body

variable {bi : Builtins} {fuel : Nat} {c : String}

theorem atom_rel {a : ImpExpr} (ha : atomOk c a = true) {env1 env2 : Env}
    (hag : AgreeOff c env1 env2) (hp : EnvPlain env1) (hc : env2 c = some (.bool false)) :
    BodyRel c env1 a ((denote' bi fuel a).run env1) ((denote' bi fuel a).run env2) := by
  obtain ⟨h1, h2, h3⟩ := atom_run (bi := bi) (fuel := fuel) ha hag
  have hnc : isCont ((denote' bi fuel a).run env1).1 = false := by
    rcases atom_plain (bi := bi) (fuel := fuel) ha hp with ⟨v, hv, hcf⟩ | ⟨m, hm⟩
    · rw [hv]; cases v with
      | controlFlow => simp [Value.isControlFlow] at hcf
      | _ => rfl
    · rw [hm]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => hnc⟩
  · rw [← h1, contNorm_of_not_isCont hnc]
  · rw [h2, h3]; exact hag
  · rw [h2]
  · rw [h3, hnc, hc]
  · rw [h2]; exact hp

theorem atom_pair {a : ImpExpr} (ha : atomOk c a = true) {env1 env2 : Env}
    (hag : AgreeOff c env1 env2) (hp : EnvPlain env1) :
    ∃ o, (denote' bi fuel a).run env1 = (o, env1) ∧ (denote' bi fuel a).run env2 = (o, env2) ∧
      ((∃ v, o = .val v ∧ v.isControlFlow = false) ∨ ∃ m, o = .err m) := by
  obtain ⟨h1, h2, h3⟩ := atom_run (bi := bi) (fuel := fuel) ha hag
  refine ⟨_, Prod.ext rfl h2, Prod.ext h1.symm h3, ?_⟩
  exact atom_plain ha hp

theorem cfBreak_rel {e : ImpExpr} (ha : atomOk c e = true) {env1 env2 : Env}
    (hag : AgreeOff c env1 env2) (hp : EnvPlain env1) (hc : env2 c = some (.bool false)) :
    BodyRel c env1 (.cfBreak e) ((denote' bi fuel (.cfBreak e)).run env1)
      ((denote' bi fuel (contBody c (.cfBreak e))).run env2) := by
  obtain ⟨o, h1, h2, ⟨v, rfl, hcf⟩ | ⟨m, rfl⟩⟩ := atom_pair (bi := bi) (fuel := fuel) ha hag hp
  · simp only [contBody]
    rw [cfBreak_run, cfBreak_run, h1, h2]
    cases v with
    | controlFlow => simp [Value.isControlFlow] at hcf
    | _ => exact ⟨rfl, hag, rfl, hc, hp, fun _ => rfl⟩
  · simp only [contBody]
    rw [cfBreak_run, cfBreak_run, h1, h2]
    exact ⟨rfl, hag, rfl, hc, hp, fun _ => rfl⟩

theorem cfContinue_rel {e : ImpExpr} (ha : atomOk c e = true) {env1 env2 : Env}
    (hag : AgreeOff c env1 env2) (hp : EnvPlain env1) (hc : env2 c = some (.bool false)) :
    BodyRel c env1 (.cfContinue e) ((denote' bi fuel (.cfContinue e)).run env1)
      ((denote' bi fuel (contBody c (.cfContinue e))).run env2) := by
  obtain ⟨o, h1, h2, ⟨v, rfl, hcf⟩ | ⟨m, rfl⟩⟩ := atom_pair (bi := bi) (fuel := fuel) ha hag hp
  · simp only [contBody, setFlag]
    rw [cfContinue_run, seq_run, h1, h2]
    cases v with
    | controlFlow => simp [Value.isControlFlow] at hcf
    | _ =>
      simp only
      rw [letBind_run, lit_run]
      simp only [Value.ofLit]
      rw [unitVal_run]
      exact ⟨rfl, hag.extend_right _, rfl, by simp [isCont], hp, fun h => by simp [hasCont] at h⟩
  · simp only [contBody, setFlag]
    rw [cfContinue_run, seq_run, h1, h2]
    exact ⟨rfl, hag, rfl, hc, hp, fun _ => rfl⟩

/-- The hypothesis of the rewriting of a body `b`, over every pair of starting
    environments. -/
def BodyIH (bi : Builtins) (fuel : Nat) (c : String) (b : ImpExpr) : Prop :=
  ∀ env1 env2, AgreeOff c env1 env2 → EnvPlain env1 → env2 c = some (.bool false) →
    BodyRel c env1 b ((denote' bi fuel b).run env1) ((denote' bi fuel (contBody c b)).run env2)

theorem letBind_rel (hbi : BuiltinsPlain bi) {n : String} {v b : ImpExpr} (hn : n ≠ c)
    (hv : rhsOk c v = true) (ih : BodyIH bi fuel c b) : BodyIH bi fuel c (.letBind n v b) := by
  intro env1 env2 hag hp hc
  obtain ⟨h1, h2, h3⟩ := rhs_run (bi := bi) (fuel := fuel) hv hag
  have hpl := rhs_plain (fuel := fuel) hbi hv hp
  generalize ho : ((denote' bi fuel v).run env1).1 = o at h1 hpl
  have e1 : (denote' bi fuel v).run env1 = (o, env1) := Prod.ext ho h2
  have e2 : (denote' bi fuel v).run env2 = (o, env2) := Prod.ext h1.symm h3
  simp only [contBody]
  rw [letBind_run, letBind_run, e1, e2]
  rcases o with w | _ | _ | _ | _
  · have hw := hpl w rfl
    cases w with
    | controlFlow => simp [Value.isControlFlow] at hw
    | _ =>
      all_goals
        obtain ⟨r1, r2, r3, r4, r5, r6⟩ := ih _ _ (hag.extend n _) (hp.extend hw)
          (by rw [extend_ne _ (Ne.symm hn)]; exact hc)
        exact ⟨r1, r2, by rw [r3, extend_ne _ (Ne.symm hn)], r4, r5, fun h => r6 h⟩
  all_goals exact ⟨rfl, hag, rfl, hc, hp, fun _ => rfl⟩

theorem ifThenElse_rel {x : String} {t e : ImpExpr} (hx : x ≠ c) (iht : BodyIH bi fuel c t)
    (ihe : BodyIH bi fuel c e) : BodyIH bi fuel c (.ifThenElse (.var x) t e) := by
  intro env1 env2 hag hp hc
  simp only [contBody]
  rw [ifThenElse_run, ifThenElse_run, var_run, var_run, hag x hx]
  rcases hx2 : env2 x with _ | v
  · exact ⟨rfl, hag, rfl, hc, hp, fun _ => rfl⟩
  · have hcf := hp x v (by rw [hag x hx, hx2])
    cases v with
    | controlFlow => simp [Value.isControlFlow] at hcf
    | bool bv =>
      cases bv
      · obtain ⟨r1, r2, r3, r4, r5, r6⟩ := ihe env1 env2 hag hp hc
        exact ⟨r1, r2, r3, r4, r5, fun h => r6 (by simp_all [hasCont])⟩
      · obtain ⟨r1, r2, r3, r4, r5, r6⟩ := iht env1 env2 hag hp hc
        exact ⟨r1, r2, r3, r4, r5, fun h => r6 (by simp_all [hasCont])⟩
    | _ => exact ⟨rfl, hag, rfl, hc, hp, fun _ => rfl⟩

theorem seq_rel {a b : ImpExpr} (iha : BodyIH bi fuel c a) (ihb : BodyIH bi fuel c b) :
    BodyIH bi fuel c (.seq a b) := by
  intro env1 env2 hag hp hc
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := iha env1 env2 hag hp hc
  generalize hA1 : (denote' bi fuel a).run env1 = A1 at r1 r2 r3 r4 r5 r6
  generalize hA2 : (denote' bi fuel (contBody c a)).run env2 = A2 at r1 r2 r3 r4 r5 r6
  obtain ⟨o1, e1⟩ := A1
  obtain ⟨o2, e2⟩ := A2
  simp only at r1 r2 r3 r4 r5 r6
  subst r1
  -- the statement after `a` in the rewriting
  have hT : contBody c (.seq a b) = .seq (contBody c a)
      (if hasCont a = true then guardRest c (contBody c b) else contBody c b) := by
    simp only [contBody]; split <;> rfl
  generalize hRdef : (if hasCont a = true then guardRest c (contBody c b)
    else contBody c b) = R at hT
  have hR : e2 c = some (.bool false) →
      (denote' bi fuel R).run e2 = (denote' bi fuel (contBody c b)).run e2 := by
    intro hce
    rw [← hRdef]; split
    · simp only [guardRest]; rw [ifThenElse_run, var_run, hce]
    · rfl
  rw [hT, seq_run, seq_run, hA1, hA2]
  rcases o1 with v | _ | _ | _ | _
  · cases v with
    | controlFlow k w =>
      cases k with
      | true => exact ⟨rfl, r2, r3, r4, r5, fun _ => rfl⟩
      | false =>
        have hca : hasCont a = true := by
          cases h : hasCont a
          · exact absurd (r6 h) (by simp [isCont])
          · rfl
        simp only [contNorm]
        rw [← hRdef, if_pos hca]
        simp only [guardRest]
        rw [ifThenElse_run, var_run, r4]
        simp only [isCont]
        rw [unitVal_run]
        exact ⟨rfl, r2, r3, r4, r5, fun h => by simp [hasCont, hca] at h⟩
    | _ =>
      all_goals
        obtain ⟨s1, s2, s3, s4, s5, s6⟩ := ihb e1 e2 r2 r5 (by rw [r4]; rfl)
        simp only [contNorm]
        rw [hR (by rw [r4]; rfl)]
        exact ⟨s1, s2, by rw [s3, r3], s4, s5,
          fun h => s6 (by simp only [hasCont, Bool.or_eq_false_iff] at h; exact h.2)⟩
  all_goals exact ⟨rfl, r2, r3, r4, r5, fun _ => rfl⟩

/-- **The rewritten body.** For a body of the fragment, from environments agreeing off
    `c` with the flag `false`, the rewritten body ends in `contNorm` of the outcome of
    the body, in an environment agreeing off `c`, with the flag set exactly when the
    body continued. -/
theorem contBody_run (hbi : BuiltinsPlain bi) (b : ImpExpr) (h : bodyOk c b = true) :
    BodyIH bi fuel c b := by
  induction b using ImpExpr.ind with
  | letBind n v b _ ihb =>
    simp only [bodyOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact letBind_rel hbi h.1.1 h.1.2 (ihb h.2)
  | seq a b iha ihb =>
    simp only [bodyOk, Bool.and_eq_true] at h
    exact seq_rel (iha h.1) (ihb h.2)
  | ifThenElse cnd t e _ iht ihe =>
    cases cnd with
    | var x =>
      simp only [bodyOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact ifThenElse_rel h.1.1 (iht h.1.2) (ihe h.2)
    | _ => simp [bodyOk, atomOk] at h
  | cfContinue e _ => exact fun _ _ hag hp hc => cfContinue_rel h hag hp hc
  | cfBreak e _ => exact fun _ _ hag hp hc => cfBreak_rel h hag hp hc
  | var x => exact fun _ _ hag hp hc => atom_rel h hag hp hc
  | lit l => exact fun _ _ hag hp hc => atom_rel h hag hp hc
  | unitVal => exact fun _ _ hag hp hc => atom_rel h hag hp hc
  | _ => simp [bodyOk, atomOk] at h

end Body

/-! ## Loops -/

section Loops

variable (bi : Builtins)

theorem forLoop_ge_run (fuel : Nat) (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : hi ≤ lo) : (denoteForLoop' bi fuel i lo hi body).run env = (.val .unit, env) := by
  rw [denoteForLoop', if_pos h]; rfl

theorem forLoop_zero_run (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : lo < hi) : (denoteForLoop' bi 0 i lo hi body).run env = (.err "out of fuel", env) := by
  rw [denoteForLoop', if_neg (Int.not_le.mpr h), if_pos rfl]; rfl

theorem forLoop_succ_run (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : lo < hi) :
    (denoteForLoop' bi (n + 1) i lo hi body).run env =
      match (denote' bi (n + 1) body).run (env.extend i (.int lo)) with
      | (.val (.controlFlow true v), e2) => (.val v, e2)
      | (.val (.controlFlow false _), e2) => (denoteForLoop' bi n i (lo + 1) hi body).run e2
      | (.val _, e2) => (denoteForLoop' bi n i (lo + 1) hi body).run e2
      | (o, e2) => (o, e2) := by
  rw [denoteForLoop', if_neg (Int.not_le.mpr h)]
  simp only [Nat.add_one_ne_zero, if_false, StateT.run, bind, StateT.bind, pure, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Nat.add_sub_cancel]
  rcases (denote' bi (n + 1) body) (env.extend i (.int lo)) with ⟨o2, e2⟩
  rcases o2 with v2 | _ | _ | _ | _ <;> try rfl
  cases v2 with
  | controlFlow k w => cases k <;> rfl
  | _ => rfl

theorem forLoopRet_ge_run (fuel : Nat) (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : hi ≤ lo) : (denoteForLoop'Return bi fuel i lo hi body).run env = (.val .unit, env) := by
  rw [denoteForLoop'Return, if_pos h]; rfl

theorem forLoopRet_zero_run (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : lo < hi) :
    (denoteForLoop'Return bi 0 i lo hi body).run env = (.err "out of fuel", env) := by
  rw [denoteForLoop'Return, if_neg (Int.not_le.mpr h), if_pos rfl]; rfl

theorem forLoopRet_succ_run (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : lo < hi) :
    (denoteForLoop'Return bi (n + 1) i lo hi body).run env =
      match (denote' bi (n + 1) body).run (env.extend i (.int lo)) with
      | (.val (.controlFlow true (.controlFlow false v)), e2) => (.val v, e2)
      | (.val (.controlFlow true v), e2) => (.val (.controlFlow true v), e2)
      | (.val (.controlFlow false _), e2) =>
          (denoteForLoop'Return bi n i (lo + 1) hi body).run e2
      | (.val _, e2) => (denoteForLoop'Return bi n i (lo + 1) hi body).run e2
      | (o, e2) => (o, e2) := by
  rw [denoteForLoop'Return, if_neg (Int.not_le.mpr h)]
  simp only [Nat.add_one_ne_zero, if_false, StateT.run, bind, StateT.bind, pure, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Nat.add_sub_cancel]
  rcases (denote' bi (n + 1) body) (env.extend i (.int lo)) with ⟨o2, e2⟩
  rcases o2 with v2 | _ | _ | _ | _ <;> try rfl
  cases v2 with
  | controlFlow k w =>
    cases k
    · rfl
    · cases w with
      | controlFlow k2 w2 => cases k2 <;> rfl
      | _ => rfl
  | _ => rfl

/-- The rewritten loop body runs as `contBody` after binding the flag to `false`. -/
theorem contLoopBody_run (fuel : Nat) (c : String) (body : ImpExpr) (env : Env) :
    (denote' bi fuel (contLoopBody c body)).run env =
      (denote' bi fuel (contBody c body)).run (env.extend c (.bool false)) := by
  simp only [contLoopBody, setFlag]
  rw [letBind_run, lit_run]
  rfl

/-- The relation between a run `r1` of a loop over the body from `env1` and a run `r2`
    of the loop over the rewritten body: the same outcome, environments agreeing off
    `c`, `c` unchanged by `r1`, and no control-flow value bound by `r1`. -/
structure LoopRel (c : String) (env1 : Env) (r1 r2 : Outcome × Env) : Prop where
  out : r2.1 = r1.1
  agree : AgreeOff c r1.2 r2.2
  keep : r1.2 c = env1 c
  plain : EnvPlain r1.2

variable {bi}

/-- **`forFold` over the rewritten body.** `denoteForLoop'` over `contLoopBody c body`
    ends in the outcome of `denoteForLoop'` over `body`, in an environment agreeing off
    `c`. -/
theorem contLoop_forFold_run (hbi : BuiltinsPlain bi) {c i : String} {body : ImpExpr}
    (hok : bodyOk c body = true) (hic : i ≠ c) (fuel : Nat) :
    ∀ (lo hi : Int) (env1 env2 : Env), AgreeOff c env1 env2 → EnvPlain env1 →
      LoopRel c env1 ((denoteForLoop' bi fuel i lo hi body).run env1)
        ((denoteForLoop' bi fuel i lo hi (contLoopBody c body)).run env2) := by
  induction fuel with
  | zero =>
    intro lo hi env1 env2 hag hp
    by_cases h : hi ≤ lo
    · rw [forLoop_ge_run _ _ _ _ _ _ _ h, forLoop_ge_run _ _ _ _ _ _ _ h]
      exact ⟨rfl, hag, rfl, hp⟩
    · have h' : lo < hi := Int.lt_of_not_ge h
      rw [forLoop_zero_run _ _ _ _ _ _ h', forLoop_zero_run _ _ _ _ _ _ h']
      exact ⟨rfl, hag, rfl, hp⟩
  | succ n ih =>
    intro lo hi env1 env2 hag hp
    by_cases h : hi ≤ lo
    · rw [forLoop_ge_run _ _ _ _ _ _ _ h, forLoop_ge_run _ _ _ _ _ _ _ h]
      exact ⟨rfl, hag, rfl, hp⟩
    have h' : lo < hi := Int.lt_of_not_ge h
    rw [forLoop_succ_run _ _ _ _ _ _ _ h', forLoop_succ_run _ _ _ _ _ _ _ h', contLoopBody_run]
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := contBody_run (fuel := n + 1) hbi body hok
      (env1.extend i (.int lo)) ((env2.extend i (.int lo)).extend c (.bool false))
      ((hag.extend i _).extend_right _) (hp.extend rfl) (Env.extend_same _ _ _)
    have hkeep : (env1.extend i (.int lo)) c = env1 c := extend_ne _ (Ne.symm hic)
    generalize (denote' bi (n + 1) body).run (env1.extend i (.int lo)) = B1 at r1 r2 r3 r4 r5 r6
    generalize (denote' bi (n + 1) (contBody c body)).run
      ((env2.extend i (.int lo)).extend c (.bool false)) = B2 at r1 r2 r3 r4 r5 r6
    obtain ⟨o1, e1⟩ := B1
    obtain ⟨o2, e2⟩ := B2
    simp only at r1 r2 r3 r4 r5 r6
    subst r1
    rw [hkeep] at r3
    rcases o1 with v | _ | _ | _ | _
    · cases v with
      | controlFlow k w =>
        cases k with
        | true => exact ⟨rfl, r2, r3, r5⟩
        | false =>
          obtain ⟨s1, s2, s3, s4⟩ := ih (lo + 1) hi e1 e2 r2 r5
          exact ⟨s1, s2, by rw [s3, r3], s4⟩
      | _ =>
        all_goals
          obtain ⟨s1, s2, s3, s4⟩ := ih (lo + 1) hi e1 e2 r2 r5
          exact ⟨s1, s2, by rw [s3, r3], s4⟩
    all_goals exact ⟨rfl, r2, r3, r5⟩

/-- **`forFoldReturn` over the rewritten body.** `denoteForLoop'Return` over
    `contLoopBody c body` ends in the outcome of `denoteForLoop'Return` over `body`, in
    an environment agreeing off `c`. -/
theorem contLoop_forFoldReturn_run (hbi : BuiltinsPlain bi) {c i : String} {body : ImpExpr}
    (hok : bodyOk c body = true) (hic : i ≠ c) (fuel : Nat) :
    ∀ (lo hi : Int) (env1 env2 : Env), AgreeOff c env1 env2 → EnvPlain env1 →
      LoopRel c env1 ((denoteForLoop'Return bi fuel i lo hi body).run env1)
        ((denoteForLoop'Return bi fuel i lo hi (contLoopBody c body)).run env2) := by
  induction fuel with
  | zero =>
    intro lo hi env1 env2 hag hp
    by_cases h : hi ≤ lo
    · rw [forLoopRet_ge_run _ _ _ _ _ _ _ h, forLoopRet_ge_run _ _ _ _ _ _ _ h]
      exact ⟨rfl, hag, rfl, hp⟩
    · have h' : lo < hi := Int.lt_of_not_ge h
      rw [forLoopRet_zero_run _ _ _ _ _ _ h', forLoopRet_zero_run _ _ _ _ _ _ h']
      exact ⟨rfl, hag, rfl, hp⟩
  | succ n ih =>
    intro lo hi env1 env2 hag hp
    by_cases h : hi ≤ lo
    · rw [forLoopRet_ge_run _ _ _ _ _ _ _ h, forLoopRet_ge_run _ _ _ _ _ _ _ h]
      exact ⟨rfl, hag, rfl, hp⟩
    have h' : lo < hi := Int.lt_of_not_ge h
    rw [forLoopRet_succ_run _ _ _ _ _ _ _ h', forLoopRet_succ_run _ _ _ _ _ _ _ h',
      contLoopBody_run]
    obtain ⟨r1, r2, r3, r4, r5, r6⟩ := contBody_run (fuel := n + 1) hbi body hok
      (env1.extend i (.int lo)) ((env2.extend i (.int lo)).extend c (.bool false))
      ((hag.extend i _).extend_right _) (hp.extend rfl) (Env.extend_same _ _ _)
    have hkeep : (env1.extend i (.int lo)) c = env1 c := extend_ne _ (Ne.symm hic)
    generalize (denote' bi (n + 1) body).run (env1.extend i (.int lo)) = B1 at r1 r2 r3 r4 r5 r6
    generalize (denote' bi (n + 1) (contBody c body)).run
      ((env2.extend i (.int lo)).extend c (.bool false)) = B2 at r1 r2 r3 r4 r5 r6
    obtain ⟨o1, e1⟩ := B1
    obtain ⟨o2, e2⟩ := B2
    simp only at r1 r2 r3 r4 r5 r6
    subst r1
    rw [hkeep] at r3
    rcases o1 with v | _ | _ | _ | _
    · cases v with
      | controlFlow k w =>
        cases k with
        | true =>
          cases w with
          | controlFlow k2 w2 => cases k2 <;> exact ⟨rfl, r2, r3, r5⟩
          | _ => all_goals exact ⟨rfl, r2, r3, r5⟩
        | false =>
          obtain ⟨s1, s2, s3, s4⟩ := ih (lo + 1) hi e1 e2 r2 r5
          exact ⟨s1, s2, by rw [s3, r3], s4⟩
      | _ =>
        all_goals
          obtain ⟨s1, s2, s3, s4⟩ := ih (lo + 1) hi e1 e2 r2 r5
          exact ⟨s1, s2, by rw [s3, r3], s4⟩
    all_goals exact ⟨rfl, r2, r3, r5⟩

/-- **The `forFold` expression with the rewritten body.** With atomic bounds, the
    `forFold` over `contLoopBody c body` ends in the outcome of the `forFold` over
    `body`, in an environment agreeing off `c`. -/
theorem denote'_contLoop_forFold (hbi : BuiltinsPlain bi) {c i : String} {lo hi body : ImpExpr}
    (hlo : atomOk c lo = true) (hhi : atomOk c hi = true) (hok : bodyOk c body = true)
    (hic : i ≠ c) (fuel : Nat) {env1 env2 : Env} (hag : AgreeOff c env1 env2)
    (hp : EnvPlain env1) :
    LoopRel c env1 ((denote' bi fuel (.forFold i lo hi body)).run env1)
      ((denote' bi fuel (.forFold i lo hi (contLoopBody c body))).run env2) := by
  obtain ⟨ol, hl1, hl2, hlv⟩ := atom_pair (bi := bi) (fuel := fuel) hlo hag hp
  obtain ⟨oh, hh1, hh2, hhv⟩ := atom_pair (bi := bi) (fuel := fuel) hhi hag hp
  simp only [StateT.run] at hl1 hl2 hh1 hh2
  simp only [denote', StateT.run, bind, StateT.bind, hl1, hl2]
  rcases hlv with ⟨vlo, rfl, -⟩ | ⟨m, rfl⟩
  · rcases hhv with ⟨vhi, rfl, -⟩ | ⟨m, rfl⟩
    · cases vlo <;> simp only [StateT.bind, hh1, hh2] <;> cases vhi <;>
        first
          | exact contLoop_forFold_run hbi hok hic fuel _ _ _ _ hag hp
          | exact ⟨rfl, hag, rfl, hp⟩
    · cases vlo <;> simp only [StateT.bind, hh1, hh2] <;> exact ⟨rfl, hag, rfl, hp⟩
  · exact ⟨rfl, hag, rfl, hp⟩

/-- **The `forFoldReturn` expression with the rewritten body.** With atomic bounds, the
    `forFoldReturn` over `contLoopBody c body` ends in the outcome of the
    `forFoldReturn` over `body`, in an environment agreeing off `c`. -/
theorem denote'_contLoop_forFoldReturn (hbi : BuiltinsPlain bi) {c i : String}
    {lo hi body : ImpExpr} (hlo : atomOk c lo = true) (hhi : atomOk c hi = true)
    (hok : bodyOk c body = true) (hic : i ≠ c) (fuel : Nat) {env1 env2 : Env}
    (hag : AgreeOff c env1 env2) (hp : EnvPlain env1) :
    LoopRel c env1 ((denote' bi fuel (.forFoldReturn i lo hi body)).run env1)
      ((denote' bi fuel (.forFoldReturn i lo hi (contLoopBody c body))).run env2) := by
  obtain ⟨ol, hl1, hl2, hlv⟩ := atom_pair (bi := bi) (fuel := fuel) hlo hag hp
  obtain ⟨oh, hh1, hh2, hhv⟩ := atom_pair (bi := bi) (fuel := fuel) hhi hag hp
  simp only [StateT.run] at hl1 hl2 hh1 hh2
  simp only [denote', StateT.run, bind, StateT.bind, hl1, hl2]
  rcases hlv with ⟨vlo, rfl, -⟩ | ⟨m, rfl⟩
  · rcases hhv with ⟨vhi, rfl, -⟩ | ⟨m, rfl⟩
    · cases vlo <;> simp only [StateT.bind, hh1, hh2] <;> cases vhi <;>
        first
          | exact contLoop_forFoldReturn_run hbi hok hic fuel _ _ _ _ hag hp
          | exact ⟨rfl, hag, rfl, hp⟩
    · cases vlo <;> simp only [StateT.bind, hh1, hh2] <;> exact ⟨rfl, hag, rfl, hp⟩
  · exact ⟨rfl, hag, rfl, hp⟩

end Loops

/-! ## Function bodies -/

/-- The function bodies the rewriting covers, for the flag `c`: `letBind` of an atom or
    an application to atoms, `seq`, `ifThenElse` on a variable, a `forFold` or
    `forFoldReturn` with atomic bounds whose body lies in `bodyOk c`, `cfBreak` of an
    atom, and an atom. No loop is nested in a loop body. -/
def fnOk (c : String) : ImpExpr → Bool
  | .letBind n v b => n != c && rhsOk c v && fnOk c b
  | .seq a b => fnOk c a && fnOk c b
  | .ifThenElse (.var x) t e => x != c && fnOk c t && fnOk c e
  | .forFold i lo hi b => i != c && atomOk c lo && atomOk c hi && bodyOk c b
  | .forFoldReturn i lo hi b => i != c && atomOk c lo && atomOk c hi && bodyOk c b
  | .cfBreak e => atomOk c e
  | e => atomOk c e

/-- A function body with the body of each `forFold` and `forFoldReturn` rewritten by
    `contLoopBody c`. -/
def contFn (c : String) : ImpExpr → ImpExpr
  | .letBind n v b => .letBind n v (contFn c b)
  | .seq a b => .seq (contFn c a) (contFn c b)
  | .ifThenElse cnd t e => .ifThenElse cnd (contFn c t) (contFn c e)
  | .forFold i lo hi b => .forFold i lo hi (contLoopBody c b)
  | .forFoldReturn i lo hi b => .forFoldReturn i lo hi (contLoopBody c b)
  | e => e

section Fn

variable {bi : Builtins} {c : String}

/-- The hypothesis of the rewriting of a function body `e`, over every pair of starting
    environments. -/
def FnIH (bi : Builtins) (c : String) (e : ImpExpr) : Prop :=
  ∀ fuel env1 env2, AgreeOff c env1 env2 → EnvPlain env1 →
    LoopRel c env1 ((denote' bi fuel e).run env1) ((denote' bi fuel (contFn c e)).run env2)

theorem atom_fnIH {a : ImpExpr} (ha : atomOk c a = true) (hc : contFn c a = a) :
    FnIH bi c a := by
  intro fuel env1 env2 hag hp
  rw [hc]
  obtain ⟨o, h1, h2, -⟩ := atom_pair (bi := bi) (fuel := fuel) ha hag hp
  rw [h1, h2]
  exact ⟨rfl, hag, rfl, hp⟩

theorem cfBreak_fnIH {e : ImpExpr} (ha : atomOk c e = true) : FnIH bi c (.cfBreak e) := by
  intro fuel env1 env2 hag hp
  simp only [contFn]
  obtain ⟨o, h1, h2, -⟩ := atom_pair (bi := bi) (fuel := fuel) ha hag hp
  rw [cfBreak_run, cfBreak_run, h1, h2]
  rcases o with v | _ | _ | _ | _
  · cases v <;> exact ⟨rfl, hag, rfl, hp⟩
  all_goals exact ⟨rfl, hag, rfl, hp⟩

/-- **The rewritten function body.** For a function body of `fnOk c`, from
    environments agreeing off `c`, the rewritten body ends in the outcome of the body,
    in an environment agreeing off `c`. -/
theorem contFn_run (hbi : BuiltinsPlain bi) (e : ImpExpr) (h : fnOk c e = true) :
    FnIH bi c e := by
  induction e using ImpExpr.ind with
  | letBind n v b _ ihb =>
    simp only [fnOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hn, hv⟩, hb⟩ := h
    intro fuel env1 env2 hag hp
    obtain ⟨h1, h2, h3⟩ := rhs_run (bi := bi) (fuel := fuel) hv hag
    have hpl := rhs_plain (fuel := fuel) hbi hv hp
    generalize ho : ((denote' bi fuel v).run env1).1 = o at h1 hpl
    have e1 : (denote' bi fuel v).run env1 = (o, env1) := Prod.ext ho h2
    have e2 : (denote' bi fuel v).run env2 = (o, env2) := Prod.ext h1.symm h3
    simp only [contFn]
    rw [letBind_run, letBind_run, e1, e2]
    rcases o with w | _ | _ | _ | _
    · have hw := hpl w rfl
      cases w with
      | controlFlow => simp [Value.isControlFlow] at hw
      | _ =>
        all_goals
          obtain ⟨r1, r2, r3, r4⟩ := ihb hb fuel _ _ (hag.extend n _) (hp.extend hw)
          exact ⟨r1, r2, by rw [r3, extend_ne _ (Ne.symm hn)], r4⟩
    all_goals exact ⟨rfl, hag, rfl, hp⟩
  | seq a b iha ihb =>
    simp only [fnOk, Bool.and_eq_true] at h
    intro fuel env1 env2 hag hp
    obtain ⟨r1, r2, r3, r4⟩ := iha h.1 fuel env1 env2 hag hp
    generalize hA1 : (denote' bi fuel a).run env1 = A1 at r1 r2 r3 r4
    generalize hA2 : (denote' bi fuel (contFn c a)).run env2 = A2 at r1 r2 r3 r4
    obtain ⟨o1, e1⟩ := A1
    obtain ⟨o2, e2⟩ := A2
    simp only at r1 r2 r3 r4
    subst r1
    simp only [contFn]
    rw [seq_run, seq_run, hA1, hA2]
    rcases o2 with v | _ | _ | _ | _
    · cases v with
      | controlFlow k w => exact ⟨rfl, r2, r3, r4⟩
      | _ =>
        all_goals
          obtain ⟨s1, s2, s3, s4⟩ := ihb h.2 fuel e1 e2 r2 r4
          exact ⟨s1, s2, by rw [s3, r3], s4⟩
    all_goals exact ⟨rfl, r2, r3, r4⟩
  | ifThenElse cnd t e _ iht ihe =>
    cases cnd with
    | var x =>
      simp only [fnOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      intro fuel env1 env2 hag hp
      simp only [contFn]
      rw [ifThenElse_run, ifThenElse_run, var_run, var_run, hag x h.1.1]
      rcases env2 x with _ | v
      · exact ⟨rfl, hag, rfl, hp⟩
      · cases v with
        | bool bv =>
          cases bv
          · exact ihe h.2 fuel env1 env2 hag hp
          · exact iht h.1.2 fuel env1 env2 hag hp
        | _ => exact ⟨rfl, hag, rfl, hp⟩
    | _ => simp [fnOk, atomOk] at h
  | forFold i lo hi b _ _ _ =>
    simp only [fnOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨hi_, hlo⟩, hhi⟩, hb⟩ := h
    exact fun fuel _ _ hag hp => denote'_contLoop_forFold hbi hlo hhi hb hi_ fuel hag hp
  | forFoldReturn i lo hi b _ _ _ =>
    simp only [fnOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨hi_, hlo⟩, hhi⟩, hb⟩ := h
    exact fun fuel _ _ hag hp => denote'_contLoop_forFoldReturn hbi hlo hhi hb hi_ fuel hag hp
  | cfBreak e _ => exact cfBreak_fnIH h
  | var x => exact atom_fnIH h rfl
  | lit l => exact atom_fnIH h rfl
  | unitVal => exact atom_fnIH h rfl
  | _ => simp [fnOk, atomOk] at h

/-- **The rewritten function body from one environment.** A run of a body of `fnOk c`
    and the run of `contFn c` of it from the same environment end in the same
    outcome. -/
theorem contFn_run_same (hbi : BuiltinsPlain bi) {e : ImpExpr} (h : fnOk c e = true)
    (fuel : Nat) {env : Env} (hp : EnvPlain env) :
    ((denote' bi fuel (contFn c e)).run env).1 = ((denote' bi fuel e).run env).1 :=
  (contFn_run hbi e h fuel env env (fun _ _ => rfl) hp).out

end Fn

end Hax.ContinueFlag

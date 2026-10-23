/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Phase.ContinueFlag

/-!
# A counted loop that breaks, as a while loop on a run flag

A `forFold i lo hi body` whose body ends a trip by `cfBreak e` leaves the loop with the
value of `e`; `denote'` passes the value `controlFlow true v` through `seq` and `letBind`
to the loop. `brkLoop N i lo hi body` expresses the same control with program variables
the function does not use (`BrkNames`):

* `ctr` holds the counter and `hi` the upper bound, both read once as integers by the
  builtin `ofB`;
* `go`, the run flag, is `true` while the next trip runs: it starts as `lt ctr hi`, a
  break sets it to `false`, and the end of a trip that did not break increments `ctr`
  and sets `go` to `lt ctr hi`;
* `res` holds the value of the loop: `unit`, or the payload of the break;
* the loop is `whileFold (var go)` over the body with each `cfBreak e` replaced by
  binding `res` to `e` and `go` to `false`, each statement after a statement that may
  break guarded by `go` (`brkBody`), followed by the end of the trip (`tripEnd`).

The rewritten loop has no `cfBreak`; its statements are `letBind`s of atoms and of
applications to atoms, `seq`, `ifThenElse` on a variable and one `whileFold` on a
variable.

**Fragment.** `bodyOk N` admits `letBind` of an atom or an application to atoms, `seq`,
`ifThenElse` on a variable, `cfBreak` of an atom, and an atom; an atom is a literal,
`unitVal` or a variable that is not one of the four names, and no `letBind` binds one of
them. The fragment has no `cfContinue`; `ContinueFlag.contFn` removes it, so the phase
runs after that one.

**Refinement.** Runs are compared from environments agreeing off the four names
(`AgreeOff N`), from an environment holding no control-flow value and a builtin table
returning none. The while loop spends one unit of fuel more than the counted loop: it
checks its fuel before reading its guard. Whenever the `forFold` at fuel `n` ends in a
value, the rewritten loop at fuel `n + 1` ends in the same value, in an environment
agreeing off the four names. A run of the `forFold` that fails (out of fuel, a bound
that is not an integer, an undefined variable) constrains nothing.

## Main results

* `brkBody_run`: the rewritten body ends in `brkNorm` of the outcome of the body, with
  `go` cleared and `res` holding the payload exactly when the body broke
* `brkWhile_run`: `denoteWhile'` over `brkLoopBody` at fuel `n + 1` refines
  `denoteForLoop'` over the body at fuel `n`
* `brkLoop_run`: the same for the `forFold` expression with atomic bounds and
  `brkLoop`
* `brkFn`, `brkFn_run`: the phase over function bodies of `fnOk N`, rewriting each
  `forFold` whose body breaks
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.BreakFlag

open Hax.ContinueFlag (EnvPlain BuiltinsPlain EnvPlain.extend var_run lit_run unitVal_run
  letBind_run seq_run ifThenElse_run cfBreak_run app_run args_nil_run args_cons_run
  ofLit_not_cf forLoop_ge_run forLoop_zero_run forLoop_succ_run)

/-! ## Names -/

/-- The names of the rewriting: the program variables `go` (run flag), `ctr` (counter),
    `hi` (upper bound) and `res` (value of the loop), and the builtin heads `ofB` (a
    bound as an integer), `add` and `lt`. -/
structure BrkNames where
  go : String
  ctr : String
  hi : String
  res : String
  ofB : String
  add : String
  lt : String

namespace BrkNames

/-- Whether `x` is one of the four program variables of the rewriting. -/
def fresh (N : BrkNames) (x : String) : Bool :=
  x == N.go || x == N.ctr || x == N.hi || x == N.res

/-- The four program variables of the rewriting are pairwise distinct. -/
structure Distinct (N : BrkNames) : Prop where
  go_ctr : N.go ≠ N.ctr
  go_hi : N.go ≠ N.hi
  go_res : N.go ≠ N.res
  ctr_hi : N.ctr ≠ N.hi
  ctr_res : N.ctr ≠ N.res
  hi_res : N.hi ≠ N.res

/-- The integer a loop bound denotes: an integer, or an unsigned word read as an
    integer, as `denote'` reads the bounds of a `forFold`. -/
def boundInt : Value → Option Int
  | .int k => some k
  | .uint _ k => some (k : Int)
  | _ => none

/-- The builtin heads of the rewriting: `ofB` reads a bound as an integer, `add` adds
    `1` to an integer and `lt` compares two integers. -/
structure Spec (N : BrkNames) (bi : Builtins) : Prop where
  ofB : ∀ v k, boundInt v = some k → bi N.ofB [v] = some (.int k)
  add : ∀ a : Int, bi N.add [.int a, .int 1] = some (.int (a + 1))
  lt : ∀ a b : Int, bi N.lt [.int a, .int b] = some (.bool (decide (a < b)))

theorem fresh_go (N : BrkNames) : N.fresh N.go = true := by simp [fresh]
theorem fresh_ctr (N : BrkNames) : N.fresh N.ctr = true := by simp [fresh]
theorem fresh_hi (N : BrkNames) : N.fresh N.hi = true := by simp [fresh]
theorem fresh_res (N : BrkNames) : N.fresh N.res = true := by simp [fresh]

theorem ne_of_fresh {N : BrkNames} {x y : String} (hx : N.fresh x = false)
    (hy : N.fresh y = true) : x ≠ y := by
  rintro rfl; rw [hx] at hy; cases hy

end BrkNames

/-! ## The rewriting -/

variable (N : BrkNames)

/-- An atom: a literal, `unitVal`, or a variable that is not one of the four names. -/
def atomOk : ImpExpr → Bool
  | .var x => !N.fresh x
  | .lit _ => true
  | .unitVal => true
  | _ => false

/-- The right-hand side of a `letBind` in the fragment: an atom, or an application to
    atoms. -/
def rhsOk : ImpExpr → Bool
  | .app _ args => args.all (atomOk N)
  | e => atomOk N e

/-- Whether `e` has a `cfBreak` at a statement position. -/
def hasBrk : ImpExpr → Bool
  | .cfBreak _ => true
  | .letBind _ _ b => hasBrk b
  | .seq a b => hasBrk a || hasBrk b
  | .ifThenElse _ t e => hasBrk t || hasBrk e
  | _ => false

/-- The loop bodies the rewriting covers. -/
def bodyOk : ImpExpr → Bool
  | .letBind n v b => !N.fresh n && rhsOk N v && bodyOk b
  | .seq a b => bodyOk a && bodyOk b
  | .ifThenElse (.var x) t e => !N.fresh x && bodyOk t && bodyOk e
  | .cfBreak e => atomOk N e
  | e => atomOk N e

/-- The body with each `cfBreak e` replaced by binding `res` to `e` and clearing `go`,
    and each statement after a statement that may break guarded by `go`. -/
def brkBody : ImpExpr → ImpExpr
  | .letBind n v b => .letBind n v (brkBody b)
  | .seq a b =>
      if hasBrk a then .seq (brkBody a) (.ifThenElse (.var N.go) (brkBody b) .unitVal)
      else .seq (brkBody a) (brkBody b)
  | .ifThenElse c t e => .ifThenElse c (brkBody t) (brkBody e)
  | .cfBreak e => .letBind N.res e (.letBind N.go (.lit (.bool false)) .unitVal)
  | e => e

/-- The end of a trip: when `go` is set, increment `ctr` and set `go` to `lt ctr hi`. -/
def tripEnd : ImpExpr :=
  .ifThenElse (.var N.go)
    (.letBind N.ctr (.app N.add [.var N.ctr, .lit (.int 1)])
      (.letBind N.go (.app N.lt [.var N.ctr, .var N.hi]) .unitVal))
    .unitVal

/-- The body of the while loop: bind the counter `i` to `ctr`, run the rewritten body,
    then end the trip. -/
def brkLoopBody (i : String) (body : ImpExpr) : ImpExpr :=
  .letBind i (.var N.ctr) (.seq (brkBody N body) (tripEnd N))

/-- The rewriting of `forFold i lo hi body`: read the bounds into `ctr` and `hi`, set
    `res` to `unit` and `go` to `lt ctr hi`, run the while loop on `go`, and return
    `res`. -/
def brkLoop (i : String) (lo hi body : ImpExpr) : ImpExpr :=
  .letBind N.ctr (.app N.ofB [lo]) <|
  .letBind N.hi (.app N.ofB [hi]) <|
  .letBind N.res .unitVal <|
  .letBind N.go (.app N.lt [.var N.ctr, .var N.hi]) <|
  .seq (.whileFold (.var N.go) (brkLoopBody N i body)) (.var N.res)

/-! ## Outcomes and environments -/

/-- Whether an outcome is a break, `val (controlFlow true v)`. -/
def isBrk : Outcome → Bool
  | .val (.controlFlow true _) => true
  | _ => false

/-- A break outcome read as the value `unit`; every other outcome unchanged. -/
def brkNorm : Outcome → Outcome
  | .val (.controlFlow true _) => .val .unit
  | o => o

/-- Two environments agree off the four names. -/
def AgreeOff (e1 e2 : Env) : Prop := ∀ x, N.fresh x = false → e1 x = e2 x

variable {N}

theorem AgreeOff.extend {e1 e2 : Env} (h : AgreeOff N e1 e2) (n : String) (v : Value) :
    AgreeOff N (e1.extend n v) (e2.extend n v) := by
  intro x hx
  simp only [Env.extend]
  split
  · rfl
  · exact h x hx

theorem AgreeOff.extend_right {e1 e2 : Env} (h : AgreeOff N e1 e2) {n : String}
    (hn : N.fresh n = true) (v : Value) : AgreeOff N e1 (e2.extend n v) := by
  intro x hx
  rw [Env.extend_other _ _ _ _ (BrkNames.ne_of_fresh hx hn)]
  exact h x hx

theorem brkNorm_of_plain {v : Value} (hv : v.isControlFlow = false) :
    brkNorm (.val v) = .val v := by
  cases v <;> first | rfl | simp at hv

theorem isBrk_of_plain {v : Value} (hv : v.isControlFlow = false) :
    isBrk (.val v) = false := by
  cases v <;> first | rfl | simp at hv

/-! ## Steps of `denote'` on a value -/

section Steps

variable {bi : Builtins} {f : Nat}

theorem letBind_run_val {n : String} {val body : ImpExpr} {env e1 : Env} {v : Value}
    (h : (denote' bi f val).run env = (.val v, e1)) (hv : v.isControlFlow = false) :
    (denote' bi f (.letBind n val body)).run env = (denote' bi f body).run (e1.extend n v) := by
  rw [letBind_run, h]
  cases v <;> first | rfl | simp at hv

theorem letBind_run_err {n : String} {val body : ImpExpr} {env e1 : Env} {m : String}
    (h : (denote' bi f val).run env = (.err m, e1)) :
    (denote' bi f (.letBind n val body)).run env = (.err m, e1) := by
  rw [letBind_run, h]

theorem seq_run_val {a b : ImpExpr} {env e1 : Env} {v : Value}
    (h : (denote' bi f a).run env = (.val v, e1)) (hv : v.isControlFlow = false) :
    (denote' bi f (.seq a b)).run env = (denote' bi f b).run e1 := by
  rw [seq_run, h]
  cases v <;> first | rfl | simp at hv

theorem seq_run_brk {a b : ImpExpr} {env e1 : Env} {v : Value}
    (h : (denote' bi f a).run env = (.val (.controlFlow true v), e1)) :
    (denote' bi f (.seq a b)).run env = (.val (.controlFlow true v), e1) := by
  rw [seq_run, h]

theorem seq_run_err {a b : ImpExpr} {env e1 : Env} {m : String}
    (h : (denote' bi f a).run env = (.err m, e1)) :
    (denote' bi f (.seq a b)).run env = (.err m, e1) := by
  rw [seq_run, h]

theorem ite_run_var {x : String} {t e : ImpExpr} {env : Env} {b : Bool}
    (h : env x = some (.bool b)) :
    (denote' bi f (.ifThenElse (.var x) t e)).run env =
      (denote' bi f (if b then t else e)).run env := by
  rw [ifThenElse_run, var_run, h]
  cases b <;> rfl

theorem whileFold_run (c body : ImpExpr) (env : Env) :
    (denote' bi f (.whileFold c body)).run env = (denoteWhile' bi f c body).run env := by
  conv => lhs; unfold denote'

theorem while_var_false {g : String} {body : ImpExpr} {env : Env} (n : Nat)
    (h : env g = some (.bool false)) :
    (denoteWhile' bi (n + 1) (.var g) body).run env = (.val .unit, env) := by
  have hc : (denote' bi (n + 1) (.var g)).run env = (.val (.bool false), env) := by
    rw [var_run, h]
  unfold denoteWhile'
  rw [ite_eq_right (Nat.add_one_ne_zero n)]
  simp only [StateT.run, bind, StateT.bind] at hc ⊢
  rw [hc]; rfl

theorem while_var_true {g : String} {body : ImpExpr} {env e1 : Env} (n : Nat) {w : Value}
    (h : env g = some (.bool true))
    (hb : (denote' bi (n + 1) body).run env = (.val w, e1)) (hw : w.isControlFlow = false) :
    (denoteWhile' bi (n + 1) (.var g) body).run env = (denoteWhile' bi n (.var g) body).run e1 := by
  have hc : (denote' bi (n + 1) (.var g)).run env = (.val (.bool true), env) := by
    rw [var_run, h]
  conv => lhs; unfold denoteWhile'
  rw [ite_eq_right (Nat.add_one_ne_zero n)]
  simp only [StateT.run, bind, StateT.bind] at hc hb ⊢
  rw [hc]
  dsimp only
  simp only [StateT.bind, hb]
  cases w <;> first | rfl | simp at hw

end Steps

/-! ## Atoms and right-hand sides -/

section Atoms

variable {bi : Builtins}

/-- An atom evaluates to the same outcome, at any two fuels, in environments agreeing off
    the four names, and leaves each environment unchanged. -/
theorem atom_run {a : ImpExpr} (ha : atomOk N a = true) (f1 f2 : Nat) {env1 env2 : Env}
    (hag : AgreeOff N env1 env2) :
    ((denote' bi f1 a).run env1).1 = ((denote' bi f2 a).run env2).1 ∧
      ((denote' bi f1 a).run env1).2 = env1 ∧ ((denote' bi f2 a).run env2).2 = env2 := by
  cases a with
  | var x =>
    have hx : N.fresh x = false := by simpa [atomOk] using ha
    rw [var_run, var_run, hag x hx]
    cases env2 x <;> exact ⟨rfl, rfl, rfl⟩
  | lit l => rw [lit_run, lit_run]; exact ⟨rfl, rfl, rfl⟩
  | unitVal => rw [unitVal_run, unitVal_run]; exact ⟨rfl, rfl, rfl⟩
  | _ => simp [atomOk] at ha

/-- An atom in an environment holding no control-flow value ends in a value that is not
    control-flow-tagged, or in an error. -/
theorem atom_plain {a : ImpExpr} (ha : atomOk N a = true) (f : Nat) {env : Env}
    (hp : EnvPlain env) :
    (∃ v, ((denote' bi f a).run env).1 = .val v ∧ v.isControlFlow = false) ∨
      ∃ m, ((denote' bi f a).run env).1 = .err m := by
  cases a with
  | var x =>
    rw [var_run]
    cases h : env x with
    | none => exact .inr ⟨_, rfl⟩
    | some v => exact .inl ⟨v, rfl, hp x v h⟩
  | lit l => rw [lit_run]; exact .inl ⟨_, rfl, ofLit_not_cf l⟩
  | unitVal => rw [unitVal_run]; exact .inl ⟨_, rfl, rfl⟩
  | _ => simp [atomOk] at ha

/-- The outcome shared by the runs of an atom from two environments agreeing off the
    four names. -/
theorem atom_pair {a : ImpExpr} (ha : atomOk N a = true) (f1 f2 : Nat) {env1 env2 : Env}
    (hag : AgreeOff N env1 env2) (hp : EnvPlain env1) :
    ∃ o, (denote' bi f1 a).run env1 = (o, env1) ∧ (denote' bi f2 a).run env2 = (o, env2) ∧
      ((∃ v, o = .val v ∧ v.isControlFlow = false) ∨ ∃ m, o = .err m) := by
  obtain ⟨h1, h2, h3⟩ := atom_run (bi := bi) ha f1 f2 hag
  exact ⟨_, Prod.ext rfl h2, Prod.ext h1.symm h3, atom_plain ha f1 hp⟩

/-- A list of atoms evaluates to the same result, at any two fuels, in environments
    agreeing off the four names, and leaves each environment unchanged. -/
theorem args_run {args : List ImpExpr} (hs : args.all (atomOk N) = true) (f1 f2 : Nat)
    {env1 env2 : Env} (hag : AgreeOff N env1 env2) :
    ((denoteArgs' bi f1 args).run env1).1 = ((denoteArgs' bi f2 args).run env2).1 ∧
      ((denoteArgs' bi f1 args).run env1).2 = env1 ∧
      ((denoteArgs' bi f2 args).run env2).2 = env2 := by
  induction args with
  | nil => rw [args_nil_run, args_nil_run]; exact ⟨rfl, rfl, rfl⟩
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hs
    obtain ⟨h1, h2, h3⟩ := atom_run (bi := bi) hs.1 f1 f2 hag
    obtain ⟨i1, i2, i3⟩ := ih hs.2
    rw [args_cons_run, args_cons_run]
    rcases hr1 : (denote' bi f1 a).run env1 with ⟨o1, e1⟩
    rcases hr2 : (denote' bi f2 a).run env2 with ⟨o2, e2⟩
    simp only [hr1, hr2] at h1 h2 h3
    subst h1 h2 h3
    rcases o1 with v | _ | _ | _ | _
    · cases v with
      | controlFlow => exact ⟨rfl, rfl, rfl⟩
      | _ => dsimp only; exact ⟨by rw [i1], i2, i3⟩
    all_goals exact ⟨rfl, rfl, rfl⟩

/-- The outcome shared by the runs of a right-hand side of the fragment from two
    environments agreeing off the four names, under a builtin table returning no
    control-flow value. -/
theorem rhs_pair (hbi : BuiltinsPlain bi) {v : ImpExpr} (hv : rhsOk N v = true)
    (f1 f2 : Nat) {env1 env2 : Env} (hag : AgreeOff N env1 env2) (hp : EnvPlain env1) :
    ∃ o, (denote' bi f1 v).run env1 = (o, env1) ∧ (denote' bi f2 v).run env2 = (o, env2) ∧
      ((∃ w, o = .val w ∧ w.isControlFlow = false) ∨ ∃ m, o = .err m) := by
  cases v with
  | app g args =>
    obtain ⟨h1, h2, h3⟩ := args_run (bi := bi) (by simpa [rhsOk] using hv) f1 f2 hag
    rw [app_run, app_run]
    rcases hr1 : (denoteArgs' bi f1 args).run env1 with ⟨o1, e1⟩
    rcases hr2 : (denoteArgs' bi f2 args).run env2 with ⟨o2, e2⟩
    simp only [hr1, hr2] at h1 h2 h3
    subst h1 h2 h3
    rcases o1 with _ | vals
    · exact ⟨_, rfl, rfl, .inr ⟨_, rfl⟩⟩
    · dsimp only
      rcases hb : bi g vals with _ | u
      · exact ⟨_, rfl, rfl, .inr ⟨_, rfl⟩⟩
      · exact ⟨_, rfl, rfl, .inl ⟨u, rfl, hbi g vals u hb⟩⟩
  | _ => exact atom_pair (by simpa [rhsOk] using hv) f1 f2 hag hp

end Atoms

/-! ## The body -/

/-- The relation between a run `r1` of the body `b` and a run `r2` of its rewriting from
    `env2`: `r2` ends in `brkNorm` of the outcome of `r1`, in an environment agreeing with
    that of `r1` off the four names; a break clears `go` and leaves its payload in `res`;
    otherwise `go` and `res` keep their values, and `ctr` and `hi` keep theirs in any
    case. The outcome of `r1` is a value that is not control-flow-tagged, a break or an
    error, it is not a break when `b` has no `cfBreak`, and `r1` binds no control-flow
    value. -/
structure BodyRel (N : BrkNames) (env2 : Env) (b : ImpExpr) (r1 r2 : Outcome × Env) :
    Prop where
  out : r2.1 = brkNorm r1.1
  agree : AgreeOff N r1.2 r2.2
  goBrk : isBrk r1.1 = true → r2.2 N.go = some (.bool false)
  goKeep : isBrk r1.1 = false → r2.2 N.go = env2 N.go
  res : ∀ v, r1.1 = .val (.controlFlow true v) → r2.2 N.res = some v
  resKeep : isBrk r1.1 = false → r2.2 N.res = env2 N.res
  ctr : r2.2 N.ctr = env2 N.ctr
  hi : r2.2 N.hi = env2 N.hi
  plain : EnvPlain r1.2
  shape : (∃ v, r1.1 = .val v ∧ v.isControlFlow = false) ∨
    (∃ v, r1.1 = .val (.controlFlow true v) ∧ v.isControlFlow = false) ∨ ∃ m, r1.1 = .err m
  noBrk : hasBrk b = false → isBrk r1.1 = false

/-- The hypothesis of the rewriting of a body `b` at the fuels `f1` and `f2`, over every
    pair of starting environments; `go` is set where `b` may break. -/
def BodyIH (N : BrkNames) (bi : Builtins) (f1 f2 : Nat) (b : ImpExpr) : Prop :=
  ∀ env1 env2, AgreeOff N env1 env2 → EnvPlain env1 →
    (hasBrk b = true → env2 N.go = some (.bool true)) →
    BodyRel N env2 b ((denote' bi f1 b).run env1) ((denote' bi f2 (brkBody N b)).run env2)

section Body

variable {bi : Builtins} {f1 f2 : Nat}

/-- Runs of a body and of its rewriting ending in the same outcome, that is neither a
    value tagged as control flow nor a break, in the starting environments. -/
theorem BodyRel.same {env1 env2 : Env} {b : ImpExpr} {o : Outcome}
    (hag : AgreeOff N env1 env2) (hp : EnvPlain env1)
    (ho : (∃ v, o = .val v ∧ v.isControlFlow = false) ∨ ∃ m, o = .err m) :
    BodyRel N env2 b (o, env1) (o, env2) := by
  have hnb : isBrk o = false := by
    rcases ho with ⟨v, rfl, hv⟩ | ⟨m, rfl⟩
    · exact isBrk_of_plain hv
    · rfl
  refine ⟨?_, hag, ?_, fun _ => rfl, ?_, fun _ => rfl, rfl, rfl, hp, ?_, fun _ => hnb⟩
  · rcases ho with ⟨v, rfl, hv⟩ | ⟨m, rfl⟩
    · exact (brkNorm_of_plain hv).symm
    · rfl
  · intro h; rw [hnb] at h; cases h
  · intro v hv; simp only at hv; rw [hv] at hnb; cases hnb
  · rcases ho with h | h
    · exact .inl h
    · exact .inr (.inr h)

/-- A relation between runs of `b` holds for `b'` when a break of the first run implies
    a `cfBreak` in `b'`. -/
theorem BodyRel.mono {env2 : Env} {b b' : ImpExpr} {r1 r2 : Outcome × Env}
    (r : BodyRel N env2 b r1 r2) (h : hasBrk b' = false → isBrk r1.1 = false) :
    BodyRel N env2 b' r1 r2 :=
  { r with noBrk := h }

theorem atom_rel {a : ImpExpr} (ha : atomOk N a = true) : BodyIH N bi f1 f2 a := by
  intro env1 env2 hag hp _
  obtain ⟨o, h1, h2, ho⟩ := atom_pair (bi := bi) ha f1 f2 hag hp
  have hb : brkBody N a = a := by
    cases a <;> simp_all [atomOk, brkBody]
  rw [hb, h1, h2]
  exact BodyRel.same hag hp ho

theorem cfBreak_rel (hN : N.Distinct) {e : ImpExpr} (ha : atomOk N e = true) :
    BodyIH N bi f1 f2 (.cfBreak e) := by
  intro env1 env2 hag hp _
  obtain ⟨o, h1, h2, ⟨v, rfl, hv⟩ | ⟨m, rfl⟩⟩ := atom_pair (bi := bi) ha f1 f2 hag hp
  · have hb : (denote' bi f1 (.cfBreak e)).run env1 = (.val (.controlFlow true v), env1) := by
      rw [cfBreak_run, h1]; cases v <;> first | rfl | simp at hv
    have h3 : (denote' bi f2 (brkBody N (.cfBreak e))).run env2 =
        (.val .unit, (env2.extend N.res v).extend N.go (.bool false)) := by
      simp only [brkBody]
      rw [letBind_run_val h2 hv, letBind_run_val (lit_run _ _ _ _) rfl, unitVal_run]
      rfl
    rw [hb, h3]
    refine ⟨rfl, (hag.extend_right N.fresh_res v).extend_right N.fresh_go _,
      fun _ => Env.extend_same _ _ _, fun h => by simp [isBrk] at h, ?_,
      fun h => by simp [isBrk] at h, ?_, ?_, hp, .inr (.inl ⟨v, rfl, hv⟩),
      fun h => by simp [hasBrk] at h⟩
    · intro u hu
      simp only [Outcome.val.injEq, Value.controlFlow.injEq, true_and] at hu
      subst hu
      dsimp only
      rw [Env.extend_other _ _ _ _ hN.go_res.symm, Env.extend_same]
    · dsimp only
      rw [Env.extend_other _ _ _ _ hN.go_ctr.symm, Env.extend_other _ _ _ _ hN.ctr_res]
    · dsimp only
      rw [Env.extend_other _ _ _ _ hN.go_hi.symm, Env.extend_other _ _ _ _ hN.hi_res]
  · simp only [brkBody]
    rw [cfBreak_run, h1, letBind_run_err h2]
    exact BodyRel.same hag hp (.inr ⟨m, rfl⟩)

theorem letBind_rel (hbi : BuiltinsPlain bi) {n : String} {v b : ImpExpr}
    (hn : N.fresh n = false) (hv : rhsOk N v = true) (ih : BodyIH N bi f1 f2 b) :
    BodyIH N bi f1 f2 (.letBind n v b) := by
  intro env1 env2 hag hp hgo
  obtain ⟨o, h1, h2, ⟨w, rfl, hw⟩ | ⟨m, rfl⟩⟩ := rhs_pair hbi hv f1 f2 hag hp
  · have hn' : ∀ y, N.fresh y = true → y ≠ n := fun y hy h => by
      subst h; rw [hn] at hy; cases hy
    simp only [brkBody]
    rw [letBind_run_val h1 hw, letBind_run_val h2 hw]
    have hgo' : hasBrk b = true → (env2.extend n w) N.go = some (.bool true) := fun h => by
      rw [Env.extend_other _ _ _ _ (hn' _ N.fresh_go)]; exact hgo h
    have s := ih _ _ (hag.extend n w) (hp.extend hw) hgo'
    exact ⟨s.out, s.agree, s.goBrk,
      fun h => (s.goKeep h).trans (Env.extend_other _ _ _ _ (hn' _ N.fresh_go)), s.res,
      fun h => (s.resKeep h).trans (Env.extend_other _ _ _ _ (hn' _ N.fresh_res)),
      s.ctr.trans (Env.extend_other _ _ _ _ (hn' _ N.fresh_ctr)),
      s.hi.trans (Env.extend_other _ _ _ _ (hn' _ N.fresh_hi)), s.plain, s.shape,
      fun h => s.noBrk h⟩
  · simp only [brkBody]
    rw [letBind_run_err h1, letBind_run_err h2]
    exact BodyRel.same hag hp (.inr ⟨m, rfl⟩)

theorem ifThenElse_rel {x : String} {t e : ImpExpr} (hx : N.fresh x = false)
    (iht : BodyIH N bi f1 f2 t) (ihe : BodyIH N bi f1 f2 e) :
    BodyIH N bi f1 f2 (.ifThenElse (.var x) t e) := by
  intro env1 env2 hag hp hgo
  simp only [brkBody]
  rw [ifThenElse_run, ifThenElse_run, var_run, var_run, hag x hx]
  rcases hx2 : env2 x with _ | v
  · exact BodyRel.same hag hp (.inr ⟨_, rfl⟩)
  · have hcf := hp x v (by rw [hag x hx, hx2])
    cases v with
    | controlFlow => simp at hcf
    | bool bv =>
      cases bv
      · exact (ihe env1 env2 hag hp (fun h => hgo (by simp [hasBrk, h]))).mono
          (fun h => (ihe env1 env2 hag hp (fun h' => hgo (by simp [hasBrk, h']))).noBrk
            (by simp_all [hasBrk]))
      · exact (iht env1 env2 hag hp (fun h => hgo (by simp [hasBrk, h]))).mono
          (fun h => (iht env1 env2 hag hp (fun h' => hgo (by simp [hasBrk, h']))).noBrk
            (by simp_all [hasBrk]))
    | _ => exact BodyRel.same hag hp (.inr ⟨_, rfl⟩)

theorem seq_rel {a b : ImpExpr} (iha : BodyIH N bi f1 f2 a) (ihb : BodyIH N bi f1 f2 b) :
    BodyIH N bi f1 f2 (.seq a b) := by
  intro env1 env2 hag hp hgo
  have r := iha env1 env2 hag hp (fun h => hgo (by simp [hasBrk, h]))
  generalize hA1 : (denote' bi f1 a).run env1 = A1 at r
  generalize hA2 : (denote' bi f2 (brkBody N a)).run env2 = A2 at r
  obtain ⟨o1, e1⟩ := A1
  obtain ⟨o2, e2⟩ := A2
  have hT : brkBody N (.seq a b) = .seq (brkBody N a)
      (if hasBrk a = true then .ifThenElse (.var N.go) (brkBody N b) .unitVal
        else brkBody N b) := by
    simp only [brkBody]; split <;> rfl
  rw [hT]
  rcases r.shape with ⟨w, hw1, hw⟩ | ⟨w, hw1, hw⟩ | ⟨m, hm⟩
  · simp only at hw1; subst hw1
    have ho2 : o2 = .val w := by
      have := r.out; simp only at this; rw [this, brkNorm_of_plain hw]
    subst ho2
    have hnb := isBrk_of_plain hw
    have hgoe2 : e2 N.go = env2 N.go := r.goKeep hnb
    rw [seq_run_val hA1 hw, seq_run_val hA2 hw]
    have hR : (denote' bi f2 (if hasBrk a = true then
        .ifThenElse (.var N.go) (brkBody N b) .unitVal else brkBody N b)).run e2 =
        (denote' bi f2 (brkBody N b)).run e2 := by
      split
      · next hab =>
        rw [ite_run_var (b := true) (by rw [hgoe2]; exact hgo (by simp [hasBrk, hab]))]
        rfl
      · rfl
    rw [hR]
    have s := ihb e1 e2 r.agree r.plain
      (fun h => by rw [hgoe2]; exact hgo (by simp [hasBrk, h]))
    exact ⟨s.out, s.agree, s.goBrk, fun h => (s.goKeep h).trans hgoe2, s.res,
      fun h => (s.resKeep h).trans (r.resKeep hnb), s.ctr.trans r.ctr, s.hi.trans r.hi,
      s.plain, s.shape,
      fun h => s.noBrk (by simp only [hasBrk, Bool.or_eq_false_iff] at h; exact h.2)⟩
  · simp only at hw1; subst hw1
    have ho2 : o2 = .val .unit := by have := r.out; simpa [brkNorm] using this
    subst ho2
    have hab : hasBrk a = true := by
      cases h : hasBrk a
      · have := r.noBrk h; simp [isBrk] at this
      · rfl
    have hgo2 : e2 N.go = some (.bool false) := r.goBrk rfl
    rw [seq_run_brk hA1, seq_run_val hA2 rfl, ite_eq_left hab, ite_run_var hgo2]
    simp only [Bool.false_eq_true, ↓reduceIte, unitVal_run]
    exact r.mono (fun h => by simp [hasBrk, hab] at h)
  · simp only at hm; subst hm
    have ho2 : o2 = .err m := by have := r.out; simpa [brkNorm] using this
    subst ho2
    rw [seq_run_err hA1, seq_run_err hA2]
    exact r.mono (fun _ => rfl)

/-- **The rewritten body.** For a body of the fragment, at any two fuels, from
    environments agreeing off the four names with `go` set where the body may break,
    the rewritten body ends in `brkNorm` of the outcome of the body; a break clears `go`
    and leaves its payload in `res`. -/
theorem brkBody_run (hN : N.Distinct) (hbi : BuiltinsPlain bi) (b : ImpExpr)
    (h : bodyOk N b = true) : BodyIH N bi f1 f2 b := by
  induction b using ImpExpr.ind with
  | letBind n v b _ ihb =>
    simp only [bodyOk, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact letBind_rel hbi h.1.1 h.1.2 (ihb h.2)
  | seq a b iha ihb =>
    simp only [bodyOk, Bool.and_eq_true] at h
    exact seq_rel (iha h.1) (ihb h.2)
  | ifThenElse cnd t e _ iht ihe =>
    cases cnd with
    | var x =>
      simp only [bodyOk, Bool.and_eq_true, Bool.not_eq_true'] at h
      exact ifThenElse_rel h.1.1 (iht h.1.2) (ihe h.2)
    | _ => simp [bodyOk, atomOk] at h
  | cfBreak e _ => exact cfBreak_rel hN h
  | var x => exact atom_rel h
  | lit l => exact atom_rel h
  | unitVal => exact atom_rel h
  | _ => simp [bodyOk, atomOk] at h

end Body

/-! ## The loop -/

/-- The refinement of a run `r1` by a run `r2`: whenever `r1` ends in a value, `r2` ends
    in the same value, in an environment agreeing off the four names; the value is not
    control-flow-tagged and `r1` binds no control-flow value. -/
def Refines (N : BrkNames) (r1 r2 : Outcome × Env) : Prop :=
  ∀ v, r1.1 = .val v →
    r2.1 = .val v ∧ AgreeOff N r1.2 r2.2 ∧ EnvPlain r1.2 ∧ v.isControlFlow = false

/-- The relation between a run `r1` of a counted loop and a run `r2` of the while loop:
    whenever `r1` ends in a value, `r2` ends in `unit` with that value in `res`, in an
    environment agreeing off the four names. -/
def LoopRel (N : BrkNames) (r1 r2 : Outcome × Env) : Prop :=
  ∀ v, r1.1 = .val v → r2.1 = .val .unit ∧ r2.2 N.res = some v ∧ AgreeOff N r1.2 r2.2 ∧
    EnvPlain r1.2 ∧ v.isControlFlow = false

section Loop

variable {bi : Builtins}

theorem forLoop_succ_val {n : Nat} {i : String} {lo H : Int} {body : ImpExpr} {env e1 : Env}
    {w : Value} (h : lo < H)
    (hb : (denote' bi (n + 1) body).run (env.extend i (.int lo)) = (.val w, e1))
    (hw : w.isControlFlow = false) :
    (denoteForLoop' bi (n + 1) i lo H body).run env =
      (denoteForLoop' bi n i (lo + 1) H body).run e1 := by
  rw [forLoop_succ_run _ _ _ _ _ _ _ h, hb]
  cases w <;> first | rfl | simp at hw

theorem forLoop_succ_brk {n : Nat} {i : String} {lo H : Int} {body : ImpExpr} {env e1 : Env}
    {w : Value} (h : lo < H)
    (hb : (denote' bi (n + 1) body).run (env.extend i (.int lo)) =
      (.val (.controlFlow true w), e1)) :
    (denoteForLoop' bi (n + 1) i lo H body).run env = (.val w, e1) := by
  rw [forLoop_succ_run _ _ _ _ _ _ _ h, hb]

/-- The end of a trip with `go` set increments `ctr` and sets `go` to `lt ctr hi`. -/
theorem tripEnd_run_go (hN : N.Distinct) (hs : N.Spec bi) {f : Nat} {e : Env} {k H : Int}
    (hg : e N.go = some (.bool true)) (hc : e N.ctr = some (.int k))
    (hh : e N.hi = some (.int H)) :
    (denote' bi f (tripEnd N)).run e =
      (.val .unit, (e.extend N.ctr (.int (k + 1))).extend N.go (.bool (decide (k + 1 < H)))) := by
  have h1 : (denote' bi f (.app N.add [.var N.ctr, .lit (.int 1)])).run e =
      (.val (.int (k + 1)), e) := by
    rw [app_run, args_cons_run, var_run, hc]
    dsimp only
    rw [args_cons_run, lit_run]
    dsimp only [Value.ofLit]
    rw [args_nil_run]
    simp [hs.add]
  have h2 : (denote' bi f (.app N.lt [.var N.ctr, .var N.hi])).run
      (e.extend N.ctr (.int (k + 1))) =
      (.val (.bool (decide (k + 1 < H))), e.extend N.ctr (.int (k + 1))) := by
    rw [app_run, args_cons_run, var_run, Env.extend_same]
    dsimp only
    rw [args_cons_run, var_run, Env.extend_other _ _ _ _ hN.ctr_hi.symm, hh]
    dsimp only
    rw [args_nil_run]
    simp [hs.lt]
  simp only [tripEnd]
  rw [ite_run_var hg]
  simp only [↓reduceIte]
  rw [letBind_run_val h1 rfl, letBind_run_val h2 rfl, unitVal_run]

/-- The end of a trip with `go` cleared does nothing. -/
theorem tripEnd_run_stop {f : Nat} {e : Env} (hg : e N.go = some (.bool false)) :
    (denote' bi f (tripEnd N)).run e = (.val .unit, e) := by
  simp only [tripEnd]
  rw [ite_run_var hg]
  exact unitVal_run _ _ _

/-- **The while loop.** From environments agreeing off the four names, with `ctr` holding
    the counter `lo`, `hi` the bound `H`, `go` the comparison `lo < H` and `res` the value
    `unit`, `denoteWhile'` over `brkLoopBody` at fuel `n + 1` refines `denoteForLoop'`
    over the body at fuel `n`. -/
theorem brkWhile_run (hN : N.Distinct) (hbi : BuiltinsPlain bi) (hs : N.Spec bi)
    {i : String} {body : ImpExpr} (hok : bodyOk N body = true) (hi : N.fresh i = false)
    (n : Nat) :
    ∀ (lo H : Int) (env1 env2 : Env), AgreeOff N env1 env2 → EnvPlain env1 →
      env2 N.ctr = some (.int lo) → env2 N.hi = some (.int H) →
      env2 N.go = some (.bool (decide (lo < H))) → env2 N.res = some .unit →
      LoopRel N ((denoteForLoop' bi n i lo H body).run env1)
        ((denoteWhile' bi (n + 1) (.var N.go) (brkLoopBody N i body)).run env2) := by
  have hfi : ∀ y, N.fresh y = true → y ≠ i := fun y hy h => by
    subst h; rw [hi] at hy; cases hy
  induction n with
  | zero =>
    intro lo H env1 env2 hag hp _ _ hg hr v hv
    by_cases h : H ≤ lo
    · rw [forLoop_ge_run _ _ _ _ _ _ _ h] at hv ⊢
      simp only [Outcome.val.injEq] at hv; subst hv
      rw [while_var_false 0 (by rw [hg]; simp [Int.not_lt.mpr h])]
      exact ⟨rfl, hr, hag, hp, rfl⟩
    · rw [forLoop_zero_run _ _ _ _ _ _ (Int.lt_of_not_ge h)] at hv; cases hv
  | succ n ih =>
    intro lo H env1 env2 hag hp hc hh hg hr v hv
    by_cases h : H ≤ lo
    · rw [forLoop_ge_run _ _ _ _ _ _ _ h] at hv ⊢
      simp only [Outcome.val.injEq] at hv; subst hv
      rw [while_var_false (n + 1) (by rw [hg]; simp [Int.not_lt.mpr h])]
      exact ⟨rfl, hr, hag, hp, rfl⟩
    have h' : lo < H := Int.lt_of_not_ge h
    have hgT : env2 N.go = some (.bool true) := by rw [hg]; simp [h']
    have hstart : (denote' bi (n + 1 + 1) (brkLoopBody N i body)).run env2 =
        (denote' bi (n + 1 + 1) (.seq (brkBody N body) (tripEnd N))).run
          (env2.extend i (.int lo)) := by
      simp only [brkLoopBody]
      rw [letBind_run_val (by rw [var_run, hc]) rfl]
    have s := brkBody_run (f1 := n + 1) (f2 := n + 1 + 1) hN hbi body hok
      (env1.extend i (.int lo)) (env2.extend i (.int lo)) (hag.extend i _) (hp.extend rfl)
      (fun _ => by rw [Env.extend_other _ _ _ _ (hfi _ N.fresh_go)]; exact hgT)
    generalize hB1 : (denote' bi (n + 1) body).run (env1.extend i (.int lo)) = B1 at s
    generalize hB2 : (denote' bi (n + 1 + 1) (brkBody N body)).run
      (env2.extend i (.int lo)) = B2 at s
    obtain ⟨o1, e1⟩ := B1
    obtain ⟨o2, e2⟩ := B2
    rcases s.shape with ⟨w, hw1, hw⟩ | ⟨w, hw1, hw⟩ | ⟨m, hm⟩
    · simp only at hw1; subst hw1
      have ho2 : o2 = .val w := by
        have := s.out; simp only at this; rw [this, brkNorm_of_plain hw]
      subst ho2
      have hnb := isBrk_of_plain hw
      rw [forLoop_succ_val h' hB1 hw] at hv ⊢
      have hg2 : e2 N.go = some (.bool true) :=
        (s.goKeep hnb).trans (by rw [Env.extend_other _ _ _ _ (hfi _ N.fresh_go)]; exact hgT)
      have hc2 : e2 N.ctr = some (.int lo) :=
        s.ctr.trans (by rw [Env.extend_other _ _ _ _ (hfi _ N.fresh_ctr)]; exact hc)
      have hh2 : e2 N.hi = some (.int H) :=
        s.hi.trans (by rw [Env.extend_other _ _ _ _ (hfi _ N.fresh_hi)]; exact hh)
      have hr2 : e2 N.res = some .unit :=
        (s.resKeep hnb).trans (by rw [Env.extend_other _ _ _ _ (hfi _ N.fresh_res)]; exact hr)
      have hag2 : AgreeOff N e1
          ((e2.extend N.ctr (.int (lo + 1))).extend N.go (.bool (decide (lo + 1 < H)))) :=
        (s.agree.extend_right N.fresh_ctr _).extend_right N.fresh_go _
      have hbody : (denote' bi (n + 1 + 1) (brkLoopBody N i body)).run env2 =
          (.val .unit,
            (e2.extend N.ctr (.int (lo + 1))).extend N.go (.bool (decide (lo + 1 < H)))) := by
        rw [hstart, seq_run_val hB2 hw, tripEnd_run_go hN hs hg2 hc2 hh2]
      rw [while_var_true (n + 1) hgT hbody rfl]
      exact ih (lo + 1) H e1 _ hag2 s.plain
        (by rw [Env.extend_other _ _ _ _ hN.go_ctr.symm, Env.extend_same])
        (by rw [Env.extend_other _ _ _ _ hN.go_hi.symm,
          Env.extend_other _ _ _ _ hN.ctr_hi.symm, hh2])
        (Env.extend_same _ _ _)
        (by rw [Env.extend_other _ _ _ _ hN.go_res.symm,
          Env.extend_other _ _ _ _ hN.ctr_res.symm, hr2]) v hv
    · simp only at hw1; subst hw1
      have ho2 : o2 = .val .unit := by have := s.out; simpa [brkNorm] using this
      subst ho2
      rw [forLoop_succ_brk h' hB1] at hv ⊢
      have hwv : w = v := by simpa using hv
      subst hwv
      have hg2 : e2 N.go = some (.bool false) := s.goBrk rfl
      have hbody : (denote' bi (n + 1 + 1) (brkLoopBody N i body)).run env2 =
          (.val .unit, e2) := by
        rw [hstart, seq_run_val hB2 rfl, tripEnd_run_stop hg2]
      rw [while_var_true (n + 1) hgT hbody rfl, while_var_false n hg2]
      exact ⟨rfl, s.res w rfl, s.agree, s.plain, hw⟩
    · simp only at hm; subst hm
      rw [forLoop_succ_run _ _ _ _ _ _ _ h', hB1] at hv; cases hv

/-- A `forFold` with atomic bounds that ends in a value read both bounds as integers and
    ran `denoteForLoop'` between them. -/
theorem forFold_val {f : Nat} {i : String} {lo hi body : ImpExpr} {env e : Env} {v : Value}
    (hlo : atomOk N lo = true) (hhi : atomOk N hi = true) (hp : EnvPlain env)
    (h : (denote' bi f (.forFold i lo hi body)).run env = (.val v, e)) :
    ∃ vlo vhi klo khi, (denote' bi f lo).run env = (.val vlo, env) ∧
      (denote' bi f hi).run env = (.val vhi, env) ∧ BrkNames.boundInt vlo = some klo ∧
      BrkNames.boundInt vhi = some khi ∧
      (denoteForLoop' bi f i klo khi body).run env = (.val v, e) := by
  obtain ⟨ol, hl1, -, hlv⟩ := atom_pair (bi := bi) hlo f f (fun _ _ => rfl) hp
  obtain ⟨oh, hh1, -, hhv⟩ := atom_pair (bi := bi) hhi f f (fun _ _ => rfl) hp
  simp only [StateT.run] at hl1 hh1 h ⊢
  simp only [denote', StateT.bind, bind, hl1] at h
  rcases hlv with ⟨vlo, rfl, hvlo⟩ | ⟨m, rfl⟩
  · rcases hhv with ⟨vhi, rfl, hvhi⟩ | ⟨m, rfl⟩
    · cases vlo <;> cases vhi <;> simp only [StateT.bind, hh1, bind] at h <;>
        first
          | exact ⟨_, _, _, _, hl1, hh1, rfl, rfl, h⟩
          | exact Outcome.noConfusion (congrArg Prod.fst h)
          | (simp [pure, StateT.pure] at h; done)
          | (simp at hvlo; done)
          | (simp at hvhi; done)
          | (simp [pure, StateT.pure] at h; done)
    · cases vlo <;> simp only [StateT.bind, hh1, bind] at h <;>
        first
          | exact Outcome.noConfusion (congrArg Prod.fst h)
          | (simp at hvlo; done)
  · exact Outcome.noConfusion (congrArg Prod.fst h)

theorem args_cons_run_val {f : Nat} {e : ImpExpr} {es : List ImpExpr} {env e1 : Env}
    {v : Value} (h : (denote' bi f e).run env = (.val v, e1)) (hv : v.isControlFlow = false) :
    (denoteArgs' bi f (e :: es)).run env =
      (((denoteArgs' bi f es).run e1).1.map (v :: ·), ((denoteArgs' bi f es).run e1).2) := by
  rw [args_cons_run, h]
  cases v <;> first | rfl | simp at hv

/-- `ofB` applied to an atom holding a bound reads the integer it denotes. -/
theorem ofB_run (hs : N.Spec bi) {f : Nat} {a : ImpExpr} {env : Env} {u : Value} {k : Int}
    (ha : (denote' bi f a).run env = (.val u, env)) (hk : BrkNames.boundInt u = some k) :
    (denote' bi f (.app N.ofB [a])).run env = (.val (.int k), env) := by
  have hu : u.isControlFlow = false := by
    cases u <;> first | rfl | simp [BrkNames.boundInt] at hk
  rw [app_run, args_cons_run_val ha hu, args_nil_run]
  simp [hs.ofB _ _ hk]

/-- `lt ctr hi` on integers. -/
theorem lt_run (hs : N.Spec bi) {f : Nat} {env : Env} {k H : Int}
    (hc : env N.ctr = some (.int k)) (hh : env N.hi = some (.int H)) :
    (denote' bi f (.app N.lt [.var N.ctr, .var N.hi])).run env =
      (.val (.bool (decide (k < H))), env) := by
  rw [app_run, args_cons_run_val (by rw [var_run, hc]) rfl,
    args_cons_run_val (by rw [var_run, hh]) rfl, args_nil_run]
  simp [hs.lt]

/-- **The `forFold` expression and its rewriting.** With atomic bounds and a body of the
    fragment, from environments agreeing off the four names, `brkLoop` at fuel `n + 1`
    refines the `forFold` at fuel `n`: whenever the `forFold` ends in a value, `brkLoop`
    ends in the same value, in an environment agreeing off the four names. -/
theorem brkLoop_run (hN : N.Distinct) (hbi : BuiltinsPlain bi) (hs : N.Spec bi)
    {i : String} {lo hi body : ImpExpr} (hlo : atomOk N lo = true) (hhi : atomOk N hi = true)
    (hok : bodyOk N body = true) (hi' : N.fresh i = false) (n : Nat) {env1 env2 : Env}
    (hag : AgreeOff N env1 env2) (hp : EnvPlain env1) :
    Refines N ((denote' bi n (.forFold i lo hi body)).run env1)
      ((denote' bi (n + 1) (brkLoop N i lo hi body)).run env2) := by
  intro v hv
  generalize hF : (denote' bi n (.forFold i lo hi body)).run env1 = F at hv ⊢
  obtain ⟨o, e1⟩ := F
  simp only at hv; subst hv
  obtain ⟨vlo, vhi, klo, khi, hl1, hh1, hklo, hkhi, hloop⟩ := forFold_val hlo hhi hp hF
  -- the environments of the rewritten loop
  have hagA : AgreeOff N env1 (env2.extend N.ctr (.int klo)) := hag.extend_right N.fresh_ctr _
  have hagB : AgreeOff N env1 ((env2.extend N.ctr (.int klo)).extend N.hi (.int khi)) :=
    hagA.extend_right N.fresh_hi _
  have hagC : AgreeOff N env1
      (((env2.extend N.ctr (.int klo)).extend N.hi (.int khi)).extend N.res .unit) :=
    hagB.extend_right N.fresh_res _
  generalize hC : ((env2.extend N.ctr (.int klo)).extend N.hi (.int khi)).extend N.res .unit
    = envC at hagC
  have hcC : envC N.ctr = some (.int klo) := by
    rw [← hC, Env.extend_other _ _ _ _ hN.ctr_res, Env.extend_other _ _ _ _ hN.ctr_hi,
      Env.extend_same]
  have hhC : envC N.hi = some (.int khi) := by
    rw [← hC, Env.extend_other _ _ _ _ hN.hi_res, Env.extend_same]
  have hrC : envC N.res = some .unit := by rw [← hC, Env.extend_same]
  have hagD : AgreeOff N env1 (envC.extend N.go (.bool (decide (klo < khi)))) :=
    hagC.extend_right N.fresh_go _
  -- the bounds read in the rewritten loop
  have hl2 : (denote' bi (n + 1) lo).run env2 = (.val vlo, env2) := by
    obtain ⟨o', h1, h2, -⟩ := atom_pair (bi := bi) hlo n (n + 1) hag hp
    rw [h1] at hl1; cases hl1; exact h2
  have hh2 : (denote' bi (n + 1) hi).run (env2.extend N.ctr (.int klo)) =
      (.val vhi, env2.extend N.ctr (.int klo)) := by
    obtain ⟨o', h1, h2, -⟩ := atom_pair (bi := bi) hhi n (n + 1) hagA hp
    rw [h1] at hh1; cases hh1; exact h2
  have hlr := brkWhile_run hN hbi hs hok hi' n klo khi env1 _ hagD hp
    (by rw [Env.extend_other _ _ _ _ hN.go_ctr.symm, hcC])
    (by rw [Env.extend_other _ _ _ _ hN.go_hi.symm, hhC])
    (Env.extend_same _ _ _)
    (by rw [Env.extend_other _ _ _ _ hN.go_res.symm, hrC])
  rw [hloop] at hlr
  generalize hW : (denoteWhile' bi (n + 1) (.var N.go) (brkLoopBody N i body)).run
    (envC.extend N.go (.bool (decide (klo < khi)))) = W at hlr
  obtain ⟨ow, ew⟩ := W
  obtain ⟨how, hres, hagw, hpw, hvcf⟩ := hlr v rfl
  simp only at how hres hagw hpw
  subst how
  simp only [brkLoop]
  rw [letBind_run_val (ofB_run hs hl2 hklo) rfl, letBind_run_val (ofB_run hs hh2 hkhi) rfl,
    letBind_run_val (unitVal_run _ _ _) rfl, hC, letBind_run_val (lt_run hs hcC hhC) rfl,
    seq_run_val (by rw [whileFold_run, hW]) rfl, var_run, hres]
  exact ⟨rfl, hagw, hpw, hvcf⟩

/-- A body with no `cfBreak` is its own rewriting. -/
theorem brkBody_of_noBrk {b : ImpExpr} (h : hasBrk b = false) : brkBody N b = b := by
  induction b using ImpExpr.ind with
  | letBind n v b _ ihb => simp only [hasBrk] at h; simp only [brkBody, ihb h]
  | seq a b iha ihb =>
    simp only [hasBrk, Bool.or_eq_false_iff] at h
    simp only [brkBody, h.1, iha h.1, ihb h.2]; rfl
  | ifThenElse c t e _ iht ihe =>
    simp only [hasBrk, Bool.or_eq_false_iff] at h
    simp only [brkBody, iht h.1, ihe h.2]
  | cfBreak e _ => simp [hasBrk] at h
  | _ => rfl

/-- A `forFold` whose bounds are atoms holding bounds runs `denoteForLoop'` between the
    integers they denote. -/
theorem forFold_run_bounds {f : Nat} {i : String} {lo hi body : ImpExpr} {env : Env}
    {vlo vhi : Value} {klo khi : Int} (hl : (denote' bi f lo).run env = (.val vlo, env))
    (hh : (denote' bi f hi).run env = (.val vhi, env))
    (hklo : BrkNames.boundInt vlo = some klo) (hkhi : BrkNames.boundInt vhi = some khi) :
    (denote' bi f (.forFold i lo hi body)).run env =
      (denoteForLoop' bi f i klo khi body).run env := by
  simp only [StateT.run] at hl hh ⊢
  simp only [denote', StateT.bind, bind, hl]
  cases vlo <;> cases vhi <;> simp only [BrkNames.boundInt, Option.some.injEq,
    reduceCtorEq] at hklo hkhi <;> subst hklo hkhi <;> simp only [StateT.bind, hh, bind] <;>
    rfl

/-- **A counted loop that does not break.** `denoteForLoop'` over a body of the fragment
    with no `cfBreak` at fuel `n + 1` refines the same loop at fuel `n`. -/
theorem plainLoop_run (hN : N.Distinct) (hbi : BuiltinsPlain bi) {i : String}
    {body : ImpExpr} (hok : bodyOk N body = true) (hnb : hasBrk body = false) (n : Nat) :
    ∀ (lo H : Int) (env1 env2 : Env), AgreeOff N env1 env2 → EnvPlain env1 →
      Refines N ((denoteForLoop' bi n i lo H body).run env1)
        ((denoteForLoop' bi (n + 1) i lo H body).run env2) := by
  induction n with
  | zero =>
    intro lo H env1 env2 hag hp v hv
    by_cases h : H ≤ lo
    · rw [forLoop_ge_run _ _ _ _ _ _ _ h] at hv ⊢
      rw [forLoop_ge_run _ _ _ _ _ _ _ h]
      simp only [Outcome.val.injEq] at hv; subst hv
      exact ⟨rfl, hag, hp, rfl⟩
    · rw [forLoop_zero_run _ _ _ _ _ _ (Int.lt_of_not_ge h)] at hv; cases hv
  | succ n ih =>
    intro lo H env1 env2 hag hp v hv
    by_cases h : H ≤ lo
    · rw [forLoop_ge_run _ _ _ _ _ _ _ h] at hv ⊢
      rw [forLoop_ge_run _ _ _ _ _ _ _ h]
      simp only [Outcome.val.injEq] at hv; subst hv
      exact ⟨rfl, hag, hp, rfl⟩
    have h' : lo < H := Int.lt_of_not_ge h
    have s := brkBody_run (f1 := n + 1) (f2 := n + 1 + 1) hN hbi body hok
      (env1.extend i (.int lo)) (env2.extend i (.int lo)) (hag.extend i _) (hp.extend rfl)
      (fun h => by rw [hnb] at h; cases h)
    rw [brkBody_of_noBrk hnb] at s
    generalize hB1 : (denote' bi (n + 1) body).run (env1.extend i (.int lo)) = B1 at s
    generalize hB2 : (denote' bi (n + 1 + 1) body).run (env2.extend i (.int lo)) = B2 at s
    obtain ⟨o1, e1⟩ := B1
    obtain ⟨o2, e2⟩ := B2
    rcases s.shape with ⟨w, hw1, hw⟩ | ⟨w, hw1, hw⟩ | ⟨m, hm⟩
    · simp only at hw1; subst hw1
      have ho2 : o2 = .val w := by
        have := s.out; simp only at this; rw [this, brkNorm_of_plain hw]
      subst ho2
      rw [forLoop_succ_val h' hB1 hw] at hv ⊢
      rw [forLoop_succ_val h' hB2 hw]
      exact ih (lo + 1) H e1 e2 s.agree s.plain v hv
    · have := s.noBrk hnb; simp only at hw1; rw [hw1] at this; simp [isBrk] at this
    · simp only at hm; subst hm
      rw [forLoop_succ_run _ _ _ _ _ _ _ h', hB1] at hv; cases hv

/-- The `forFold` expression over a body with no `cfBreak` at fuel `n + 1` refines the
    same expression at fuel `n`. -/
theorem plainFold_run (hN : N.Distinct) (hbi : BuiltinsPlain bi) {i : String}
    {lo hi body : ImpExpr} (hlo : atomOk N lo = true) (hhi : atomOk N hi = true)
    (hok : bodyOk N body = true) (hnb : hasBrk body = false)
    (n : Nat) {env1 env2 : Env} (hag : AgreeOff N env1 env2) (hp : EnvPlain env1) :
    Refines N ((denote' bi n (.forFold i lo hi body)).run env1)
      ((denote' bi (n + 1) (.forFold i lo hi body)).run env2) := by
  intro v hv
  generalize hF : (denote' bi n (.forFold i lo hi body)).run env1 = F at hv ⊢
  obtain ⟨o, e1⟩ := F
  simp only at hv; subst hv
  obtain ⟨vlo, vhi, klo, khi, hl1, hh1, hklo, hkhi, hloop⟩ := forFold_val hlo hhi hp hF
  have hl2 : (denote' bi (n + 1) lo).run env2 = (.val vlo, env2) := by
    obtain ⟨o', h1, h2, -⟩ := atom_pair (bi := bi) hlo n (n + 1) hag hp
    rw [h1] at hl1; cases hl1; exact h2
  have hh2 : (denote' bi (n + 1) hi).run env2 = (.val vhi, env2) := by
    obtain ⟨o', h1, h2, -⟩ := atom_pair (bi := bi) hhi n (n + 1) hag hp
    rw [h1] at hh1; cases hh1; exact h2
  rw [forFold_run_bounds hl2 hh2 hklo hkhi]
  have := plainLoop_run (i := i) hN hbi hok hnb n klo khi env1 env2 hag hp v
  rw [hloop] at this
  exact this rfl

end Loop

/-! ## Function bodies -/

/-- The function bodies the phase covers: `letBind` of an atom or an application to
    atoms, `seq`, `ifThenElse` on a variable, a `forFold` with atomic bounds whose body
    lies in `bodyOk N`, and an atom; no `letBind` or loop counter binds one of the four
    names, and no loop is nested in a loop body. -/
def fnOk (N : BrkNames) : ImpExpr → Bool
  | .letBind n v b => !N.fresh n && rhsOk N v && fnOk N b
  | .seq a b => fnOk N a && fnOk N b
  | .ifThenElse (.var x) t e => !N.fresh x && fnOk N t && fnOk N e
  | .forFold i lo hi body => !N.fresh i && atomOk N lo && atomOk N hi && bodyOk N body
  | e => atomOk N e

/-- **The phase.** Each `forFold` whose body has a `cfBreak` becomes `brkLoop`, in every
    statement position of a function body. -/
def brkFn (N : BrkNames) : ImpExpr → ImpExpr
  | .letBind n v b => .letBind n v (brkFn N b)
  | .seq a b => .seq (brkFn N a) (brkFn N b)
  | .ifThenElse c t e => .ifThenElse c (brkFn N t) (brkFn N e)
  | .forFold i lo hi body =>
      if hasBrk body then brkLoop N i lo hi body else .forFold i lo hi body
  | e => e

section Fn

variable {bi : Builtins}

/-- An atom at fuel `k + 1` refines the atom at fuel `k`. -/
theorem atom_refines {a : ImpExpr} (ha : atomOk N a = true) (k : Nat) {env1 env2 : Env}
    (hag : AgreeOff N env1 env2) (hp : EnvPlain env1) :
    Refines N ((denote' bi k a).run env1) ((denote' bi (k + 1) (brkFn N a)).run env2) := by
  have hb : brkFn N a = a := by cases a <;> simp_all [atomOk, brkFn]
  obtain ⟨o, h1, h2, ho⟩ := atom_pair (bi := bi) ha k (k + 1) hag hp
  rw [hb, h1, h2]
  intro w hw
  simp only at hw; subst hw
  rcases ho with ⟨u, hu, hcf⟩ | ⟨m, hm⟩
  · cases hu; exact ⟨rfl, hag, hp, hcf⟩
  · cases hm

/-- **Refinement of the phase.** For a function body of `fnOk N`, from environments
    agreeing off the four names, `brkFn N e` at fuel `n + 1` refines `e` at fuel `n`:
    whenever `e` ends in a value, `brkFn N e` ends in the same value, in an environment
    agreeing off the four names. -/
theorem brkFn_run (hN : N.Distinct) (hbi : BuiltinsPlain bi) (hs : N.Spec bi)
    (e : ImpExpr) (h : fnOk N e = true) :
    ∀ (n : Nat) (env1 env2 : Env), AgreeOff N env1 env2 → EnvPlain env1 →
      Refines N ((denote' bi n e).run env1) ((denote' bi (n + 1) (brkFn N e)).run env2) := by
  induction e using ImpExpr.ind with
  | letBind n v b _ ihb =>
    simp only [fnOk, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨-, hv⟩, hb⟩ := h
    intro k env1 env2 hag hp w hw
    obtain ⟨o, h1, h2, ⟨u, rfl, hu⟩ | ⟨m, rfl⟩⟩ := rhs_pair hbi hv k (k + 1) hag hp
    · simp only [brkFn]
      rw [letBind_run_val h1 hu] at hw ⊢
      rw [letBind_run_val h2 hu]
      exact ihb hb k _ _ (hag.extend n u) (hp.extend hu) w hw
    · rw [letBind_run_err h1] at hw; cases hw
  | seq a b iha ihb =>
    simp only [fnOk, Bool.and_eq_true] at h
    intro k env1 env2 hag hp w hw
    simp only [brkFn]
    have ra := iha h.1 k env1 env2 hag hp
    generalize hF : (denote' bi k (.seq a b)).run env1 = F at hw ⊢
    obtain ⟨o, e1⟩ := F
    simp only at hw; subst hw
    rcases hA : (denote' bi k a).run env1 with ⟨oa, ea⟩
    have hval : ∃ va, oa = .val va := by
      rcases oa with va | m | _ | _ | _
      · exact ⟨va, rfl⟩
      all_goals (rw [seq_run, hA] at hF; exact Outcome.noConfusion (congrArg Prod.fst hF))
    obtain ⟨va, rfl⟩ := hval
    obtain ⟨hA2, hagA, hpA, hva⟩ := ra va (by rw [hA])
    rw [hA] at hagA hpA
    rcases hA2' : (denote' bi (k + 1) (brkFn N a)).run env2 with ⟨oa2, ea2⟩
    rw [hA2'] at hA2 hagA
    simp only at hA2 hagA hpA
    subst hA2
    rw [seq_run_val hA hva] at hF
    rw [seq_run_val hA2' hva]
    have rb := ihb h.2 k ea ea2 hagA hpA w (by rw [hF])
    rw [hF] at rb
    exact rb
  | ifThenElse cnd t e _ iht ihe =>
    cases cnd with
    | var x =>
      simp only [fnOk, Bool.and_eq_true, Bool.not_eq_true'] at h
      intro k env1 env2 hag hp w hw
      simp only [brkFn]
      generalize hF : (denote' bi k (.ifThenElse (.var x) t e)).run env1 = F at hw ⊢
      obtain ⟨o, e1⟩ := F
      simp only at hw; subst hw
      rcases hx : env1 x with _ | u
      · rw [ifThenElse_run, var_run, hx] at hF
        exact Outcome.noConfusion (congrArg Prod.fst hF)
      · cases u with
        | bool bv =>
          have hx2 : env2 x = some (.bool bv) := by rw [← hag x h.1.1, hx]
          rw [ite_run_var hx] at hF
          rw [ite_run_var hx2]
          cases bv
          · simp only [Bool.false_eq_true, ↓reduceIte] at hF ⊢
            have := ihe h.2 k env1 env2 hag hp w (by rw [hF])
            rw [hF] at this; exact this
          · simp only [↓reduceIte] at hF ⊢
            have := iht h.1.2 k env1 env2 hag hp w (by rw [hF])
            rw [hF] at this; exact this
        | controlFlow => have := hp x _ hx; simp at this
        | _ =>
          rw [ifThenElse_run, var_run, hx] at hF
          exact Outcome.noConfusion (congrArg Prod.fst hF)
    | _ => simp [fnOk, atomOk] at h
  | forFold i lo hi body _ _ _ =>
    simp only [fnOk, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hi', hlo⟩, hhi⟩, hok⟩ := h
    intro k env1 env2 hag hp
    simp only [brkFn]
    split
    · exact brkLoop_run hN hbi hs hlo hhi hok hi' k hag hp
    · next hnb => exact plainFold_run hN hbi hlo hhi hok (by simpa using hnb) k hag hp
  | var x => exact fun k _ _ hag hp => atom_refines h k hag hp
  | lit l => exact fun k _ _ hag hp => atom_refines h k hag hp
  | unitVal => exact fun k _ _ hag hp => atom_refines h k hag hp
  | _ => simp [fnOk, atomOk] at h

end Fn

end Hax.BreakFlag

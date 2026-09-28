/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Phase.ContinueFlag
public import HaxLean.AnfLowCT

/-!
# `while true` as a loop on a flag variable

hax-lean emits a Rust loop whose state is a tuple threaded through `continue (s)` and
`break (s)` as `whileFold (lit (bool true)) body`: the state lives in program variables,
the body ends a trip normally where the source continues, and leaves the loop by
`cfBreak`. A lowering that accepts only a variable as the guard of a `whileFold`
refuses this loop. `wtFn g` replaces each such loop by
`letBind g (lit (bool true)) (whileFold (var g) body)`, and each
`whileFoldReturn (lit (bool true)) body` likewise, for a flag variable `g` the
function does not bind or read; nested loops are rewritten in the same way, and
every rewritten loop binds `g` to the same value `true`, so one flag serves every
nesting level.

**Fragment.** `wtOk g` admits `letBind` of a value, `seq`, `ifThenElse` on a variable,
a `forFold` with atomic bounds, a `whileFold` or `whileFoldReturn` on the literal `true`
or on a variable, `cfBreak` of an atom, and a value in tail position, where an atom is
a literal, `unitVal` or a variable other than `g` (`Hax.ContinueFlag.atomOk`) and a
value is an atom, an application to atoms or a tuple of atoms (`valOk`), and no
`letBind` or loop counter binds `g`. Loops nest in loop bodies.

**Agreement.** Runs of `e` and of `wtFn g e` are compared from environments agreeing
off `g` (`Hax.ContinueFlag.AgreeOff`); they end in the same outcome, in environments
agreeing off `g`, and the rewritten run keeps `g` bound to `true` when it starts so.

## Main results

* `wtFn`, `wtOk`, `valOk`: the rewriting and its fragment
* `whileLoop_wt`, `whileLoopR_wt`: a `denoteWhile'` (`denoteWhile'Return`) loop over a
  body and over its rewriting, under guards that evaluate alike, ends alike
* `wtFn_run`: the rewritten expression ends in the outcome of `e`, in an environment
  agreeing off `g`
* `wtFn_run_same`: from one environment, the outcomes of `e` and `wtFn g e` agree
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.WhileTrueFlag

open Hax.ContinueFlag (atomOk rhsOk AgreeOff extend_ne var_run lit_run letBind_run seq_run
  ifThenElse_run cfBreak_run atom_run rhs_run forLoop_ge_run forLoop_zero_run forLoop_succ_run)

/-! ## The rewriting -/

/-- A `whileFold` on the guard `c` over the rewritten body `b`: on the literal `true`,
    the loop on the flag `g` bound to `true`; on any other guard, the loop itself. -/
def wtLoop (g : String) : ImpExpr → ImpExpr → ImpExpr
  | .lit (.bool true), b => .letBind g (.lit (.bool true)) (.whileFold (.var g) b)
  | c, b => .whileFold c b

/-- A `whileFoldReturn` on the guard `c` over the rewritten body `b`: on the literal
    `true`, the loop on the flag `g` bound to `true`; on any other guard, the loop
    itself. -/
def wtLoopR (g : String) : ImpExpr → ImpExpr → ImpExpr
  | .lit (.bool true), b => .letBind g (.lit (.bool true)) (.whileFoldReturn (.var g) b)
  | c, b => .whileFoldReturn c b

/-- The expression with each `whileFold (lit (bool true)) body` and each
    `whileFoldReturn (lit (bool true)) body` replaced by the loop on the flag `g` bound to
    `true`, in every statement position and every loop body. -/
def wtFn (g : String) : ImpExpr → ImpExpr
  | .letBind n v b => .letBind n v (wtFn g b)
  | .seq a b => .seq (wtFn g a) (wtFn g b)
  | .ifThenElse c t e => .ifThenElse c (wtFn g t) (wtFn g e)
  | .forFold i lo hi b => .forFold i lo hi (wtFn g b)
  | .whileFold c b => wtLoop g c (wtFn g b)
  | .whileFoldReturn c b => wtLoopR g c (wtFn g b)
  | e => e

/-- A value of the fragment: a right-hand side of `rhsOk` (an atom or an application to
    atoms) or a tuple of atoms. -/
def valOk (g : String) : ImpExpr → Bool
  | .tuple es => es.all (atomOk g)
  | e => rhsOk g e

/-- The expressions the rewriting covers, for the flag `g`: the right-hand sides of
    `letBind` and the tail values are values of `valOk`. -/
def wtOk (g : String) : ImpExpr → Bool
  | .letBind n v b => n != g && valOk g v && wtOk g b
  | .seq a b => wtOk g a && wtOk g b
  | .ifThenElse (.var x) t e => x != g && wtOk g t && wtOk g e
  | .forFold i lo hi b => i != g && atomOk g lo && atomOk g hi && wtOk g b
  | .whileFold (.lit (.bool true)) b => wtOk g b
  | .whileFold (.var x) b => x != g && wtOk g b
  | .whileFoldReturn (.lit (.bool true)) b => wtOk g b
  | .whileFoldReturn (.var x) b => x != g && wtOk g b
  | .cfBreak e => atomOk g e
  | e => valOk g e

/-! ## The relation between runs -/

/-- The relation between a run `r1` of an expression and a run `r2` of its rewriting
    from `env2`: the same outcome, environments agreeing off `g`, and `g` bound to
    `true` at the end of `r2` when it is so in `env2`. -/
structure WtRel (g : String) (env2 : Env) (r1 r2 : Outcome × Env) : Prop where
  out : r2.1 = r1.1
  agree : AgreeOff g r1.2 r2.2
  keep : env2 g = some (.bool true) → r2.2 g = some (.bool true)

/-- The hypothesis of the rewriting of `e`, over every fuel and every pair of
    environments agreeing off `g`. -/
def WtIH (bi : Builtins) (g : String) (e : ImpExpr) : Prop :=
  ∀ fuel env1 env2, AgreeOff g env1 env2 →
    WtRel g env2 ((denote' bi fuel e).run env1) ((denote' bi fuel (wtFn g e)).run env2)

theorem WtRel.refl {g : String} {env1 env2 : Env} {o : Outcome} (hag : AgreeOff g env1 env2) :
    WtRel g env2 (o, env1) (o, env2) := ⟨rfl, hag, id⟩

section Body

variable {bi : Builtins} {g : String}

theorem atom_wtIH {a : ImpExpr} (ha : atomOk g a = true) (hw : wtFn g a = a) :
    WtIH bi g a := by
  intro fuel env1 env2 hag
  rw [hw]
  obtain ⟨h1, h2, h3⟩ := atom_run (bi := bi) (fuel := fuel) ha hag
  exact ⟨h1.symm, by rw [h2, h3]; exact hag, fun h => by rw [h3]; exact h⟩

theorem letBind_wtIH {n : String} {v b : ImpExpr} (hn : n ≠ g) (hv : rhsOk g v = true)
    (ihb : WtIH bi g b) : WtIH bi g (.letBind n v b) := by
  intro fuel env1 env2 hag
  obtain ⟨h1, h2, h3⟩ := rhs_run (bi := bi) (fuel := fuel) hv hag
  generalize ho : ((denote' bi fuel v).run env1).1 = o at h1
  have e1 : (denote' bi fuel v).run env1 = (o, env1) := Prod.ext ho h2
  have e2 : (denote' bi fuel v).run env2 = (o, env2) := Prod.ext h1.symm h3
  simp only [wtFn]
  rw [letBind_run, letBind_run, e1, e2]
  have hkeep : ∀ w, env2 g = some (.bool true) → (env2.extend n w) g = some (.bool true) :=
    fun w h => by rw [extend_ne _ (Ne.symm hn)]; exact h
  rcases o with w | _ | _ | _ | _
  · cases w with
    | controlFlow k u => exact WtRel.refl hag
    | _ =>
      all_goals
        obtain ⟨r1, r2, r3⟩ := ihb fuel _ _ (hag.extend n _)
        exact ⟨r1, r2, fun h => r3 (hkeep _ h)⟩
  all_goals exact WtRel.refl hag

/-- One step of `denote'` at a tuple. -/
theorem tupleElems_run (fuel : Nat) (es : List ImpExpr) (env : Env) :
    (denote' bi fuel (.tuple es)).run env =
      match (denoteArgs' bi fuel es).run env with
      | (some vals, e1) => (.val (.tuple vals), e1)
      | (none, e1) => (.err "non-value in tuple elements", e1) := by
  simp only [denote', StateT.run, bind, StateT.bind, pure]
  rcases (denoteArgs' bi fuel es) env with ⟨o, e1⟩
  rcases o with _ | vals <;> rfl

theorem valOk_of_rhsOk {v : ImpExpr} (h : rhsOk g v = true) : valOk g v = true := by
  cases v <;> first | exact h | simp [rhsOk, atomOk] at h

/-- A value of the fragment evaluates to the same outcome in environments agreeing off
    `g`, and leaves each environment unchanged. -/
theorem val_run {fuel : Nat} {v : ImpExpr} (hv : valOk g v = true) {env1 env2 : Env}
    (hag : AgreeOff g env1 env2) :
    ((denote' bi fuel v).run env1).1 = ((denote' bi fuel v).run env2).1 ∧
      ((denote' bi fuel v).run env1).2 = env1 ∧ ((denote' bi fuel v).run env2).2 = env2 := by
  cases v with
  | tuple es =>
    obtain ⟨h1, h2, h3⟩ :=
      Hax.ContinueFlag.args_run (bi := bi) (fuel := fuel) (by simpa [valOk] using hv) hag
    rw [tupleElems_run, tupleElems_run]
    rcases hr1 : (denoteArgs' bi fuel es).run env1 with ⟨o1, e1⟩
    rcases hr2 : (denoteArgs' bi fuel es).run env2 with ⟨o2, e2⟩
    simp only [hr1, hr2] at h1 h2 h3
    subst h1 h2 h3
    rcases o1 with _ | vals <;> exact ⟨rfl, rfl, rfl⟩
  | _ => exact rhs_run (by simpa [valOk] using hv) hag

theorem letBindV_wtIH {n : String} {v b : ImpExpr} (hn : n ≠ g) (hv : valOk g v = true)
    (ihb : WtIH bi g b) : WtIH bi g (.letBind n v b) := by
  intro fuel env1 env2 hag
  obtain ⟨h1, h2, h3⟩ := val_run (bi := bi) (fuel := fuel) hv hag
  generalize ho : ((denote' bi fuel v).run env1).1 = o at h1
  have e1 : (denote' bi fuel v).run env1 = (o, env1) := Prod.ext ho h2
  have e2 : (denote' bi fuel v).run env2 = (o, env2) := Prod.ext h1.symm h3
  simp only [wtFn]
  rw [letBind_run, letBind_run, e1, e2]
  have hkeep : ∀ w, env2 g = some (.bool true) → (env2.extend n w) g = some (.bool true) :=
    fun w h => by rw [extend_ne _ (Ne.symm hn)]; exact h
  rcases o with w | _ | _ | _ | _
  · cases w with
    | controlFlow k u => exact WtRel.refl hag
    | _ =>
      all_goals
        obtain ⟨r1, r2, r3⟩ := ihb fuel _ _ (hag.extend n _)
        exact ⟨r1, r2, fun h => r3 (hkeep _ h)⟩
  all_goals exact WtRel.refl hag

theorem val_wtIH {a : ImpExpr} (ha : valOk g a = true) (hw : wtFn g a = a) :
    WtIH bi g a := by
  intro fuel env1 env2 hag
  rw [hw]
  obtain ⟨h1, h2, h3⟩ := val_run (bi := bi) (fuel := fuel) ha hag
  exact ⟨h1.symm, by rw [h2, h3]; exact hag, fun h => by rw [h3]; exact h⟩

theorem seq_wtIH {a b : ImpExpr} (iha : WtIH bi g a) (ihb : WtIH bi g b) :
    WtIH bi g (.seq a b) := by
  intro fuel env1 env2 hag
  obtain ⟨r1, r2, r3⟩ := iha fuel env1 env2 hag
  generalize hA1 : (denote' bi fuel a).run env1 = A1 at r1 r2 r3
  generalize hA2 : (denote' bi fuel (wtFn g a)).run env2 = A2 at r1 r2 r3
  obtain ⟨o1, e1⟩ := A1
  obtain ⟨o2, e2⟩ := A2
  simp only at r1 r2 r3
  subst r1
  simp only [wtFn]
  rw [seq_run, seq_run, hA1, hA2]
  rcases o2 with v | _ | _ | _ | _
  · cases v with
    | controlFlow k w => exact ⟨rfl, r2, r3⟩
    | _ =>
      all_goals
        obtain ⟨s1, s2, s3⟩ := ihb fuel e1 e2 r2
        exact ⟨s1, s2, fun h => s3 (r3 h)⟩
  all_goals exact ⟨rfl, r2, r3⟩

theorem ifThenElse_wtIH {x : String} {t e : ImpExpr} (hx : x ≠ g) (iht : WtIH bi g t)
    (ihe : WtIH bi g e) : WtIH bi g (.ifThenElse (.var x) t e) := by
  intro fuel env1 env2 hag
  simp only [wtFn]
  rw [ifThenElse_run, ifThenElse_run, var_run, var_run, hag x hx]
  rcases env2 x with _ | v
  · exact WtRel.refl hag
  · cases v with
    | bool bv =>
      cases bv
      · exact ihe fuel env1 env2 hag
      · exact iht fuel env1 env2 hag
    | _ => exact WtRel.refl hag

theorem cfBreak_wtIH {a : ImpExpr} (ha : atomOk g a = true) : WtIH bi g (.cfBreak a) := by
  intro fuel env1 env2 hag
  obtain ⟨h1, h2, h3⟩ := atom_run (bi := bi) (fuel := fuel) ha hag
  generalize ho : ((denote' bi fuel a).run env1).1 = o at h1
  have e1 : (denote' bi fuel a).run env1 = (o, env1) := Prod.ext ho h2
  have e2 : (denote' bi fuel a).run env2 = (o, env2) := Prod.ext h1.symm h3
  simp only [wtFn]
  rw [cfBreak_run, cfBreak_run, e1, e2]
  rcases o with w | _ | _ | _ | _
  · cases w <;> exact WtRel.refl hag
  all_goals exact WtRel.refl hag

end Body

/-! ## Loops -/

section Loops

variable {bi : Builtins} {g : String}

/-- **`forFold` over the rewritten body.** `denoteForLoop'` over `wtFn g body` ends
    alike with `denoteForLoop'` over `body`. -/
theorem forLoop_wt {i : String} {body : ImpExpr} (hig : i ≠ g) (ihb : WtIH bi g body)
    (fuel : Nat) :
    ∀ (lo hi : Int) (env1 env2 : Env), AgreeOff g env1 env2 →
      WtRel g env2 ((denoteForLoop' bi fuel i lo hi body).run env1)
        ((denoteForLoop' bi fuel i lo hi (wtFn g body)).run env2) := by
  induction fuel with
  | zero =>
    intro lo hi env1 env2 hag
    by_cases h : hi ≤ lo
    · rw [forLoop_ge_run _ _ _ _ _ _ _ h, forLoop_ge_run _ _ _ _ _ _ _ h]
      exact WtRel.refl hag
    · have h' : lo < hi := Int.lt_of_not_ge h
      rw [forLoop_zero_run _ _ _ _ _ _ h', forLoop_zero_run _ _ _ _ _ _ h']
      exact WtRel.refl hag
  | succ n ih =>
    intro lo hi env1 env2 hag
    by_cases h : hi ≤ lo
    · rw [forLoop_ge_run _ _ _ _ _ _ _ h, forLoop_ge_run _ _ _ _ _ _ _ h]
      exact WtRel.refl hag
    have h' : lo < hi := Int.lt_of_not_ge h
    rw [forLoop_succ_run _ _ _ _ _ _ _ h', forLoop_succ_run _ _ _ _ _ _ _ h']
    have hk0 : env2 g = some (.bool true) →
        (env2.extend i (.int lo)) g = some (.bool true) :=
      fun hg => by rw [extend_ne _ (Ne.symm hig)]; exact hg
    obtain ⟨r1, r2, r3⟩ := ihb (n + 1) (env1.extend i (.int lo)) (env2.extend i (.int lo))
      (hag.extend i _)
    generalize (denote' bi (n + 1) body).run (env1.extend i (.int lo)) = B1 at r1 r2 r3
    generalize (denote' bi (n + 1) (wtFn g body)).run (env2.extend i (.int lo)) = B2
      at r1 r2 r3
    obtain ⟨o1, e1⟩ := B1
    obtain ⟨o2, e2⟩ := B2
    simp only at r1 r2 r3
    subst r1
    rcases o2 with v | _ | _ | _ | _
    · cases v with
      | controlFlow k w =>
        cases k with
        | true => exact ⟨rfl, r2, fun hg => r3 (hk0 hg)⟩
        | false =>
          obtain ⟨s1, s2, s3⟩ := ih (lo + 1) hi e1 e2 r2
          exact ⟨s1, s2, fun hg => s3 (r3 (hk0 hg))⟩
      | _ =>
        all_goals
          obtain ⟨s1, s2, s3⟩ := ih (lo + 1) hi e1 e2 r2
          exact ⟨s1, s2, fun hg => s3 (r3 (hk0 hg))⟩
    all_goals exact ⟨rfl, r2, fun hg => r3 (hk0 hg)⟩

/-- **The `forFold` expression over the rewritten body.** With atomic bounds, the
    `forFold` over `wtFn g body` ends alike with the `forFold` over `body`. -/
theorem forFold_wtIH {i : String} {lo hi body : ImpExpr} (hig : i ≠ g)
    (hlo : atomOk g lo = true) (hhi : atomOk g hi = true) (ihb : WtIH bi g body) :
    WtIH bi g (.forFold i lo hi body) := by
  intro fuel env1 env2 hag
  obtain ⟨l1, l2, l3⟩ := atom_run (bi := bi) (fuel := fuel) hlo hag
  obtain ⟨u1, u2, u3⟩ := atom_run (bi := bi) (fuel := fuel) hhi hag
  generalize hol : ((denote' bi fuel lo).run env1).1 = ol at l1
  generalize hoh : ((denote' bi fuel hi).run env1).1 = oh at u1
  have hl1 : (denote' bi fuel lo).run env1 = (ol, env1) := Prod.ext hol l2
  have hl2 : (denote' bi fuel lo).run env2 = (ol, env2) := Prod.ext l1.symm l3
  have hh1 : (denote' bi fuel hi).run env1 = (oh, env1) := Prod.ext hoh u2
  have hh2 : (denote' bi fuel hi).run env2 = (oh, env2) := Prod.ext u1.symm u3
  simp only [StateT.run] at hl1 hl2 hh1 hh2
  simp only [wtFn, denote', StateT.run, bind, StateT.bind, hl1, hl2]
  rcases ol with vlo | _ | _ | _ | _
  · rcases oh with vhi | _ | _ | _ | _
    all_goals
      cases vlo <;> simp only [StateT.bind, hh1, hh2]
    all_goals
      first
        | exact WtRel.refl hag
        | exact forLoop_wt hig ihb fuel _ _ _ _ hag
        | (cases vhi <;>
            first
              | exact WtRel.refl hag
              | exact forLoop_wt hig ihb fuel _ _ _ _ hag)
  all_goals exact WtRel.refl hag

theorem denoteWhile'_zero (c body : ImpExpr) (env : Env) :
    (denoteWhile' bi 0 c body).run env = (.err "out of fuel", env) := by
  rw [denoteWhile', if_pos rfl]; rfl

/-- **A `whileFold` over the rewritten body.** For guards `c1` and `c2` that end in
    the same outcome and leave the environment unchanged on environments agreeing
    off `g` and satisfying `Q` on the rewritten side, where `Q` persists across a run
    that keeps `g` bound to `true`, `denoteWhile'` over `c2` and `wtFn g body` ends
    alike with `denoteWhile'` over `c1` and `body`. -/
theorem whileLoop_wt {c1 c2 body : ImpExpr} (Q : Env → Prop)
    (hQ : ∀ e e' : Env, Q e → (e g = some (.bool true) → e' g = some (.bool true)) → Q e')
    (hc : ∀ (n : Nat) (env1 env2 : Env), AgreeOff g env1 env2 → Q env2 →
      ∃ o, (denote' bi n c1).run env1 = (o, env1) ∧ (denote' bi n c2).run env2 = (o, env2))
    (ihb : WtIH bi g body) (fuel : Nat) :
    ∀ (env1 env2 : Env), AgreeOff g env1 env2 → Q env2 →
      WtRel g env2 ((denoteWhile' bi fuel c1 body).run env1)
        ((denoteWhile' bi fuel c2 (wtFn g body)).run env2) := by
  induction fuel with
  | zero =>
    intro env1 env2 hag _
    rw [denoteWhile'_zero, denoteWhile'_zero]
    exact WtRel.refl hag
  | succ n ih =>
    intro env1 env2 hag hq
    obtain ⟨o, hc1, hc2⟩ := hc (n + 1) env1 env2 hag hq
    simp only [StateT.run] at hc1 hc2 ⊢
    rw [denoteWhile'_succ_run, denoteWhile'_succ_run, hc1, hc2]
    rcases o with v | _ | _ | _ | _
    · cases v with
      | bool bv =>
        cases bv with
        | false => exact WtRel.refl hag
        | true =>
          dsimp only
          obtain ⟨r1, r2, r3⟩ := ihb (n + 1) env1 env2 hag
          simp only [StateT.run] at r1 r2 r3
          generalize denote' bi (n + 1) body env1 = B1 at r1 r2 r3
          generalize denote' bi (n + 1) (wtFn g body) env2 = B2 at r1 r2 r3
          obtain ⟨o1, e1⟩ := B1
          obtain ⟨o2, e2⟩ := B2
          simp only at r1 r2 r3
          subst r1
          have hq2 : Q e2 := hQ env2 e2 hq r3
          rcases o2 with w | _ | _ | _ | _
          · cases w with
            | controlFlow k u =>
              cases k with
              | true => exact ⟨rfl, r2, r3⟩
              | false =>
                obtain ⟨s1, s2, s3⟩ := ih e1 e2 r2 hq2
                exact ⟨s1, s2, fun hg => s3 (r3 hg)⟩
            | _ =>
              all_goals
                obtain ⟨s1, s2, s3⟩ := ih e1 e2 r2 hq2
                exact ⟨s1, s2, fun hg => s3 (r3 hg)⟩
          all_goals exact ⟨rfl, r2, r3⟩
      | _ => exact WtRel.refl hag
    all_goals exact WtRel.refl hag

/-- **`while true` on the flag.** The rewritten `whileFold (lit (bool true)) body`, a
    loop on `g` bound to `true`, ends alike with the loop. -/
theorem whileTrue_wtIH {body : ImpExpr} (ihb : WtIH bi g body) :
    WtIH bi g (.whileFold (.lit (.bool true)) body) := by
  intro fuel env1 env2 hag
  simp only [wtFn, wtLoop]
  rw [letBind_run, lit_run]
  simp only [Value.ofLit]
  rw [denote'_whileFold, denote'_whileFold]
  have hag' : AgreeOff g env1 (env2.extend g (.bool true)) := hag.extend_right _
  have hq : (env2.extend g (.bool true)) g = some (.bool true) := Env.extend_same _ _ _
  obtain ⟨s1, s2, s3⟩ := whileLoop_wt (bi := bi) (g := g) (c1 := .lit (.bool true))
    (c2 := .var g) (fun e => e g = some (.bool true)) (fun _ _ h k => k h)
    (fun n e1 e2 _ h => ⟨.val (.bool true), lit_run _ _ _ _, by rw [var_run, h]⟩)
    ihb fuel env1 _ hag' hq
  exact ⟨s1, s2, fun _ => s3 hq⟩

/-- A `whileFold` on a variable other than `g` over the rewritten body ends alike with
    the loop. -/
theorem whileVar_wtIH {x : String} {body : ImpExpr} (hx : x ≠ g) (ihb : WtIH bi g body) :
    WtIH bi g (.whileFold (.var x) body) := by
  intro fuel env1 env2 hag
  simp only [wtFn, wtLoop]
  rw [denote'_whileFold, denote'_whileFold]
  have hxa : atomOk g (.var x) = true := by simpa [atomOk] using hx
  refine whileLoop_wt (fun _ => True) (fun _ _ _ _ => trivial) (fun n e1 e2 h _ => ?_) ihb
    fuel env1 env2 hag trivial
  obtain ⟨h1, h2, h3⟩ := atom_run (bi := bi) (fuel := n) hxa h
  exact ⟨_, Prod.ext rfl h2, Prod.ext h1.symm h3⟩

/-- `denote'` at a `whileFoldReturn` is `denoteWhile'Return`. -/
theorem denote'_whileFoldReturn_eq (fuel : Nat) (c body : ImpExpr) :
    denote' bi fuel (.whileFoldReturn c body) = denoteWhile'Return bi fuel c body := by
  conv => lhs; unfold denote'

theorem denoteWhile'Return_zero (c body : ImpExpr) (env : Env) :
    (denoteWhile'Return bi 0 c body).run env = (.err "out of fuel", env) := by
  rw [denoteWhile'Return, if_pos rfl]; rfl

/-- One trip of `denoteWhile'Return` at positive fuel. -/
theorem denoteWhile'Return_succ (n : Nat) (cond body : ImpExpr) (env : Env) :
    denoteWhile'Return bi (n + 1) cond body env =
      match denote' bi (n + 1) cond env with
      | (.val (.controlFlow isBreak v), env') => (.val (.controlFlow isBreak v), env')
      | (.val (.bool true), env') =>
          match denote' bi (n + 1) body env' with
          | (.val (.controlFlow true (.controlFlow false v)), env'') => (.val v, env'')
          | (.val (.controlFlow true v), env'') => (.val (.controlFlow true v), env'')
          | (.val (.controlFlow false _), env'') => denoteWhile'Return bi n cond body env''
          | (.val _, env'') => denoteWhile'Return bi n cond body env''
          | (other, env'') => (other, env'')
      | (.val (.bool false), env') => (.val .unit, env')
      | (.val _, env') => (.err "while condition not a bool", env')
      | (other, env') => (other, env') := by
  have hfuel : ¬(n + 1 = 0) := by omega
  conv => lhs; unfold denoteWhile'Return
  rw [if_neg hfuel]
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  simp only [show n + 1 - 1 = n from rfl]
  generalize denote' bi (n + 1) cond env = p
  obtain ⟨rc, env'⟩ := p
  cases rc <;> try rfl
  rename_i w; cases w <;> try rfl
  rename_i b; cases b <;> try rfl
  dsimp only [bind, Bind.bind, StateT.bind, pure, Pure.pure, StateT.pure, Id.run]
  generalize denote' bi (n + 1) body env' = q
  obtain ⟨rb, env''⟩ := q
  cases rb <;> try rfl
  rename_i w; cases w <;> try rfl
  rename_i b u; cases b <;> try rfl
  cases u <;> try rfl
  rename_i b' _; cases b' <;> rfl

/-- **A `whileFoldReturn` over the rewritten body.** The statement of `whileLoop_wt` for
    `denoteWhile'Return`. -/
theorem whileLoopR_wt {c1 c2 body : ImpExpr} (Q : Env → Prop)
    (hQ : ∀ e e' : Env, Q e → (e g = some (.bool true) → e' g = some (.bool true)) → Q e')
    (hc : ∀ (n : Nat) (env1 env2 : Env), AgreeOff g env1 env2 → Q env2 →
      ∃ o, (denote' bi n c1).run env1 = (o, env1) ∧ (denote' bi n c2).run env2 = (o, env2))
    (ihb : WtIH bi g body) (fuel : Nat) :
    ∀ (env1 env2 : Env), AgreeOff g env1 env2 → Q env2 →
      WtRel g env2 ((denoteWhile'Return bi fuel c1 body).run env1)
        ((denoteWhile'Return bi fuel c2 (wtFn g body)).run env2) := by
  induction fuel with
  | zero =>
    intro env1 env2 hag _
    rw [denoteWhile'Return_zero, denoteWhile'Return_zero]
    exact WtRel.refl hag
  | succ n ih =>
    intro env1 env2 hag hq
    obtain ⟨o, hc1, hc2⟩ := hc (n + 1) env1 env2 hag hq
    simp only [StateT.run] at hc1 hc2 ⊢
    rw [denoteWhile'Return_succ, denoteWhile'Return_succ, hc1, hc2]
    rcases o with v | _ | _ | _ | _
    · cases v with
      | bool bv =>
        cases bv with
        | false => exact WtRel.refl hag
        | true =>
          dsimp only
          obtain ⟨r1, r2, r3⟩ := ihb (n + 1) env1 env2 hag
          simp only [StateT.run] at r1 r2 r3
          generalize denote' bi (n + 1) body env1 = B1 at r1 r2 r3
          generalize denote' bi (n + 1) (wtFn g body) env2 = B2 at r1 r2 r3
          obtain ⟨o1, e1⟩ := B1
          obtain ⟨o2, e2⟩ := B2
          simp only at r1 r2 r3
          subst r1
          have hq2 : Q e2 := hQ env2 e2 hq r3
          rcases o2 with w | _ | _ | _ | _
          · cases w with
            | controlFlow k u =>
              cases k with
              | true =>
                cases u with
                | controlFlow k' u' =>
                  cases k' with
                  | false => exact ⟨rfl, r2, r3⟩
                  | true => exact ⟨rfl, r2, r3⟩
                | _ => exact ⟨rfl, r2, r3⟩
              | false =>
                obtain ⟨s1, s2, s3⟩ := ih e1 e2 r2 hq2
                exact ⟨s1, s2, fun hg => s3 (r3 hg)⟩
            | _ =>
              all_goals
                obtain ⟨s1, s2, s3⟩ := ih e1 e2 r2 hq2
                exact ⟨s1, s2, fun hg => s3 (r3 hg)⟩
          all_goals exact ⟨rfl, r2, r3⟩
      | _ => exact WtRel.refl hag
    all_goals exact WtRel.refl hag

/-- **`while true` with early return on the flag.** The rewritten
    `whileFoldReturn (lit (bool true)) body` ends alike with the loop. -/
theorem whileTrueR_wtIH {body : ImpExpr} (ihb : WtIH bi g body) :
    WtIH bi g (.whileFoldReturn (.lit (.bool true)) body) := by
  intro fuel env1 env2 hag
  simp only [wtFn, wtLoopR]
  rw [letBind_run, lit_run]
  simp only [Value.ofLit]
  rw [denote'_whileFoldReturn_eq, denote'_whileFoldReturn_eq]
  have hag' : AgreeOff g env1 (env2.extend g (.bool true)) := hag.extend_right _
  have hq : (env2.extend g (.bool true)) g = some (.bool true) := Env.extend_same _ _ _
  obtain ⟨s1, s2, s3⟩ := whileLoopR_wt (bi := bi) (g := g) (c1 := .lit (.bool true))
    (c2 := .var g) (fun e => e g = some (.bool true)) (fun _ _ h k => k h)
    (fun n e1 e2 _ h => ⟨.val (.bool true), lit_run _ _ _ _, by rw [var_run, h]⟩)
    ihb fuel env1 _ hag' hq
  exact ⟨s1, s2, fun _ => s3 hq⟩

/-- A `whileFoldReturn` on a variable other than `g` over the rewritten body ends alike
    with the loop. -/
theorem whileVarR_wtIH {x : String} {body : ImpExpr} (hx : x ≠ g) (ihb : WtIH bi g body) :
    WtIH bi g (.whileFoldReturn (.var x) body) := by
  intro fuel env1 env2 hag
  simp only [wtFn, wtLoopR]
  rw [denote'_whileFoldReturn_eq, denote'_whileFoldReturn_eq]
  have hxa : atomOk g (.var x) = true := by simpa [atomOk] using hx
  refine whileLoopR_wt (fun _ => True) (fun _ _ _ _ => trivial) (fun n e1 e2 h _ => ?_) ihb
    fuel env1 env2 hag trivial
  obtain ⟨h1, h2, h3⟩ := atom_run (bi := bi) (fuel := n) hxa h
  exact ⟨_, Prod.ext rfl h2, Prod.ext h1.symm h3⟩

end Loops

/-! ## The rewritten expression -/

section Fn

variable {bi : Builtins} {g : String}

/-- **The rewritten expression.** For an expression of `wtOk g`, from environments
    agreeing off `g`, the rewritten expression ends in the outcome of the expression,
    in an environment agreeing off `g`. -/
theorem wtFn_run (e : ImpExpr) (h : wtOk g e = true) : WtIH bi g e := by
  induction e using ImpExpr.ind with
  | letBind n v b _ ihb =>
    simp only [wtOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact letBindV_wtIH h.1.1 h.1.2 (ihb h.2)
  | seq a b iha ihb =>
    simp only [wtOk, Bool.and_eq_true] at h
    exact seq_wtIH (iha h.1) (ihb h.2)
  | ifThenElse cnd t e _ iht ihe =>
    cases cnd with
    | var x =>
      simp only [wtOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact ifThenElse_wtIH h.1.1 (iht h.1.2) (ihe h.2)
    | _ => simp [wtOk, valOk, rhsOk, atomOk] at h
  | forFold i lo hi b _ _ ihb =>
    simp only [wtOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact forFold_wtIH h.1.1.1 h.1.1.2 h.1.2 (ihb h.2)
  | whileFold c b _ ihb =>
    cases c with
    | lit l =>
      cases l with
      | bool bv =>
        cases bv with
        | true => exact whileTrue_wtIH (ihb (by simpa [wtOk] using h))
        | false => simp [wtOk, valOk, rhsOk, atomOk] at h
      | _ => simp [wtOk, valOk, rhsOk, atomOk] at h
    | var x =>
      simp only [wtOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact whileVar_wtIH h.1 (ihb h.2)
    | _ => simp [wtOk, valOk, rhsOk, atomOk] at h
  | whileFoldReturn c b _ ihb =>
    cases c with
    | lit l =>
      cases l with
      | bool bv =>
        cases bv with
        | true => exact whileTrueR_wtIH (ihb (by simpa [wtOk] using h))
        | false => simp [wtOk, valOk, rhsOk, atomOk] at h
      | _ => simp [wtOk, valOk, rhsOk, atomOk] at h
    | var x =>
      simp only [wtOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact whileVarR_wtIH h.1 (ihb h.2)
    | _ => simp [wtOk, valOk, rhsOk, atomOk] at h
  | cfBreak a _ => exact cfBreak_wtIH (by simpa [wtOk] using h)
  | var x => exact val_wtIH (by simpa [wtOk] using h) rfl
  | lit l => exact val_wtIH (by simpa [wtOk] using h) rfl
  | unitVal => exact val_wtIH (by simpa [wtOk] using h) rfl
  | app f args _ => exact val_wtIH (by simpa [wtOk] using h) rfl
  | tuple es _ => exact val_wtIH (by simpa [wtOk] using h) rfl
  | _ => simp [wtOk, valOk, rhsOk, atomOk] at h

/-- **The rewritten expression from one environment.** A run of an expression of
    `wtOk g` and the run of `wtFn g` of it from the same environment end in the same
    outcome. -/
theorem wtFn_run_same {e : ImpExpr} (h : wtOk g e = true) (fuel : Nat) (env : Env) :
    ((denote' bi fuel (wtFn g e)).run env).1 = ((denote' bi fuel e).run env).1 :=
  (wtFn_run e h fuel env env (fun _ _ => rfl)).out

end Fn

end Hax.WhileTrueFlag

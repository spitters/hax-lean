/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Phase.ContinueFlag
public import HaxLean.Phase.ExplicitMonadicCF

/-!
# A stepped range as a counted loop

The adapter reads `for j in iter { body }` over an iterator `iter` that is neither a
range nor `.iter()` of a collection as a counted loop over the positions of `iter`:
`forFold v 0 (len iter) (let j := index iter v; body)`. For `iter` the stepped range
`(a..b).step_by(s)` with integer literals `a`, `b` and `s > 0` (`stepSrc`), the loop
reads the builtins `Range`, `step_by`, `len` and `index`, which the lowering to `LowCT`
does not accept. `stepTgt` is the counted loop over `0..stepCount a b s` binding `j`
to `a + v * s` by one `mul` and one `add` of atoms.

**Specification.** `Spec bi N` states that the table `bi` gives the stepped range its
Rust meaning: the iterator has `stepCount a b s` elements, element `k` being
`a + k * s`, and `add` and `mul` compute on integers. `refTable` meets it.

## Main results

* `stepTgt_run`: the loop `stepTgt` ends in the outcome and environment of the loop
  `stepSrc`, for every fuel and environment
* `stepVTgt_run`: for bounds that are integer literals or variables, the counted loop
  `stepVTgt` over `0..(hi - lo + (s - 1)) / s`, computed at run time, binding `j` to
  `lo + v * s`, ends as the loop `stepVSrc`, when the body keeps the variables the
  bounds read (`keeps`, `keeps_frame`)
* `stepFn_run`: `stepFn N`, which rewrites every recognized loop under `letBind`,
  `seq`, `ifThenElse` and inside loop bodies, preserves the outcome and environment of
  every expression under a table meeting `VSpec`
* `refTable_spec`, `refTableV_vspec`: tables materializing `Range` and `step_by` as
  arrays meet `Spec` and `VSpec`
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.IterStepBy

open Hax.ContinueFlag (app_run lit_run var_run letBind_run unitVal_run seq_run ifThenElse_run
  args_cons_run args_nil_run cfBreak_run cfContinue_run extend_ne
  forLoop_ge_run forLoop_zero_run forLoop_succ_run
  forLoopRet_ge_run forLoopRet_zero_run forLoopRet_succ_run)

/-- The builtin names a stepped-range loop uses. -/
structure Names where
  range : String := "Range"
  stepBy : String := "step_by"
  len : String := "len"
  index : String := "index"
  add : String := "add"
  mul : String := "mul"
  sub : String := "sub"
  div : String := "div"

/-- The number of elements of `(a..b).step_by(s)`. -/
def stepCount (a b s : Int) : Nat := ((b - a).toNat + s.toNat - 1) / s.toNat

/-- The iterator `(a..b).step_by(s)`. -/
def stepIter (N : Names) (a b s : Int) : ImpExpr :=
  .app N.stepBy [.app N.range [.lit (.int a), .lit (.int b)], .lit (.int s)]

/-- `for j in (a..b).step_by(s) { body }` as a counted loop over the positions `v` of the
    iterator, reading element `v` of the iterator into `j`. -/
def stepSrc (N : Names) (v j : String) (a b s : Int) (body : ImpExpr) : ImpExpr :=
  .forFold v (.lit (.int 0)) (.app N.len [stepIter N a b s])
    (.letBind j (.app N.index [stepIter N a b s, .var v]) body)

/-- The counted loop over `0..stepCount a b s` binding `j` to `a + v * s`. -/
def stepTgt (N : Names) (v j : String) (a b s : Int) (body : ImpExpr) : ImpExpr :=
  .forFold v (.lit (.int 0)) (.lit (.int (stepCount a b s)))
    (.letBind j (.app N.mul [.var v, .lit (.int s)])
      (.letBind j (.app N.add [.lit (.int a), .var j]) body))

/-- A builtin table giving the stepped range its Rust meaning: the iterator of
    `(a..b).step_by(s)` has `stepCount a b s` elements, element `k` being `a + k * s`,
    and `add` and `mul` compute on integers. -/
structure Spec (bi : Builtins) (N : Names) : Prop where
  iter : ∀ a b s : Int, 0 < s → ∃ rv itv : Value,
    bi N.range [.int a, .int b] = some rv ∧ rv.isControlFlow = false ∧
    bi N.stepBy [rv, .int s] = some itv ∧ itv.isControlFlow = false ∧
    (bi N.len [itv] = some (.int (stepCount a b s)) ∨
      ∃ w, bi N.len [itv] = some (.uint w (stepCount a b s))) ∧
    ∀ k : Nat, k < stepCount a b s → bi N.index [itv, .int k] = some (.int (a + k * s))
  add : ∀ x y : Int, bi N.add [.int x, .int y] = some (.int (x + y))
  mul : ∀ x y : Int, bi N.mul [.int x, .int y] = some (.int (x * y))

section Runs

variable {bi : Builtins} {fuel : Nat}

theorem app1_run {f : String} {x : ImpExpr} {vx r : Value} {env : Env}
    (hx : (denote' bi fuel x).run env = (.val vx, env)) (hcx : vx.isControlFlow = false)
    (hf : bi f [vx] = some r) :
    (denote' bi fuel (.app f [x])).run env = (.val r, env) := by
  rw [app_run, args_cons_run, hx]
  cases vx <;> simp_all [Value.isControlFlow, args_nil_run]

theorem app2_run {f : String} {x y : ImpExpr} {vx vy r : Value} {env : Env}
    (hx : (denote' bi fuel x).run env = (.val vx, env)) (hcx : vx.isControlFlow = false)
    (hy : (denote' bi fuel y).run env = (.val vy, env)) (hcy : vy.isControlFlow = false)
    (hf : bi f [vx, vy] = some r) :
    (denote' bi fuel (.app f [x, y])).run env = (.val r, env) := by
  rw [app_run, args_cons_run, hx]
  cases vx <;> simp_all [Value.isControlFlow, args_cons_run, args_nil_run] <;>
    cases vy <;> simp_all

theorem forFold_run_int {v : String} {lo hi body : ImpExpr} {l h : Int} {env : Env}
    (hl : (denote' bi fuel lo).run env = (.val (.int l), env))
    (hh : (denote' bi fuel hi).run env = (.val (.int h), env)) :
    (denote' bi fuel (.forFold v lo hi body)).run env =
      (denoteForLoop' bi fuel v l h body).run env := by
  simp only [StateT.run] at hl hh
  simp only [denote', StateT.run, bind, StateT.bind, hl, hh]

theorem forFold_run_uint {v : String} {lo hi body : ImpExpr} {l : Int} {w : IntWidth}
    {h : Nat} {env : Env}
    (hl : (denote' bi fuel lo).run env = (.val (.int l), env))
    (hh : (denote' bi fuel hi).run env = (.val (.uint w h), env)) :
    (denote' bi fuel (.forFold v lo hi body)).run env =
      (denoteForLoop' bi fuel v l h body).run env := by
  simp only [StateT.run] at hl hh
  simp only [denote', StateT.run, bind, StateT.bind, hl, hh]

theorem extend_extend_same (env : Env) (n : String) (x y : Value) :
    (env.extend n x).extend n y = env.extend n y := by
  funext z
  simp only [Env.extend]
  split <;> rfl

end Runs

section Loop

variable {bi : Builtins}

/-- Two loop bodies agreeing on every trip whose counter lies in `[0, hi)` give the
    same loop from a nonnegative start. -/
theorem loop_congr_range {v : String} {hi : Int} {b1 b2 : ImpExpr}
    (h : ∀ fuel (env : Env) (k : Int), 0 ≤ k → k < hi →
      (denote' bi fuel b1).run (env.extend v (.int k)) =
        (denote' bi fuel b2).run (env.extend v (.int k))) :
    ∀ fuel (lo : Int) env, 0 ≤ lo →
      (denoteForLoop' bi fuel v lo hi b1).run env =
        (denoteForLoop' bi fuel v lo hi b2).run env := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo env _
    by_cases hl : hi ≤ lo
    · rw [forLoop_ge_run bi _ _ _ _ _ _ hl, forLoop_ge_run bi _ _ _ _ _ _ hl]
    · rw [forLoop_zero_run bi _ _ _ _ _ (by omega), forLoop_zero_run bi _ _ _ _ _ (by omega)]
  | succ n ih =>
    intro lo env hlo
    by_cases hl : hi ≤ lo
    · rw [forLoop_ge_run bi _ _ _ _ _ _ hl, forLoop_ge_run bi _ _ _ _ _ _ hl]
    · rw [forLoop_succ_run bi _ _ _ _ _ _ (by omega), forLoop_succ_run bi _ _ _ _ _ _ (by omega),
        h (n + 1) env lo hlo (by omega)]
      rcases (denote' bi (n + 1) b2).run (env.extend v (.int lo)) with ⟨o, e2⟩
      rcases o with w | _ | _ | _ | _ <;> try rfl
      cases w with
      | controlFlow k _ => cases k
                           · exact ih (lo + 1) e2 (by omega)
                           · rfl
      | _ => exact ih (lo + 1) e2 (by omega)

end Loop

section Node

variable {bi : Builtins} {N : Names}

/-- **A stepped-range loop.** The counted loop `stepTgt` ends as the loop `stepSrc`
    over the positions of the iterator `(a..b).step_by(s)`, for every fuel and
    environment. -/
theorem stepTgt_run (hN : Spec bi N) {v j : String} {a b s : Int} (hs : 0 < s)
    (body : ImpExpr) (fuel : Nat) (env : Env) :
    (denote' bi fuel (stepTgt N v j a b s body)).run env =
      (denote' bi fuel (stepSrc N v j a b s body)).run env := by
  obtain ⟨rv, itv, hr, hrc, hst, hitc, hlen, hidx⟩ := hN.iter a b s hs
  have hit : ∀ fuel env, (denote' bi fuel (stepIter N a b s)).run env = (.val itv, env) := by
    intro fuel env
    exact app2_run (app2_run (lit_run bi fuel _ env) rfl (lit_run bi fuel _ env) rfl hr) hrc
      (lit_run bi fuel _ env) rfl hst
  have hbody : ∀ fuel (env : Env) (k : Int), 0 ≤ k → k < (stepCount a b s : Int) →
      (denote' bi fuel (.letBind j (.app N.mul [.var v, .lit (.int s)])
          (.letBind j (.app N.add [.lit (.int a), .var j]) body))).run
          (env.extend v (.int k)) =
        (denote' bi fuel (.letBind j (.app N.index [stepIter N a b s, .var v]) body)).run
          (env.extend v (.int k)) := by
    intro fuel env k hk0 hkn
    have hv : ∀ e : Env, (denote' bi fuel (.var v)).run (e.extend v (.int k)) =
        (.val (.int k), e.extend v (.int k)) := by
      intro e; rw [var_run, Env.extend_same]
    rw [letBind_run, letBind_run,
      app2_run (hv env) rfl (lit_run bi fuel _ _) rfl (hN.mul k s),
      app2_run (hit _ _) hitc (hv env) rfl (by
        have := hidx k.toNat (by omega)
        rwa [Int.toNat_of_nonneg hk0] at this)]
    simp only
    rw [letBind_run, app2_run (lit_run bi fuel _ _) rfl (by rw [var_run, Env.extend_same]) rfl
      (hN.add a (k * s))]
    simp only [extend_extend_same]
  rw [stepTgt, stepSrc, forFold_run_int (lit_run bi fuel _ env) (lit_run bi fuel _ env)]
  rcases hlen with hl | ⟨w, hl⟩
  · rw [forFold_run_int (lit_run bi fuel _ env) (app1_run (hit fuel env) hitc hl)]
    exact loop_congr_range hbody fuel 0 env (Int.le_refl 0)
  · rw [forFold_run_uint (lit_run bi fuel _ env) (app1_run (hit fuel env) hitc hl)]
    exact loop_congr_range hbody fuel 0 env (Int.le_refl 0)

end Node

/-! ## Variables a loop body leaves unchanged -/

/-- A syntactic check that `e` leaves the variable `x` unchanged: `e` is built from
    literals, variables, `()`, `let` and assignments of names other than `x`, calls,
    `if`, `;`, `cfBreak`, `cfContinue`, and `forFold`/`forFoldReturn` loops whose
    counter is not `x`. -/
def keeps (x : String) : ImpExpr → Bool
  | .lit _ | .var _ | .unitVal => true
  | .letBind n v b => n != x && keeps x v && keeps x b
  | .app _ args => keepsArgs x args
  | .ifThenElse c t e => keeps x c && keeps x t && keeps x e
  | .seq a b => keeps x a && keeps x b
  | .cfBreak e | .cfContinue e => keeps x e
  | .forFold v lo hi b | .forFoldReturn v lo hi b =>
    v != x && keeps x lo && keeps x hi && keeps x b
  | _ => false
where
  /-- `keeps` of every argument. -/
  keepsArgs (x : String) : List ImpExpr → Bool
    | [] => true
    | a :: as => keeps x a && keepsArgs x as

section Frame

variable {bi : Builtins}

/-- The statement that a run of `e` from any environment leaves `x` unchanged. -/
def Frame (bi : Builtins) (x : String) (e : ImpExpr) : Prop :=
  ∀ fuel env, ((denote' bi fuel e).run env).2 x = env x

theorem args_frame {x : String} {args : List ImpExpr} (h : ∀ a ∈ args, Frame bi x a) :
    ∀ fuel env, ((denoteArgs' bi fuel args).run env).2 x = env x := by
  induction args with
  | nil => intro fuel env; rw [args_nil_run]
  | cons a as ih =>
    intro fuel env
    have ha := h a (by simp) fuel env
    have ih' := ih (fun b hb => h b (by simp [hb]))
    rw [args_cons_run]
    rcases hr : (denote' bi fuel a).run env with ⟨o, e1⟩
    rw [hr] at ha
    simp only at ha
    rcases o with v | _ | _ | _ | _ <;> try exact ha
    cases v <;> first | exact ha | (simp only; rw [ih' fuel e1]; exact ha)

theorem loop_frame {x i : String} {body : ImpExpr} (hi : i ≠ x) (hb : Frame bi x body) :
    ∀ fuel lo hi env, ((denoteForLoop' bi fuel i lo hi body).run env).2 x = env x := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo h env
    by_cases hl : h ≤ lo
    · rw [forLoop_ge_run bi _ _ _ _ _ _ hl]
    · rw [forLoop_zero_run bi _ _ _ _ _ (by omega)]
  | succ n ih =>
    intro lo h env
    by_cases hl : h ≤ lo
    · rw [forLoop_ge_run bi _ _ _ _ _ _ hl]
    · rw [forLoop_succ_run bi _ _ _ _ _ _ (by omega)]
      have hb' := hb (n + 1) (env.extend i (.int lo))
      rw [extend_ne _ (Ne.symm hi)] at hb'
      rcases hr : (denote' bi (n + 1) body).run (env.extend i (.int lo)) with ⟨o, e2⟩
      rw [hr] at hb'
      simp only at hb'
      rcases o with v | _ | _ | _ | _ <;> try exact hb'
      cases v with
      | controlFlow k w => cases k <;> first | exact hb' | (simp only; rw [ih]; exact hb')
      | _ => simp only; rw [ih]; exact hb'

theorem loopRet_frame {x i : String} {body : ImpExpr} (hi : i ≠ x) (hb : Frame bi x body) :
    ∀ fuel lo hi env, ((denoteForLoop'Return bi fuel i lo hi body).run env).2 x = env x := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo h env
    by_cases hl : h ≤ lo
    · rw [forLoopRet_ge_run bi _ _ _ _ _ _ hl]
    · rw [forLoopRet_zero_run bi _ _ _ _ _ (by omega)]
  | succ n ih =>
    intro lo h env
    by_cases hl : h ≤ lo
    · rw [forLoopRet_ge_run bi _ _ _ _ _ _ hl]
    · rw [forLoopRet_succ_run bi _ _ _ _ _ _ (by omega)]
      have hb' := hb (n + 1) (env.extend i (.int lo))
      rw [extend_ne _ (Ne.symm hi)] at hb'
      rcases hr : (denote' bi (n + 1) body).run (env.extend i (.int lo)) with ⟨o, e2⟩
      rw [hr] at hb'
      simp only at hb'
      rcases o with v | _ | _ | _ | _ <;> try exact hb'
      cases v with
      | controlFlow k w =>
        cases k
        · simp only; rw [ih]; exact hb'
        · cases w with
          | controlFlow k' w' => cases k' <;> exact hb'
          | _ => exact hb'
      | _ => simp only; rw [ih]; exact hb'

theorem forFold_frame {x v : String} {lo hi b : ImpExpr} (hv : v ≠ x)
    (hlo : Frame bi x lo) (hhi : Frame bi x hi) (hb : Frame bi x b) :
    Frame bi x (.forFold v lo hi b) := by
  intro fuel env
  have hL := loop_frame hv hb fuel
  have hl := hlo fuel env
  simp only [StateT.run] at hl hL ⊢
  simp only [denote', bind, StateT.bind]
  rcases h1 : denote' bi fuel lo env with ⟨o1, e1⟩
  rw [h1] at hl
  have hh : ((denote' bi fuel hi) e1).2 x = e1 x := hhi fuel e1
  rcases h2 : denote' bi fuel hi e1 with ⟨o2, e2⟩
  rw [h2] at hh
  simp only at hh hl
  rcases o1 with v1 | _ | _ | _ | _ <;> try exact hl
  cases v1 <;> try exact hl
  all_goals
    simp only [StateT.bind, h2, pure]
    rcases o2 with v2 | _ | _ | _ | _
    all_goals first
      | (simp only [bind, pure, StateT.pure]; rw [hh, hl]; done)
      | (cases v2 <;> simp only [bind, pure, StateT.pure] <;>
          first | (rw [hh, hl]) | (rw [hL, hh, hl]))

theorem forFoldReturn_frame {x v : String} {lo hi b : ImpExpr} (hv : v ≠ x)
    (hlo : Frame bi x lo) (hhi : Frame bi x hi) (hb : Frame bi x b) :
    Frame bi x (.forFoldReturn v lo hi b) := by
  intro fuel env
  have hL := loopRet_frame hv hb fuel
  have hl := hlo fuel env
  simp only [StateT.run] at hl hL ⊢
  simp only [denote', bind, StateT.bind]
  rcases h1 : denote' bi fuel lo env with ⟨o1, e1⟩
  rw [h1] at hl
  have hh : ((denote' bi fuel hi) e1).2 x = e1 x := hhi fuel e1
  rcases h2 : denote' bi fuel hi e1 with ⟨o2, e2⟩
  rw [h2] at hh
  simp only at hh hl
  rcases o1 with v1 | _ | _ | _ | _ <;> try exact hl
  cases v1 <;> try exact hl
  all_goals
    simp only [StateT.bind, h2, pure]
    rcases o2 with v2 | _ | _ | _ | _
    all_goals first
      | (simp only [bind, pure, StateT.pure]; rw [hh, hl]; done)
      | (cases v2 <;> simp only [bind, pure, StateT.pure] <;>
          first | (rw [hh, hl]) | (rw [hL, hh, hl]))

theorem keepsArgs_mem {x : String} {args : List ImpExpr} (h : keeps.keepsArgs x args = true) :
    ∀ a ∈ args, keeps x a = true := by
  induction args with
  | nil => simp
  | cons a as ih =>
    simp only [keeps.keepsArgs, Bool.and_eq_true] at h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h.1
    · exact ih h.2 b hb

/-- **A body that keeps `x`.** A run of an expression passing `keeps x` leaves `x`
    unchanged, for every fuel and environment. -/
theorem keeps_frame {x : String} (e : ImpExpr) (h : keeps x e = true) : Frame bi x e := by
  induction e using ImpExpr.ind with
  | lit l => intro fuel env; rw [lit_run]
  | var n =>
    intro fuel env; rw [var_run]
    cases env n <;> rfl
  | unitVal => intro fuel env; rw [unitVal_run]
  | letBind n v b ihv ihb =>
    simp only [keeps, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hn, hv⟩, hb⟩ := h
    intro fuel env
    have h1 := ihv hv fuel env
    rw [letBind_run]
    rcases hr : (denote' bi fuel v).run env with ⟨o, e1⟩
    rw [hr] at h1
    simp only at h1
    rcases o with w | _ | _ | _ | _ <;> try exact h1
    cases w <;> first
      | exact h1
      | (simp only; rw [ihb hb, extend_ne _ (Ne.symm hn)]; exact h1)
  | app f args ih =>
    simp only [keeps] at h
    intro fuel env
    have ha := args_frame (bi := bi) (fun a ha => ih a ha (keepsArgs_mem h a ha)) fuel env
    rw [app_run]
    rcases hr : (denoteArgs' bi fuel args).run env with ⟨o, e1⟩
    rw [hr] at ha
    simp only at ha
    rcases o with _ | vals
    · exact ha
    · simp only
      cases bi f vals <;> exact ha
  | ifThenElse c t e ihc iht ihe =>
    simp only [keeps, Bool.and_eq_true] at h
    obtain ⟨⟨hc, ht⟩, he⟩ := h
    intro fuel env
    have h1 := ihc hc fuel env
    rw [ifThenElse_run]
    rcases hr : (denote' bi fuel c).run env with ⟨o, e1⟩
    rw [hr] at h1
    simp only at h1
    rcases o with w | _ | _ | _ | _ <;> try exact h1
    cases w with
    | bool b =>
      cases b
      · simp only; rw [ihe he]; exact h1
      · simp only; rw [iht ht]; exact h1
    | _ => exact h1
  | seq a b iha ihb =>
    simp only [keeps, Bool.and_eq_true] at h
    intro fuel env
    have h1 := iha h.1 fuel env
    rw [seq_run]
    rcases hr : (denote' bi fuel a).run env with ⟨o, e1⟩
    rw [hr] at h1
    simp only at h1
    rcases o with w | _ | _ | _ | _ <;> try exact h1
    cases w <;> first | exact h1 | (simp only; rw [ihb h.2]; exact h1)
  | cfBreak e ih =>
    simp only [keeps] at h
    intro fuel env
    have h1 := ih h fuel env
    rw [cfBreak_run]
    rcases hr : (denote' bi fuel e).run env with ⟨o, e1⟩
    rw [hr] at h1
    simp only at h1
    rcases o with w | _ | _ | _ | _ <;> try exact h1
    cases w <;> exact h1
  | cfContinue e ih =>
    simp only [keeps] at h
    intro fuel env
    have h1 := ih h fuel env
    rw [cfContinue_run]
    rcases hr : (denote' bi fuel e).run env with ⟨o, e1⟩
    rw [hr] at h1
    simp only at h1
    rcases o with w | _ | _ | _ | _ <;> try exact h1
    cases w <;> exact h1
  | forFold v lo hi b ihlo ihhi ihb =>
    simp only [keeps, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨hv, hlo⟩, hhi⟩, hb⟩ := h
    exact forFold_frame hv (ihlo hlo) (ihhi hhi) (ihb hb)
  | forFoldReturn v lo hi b ihlo ihhi ihb =>
    simp only [keeps, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨hv, hlo⟩, hhi⟩, hb⟩ := h
    exact forFoldReturn_frame hv (ihlo hlo) (ihhi hhi) (ihb hb)
  | _ => simp [keeps] at h

end Frame

/-! ## Stepped ranges with variable bounds -/

/-- The integer a value denotes: an integer, or an unsigned word read as an integer. -/
def numOf : Value → Option Int
  | .int i => some i
  | .uint _ n => some n
  | _ => none

theorem numOf_not_cf {w : Value} {a : Int} (h : numOf w = some a) : w.isControlFlow = false := by
  cases w <;> simp_all [numOf, Value.isControlFlow]

/-- A bound the variable-bound rewrite accepts: an integer literal or a variable. -/
def boundOk : ImpExpr → Bool
  | .lit (.int _) | .var _ => true
  | _ => false

/-- The variables a bound reads. -/
def boundVars : ImpExpr → List String
  | .var n => [n]
  | _ => []

/-- The value of a bound in `env`. -/
def boundVal (env : Env) : ImpExpr → Option Value
  | .lit l => some (Value.ofLit l)
  | .var n => env n
  | _ => none

/-- Equality of two bounds, decided on literals and variables. -/
def boundEq : ImpExpr → ImpExpr → Bool
  | .lit (.int x), .lit (.int y) => x == y
  | .var n, .var m => n == m
  | _, _ => false

theorem boundEq_eq {a b : ImpExpr} (h : boundEq a b = true) : a = b := by
  unfold boundEq at h
  split at h <;> simp_all

theorem keeps_bound {n : String} {t : ImpExpr} (h : boundOk t = true) : keeps n t = true := by
  unfold boundOk at h
  split at h <;> first | rfl | simp at h

theorem boundVal_frame {t : ImpExpr} {e e' : Env} (h : ∀ n ∈ boundVars t, e' n = e n) :
    boundVal e' t = boundVal e t := by
  cases t <;> simp_all [boundVal, boundVars]

/-- The iterator `(lo..hi).step_by(s)` over bounds `lo`, `hi`. -/
def stepIterV (N : Names) (lo hi : ImpExpr) (s : Int) : ImpExpr :=
  .app N.stepBy [.app N.range [lo, hi], .lit (.int s)]

/-- `for j in (lo..hi).step_by(s) { body }` as a counted loop over the positions `v` of
    the iterator, reading element `v` of the iterator into `j`. -/
def stepVSrc (N : Names) (v j : String) (lo hi : ImpExpr) (s : Int) (body : ImpExpr) :
    ImpExpr :=
  .forFold v (.lit (.int 0)) (.app N.len [stepIterV N lo hi s])
    (.letBind j (.app N.index [stepIterV N lo hi s, .var v]) body)

/-- The number of elements of `(lo..hi).step_by(s)`, `(hi - lo + (s - 1)) / s`, computed
    at run time. It is nonpositive when the range is empty. -/
def stepCountE (N : Names) (lo hi : ImpExpr) (s : Int) : ImpExpr :=
  .app N.div [.app N.add [.app N.sub [hi, lo], .lit (.int (s - 1))], .lit (.int s)]

/-- The counted loop over `0..stepCountE lo hi s` binding `j` to `lo + v * s`. -/
def stepVTgt (N : Names) (v j : String) (lo hi : ImpExpr) (s : Int) (body : ImpExpr) :
    ImpExpr :=
  .forFold v (.lit (.int 0)) (stepCountE N lo hi s)
    (.letBind j (.app N.mul [.var v, .lit (.int s)])
      (.letBind j (.app N.add [lo, .var j]) body))

/-- A builtin table giving the stepped range with bounds of any numeric value its Rust
    meaning (`numOf`): the iterator of `(a..b).step_by(s)` has `stepCount a b s`
    elements, element `k` being `a + k * s`; `Range` and `sub` reject a non-numeric
    operand; `add`, `sub` and `mul` compute on integers and `div` divides by a positive
    integer. -/
structure VSpec (bi : Builtins) (N : Names) : Prop extends Spec bi N where
  iterV : ∀ (va vb : Value) (a b s : Int), numOf va = some a → numOf vb = some b → 0 < s →
    ∃ rv itv : Value,
    bi N.range [va, vb] = some rv ∧ rv.isControlFlow = false ∧
    bi N.stepBy [rv, .int s] = some itv ∧ itv.isControlFlow = false ∧
    (bi N.len [itv] = some (.int (stepCount a b s)) ∨
      ∃ w, bi N.len [itv] = some (.uint w (stepCount a b s))) ∧
    ∀ k : Nat, k < stepCount a b s → bi N.index [itv, .int k] = some (.int (a + k * s))
  range_none : ∀ w1 w2 : Value, (numOf w1 = none ∨ numOf w2 = none) →
    bi N.range [w1, w2] = none
  subV : ∀ (w1 w2 : Value) (x y : Int), numOf w1 = some x → numOf w2 = some y →
    bi N.sub [w1, w2] = some (.int (x - y))
  sub_none : ∀ w1 w2 : Value, (numOf w1 = none ∨ numOf w2 = none) → bi N.sub [w1, w2] = none
  addV : ∀ (w : Value) (x y : Int), numOf w = some x → bi N.add [w, .int y] = some (.int (x + y))
  div : ∀ x y : Int, 0 < y → bi N.div [.int x, .int y] = some (.int (x / y))

section VarNode

variable {bi : Builtins} {N : Names}

theorem bound_run_some {t : ImpExpr} (ht : boundOk t = true) {env : Env} {w : Value}
    (hw : boundVal env t = some w) (fuel : Nat) :
    (denote' bi fuel t).run env = (.val w, env) := by
  unfold boundOk at ht
  split at ht
  · simp only [boundVal, Option.some.injEq] at hw; subst hw; exact lit_run bi fuel _ env
  · simp only [boundVal] at hw; rw [var_run, hw]
  · simp at ht

theorem bound_run_none {t : ImpExpr} (ht : boundOk t = true) {env : Env}
    (hw : boundVal env t = none) (fuel : Nat) :
    ∃ m, (denote' bi fuel t).run env = (.err m, env) := by
  unfold boundOk at ht
  split at ht
  · simp [boundVal] at hw
  · simp only [boundVal] at hw; rw [var_run, hw]; exact ⟨_, rfl⟩
  · simp at ht

/-- The arguments `[t1, t2]` of two bounds evaluated in `env`. -/
def args2 (env : Env) (t1 t2 : ImpExpr) : Option (List Value) :=
  match boundVal env t1, boundVal env t2 with
  | some w1, some w2 => if w1.isControlFlow || w2.isControlFlow then none else some [w1, w2]
  | _, _ => none

theorem args2_run {t1 t2 : ImpExpr} (h1 : boundOk t1 = true) (h2 : boundOk t2 = true)
    (env : Env) (fuel : Nat) :
    (denoteArgs' bi fuel [t1, t2]).run env = (args2 env t1 t2, env) := by
  rw [args_cons_run]
  unfold args2
  rcases hb1 : boundVal env t1 with _ | w1
  · obtain ⟨m, hm⟩ := bound_run_none (bi := bi) h1 hb1 fuel; rw [hm]
  · rw [bound_run_some h1 hb1]
    rcases hb2 : boundVal env t2 with _ | w2
    · obtain ⟨m, hm⟩ := bound_run_none (bi := bi) h2 hb2 fuel
      cases w1 <;> simp [args_cons_run, hm]
    · have hr2 := bound_run_some (bi := bi) h2 hb2 fuel
      cases w1 <;> cases w2 <;>
        simp [args_cons_run, args_nil_run, hr2, Value.isControlFlow]

theorem app_err_head {f : String} {x : ImpExpr} {rest : List ImpExpr} {env : Env} {m : String}
    {fuel : Nat} (hx : (denote' bi fuel x).run env = (.err m, env)) :
    (denote' bi fuel (.app f (x :: rest))).run env =
      (.err "non-value in function arguments", env) := by
  rw [app_run, args_cons_run, hx]

/-- A call of `f` on two bounds that are not both numeric ends in an error, when `f`
    rejects a non-numeric operand. -/
theorem app2_err {f : String} {t1 t2 : ImpExpr} (h1 : boundOk t1 = true)
    (h2 : boundOk t2 = true)
    (hf : ∀ w1 w2 : Value, (numOf w1 = none ∨ numOf w2 = none) → bi f [w1, w2] = none)
    {env : Env} (hn : ¬ ∃ a b, (boundVal env t1).bind numOf = some a ∧
      (boundVal env t2).bind numOf = some b) (fuel : Nat) :
    ∃ m, (denote' bi fuel (.app f [t1, t2])).run env = (.err m, env) := by
  rw [app_run, args2_run h1 h2]
  unfold args2
  rcases hb1 : boundVal env t1 with _ | w1
  · exact ⟨_, rfl⟩
  rcases hb2 : boundVal env t2 with _ | w2
  · exact ⟨_, rfl⟩
  by_cases hc : (w1.isControlFlow || w2.isControlFlow) = true
  · simp only [if_pos hc]
    exact ⟨_, rfl⟩
  · have hnn : numOf w1 = none ∨ numOf w2 = none := by
      rw [hb1, hb2] at hn
      cases h1' : numOf w1 <;> cases h2' : numOf w2 <;> simp_all
    simp only [if_neg hc, hf w1 w2 hnn]
    exact ⟨_, rfl⟩

theorem forFold_hi_err {v : String} {hiE body : ImpExpr} {env : Env} {m : String}
    {fuel : Nat} (hh : (denote' bi fuel hiE).run env = (.err m, env)) :
    (denote' bi fuel (.forFold v (.lit (.int 0)) hiE body)).run env = (.err m, env) := by
  simp only [StateT.run] at hh
  simp [denote', StateT.run, bind, StateT.bind, hh, pure, StateT.pure, Value.ofLit]

theorem boundVal_extend {t : ImpExpr} {n : String} (hn : n ∉ boundVars t) (env : Env)
    (w : Value) : boundVal (env.extend n w) t = boundVal env t :=
  boundVal_frame fun _m hm => extend_ne _ (fun h => hn (h ▸ hm))

/-- Two loop bodies agreeing on every trip whose counter lies in `[0, hi)` from an
    environment satisfying `P` give the same loop from a nonnegative start, when binding
    the counter and running the second body keep `P`. -/
theorem loop_congr_inv {v : String} {hi : Int} {b1 b2 : ImpExpr} (P : Env → Prop)
    (hPv : ∀ env (k : Int), P env → P (env.extend v (.int k)))
    (hPb : ∀ fuel env, P env → P ((denote' bi fuel b2).run env).2)
    (h : ∀ fuel (env : Env) (k : Int), 0 ≤ k → k < hi → P env →
      (denote' bi fuel b1).run (env.extend v (.int k)) =
        (denote' bi fuel b2).run (env.extend v (.int k))) :
    ∀ fuel (lo : Int) env, 0 ≤ lo → P env →
      (denoteForLoop' bi fuel v lo hi b1).run env =
        (denoteForLoop' bi fuel v lo hi b2).run env := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo env _ _
    by_cases hl : hi ≤ lo
    · rw [forLoop_ge_run bi _ _ _ _ _ _ hl, forLoop_ge_run bi _ _ _ _ _ _ hl]
    · rw [forLoop_zero_run bi _ _ _ _ _ (by omega), forLoop_zero_run bi _ _ _ _ _ (by omega)]
  | succ n ih =>
    intro lo env hlo hP
    by_cases hl : hi ≤ lo
    · rw [forLoop_ge_run bi _ _ _ _ _ _ hl, forLoop_ge_run bi _ _ _ _ _ _ hl]
    · rw [forLoop_succ_run bi _ _ _ _ _ _ (by omega), forLoop_succ_run bi _ _ _ _ _ _ (by omega),
        h (n + 1) env lo hlo (by omega) hP]
      have hP2 := hPb (n + 1) _ (hPv env lo hP)
      rcases hr : (denote' bi (n + 1) b2).run (env.extend v (.int lo)) with ⟨o, e2⟩
      rw [hr] at hP2
      rcases o with w | _ | _ | _ | _ <;> try rfl
      cases w with
      | controlFlow k _ => cases k
                           · exact ih (lo + 1) e2 (by omega) hP2
                           · rfl
      | _ => exact ih (lo + 1) e2 (by omega) hP2

theorem stepCount_cast {a b s : Int} (hs : 0 < s) (hab : a ≤ b) :
    (b - a + (s - 1)) / s = ((stepCount a b s : Nat) : Int) := by
  unfold stepCount
  have h1 : (((b - a).toNat + s.toNat - 1 : Nat) : Int) = b - a + (s - 1) := by omega
  rw [Int.natCast_ediv, h1, Int.toNat_of_nonneg (by omega)]

theorem stepCount_empty {a b s : Int} (hs : 0 < s) (hab : b < a) :
    (b - a + (s - 1)) / s ≤ 0 ∧ stepCount a b s = 0 := by
  constructor
  · have : (b - a + (s - 1)) / s < 1 := by
      rw [Int.ediv_lt_iff_lt_mul hs]; omega
    omega
  · unfold stepCount
    rw [show (b - a).toNat = 0 by omega]
    exact Nat.div_eq_of_lt (by omega)

/-- **A stepped-range loop with variable bounds.** When the body keeps the variables the
    bounds read, the counted loop `stepVTgt` ends as the loop `stepVSrc` over the
    positions of the iterator `(lo..hi).step_by(s)`, for every fuel and environment. -/
theorem stepVTgt_run (hN : VSpec bi N) {v j : String} {lo hi : ImpExpr} {s : Int}
    (hs : 0 < s) (hlo : boundOk lo = true) (hhi : boundOk hi = true) {body : ImpExpr}
    (hk : ∀ n ∈ boundVars lo ++ boundVars hi, n ≠ v ∧ n ≠ j ∧ keeps n body = true)
    (fuel : Nat) (env : Env) :
    (denote' bi fuel (stepVTgt N v j lo hi s body)).run env =
      (denote' bi fuel (stepVSrc N v j lo hi s body)).run env := by
  by_cases hn : ∃ a b, (boundVal env lo).bind numOf = some a ∧
      (boundVal env hi).bind numOf = some b
  · obtain ⟨a, b, ha, hb⟩ := hn
    rcases hwa : boundVal env lo with _ | wa
    · simp [hwa] at ha
    rcases hwb : boundVal env hi with _ | wb
    · simp [hwb] at hb
    rw [hwa] at ha; rw [hwb] at hb
    simp only [Option.bind_some] at ha hb
    obtain ⟨rv, itv, hr, hrc, hst, hitc, hlen, hidx⟩ := hN.iterV wa wb a b s ha hb hs
    -- the iterator from any environment where the bounds read `wa` and `wb`
    have hit : ∀ fuel (e : Env), boundVal e lo = some wa → boundVal e hi = some wb →
        (denote' bi fuel (stepIterV N lo hi s)).run e = (.val itv, e) := by
      intro fuel e h1 h2
      exact app2_run (app2_run (bound_run_some hlo h1 fuel) (numOf_not_cf ha)
        (bound_run_some hhi h2 fuel) (numOf_not_cf hb) hr) hrc (lit_run bi fuel _ e) rfl hst
    -- the run-time count
    have hcnt : (denote' bi fuel (stepCountE N lo hi s)).run env =
        (.val (.int ((b - a + (s - 1)) / s)), env) := by
      have hsub := app2_run (bi := bi) (f := N.sub) (bound_run_some hhi hwb fuel)
        (numOf_not_cf hb) (bound_run_some hlo hwa fuel) (numOf_not_cf ha)
        (hN.subV wb wa b a hb ha)
      have hadd := app2_run hsub rfl (lit_run bi fuel (.int (s - 1)) env) rfl
        (hN.addV (.int (b - a)) (b - a) (s - 1) rfl)
      exact app2_run hadd rfl (lit_run bi fuel (.int s) env) rfl (hN.div _ s hs)
    -- the invariant: the bounds read `wa` and `wb`
    let P : Env → Prop := fun e => boundVal e lo = some wa ∧ boundVal e hi = some wb
    have hvlo : v ∉ boundVars lo := fun h => (hk v (List.mem_append_left _ h)).1 rfl
    have hvhi : v ∉ boundVars hi := fun h => (hk v (List.mem_append_right _ h)).1 rfl
    have hjlo : j ∉ boundVars lo := fun h => (hk j (List.mem_append_left _ h)).2.1 rfl
    have hjhi : j ∉ boundVars hi := fun h => (hk j (List.mem_append_right _ h)).2.1 rfl
    have hPv : ∀ e (k : Int), P e → P (e.extend v (.int k)) := fun e k ⟨h1, h2⟩ =>
      ⟨(boundVal_extend hvlo e _).trans h1, (boundVal_extend hvhi e _).trans h2⟩
    have hkeep : ∀ n ∈ boundVars lo ++ boundVars hi,
        keeps n (.letBind j (.app N.index [stepIterV N lo hi s, .var v]) body) = true := by
      intro n hn'
      obtain ⟨_, hnj, hkb⟩ := hk n hn'
      simp [keeps, keeps.keepsArgs, stepIterV, keeps_bound hlo, keeps_bound hhi, hkb,
        Ne.symm hnj]
    have hPb : ∀ fuel e, P e →
        P ((denote' bi fuel (.letBind j (.app N.index [stepIterV N lo hi s, .var v])
          body)).run e).2 := by
      intro fuel e ⟨h1, h2⟩
      refine ⟨(boundVal_frame fun n hn' => ?_).trans h1, (boundVal_frame fun n hn' => ?_).trans h2⟩
      · exact keeps_frame _ (hkeep n (List.mem_append_left _ hn')) fuel e
      · exact keeps_frame _ (hkeep n (List.mem_append_right _ hn')) fuel e
    have hbody : ∀ fuel (e : Env) (k : Int), 0 ≤ k → k < (stepCount a b s : Int) → P e →
        (denote' bi fuel (.letBind j (.app N.mul [.var v, .lit (.int s)])
            (.letBind j (.app N.add [lo, .var j]) body))).run (e.extend v (.int k)) =
          (denote' bi fuel (.letBind j (.app N.index [stepIterV N lo hi s, .var v]) body)).run
            (e.extend v (.int k)) := by
      intro fuel e k hk0 hkn hP
      obtain ⟨h1, h2⟩ := hPv e k hP
      have hv : ∀ e' : Env, (denote' bi fuel (.var v)).run (e'.extend v (.int k)) =
          (.val (.int k), e'.extend v (.int k)) := by
        intro e'; rw [var_run, Env.extend_same]
      rw [letBind_run, letBind_run,
        app2_run (hv e) rfl (lit_run bi fuel _ _) rfl (hN.mul k s),
        app2_run (hit fuel _ h1 h2) hitc (hv e) rfl (by
          have := hidx k.toNat (by omega)
          rwa [Int.toNat_of_nonneg hk0] at this)]
      simp only
      rw [letBind_run, app2_run
        (bound_run_some hlo ((boundVal_extend hjlo _ _).trans h1) fuel) (numOf_not_cf ha)
        (by rw [var_run, Env.extend_same]) rfl (hN.addV wa a (k * s) ha)]
      simp only [extend_extend_same]
    have hloop : ∀ H : Int, (0 < stepCount a b s → H = stepCount a b s) →
        (H ≤ 0 ↔ stepCount a b s = 0) →
        (denoteForLoop' bi fuel v 0 H (.letBind j (.app N.mul [.var v, .lit (.int s)])
            (.letBind j (.app N.add [lo, .var j]) body))).run env =
          (denoteForLoop' bi fuel v 0 (stepCount a b s)
            (.letBind j (.app N.index [stepIterV N lo hi s, .var v]) body)).run env := by
      intro H hH hz
      by_cases h0 : stepCount a b s = 0
      · rw [forLoop_ge_run bi _ _ _ _ _ _ (hz.mpr h0),
          forLoop_ge_run bi _ _ _ _ _ _ (by rw [h0]; exact Int.le_refl _)]
      · rw [hH (Nat.pos_of_ne_zero h0)]
        exact loop_congr_inv P hPv hPb hbody fuel 0 env (Int.le_refl 0) ⟨hwa, hwb⟩
    have hHc : (0 < stepCount a b s → (b - a + (s - 1)) / s = stepCount a b s) ∧
        ((b - a + (s - 1)) / s ≤ 0 ↔ stepCount a b s = 0) := by
      by_cases hab : a ≤ b
      · rw [stepCount_cast hs hab]; exact ⟨fun _ => rfl, by omega⟩
      · obtain ⟨h1, h2⟩ := stepCount_empty (a := a) (b := b) hs (by omega)
        exact ⟨fun h => by omega, ⟨fun _ => h2, fun _ => h1⟩⟩
    rw [stepVTgt, stepVSrc, forFold_run_int (lit_run bi fuel _ env) hcnt]
    rcases hlen with hl | ⟨w, hl⟩
    · rw [forFold_run_int (lit_run bi fuel _ env) (app1_run (hit fuel env hwa hwb) hitc hl)]
      exact hloop _ hHc.1 hHc.2
    · rw [forFold_run_uint (lit_run bi fuel _ env) (app1_run (hit fuel env hwa hwb) hitc hl)]
      exact hloop _ hHc.1 hHc.2
  · -- a bound is not numeric: both loops end in the error of their upper bound
    have hn' : ¬ ∃ b a, (boundVal env hi).bind numOf = some b ∧
        (boundVal env lo).bind numOf = some a := fun ⟨b, a, h1, h2⟩ => hn ⟨a, b, h2, h1⟩
    obtain ⟨m1, hsub⟩ := app2_err (bi := bi) (f := N.sub) hhi hlo hN.sub_none hn' fuel
    obtain ⟨m2, hrg⟩ := app2_err (bi := bi) (f := N.range) hlo hhi hN.range_none hn fuel
    rw [stepVTgt, stepVSrc, stepCountE, stepIterV,
      forFold_hi_err (app_err_head (app_err_head hsub)),
      forFold_hi_err (app_err_head (rest := []) (app_err_head hrg))]

end VarNode

/-! ## The rewriting of a function body -/

/-- The components `(v, j, a, b, s, body)` of a loop `stepSrc N v j a b s body` with
    `0 < s`, and `none` for every other expression. -/
def matchStep (N : Names) : ImpExpr → Option (String × String × Int × Int × Int × ImpExpr)
  | .forFold v (.lit (.int lo))
      (.app l [.app st [.app rg [.lit (.int a), .lit (.int b)], .lit (.int s)]])
      (.letBind j (.app ix [.app st' [.app rg' [.lit (.int a'), .lit (.int b')],
        .lit (.int s')], .var v']) body) =>
    if lo = 0 ∧ l = N.len ∧ st = N.stepBy ∧ rg = N.range ∧ ix = N.index ∧ st' = N.stepBy ∧
        rg' = N.range ∧ a' = a ∧ b' = b ∧ s' = s ∧ v' = v ∧ 0 < s then
      some (v, j, a, b, s, body)
    else none
  | _ => none

theorem matchStep_eq {N : Names} {e : ImpExpr} {v j : String} {a b s : Int}
    {body : ImpExpr} (h : matchStep N e = some (v, j, a, b, s, body)) :
    e = stepSrc N v j a b s body ∧ 0 < s := by
  unfold matchStep at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hs⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      exact ⟨rfl, hs⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The components `(v, j, lo, hi, s, body)` of a loop `stepVSrc N v j lo hi s body` with
    bounds passing `boundOk`, `0 < s`, and a body that keeps every variable the bounds read,
    none of which is `v` or `j`; `none` for every other expression. -/
def matchStepV (N : Names) :
    ImpExpr → Option (String × String × ImpExpr × ImpExpr × Int × ImpExpr)
  | .forFold v (.lit (.int z)) (.app l [.app st [.app rg [lo, hi], .lit (.int s)]])
      (.letBind j (.app ix [.app st' [.app rg' [lo', hi'], .lit (.int s')], .var v']) body) =>
    if z = 0 ∧ l = N.len ∧ st = N.stepBy ∧ rg = N.range ∧ ix = N.index ∧ st' = N.stepBy ∧
        rg' = N.range ∧ boundEq lo' lo = true ∧ boundEq hi' hi = true ∧ s' = s ∧ v' = v ∧
        0 < s ∧ boundOk lo = true ∧ boundOk hi = true ∧
        (boundVars lo ++ boundVars hi).all (fun n => n != v && n != j && keeps n body) = true
    then some (v, j, lo, hi, s, body)
    else none
  | _ => none

theorem matchStepV_eq {N : Names} {e : ImpExpr} {v j : String} {lo hi : ImpExpr} {s : Int}
    {body : ImpExpr} (h : matchStepV N e = some (v, j, lo, hi, s, body)) :
    e = stepVSrc N v j lo hi s body ∧ 0 < s ∧ boundOk lo = true ∧ boundOk hi = true ∧
      ∀ n ∈ boundVars lo ++ boundVars hi, n ≠ v ∧ n ≠ j ∧ keeps n body = true := by
  unfold matchStepV at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hlo', hhi', rfl, rfl, hs, hlo, hhi, hall⟩ := hc
      obtain rfl := boundEq_eq hlo'
      obtain rfl := boundEq_eq hhi'
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      refine ⟨rfl, hs, hlo, hhi, fun n hn => ?_⟩
      have := List.all_eq_true.mp hall n hn
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The loop `e` rewritten to `stepTgt N v j a b s body` when `matchStep N e` recognizes
    it, to `stepVTgt N v j lo hi s body` when `matchStepV N e` recognizes it, and `e`
    otherwise. -/
def stepNode (N : Names) (e : ImpExpr) : ImpExpr :=
  match matchStep N e with
  | some (v, j, a, b, s, body) => stepTgt N v j a b s body
  | none =>
    match matchStepV N e with
    | some (v, j, lo, hi, s, body) => stepVTgt N v j lo hi s body
    | none => e

/-- A function body with each loop `stepSrc N v j a b s body` with `0 < s` rewritten to
    `stepTgt N v j a b s body`, and each loop recognized by `matchStepV` rewritten to
    `stepVTgt`, under `letBind`, `seq`, `ifThenElse` and inside the body of every
    `forFold` and `forFoldReturn`. -/
def stepFn (N : Names) : ImpExpr → ImpExpr
  | .letBind n v b => .letBind n v (stepFn N b)
  | .seq a b => .seq (stepFn N a) (stepFn N b)
  | .ifThenElse c t e => .ifThenElse c (stepFn N t) (stepFn N e)
  | .forFold i lo hi b => stepNode N (.forFold i lo hi (stepFn N b))
  | .forFoldReturn i lo hi b => .forFoldReturn i lo hi (stepFn N b)
  | e => e

section Fn

variable {bi : Builtins} {N : Names}

theorem forFold_body_congr {i : String} {lo hi b1 b2 : ImpExpr}
    (h : ∀ fuel env, (denote' bi fuel b1).run env = (denote' bi fuel b2).run env)
    (fuel : Nat) (env : Env) :
    (denote' bi fuel (.forFold i lo hi b1)).run env =
      (denote' bi fuel (.forFold i lo hi b2)).run env := by
  have hl := denoteForLoop'_body_congr bi i b1 b2 (fun f e => h f e)
  have hf : ∀ fuel lo hi, denoteForLoop' bi fuel i lo hi b1 = denoteForLoop' bi fuel i lo hi b2 :=
    fun f l u => funext (hl f l u)
  simp only [denote', hf]

theorem forFoldReturn_body_congr {i : String} {lo hi b1 b2 : ImpExpr}
    (h : ∀ fuel env, (denote' bi fuel b1).run env = (denote' bi fuel b2).run env)
    (fuel : Nat) (env : Env) :
    (denote' bi fuel (.forFoldReturn i lo hi b1)).run env =
      (denote' bi fuel (.forFoldReturn i lo hi b2)).run env := by
  have hl := denoteForLoop'Return_body_congr bi i b1 b2 (fun f e => h f e)
  have hf : ∀ fuel lo hi,
      denoteForLoop'Return bi fuel i lo hi b1 = denoteForLoop'Return bi fuel i lo hi b2 :=
    fun f l u => funext (hl f l u)
  simp only [denote', hf]

/-- **The rewritten function body.** Under a table meeting `VSpec`, `stepFn N e` and `e`
    end in the same outcome and environment, for every fuel and environment. -/
theorem stepFn_run (hN : VSpec bi N) (e : ImpExpr) :
    ∀ fuel env, (denote' bi fuel (stepFn N e)).run env = (denote' bi fuel e).run env := by
  induction e using ImpExpr.ind with
  | letBind n v b _ ihb =>
    intro fuel env
    show (denote' bi fuel (.letBind n v (stepFn N b))).run env = _
    rw [letBind_run, letBind_run]
    simp only [ihb]
  | seq a b iha ihb =>
    intro fuel env
    show (denote' bi fuel (.seq (stepFn N a) (stepFn N b))).run env = _
    rw [seq_run, seq_run, iha]
    simp only [ihb]
  | ifThenElse c t e _ iht ihe =>
    intro fuel env
    show (denote' bi fuel (.ifThenElse c (stepFn N t) (stepFn N e))).run env = _
    rw [ifThenElse_run, ifThenElse_run]
    simp only [iht, ihe]
  | forFold i lo hi b _ _ ihb =>
    intro fuel env
    have hb := forFold_body_congr (i := i) (lo := lo) (hi := hi) ihb fuel env
    show (denote' bi fuel (stepNode N (.forFold i lo hi (stepFn N b)))).run env = _
    unfold stepNode
    split
    · rename_i hm
      obtain ⟨he, hs⟩ := matchStep_eq hm
      rw [stepTgt_run hN.toSpec hs, ← he, hb]
    · split
      · rename_i hm
        obtain ⟨he, hs, hlo, hhi, hk⟩ := matchStepV_eq hm
        rw [stepVTgt_run hN hs hlo hhi hk, ← he, hb]
      · exact hb
  | forFoldReturn i lo hi b _ _ ihb =>
    intro fuel env
    exact forFoldReturn_body_congr ihb fuel env
  | _ => intros; rfl

end Fn

/-! ## A table meeting the specification -/

/-- Element `k` of `vs.step_by(s)` is element `k * s` of `vs`. -/
def stepList (vs : List Value) (s : Nat) : List Value :=
  (List.range ((vs.length + s - 1) / s)).map fun k => vs.getD (k * s) .unit

/-- A builtin table with `Range` and `step_by` materialized as arrays, `len`, `index`,
    and integer `add` and `mul`. -/
def refTable : Builtins := fun f args =>
  match f, args with
  | "Range", [.int a, .int b] =>
    some (.array ((List.range (b - a).toNat).map fun i : Nat => .int (a + i)))
  | "step_by", [.array vs, .int s] => some (.array (stepList vs s.toNat))
  | "len", [.array vs] => some (.int vs.length)
  | "index", [.array vs, .int i] => if 0 ≤ i then vs[i.toNat]? else none
  | "add", [.int x, .int y] => some (.int (x + y))
  | "mul", [.int x, .int y] => some (.int (x * y))
  | _, _ => none

/-- `refTable` meets `Spec` at the default names. -/
theorem refTable_spec : Spec refTable {} where
  iter a b s hs := by
    refine ⟨_, _, rfl, rfl, rfl, rfl, Or.inl ?_, ?_⟩
    · show some (Value.int _) = _
      simp only [stepList, stepCount, List.length_map, List.length_range]
    · intro k hk
      have hs' : 0 < s.toNat := by omega
      have hks : k * s.toNat < (b - a).toNat := by
        have h1 : k + 1 ≤ ((b - a).toNat + s.toNat - 1) / s.toNat := hk
        rw [Nat.le_div_iff_mul_le hs', Nat.add_mul, Nat.one_mul] at h1
        omega
      show (if (0 : Int) ≤ ((k : Nat) : Int) then
          (stepList ((List.range (b - a).toNat).map fun i : Nat => Value.int (a + i))
            s.toNat)[((k : Nat) : Int).toNat]? else none) = some (Value.int (a + k * s))
      simp only [stepList, Int.natCast_nonneg, if_true, Int.toNat_natCast]
      rw [List.getElem?_map, List.getElem?_range (by simpa [stepCount] using hk)]
      simp only [Option.map_some, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hks, Option.getD_some, Option.some.injEq, Value.int.injEq]
      rw [Int.natCast_mul, Int.toNat_of_nonneg (by omega)]
  add _ _ := rfl
  mul _ _ := rfl

/-- `refTable` with `Range`, `add` and `sub` on every numeric operand (`numOf`) and `div`
    by a positive integer. -/
def refTableV : Builtins := fun f args =>
  match f, args with
  | "Range", [x, y] => (numOf x).bind fun a => (numOf y).bind fun b =>
      some (.array ((List.range (b - a).toNat).map fun i : Nat => .int (a + i)))
  | "sub", [x, y] => (numOf x).bind fun a => (numOf y).bind fun b => some (.int (a - b))
  | "add", [x, y] => (numOf x).bind fun a => (numOf y).bind fun b => some (.int (a + b))
  | "div", [.int x, .int y] => if 0 < y then some (.int (x / y)) else none
  | _, _ => refTable f args

theorem refTableV_range {va vb : Value} {a b : Int} (ha : numOf va = some a)
    (hb : numOf vb = some b) : refTableV "Range" [va, vb] = refTable "Range" [.int a, .int b] := by
  simp only [refTableV, ha, hb, Option.bind_some]; rfl

/-- `refTableV` meets `VSpec` at the default names. -/
theorem refTableV_vspec : VSpec refTableV {} where
  iter a b s hs := by
    obtain ⟨rv, itv, h1, h2, h3, h4, h5, h6⟩ := refTable_spec.iter a b s hs
    exact ⟨rv, itv, (refTableV_range rfl rfl).trans h1, h2, h3, h4, h5, h6⟩
  add _ _ := rfl
  mul _ _ := rfl
  iterV va vb a b s ha hb hs := by
    obtain ⟨rv, itv, h1, h2, h3, h4, h5, h6⟩ := refTable_spec.iter a b s hs
    exact ⟨rv, itv, (refTableV_range ha hb).trans h1, h2, h3, h4, h5, h6⟩
  range_none w1 w2 h := by
    show refTableV "Range" [w1, w2] = none
    rcases h with h | h <;> simp [refTableV, h]
  subV w1 w2 x y h1 h2 := by
    show refTableV "sub" [w1, w2] = _
    simp [refTableV, h1, h2]
  sub_none w1 w2 h := by
    show refTableV "sub" [w1, w2] = none
    rcases h with h | h <;> simp [refTableV, h]
  addV w x y h := by
    show refTableV "add" [w, .int y] = _
    simp only [refTableV, h, Option.bind_some]; rfl
  div x y hy := by
    show refTableV "div" [.int x, .int y] = _
    simp [refTableV, hy]

end Hax.IterStepBy

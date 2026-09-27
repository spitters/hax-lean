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
* `stepFn_run`: `stepFn N`, which rewrites every recognized loop under `letBind`,
  `seq`, `ifThenElse` and inside loop bodies, preserves the outcome and environment of
  every expression
* `refTable_spec`: a table materializing `Range` and `step_by` as arrays meets `Spec`
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.IterStepBy

open Hax.ContinueFlag (app_run lit_run var_run letBind_run seq_run ifThenElse_run
  args_cons_run args_nil_run
  forLoop_ge_run forLoop_zero_run forLoop_succ_run)

/-- The builtin names a stepped-range loop uses. -/
structure Names where
  range : String := "Range"
  stepBy : String := "step_by"
  len : String := "len"
  index : String := "index"
  add : String := "add"
  mul : String := "mul"

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

/-- The loop `e` rewritten to `stepTgt N v j a b s body` when `matchStep N e` recognizes
    it, and `e` otherwise. -/
def stepNode (N : Names) (e : ImpExpr) : ImpExpr :=
  match matchStep N e with
  | some (v, j, a, b, s, body) => stepTgt N v j a b s body
  | none => e

/-- A function body with each loop `stepSrc N v j a b s body` with `0 < s` rewritten to
    `stepTgt N v j a b s body`, under `letBind`, `seq`, `ifThenElse` and inside the body
    of every `forFold` and `forFoldReturn`. -/
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

/-- **The rewritten function body.** Under a table meeting `Spec`, `stepFn N e` and `e`
    end in the same outcome and environment, for every fuel and environment. -/
theorem stepFn_run (hN : Spec bi N) (e : ImpExpr) :
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
      rw [stepTgt_run hN hs, ← he, hb]
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

end Hax.IterStepBy

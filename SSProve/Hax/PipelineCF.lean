/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.Pipeline
import SSProve.Hax.Phase.FunctionalizeLoopsCF
import SSProve.Hax.Phase.CfIntoMonadsCF

/-!
# Pipeline Semantic Correctness with ControlFlow Encoding

Composes the 4-phase correctness theorems into end-to-end pipeline results.

## Main results

* `pipeline_cf` — for `NoEarlyExit` programs, the pipeline maps `denote` to
  `denote'` with `encodeCF3` encoding (loops → ControlFlow, rest preserved)
* `pipeline_cf_val` — corollary: normal-terminating programs evaluate to the
  same value under `denote'`

## Scope and limitations

This composition handles programs **without** `earlyReturn`/`questionMark`.
For such programs, Phase 4 (`cfIntoMonads`) is the identity, so the pipeline
reduces to Phases 1-3.

Programs with `earlyReturn` inside loop bodies require a nested ControlFlow
encoding that our flat `denote'` does not capture. The individual Phase 3
(`FL_combined`) and Phase 4 (`CF4_combined`) theorems remain valid but cannot
be naively composed when both control flow features are present.
-/

namespace SSProve.Hax

/-! ### Preservation: functionalizeLoops preserves NoEarlyExit -/

theorem functionalizeLoops_preserves_noEarlyExit (e : ImpExpr) (h : NoEarlyExit e) :
    NoEarlyExit (functionalizeLoops e) := by
  induction e using ImpExpr.ind with
  | lit => exact .lit
  | var => exact .var
  | letBind _ _ _ ih1 ih2 => cases h with | letBind h1 h2 => exact .letBind (ih1 h1) (ih2 h2)
  | app _ args ih =>
    cases h with | app hargs =>
    simp only [functionalizeLoops, functionalizeLoops.mapExpr_eq]
    exact .app (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (hargs b hb))
  | tuple elems ih =>
    cases h with | tuple helems =>
    simp only [functionalizeLoops, functionalizeLoops.mapExpr_eq]
    exact .tuple (fun a ha => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact ih b hb (helems b hb))
  | proj _ _ ih => cases h with | proj he => exact .proj (ih he)
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    cases h with | ifThenElse h1 h2 h3 => exact .ifThenElse (ih1 h1) (ih2 h2) (ih3 h3)
  | match_ _ arms ih1 ih2 =>
    cases h with | match_ hs harms =>
    simp only [functionalizeLoops, functionalizeLoops.mapArms_eq]
    exact .match_ (ih1 hs) (fun pa hpa => by
      obtain ⟨⟨p, b⟩, hpb, rfl⟩ := List.mem_map.mp hpa
      exact ih2 (p, b) hpb (harms (p, b) hpb))
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => cases h with | seq h1 h2 => exact .seq (ih1 h1) (ih2 h2)
  | borrow _ ih => cases h with | borrow he => exact .borrow (ih he)
  | deref _ ih => cases h with | deref he => exact .deref (ih he)
  | assign _ _ ih => cases h with | assign hrhs => exact .assign (ih hrhs)
  | forLoop _ _ _ _ ih1 ih2 ih3 =>
    cases h with | forLoop h1 h2 h3 =>
    exact .app (fun a ha => by
      simp at ha
      rcases ha with rfl | rfl | rfl | rfl
      · exact .var
      · exact ih1 h1
      · exact ih2 h2
      · exact ih3 h3)
  | whileLoop _ _ ih1 ih2 =>
    cases h with | whileLoop h1 h2 =>
    exact .app (fun a ha => by
      simp at ha
      rcases ha with rfl | rfl
      · exact ih1 h1
      · exact ih2 h2)
  | break_none => exact .app (fun a ha => by simp at ha; subst ha; exact .unitVal)
  | break_some _ ih =>
    cases h with | break_some he =>
    exact .app (fun a ha => by simp at ha; subst ha; exact ih he)
  | continue_ => exact .app (fun a ha => by simp at ha; subst ha; exact .unitVal)
  | earlyReturn => exact absurd h NoEarlyExit.not_earlyReturn
  | questionMark => exact absurd h NoEarlyExit.not_questionMark

/-! ### Pipeline composition -/

/-- For programs without `earlyReturn`/`questionMark`, the pipeline maps
    `denote` outcomes to `denote'` outcomes via `encodeCF3`:
    - `val v` → `val v` (unchanged)
    - `broke v` → `val (controlFlow true v)` (break encoded)
    - `continued` → `val (controlFlow false unit)` (continue encoded)
    - `err msg` → `err msg` (unchanged)
    - `earlyRet v` → `earlyRet v` (cannot occur under `NoEarlyExit`) -/
theorem pipeline_cf (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (e : ImpExpr)
    (hnr : NoReservedApps (localMutation (mutatedVars e) (dropReferences e)))
    (hnee : NoEarlyExit (localMutation (mutatedVars e) (dropReferences e))) :
    ∀ fuel env, Env.NoControlFlow env →
      denote' bi fuel (pipeline e) env =
        (Outcome.encodeCF3 (denote bi fuel e env).1, (denote bi fuel e env).2) := by
  intro fuel env henv
  -- Phase 4 is identity since input has NoEarlyExit after Phase 3
  have hfl_nee := functionalizeLoops_preserves_noEarlyExit _ hnee
  have hcf := cfIntoMonads_correct _ hfl_nee
  -- Pipeline = cfIntoMonads (functionalizeLoops e12) = functionalizeLoops e12
  show denote' bi fuel (pipeline e) env = _
  unfold pipeline
  rw [hcf]
  -- Phase 3 correctness
  have hfl := FL_combined bi hbi _ hnr
  obtain ⟨_, _, _, hsim⟩ := hfl fuel env henv
  rw [hsim]
  -- Phases 1-2 correctness
  rw [localMutation_correct, dropReferences_correct]

/-- For normal-terminating programs (`val v` outcome), the pipeline output
    evaluates to the same value. -/
theorem pipeline_cf_val (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (e : ImpExpr)
    (hnr : NoReservedApps (localMutation (mutatedVars e) (dropReferences e)))
    (hnee : NoEarlyExit (localMutation (mutatedVars e) (dropReferences e)))
    (fuel : Nat) (env : Env) (henv : Env.NoControlFlow env)
    (v : Value) (hval : (denote bi fuel e env).1 = .val v) :
    (denote' bi fuel (pipeline e) env).1 = .val v := by
  rw [pipeline_cf bi hbi e hnr hnee fuel env henv, hval]
  rfl

/-- For erroring programs, the pipeline preserves the error. -/
theorem pipeline_cf_err (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (e : ImpExpr)
    (hnr : NoReservedApps (localMutation (mutatedVars e) (dropReferences e)))
    (hnee : NoEarlyExit (localMutation (mutatedVars e) (dropReferences e)))
    (fuel : Nat) (env : Env) (henv : Env.NoControlFlow env)
    (msg : String) (herr : (denote bi fuel e env).1 = .err msg) :
    (denote' bi fuel (pipeline e) env).1 = .err msg := by
  rw [pipeline_cf bi hbi e hnr hnee fuel env henv, herr]
  rfl

/-- The pipeline preserves the environment (second component). -/
theorem pipeline_cf_env (bi : Builtins) (hbi : Builtins.DeepNoControlFlow bi)
    (e : ImpExpr)
    (hnr : NoReservedApps (localMutation (mutatedVars e) (dropReferences e)))
    (hnee : NoEarlyExit (localMutation (mutatedVars e) (dropReferences e)))
    (fuel : Nat) (env : Env) (henv : Env.NoControlFlow env) :
    (denote' bi fuel (pipeline e) env).2 = (denote bi fuel e env).2 := by
  rw [pipeline_cf bi hbi e hnr hnee fuel env henv]

end SSProve.Hax

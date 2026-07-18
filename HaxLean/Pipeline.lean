/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import HaxLean.AST
import HaxLean.Value
import HaxLean.Features
import HaxLean.FreeVars
import HaxLean.Semantics
import HaxLean.Phase.DropReferences
import HaxLean.Phase.LocalMutation
import HaxLean.Phase.FunctionalizeLoops
import HaxLean.Phase.CfIntoMonads
import HaxLean.Phase.ExplicitMonadic

/-!
# End-to-End Pipeline

Compose the phases; the output lands in the `FullyFunctional` fragment of `ImpExpr`.

```
ImpExpr
  --[dropReferences]-->    ImpExpr  (NoReferences)
  --[localMutation]-->     ImpExpr  (NoMutation)
  --[functionalizeLoops]-> ImpExpr  (NoLoops)
  --[cfIntoMonads]-------> ImpExpr  (NoEarlyExit)
  --[explicitMonadic]----> ImpExpr  (FullyFunctional, explicit CF encoding)
```

## Main definitions

* `pipeline` — full phase composition (4 core phases)
* `pipelineExt` — extended pipeline with explicit monadic encoding (5 phases)
* `pipeline_fullyFunctional` — all feature predicates hold after pipeline
-/

namespace Hax

/-- The full 4-phase pipeline. -/
def pipeline (e : ImpExpr) : ImpExpr :=
  cfIntoMonads (functionalizeLoops (localMutation (mutatedVars e) (dropReferences e)))

/-- The pipeline output has no references. -/
theorem pipeline_noRefs (e : ImpExpr) : NoReferences (pipeline e) := by
  unfold pipeline
  exact cfIntoMonads_preserves_noRefs _
    (functionalizeLoops_preserves_noRefs _
      (localMutation_preserves_noRefs _ _
        (dropReferences_noRefs e)))

/-- The pipeline output has no mutation. -/
theorem pipeline_noMut (e : ImpExpr) : NoMutation (pipeline e) := by
  unfold pipeline
  exact cfIntoMonads_preserves_noMut _
    (functionalizeLoops_preserves_noMut _
      (localMutation_noMut _ _))

/-- The pipeline output has no loops. -/
theorem pipeline_noLoops (e : ImpExpr) : NoLoops (pipeline e) := by
  unfold pipeline
  exact cfIntoMonads_preserves_noLoops _
    (functionalizeLoops_noLoops _)

/-- The pipeline output has no early exits. -/
theorem pipeline_noEarlyExit (e : ImpExpr) : NoEarlyExit (pipeline e) := by
  unfold pipeline
  exact cfIntoMonads_noEarlyExit _

/-- The pipeline output is fully functional. -/
theorem pipeline_fullyFunctional (e : ImpExpr) : FullyFunctional (pipeline e) :=
  ⟨pipeline_noRefs e, pipeline_noMut e, pipeline_noLoops e, pipeline_noEarlyExit e⟩

/-- End-to-end correctness: the pipeline preserves semantics for inputs
    whose loop-free and early-exit-free structure is preserved through
    phases 1–2.

    For inputs with loops or early exits, phases 3–4 rewrite them into the
    fold constructors (`forFold`, `whileFold`, `cfBreak`, `cfContinue`), which
    `denote` errors on. Those cases are discharged in `PipelineCF`: the output
    is read by the ControlFlow-aware evaluator `denote'` and agrees with `denote`
    up to `Outcome.encodeCF` (see `pipeline_correct'`, which drops `hNoLoops`,
    and `pipeline_full_correct`, which also drops `hNoEE`). -/
theorem pipeline_correct (bi : Builtins) (fuel : Nat) (e : ImpExpr)
    (hNoLoops : NoLoops (localMutation (mutatedVars e) (dropReferences e)))
    (hNoEE : NoEarlyExit (localMutation (mutatedVars e) (dropReferences e))) :
    denote bi fuel (pipeline e) = denote bi fuel e := by
  unfold pipeline
  have hfl := functionalizeLoops_correct _ hNoLoops
  rw [cfIntoMonads_correct _ (by rw [hfl]; exact hNoEE), hfl,
      localMutation_correct, dropReferences_correct]

/-! ## Extended Pipeline with Explicit Monadic Encoding -/

/-- The extended 5-phase pipeline: core pipeline + explicit monadic encoding. -/
def pipelineExt (e : ImpExpr) : ImpExpr :=
  explicitMonadic (pipeline e)

/-- The extended pipeline output is fully functional. -/
theorem pipelineExt_fullyFunctional (e : ImpExpr) : FullyFunctional (pipelineExt e) := by
  unfold pipelineExt
  have hff := pipeline_fullyFunctional e
  exact ⟨explicitMonadic_preserves_noRefs _ hff.1,
         explicitMonadic_preserves_noMut _ hff.2.1,
         explicitMonadic_preserves_noLoops _ hff.2.2.1,
         explicitMonadic_preserves_noEarlyExit _ hff.2.2.2⟩

end Hax

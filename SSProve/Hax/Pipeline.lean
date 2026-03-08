/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.AST
import SSProve.Hax.Value
import SSProve.Hax.Features
import SSProve.Hax.FreeVars
import SSProve.Hax.Semantics
import SSProve.Hax.Phase.DropReferences
import SSProve.Hax.Phase.LocalMutation
import SSProve.Hax.Phase.FunctionalizeLoops
import SSProve.Hax.Phase.CfIntoMonads
import SSProve.Hax.ToRawCode

/-!
# End-to-End Pipeline

Compose all four phases and translate to `RawCode`.

```
ImpExpr
  --[dropReferences]-->    ImpExpr  (NoReferences)
  --[localMutation]-->     ImpExpr  (NoMutation)
  --[functionalizeLoops]-> ImpExpr  (NoLoops)
  --[cfIntoMonads]-------> ImpExpr  (NoEarlyExit)
  --[toRawCode]----------> RawCode
```

## Main definitions

* `pipeline` — full phase composition
* `pipelineToRawCode` — pipeline + translation to RawCode
* `pipeline_fullyFunctional` — all feature predicates hold after pipeline
-/

namespace SSProve.Hax

open SSProve.Deep

/-- The full 4-phase pipeline. -/
def pipeline (e : ImpExpr) : ImpExpr :=
  cfIntoMonads (functionalizeLoops (localMutation (mutatedVars e) (dropReferences e)))

/-- Pipeline + translation to RawCode. -/
noncomputable def pipelineToRawCode (e : ImpExpr) : RawCode Value :=
  toRawCode (pipeline e)

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

    For inputs with loops or early exits, phases 3–4 rewrite them into
    builtin `app` calls, so correctness additionally requires that the
    builtins implement `for_fold`, `while_fold`, `ControlFlow.Break`, etc. -/
theorem pipeline_correct (bi : Builtins) (fuel : Nat) (e : ImpExpr)
    (hNoLoops : NoLoops (localMutation (mutatedVars e) (dropReferences e)))
    (hNoEE : NoEarlyExit (localMutation (mutatedVars e) (dropReferences e))) :
    denote bi fuel (pipeline e) = denote bi fuel e := by
  unfold pipeline
  have hfl := functionalizeLoops_correct _ hNoLoops
  rw [cfIntoMonads_correct _ (by rw [hfl]; exact hNoEE), hfl,
      localMutation_correct, dropReferences_correct]

end SSProve.Hax

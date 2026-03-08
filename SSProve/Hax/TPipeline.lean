/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.TExpr
import SSProve.Hax.TFeatures
import SSProve.Hax.TPhase.DropReferences
import SSProve.Hax.TPhase.LocalMutation
import SSProve.Hax.TPhase.FunctionalizeLoops
import SSProve.Hax.TPhase.CfIntoMonads
import SSProve.Hax.TPhase.ExplicitMonadic
import SSProve.Hax.Pipeline

/-!
# Typed Pipeline

End-to-end typed pipeline composition with correctness via commuting diagram.

```
TExpr ──[tPipeline]──→ TExpr
  │                       │
  │ erase                 │ erase
  ↓                       ↓
ImpExpr ──[pipeline]──→ ImpExpr    (already verified)
```
-/

namespace SSProve.Hax

/-- Typed mutated variables: computed via erasure. -/
def tMutatedVars (e : TExpr) : List String := mutatedVars e.erase

/-- The full typed 4-phase pipeline. -/
def tPipeline (e : TExpr) : TExpr :=
  tCfIntoMonads (tFunctionalizeLoops (tLocalMutation (tMutatedVars e) (tDropReferences e)))

/-- Commuting diagram: `erase ∘ tPipeline = pipeline ∘ erase`. -/
theorem tPipeline_erase (e : TExpr) :
    (tPipeline e).erase = pipeline e.erase := by
  unfold tPipeline pipeline
  rw [tCfIntoMonads_erase, tFunctionalizeLoops_erase, tLocalMutation_erase,
    tDropReferences_erase]
  rfl

/-- The typed pipeline output is fully functional (via erasure + untyped proof). -/
theorem tPipeline_fullyFunctional (e : TExpr) : TFullyFunctional (tPipeline e) := by
  unfold TFullyFunctional
  rw [tPipeline_erase]
  exact pipeline_fullyFunctional e.erase

/-! ## Extended Typed Pipeline -/

/-- The extended typed 5-phase pipeline. -/
def tPipelineExt (e : TExpr) : TExpr :=
  tExplicitMonadic (tPipeline e)

/-- Commuting diagram for the extended pipeline. -/
theorem tPipelineExt_erase (e : TExpr) :
    (tPipelineExt e).erase = pipelineExt e.erase := by
  unfold tPipelineExt pipelineExt
  rw [tExplicitMonadic_erase, tPipeline_erase]

/-- The extended typed pipeline output is fully functional. -/
theorem tPipelineExt_fullyFunctional (e : TExpr) : TFullyFunctional (tPipelineExt e) := by
  unfold TFullyFunctional
  rw [tPipelineExt_erase]
  exact pipelineExt_fullyFunctional e.erase

end SSProve.Hax

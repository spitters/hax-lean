/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr
import Hax.TFeatures
import Hax.TPhase.DropReferences
import Hax.TPhase.LocalMutation
import Hax.TPhase.FunctionalizeLoops
import Hax.TPhase.CfIntoMonads
import Hax.TPhase.WrapMatchArms
import Hax.TPhase.ExplicitMonadic
import Hax.TPhase.AnnotateLets
import Hax.Pipeline

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

namespace Hax

/-- Typed mutated variables: computed via erasure. -/
def tMutatedVars (e : TExpr) : List String := mutatedVars e.erase

/-- The full typed 4-phase pipeline, followed by the post-pipeline
    annotation phase. `tAnnotateLetBindings` is denotation-identity
    (wraps non-trivial let-RHSs in `.ann` markers that erase away),
    so the same correctness theorems apply unchanged. -/
def tPipeline (e : TExpr) : TExpr :=
  tAnnotateLetBindings
    (tCfIntoMonads (tFunctionalizeLoops (tLocalMutation (tMutatedVars e) (tDropReferences e))))

/-- Extended typed pipeline with the match-arms-cfContinue wrap.
    Applied as a post-pipeline correction for Rust's "fall-through-as-
    continue" semantic. Erase commutativity (with a hypothetical
    `pipelineWithWrap := wrapMatchArmsCF ∘ pipeline`) is supported by
    `TExpr.endsInCF_erase` and `TExpr.maybeWrapContinue_erase`
    (defined in `TPhase/WrapMatchArms.lean`). -/
def tPipelineWithCFWrap (e : TExpr) : TExpr :=
  tWrapMatchArmsCF (tPipeline e)

/-- Commuting diagram: `erase ∘ tPipeline = pipeline ∘ erase`. -/
theorem tPipeline_erase (e : TExpr) :
    (tPipeline e).erase = pipeline e.erase := by
  unfold tPipeline pipeline
  rw [tAnnotateLetBindings_erase, tCfIntoMonads_erase, tFunctionalizeLoops_erase,
    tLocalMutation_erase, tDropReferences_erase]
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

end Hax

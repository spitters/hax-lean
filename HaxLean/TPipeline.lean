/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import HaxLean.TExpr
import HaxLean.TFeatures
import HaxLean.TPhase.DropReferences
import HaxLean.TPhase.LocalMutation
import HaxLean.TPhase.FunctionalizeLoops
import HaxLean.TPhase.CfIntoMonads
import HaxLean.TPhase.WrapMatchArms
import HaxLean.TPhase.ExplicitMonadic
import HaxLean.TPhase.AnnotateLets
import HaxLean.TPhase.ElideNewtypeProj
import HaxLean.TPhase.FlattenLetFoldReturn
import HaxLean.Pipeline

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

/-- Extended typed pipeline including the newtype-projection elision
    and the let-fold-return flattening (post-pipeline normalisations).

    Composed alongside `tPipeline` so the existing `tPipeline_erase` is
    unchanged. `tElideToNamedProj` is a denotation-identity via the
    standard erase-then-untyped-denote route. `tFlattenLetFoldReturn` is
    a **render-time** normalisation, now a **total** `fuel`-bounded
    function (no `partial`). Its four rewrites are mechanised as
    denotation-preserving identities on the untyped semantics in
    `Hax/Phase/FlattenLetFoldReturn.lean` (`flattenA_denote`..
    `flattenD_denote`): B and C are unconditional `denote = denote`
    equalities; A and D hold under the `noVarRef "_"` freshness
    side-condition via the env-insensitivity congruence
    `denote_agreeExcept`, with composable two-environment forms
    (`flattenA_rel`, `flattenD_rel`) and `Rel` a partial equivalence.
    The fuel below is a generous quadratic bound in the AST node count,
    exceeding the recursion depth, so the result is the rewrite fixpoint
    — byte-identical to the previous `partial def`. The whole-pass
    denotation preservation `flattenLetFoldReturn_denote`
    (`noVarRef "_" e → Rel "_" (denote (flattenLetFoldReturn k e))
    (denote e)`) is **proved** on the total untyped twin (axiom-clean),
    by a heterogeneous structural congruence composed with the four
    rewrite identities. A fixed-fuel erase lemma does not hold for all
    fuel (`ann`/`namedProj` nodes consume typed-side fuel that `erase`
    removes), so the whole-pass theorem is stated on the untyped twin to
    avoid that obstruction. -/
def tPipelineFull (newtypes : HaxAdapter.NewtypeMap) (e : TExpr) : TExpr :=
  let inner := tElideToNamedProj newtypes (tWrapMatchArmsCF (tPipeline e))
  -- `tFlattenLetFoldReturn` is now total (fuel-bounded). The fuel is a
  -- generous quadratic bound in the AST size, exceeding the (finite)
  -- recursion depth, so the result is the rewrite fixpoint — identical
  -- to the previous `partial def`.
  let n := inner.erase.nodeCount
  tFlattenLetFoldReturn (n * n + n + 1000) inner

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

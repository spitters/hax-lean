/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.TExpr
public import HaxLean.TFeatures
public import HaxLean.TPhase.DropReferences
public import HaxLean.TPhase.LocalMutation
public import HaxLean.TPhase.FunctionalizeLoops
public import HaxLean.TPhase.CfIntoMonads
public import HaxLean.TPhase.WrapMatchArms
public import HaxLean.TPhase.ExplicitMonadic
public import HaxLean.TPhase.AnnotateLets
public import HaxLean.TPhase.ElideNewtypeProj
public import HaxLean.TPhase.FlattenLetFoldReturn
public import HaxLean.TPhase.IrrefutableTupleMatch
public import HaxLean.Pipeline

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

@[expose] public section

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

/-- The typed pipeline followed by the post-pipeline normalisations: the
    match-arm control-flow wrap, the rewrite of irrefutable tuple matches into
    `let` chains, the newtype-projection elision and the let-fold-return
    flattening. Every backend reads this term or its erasure.

    `tIrrefutableTupleMatch` commutes with erasure
    (`tIrrefutableTupleMatch_erase`) and its rewrite of a node refines the node
    under `denote'` (`IrrefutableTupleMatch.denote'_rewriteSite`).
    `tElideToNamedProj` is the identity after erasure. `tFlattenLetFoldReturn`
    is a total `fuel`-bounded function; its four rewrites preserve the untyped
    denotation (`flattenA_denote`..`flattenD_denote` in
    `Hax/Phase/FlattenLetFoldReturn.lean`, A and D under the `noVarRef "_"`
    freshness condition), and the whole pass satisfies
    `flattenLetFoldReturn_denote`
    (`noVarRef "_" e → Rel "_" (denote (flattenLetFoldReturn k e)) (denote e)`)
    on the untyped twin. A fixed-fuel erase lemma does not hold for every fuel
    (`ann`/`namedProj` nodes consume typed-side fuel that `erase` removes), so
    that theorem is stated on the untyped twin. -/
def tPipelineFull (newtypes : HaxAdapter.NewtypeMap) (e : TExpr) : TExpr :=
  let inner :=
    tElideToNamedProj newtypes (tIrrefutableTupleMatch (tWrapMatchArmsCF (tPipeline e)))
  -- The fuel is a quadratic bound in the AST size, which exceeds the
  -- recursion depth, so the result is the rewrite fixpoint.
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

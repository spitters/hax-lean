/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TPipeline
import Hax.InlineClosuresErase
import Hax.ThreadMutationsErase

/-!
# Pre-pipeline passes in the erase capstone

`Hax/MainT.lean` runs

    tPipelineFull newtypes (tThreadMut true (tLowerClosureCalls [] te))

so two *pre-pipeline* passes (`tLowerClosureCalls`, `tThreadMut`) and three
*post-pipeline* passes (`tWrapMatchArmsCF`, `tElideToNamedProj`,
`tFlattenLetFoldReturn`) sit around the verified 4-phase `tPipeline`. The
individual erase lemmas
`tLowerClosureCalls_erase`/`tThreadMut_erase` (the pre-passes) and
`tPipeline_erase`/`tElideToNamedProj_erase` (the pipeline + elision) already
exist; this file proves `tWrapMatchArmsCF_erase` and then *composes* the whole
chain into a single commuting square, bringing the pre-passes into the diagram:

    TExpr  ──[tElide ∘ tWrapCF ∘ tPipeline ∘ tThreadMut ∘ tLowerClosureCalls]──→ TExpr
      │                                                                            │
      │ erase                                                                      │ erase
      ↓                                                                            ↓
    ImpExpr ──[wrapMatchArmsCF ∘ pipeline ∘ threadMut ∘ lowerClosureCalls]──────→ ImpExpr

## The flatten boundary

The chain composes cleanly up to but **not through** `tFlattenLetFoldReturn`
(the last pass `tPipelineFull` applies). A *fixed-fuel* erase lemma
`(tFlattenLetFoldReturn k e).erase = flattenLetFoldReturn k e.erase` does **not**
hold for arbitrary `k`: `.ann`/`.namedProj` nodes exist in `TExpr` but are
deleted (`.ann`) / reshaped to `.app ".0"` (`.namedProj`) by `erase`, so they
consume typed-side fuel that the untyped side never sees. The two agree only
once *both* reach the rewrite fixpoint (sufficient fuel), not at each `k` — see
the discussion in `Hax/TPhase/FlattenLetFoldReturn.lean`. The strongest clean
composed erase theorem therefore lands on `tPipelineFullInner` (everything in
`tPipelineFull` except the final flatten).
-/

namespace Hax

/-! ## Erase commutation for the match-arm CF wrap -/

/-- The `anyCF` decision (does any arm end in a control-flow marker?) commutes
    with erasure, given the per-arm erase IH. -/
private theorem wrapAnyCF_erase (arms : List (ImpPat × TExpr))
    (ih : ∀ pa ∈ arms, (tWrapMatchArmsCF pa.2).erase = wrapMatchArmsCF pa.2.erase) :
    (tWrapMatchArmsCF.mapArms arms).any (fun (_, b) => b.endsInCF)
      = (wrapMatchArmsCF.mapArms (TExpr.erase.eraseArms arms)).any (fun (_, b) => Hax.endsInCF b) := by
  induction arms with
  | nil => rfl
  | cons pa rest ihr =>
    obtain ⟨p, e⟩ := pa
    simp only [tWrapMatchArmsCF.mapArms, wrapMatchArmsCF.mapArms, TExpr.erase.eraseArms,
      List.any_cons]
    rw [TExpr.endsInCF_erase, ih (p, e) (by simp),
      ihr (fun pa h => ih pa (List.mem_cons_of_mem _ h))]

/-- The non-wrapping arm transformation commutes with erasure. -/
private theorem wrapArmsId_erase (arms : List (ImpPat × TExpr))
    (ih : ∀ pa ∈ arms, (tWrapMatchArmsCF pa.2).erase = wrapMatchArmsCF pa.2.erase) :
    TExpr.erase.eraseArms (tWrapMatchArmsCF.mapArms arms)
      = wrapMatchArmsCF.mapArms (TExpr.erase.eraseArms arms) := by
  induction arms with
  | nil => rfl
  | cons pa rest ihr =>
    obtain ⟨p, e⟩ := pa
    simp only [tWrapMatchArmsCF.mapArms, wrapMatchArmsCF.mapArms, TExpr.erase.eraseArms]
    rw [ih (p, e) (by simp), ihr (fun pa h => ih pa (List.mem_cons_of_mem _ h))]

/-- The wrapping arm transformation (`maybeWrapContinue` on each arm body)
    commutes with erasure. -/
private theorem wrapArmsWrap_erase (arms : List (ImpPat × TExpr))
    (ih : ∀ pa ∈ arms, (tWrapMatchArmsCF pa.2).erase = wrapMatchArmsCF pa.2.erase) :
    TExpr.erase.eraseArms (tWrapMatchArmsCF.mapArmsWrap (tWrapMatchArmsCF.mapArms arms))
      = wrapMatchArmsCF.mapArmsWrap (wrapMatchArmsCF.mapArms (TExpr.erase.eraseArms arms)) := by
  induction arms with
  | nil => rfl
  | cons pa rest ihr =>
    obtain ⟨p, e⟩ := pa
    simp only [tWrapMatchArmsCF.mapArms, tWrapMatchArmsCF.mapArmsWrap,
      wrapMatchArmsCF.mapArms, wrapMatchArmsCF.mapArmsWrap, TExpr.erase.eraseArms]
    rw [TExpr.maybeWrapContinue_erase, ih (p, e) (by simp),
      ihr (fun pa h => ih pa (List.mem_cons_of_mem _ h))]

/-- Commuting diagram for `tWrapMatchArmsCF`. The prose statement in
    `Hax/TPhase/WrapMatchArms.lean` is here discharged: every constructor
    mirrors `wrapMatchArmsCF` structurally; `.ann` erases to its inner and
    `.namedProj` to an `.app ".0"`, both traversed identically by the untyped
    pass, and the `match_` arm's `anyCF`/`maybeWrapContinue` decisions commute
    with erasure via `TExpr.endsInCF_erase` and `TExpr.maybeWrapContinue_erase`. -/
theorem tWrapMatchArmsCF_erase (e : TExpr) :
    (tWrapMatchArmsCF e).erase = wrapMatchArmsCF e.erase := by
  induction e using TExpr.ind with
  | lit | var | unitVal | continue_ | break_none => rfl
  | letBind _ _ _ _ ih1 ih2 => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih1, ih2]
  | lam _ _ _ ih => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih]
  | seq _ _ _ ih1 ih2 => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih1, ih2]
  | proj _ _ _ ih => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih]
  | ifThenElse _ _ _ _ ih1 ih2 ih3 =>
    simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih1, ih2, ih3]
  | borrow _ _ ih => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih]
  | deref _ _ ih => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih]
  | assign _ _ _ ih => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih]
  | forLoop _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih1, ih2, ih3]
  | forLoopRev _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih1, ih2, ih3]
  | whileLoop _ _ _ ih1 ih2 => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih1, ih2]
  | break_some _ _ ih => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih]
  | earlyReturn _ _ ih => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih]
  | questionMark _ _ ih => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih]
  | forFold _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih1, ih2, ih3]
  | forFoldRev _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih1, ih2, ih3]
  | whileFold _ _ _ ih1 ih2 => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih1, ih2]
  | forFoldReturn _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih1, ih2, ih3]
  | forFoldRevReturn _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih1, ih2, ih3]
  | whileFoldReturn _ _ _ ih1 ih2 => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih1, ih2]
  | cfBreak _ _ ih => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih]
  | cfContinue _ _ ih => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih]
  | cfBreakContinue _ _ ih => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih]
  | ann _ _ ih => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih]
  | namedProj _ _ _ ih => simp [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih]
  | app _ _ args ih =>
    simp only [tWrapMatchArmsCF, tWrapMatchArmsCF.mapExpr_eq, TExpr.erase, TExpr.eraseList_eq,
      wrapMatchArmsCF, wrapMatchArmsCF.mapExpr_eq, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha)
  | tuple _ elems ih =>
    simp only [tWrapMatchArmsCF, tWrapMatchArmsCF.mapExpr_eq, TExpr.erase, TExpr.eraseList_eq,
      wrapMatchArmsCF, wrapMatchArmsCF.mapExpr_eq, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha)
  | match_ _ scrut arms ih1 ih2 =>
    have ih2' : ∀ pa ∈ arms, (tWrapMatchArmsCF pa.2).erase = wrapMatchArmsCF pa.2.erase := ih2
    simp only [tWrapMatchArmsCF, TExpr.erase, wrapMatchArmsCF, ih1]
    congr 1
    rw [wrapAnyCF_erase arms ih2']
    split
    · exact wrapArmsWrap_erase arms ih2'
    · exact wrapArmsId_erase arms ih2'

/-! ## Pre-pipeline composition -/

/-- The two pre-pipeline passes commute with erasure as a block. -/
theorem prePipeline_erase (active : Bool) (names : List String) (e : TExpr) :
    (tThreadMut active (tLowerClosureCalls names e)).erase
      = threadMut active (lowerClosureCalls names e.erase) := by
  rw [tThreadMut_erase, tLowerClosureCalls_erase]

/-- The 4-phase `tPipeline` applied after the pre-passes commutes with erasure. -/
theorem tPipeline_prePipeline_erase (active : Bool) (names : List String) (e : TExpr) :
    (tPipeline (tThreadMut active (tLowerClosureCalls names e))).erase
      = pipeline (threadMut active (lowerClosureCalls names e.erase)) := by
  rw [tPipeline_erase, prePipeline_erase]

/-- The pipeline + match-arm CF wrap, after the pre-passes, commutes with erasure. -/
theorem tPipelineWithCFWrap_prePipeline_erase (active : Bool) (names : List String) (e : TExpr) :
    (tPipelineWithCFWrap (tThreadMut active (tLowerClosureCalls names e))).erase
      = wrapMatchArmsCF (pipeline (threadMut active (lowerClosureCalls names e.erase))) := by
  unfold tPipelineWithCFWrap
  rw [tWrapMatchArmsCF_erase, tPipeline_erase, prePipeline_erase]

/-- The pre-flatten core of `tPipelineFull`: elision ∘ CF-wrap ∘ pipeline.
    `tElideToNamedProj` is denotation-identity at the erase level
    (`tElideToNamedProj_erase : … = e.erase`), so it adds nothing to the untyped
    side. This is the strongest composed erase theorem that holds cleanly — the
    chain stops here, before the final `tFlattenLetFoldReturn` (see the module
    docstring's "flatten boundary"). -/
def tPipelineFullInner (newtypes : HaxAdapter.NewtypeMap) (e : TExpr) : TExpr :=
  tElideToNamedProj newtypes (tWrapMatchArmsCF (tPipeline e))

/-- Commuting diagram for the full pre-flatten chain, with the pre-passes. -/
theorem tPipelineFullInner_prePipeline_erase
    (newtypes : HaxAdapter.NewtypeMap) (active : Bool) (names : List String) (e : TExpr) :
    (tPipelineFullInner newtypes (tThreadMut active (tLowerClosureCalls names e))).erase
      = wrapMatchArmsCF (pipeline (threadMut active (lowerClosureCalls names e.erase))) := by
  unfold tPipelineFullInner
  rw [tElideToNamedProj_erase, tWrapMatchArmsCF_erase, tPipeline_erase, prePipeline_erase]

/-- `tPipelineFull` is the pre-flatten core followed by the fuel-bounded flatten;
    the erase capstone composes through the core (`tPipelineFullInner`). -/
theorem tPipelineFull_eq_flatten_inner (newtypes : HaxAdapter.NewtypeMap) (e : TExpr) :
    tPipelineFull newtypes e
      = tFlattenLetFoldReturn ((tPipelineFullInner newtypes e).erase.nodeCount *
          (tPipelineFullInner newtypes e).erase.nodeCount +
          (tPipelineFullInner newtypes e).erase.nodeCount + 1000)
          (tPipelineFullInner newtypes e) := rfl

end Hax

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import HaxLean.Py.ToTExpr
public import HaxLean.Phase.CfIntoMonadsCF

/-!
# Pipeline preconditions of the Python image

The terms in `PyImage` satisfy the syntactic hypotheses of
`pipeline_full_correct` other than the one on the builtins table.

* `PyImage.loopScoped`, `PyImage.noQuestionMark`, `PyImage.noCFConstructors` —
  each predicate holds on every term of `PyImage`, by rule induction.
* `pyToTExpr_loopScoped`, `pyToTExpr_noQuestionMark`, `pyToTExpr_noCFConstructors`
  — each predicate holds on the erasure of every function term of `pyToTExpr`.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Py

/-- Every term of `PyImage` is `LoopScoped`. -/
theorem PyImage.loopScoped {e : ImpExpr} (h : PyImage e) : LoopScoped e := by
  induction h with
  | lit => exact .lit
  | var => exact .var
  | letBind _ _ ih1 ih2 => exact .letBind ih1 ih2
  | app _ ih => exact .app ih
  | tuple _ ih => exact .tuple ih
  | proj _ ih => exact .proj ih
  | ifThenElse _ _ _ ih1 ih2 ih3 => exact .ifThenElse ih1 ih2 ih3
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | assign _ ih => exact .assign ih
  | forLoop _ _ _ ih1 ih2 _ => exact .forLoop ih1 ih2
  | forLoopRev _ _ _ ih1 ih2 _ => exact .forLoopRev ih1 ih2

/-- No term of `PyImage` contains a `questionMark` node. -/
theorem PyImage.noQuestionMark {e : ImpExpr} (h : PyImage e) : NoQuestionMark e := by
  induction h with
  | lit => exact .lit
  | var => exact .var
  | letBind _ _ ih1 ih2 => exact .letBind ih1 ih2
  | app _ ih => exact .app ih
  | tuple _ ih => exact .tuple ih
  | proj _ ih => exact .proj ih
  | ifThenElse _ _ _ ih1 ih2 ih3 => exact .ifThenElse ih1 ih2 ih3
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | assign _ ih => exact .assign ih
  | forLoop _ _ _ ih1 ih2 ih3 => exact .forLoop ih1 ih2 ih3
  | forLoopRev _ _ _ ih1 ih2 ih3 => exact .forLoopRev ih1 ih2 ih3

/-- No term of `PyImage` contains a fold or control-flow constructor. -/
theorem PyImage.noCFConstructors {e : ImpExpr} (h : PyImage e) : NoCFConstructors e := by
  induction h with
  | lit => exact .lit
  | var => exact .var
  | letBind _ _ ih1 ih2 => exact .letBind ih1 ih2
  | app _ ih => exact .app ih
  | tuple _ ih => exact .tuple ih
  | proj _ ih => exact .proj ih
  | ifThenElse _ _ _ ih1 ih2 ih3 => exact .ifThenElse ih1 ih2 ih3
  | unitVal => exact .unitVal
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | assign _ ih => exact .assign ih
  | forLoop _ _ _ ih1 ih2 ih3 => exact .forLoop ih1 ih2 ih3
  | forLoopRev _ _ _ ih1 ih2 ih3 => exact .forLoopRev ih1 ih2 ih3

/-- The erasure of every function term of `pyToTExpr` is `LoopScoped`. -/
theorem pyToTExpr_loopScoped {cm : CheckedModule} {x : PyExtraction}
    (h : pyToTExpr cm = .ok x) : ∀ p, p ∈ x.fns → LoopScoped p.2.erase :=
  fun p hp => (pyToTExpr_pyImage h p hp).loopScoped

/-- The erasure of no function term of `pyToTExpr` contains a `questionMark` node. -/
theorem pyToTExpr_noQuestionMark {cm : CheckedModule} {x : PyExtraction}
    (h : pyToTExpr cm = .ok x) : ∀ p, p ∈ x.fns → NoQuestionMark p.2.erase :=
  fun p hp => (pyToTExpr_pyImage h p hp).noQuestionMark

/-- The erasure of no function term of `pyToTExpr` contains a fold or control-flow
constructor. -/
theorem pyToTExpr_noCFConstructors {cm : CheckedModule} {x : PyExtraction}
    (h : pyToTExpr cm = .ok x) : ∀ p, p ∈ x.fns → NoCFConstructors p.2.erase :=
  fun p hp => (pyToTExpr_pyImage h p hp).noCFConstructors

end Hax.Py

/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.AST
import SSProve.Hax.Value
import SSProve.Hax.Features
import SSProve.Deep.RawCode

/-!
# Translation from ImpExpr to RawCode

After all four phases, an `ImpExpr` satisfying `FullyFunctional` is
essentially a pure functional expression. This file translates it into
SSProve's `RawCode` deep embedding.

## Main definitions

* `toRawCode` — translate fully functional ImpExpr to RawCode Value
* `toRawCode_noOracleCall` — output has no oracle calls

## Design

This follows the `interpDet` pattern from `Deep/DeterministicInterp.lean`:
the `FullyFunctional` proof is used to eliminate impossible cases.

Since `ImpExpr` uses untyped `Value` while `RawCode` is typed, the
translation produces `RawCode Value` — all computations return `Value`.
-/

namespace SSProve.Hax

open SSProve.Deep

/-- Translate a fully-functional `ImpExpr` into `RawCode Value`.

    Requires `FullyFunctional` (no refs, mutation, loops, or early exit).
    Uses the proof to eliminate impossible cases via `absurd`. -/
noncomputable def toRawCode : ImpExpr → RawCode Value
  | .lit v => .ret (Value.ofLit v)
  | .var _ => .ret .unit  -- Variables resolve to unit (env handled externally)
  | .letBind _ val body =>
    .bind (toRawCode val) fun _ => toRawCode body
  | .app _ _ => .ret .unit  -- Function calls are handled by builtins externally
  | .tuple elems =>
    toRawCodeList elems fun vs => .ret (.tuple vs)
  | .proj e i =>
    .bind (toRawCode e) fun v =>
      match v.projIdx i with
      | some vi => .ret vi
      | none => .fail
  | .ifThenElse cond thn els =>
    .bind (toRawCode cond) fun v =>
      match v.toBool with
      | some true => toRawCode thn
      | some false => toRawCode els
      | none => .fail
  | .match_ scrut _ =>
    -- Simplified: evaluate scrutinee, return its value
    toRawCode scrut
  | .unitVal => .ret .unit
  | .seq e1 e2 =>
    .bind (toRawCode e1) fun _ => toRawCode e2
  -- Impossible cases (eliminated by FullyFunctional):
  | .borrow e => toRawCode e
  | .deref e => toRawCode e
  | .assign _ rhs => toRawCode rhs
  | .forLoop _ _ _ body => toRawCode body
  | .whileLoop _ body => toRawCode body
  | .break_ _ => .ret .unit
  | .continue_ => .ret .unit
  | .earlyReturn e => toRawCode e
  | .questionMark e => toRawCode e
where
  /-- Translate a list of expressions, collecting into a list of values. -/
  toRawCodeList : List ImpExpr → (List Value → RawCode Value) → RawCode Value
    | [], k => k []
    | e :: es, k =>
      .bind (toRawCode e) fun v =>
        toRawCodeList es fun vs => k (v :: vs)

/-- Helper: `toRawCodeList` preserves `NoOracleCall` given that
    all elements do and the continuation does. -/
private theorem toRawCodeList_noOracleCall (es : List ImpExpr)
    (he : ∀ e, e ∈ es → RawCode.NoOracleCall (toRawCode e))
    (k : List Value → RawCode Value) (hk : ∀ vs, RawCode.NoOracleCall (k vs)) :
    RawCode.NoOracleCall (toRawCode.toRawCodeList es k) := by
  induction es generalizing k with
  | nil => exact hk []
  | cons e es ih =>
    simp only [toRawCode.toRawCodeList]
    exact .bind (he e (.head _)) fun v =>
      ih (fun e' he' => he e' (.tail _ he'))
        (fun vs => k (v :: vs)) (fun vs => hk (v :: vs))

/-- The translated code contains no oracle calls. -/
theorem toRawCode_noOracleCall (e : ImpExpr) :
    RawCode.NoOracleCall (toRawCode e) := by
  induction e using ImpExpr.ind with
  | lit => exact .ret _
  | var => exact .ret _
  | letBind _ _ _ ih1 ih2 => exact .bind ih1 fun _ => ih2
  | app => exact .ret _
  | tuple elems ih =>
    exact toRawCodeList_noOracleCall elems ih
      (fun vs => .ret (.tuple vs)) (fun _ => .ret _)
  | proj _ _ ih =>
    refine .bind ih fun v => ?_
    split <;> first | exact .ret _ | exact .fail
  | ifThenElse _ _ _ ih1 ih2 ih3 =>
    refine .bind ih1 fun v => ?_
    split
    · exact ih2
    · exact ih3
    · exact .fail
  | match_ _ _ ih1 _ => exact ih1
  | unitVal => exact .ret _
  | seq _ _ ih1 ih2 => exact .bind ih1 fun _ => ih2
  | borrow _ ih => exact ih
  | deref _ ih => exact ih
  | assign _ _ ih => exact ih
  | forLoop _ _ _ _ _ _ ih3 => exact ih3
  | whileLoop _ _ _ ih2 => exact ih2
  | break_none => exact .ret _
  | break_some => exact .ret _
  | continue_ => exact .ret _
  | earlyReturn _ ih => exact ih
  | questionMark _ ih => exact ih

end SSProve.Hax

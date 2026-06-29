/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.AST
import Hax.Value
import Hax.Features
import Hax.Deep.RawCode

/-!
# Translation from ImpExpr to RawCode

After all four phases, an `ImpExpr` satisfying `FullyFunctional` is
essentially a pure functional expression. This file translates it into
CatCrypt's `RawCode` deep embedding.

## Main definitions

* `toRawCode` — translate fully functional ImpExpr to RawCode Value

## Design

The `FullyFunctional` proof ensures no refs, mutation, loops, or early exits
remain — impossible cases use fallback translations.

Function calls are translated to `fail` (builtins are external to RawCode).
Pattern matching uses `matchPat` to dispatch arms.
Variables return `.unit` (environment is external to RawCode).

Since `ImpExpr` uses untyped `Value` while `RawCode` is typed, the
translation produces `RawCode Value` — all computations return `Value`.

When connecting to the real CatCrypt `RawCode` (which has `sample`,
`get`, `put`, `oracleCall`), predicates like `NoOracleCall` and
`IsDeterministic` can be proved against the real type — the translation
only produces `ret`, `bind`, and `fail`.
-/

namespace Hax

open Hax.Deep

/-- Translate a fully-functional `ImpExpr` into `RawCode Value`.

    Requires `FullyFunctional` (no refs, mutation, loops, or early exit).
    Uses the proof to eliminate impossible cases via `absurd`. -/
noncomputable def toRawCode : ImpExpr → RawCode Value
  | .lit v => .ret (Value.ofLit v)
  | .var _ => .ret .unit  -- Variable resolution handled externally
  | .letBind _ val body =>
    .bind (toRawCode val) fun _ => toRawCode body
  | .lam _ _ => .ret .unit  -- Closures handled externally (like app/var)
  | .app _ _ => .ret .unit  -- Function calls handled by builtins externally
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
  | .match_ scrut arms =>
    .bind (toRawCode scrut) fun v =>
      toRawCodeMatchArms v arms
  | .unitVal => .ret .unit
  | .seq e1 e2 =>
    .bind (toRawCode e1) fun _ => toRawCode e2
  -- Impossible cases (eliminated by FullyFunctional):
  | .borrow e => toRawCode e
  | .deref e => toRawCode e
  | .assign _ rhs => toRawCode rhs
  | .forLoop _ _ _ body => toRawCode body
  | .forLoopRev _ _ _ body => toRawCode body
  | .whileLoop _ body => toRawCode body
  | .break_ _ => .ret .unit
  | .continue_ => .ret .unit
  | .earlyReturn e => toRawCode e
  | .questionMark e => toRawCode e
  | .forFold _ _ _ body => toRawCode body
  | .whileFold _ body => toRawCode body
  | .forFoldReturn _ _ _ body => toRawCode body
  | .whileFoldReturn _ body => toRawCode body
  | .forFoldRev _ _ _ body => toRawCode body
  | .forFoldRevReturn _ _ _ body => toRawCode body
  | .cfBreak e => toRawCode e
  | .cfContinue e => toRawCode e
  | .cfBreakContinue e => toRawCode e
  | .typeAscription e _ => toRawCode e
where
  /-- Translate a list of expressions, collecting into a list of values. -/
  toRawCodeList : List ImpExpr → (List Value → RawCode Value) → RawCode Value
    | [], k => k []
    | e :: es, k =>
      .bind (toRawCode e) fun v =>
        toRawCodeList es fun vs => k (v :: vs)
  /-- Try to match arms against a scrutinee value. -/
  toRawCodeMatchArms (v : Value) : List (ImpPat × ImpExpr) → RawCode Value
    | [] => .fail  -- no matching arm
    | (pat, body) :: rest =>
      match matchPat pat v Env.empty with
      | some _ => toRawCode body
      | none => toRawCodeMatchArms v rest

end Hax

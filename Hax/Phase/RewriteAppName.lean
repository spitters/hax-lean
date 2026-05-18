/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.AST

/-!
# Post-pipeline pass: `rewriteAppName`

Renames `.app f args` to `.app newName args` for every occurrence of
`f == oldName`. Pure structural recursion over `ImpExpr` — no type
information consulted.

## Denotation-preservation

This transformation is **conditionally** denotation-preserving: it preserves
`denote` iff `oldName` and `newName` denote the same function in the
runtime environment. The condition is the responsibility of the caller
(typically PrettyPrintT, which only invokes the rewriter when it knows
the two names resolve to the same Lean identifier — e.g. a method-call
desugar or a module-qualification step).

We do not state the conditional theorem here; it lives at the caller
site where the runtime invariant is available.

Moved out of `PrettyPrint.lean` (TCB) into `Hax/Phase/` (verified core)
on 2026-05-18 to reduce TCB by file convention; the conditional proof
is a follow-up.
-/

namespace Hax

/-- Rewrite every `.app oldName args` to `.app newName args`. Explicit
    per-constructor recursion + named helpers (mapExpr/mapArms) so that
    Lean's structural-recursion termination check sees the recursive
    calls and `simp` can generate per-constructor equation lemmas. -/
def rewriteAppName (oldName newName : String) : ImpExpr → ImpExpr
  | .lit v => .lit v
  | .var n => .var n
  | .unitVal => .unitVal
  | .continue_ => .continue_
  | .break_ none => .break_ none
  | .break_ (some e) => .break_ (some (rewriteAppName oldName newName e))
  | .app f args =>
    let f' := if f == oldName then newName else f
    .app f' (mapExpr oldName newName args)
  | .letBind n v body =>
    .letBind n (rewriteAppName oldName newName v) (rewriteAppName oldName newName body)
  | .seq a b => .seq (rewriteAppName oldName newName a) (rewriteAppName oldName newName b)
  | .ifThenElse c t e =>
    .ifThenElse (rewriteAppName oldName newName c)
      (rewriteAppName oldName newName t) (rewriteAppName oldName newName e)
  | .tuple es => .tuple (mapExpr oldName newName es)
  | .proj e i => .proj (rewriteAppName oldName newName e) i
  | .match_ scrut arms =>
    .match_ (rewriteAppName oldName newName scrut) (mapArms oldName newName arms)
  | .borrow e => .borrow (rewriteAppName oldName newName e)
  | .deref e => .deref (rewriteAppName oldName newName e)
  | .assign n rhs => .assign n (rewriteAppName oldName newName rhs)
  | .forLoop v lo hi body =>
    .forLoop v (rewriteAppName oldName newName lo)
      (rewriteAppName oldName newName hi) (rewriteAppName oldName newName body)
  | .forLoopRev v lo hi body =>
    .forLoopRev v (rewriteAppName oldName newName lo)
      (rewriteAppName oldName newName hi) (rewriteAppName oldName newName body)
  | .whileLoop c body =>
    .whileLoop (rewriteAppName oldName newName c) (rewriteAppName oldName newName body)
  | .earlyReturn e => .earlyReturn (rewriteAppName oldName newName e)
  | .questionMark e => .questionMark (rewriteAppName oldName newName e)
  | .forFold v lo hi body =>
    .forFold v (rewriteAppName oldName newName lo)
      (rewriteAppName oldName newName hi) (rewriteAppName oldName newName body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (rewriteAppName oldName newName lo)
      (rewriteAppName oldName newName hi) (rewriteAppName oldName newName body)
  | .whileFold c body =>
    .whileFold (rewriteAppName oldName newName c) (rewriteAppName oldName newName body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (rewriteAppName oldName newName lo)
      (rewriteAppName oldName newName hi) (rewriteAppName oldName newName body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (rewriteAppName oldName newName lo)
      (rewriteAppName oldName newName hi) (rewriteAppName oldName newName body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (rewriteAppName oldName newName c) (rewriteAppName oldName newName body)
  | .cfBreak e => .cfBreak (rewriteAppName oldName newName e)
  | .cfContinue e => .cfContinue (rewriteAppName oldName newName e)
  | .cfBreakContinue e => .cfBreakContinue (rewriteAppName oldName newName e)
where
  mapExpr (oldName newName : String) : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => rewriteAppName oldName newName e :: mapExpr oldName newName es
  mapArms (oldName newName : String) : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, rewriteAppName oldName newName e) :: mapArms oldName newName rest

@[simp] theorem rewriteAppName.mapExpr_eq (oldName newName : String) (es : List ImpExpr) :
    rewriteAppName.mapExpr oldName newName es = es.map (rewriteAppName oldName newName) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [rewriteAppName.mapExpr, ih]

@[simp] theorem rewriteAppName.mapArms_eq (oldName newName : String)
    (arms : List (ImpPat × ImpExpr)) :
    rewriteAppName.mapArms oldName newName arms =
      arms.map fun (p, e) => (p, rewriteAppName oldName newName e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [rewriteAppName.mapArms, ih]

end Hax

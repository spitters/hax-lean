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

/-- Rewrite every `.app oldName args` to `.app newName args`. -/
partial def rewriteAppName (oldName newName : String) : ImpExpr → ImpExpr
  | .app f args =>
    let f' := if f == oldName then newName else f
    .app f' (args.map (rewriteAppName oldName newName))
  | .letBind n v body =>
    .letBind n (rewriteAppName oldName newName v) (rewriteAppName oldName newName body)
  | .seq a b => .seq (rewriteAppName oldName newName a) (rewriteAppName oldName newName b)
  | .ifThenElse c t e =>
    .ifThenElse (rewriteAppName oldName newName c)
      (rewriteAppName oldName newName t) (rewriteAppName oldName newName e)
  | .whileFold c body =>
    .whileFold (rewriteAppName oldName newName c) (rewriteAppName oldName newName body)
  | .forFold v lo hi body =>
    .forFold v (rewriteAppName oldName newName lo)
      (rewriteAppName oldName newName hi) (rewriteAppName oldName newName body)
  | .tuple es => .tuple (es.map (rewriteAppName oldName newName))
  | .proj e i => .proj (rewriteAppName oldName newName e) i
  | .match_ scrut arms =>
    .match_ (rewriteAppName oldName newName scrut)
      (arms.map fun (p, b) => (p, rewriteAppName oldName newName b))
  | .cfBreak e => .cfBreak (rewriteAppName oldName newName e)
  | .cfContinue e => .cfContinue (rewriteAppName oldName newName e)
  | .cfBreakContinue e => .cfBreakContinue (rewriteAppName oldName newName e)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (rewriteAppName oldName newName lo)
      (rewriteAppName oldName newName hi) (rewriteAppName oldName newName body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (rewriteAppName oldName newName lo)
      (rewriteAppName oldName newName hi) (rewriteAppName oldName newName body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (rewriteAppName oldName newName lo)
      (rewriteAppName oldName newName hi) (rewriteAppName oldName newName body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (rewriteAppName oldName newName c) (rewriteAppName oldName newName body)
  | e => e

end Hax

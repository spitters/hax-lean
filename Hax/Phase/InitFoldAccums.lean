/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.AST

/-!
# Post-pipeline pass: `initMissingFoldAccums`

Walks an `ImpExpr` and inserts `let v := (0 : Int)` before any fold
whose accumulator body references a variable `v` not bound in the
enclosing scope. This is a cleanup pass that happens after `localMutation`
lifting introduces accumulator names whose initial value got separated
from the fold introduction.

## Denotation-preservation

Inserting `let v := 0` before a fold preserves `denote` iff the fold body
either doesn't observe the pre-init value of `v`, or assigns to `v` before
the first read. In practice this is always the case for accumulator names
introduced by `localMutation` (they get rebound before any read inside
the fold body). The condition is the responsibility of the caller; we
don't state the conditional theorem here.

Moved out of `PrettyPrint.lean` (TCB) into `Hax/Phase/` (verified core)
on 2026-05-18 to reduce TCB by file convention; the conditional proof
is a follow-up.
-/

namespace Hax

/-- Collect all variable names bound by let-bindings at the top level. -/
def collectBoundNamesT : ImpExpr → List String
  | .letBind n _ body => n :: collectBoundNamesT body
  | .seq a b => collectBoundNamesT a ++ collectBoundNamesT b
  | _ => []

/-- Left-spine depth of `.seq` nesting. Used as a secondary termination
    measure for `extractAccumNamesFromBody`, whose `.seq (.seq _ _) _`
    re-association case preserves `sizeOf` but strictly reduces this
    depth (LHS = `leftSeqDepth a + 2`, RHS = `leftSeqDepth a + 1`). -/
def leftSeqDepth : ImpExpr → Nat
  | .seq a _ => leftSeqDepth a + 1
  | _ => 0

/-- Helper for `extractAccumNamesFromBody`: extract names from a
    conditional branch's mutation pattern. -/
def extractCondMutsT : ImpExpr → List String
  | .seq (.seq a b) c => extractCondMutsT (.seq a (.seq b c))
  | .seq (.letBind n _ (.var v)) rest =>
    if n == v then n :: extractCondMutsT rest else extractCondMutsT rest
  | .seq .unitVal rest => extractCondMutsT rest
  | .seq _ rest => extractCondMutsT rest
  | .letBind n _ (.var v) => if n == v then [n] else []
  | .letBind _ _ body => extractCondMutsT body
  | .unitVal => []
  | _ => []
  termination_by e => (sizeOf e, leftSeqDepth e)
  decreasing_by all_goals
    first
    | (simp_wf; simp [leftSeqDepth]; omega)
    | (simp_wf; omega)

/-- Extract accumulator variable names from a fold body by detecting mutation
    patterns: `let n := <update>; n` where `n` is rebound to its updated value. -/
def extractAccumNamesFromBody : ImpExpr → List String
  | .seq (.seq a b) c => extractAccumNamesFromBody (.seq a (.seq b c))
  | .seq (.letBind n _ (.var v)) rest =>
    if n == v && !n.startsWith "_assign" then
      let restAccs := extractAccumNamesFromBody rest
      if restAccs.contains n then restAccs else n :: restAccs
    else extractAccumNamesFromBody rest
  | .seq (.ifThenElse _ thn _) rest =>
    let thnAccs := extractCondMutsT thn |>.filter (!·.startsWith "_assign")
    let restAccs := extractAccumNamesFromBody rest
    (thnAccs ++ restAccs).eraseDups
  | .seq _ rest => extractAccumNamesFromBody rest
  | .letBind n _ (.var v) =>
    if n == v && !n.startsWith "_assign" then [n] else []
  | .letBind _ _ body => extractAccumNamesFromBody body
  | .ifThenElse _ thn _ =>
    (extractCondMutsT thn).filter (!·.startsWith "_assign") |>.eraseDups
  | _ => []
  termination_by e => (sizeOf e, leftSeqDepth e)
  decreasing_by all_goals
    first
    | (simp_wf; simp [leftSeqDepth]; omega)
    | (simp_wf; omega)

/-- Walk an `ImpExpr` and insert `let v := (0 : Int)` before any fold whose
    accumulator references a variable not bound in the enclosing scope. -/
def initMissingFoldAccums (bound : List String := []) : ImpExpr → ImpExpr
  | .letBind n v body =>
    let v' := initMissingFoldAccums bound v
    let body' := initMissingFoldAccums (n :: bound) body
    .letBind n v' body'
  | .lam ps body => .lam ps (initMissingFoldAccums (ps ++ bound) body)
  | .seq a b =>
    let a' := initMissingFoldAccums bound a
    let boundsFromA := collectBoundNamesT a
    .seq a' (initMissingFoldAccums (bound ++ boundsFromA) b)
  | .forFold v lo hi body =>
    let lo' := initMissingFoldAccums bound lo
    let hi' := initMissingFoldAccums bound hi
    let body' := initMissingFoldAccums (v :: bound) body
    let fold := ImpExpr.forFold v lo' hi' body'
    let accumNames := extractAccumNamesFromBody body'
    let freeAccums := accumNames.filter fun n => !bound.contains n
    freeAccums.foldr (fun fv expr => .letBind fv (.lit (.int 0)) expr) fold
  | .forFoldRev v lo hi body =>
    let lo' := initMissingFoldAccums bound lo
    let hi' := initMissingFoldAccums bound hi
    let body' := initMissingFoldAccums (v :: bound) body
    let fold := ImpExpr.forFoldRev v lo' hi' body'
    let accumNames := extractAccumNamesFromBody body'
    let freeAccums := accumNames.filter fun n => !bound.contains n
    freeAccums.foldr (fun fv expr => .letBind fv (.lit (.int 0)) expr) fold
  | .forFoldReturn v lo hi body =>
    let lo' := initMissingFoldAccums bound lo
    let hi' := initMissingFoldAccums bound hi
    let body' := initMissingFoldAccums (v :: bound) body
    let fold := ImpExpr.forFoldReturn v lo' hi' body'
    let accumNames := extractAccumNamesFromBody body'
    let freeAccums := accumNames.filter fun n => !bound.contains n
    freeAccums.foldr (fun fv expr => .letBind fv (.lit (.int 0)) expr) fold
  | .forFoldRevReturn v lo hi body =>
    let lo' := initMissingFoldAccums bound lo
    let hi' := initMissingFoldAccums bound hi
    let body' := initMissingFoldAccums (v :: bound) body
    let fold := ImpExpr.forFoldRevReturn v lo' hi' body'
    let accumNames := extractAccumNamesFromBody body'
    let freeAccums := accumNames.filter fun n => !bound.contains n
    freeAccums.foldr (fun fv expr => .letBind fv (.lit (.int 0)) expr) fold
  | .ifThenElse c t e =>
    .ifThenElse (initMissingFoldAccums bound c)
      (initMissingFoldAccums bound t) (initMissingFoldAccums bound e)
  | .match_ scrut arms =>
    .match_ (initMissingFoldAccums bound scrut) (mapArms bound arms)
  | .whileFold c body =>
    .whileFold (initMissingFoldAccums bound c) (initMissingFoldAccums bound body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (initMissingFoldAccums bound c) (initMissingFoldAccums bound body)
  | .tuple es => .tuple (mapExpr bound es)
  | .proj e i => .proj (initMissingFoldAccums bound e) i
  | .app f args => .app f (mapExpr bound args)
  | .cfBreak e => .cfBreak (initMissingFoldAccums bound e)
  | .cfContinue e => .cfContinue (initMissingFoldAccums bound e)
  | .cfBreakContinue e => .cfBreakContinue (initMissingFoldAccums bound e)
  -- Pre-pipeline / leftover constructors. In practice these are eliminated
  -- by earlier phases (`dropReferences`, `localMutation`,
  -- `functionalizeLoops`, `cfIntoMonads`) before this pass runs, so the
  -- recursive cases below are defensive but operationally inert. The
  -- explicit recursion matches `Hax.tInitMissingFoldAccums` (TPhase) so
  -- `tInitMissingFoldAccums_erase` can commute past these nodes.
  | .borrow e => .borrow (initMissingFoldAccums bound e)
  | .deref e => .deref (initMissingFoldAccums bound e)
  | .assign n rhs => .assign n (initMissingFoldAccums bound rhs)
  | .forLoop v lo hi body =>
    .forLoop v (initMissingFoldAccums bound lo)
              (initMissingFoldAccums bound hi)
              (initMissingFoldAccums bound body)
  | .forLoopRev v lo hi body =>
    .forLoopRev v (initMissingFoldAccums bound lo)
                 (initMissingFoldAccums bound hi)
                 (initMissingFoldAccums bound body)
  | .whileLoop c body =>
    .whileLoop (initMissingFoldAccums bound c) (initMissingFoldAccums bound body)
  | .break_ (some e) => .break_ (some (initMissingFoldAccums bound e))
  | .earlyReturn e => .earlyReturn (initMissingFoldAccums bound e)
  | .questionMark e => .questionMark (initMissingFoldAccums bound e)
  | .typeAscription e ty => .typeAscription (initMissingFoldAccums bound e) ty
  -- True base cases: leaves with no subexpressions.
  | .lit v => .lit v
  | .var n => .var n
  | .unitVal => .unitVal
  | .break_ none => .break_ none
  | .continue_ => .continue_
where
  mapExpr (bound : List String) : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => initMissingFoldAccums bound e :: mapExpr bound es
  mapArms (bound : List String) : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, initMissingFoldAccums bound e) :: mapArms bound rest

@[simp] theorem initMissingFoldAccums.mapExpr_eq (bound : List String) (es : List ImpExpr) :
    initMissingFoldAccums.mapExpr bound es =
      es.map (initMissingFoldAccums bound) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [initMissingFoldAccums.mapExpr, ih]

@[simp] theorem initMissingFoldAccums.mapArms_eq (bound : List String)
    (arms : List (ImpPat × ImpExpr)) :
    initMissingFoldAccums.mapArms bound arms =
      arms.map fun (p, e) => (p, initMissingFoldAccums bound e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [initMissingFoldAccums.mapArms, ih]

end Hax

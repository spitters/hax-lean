/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.AST

/-!
# Free Variable Analysis

Computes free variables and mutated variables for `ImpExpr`.
Used by `localMutation` to determine which variables need
state-passing transformation.
-/

namespace SSProve.Hax

/-- Collect all free variables in an expression.
    Uses an accumulator to avoid nested recursion through List.flatMap. -/
def freeVars (e : ImpExpr) : List String :=
  go e []
where
  go : ImpExpr → List String → List String
    | .lit _, acc => acc
    | .var n, acc => n :: acc
    | .letBind n val body, acc => go val (go body acc |>.filter (· != n))
    | .app _ args, acc => goList args acc
    | .tuple elems, acc => goList elems acc
    | .proj e _, acc => go e acc
    | .ifThenElse c t e, acc => go c (go t (go e acc))
    | .match_ scrut arms, acc => go scrut (goArms arms acc)
    | .unitVal, acc => acc
    | .seq e1 e2, acc => go e1 (go e2 acc)
    | .borrow e, acc => go e acc
    | .deref e, acc => go e acc
    | .assign n rhs, acc => n :: go rhs acc
    | .forLoop v lo hi body, acc =>
      go lo (go hi (go body acc |>.filter (· != v)))
    | .forLoopRev v lo hi body, acc =>
      go lo (go hi (go body acc |>.filter (· != v)))
    | .whileLoop c body, acc => go c (go body acc)
    | .break_ (some e), acc => go e acc
    | .break_ none, acc => acc
    | .continue_, acc => acc
    | .earlyReturn e, acc => go e acc
    | .questionMark e, acc => go e acc
    | .forFold v lo hi body, acc =>
      go lo (go hi (go body acc |>.filter (· != v)))
    | .forFoldRev v lo hi body, acc =>
      go lo (go hi (go body acc |>.filter (· != v)))
    | .whileFold c body, acc => go c (go body acc)
    | .forFoldReturn v lo hi body, acc =>
      go lo (go hi (go body acc |>.filter (· != v)))
    | .forFoldRevReturn v lo hi body, acc =>
      go lo (go hi (go body acc |>.filter (· != v)))
    | .whileFoldReturn c body, acc => go c (go body acc)
    | .cfBreak e, acc => go e acc
    | .cfContinue e, acc => go e acc
    | .cfBreakContinue e, acc => go e acc
  goList : List ImpExpr → List String → List String
    | [], acc => acc
    | e :: es, acc => go e (goList es acc)
  goArms : List (ImpPat × ImpExpr) → List String → List String
    | [], acc => acc
    | (_, body) :: rest, acc => go body (goArms rest acc)

/-- Collect all variables that are assigned to (mutated). -/
def mutatedVars (e : ImpExpr) : List String :=
  go e []
where
  go : ImpExpr → List String → List String
    | .lit _, acc | .var _, acc | .unitVal, acc | .continue_, acc => acc
    | .letBind _ val body, acc => go val (go body acc)
    | .app _ args, acc => goList args acc
    | .tuple elems, acc => goList elems acc
    | .proj e _, acc => go e acc
    | .ifThenElse c t e, acc => go c (go t (go e acc))
    | .match_ scrut arms, acc => go scrut (goArms arms acc)
    | .seq e1 e2, acc => go e1 (go e2 acc)
    | .borrow e, acc => go e acc
    | .deref e, acc => go e acc
    | .assign n rhs, acc => n :: go rhs acc
    | .forLoop _ lo hi body, acc => go lo (go hi (go body acc))
    | .forLoopRev _ lo hi body, acc => go lo (go hi (go body acc))
    | .whileLoop c body, acc => go c (go body acc)
    | .break_ (some e), acc => go e acc
    | .break_ none, acc => acc
    | .earlyReturn e, acc => go e acc
    | .questionMark e, acc => go e acc
    | .forFold _ lo hi body, acc => go lo (go hi (go body acc))
    | .forFoldRev _ lo hi body, acc => go lo (go hi (go body acc))
    | .whileFold c body, acc => go c (go body acc)
    | .forFoldReturn _ lo hi body, acc => go lo (go hi (go body acc))
    | .forFoldRevReturn _ lo hi body, acc => go lo (go hi (go body acc))
    | .whileFoldReturn c body, acc => go c (go body acc)
    | .cfBreak e, acc => go e acc
    | .cfContinue e, acc => go e acc
    | .cfBreakContinue e, acc => go e acc
  goList : List ImpExpr → List String → List String
    | [], acc => acc
    | e :: es, acc => go e (goList es acc)
  goArms : List (ImpPat × ImpExpr) → List String → List String
    | [], acc => acc
    | (_, body) :: rest, acc => go body (goArms rest acc)

/-- Remove duplicates from a list of strings. -/
def dedupStrings : List String → List String
  | [] => []
  | x :: xs => if xs.contains x then dedupStrings xs else x :: dedupStrings xs

/-- Unique mutated variables. -/
def mutatedVarsUnique (e : ImpExpr) : List String :=
  dedupStrings (mutatedVars e)

end SSProve.Hax

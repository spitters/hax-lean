/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr
import Hax.TPhase.StructMetaT

/-!
# Typed phase: `tRewriteNewToStructCtor`

Typed analog of the untyped `rewriteNewToStructCtor` rewriter in
`Hax/PrettyPrint.lean`. Walks a `TExpr` and rewrites
`.app "new" args` to `.app "StructName" args` whenever the outer
node's type annotation identifies the producing struct.

## Key difference vs the untyped rewriter

The untyped version is heuristic: it filters `structMeta` by arity
match and, on ties, scores by matching argument variable names to
field names. The typed version is much sharper: it reads the
**outer type annotation `ty`** carried by `.mk (.app "new" args) ty`,
optionally unwrapping `.ref` wrappers, and dispatches on
`.adt structName _`. The struct must be known to `structMeta` for the
rewrite to fire.

Compared to the untyped pass:

* Sound by construction — no guessing.
* Independent of arity-counting and arg-name heuristics. `structMeta`
  is only consulted as a sanity check that the named struct is one we
  know about; callers may pass `[]` to disable the check entirely.

## Verification

This file intentionally omits an `erase` commuting theorem. The typed
rewriter consults the outer `ty`, while the untyped rewriter consults
`structMeta` arity and arg-name heuristics over the erased form. The
two agree on well-typed inputs (which is the whole point of the typed
phase), but a syntactic erase commuting equation does not hold without
a typing-invariant hypothesis on the input. We mark this as follow-up
once a `WellTyped` predicate over `TExpr × StructMeta` lands. The
sibling phase `tQualifyProjections` documents the same trade-off.
-/

namespace Hax

namespace TRewriteNewToStructCtor

/-- Strip leading `.ref` wrappers (any mutability) and return the
    underlying type. Mirrors how a `&T` or `&mut T` produced by a
    constructor call is transparently the same nominal struct as `T`. -/
def unwrapRefs : ImpType → ImpType
  | .ref inner _ => unwrapRefs inner
  | t => t

/-- `true` iff `structMeta` knows a struct named `sname`. -/
def structKnown (structMeta : StructMetaT) (sname : String) : Bool :=
  structMeta.any fun (n, _) => n == sname

/-- Resolve the constructor name for a `new` application at outer
    type `ty`. Returns `none` if no rewrite applies (so the caller
    keeps the original head `"new"`). -/
def resolveCtor
    (structMeta : StructMetaT) (ty : ImpType) : Option String :=
  match unwrapRefs ty with
  | .adt sname _ =>
    if structKnown structMeta sname then some sname else none
  | _ => none

end TRewriteNewToStructCtor

open TRewriteNewToStructCtor in
/-- Typed `new` → struct-ctor rewriter over `TExpr`. Rewrites every
    `.app "new" args` node whose outer type (modulo `.ref` wrappers) is
    `.adt sname _` with a known `sname` to `.app sname args`. Outer
    types are preserved on every node. Mirrors the structural recursion
    of `tRewriteAppName` and `tQualifyProjections`.

    No arity-counting or arg-name heuristics: the outer type annotation
    determines the producing struct uniquely. -/
def tRewriteNewToStructCtor (structMeta : StructMetaT) : TExpr → TExpr
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty =>
    .mk (.letBind n (tRewriteNewToStructCtor structMeta val)
                    (tRewriteNewToStructCtor structMeta body)) ty
  | .mk (.app f args) ty =>
    let args' := mapExpr structMeta args
    let f' :=
      if f == "new" ∧ !args'.isEmpty then
        match resolveCtor structMeta ty with
        | some sname => sname
        | none => f
      else f
    .mk (.app f' args') ty
  | .mk (.tuple elems) ty =>
    .mk (.tuple (mapExpr structMeta elems)) ty
  | .mk (.proj e i) ty =>
    .mk (.proj (tRewriteNewToStructCtor structMeta e) i) ty
  | .mk (.ifThenElse c t e) ty =>
    .mk (.ifThenElse (tRewriteNewToStructCtor structMeta c)
                     (tRewriteNewToStructCtor structMeta t)
                     (tRewriteNewToStructCtor structMeta e)) ty
  | .mk (.match_ scrut arms) ty =>
    .mk (.match_ (tRewriteNewToStructCtor structMeta scrut)
                 (mapArms structMeta arms)) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq e1 e2) ty =>
    .mk (.seq (tRewriteNewToStructCtor structMeta e1)
              (tRewriteNewToStructCtor structMeta e2)) ty
  | .mk (.borrow e) ty =>
    .mk (.borrow (tRewriteNewToStructCtor structMeta e)) ty
  | .mk (.deref e) ty =>
    .mk (.deref (tRewriteNewToStructCtor structMeta e)) ty
  | .mk (.assign n rhs) ty =>
    .mk (.assign n (tRewriteNewToStructCtor structMeta rhs)) ty
  | .mk (.forLoop v lo hi body) ty =>
    .mk (.forLoop v (tRewriteNewToStructCtor structMeta lo)
                    (tRewriteNewToStructCtor structMeta hi)
                    (tRewriteNewToStructCtor structMeta body)) ty
  | .mk (.forLoopRev v lo hi body) ty =>
    .mk (.forLoopRev v (tRewriteNewToStructCtor structMeta lo)
                       (tRewriteNewToStructCtor structMeta hi)
                       (tRewriteNewToStructCtor structMeta body)) ty
  | .mk (.whileLoop c body) ty =>
    .mk (.whileLoop (tRewriteNewToStructCtor structMeta c)
                    (tRewriteNewToStructCtor structMeta body)) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk (.break_ (some e)) ty =>
    .mk (.break_ (some (tRewriteNewToStructCtor structMeta e))) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty =>
    .mk (.earlyReturn (tRewriteNewToStructCtor structMeta e)) ty
  | .mk (.questionMark e) ty =>
    .mk (.questionMark (tRewriteNewToStructCtor structMeta e)) ty
  | .mk (.forFold v lo hi body) ty =>
    .mk (.forFold v (tRewriteNewToStructCtor structMeta lo)
                    (tRewriteNewToStructCtor structMeta hi)
                    (tRewriteNewToStructCtor structMeta body)) ty
  | .mk (.forFoldRev v lo hi body) ty =>
    .mk (.forFoldRev v (tRewriteNewToStructCtor structMeta lo)
                       (tRewriteNewToStructCtor structMeta hi)
                       (tRewriteNewToStructCtor structMeta body)) ty
  | .mk (.whileFold c body) ty =>
    .mk (.whileFold (tRewriteNewToStructCtor structMeta c)
                    (tRewriteNewToStructCtor structMeta body)) ty
  | .mk (.forFoldReturn v lo hi body) ty =>
    .mk (.forFoldReturn v (tRewriteNewToStructCtor structMeta lo)
                          (tRewriteNewToStructCtor structMeta hi)
                          (tRewriteNewToStructCtor structMeta body)) ty
  | .mk (.forFoldRevReturn v lo hi body) ty =>
    .mk (.forFoldRevReturn v (tRewriteNewToStructCtor structMeta lo)
                             (tRewriteNewToStructCtor structMeta hi)
                             (tRewriteNewToStructCtor structMeta body)) ty
  | .mk (.whileFoldReturn c body) ty =>
    .mk (.whileFoldReturn (tRewriteNewToStructCtor structMeta c)
                          (tRewriteNewToStructCtor structMeta body)) ty
  | .mk (.cfBreak e) ty =>
    .mk (.cfBreak (tRewriteNewToStructCtor structMeta e)) ty
  | .mk (.cfContinue e) ty =>
    .mk (.cfContinue (tRewriteNewToStructCtor structMeta e)) ty
  | .mk (.cfBreakContinue e) ty =>
    .mk (.cfBreakContinue (tRewriteNewToStructCtor structMeta e)) ty
  | .mk (.ann e) ty =>
    .mk (.ann (tRewriteNewToStructCtor structMeta e)) ty
  | .mk (.namedProj n e) ty =>
    .mk (.namedProj n (tRewriteNewToStructCtor structMeta e)) ty
where
  mapExpr (structMeta : StructMetaT) : List TExpr → List TExpr
    | [] => []
    | e :: es => tRewriteNewToStructCtor structMeta e
               :: mapExpr structMeta es
  mapArms (structMeta : StructMetaT) :
      List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest =>
      (p, tRewriteNewToStructCtor structMeta e)
        :: mapArms structMeta rest

@[simp] theorem tRewriteNewToStructCtor.mapExpr_eq
    (structMeta : StructMetaT) (es : List TExpr) :
    tRewriteNewToStructCtor.mapExpr structMeta es =
      es.map (tRewriteNewToStructCtor structMeta) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [tRewriteNewToStructCtor.mapExpr, ih]

@[simp] theorem tRewriteNewToStructCtor.mapArms_eq
    (structMeta : StructMetaT) (arms : List (ImpPat × TExpr)) :
    tRewriteNewToStructCtor.mapArms structMeta arms =
      arms.map fun (p, e) => (p, tRewriteNewToStructCtor structMeta e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [tRewriteNewToStructCtor.mapArms, ih]

-- NOTE: `tRewriteNewToStructCtor_erase` is intentionally not stated here.
-- The typed rewriter reads the outer `ty`, the untyped rewriter applies
-- arity- and arg-name-heuristic disambiguation over `structMeta` against
-- the erased form. These agree under a `WellTyped` predicate but not on
-- arbitrary inputs; the predicate is follow-up work. See the sibling
-- file `Hax/TPhase/QualifyProjections.lean` for the same trade-off.

end Hax

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr
import Hax.TPhase.StructMetaT

/-!
# Typed phase: `tQualifyProjections`

Typed analog of the untyped `qualifyProjections` rewriter in
`Hax/PrettyPrint.lean`. Walks a `TExpr` and qualifies ambiguous bare
projections of the form `.app ".field" [arg]` to
`.app "StructName.field" [arg]` whenever `"field"` is listed as
ambiguous across multiple structs.

## Key difference vs the untyped rewriter

The untyped version uses the heuristic `inferExprStructType` to guess
the struct from the surrounding context. The typed version is much
sharper: it reads the **type annotation `arg.ty`** carried by the typed
expression, optionally unwrapping `.ref` wrappers, and dispatches on
`.adt structName _`. The struct must have a matching field (looked up
in `structMeta`) for the qualification to fire.

Compared to the untyped pass:

* Sound by construction — no guessing.
* Independent of `ctx`. The parameter is accepted for API parity with
  the untyped signature so callers can plug both rewriters in at the
  same site, but it is ignored by the typed body.

## Verification

This file intentionally omits an `erase` commuting theorem. The typed
rewriter consults `arg.ty`, while the untyped rewriter consults the
heuristic `inferExprStructType (structMeta) (ctx.erase) arg.erase`. The
two agree in well-typed inputs (which is the whole point of the typed
phase), but a syntactic erase commuting equation does not hold without
a typing-invariant hypothesis on the input. We mark this as follow-up
once a `WellTyped` predicate over `TExpr × StructMeta` lands.
-/

namespace Hax

namespace TQualifyProjections

/-- Strip leading `.ref` wrappers (any mutability) and return the
    underlying type. Mirrors how Rust's projection sugar transparently
    auto-derefs through `&T` and `&mut T`. -/
def unwrapRefs : ImpType → ImpType
  | .ref inner _ => unwrapRefs inner
  | t => t

/-- `true` iff `structMeta` knows a struct `sname` with a field `fname`. -/
def structHasField (structMeta : StructMetaT) (sname fname : String) : Bool :=
  structMeta.any fun (n, fields) =>
    n == sname && fields.any (·.1 == fname)

/-- Resolve the qualified function name for a projection call.
    Returns `none` if no qualification applies (so the caller keeps the
    original head `f`). -/
def resolveQualified
    (structMeta : StructMetaT) (ambiguous : List String)
    (f : String) (argTy : ImpType) : Option String :=
  if !f.startsWith "." then none
  else
    let fname := (f.drop 1).toString
    if !ambiguous.contains fname then none
    else
      match unwrapRefs argTy with
      | .adt sname _ =>
        if structHasField structMeta sname fname then
          some s!"{sname}.{fname}"
        else none
      | _ => none

end TQualifyProjections

open TQualifyProjections in
/-- Typed projection qualifier over `TExpr`. Rewrites every
    `.app ".field" [arg]` node whose `arg.ty` (modulo `.ref` wrappers)
    is an `.adt sname _` with a known `field` to
    `.app "sname.field" [arg]`. Outer types are preserved on every
    node. Mirrors the structural recursion of `tRewriteAppName`.

    `ctx` is accepted for API parity with the untyped signature; the
    typed body reads `arg.ty` instead. -/
def tQualifyProjections
    (structMeta : StructMetaT) (ambiguous : List String) (_ctx : TExpr) :
    TExpr → TExpr
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty =>
    .mk (.letBind n (tQualifyProjections structMeta ambiguous _ctx val)
                    (tQualifyProjections structMeta ambiguous _ctx body)) ty
  | .mk (.app f args) ty =>
    -- Recurse first so the head-rewrite sees already-rewritten args.
    let args' := mapExpr structMeta ambiguous _ctx args
    let f' :=
      match args' with
      | [arg] =>
        match resolveQualified structMeta ambiguous f arg.ty with
        | some q => q
        | none => f
      | _ => f
    .mk (.app f' args') ty
  | .mk (.tuple elems) ty =>
    .mk (.tuple (mapExpr structMeta ambiguous _ctx elems)) ty
  | .mk (.proj e i) ty =>
    .mk (.proj (tQualifyProjections structMeta ambiguous _ctx e) i) ty
  | .mk (.ifThenElse c t e) ty =>
    .mk (.ifThenElse (tQualifyProjections structMeta ambiguous _ctx c)
                     (tQualifyProjections structMeta ambiguous _ctx t)
                     (tQualifyProjections structMeta ambiguous _ctx e)) ty
  | .mk (.match_ scrut arms) ty =>
    .mk (.match_ (tQualifyProjections structMeta ambiguous _ctx scrut)
                 (mapArms structMeta ambiguous _ctx arms)) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq e1 e2) ty =>
    .mk (.seq (tQualifyProjections structMeta ambiguous _ctx e1)
              (tQualifyProjections structMeta ambiguous _ctx e2)) ty
  | .mk (.borrow e) ty =>
    .mk (.borrow (tQualifyProjections structMeta ambiguous _ctx e)) ty
  | .mk (.deref e) ty =>
    .mk (.deref (tQualifyProjections structMeta ambiguous _ctx e)) ty
  | .mk (.assign n rhs) ty =>
    .mk (.assign n (tQualifyProjections structMeta ambiguous _ctx rhs)) ty
  | .mk (.forLoop v lo hi body) ty =>
    .mk (.forLoop v (tQualifyProjections structMeta ambiguous _ctx lo)
                    (tQualifyProjections structMeta ambiguous _ctx hi)
                    (tQualifyProjections structMeta ambiguous _ctx body)) ty
  | .mk (.forLoopRev v lo hi body) ty =>
    .mk (.forLoopRev v (tQualifyProjections structMeta ambiguous _ctx lo)
                       (tQualifyProjections structMeta ambiguous _ctx hi)
                       (tQualifyProjections structMeta ambiguous _ctx body)) ty
  | .mk (.whileLoop c body) ty =>
    .mk (.whileLoop (tQualifyProjections structMeta ambiguous _ctx c)
                    (tQualifyProjections structMeta ambiguous _ctx body)) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk (.break_ (some e)) ty =>
    .mk (.break_ (some (tQualifyProjections structMeta ambiguous _ctx e))) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty =>
    .mk (.earlyReturn (tQualifyProjections structMeta ambiguous _ctx e)) ty
  | .mk (.questionMark e) ty =>
    .mk (.questionMark (tQualifyProjections structMeta ambiguous _ctx e)) ty
  | .mk (.forFold v lo hi body) ty =>
    .mk (.forFold v (tQualifyProjections structMeta ambiguous _ctx lo)
                    (tQualifyProjections structMeta ambiguous _ctx hi)
                    (tQualifyProjections structMeta ambiguous _ctx body)) ty
  | .mk (.forFoldRev v lo hi body) ty =>
    .mk (.forFoldRev v (tQualifyProjections structMeta ambiguous _ctx lo)
                       (tQualifyProjections structMeta ambiguous _ctx hi)
                       (tQualifyProjections structMeta ambiguous _ctx body)) ty
  | .mk (.whileFold c body) ty =>
    .mk (.whileFold (tQualifyProjections structMeta ambiguous _ctx c)
                    (tQualifyProjections structMeta ambiguous _ctx body)) ty
  | .mk (.forFoldReturn v lo hi body) ty =>
    .mk (.forFoldReturn v (tQualifyProjections structMeta ambiguous _ctx lo)
                          (tQualifyProjections structMeta ambiguous _ctx hi)
                          (tQualifyProjections structMeta ambiguous _ctx body)) ty
  | .mk (.forFoldRevReturn v lo hi body) ty =>
    .mk (.forFoldRevReturn v (tQualifyProjections structMeta ambiguous _ctx lo)
                             (tQualifyProjections structMeta ambiguous _ctx hi)
                             (tQualifyProjections structMeta ambiguous _ctx body)) ty
  | .mk (.whileFoldReturn c body) ty =>
    .mk (.whileFoldReturn (tQualifyProjections structMeta ambiguous _ctx c)
                          (tQualifyProjections structMeta ambiguous _ctx body)) ty
  | .mk (.cfBreak e) ty =>
    .mk (.cfBreak (tQualifyProjections structMeta ambiguous _ctx e)) ty
  | .mk (.cfContinue e) ty =>
    .mk (.cfContinue (tQualifyProjections structMeta ambiguous _ctx e)) ty
  | .mk (.cfBreakContinue e) ty =>
    .mk (.cfBreakContinue (tQualifyProjections structMeta ambiguous _ctx e)) ty
  | .mk (.ann e) ty =>
    .mk (.ann (tQualifyProjections structMeta ambiguous _ctx e)) ty
  | .mk (.namedProj n e) ty =>
    .mk (.namedProj n (tQualifyProjections structMeta ambiguous _ctx e)) ty
where
  mapExpr (structMeta : StructMetaT) (ambiguous : List String) (ctx : TExpr) :
      List TExpr → List TExpr
    | [] => []
    | e :: es => tQualifyProjections structMeta ambiguous ctx e
               :: mapExpr structMeta ambiguous ctx es
  mapArms (structMeta : StructMetaT) (ambiguous : List String) (ctx : TExpr) :
      List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest =>
      (p, tQualifyProjections structMeta ambiguous ctx e)
        :: mapArms structMeta ambiguous ctx rest

@[simp] theorem tQualifyProjections.mapExpr_eq
    (structMeta : StructMetaT) (ambiguous : List String) (ctx : TExpr)
    (es : List TExpr) :
    tQualifyProjections.mapExpr structMeta ambiguous ctx es =
      es.map (tQualifyProjections structMeta ambiguous ctx) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [tQualifyProjections.mapExpr, ih]

@[simp] theorem tQualifyProjections.mapArms_eq
    (structMeta : StructMetaT) (ambiguous : List String) (ctx : TExpr)
    (arms : List (ImpPat × TExpr)) :
    tQualifyProjections.mapArms structMeta ambiguous ctx arms =
      arms.map fun (p, e) => (p, tQualifyProjections structMeta ambiguous ctx e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [tQualifyProjections.mapArms, ih]

/-- The typed phase preserves the outer type annotation at every node:
    no node is rewritten to a different type. This is the invariant that
    makes the typed phases safe to chain in arbitrary order — the
    succeeding phase still sees the same `ty` annotations. -/
theorem tQualifyProjections_ty
    (structMeta : StructMetaT) (ambiguous : List String) (ctx e : TExpr) :
    (tQualifyProjections structMeta ambiguous ctx e).ty = e.ty := by
  cases e with
  | mk kind ty =>
    cases kind <;> first | rfl | (rename_i e; cases e <;> rfl)

-- NOTE: `tQualifyProjections_erase` is intentionally not stated here.
-- The typed rewriter reads `arg.ty`, the untyped rewriter heuristically
-- infers a struct from `inferExprStructType` over the erased context.
-- These agree under a `WellTyped` predicate but not on arbitrary inputs;
-- the predicate is follow-up work.

end Hax

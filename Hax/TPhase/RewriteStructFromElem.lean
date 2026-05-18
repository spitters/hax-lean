/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr
import Hax.TPhase.StructMetaT

/-!
# Typed phase: `tRewriteStructFromElem`

Typed analog of the untyped `rewriteStructFromElem` rewriter in
`Hax/PrettyPrint.lean` (around line 4085).

At each `let arr := from_elem initVal sz` node we read the type
annotation on the right-hand side. If it is a `Vec` of a struct with
more than one field, or a `Vec` / `array` / `slice` of a tuple with
more than one element, we expand `initVal` into a tuple of `initVal`
copies whose arity matches the element type.

## Key difference vs the untyped rewriter

The untyped version uses five overlapping body-walking heuristics
(`checkArrayElemProjection`, `checkArrayElemUsedAsStruct`,
`checkBodyContainsStructAssign`, `checkPushWithStruct`,
`checkArrayAssignedStruct`) to *guess* the element type of the
constructed array from how `arrVar` is later consumed. The typed
version reads the type annotation on the `from_elem` call directly:
no walks, no heuristics, no false matches.

The `fnRetTypes` and `allDefs` parameters are accepted for API parity
with the untyped signature so callers can plug both rewriters in at
the same site; the typed body ignores them.

## Verification

This file intentionally omits an `erase` commuting theorem. The
typed rewriter inspects `val.ty`; the untyped rewriter inspects the
body via five heuristics, none of which depend on a type annotation.
A syntactic commuting equation does not hold on arbitrary inputs,
only on well-typed ones — a `WellTyped` predicate is follow-up work.
-/

namespace Hax

namespace TRewriteStructFromElem

/-- Strip leading `.ref` wrappers. -/
def unwrapRefs : ImpType → ImpType
  | .ref inner _ => unwrapRefs inner
  | t => t

/-- Look up a struct by name and return its field count when known. -/
def structFieldCount (structMeta : StructMetaT) (sname : String) : Option Nat :=
  (structMeta.find? (·.1 == sname)).map (·.2.length)

/-- Determine the desired tuple arity of `initVal` for a `from_elem`
    call whose return type is `callTy`. Returns `some n` when the
    element type is a struct with `n > 1` fields or a tuple with
    `n > 1` elements; returns `none` to keep `initVal` unchanged.

    Recognized container shapes (mirroring the untyped pass):
    * `Vec<elem, _alloc>` — two generic args, element + allocator
    * `array elem _len`
    * `slice elem`
    Also peels outer `.ref` wrappers transparently. -/
def desiredArity (structMeta : StructMetaT) : ImpType → Option Nat
  | .ref inner _ => desiredArity structMeta inner
  | .adt name (elemTy :: _) =>
    if name == "Vec" || name.endsWith "::Vec" then
      match elemTy with
      | .adt sname _ =>
        match structFieldCount structMeta sname with
        | some n => if n > 1 then some n else none
        | none => none
      | .tuple elems => if elems.length > 1 then some elems.length else none
      | _ => none
    else none
  | .array elemTy _ =>
    match elemTy with
    | .adt sname _ =>
      match structFieldCount structMeta sname with
      | some n => if n > 1 then some n else none
      | none => none
    | .tuple elems => if elems.length > 1 then some elems.length else none
    | _ => none
  | .slice elemTy =>
    match elemTy with
    | .adt sname _ =>
      match structFieldCount structMeta sname with
      | some n => if n > 1 then some n else none
      | none => none
    | .tuple elems => if elems.length > 1 then some elems.length else none
    | _ => none
  | _ => none

/-- Build the tuple-expanded `from_elem` call.
    Returns the original call when no expansion is needed. -/
def expandFromElem (structMeta : StructMetaT)
    (initVal sz : TExpr) (callTy : ImpType) : TExpr :=
  match desiredArity structMeta callTy with
  | some n =>
    -- Replace `initVal` with a tuple of `n` copies. Each copy keeps
    -- `initVal`'s type. The outer tuple's type is the tuple of these
    -- copies' types (so the new `from_elem` call still has type
    -- `callTy`, modulo the element-type swap that downstream phases
    -- perform when emitting struct constructors).
    let copies := List.replicate n initVal
    let tupleTy : ImpType := .tuple (copies.map TExpr.ty)
    let tupleInit : TExpr := .mk (.tuple copies) tupleTy
    .mk (.app "from_elem" [tupleInit, sz]) callTy
  | none =>
    .mk (.app "from_elem" [initVal, sz]) callTy

end TRewriteStructFromElem

open TRewriteStructFromElem in
/-- Typed `from_elem` struct/tuple expander over `TExpr`.

    At each `let arr := from_elem initVal sz` node, inspect the type
    `callTy` annotated on the `from_elem` call. If `callTy` denotes a
    container of structs/tuples whose arity is `> 1`, replace `initVal`
    with an `n`-tuple of `initVal` copies.

    `fnRetTypes` and `allDefs` are accepted for API parity with the
    untyped pass; the typed body does not consult them. -/
def tRewriteStructFromElem
    (structMeta : StructMetaT)
    (_fnRetTypes : List (String × ImpType))
    (_allDefs : List (String × TExpr)) : TExpr → TExpr
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty =>
    let val' := tRewriteStructFromElem structMeta _fnRetTypes _allDefs val
    let body' := tRewriteStructFromElem structMeta _fnRetTypes _allDefs body
    -- Specialised pattern: `let arr := from_elem initVal sz`.
    match val' with
    | .mk (.app "from_elem" [initVal, sz]) callTy =>
      let val'' := expandFromElem structMeta initVal sz callTy
      .mk (.letBind n val'' body') ty
    | _ => .mk (.letBind n val' body') ty
  | .mk (.app f args) ty =>
    .mk (.app f (mapExpr structMeta _fnRetTypes _allDefs args)) ty
  | .mk (.tuple elems) ty =>
    .mk (.tuple (mapExpr structMeta _fnRetTypes _allDefs elems)) ty
  | .mk (.proj e i) ty =>
    .mk (.proj (tRewriteStructFromElem structMeta _fnRetTypes _allDefs e) i) ty
  | .mk (.ifThenElse c t e) ty =>
    .mk (.ifThenElse (tRewriteStructFromElem structMeta _fnRetTypes _allDefs c)
                     (tRewriteStructFromElem structMeta _fnRetTypes _allDefs t)
                     (tRewriteStructFromElem structMeta _fnRetTypes _allDefs e)) ty
  | .mk (.match_ scrut arms) ty =>
    .mk (.match_ (tRewriteStructFromElem structMeta _fnRetTypes _allDefs scrut)
                 (mapArms structMeta _fnRetTypes _allDefs arms)) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq e1 e2) ty =>
    .mk (.seq (tRewriteStructFromElem structMeta _fnRetTypes _allDefs e1)
              (tRewriteStructFromElem structMeta _fnRetTypes _allDefs e2)) ty
  | .mk (.borrow e) ty =>
    .mk (.borrow (tRewriteStructFromElem structMeta _fnRetTypes _allDefs e)) ty
  | .mk (.deref e) ty =>
    .mk (.deref (tRewriteStructFromElem structMeta _fnRetTypes _allDefs e)) ty
  | .mk (.assign n rhs) ty =>
    .mk (.assign n (tRewriteStructFromElem structMeta _fnRetTypes _allDefs rhs)) ty
  | .mk (.forLoop v lo hi body) ty =>
    .mk (.forLoop v (tRewriteStructFromElem structMeta _fnRetTypes _allDefs lo)
                    (tRewriteStructFromElem structMeta _fnRetTypes _allDefs hi)
                    (tRewriteStructFromElem structMeta _fnRetTypes _allDefs body)) ty
  | .mk (.forLoopRev v lo hi body) ty =>
    .mk (.forLoopRev v (tRewriteStructFromElem structMeta _fnRetTypes _allDefs lo)
                       (tRewriteStructFromElem structMeta _fnRetTypes _allDefs hi)
                       (tRewriteStructFromElem structMeta _fnRetTypes _allDefs body)) ty
  | .mk (.whileLoop c body) ty =>
    .mk (.whileLoop (tRewriteStructFromElem structMeta _fnRetTypes _allDefs c)
                    (tRewriteStructFromElem structMeta _fnRetTypes _allDefs body)) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk (.break_ (some e)) ty =>
    .mk (.break_ (some (tRewriteStructFromElem structMeta _fnRetTypes _allDefs e))) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty =>
    .mk (.earlyReturn (tRewriteStructFromElem structMeta _fnRetTypes _allDefs e)) ty
  | .mk (.questionMark e) ty =>
    .mk (.questionMark (tRewriteStructFromElem structMeta _fnRetTypes _allDefs e)) ty
  | .mk (.forFold v lo hi body) ty =>
    .mk (.forFold v (tRewriteStructFromElem structMeta _fnRetTypes _allDefs lo)
                    (tRewriteStructFromElem structMeta _fnRetTypes _allDefs hi)
                    (tRewriteStructFromElem structMeta _fnRetTypes _allDefs body)) ty
  | .mk (.forFoldRev v lo hi body) ty =>
    .mk (.forFoldRev v (tRewriteStructFromElem structMeta _fnRetTypes _allDefs lo)
                       (tRewriteStructFromElem structMeta _fnRetTypes _allDefs hi)
                       (tRewriteStructFromElem structMeta _fnRetTypes _allDefs body)) ty
  | .mk (.whileFold c body) ty =>
    .mk (.whileFold (tRewriteStructFromElem structMeta _fnRetTypes _allDefs c)
                    (tRewriteStructFromElem structMeta _fnRetTypes _allDefs body)) ty
  | .mk (.forFoldReturn v lo hi body) ty =>
    .mk (.forFoldReturn v (tRewriteStructFromElem structMeta _fnRetTypes _allDefs lo)
                          (tRewriteStructFromElem structMeta _fnRetTypes _allDefs hi)
                          (tRewriteStructFromElem structMeta _fnRetTypes _allDefs body)) ty
  | .mk (.forFoldRevReturn v lo hi body) ty =>
    .mk (.forFoldRevReturn v (tRewriteStructFromElem structMeta _fnRetTypes _allDefs lo)
                             (tRewriteStructFromElem structMeta _fnRetTypes _allDefs hi)
                             (tRewriteStructFromElem structMeta _fnRetTypes _allDefs body)) ty
  | .mk (.whileFoldReturn c body) ty =>
    .mk (.whileFoldReturn (tRewriteStructFromElem structMeta _fnRetTypes _allDefs c)
                          (tRewriteStructFromElem structMeta _fnRetTypes _allDefs body)) ty
  | .mk (.cfBreak e) ty =>
    .mk (.cfBreak (tRewriteStructFromElem structMeta _fnRetTypes _allDefs e)) ty
  | .mk (.cfContinue e) ty =>
    .mk (.cfContinue (tRewriteStructFromElem structMeta _fnRetTypes _allDefs e)) ty
  | .mk (.cfBreakContinue e) ty =>
    .mk (.cfBreakContinue (tRewriteStructFromElem structMeta _fnRetTypes _allDefs e)) ty
  | .mk (.ann e) ty =>
    .mk (.ann (tRewriteStructFromElem structMeta _fnRetTypes _allDefs e)) ty
  | .mk (.namedProj n e) ty =>
    .mk (.namedProj n (tRewriteStructFromElem structMeta _fnRetTypes _allDefs e)) ty
where
  mapExpr (structMeta : StructMetaT)
      (fnRetTypes : List (String × ImpType))
      (allDefs : List (String × TExpr)) :
      List TExpr → List TExpr
    | [] => []
    | e :: es => tRewriteStructFromElem structMeta fnRetTypes allDefs e
               :: mapExpr structMeta fnRetTypes allDefs es
  mapArms (structMeta : StructMetaT)
      (fnRetTypes : List (String × ImpType))
      (allDefs : List (String × TExpr)) :
      List (ImpPat × TExpr) → List (ImpPat × TExpr) :=
    fun
    | [] => []
    | (p, e) :: rest =>
      (p, tRewriteStructFromElem structMeta fnRetTypes allDefs e)
        :: mapArms structMeta fnRetTypes allDefs rest

@[simp] theorem tRewriteStructFromElem.mapExpr_eq
    (structMeta : StructMetaT)
    (fnRetTypes : List (String × ImpType))
    (allDefs : List (String × TExpr))
    (es : List TExpr) :
    tRewriteStructFromElem.mapExpr structMeta fnRetTypes allDefs es =
      es.map (tRewriteStructFromElem structMeta fnRetTypes allDefs) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [tRewriteStructFromElem.mapExpr, ih]

@[simp] theorem tRewriteStructFromElem.mapArms_eq
    (structMeta : StructMetaT)
    (fnRetTypes : List (String × ImpType))
    (allDefs : List (String × TExpr))
    (arms : List (ImpPat × TExpr)) :
    tRewriteStructFromElem.mapArms structMeta fnRetTypes allDefs arms =
      arms.map fun (p, e) =>
        (p, tRewriteStructFromElem structMeta fnRetTypes allDefs e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa
                       simp [tRewriteStructFromElem.mapArms, ih]

-- NOTE: `tRewriteStructFromElem_erase` is intentionally not stated here.
-- The typed rewriter reads `callTy` on the `from_elem` call; the
-- untyped rewriter runs five body-walking heuristics over the erased
-- continuation. The two agree on well-typed inputs (which is the
-- whole point of the typed phase) but a syntactic erase commuting
-- equation requires a `WellTyped` hypothesis — follow-up work.

end Hax

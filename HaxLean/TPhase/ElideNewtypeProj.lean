/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import HaxLean.TExpr
import HaxLean.HaxAdapter

/-!
# Typed Phase: Elide Newtype Projections to `.namedProj`

When the Rust source contains `commitment.0` where `commitment : T`
and `T` is a tuple-struct newtype (`struct T(Inner)`), hax extracts
this as a call `.app ".0" [x]` whose runtime semantics in our model is
identity (the underlying `Hax.«.0»` is polymorphic-identity in
`Runtime.lean`). The TYPE story is more subtle: in Rust, `T.0` unwraps
to `Inner`, but our polymorphic identity gives back `T`, leading to
type-mismatch errors at use sites where `Inner` is expected.

This pass rewrites the typed AST so that `.app ".0" [x]` (when
`x.ty` is a known newtype `T`) becomes `.namedProj T x`. The renderer
then emits `«T.0» x`, where `«T.0»` is a *definitional* unwrap
(`def «T.0» (x : T_T) : Inner := x`) — i.e., it carries the type
refinement that hax's IR omits.

## Verification

`.namedProj T e` erases to `.app ".0" [e.erase]` (see `TExpr.erase`):
the underlying ImpExpr is unchanged. So the new phase is *transparent*
to the untyped pipeline, and `pipeline_correct` (parametric in
builtins) is unaffected. The phase's own correctness theorem is
trivial: `(tElideToNamedProj nt e).erase = e.erase`.
-/

namespace Hax

/-- Unwrap a single layer of `.ref` (Rust receivers are `&self`-borrowed). -/
private def unwrapRefImp : ImpType → ImpType
  | .ref inner _ => inner
  | t => t

/-- Rewrite `.app ".0" [x]` to `.namedProj T x` if `x.ty` is a newtype.
    Otherwise return the original `.app f args`. Used inside
    `tElideToNamedProj` to keep the function definition flat and the
    erase proof tractable. -/
private def rewriteAppHead
    (newtypes : HaxAdapter.NewtypeMap) (f : String) (args : List TExpr) : TExprKind :=
  match f, args with
  | ".0", [x] =>
    match unwrapRefImp x.ty with
    | .adt rawName _ =>
      if newtypes.any (·.1 == rawName) then .namedProj rawName x
      else if newtypes.any (·.1 == ImpType.sanitizeAdtShortName rawName) then
        .namedProj (ImpType.sanitizeAdtShortName rawName) x
      else .app f args
    | _ => .app f args
  | _, _ => .app f args

/-- `rewriteAppHead` is erase-identity at the ImpExpr level: a `.namedProj`
    erases to `.app ".0" [x.erase]`, which is what the original input was. -/
private theorem rewriteAppHead_erase
    (newtypes : HaxAdapter.NewtypeMap) (f : String) (args : List TExpr) (ty : ImpType) :
    (TExpr.mk (rewriteAppHead newtypes f args) ty).erase =
      (TExpr.mk (.app f args) ty).erase := by
  -- The function either returns `.app f args` (rfl) or `.namedProj T x`
  -- whose erase is `.app ".0" [x.erase]`. The latter only happens when
  -- f = ".0" and args = [x], so erase-equal in both branches.
  unfold rewriteAppHead
  split <;> (try rfl)
  split <;> (try rfl)
  split <;> (try rfl)
  split <;> (try rfl)
  all_goals simp [TExpr.erase, TExpr.erase.eraseList]

/-- Return the newtype short-name from `x.ty` if `x : <T>` for some
    `T` in the newtype map; else `none`.

    We unwrap `.ref` once (Rust's `&T` for an inherent-receiver call)
    and accept either the raw ADT path or its sanitized short form. -/
private def receiverNewtype? (newtypes : HaxAdapter.NewtypeMap) (ty : ImpType) : Option String :=
  let unwrap : ImpType → ImpType
    | .ref inner _ => inner
    | t => t
  match unwrap ty with
  | .adt rawName _ =>
    let short := ImpType.sanitizeAdtShortName rawName
    if newtypes.any (·.1 == rawName) then some rawName
    else if newtypes.any (·.1 == short) then some short
    else none
  | _ => none

/-- Phase: rewrite `.app ".0" [x]` to `.namedProj T x` when `x` has a
    newtype receiver. Other constructors recurse structurally. -/
def tElideToNamedProj (newtypes : HaxAdapter.NewtypeMap) : TExpr → TExpr
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty =>
      .mk (.letBind n (tElideToNamedProj newtypes val)
                      (tElideToNamedProj newtypes body)) ty
  | .mk (.lam ps body) ty => .mk (.lam ps (tElideToNamedProj newtypes body)) ty
  | .mk (.app f args) ty =>
      .mk (rewriteAppHead newtypes f (mapExpr newtypes args)) ty
  | .mk (.tuple elems) ty => .mk (.tuple (mapExpr newtypes elems)) ty
  | .mk (.proj e i) ty => .mk (.proj (tElideToNamedProj newtypes e) i) ty
  | .mk (.ifThenElse c t e) ty =>
      .mk (.ifThenElse (tElideToNamedProj newtypes c)
                       (tElideToNamedProj newtypes t)
                       (tElideToNamedProj newtypes e)) ty
  | .mk (.match_ scrut arms) ty =>
      .mk (.match_ (tElideToNamedProj newtypes scrut)
                   (mapArms newtypes arms)) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq e1 e2) ty =>
      .mk (.seq (tElideToNamedProj newtypes e1) (tElideToNamedProj newtypes e2)) ty
  | .mk (.borrow e) ty => .mk (.borrow (tElideToNamedProj newtypes e)) ty
  | .mk (.deref e) ty => .mk (.deref (tElideToNamedProj newtypes e)) ty
  | .mk (.assign n rhs) ty => .mk (.assign n (tElideToNamedProj newtypes rhs)) ty
  | .mk (.forLoop v lo hi body) ty =>
      .mk (.forLoop v (tElideToNamedProj newtypes lo)
                      (tElideToNamedProj newtypes hi)
                      (tElideToNamedProj newtypes body)) ty
  | .mk (.forLoopRev v lo hi body) ty =>
      .mk (.forLoopRev v (tElideToNamedProj newtypes lo)
                         (tElideToNamedProj newtypes hi)
                         (tElideToNamedProj newtypes body)) ty
  | .mk (.whileLoop c body) ty =>
      .mk (.whileLoop (tElideToNamedProj newtypes c)
                      (tElideToNamedProj newtypes body)) ty
  | .mk (.break_ (some e)) ty => .mk (.break_ (some (tElideToNamedProj newtypes e))) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty => .mk (.earlyReturn (tElideToNamedProj newtypes e)) ty
  | .mk (.questionMark e) ty => .mk (.questionMark (tElideToNamedProj newtypes e)) ty
  | .mk (.forFold v lo hi body) ty =>
      .mk (.forFold v (tElideToNamedProj newtypes lo)
                      (tElideToNamedProj newtypes hi)
                      (tElideToNamedProj newtypes body)) ty
  | .mk (.forFoldRev v lo hi body) ty =>
      .mk (.forFoldRev v (tElideToNamedProj newtypes lo)
                         (tElideToNamedProj newtypes hi)
                         (tElideToNamedProj newtypes body)) ty
  | .mk (.whileFold c body) ty =>
      .mk (.whileFold (tElideToNamedProj newtypes c)
                      (tElideToNamedProj newtypes body)) ty
  | .mk (.forFoldReturn v lo hi body) ty =>
      .mk (.forFoldReturn v (tElideToNamedProj newtypes lo)
                            (tElideToNamedProj newtypes hi)
                            (tElideToNamedProj newtypes body)) ty
  | .mk (.forFoldRevReturn v lo hi body) ty =>
      .mk (.forFoldRevReturn v (tElideToNamedProj newtypes lo)
                               (tElideToNamedProj newtypes hi)
                               (tElideToNamedProj newtypes body)) ty
  | .mk (.whileFoldReturn c body) ty =>
      .mk (.whileFoldReturn (tElideToNamedProj newtypes c)
                            (tElideToNamedProj newtypes body)) ty
  | .mk (.cfBreak e) ty => .mk (.cfBreak (tElideToNamedProj newtypes e)) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue (tElideToNamedProj newtypes e)) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (tElideToNamedProj newtypes e)) ty
  | .mk (.ann e) ty => .mk (.ann (tElideToNamedProj newtypes e)) ty
  | .mk (.namedProj n e) ty => .mk (.namedProj n (tElideToNamedProj newtypes e)) ty
where
  mapExpr (newtypes : HaxAdapter.NewtypeMap) : List TExpr → List TExpr
    | [] => []
    | e :: es => tElideToNamedProj newtypes e :: mapExpr newtypes es
  mapArms (newtypes : HaxAdapter.NewtypeMap) : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tElideToNamedProj newtypes e) :: mapArms newtypes rest

@[simp] theorem tElideToNamedProj.mapExpr_eq (nt : HaxAdapter.NewtypeMap) (es : List TExpr) :
    tElideToNamedProj.mapExpr nt es = es.map (tElideToNamedProj nt) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [tElideToNamedProj.mapExpr, ih]

@[simp] theorem tElideToNamedProj.mapArms_eq (nt : HaxAdapter.NewtypeMap)
    (arms : List (ImpPat × TExpr)) :
    tElideToNamedProj.mapArms nt arms =
      arms.map fun (p, e) => (p, tElideToNamedProj nt e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [tElideToNamedProj.mapArms, ih]

/-- Helper: when the pass rewrites a single-arg `.app ".0"` to a
    `.namedProj`, the erase result is unchanged because `.namedProj T e`
    erases to `.app ".0" [e.erase]`. -/
private theorem app_dot0_erase_eq (e : TExpr) (tname : String) (ty : ImpType) :
    (TExpr.mk (.namedProj tname e) ty).erase =
      (TExpr.mk (.app ".0" [e]) ty).erase := by
  simp [TExpr.erase]

/-- **Main theorem.** `tElideToNamedProj` is denotation-identity via
    erasure: the underlying ImpExpr is structurally unchanged
    (every `.namedProj T e` erases to the same `.app ".0" [e.erase]`
    as the original).

    The verified pipeline `pipeline_correct` is therefore unaffected. -/
theorem tElideToNamedProj_erase (newtypes : HaxAdapter.NewtypeMap) (e : TExpr) :
    (tElideToNamedProj newtypes e).erase = e.erase := by
  induction e using TExpr.ind with
  | lit => rfl
  | var => rfl
  | unitVal => rfl
  | break_none => rfl
  | continue_ => rfl
  | lam _ _ _ ih =>
    simp [tElideToNamedProj, TExpr.erase, ih]
  | letBind _ _ _ _ ih1 ih2 =>
    simp [tElideToNamedProj, TExpr.erase, ih1, ih2]
  | seq _ _ _ ih1 ih2 =>
    simp [tElideToNamedProj, TExpr.erase, ih1, ih2]
  | proj _ _ _ ih => simp [tElideToNamedProj, TExpr.erase, ih]
  | ifThenElse _ _ _ _ ih1 ih2 ih3 =>
    simp [tElideToNamedProj, TExpr.erase, ih1, ih2, ih3]
  | borrow _ _ ih => simp [tElideToNamedProj, TExpr.erase, ih]
  | deref _ _ ih => simp [tElideToNamedProj, TExpr.erase, ih]
  | assign _ _ _ ih => simp [tElideToNamedProj, TExpr.erase, ih]
  | forLoop _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tElideToNamedProj, TExpr.erase, ih1, ih2, ih3]
  | forLoopRev _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tElideToNamedProj, TExpr.erase, ih1, ih2, ih3]
  | whileLoop _ _ _ ih1 ih2 =>
    simp [tElideToNamedProj, TExpr.erase, ih1, ih2]
  | break_some _ _ ih => simp [tElideToNamedProj, TExpr.erase, ih]
  | earlyReturn _ _ ih => simp [tElideToNamedProj, TExpr.erase, ih]
  | questionMark _ _ ih => simp [tElideToNamedProj, TExpr.erase, ih]
  | forFold _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tElideToNamedProj, TExpr.erase, ih1, ih2, ih3]
  | forFoldRev _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tElideToNamedProj, TExpr.erase, ih1, ih2, ih3]
  | whileFold _ _ _ ih1 ih2 =>
    simp [tElideToNamedProj, TExpr.erase, ih1, ih2]
  | forFoldReturn _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tElideToNamedProj, TExpr.erase, ih1, ih2, ih3]
  | forFoldRevReturn _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tElideToNamedProj, TExpr.erase, ih1, ih2, ih3]
  | whileFoldReturn _ _ _ ih1 ih2 =>
    simp [tElideToNamedProj, TExpr.erase, ih1, ih2]
  | cfBreak _ _ ih => simp [tElideToNamedProj, TExpr.erase, ih]
  | cfContinue _ _ ih => simp [tElideToNamedProj, TExpr.erase, ih]
  | cfBreakContinue _ _ ih => simp [tElideToNamedProj, TExpr.erase, ih]
  | ann _ _ ih => simp [tElideToNamedProj, TExpr.erase, ih]
  | namedProj _ _ _ ih => simp [tElideToNamedProj, TExpr.erase, ih]
  | tuple _ elems ih =>
    simp only [tElideToNamedProj, tElideToNamedProj.mapExpr_eq, TExpr.erase,
      TExpr.eraseList_eq, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha)
  | match_ _ _ arms _ ih2 =>
    simp only [tElideToNamedProj, tElideToNamedProj.mapArms_eq, TExpr.erase,
      TExpr.eraseArms_eq, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun ⟨p, e⟩ hpa => by
      simp only [ih2 (p, e) hpa])
  | app _ f args ih =>
    -- The function reduces to `.mk (rewriteAppHead newtypes f args') ty`
    -- where args' is the structurally-recursed args. We use
    -- `rewriteAppHead_erase` to commute the rewrite past erase, then
    -- the standard IH-based structural argument.
    simp only [tElideToNamedProj, tElideToNamedProj.mapExpr_eq]
    rw [rewriteAppHead_erase]
    simp only [TExpr.erase, TExpr.eraseList_eq, List.map_map, Function.comp_def]
    congr 1
    exact List.map_congr_left (fun a ha => ih a ha)

end Hax

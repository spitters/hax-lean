/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr
import Hax.Phase.RewriteAppName

/-!
# Typed phase: `tRewriteAppName`

Typed analog of `Hax.rewriteAppName`. Walks a `TExpr` renaming every
`.app f args` whose function name equals `oldName` to `.app newName args`,
preserving outer types unchanged.

## Verification

The main theorem `tRewriteAppName_erase` states that erase commutes with
the typed renamer:

```
(tRewriteAppName old new e).erase = rewriteAppName old new e.erase
```

This makes the typed phase a denotation-respecting refinement of the
untyped one: any caller that proves the untyped `rewriteAppName` correct
under some runtime invariant (e.g. "oldName and newName denote the same
function") gets the typed version's correctness for free.
-/

namespace Hax

/-- Typed renamer over TExpr. Mirrors `rewriteAppName` structurally and
    preserves the outer type on every node. -/
def tRewriteAppName (oldName newName : String) : TExpr → TExpr
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n val body) ty =>
    .mk (.letBind n (tRewriteAppName oldName newName val)
                    (tRewriteAppName oldName newName body)) ty
  | .mk (.lam ps body) ty => .mk (.lam ps (tRewriteAppName oldName newName body)) ty
  | .mk (.app f args) ty =>
    let f' := if f == oldName then newName else f
    .mk (.app f' (mapExpr oldName newName args)) ty
  | .mk (.tuple elems) ty =>
    .mk (.tuple (mapExpr oldName newName elems)) ty
  | .mk (.proj e i) ty => .mk (.proj (tRewriteAppName oldName newName e) i) ty
  | .mk (.ifThenElse c t e) ty =>
    .mk (.ifThenElse (tRewriteAppName oldName newName c)
                     (tRewriteAppName oldName newName t)
                     (tRewriteAppName oldName newName e)) ty
  | .mk (.match_ scrut arms) ty =>
    .mk (.match_ (tRewriteAppName oldName newName scrut)
                 (mapArms oldName newName arms)) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq e1 e2) ty =>
    .mk (.seq (tRewriteAppName oldName newName e1)
              (tRewriteAppName oldName newName e2)) ty
  | .mk (.borrow e) ty => .mk (.borrow (tRewriteAppName oldName newName e)) ty
  | .mk (.deref e) ty => .mk (.deref (tRewriteAppName oldName newName e)) ty
  | .mk (.assign n rhs) ty =>
    .mk (.assign n (tRewriteAppName oldName newName rhs)) ty
  | .mk (.forLoop v lo hi body) ty =>
    .mk (.forLoop v (tRewriteAppName oldName newName lo)
                    (tRewriteAppName oldName newName hi)
                    (tRewriteAppName oldName newName body)) ty
  | .mk (.forLoopRev v lo hi body) ty =>
    .mk (.forLoopRev v (tRewriteAppName oldName newName lo)
                       (tRewriteAppName oldName newName hi)
                       (tRewriteAppName oldName newName body)) ty
  | .mk (.whileLoop c body) ty =>
    .mk (.whileLoop (tRewriteAppName oldName newName c)
                    (tRewriteAppName oldName newName body)) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk (.break_ (some e)) ty =>
    .mk (.break_ (some (tRewriteAppName oldName newName e))) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty =>
    .mk (.earlyReturn (tRewriteAppName oldName newName e)) ty
  | .mk (.questionMark e) ty =>
    .mk (.questionMark (tRewriteAppName oldName newName e)) ty
  | .mk (.forFold v lo hi body) ty =>
    .mk (.forFold v (tRewriteAppName oldName newName lo)
                    (tRewriteAppName oldName newName hi)
                    (tRewriteAppName oldName newName body)) ty
  | .mk (.forFoldRev v lo hi body) ty =>
    .mk (.forFoldRev v (tRewriteAppName oldName newName lo)
                       (tRewriteAppName oldName newName hi)
                       (tRewriteAppName oldName newName body)) ty
  | .mk (.whileFold c body) ty =>
    .mk (.whileFold (tRewriteAppName oldName newName c)
                    (tRewriteAppName oldName newName body)) ty
  | .mk (.forFoldReturn v lo hi body) ty =>
    .mk (.forFoldReturn v (tRewriteAppName oldName newName lo)
                          (tRewriteAppName oldName newName hi)
                          (tRewriteAppName oldName newName body)) ty
  | .mk (.forFoldRevReturn v lo hi body) ty =>
    .mk (.forFoldRevReturn v (tRewriteAppName oldName newName lo)
                             (tRewriteAppName oldName newName hi)
                             (tRewriteAppName oldName newName body)) ty
  | .mk (.whileFoldReturn c body) ty =>
    .mk (.whileFoldReturn (tRewriteAppName oldName newName c)
                          (tRewriteAppName oldName newName body)) ty
  | .mk (.cfBreak e) ty =>
    .mk (.cfBreak (tRewriteAppName oldName newName e)) ty
  | .mk (.cfContinue e) ty =>
    .mk (.cfContinue (tRewriteAppName oldName newName e)) ty
  | .mk (.cfBreakContinue e) ty =>
    .mk (.cfBreakContinue (tRewriteAppName oldName newName e)) ty
  | .mk (.ann e) ty =>
    .mk (.ann (tRewriteAppName oldName newName e)) ty
  | .mk (.namedProj n e) ty =>
    .mk (.namedProj n (tRewriteAppName oldName newName e)) ty
where
  mapExpr (oldName newName : String) : List TExpr → List TExpr
    | [] => []
    | e :: es => tRewriteAppName oldName newName e :: mapExpr oldName newName es
  mapArms (oldName newName : String) : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tRewriteAppName oldName newName e)
                       :: mapArms oldName newName rest

@[simp] theorem tRewriteAppName.mapExpr_eq (oldName newName : String) (es : List TExpr) :
    tRewriteAppName.mapExpr oldName newName es = es.map (tRewriteAppName oldName newName) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [tRewriteAppName.mapExpr, ih]

@[simp] theorem tRewriteAppName.mapArms_eq (oldName newName : String)
    (arms : List (ImpPat × TExpr)) :
    tRewriteAppName.mapArms oldName newName arms =
      arms.map fun (p, e) => (p, tRewriteAppName oldName newName e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [tRewriteAppName.mapArms, ih]

/-- **Main theorem.** Type erasure commutes with `tRewriteAppName`.

    Side condition `oldName ≠ ".0"`: the typed renamer preserves the
    `.namedProj` constructor (which erases to `.app ".0" [_]`), but the
    untyped `rewriteAppName` would rewrite `".0"` if asked. The two
    diverge there. Real call sites pass projection names like
    `".field"` or constructor names like `"new"`, never `".0"`. -/
theorem tRewriteAppName_erase (oldName newName : String) (h : oldName ≠ ".0")
    (e : TExpr) :
    (tRewriteAppName oldName newName e).erase = rewriteAppName oldName newName e.erase := by
  induction e using TExpr.ind with
  | lit | var | unitVal | continue_ | break_none => rfl
  | lam _ _ _ ih =>
    simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih]
  | letBind _ _ _ _ ih1 ih2 =>
    simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih1, ih2]
  | seq _ _ _ ih1 ih2 =>
    simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih1, ih2]
  | proj _ _ _ ih => simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih]
  | ifThenElse _ _ _ _ ih1 ih2 ih3 =>
    simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih1, ih2, ih3]
  | borrow _ _ ih => simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih]
  | deref _ _ ih => simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih]
  | assign _ _ _ ih => simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih]
  | forLoop _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih1, ih2, ih3]
  | forLoopRev _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih1, ih2, ih3]
  | whileLoop _ _ _ ih1 ih2 =>
    simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih1, ih2]
  | break_some _ _ ih => simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih]
  | earlyReturn _ _ ih => simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih]
  | questionMark _ _ ih => simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih]
  | forFold _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih1, ih2, ih3]
  | forFoldRev _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih1, ih2, ih3]
  | whileFold _ _ _ ih1 ih2 =>
    simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih1, ih2]
  | forFoldReturn _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih1, ih2, ih3]
  | forFoldRevReturn _ _ _ _ _ ih1 ih2 ih3 =>
    simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih1, ih2, ih3]
  | whileFoldReturn _ _ _ ih1 ih2 =>
    simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih1, ih2]
  | cfBreak _ _ ih => simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih]
  | cfContinue _ _ ih => simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih]
  | cfBreakContinue _ _ ih => simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih]
  | ann _ _ ih => simp [tRewriteAppName, TExpr.erase, rewriteAppName, ih]
  | namedProj _ _ _ ih =>
    simp only [tRewriteAppName, TExpr.erase, rewriteAppName, ih]
    -- The erased form is `.app ".0" [inner.erase]`. `rewriteAppName` then
    -- checks `if ".0" == oldName then newName else ".0"`. By the side
    -- condition `oldName ≠ ".0"` the branch is `else ".0"`, so the head
    -- stays as `".0"` and matches the typed form's preserved `.namedProj`.
    simp [h.symm]
  | app _ _ args ih =>
    simp only [tRewriteAppName, tRewriteAppName.mapExpr_eq, TExpr.erase,
      TExpr.eraseList_eq, rewriteAppName, rewriteAppName.mapExpr_eq,
      List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha)
  | tuple _ elems ih =>
    simp only [tRewriteAppName, tRewriteAppName.mapExpr_eq, TExpr.erase,
      TExpr.eraseList_eq, rewriteAppName, rewriteAppName.mapExpr_eq,
      List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun a ha => ih a ha)
  | match_ _ _ arms ih1 ih2 =>
    simp only [tRewriteAppName, tRewriteAppName.mapArms_eq, TExpr.erase,
      TExpr.eraseArms_eq, rewriteAppName, rewriteAppName.mapArms_eq,
      ih1, List.map_map, Function.comp_def]
    congr 1; exact List.map_congr_left (fun ⟨p, e⟩ hpa => by
      simp only [ih2 (p, e) hpa])

end Hax

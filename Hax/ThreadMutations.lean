/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr
import Hax.InlineClosures

/-!
# Pre-pipeline normalization: thread mutations across `if`-statement joins

A Rust `let mut v = …; if c { v = … } else { v = … }; <use v>` lowers (before this
pass) to `seq (ifThenElse c (assign v …) (assign v …)) rest`. `localMutation` then
rewrites each `assign v x` to a *locally-scoped* `let v := x; …` — so the new `v`
never escapes the branch, and `rest` sees the stale `v`. Worse, the branches end up
with mismatched types (a value-yielding arm vs a `()` arm).

This pass restructures an `if` used as a STATEMENT (its value discarded by an
enclosing `seq`) so the mutated, still-live variables are returned by every branch
and rebound after the join:

    seq (if c then T else E) rest
  ↦ letBind _mtup (if c then (T; (v₁,…,vₙ)) else (E; (v₁,…,vₙ)))
       (let v₁ := _mtup.0; …; let vₙ := _mtup.(n-1); rest)

where `{v₁,…,vₙ}` = variables assigned in either branch that are still used in `rest`.
Because the appended tuple sits in the assigns' continuation, after `localMutation`
+ rendering each `vᵢ` resolves to its mutated value. A bonus: a loop sitting at a
branch tail now has a continuation, so `functionalizeLoops`/the renderer emit its
`.merge` + projection instead of leaving a bare `whileFold` (a `ControlFlow`).

Run BEFORE the typed pipeline (parse-time normalization, not a verified phase).
-/

namespace Hax

/-- Immediate `TExpr` children. -/
private def tChildrenM : TExpr → List TExpr
  | .mk (.letBind _ v b) _ => [v, b]
  | .mk (.lam _ b) _ => [b]
  | .mk (.app _ args) _ => args
  | .mk (.tuple es) _ => es
  | .mk (.proj e _) _ => [e]
  | .mk (.ifThenElse c t e) _ => [c, t, e]
  | .mk (.match_ s arms) _ => s :: arms.map (·.2)
  | .mk (.seq a b) _ => [a, b]
  | .mk (.borrow e) _ | .mk (.deref e) _ | .mk (.ann e) _
  | .mk (.namedProj _ e) _ | .mk (.earlyReturn e) _ | .mk (.questionMark e) _
  | .mk (.cfBreak e) _ | .mk (.cfContinue e) _ | .mk (.cfBreakContinue e) _
  | .mk (.break_ (some e)) _ | .mk (.assign _ e) _ => [e]
  | .mk (.forLoop _ lo hi b) _ | .mk (.forLoopRev _ lo hi b) _
  | .mk (.forFold _ lo hi b) _ | .mk (.forFoldRev _ lo hi b) _
  | .mk (.forFoldReturn _ lo hi b) _ | .mk (.forFoldRevReturn _ lo hi b) _ => [lo, hi, b]
  | .mk (.whileLoop c b) _ | .mk (.whileFold c b) _ | .mk (.whileFoldReturn c b) _ => [c, b]
  | _ => []

/-- Names assigned (`.assign`) anywhere in `e`. -/
partial def tAssignedVars : TExpr → List String
  | .mk (.assign n rhs) _ => n :: tAssignedVars rhs
  | e => (tChildrenM e).foldl (fun acc c => acc ++ tAssignedVars c) []

/-- Names referenced (`.var`) anywhere in `e` (over-approximate: ignores binders). -/
partial def tVarRefs : TExpr → List String
  | .mk (.var n) _ => [n]
  | e => (tChildrenM e).foldl (fun acc c => acc ++ tVarRefs c) []

/-- Build `(v₁, …, vₙ)` (or just `vᵢ` when singleton) from variable names. -/
def tVarTuple : List String → TExpr
  | [v] => .mk (.var v) .unknown
  | vs => .mk (.tuple (vs.map (fun v => .mk (.var v) .unknown))) .unknown

/-- Rebind `vars` from the right-nested tuple `tup`, then continue with `cont`.
    A Lean n-tuple `(v₁,…,vₙ)` is `(v₁, (v₂, … vₙ))`, so the head is `tup.1`
    (`proj 0`) and the rest live in `tup.2` (`proj 1`) — recurse there. The last
    variable binds the remaining tail directly. (A flat `tup.i` would be invalid:
    `(a,b,c).3` doesn't exist.) -/
def tDestructure : List String → TExpr → TExpr → TExpr
  | [], _, cont => cont
  | [v], tup, cont => .mk (.letBind v tup cont) cont.ty
  | v :: vs, tup, cont =>
    .mk (.letBind v (.mk (.proj tup 0) .unknown)
      (tDestructure vs (.mk (.proj tup 1) .unknown) cont)) cont.ty

/-- Replace the tail value of a `let`/`seq` chain with `newTail`, keeping the
    bindings (and keeping a trailing `assign` as a statement before `newTail`). -/
partial def tReplaceTail (e newTail : TExpr) : TExpr :=
  match e.kind with
  | .letBind n v body => .mk (.letBind n v (tReplaceTail body newTail)) e.ty
  | .seq a b => .mk (.seq a (tReplaceTail b newTail)) e.ty
  | .assign _ _ => .mk (.seq e newTail) e.ty
  | _ => newTail

/-- Thread mutations across `if`-statement joins (see module docstring). -/
partial def tThreadMut (e : TExpr) : TExpr :=
  match e.kind with
  | .seq (.mk (.ifThenElse c t f) ifTy) rest =>
    let t := tThreadMut t
    let f := tThreadMut f
    let rest := tThreadMut rest
    let used := tVarRefs rest
    let m := (tAssignedVars t ++ tAssignedVars f).eraseDups.filter used.contains
    if m.isEmpty then
      .mk (.seq (.mk (.ifThenElse (tThreadMut c) t f) ifTy) rest) e.ty
    else
      let tup := tVarTuple m
      let ifE := .mk (.ifThenElse (tThreadMut c) (tReplaceTail t tup) (tReplaceTail f tup)) .unknown
      .mk (.letBind "_mtup" ifE (tDestructure m (.mk (.var "_mtup") .unknown) rest)) e.ty
  | _ => tMapChildren tThreadMut e

end Hax

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

/-- Names assigned (`.assign`) anywhere in `e`. Structural recursion (one
    `match` arm per constructor) so the function is non-`partial` and admits the
    `tAssignedVars_erase` commutation lemma in `ThreadMutationsErase`. -/
def tAssignedVars : TExpr → List String
  | .mk (.assign n rhs) _ => n :: tAssignedVars rhs
  | .mk (.letBind _ v b) _ => tAssignedVars v ++ tAssignedVars b
  | .mk (.lam _ b) _ => tAssignedVars b
  | .mk (.app _ args) _ => goE args
  | .mk (.tuple es) _ => goE es
  | .mk (.proj e _) _ => tAssignedVars e
  | .mk (.ifThenElse c t e) _ => tAssignedVars c ++ tAssignedVars t ++ tAssignedVars e
  | .mk (.match_ s arms) _ => tAssignedVars s ++ goA arms
  | .mk (.seq a b) _ => tAssignedVars a ++ tAssignedVars b
  | .mk (.borrow e) _ => tAssignedVars e
  | .mk (.deref e) _ => tAssignedVars e
  | .mk (.forLoop _ lo hi b) _ => tAssignedVars lo ++ tAssignedVars hi ++ tAssignedVars b
  | .mk (.forLoopRev _ lo hi b) _ => tAssignedVars lo ++ tAssignedVars hi ++ tAssignedVars b
  | .mk (.whileLoop c b) _ => tAssignedVars c ++ tAssignedVars b
  | .mk (.earlyReturn e) _ => tAssignedVars e
  | .mk (.questionMark e) _ => tAssignedVars e
  | .mk (.forFold _ lo hi b) _ => tAssignedVars lo ++ tAssignedVars hi ++ tAssignedVars b
  | .mk (.forFoldRev _ lo hi b) _ => tAssignedVars lo ++ tAssignedVars hi ++ tAssignedVars b
  | .mk (.whileFold c b) _ => tAssignedVars c ++ tAssignedVars b
  | .mk (.forFoldReturn _ lo hi b) _ => tAssignedVars lo ++ tAssignedVars hi ++ tAssignedVars b
  | .mk (.forFoldRevReturn _ lo hi b) _ => tAssignedVars lo ++ tAssignedVars hi ++ tAssignedVars b
  | .mk (.whileFoldReturn c b) _ => tAssignedVars c ++ tAssignedVars b
  | .mk (.cfBreak e) _ => tAssignedVars e
  | .mk (.cfContinue e) _ => tAssignedVars e
  | .mk (.cfBreakContinue e) _ => tAssignedVars e
  | .mk (.ann e) _ => tAssignedVars e
  | .mk (.namedProj _ e) _ => tAssignedVars e
  | .mk (.break_ (some e)) _ => tAssignedVars e
  | _ => []
where
  goE : List TExpr → List String
    | [] => []
    | e :: es => tAssignedVars e ++ goE es
  goA : List (ImpPat × TExpr) → List String
    | [] => []
    | (_, e) :: rest => tAssignedVars e ++ goA rest

/-- Names referenced (`.var`) anywhere in `e` (over-approximate: ignores binders). -/
def tVarRefs : TExpr → List String
  | .mk (.var n) _ => [n]
  | .mk (.letBind _ v b) _ => tVarRefs v ++ tVarRefs b
  | .mk (.lam _ b) _ => tVarRefs b
  | .mk (.app _ args) _ => goE args
  | .mk (.tuple es) _ => goE es
  | .mk (.proj e _) _ => tVarRefs e
  | .mk (.ifThenElse c t e) _ => tVarRefs c ++ tVarRefs t ++ tVarRefs e
  | .mk (.match_ s arms) _ => tVarRefs s ++ goA arms
  | .mk (.seq a b) _ => tVarRefs a ++ tVarRefs b
  | .mk (.borrow e) _ => tVarRefs e
  | .mk (.deref e) _ => tVarRefs e
  | .mk (.assign _ rhs) _ => tVarRefs rhs
  | .mk (.forLoop _ lo hi b) _ => tVarRefs lo ++ tVarRefs hi ++ tVarRefs b
  | .mk (.forLoopRev _ lo hi b) _ => tVarRefs lo ++ tVarRefs hi ++ tVarRefs b
  | .mk (.whileLoop c b) _ => tVarRefs c ++ tVarRefs b
  | .mk (.earlyReturn e) _ => tVarRefs e
  | .mk (.questionMark e) _ => tVarRefs e
  | .mk (.forFold _ lo hi b) _ => tVarRefs lo ++ tVarRefs hi ++ tVarRefs b
  | .mk (.forFoldRev _ lo hi b) _ => tVarRefs lo ++ tVarRefs hi ++ tVarRefs b
  | .mk (.whileFold c b) _ => tVarRefs c ++ tVarRefs b
  | .mk (.forFoldReturn _ lo hi b) _ => tVarRefs lo ++ tVarRefs hi ++ tVarRefs b
  | .mk (.forFoldRevReturn _ lo hi b) _ => tVarRefs lo ++ tVarRefs hi ++ tVarRefs b
  | .mk (.whileFoldReturn c b) _ => tVarRefs c ++ tVarRefs b
  | .mk (.cfBreak e) _ => tVarRefs e
  | .mk (.cfContinue e) _ => tVarRefs e
  | .mk (.cfBreakContinue e) _ => tVarRefs e
  | .mk (.ann e) _ => tVarRefs e
  | .mk (.namedProj _ e) _ => tVarRefs e
  | .mk (.break_ (some e)) _ => tVarRefs e
  | _ => []
where
  goE : List TExpr → List String
    | [] => []
    | e :: es => tVarRefs e ++ goE es
  goA : List (ImpPat × TExpr) → List String
    | [] => []
    | (_, e) :: rest => tVarRefs e ++ goA rest

/-- Whether `e` contains a loop / fold construct. Used to decide whether to thread
    mutations through an `if` that sits *inside* a fold body: when the continuation
    feeds a subsequent loop (so the loop needs the merged post-`if` state) the
    threading is required and safe, whereas an `if` whose mutated variables merely
    become the enclosing fold's accumulator return must be left to the accumulator
    mechanism. -/
def tContainsLoop : TExpr → Bool
  | .mk (.forLoop ..) _ => true
  | .mk (.forLoopRev ..) _ => true
  | .mk (.whileLoop ..) _ => true
  | .mk (.forFold ..) _ => true
  | .mk (.forFoldRev ..) _ => true
  | .mk (.whileFold ..) _ => true
  | .mk (.forFoldReturn ..) _ => true
  | .mk (.forFoldRevReturn ..) _ => true
  | .mk (.whileFoldReturn ..) _ => true
  | .mk (.letBind _ v b) _ => tContainsLoop v || tContainsLoop b
  | .mk (.lam _ b) _ => tContainsLoop b
  | .mk (.app _ args) _ => goE args
  | .mk (.tuple es) _ => goE es
  | .mk (.proj e _) _ => tContainsLoop e
  | .mk (.ifThenElse c t e) _ => tContainsLoop c || tContainsLoop t || tContainsLoop e
  | .mk (.match_ s arms) _ => tContainsLoop s || goA arms
  | .mk (.seq a b) _ => tContainsLoop a || tContainsLoop b
  | .mk (.borrow e) _ => tContainsLoop e
  | .mk (.deref e) _ => tContainsLoop e
  | .mk (.assign _ rhs) _ => tContainsLoop rhs
  | .mk (.earlyReturn e) _ => tContainsLoop e
  | .mk (.questionMark e) _ => tContainsLoop e
  | .mk (.cfBreak e) _ => tContainsLoop e
  | .mk (.cfContinue e) _ => tContainsLoop e
  | .mk (.cfBreakContinue e) _ => tContainsLoop e
  | .mk (.ann e) _ => tContainsLoop e
  | .mk (.namedProj _ e) _ => tContainsLoop e
  | .mk (.break_ (some e)) _ => tContainsLoop e
  | _ => false
where
  goE : List TExpr → Bool
    | [] => false
    | e :: es => tContainsLoop e || goE es
  goA : List (ImpPat × TExpr) → Bool
    | [] => false
    | (_, e) :: rest => tContainsLoop e || goA rest

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
def tReplaceTail : TExpr → TExpr → TExpr
  | .mk (.letBind n v body) ty, newTail => .mk (.letBind n v (tReplaceTail body newTail)) ty
  | .mk (.seq a b) ty, newTail => .mk (.seq a (tReplaceTail b newTail)) ty
  | .mk (.assign n r) ty, newTail => .mk (.seq (.mk (.assign n r) ty) newTail) ty
  | _, newTail => newTail

/-- Strip the erase-deleted `.ann` type-ascription marker. Used so that the
    `if`-statement detection in `tThreadMut` looks through `.ann` and thus
    commutes with type erasure. No `.ann` nodes exist at this pre-pipeline
    stage, so this is the identity on real inputs. -/
def tStripAnn : TExpr → TExpr
  | .mk (.ann e) _ => tStripAnn e
  | e => e

/-- Thread mutations across `if`-statement joins (see module docstring).

    `active` gates the join-threading transformation. It is `true` in
    straight-line / function-tail position and `false` inside a loop or fold
    body — there the loop accumulator mechanism (in the renderer's
    `extractAccumulators` / fold-body transforms) already threads mutated
    variables, and a competing `_mtup` rebind here would mis-detect the
    accumulator (e.g. collapse it to `()`) and emit inconsistent branch types.
    We still recurse into loop bodies (to reach nested straight-line `if`s) but
    with `active := false`. -/
partial def tThreadMut (active : Bool) (e : TExpr) : TExpr :=
  match e.kind with
  | .seq (.mk (.ifThenElse c t f) ifTy) rest =>
    let c := tThreadMut active c
    let t := tThreadMut active t
    let f := tThreadMut active f
    let rest := tThreadMut active rest
    let used := tVarRefs rest
    let m := (tAssignedVars t ++ tAssignedVars f).eraseDups.filter used.contains
    -- Fire at straight-line/top-level position (`active`), or — even inside a fold
    -- body — when the continuation contains a loop that consumes the merged state.
    if (!active && !tContainsLoop rest) || m.isEmpty then
      .mk (.seq (.mk (.ifThenElse c t f) ifTy) rest) e.ty
    else
      let tup := tVarTuple m
      let ifE := .mk (.ifThenElse c (tReplaceTail t tup) (tReplaceTail f tup)) .unknown
      .mk (.letBind "_mtup" ifE (tDestructure m (.mk (.var "_mtup") .unknown) rest)) e.ty
  -- Loop / fold bodies: descend with the transformation disabled.
  | .forLoop v lo hi b => .mk (.forLoop v (tThreadMut active lo) (tThreadMut active hi) (tThreadMut false b)) e.ty
  | .forLoopRev v lo hi b => .mk (.forLoopRev v (tThreadMut active lo) (tThreadMut active hi) (tThreadMut false b)) e.ty
  | .forFold v lo hi b => .mk (.forFold v (tThreadMut active lo) (tThreadMut active hi) (tThreadMut false b)) e.ty
  | .forFoldRev v lo hi b => .mk (.forFoldRev v (tThreadMut active lo) (tThreadMut active hi) (tThreadMut false b)) e.ty
  | .forFoldReturn v lo hi b => .mk (.forFoldReturn v (tThreadMut active lo) (tThreadMut active hi) (tThreadMut false b)) e.ty
  | .forFoldRevReturn v lo hi b => .mk (.forFoldRevReturn v (tThreadMut active lo) (tThreadMut active hi) (tThreadMut false b)) e.ty
  | .whileLoop c b => .mk (.whileLoop (tThreadMut active c) (tThreadMut false b)) e.ty
  | .whileFold c b => .mk (.whileFold (tThreadMut active c) (tThreadMut false b)) e.ty
  | .whileFoldReturn c b => .mk (.whileFoldReturn (tThreadMut active c) (tThreadMut false b)) e.ty
  | _ => tMapChildren (tThreadMut active) e

end Hax

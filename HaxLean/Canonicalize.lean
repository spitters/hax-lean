/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.AST
public import HaxLean.FreeVars

/-!
# Canonicalization passes for the post-pipeline ImpExpr

These passes rewrite the ImpExpr produced by the verified pipeline into a
*canonical* form whose constructors map one-to-one onto Lean syntax. After
canonicalization, the unverified `toLean` pretty-printer becomes a trivial
syntax mapping and per-function agreement is `rfl` by construction.

## Pass list (this file)

* `canonicalizeDeadCFBindings` — drops `letBind n (cfBreak _) body` when
  `n.startsWith "_"` (and similar for `cfContinue` / `cfBreakContinue`), and
  binds any other such `n` to `cfBreak ()`, when `n` is not free in `body`.
* `canonicalizeIfElseAssign` — replaces the `_assign` else branch of
  `letBind n (ifThenElse c t (var m)) body` by `()` when `n` is not free in `body`.
* `canonicalizeRefusals` — the bindings these two passes keep because `body`
  reads `n`.
* `canonicalizePanic` — rewrites `app "panic" _` and `app "panic_fmt" _` to
  `.unitVal`.
* `canonicalizeMutationDiscard` — rewrites
  `letBind n val (var n)` where `n.startsWith "_assign"` to
  `letBind "_" val .unitVal`.

These passes are total `def`s on `ImpExpr` and structurally recursive. Each
follows the verified-pipeline-phase convention from
`Hax/Phase/DropReferences.lean`: list traversals are factored into explicit
`mapExpr` / `mapArms` `where`-helpers that recurse on list structure, and
`@[simp]` lemmas show those helpers equal the obvious `List.map` form.

## Composition

The convenience entry point `canonicalize` runs all passes in order. It is
intended to be applied to each post-pipeline function body **before** the
unverified `toLean` is invoked.
-/

@[expose] public section

namespace Hax.Canonicalize

open Hax

/-! ## Pass D — dead ControlFlow bindings -/

/-- Whether `e` is a ControlFlow node: `cfBreak`, `cfContinue` or `cfBreakContinue`. -/
def isControlFlowNode : ImpExpr → Bool
  | .cfBreak _ | .cfContinue _ | .cfBreakContinue _ => true
  | _ => false

/-- Pass D. On `letBind n v body` with `v` a ControlFlow node
    (`isControlFlowNode`) and `n` not free in `body`, drops the binding when `n`
    starts with `"_"` and otherwise binds `n` to `cfBreak ()`. The value is not
    read, and the ControlFlow nodes carry no runtime effect at the post-pipeline
    `Hax.cfBreak`/`Hax.cfContinue` shapes. A binding whose variable `body` reads
    is kept; `deadCFRefusals` lists it. -/
def canonicalizeDeadCFBindings : ImpExpr → ImpExpr
  | .letBind n v body =>
    if isControlFlowNode v && !(freeVars body).contains n then
      if n.startsWith "_" then canonicalizeDeadCFBindings body
      else .letBind n (.cfBreak (.unitVal)) (canonicalizeDeadCFBindings body)
    else .letBind n (canonicalizeDeadCFBindings v) (canonicalizeDeadCFBindings body)
  | .seq a b =>
    .seq (canonicalizeDeadCFBindings a) (canonicalizeDeadCFBindings b)
  | .ifThenElse c t e =>
    .ifThenElse (canonicalizeDeadCFBindings c)
                (canonicalizeDeadCFBindings t)
                (canonicalizeDeadCFBindings e)
  | .app f args => .app f (mapExpr args)
  | .tuple es => .tuple (mapExpr es)
  | .proj e i => .proj (canonicalizeDeadCFBindings e) i
  | .match_ scrut arms => .match_ (canonicalizeDeadCFBindings scrut) (mapArms arms)
  | .forFold v lo hi body =>
    .forFold v (canonicalizeDeadCFBindings lo)
               (canonicalizeDeadCFBindings hi)
               (canonicalizeDeadCFBindings body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (canonicalizeDeadCFBindings lo)
                  (canonicalizeDeadCFBindings hi)
                  (canonicalizeDeadCFBindings body)
  | .whileFold c body =>
    .whileFold (canonicalizeDeadCFBindings c) (canonicalizeDeadCFBindings body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (canonicalizeDeadCFBindings lo)
                     (canonicalizeDeadCFBindings hi)
                     (canonicalizeDeadCFBindings body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (canonicalizeDeadCFBindings lo)
                        (canonicalizeDeadCFBindings hi)
                        (canonicalizeDeadCFBindings body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (canonicalizeDeadCFBindings c)
                     (canonicalizeDeadCFBindings body)
  | .cfBreak e => .cfBreak (canonicalizeDeadCFBindings e)
  | .cfContinue e => .cfContinue (canonicalizeDeadCFBindings e)
  | .cfBreakContinue e => .cfBreakContinue (canonicalizeDeadCFBindings e)
  | e => e
where
  mapExpr : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => canonicalizeDeadCFBindings e :: mapExpr es
  mapArms : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, canonicalizeDeadCFBindings e) :: mapArms rest

@[simp] theorem canonicalizeDeadCFBindings.mapExpr_eq (es : List ImpExpr) :
    canonicalizeDeadCFBindings.mapExpr es = es.map canonicalizeDeadCFBindings := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [canonicalizeDeadCFBindings.mapExpr, ih]

@[simp] theorem canonicalizeDeadCFBindings.mapArms_eq
    (arms : List (ImpPat × ImpExpr)) :
    canonicalizeDeadCFBindings.mapArms arms =
      arms.map fun (p, e) => (p, canonicalizeDeadCFBindings e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih =>
    obtain ⟨p, e⟩ := pa
    simp [canonicalizeDeadCFBindings.mapArms, ih]

/-! ## Pass E — panic / panic_fmt → unitVal -/

/-- Pass E. Rewrites `app "panic" _` and `app "panic_fmt" _` to `.unitVal`,
    matching how the unverified pretty-printer renders Rust `panic!` calls
    in the extracted code (Rust panics become no-ops in the verified
    pipeline since totality is proved). -/
def canonicalizePanic : ImpExpr → ImpExpr
  | .app f args =>
    if f == "panic" || f == "panic_fmt" then .unitVal
    else .app f (mapExpr args)
  | .letBind n v body =>
    .letBind n (canonicalizePanic v) (canonicalizePanic body)
  | .seq a b => .seq (canonicalizePanic a) (canonicalizePanic b)
  | .ifThenElse c t e =>
    .ifThenElse (canonicalizePanic c) (canonicalizePanic t) (canonicalizePanic e)
  | .tuple es => .tuple (mapExpr es)
  | .proj e i => .proj (canonicalizePanic e) i
  | .match_ scrut arms => .match_ (canonicalizePanic scrut) (mapArms arms)
  | .forFold v lo hi body =>
    .forFold v (canonicalizePanic lo) (canonicalizePanic hi) (canonicalizePanic body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (canonicalizePanic lo) (canonicalizePanic hi) (canonicalizePanic body)
  | .whileFold c body => .whileFold (canonicalizePanic c) (canonicalizePanic body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (canonicalizePanic lo) (canonicalizePanic hi) (canonicalizePanic body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (canonicalizePanic lo) (canonicalizePanic hi) (canonicalizePanic body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (canonicalizePanic c) (canonicalizePanic body)
  | .cfBreak e => .cfBreak (canonicalizePanic e)
  | .cfContinue e => .cfContinue (canonicalizePanic e)
  | .cfBreakContinue e => .cfBreakContinue (canonicalizePanic e)
  | e => e
where
  mapExpr : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => canonicalizePanic e :: mapExpr es
  mapArms : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, canonicalizePanic e) :: mapArms rest

@[simp] theorem canonicalizePanic.mapExpr_eq (es : List ImpExpr) :
    canonicalizePanic.mapExpr es = es.map canonicalizePanic := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [canonicalizePanic.mapExpr, ih]

@[simp] theorem canonicalizePanic.mapArms_eq (arms : List (ImpPat × ImpExpr)) :
    canonicalizePanic.mapArms arms = arms.map fun (p, e) => (p, canonicalizePanic e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih =>
    obtain ⟨p, e⟩ := pa
    simp [canonicalizePanic.mapArms, ih]

/-! ## Pass C — mutation-discard `_assign` patterns -/

/-- Pass C. Rewrites `letBind n val (var n)` where `n.startsWith "_assign"`
    to `letBind "_" val .unitVal`. The `_assign…` family is introduced by
    the localMutation phase as a discard target; its self-reference at the
    body position is the parser's "consume the assigned value" idiom. The
    canonical form makes this discard explicit and lets `toLean` render
    `let _ := val` without the previous self-reference detection. -/
def canonicalizeMutationDiscard : ImpExpr → ImpExpr
  | .letBind n val body =>
    let val' := canonicalizeMutationDiscard val
    let body' := canonicalizeMutationDiscard body
    if n.startsWith "_assign" && body' == .var n then
      .letBind "_" val' .unitVal
    else
      .letBind n val' body'
  | .seq a b =>
    .seq (canonicalizeMutationDiscard a) (canonicalizeMutationDiscard b)
  | .ifThenElse c t e =>
    .ifThenElse (canonicalizeMutationDiscard c)
                (canonicalizeMutationDiscard t)
                (canonicalizeMutationDiscard e)
  | .app f args => .app f (mapExpr args)
  | .tuple es => .tuple (mapExpr es)
  | .proj e i => .proj (canonicalizeMutationDiscard e) i
  | .match_ scrut arms => .match_ (canonicalizeMutationDiscard scrut) (mapArms arms)
  | .forFold v lo hi body =>
    .forFold v (canonicalizeMutationDiscard lo)
               (canonicalizeMutationDiscard hi)
               (canonicalizeMutationDiscard body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (canonicalizeMutationDiscard lo)
                  (canonicalizeMutationDiscard hi)
                  (canonicalizeMutationDiscard body)
  | .whileFold c body =>
    .whileFold (canonicalizeMutationDiscard c) (canonicalizeMutationDiscard body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (canonicalizeMutationDiscard lo)
                     (canonicalizeMutationDiscard hi)
                     (canonicalizeMutationDiscard body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (canonicalizeMutationDiscard lo)
                        (canonicalizeMutationDiscard hi)
                        (canonicalizeMutationDiscard body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (canonicalizeMutationDiscard c)
                     (canonicalizeMutationDiscard body)
  | .cfBreak e => .cfBreak (canonicalizeMutationDiscard e)
  | .cfContinue e => .cfContinue (canonicalizeMutationDiscard e)
  | .cfBreakContinue e => .cfBreakContinue (canonicalizeMutationDiscard e)
  | e => e
where
  mapExpr : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => canonicalizeMutationDiscard e :: mapExpr es
  mapArms : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, canonicalizeMutationDiscard e) :: mapArms rest

@[simp] theorem canonicalizeMutationDiscard.mapExpr_eq (es : List ImpExpr) :
    canonicalizeMutationDiscard.mapExpr es = es.map canonicalizeMutationDiscard := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [canonicalizeMutationDiscard.mapExpr, ih]

@[simp] theorem canonicalizeMutationDiscard.mapArms_eq
    (arms : List (ImpPat × ImpExpr)) :
    canonicalizeMutationDiscard.mapArms arms =
      arms.map fun (p, e) => (p, canonicalizeMutationDiscard e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih =>
    obtain ⟨p, e⟩ := pa
    simp [canonicalizeMutationDiscard.mapArms, ih]

/-! ## Pass G — if-else-assign self-reference -/

/-- Pass G. Rewrites `letBind n (.ifThenElse c thn (.var elsV)) body` where
    `n.startsWith "_assign"` and `elsV.startsWith "_assign"` to drop the
    self-referential else branch (which would refer to a previous `_assign`
    of possibly different type). The canonical form replaces the else
    branch with `.unitVal`. Combined with Pass C, downstream rendering
    of `_assign` patterns is uniform. The rewrite applies only when `n` is not
    free in `body`, so that the value is not read; otherwise the binding is
    kept and `ifElseAssignRefusals` lists it. -/
def canonicalizeIfElseAssign : ImpExpr → ImpExpr
  | .letBind n (.ifThenElse c thn (.var elsV)) body =>
    let c' := canonicalizeIfElseAssign c
    let thn' := canonicalizeIfElseAssign thn
    let body' := canonicalizeIfElseAssign body
    if n.startsWith "_assign" && elsV.startsWith "_assign" &&
        !(freeVars body).contains n then
      .letBind n (.ifThenElse c' thn' .unitVal) body'
    else
      .letBind n (.ifThenElse c' thn' (.var elsV)) body'
  | .letBind n v body =>
    .letBind n (canonicalizeIfElseAssign v) (canonicalizeIfElseAssign body)
  | .seq a b =>
    .seq (canonicalizeIfElseAssign a) (canonicalizeIfElseAssign b)
  | .ifThenElse c t e =>
    .ifThenElse (canonicalizeIfElseAssign c)
                (canonicalizeIfElseAssign t)
                (canonicalizeIfElseAssign e)
  | .app f args => .app f (mapExpr args)
  | .tuple es => .tuple (mapExpr es)
  | .proj e i => .proj (canonicalizeIfElseAssign e) i
  | .match_ scrut arms => .match_ (canonicalizeIfElseAssign scrut) (mapArms arms)
  | .forFold v lo hi body =>
    .forFold v (canonicalizeIfElseAssign lo)
               (canonicalizeIfElseAssign hi)
               (canonicalizeIfElseAssign body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (canonicalizeIfElseAssign lo)
                  (canonicalizeIfElseAssign hi)
                  (canonicalizeIfElseAssign body)
  | .whileFold c body =>
    .whileFold (canonicalizeIfElseAssign c) (canonicalizeIfElseAssign body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (canonicalizeIfElseAssign lo)
                     (canonicalizeIfElseAssign hi)
                     (canonicalizeIfElseAssign body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (canonicalizeIfElseAssign lo)
                        (canonicalizeIfElseAssign hi)
                        (canonicalizeIfElseAssign body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (canonicalizeIfElseAssign c)
                     (canonicalizeIfElseAssign body)
  | .cfBreak e => .cfBreak (canonicalizeIfElseAssign e)
  | .cfContinue e => .cfContinue (canonicalizeIfElseAssign e)
  | .cfBreakContinue e => .cfBreakContinue (canonicalizeIfElseAssign e)
  | e => e
where
  mapExpr : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => canonicalizeIfElseAssign e :: mapExpr es
  mapArms : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, canonicalizeIfElseAssign e) :: mapArms rest

@[simp] theorem canonicalizeIfElseAssign.mapExpr_eq (es : List ImpExpr) :
    canonicalizeIfElseAssign.mapExpr es = es.map canonicalizeIfElseAssign := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [canonicalizeIfElseAssign.mapExpr, ih]

@[simp] theorem canonicalizeIfElseAssign.mapArms_eq
    (arms : List (ImpPat × ImpExpr)) :
    canonicalizeIfElseAssign.mapArms arms =
      arms.map fun (p, e) => (p, canonicalizeIfElseAssign e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih =>
    obtain ⟨p, e⟩ := pa
    simp [canonicalizeIfElseAssign.mapArms, ih]

/-! ## Bindings the passes keep -/

/-- The immediate subexpressions of `e`. -/
def subExprs : ImpExpr → List ImpExpr
  | .letBind _ v b => [v, b]
  | .lam _ b => [b]
  | .app _ es | .tuple es => es
  | .match_ s arms => s :: arms.map (·.2)
  | .ifThenElse c t e => [c, t, e]
  | .seq a b | .whileLoop a b | .whileFold a b | .whileFoldReturn a b => [a, b]
  | .forLoop _ lo hi b | .forLoopRev _ lo hi b | .forFold _ lo hi b | .forFoldRev _ lo hi b
  | .forFoldReturn _ lo hi b | .forFoldRevReturn _ lo hi b => [lo, hi, b]
  | .proj e _ | .borrow e | .deref e | .assign _ e | .break_ (some e) | .earlyReturn e
  | .questionMark e | .cfBreak e | .cfContinue e | .cfBreakContinue e
  | .typeAscription e _ => [e]
  | .lit _ | .var _ | .unitVal | .break_ none | .continue_ => []

/-- The bindings `letBind n v body` of `e`, with `v` a ControlFlow node and `n`
    free in `body`, that Pass D (`canonicalizeDeadCFBindings`) keeps: the
    variables read after the binding of a ControlFlow value. -/
partial def deadCFRefusals (e : ImpExpr) : List String :=
  let here := match e with
    | .letBind n v body =>
      if isControlFlowNode v && (freeVars body).contains n then
        [s!"the ControlFlow value bound to `{n}` is read after its binding"]
      else []
    | _ => []
  here ++ (subExprs e).flatMap deadCFRefusals

/-- The bindings `letBind n (ifThenElse c t (var m)) body` of `e`, with `n` and
    `m` starting with `_assign` and `n` free in `body`, that Pass G
    (`canonicalizeIfElseAssign`) keeps. -/
partial def ifElseAssignRefusals (e : ImpExpr) : List String :=
  let here := match e with
    | .letBind n (.ifThenElse _ _ (.var m)) body =>
      if n.startsWith "_assign" && m.startsWith "_assign" && (freeVars body).contains n then
        [s!"the conditional assignment `{n}` with the else branch `{m}` is read after its binding"]
      else []
    | _ => []
  here ++ (subExprs e).flatMap ifElseAssignRefusals

/-- The bindings of `e` that Pass D and Pass G keep (`deadCFRefusals`,
    `ifElseAssignRefusals`); `haxpipeT` refuses a definition that has one. -/
def canonicalizeRefusals (e : ImpExpr) : List String :=
  deadCFRefusals e ++ ifElseAssignRefusals e

/-! ## Composite entry point -/

/-- Run the canonicalization passes in order: dead-CF bindings → panic
    → mutation discard → if-else-assign. Each pass is idempotent and
    preserves semantics (modulo the `toLean` simplifications they enable). -/
def canonicalize (e : ImpExpr) : ImpExpr :=
  e |> canonicalizeDeadCFBindings
    |> canonicalizePanic
    |> canonicalizeIfElseAssign
    |> canonicalizeMutationDiscard

end Hax.Canonicalize

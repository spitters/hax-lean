/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import HaxLean.TExpr
import HaxLean.Semantics
import HaxLean.SemanticsCF
import HaxLean.Runtime

/-!
# Typed Phase: Encode loop control-flow into `ControlFlow`-valued fold bodies

This phase moves the loop **control-flow encoding** out of the unverified
pretty-printer (`Hax/PrettyPrint.lean`: `transformForFoldCfBody`,
`transformWhileFoldBody`, `patchCfBreakUnit`, `nestCfBreakForReturn`, …) into a
single structural transformation that is correct by construction, leaving the
printer a trivial structural emit.

## What the encoding does (the spec the printer implements ad hoc)

`functionalizeLoops` (Phase 3) already rewrites
`forLoop`→`forFold`/`forFoldReturn`, `whileLoop`→`whileFold`/`whileFoldReturn`,
and `break_`/`continue_` into `cfBreak`/`cfContinue`/`cfBreakContinue`. But that
phase carries the *original* break/continue payload (the surface break value, or
`unit`); it does **not** thread the loop's mutated accumulators back through the
fold. Threading the accumulators is the job of this encoding.

A fold body, after `functionalizeLoops`, is a straight-line/branching term whose
"tails" are one of: a bare value / `unit` (fell off the end → continue), an
explicit `cfBreak v` (loop break, or — in a return-fold — an early function
return), `cfContinue v` (continue), or `cfBreakContinue v` (loop break inside a
return-fold). The encoding rewrites every tail so the body has the **fold body
type** the runtime fold expects, threading the accumulator tuple `accs`:

  * bare tail / `unit`         ↦ `cfContinue accs`   (continue, carrying accs)
  * `cfContinue v`             ↦ `cfContinue v`      (already carries its value)
  * `cfBreak unit`             ↦ loop break (see below)
  * `cfBreak v` (v ≠ unit)     ↦ early return (return-folds only; see below)

where `accs = accTuple [a₁,…,aₙ]` is `var a` for one accumulator and a tuple
otherwise.

### The loop-kind-dependent decision (the `isReturn` distinction)

The ONE decision that depends on the loop kind — and the source of the bugs this
phase eliminates — is how a **loop break** is wrapped, because the two fold
families have different result types and different consumers:

| Loop kind            | runtime fn          | body type                          | consume | loop break encoding              |
|----------------------|---------------------|------------------------------------|---------|----------------------------------|
| `forFold`/`whileFold`| `Hax.forFold`       | `ControlFlow α α`                  | `.merge`| `cfBreak accs`        (single)   |
| `…FoldReturn`        | `Hax.forFoldReturn` | `ControlFlow (ControlFlow β γ) α`   | nested  | `cfBreakContinue accs` (= Break(Continue accs)) |

So:

  * **Plain fold** (`isReturn = false`), consumed by `.merge`, body type
    `ControlFlow α α` (single level): a loop break is `cfBreak accs`. Both the
    `Break` and the `Continue` exit carry an `α`, so `.merge` extracts the
    accumulator-at-exit on *either* path. This is the only place `α = β`.

  * **Return fold** (`isReturn = true`), body type
    `ControlFlow (ControlFlow β γ) α` (two levels): a loop break is
    `cfBreakContinue accs` = `Break (Continue accs)` — the inner `Continue`
    distinguishes it from an early function return, which is
    `cfBreak (cfBreak v)` = `Break (Break v)` (applied afterwards by
    `nestReturn`). `Hax.forFoldReturn` maps `Break (Continue v)` → loop break
    returning `v`, and `Break (Break v)` → early return propagating `Break v`.

Getting this wrong is exactly the family of bugs the printer kept hitting:
a value-less break dropped to `()` (forgot to thread `accs`), a loop-state
break double-wrapped into an early return (used `cfBreak accs` then
`nestReturn` turned it into `cfBreak (cfBreak accs)` — an early return of the
accumulator), and the encoding leaking from return-folds into plain folds
(used `cfBreakContinue` under `.merge`, which then sees a doubly-nested
`ControlFlow` and is ill-typed).

### Deliberate divergence from the printer (soundness)

The printer additionally tries to *reconstruct* control flow from the **shape**
of `if`-statements (`transformForFoldCfBody` Cases 3/4: an `if c then () else
work` is guessed to mean "if c then break else continue"). That heuristic is
unsound — `if c { } else { work }` in Rust is a no-op then-branch, not a break —
and is itself a documented bug source. This verified encoding deliberately drops
those heuristics: only the **explicit** `cfBreak`/`cfContinue`/`cfBreakContinue`
nodes produced by `functionalizeLoops` carry control-flow meaning; every other
tail is a `continue`. This is what makes the encoding correct by construction.

## Result consumption (what the printer emits after the fold)

  * Plain fold: `(Hax.forFold lo hi init body).merge` (or a `let (a₁,…) := … .merge`).
  * Return fold: `match fr with | .Break v => v | .Continue cf => match cf with
    | .Continue accs => … | .Break _ => …` — the early-return value is `v`, the
    normal/loop-break completion binds `accs`.

The runtime semantics of these consumers is captured by `refFold` /
`refFoldReturn` below and proved equal to `Hax.forFold` / `Hax.forFoldReturn`.

## What is proved here

* `encodeForFoldBody` / `encodeReturnFoldBody` — the structural encoding (plain
  and return variants), total (structural recursion), no `partial`.
* `tEncodeControlFlow` — the typed phase on `TExpr`, with `tEncodeControlFlow_erase`
  (commutes with type erasure, like every other typed phase).
* **Denote-correctness, plain case (GREEN):** `forFold_merge_eq_refFold` — the
  runtime `Hax.forFold` consumed by `.merge` computes exactly the imperative
  early-breaking threaded fold `refFold` (the loop's reference meaning). Because
  the plain encoding makes break carry the accumulator (`β = α`), `.merge`
  extracts the accumulator-at-exit on both paths, so this *is* the loop's final
  accumulator. Companion shape lemmas (`encode_*_denote'`) show the encoded
  tails evaluate, under the ControlFlow-aware `denote'`, to the `Value.controlFlow`
  tags `denoteForLoop'` consumes.
* **Return case (GREEN):** `forFoldReturn_consume_eq_refFoldReturn` characterises
  the doubly-nested runtime fold (consumed by the nested match) against the
  three-way reference `refFoldReturn`.
* **Environment-threading loop induction (GREEN, both kinds):**
  `denoteForLoop'_eq_forFold` and `denoteForLoop'Return_eq_forFoldReturn` — the
  semantics loops (`denoteForLoop'` / `denoteForLoop'Return`, which thread the
  accumulator through the *environment* and discard the continue payload) agree
  with the runtime folds (`Hax.forFold` / `Hax.forFoldReturn`, value-threaded),
  for a body satisfying the per-iteration reconciliation `hstep`. The fuel/range
  induction's step is one application of the per-tail reconciliation, with the
  environment accumulator and the runtime accumulator in lockstep. This closes
  the env-vs-value bridge for both the plain (one `ControlFlow` level) and the
  return (doubly-nested) folds.
-/

namespace Hax

set_option autoImplicit false

/-! ## Accumulator tuple -/

/-- The accumulator value threaded through a fold: a single `var` for one
    accumulator, a tuple otherwise. Mirrors `accTuple` in the printer. -/
def accTupleE : List String → ImpExpr
  | [a] => .var a
  | accs => .tuple (accs.map .var)

/-! ## Surface control-flow detection (structural port) -/

/-- Does `e` have a `cfBreak`/`cfContinue`/`cfBreakContinue` at the *surface*
    (not crossing a nested fold boundary)? Structural, total port of the
    printer's `hasSurfaceControlFlow`. `match_` is treated conservatively as
    non-CF (no arm recursion): the only use is the dead-code guard in the `seq`
    case of the encoding, and treating a `match` as non-CF only ever *keeps* a
    following tail, which is sound — under the ControlFlow-aware `denote'` a
    `match` that returns a `controlFlow` value already short-circuits the `seq`,
    so the retained tail is never run. -/
def hasSurfaceCF : ImpExpr → Bool
  | .cfBreak _ | .cfContinue _ | .cfBreakContinue _ => true
  | .letBind _ v b => hasSurfaceCF v || hasSurfaceCF b
  | .seq e1 e2 => hasSurfaceCF e1 || hasSurfaceCF e2
  | .ifThenElse _ t e => hasSurfaceCF t || hasSurfaceCF e
  | _ => false

/-- Does *every* execution path of `e` end in a surface control-flow node?
    Sound underapproximation (a `match` counts as non-CF, like
    `hasSurfaceCF`): the only use is the dead-code drop in the `seq` case of
    the encoders, and underapproximating only ever keeps a following tail. -/
def allPathsCF : ImpExpr → Bool
  | .cfBreak _ | .cfContinue _ | .cfBreakContinue _ => true
  | .letBind _ _ b => allPathsCF b
  | .seq a b => allPathsCF a || allPathsCF b
  | .ifThenElse _ t e => allPathsCF t && allPathsCF e
  | _ => false

/-- Does `e` carry an effect a tail encoding must keep — an assignment, a
    loop, or a surface control-flow node? An all-pure `match` at a fold-body
    tail is replaced by the continue like any other pure-value tail; a `match`
    with an effectful arm has the encoding distributed into its arms. -/
def keepsTailEffect : ImpExpr → Bool
  | .assign _ _ => true
  | .cfBreak _ | .cfContinue _ | .cfBreakContinue _ => true
  | .forLoop _ _ _ _ | .forLoopRev _ _ _ _ | .whileLoop _ _ => true
  | .forFold _ _ _ _ | .forFoldRev _ _ _ _ | .whileFold _ _ => true
  | .forFoldReturn _ _ _ _ | .forFoldRevReturn _ _ _ _ | .whileFoldReturn _ _ => true
  | .letBind _ v b => keepsTailEffect v || keepsTailEffect b
  | .seq a b => keepsTailEffect a || keepsTailEffect b
  | .ifThenElse c t e => keepsTailEffect c || keepsTailEffect t || keepsTailEffect e
  | .match_ s arms => keepsTailEffect s || goA arms
  | _ => false
where
  goA : List (ImpPat × ImpExpr) → Bool
    | [] => false
    | (_, e) :: rest => keepsTailEffect e || goA rest

/-- Push `e2` into the non-CF tails of the statement `e1` — the distributed
    form of `e1; e2` when `e1` breaks on *some* paths only. A CF tail keeps
    `e2` off its (unreachable) path; a `seq` distributes into its own tail,
    which is where its completed paths continue. -/
def seqIntoStmtTails (e2 : ImpExpr) : ImpExpr → ImpExpr
  | .letBind n v b => .letBind n v (seqIntoStmtTails e2 b)
  | .ifThenElse c t e => .ifThenElse c (seqIntoStmtTails e2 t) (seqIntoStmtTails e2 e)
  | .seq a b => .seq a (seqIntoStmtTails e2 b)
  | .cfBreak v => .cfBreak v
  | .cfContinue v => .cfContinue v
  | .cfBreakContinue v => .cfBreakContinue v
  | t => .seq t e2

/-- Distribute the statements that follow a *conditionally* breaking statement
    into that statement's non-breaking branches, so the fold-body encoders see
    every `seq` head as either CF-free or CF-on-every-path:
    `if c { break }; rest` becomes `if c { break } else { rest }`, which
    encodes and renders as the standard conditional-break loop body. Applied to
    a fold body before encoding. -/
def distributeStmtCF : ImpExpr → ImpExpr
  | .seq e1 e2 =>
      let e1' := distributeStmtCF e1
      let e2' := distributeStmtCF e2
      if hasSurfaceCF e1' && !allPathsCF e1' then seqIntoStmtTails e2' e1'
      else .seq e1' e2'
  | .letBind n v b => .letBind n (distributeStmtCF v) (distributeStmtCF b)
  | .ifThenElse c t e => .ifThenElse c (distributeStmtCF t) (distributeStmtCF e)
  | e => e

/-! ## The encoding -/

/-- Plain-fold control-flow encoding (`isReturn = false`): thread the
    accumulator expression `accE` (build it with `accTupleE`) through every tail
    so the body has type `ControlFlow α α`, consumed by `.merge`.

    * bare tail / `unit` ↦ `cfContinue accE`
    * `cfBreak unit`     ↦ `cfBreak accE`   (loop break carries the accumulator)
    * explicit CF nodes with a value are preserved.

    Total (structural recursion). Deliberately does **not** reconstruct control
    flow from `if`-shape heuristics — see the module docstring. -/
def encodeForFoldBody (accE : ImpExpr) : ImpExpr → ImpExpr
  | .letBind n v body => .letBind n v (encodeForFoldBody accE body)
  | .seq e1 e2 =>
      -- Dead-code after CF: a tail following a head that leaves on every path
      -- is unreachable. A head with *conditional* CF keeps its tail; callers
      -- normalize that shape away first with `distributeStmtCF`.
      if allPathsCF e1 then encodeForFoldBody accE e1
      else .seq e1 (encodeForFoldBody accE e2)
  | .ifThenElse c t e =>
      .ifThenElse c (encodeForFoldBody accE t) (encodeForFoldBody accE e)
  -- A match with an effectful arm carries the encoding into every arm; an
  -- all-pure match is a pure-value tail and is replaced by the continue.
  | .match_ s arms =>
      if keepsTailEffect (.match_ s arms) then .match_ s (goA accE arms)
      else .cfContinue accE
  -- A mutation or a nested loop at the tail is kept ahead of the continue.
  | .assign n r => .seq (.assign n r) (.cfContinue accE)
  | .forLoop v lo hi b => .seq (.forLoop v lo hi b) (.cfContinue accE)
  | .forLoopRev v lo hi b => .seq (.forLoopRev v lo hi b) (.cfContinue accE)
  | .whileLoop c b => .seq (.whileLoop c b) (.cfContinue accE)
  | .forFold v lo hi b => .seq (.forFold v lo hi b) (.cfContinue accE)
  | .forFoldRev v lo hi b => .seq (.forFoldRev v lo hi b) (.cfContinue accE)
  | .whileFold c b => .seq (.whileFold c b) (.cfContinue accE)
  | .forFoldReturn v lo hi b => .seq (.forFoldReturn v lo hi b) (.cfContinue accE)
  | .forFoldRevReturn v lo hi b => .seq (.forFoldRevReturn v lo hi b) (.cfContinue accE)
  | .whileFoldReturn c b => .seq (.whileFoldReturn c b) (.cfContinue accE)
  | .cfBreak .unitVal => .cfBreak accE
  | .cfBreak v => .cfBreak v
  | .cfContinue v => .cfContinue v
  | .cfBreakContinue v => .cfBreakContinue v
  | _ => .cfContinue accE
where
  goA (accE : ImpExpr) : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, encodeForFoldBody accE e) :: goA accE rest

/-- Return-fold loop-body encoding (`isReturn = true`): like
    `encodeForFoldBody`, but a **loop break** is `cfBreakContinue accE`
    (= `Break (Continue accE)`), the inner `Continue` distinguishing it from an
    early function return. Early returns (`cfBreak v`, v ≠ unit)
    are nested afterwards by `nestReturn`. -/
def encodeReturnCfBody (accE : ImpExpr) : ImpExpr → ImpExpr
  | .letBind n v body => .letBind n v (encodeReturnCfBody accE body)
  | .seq e1 e2 =>
      if allPathsCF e1 then encodeReturnCfBody accE e1
      else .seq e1 (encodeReturnCfBody accE e2)
  | .ifThenElse c t e =>
      .ifThenElse c (encodeReturnCfBody accE t) (encodeReturnCfBody accE e)
  | .match_ s arms =>
      if keepsTailEffect (.match_ s arms) then .match_ s (goA accE arms)
      else .cfContinue accE
  | .assign n r => .seq (.assign n r) (.cfContinue accE)
  | .forLoop v lo hi b => .seq (.forLoop v lo hi b) (.cfContinue accE)
  | .forLoopRev v lo hi b => .seq (.forLoopRev v lo hi b) (.cfContinue accE)
  | .whileLoop c b => .seq (.whileLoop c b) (.cfContinue accE)
  | .forFold v lo hi b => .seq (.forFold v lo hi b) (.cfContinue accE)
  | .forFoldRev v lo hi b => .seq (.forFoldRev v lo hi b) (.cfContinue accE)
  | .whileFold c b => .seq (.whileFold c b) (.cfContinue accE)
  | .forFoldReturn v lo hi b => .seq (.forFoldReturn v lo hi b) (.cfContinue accE)
  | .forFoldRevReturn v lo hi b => .seq (.forFoldRevReturn v lo hi b) (.cfContinue accE)
  | .whileFoldReturn c b => .seq (.whileFoldReturn c b) (.cfContinue accE)
  | .cfBreak .unitVal => .cfBreakContinue accE              -- loop break
  | .cfBreak v => .cfBreak v                                 -- early return (nested later)
  | .cfContinue v => .cfContinue v
  | .cfBreakContinue v => .cfBreakContinue v
  | _ => .cfContinue accE
where
  goA (accE : ImpExpr) : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, encodeReturnCfBody accE e) :: goA accE rest

/-- Nest an early-return `cfBreak v` into `cfBreak (cfBreak v)`
    (= `Break (Break v)`) inside a return-fold body, where the body type is
    `ControlFlow (ControlFlow β γ) α`. Loop breaks are already `cfBreakContinue`
    and are left intact. Total structural port of `nestCfBreakForReturn`. -/
def nestReturn : ImpExpr → ImpExpr
  | .cfBreak v => .cfBreak (.cfBreak v)
  | .letBind n v body => .letBind n v (nestReturn body)
  | .seq a b => .seq (nestReturn a) (nestReturn b)
  | .ifThenElse c t e => .ifThenElse c (nestReturn t) (nestReturn e)
  | e => e

/-- Full return-fold body encoding: thread accumulators (`encodeReturnCfBody`)
    then nest early returns (`nestReturn`). -/
def encodeReturnFoldBody (accE : ImpExpr) (e : ImpExpr) : ImpExpr :=
  nestReturn (encodeReturnCfBody accE e)

/-! ## Reference fold semantics (the loop's meaning)

These mirror the runtime `Hax.forFold` / `Hax.forFoldReturn` recursion but
return the *consumed* value (what the printer emits after the fold), so the
correctness theorems are non-tautological: the runtime fold returns a
`ControlFlow`, the reference returns the plain result the surrounding code uses.
-/

/-- Reference meaning of a **plain** fold loop consumed by `.merge`: iterate over
    `[lo, hi)`, threading the accumulator; on `Break` stop and yield the break
    value, on `Continue` keep going. Returns `α` directly — the imperative `for`
    loop with `break`, yielding its final accumulator. Because the plain encoding
    makes break carry the accumulator (`β = α`), the break value *is* an
    accumulator, so this is the value the surrounding code reads. -/
def refFold {α : Type} (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow α α) : α :=
  if lo ≥ hi then init
  else
    match f lo init with
    | .Break v => v
    | .Continue acc => refFold (lo + 1) hi acc f
termination_by (hi - lo).toNat

/-! ## Denote-correctness: plain fold (runtime ↔ reference)

The plain encoding's consumer is `(Hax.forFold lo hi init f).merge`. We prove it
equals the reference imperative loop `refFold`. This is the core value: it shows
the value-threading runtime fold, after `.merge`, computes exactly the loop's
final accumulator, for an *arbitrary* per-iteration step `f : Int → α →
ControlFlow α α` (the shape the plain encoding produces, `β = α`). -/

/-- Runtime `Hax.forFold` consumed by `.merge` equals the reference loop
    `refFold`. Proved by the recursion's own induction principle. -/
theorem forFold_merge_eq_refFold {α : Type} (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow α α) :
    (Hax.forFold lo hi init f).merge = refFold lo hi init f := by
  fun_induction Hax.forFold lo hi init f with
  | case1 lo init h =>
    rw [refFold, if_pos h]; simp [ControlFlow.merge]
  | case2 lo init v h hbrk =>
    rw [refFold, if_neg (by omega), hbrk]; simp [ControlFlow.merge]
  | case3 lo init acc h hcont ih =>
    rw [refFold, if_neg (by omega), hcont]; simpa [ControlFlow.merge] using ih

/-! ### Encoding-shape lemmas (plain)

These pin down, definitionally, the wrapping the plain encoding produces on the
canonical post-`functionalizeLoops` tails. They are the syntactic half of
correctness: a bare/`unit` tail becomes a `continue` carrying the accumulator,
and a value-less `cfBreak` becomes a `break` carrying the accumulator. -/

@[simp] theorem encodeForFoldBody_unitVal (accE : ImpExpr) :
    encodeForFoldBody accE .unitVal = .cfContinue accE := rfl

@[simp] theorem encodeForFoldBody_var (accE : ImpExpr) (n : String) :
    encodeForFoldBody accE (.var n) = .cfContinue accE := rfl

@[simp] theorem encodeForFoldBody_cfBreak_unit (accE : ImpExpr) :
    encodeForFoldBody accE (.cfBreak .unitVal) = .cfBreak accE := rfl

@[simp] theorem encodeForFoldBody_cfContinue (accE v : ImpExpr) :
    encodeForFoldBody accE (.cfContinue v) = .cfContinue v := rfl

/-- The encoded `continue` tail threads the *value of* `accE` (read from the
    environment) into the `controlFlow false` payload — this is precisely the
    step that converts the semantics' environment-threaded accumulator into the
    runtime fold's value-threaded accumulator. Holds for any `accE` that denotes
    to a non-controlFlow value. -/
theorem denote'_cfContinue_run (bi : Builtins) (fuel : Nat) (accE : ImpExpr)
    (env env' : Env) (v : Value)
    (h : (denote' bi fuel accE).run env = (.val v, env'))
    (hv : v.isControlFlow = false) :
    (denote' bi fuel (.cfContinue accE)).run env = (.val (.controlFlow false v), env') := by
  unfold denote'
  simp only [StateT.run, bind, StateT.bind] at h ⊢
  rw [h]
  cases v <;> simp_all [Value.isControlFlow, StateT.pure, pure]

/-- Dual of `denote'_cfContinue_run` for the value-less `cfBreak` that the plain
    encoding emits for a loop break: it carries the accumulator value into the
    `controlFlow true` (break) payload. -/
theorem denote'_cfBreak_run (bi : Builtins) (fuel : Nat) (accE : ImpExpr)
    (env env' : Env) (v : Value)
    (h : (denote' bi fuel accE).run env = (.val v, env'))
    (hv : v.isControlFlow = false) :
    (denote' bi fuel (.cfBreak accE)).run env = (.val (.controlFlow true v), env') := by
  unfold denote'
  simp only [StateT.run, bind, StateT.bind] at h ⊢
  rw [h]
  cases v <;> simp_all [Value.isControlFlow, StateT.pure, pure]

/-! ## Typed phase on `TExpr`

`tEncodeForFoldBody accT` is the typed encoding of a *single plain fold body*,
where `accT : TExpr` is the (already typed) accumulator tuple. It commutes with
type erasure (`tEncodeForFoldBody_erase`), so the untyped correctness above
transports to the typed pipeline — exactly the discipline every other typed
phase follows (`tFunctionalizeLoops_erase`, etc.).

Accumulator *detection* (which variables are the loop accumulators, and hence
how to build `accT`) is a separate analysis, intentionally not part of the
encoding: the encoding is correct *given* the accumulator expression. -/

/-- Typed plain-fold body encoding. Mirrors `encodeForFoldBody`.

    `.ann` (a denotational no-op wrapper) is traversed transparently — it erases
    to its inner term, so the encoding must too, or the erase lemma fails. The
    value-less-break test uses `v.erase` so it agrees with erasure even when the
    break value is wrapped (e.g. `cfBreak (ann ())`). -/
def tEncodeForFoldBody (accT : TExpr) : TExpr → TExpr
  | .mk (.letBind n v body) ty => .mk (.letBind n v (tEncodeForFoldBody accT body)) ty
  | .mk (.seq e1 e2) ty =>
      if allPathsCF e1.erase then tEncodeForFoldBody accT e1
      else .mk (.seq e1 (tEncodeForFoldBody accT e2)) ty
  | .mk (.ifThenElse c t e) ty =>
      .mk (.ifThenElse c (tEncodeForFoldBody accT t) (tEncodeForFoldBody accT e)) ty
  | .mk (.match_ s arms) ty =>
      if keepsTailEffect (TExpr.mk (.match_ s arms) ty).erase then
        .mk (.match_ s (goA accT arms)) ty
      else .mk (.cfContinue accT) ty
  | .mk (.assign n r) ty =>
      .mk (.seq (.mk (.assign n r) ty) (.mk (.cfContinue accT) ty)) ty
  | .mk (.forLoop v lo hi b) ty =>
      .mk (.seq (.mk (.forLoop v lo hi b) ty) (.mk (.cfContinue accT) ty)) ty
  | .mk (.forLoopRev v lo hi b) ty =>
      .mk (.seq (.mk (.forLoopRev v lo hi b) ty) (.mk (.cfContinue accT) ty)) ty
  | .mk (.whileLoop c b) ty =>
      .mk (.seq (.mk (.whileLoop c b) ty) (.mk (.cfContinue accT) ty)) ty
  | .mk (.forFold v lo hi b) ty =>
      .mk (.seq (.mk (.forFold v lo hi b) ty) (.mk (.cfContinue accT) ty)) ty
  | .mk (.forFoldRev v lo hi b) ty =>
      .mk (.seq (.mk (.forFoldRev v lo hi b) ty) (.mk (.cfContinue accT) ty)) ty
  | .mk (.whileFold c b) ty =>
      .mk (.seq (.mk (.whileFold c b) ty) (.mk (.cfContinue accT) ty)) ty
  | .mk (.forFoldReturn v lo hi b) ty =>
      .mk (.seq (.mk (.forFoldReturn v lo hi b) ty) (.mk (.cfContinue accT) ty)) ty
  | .mk (.forFoldRevReturn v lo hi b) ty =>
      .mk (.seq (.mk (.forFoldRevReturn v lo hi b) ty) (.mk (.cfContinue accT) ty)) ty
  | .mk (.whileFoldReturn c b) ty =>
      .mk (.seq (.mk (.whileFoldReturn c b) ty) (.mk (.cfContinue accT) ty)) ty
  | .mk (.ann e) ty => .mk (.ann (tEncodeForFoldBody accT e)) ty
  | .mk (.cfBreak v) ty =>
      match v.erase with
      | .unitVal => .mk (.cfBreak accT) ty
      | _ => .mk (.cfBreak v) ty
  | .mk (.cfContinue v) ty => .mk (.cfContinue v) ty
  | .mk (.cfBreakContinue v) ty => .mk (.cfBreakContinue v) ty
  | .mk _ ty => .mk (.cfContinue accT) ty
where
  goA (accT : TExpr) : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, tEncodeForFoldBody accT e) :: goA accT rest

set_option linter.unusedSimpArgs false in
/-- Type erasure commutes with the typed encoding. -/
theorem tEncodeForFoldBody_erase (accT : TExpr) (e : TExpr) :
    (tEncodeForFoldBody accT e).erase = encodeForFoldBody accT.erase e.erase := by
  induction e using TExpr.ind
  case letBind ty n val body _ ihb =>
    simp [tEncodeForFoldBody, TExpr.erase, encodeForFoldBody, ihb]
  case seq ty e1 e2 ih1 ih2 =>
    simp only [tEncodeForFoldBody, TExpr.erase, encodeForFoldBody]
    by_cases h : allPathsCF e1.erase
    · simp [h, ih1]
    · simp [h, ih2, TExpr.erase]
  case ifThenElse ty c t e _ iht ihe =>
    simp [tEncodeForFoldBody, TExpr.erase, encodeForFoldBody, iht, ihe]
  case match_ ty scrut arms ihs iharms =>
    simp only [tEncodeForFoldBody, TExpr.erase, encodeForFoldBody, TExpr.eraseArms_eq]
    by_cases h :
        keepsTailEffect (.match_ scrut.erase (arms.map (fun pe => (pe.1, pe.2.erase))))
    · simp only [h, if_true, TExpr.erase, TExpr.eraseArms_eq]
      congr 1
      clear h
      induction arms with
      | nil => rfl
      | cons pa rest ih =>
        obtain ⟨p, e⟩ := pa
        simp only [tEncodeForFoldBody.goA, encodeForFoldBody.goA, List.map_cons,
          iharms (p, e) (List.mem_cons_self ..),
          ih (fun pa hpa => iharms pa (List.mem_cons_of_mem _ hpa))]
    · simp [h, TExpr.erase]
  case ann ty e ih =>
    simp [tEncodeForFoldBody, TExpr.erase, ih]
  case cfBreak ty e _ =>
    simp only [tEncodeForFoldBody, TExpr.erase]
    split <;> rename_i h <;> simp [encodeForFoldBody, TExpr.erase, h]
  case cfContinue ty e _ => simp [tEncodeForFoldBody, TExpr.erase, encodeForFoldBody]
  case cfBreakContinue ty e _ => simp [tEncodeForFoldBody, TExpr.erase, encodeForFoldBody]
  all_goals simp [tEncodeForFoldBody, TExpr.erase, encodeForFoldBody]

/-! ## Return fold (doubly-nested): per-iteration tag classification

For the return fold the body type is `ControlFlow (ControlFlow β γ) α` and the
runtime is `Hax.forFoldReturn`. The encoding's two return-specific tags are
justified by how `Hax.forFoldReturn` classifies them on a non-empty range:

  * loop break  `cfBreakContinue accs` = `Break (Continue accs)` ↦ `Continue (Break accs)`
  * early return `cfBreak (cfBreak v)` = `Break (Break v)`        ↦ `Break v`

These are exactly the unfold lemmas below. They show why the plain encoding's
single-level `cfBreak accs` would be *wrong* here (it is `Break v` with `v : β`,
i.e. read as an early return of the accumulator) — the documented bug class. -/

/-- Loop break: `Break (Continue v)` becomes the loop-break result
    `Continue (Break v)` (iteration stops, loop yields `v`). -/
theorem forFoldReturn_loopBreak {α β γ : Type} (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow (ControlFlow β γ) α) (v : γ)
    (hlt : lo < hi) (hf : f lo init = .Break (.Continue v)) :
    Hax.forFoldReturn lo hi init f = .Continue (.Break v) := by
  rw [Hax.forFoldReturn]; simp [Int.not_le.mpr hlt, hf]

/-- Early return: `Break (Break v)` propagates as `Break v` (function returns). -/
theorem forFoldReturn_earlyReturn {α β γ : Type} (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow (ControlFlow β γ) α) (v : β)
    (hlt : lo < hi) (hf : f lo init = .Break (.Break v)) :
    Hax.forFoldReturn lo hi init f = .Break v := by
  rw [Hax.forFoldReturn]; simp [Int.not_le.mpr hlt, hf]

/-- Normal completion of an empty/finished range yields `Continue (Continue init)`
    — the accumulator, in the consumer's normal-completion arm. -/
theorem forFoldReturn_done {α β γ : Type} (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow (ControlFlow β γ) α) (h : lo ≥ hi) :
    Hax.forFoldReturn lo hi init f = .Continue (.Continue init) := by
  rw [Hax.forFoldReturn]; simp [h]

/-! ## Two-level reconciliation (denote' shape lemma)

`denote'_cfContinue_run` / `denote'_cfBreak_run` reconcile the *one-level*
encoded tails (`cfContinue`/`cfBreak`) with the `controlFlow` tags the semantics
consumes. The return fold adds one more tail — the loop break
`cfBreakContinue accs` — whose denotation is the *two-level*
`controlFlow true (controlFlow false v)` that `denoteForLoop'Return` reads as a
loop break. This lemma is the missing reconciliation, lifting the one-level
lemmas to the doubly-nested encoding. -/

/-- The return-fold loop-break tail `cfBreakContinue accE` threads the
    accumulator's value into the *inner* `controlFlow false` of a two-level
    `controlFlow true (controlFlow false ·)` — exactly the value
    `denoteForLoop'Return` classifies as a loop break (and the runtime
    `Hax.forFoldReturn` sees as `Break (Continue ·)`). Companion to
    `denote'_cfContinue_run` (continue) and `denote'_cfBreak_run` (early return),
    completing the per-tail reconciliation for all three return-fold tags. -/
theorem denote'_cfBreakContinue_run (bi : Builtins) (fuel : Nat) (accE : ImpExpr)
    (env env' : Env) (v : Value)
    (h : (denote' bi fuel accE).run env = (.val v, env'))
    (hv : v.isControlFlow = false) :
    (denote' bi fuel (.cfBreakContinue accE)).run env
      = (.val (.controlFlow true (.controlFlow false v)), env') := by
  unfold denote'
  simp only [StateT.run, bind, StateT.bind] at h ⊢
  rw [h]
  cases v <;> simp_all [Value.isControlFlow, StateT.pure, pure]

/-! ## Runtime ↔ reference consumption (return fold)

The plain case's core theorem is `forFold_merge_eq_refFold`: the runtime
`Hax.forFold` consumed by `.merge` equals the reference loop `refFold`. This
section is the **return-fold analog**: the runtime `Hax.forFoldReturn` consumed
by the *nested match* (`consumeForFoldReturn`) equals the three-way classified
reference loop `refFoldReturn`. It is the value-level (runtime) half of the
return-fold bridge, and — unlike the plain case, which collapses to one
`ControlFlow` level — it exercises both levels of the doubly-nested
result, using the `forFoldReturn_loopBreak`/`_earlyReturn`/`_done` unfold
structure. -/

/-- The three exit modes of a return fold, as a reference result type. The
    runtime's `ControlFlow β (ControlFlow γ α)` is consumed into this by
    `consumeForFoldReturn`; the printer emits the matching nested `match`. -/
inductive FoldReturnResult (β γ α : Type) where
  | earlyRet (v : β)   -- function early return (propagated up)
  | broke (v : γ)      -- loop break (loop yields v)
  | done (acc : α)     -- normal completion (final accumulator)

/-- Consume the runtime `Hax.forFoldReturn` result into `FoldReturnResult` —
    the value-level model of the printer's post-fold nested `match`. -/
def consumeForFoldReturn {β γ α : Type} :
    ControlFlow β (ControlFlow γ α) → FoldReturnResult β γ α
  | .Break v => .earlyRet v
  | .Continue (.Break v) => .broke v
  | .Continue (.Continue acc) => .done acc

/-- Reference meaning of a **return** fold loop: iterate over `[lo, hi)`,
    threading the accumulator; the body's per-iteration `ControlFlow (ControlFlow
    β γ) α` step classifies as `Break (Continue v)` = loop break (yield `v`),
    `Break (Break v)` = early return (propagate `v`), or `Continue acc` = keep
    going. This is the imperative `for` loop with both `break` and early
    `return`, returning which exit fired and with what value. -/
def refFoldReturn {α β γ : Type} (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow (ControlFlow β γ) α) : FoldReturnResult β γ α :=
  if lo ≥ hi then .done init
  else
    match f lo init with
    | .Break (.Continue v) => .broke v       -- loop break
    | .Break (.Break v) => .earlyRet v       -- early return
    | .Continue acc => refFoldReturn (lo + 1) hi acc f
termination_by (hi - lo).toNat

/-- Runtime `Hax.forFoldReturn` consumed by the nested match equals the
    reference return-fold `refFoldReturn`: the doubly-nested fold, after the
    consumer, computes exactly the loop's three-way exit classification and
    value. The return analog of `forFold_merge_eq_refFold`. -/
theorem forFoldReturn_consume_eq_refFoldReturn {α β γ : Type} (lo hi : Int)
    (init : α) (f : Int → α → ControlFlow (ControlFlow β γ) α) :
    consumeForFoldReturn (Hax.forFoldReturn lo hi init f)
      = refFoldReturn lo hi init f := by
  fun_induction Hax.forFoldReturn lo hi init f with
  | case1 lo init h =>
    rw [refFoldReturn, if_pos h]; rfl
  | case2 lo init v h hf =>
    rw [refFoldReturn, if_neg (by omega), hf]; rfl
  | case3 lo init v h hf =>
    rw [refFoldReturn, if_neg (by omega), hf]; rfl
  | case4 lo init acc h hf ih =>
    rw [refFoldReturn, if_neg (by omega), hf]; exact ih

/-! ## Environment-threading loop induction (plain)

The final bridge for the plain fold: `denoteForLoop'` (the semantics — it threads
accumulators through the *environment* and discards the continue payload) agrees
with `Hax.forFold` (the runtime — it threads through the *value*), for a body
that satisfies the per-iteration reconciliation `hstep`. `hstep` is exactly the
per-tail behaviour of `denote'_cfContinue_run`/`denote'_cfBreak_run`, lifted to
"run the body at loop index `i` from an env whose accumulator variable `a` holds
`aval`": it yields a `controlFlow` whose tag is the runtime step `g i aval`'s
break/continue and whose payload is that step's value, and it leaves the new
accumulator in `env' a`. The proof is the fuel/range induction; its inductive
step is one application of `hstep` with the environment accumulator and the
runtime accumulator in lockstep (`env' a = some (g i aval).merge`). -/

set_option linter.unusedSimpArgs false in
/-- `denoteForLoop'` over an encoded body equals `Hax.forFold`, env- and
    value-threaded accumulators kept in lockstep. The runtime result's `.merge`
    is always the final environment accumulator; the returned outcome is `.unit`
    on normal completion and the break value on break. -/
theorem denoteForLoop'_eq_forFold
    (bi : Builtins) (var a : String) (body : ImpExpr)
    (g : Int → Value → ControlFlow Value Value)
    (hstep : ∀ (fuel : Nat) (i : Int) (env : Env) (aval : Value), env a = some aval →
        ∃ env', (denote' bi fuel body).run (Env.extend env var (.int i))
              = (.val (.controlFlow (g i aval).isBreak (g i aval).merge), env')
          ∧ env' a = some (g i aval).merge) :
    ∀ (fuel : Nat) (lo hi : Int) (env : Env) (aval : Value),
      env a = some aval → (hi - lo).toNat ≤ fuel →
      ∃ env'',
        (denoteForLoop' bi fuel var lo hi body).run env
          = ((if (Hax.forFold lo hi aval g).isBreak then
                Outcome.val (Hax.forFold lo hi aval g).merge
              else Outcome.val .unit), env'')
        ∧ env'' a = some (Hax.forFold lo hi aval g).merge := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi env aval ha hfuel
    have hge : lo ≥ hi := by omega
    refine ⟨env, ?_, ?_⟩
    · rw [denoteForLoop', if_pos hge, Hax.forFold, if_pos hge]
      simp [ControlFlow.isBreak, ControlFlow.merge, StateT.run, pure, StateT.pure]
    · rw [Hax.forFold, if_pos hge]; simpa [ControlFlow.merge] using ha
  | succ n ih =>
    intro lo hi env aval ha hfuel
    by_cases hge : lo ≥ hi
    · refine ⟨env, ?_, ?_⟩
      · rw [denoteForLoop', if_pos hge, Hax.forFold, if_pos hge]
        simp [ControlFlow.isBreak, ControlFlow.merge, StateT.run, pure, StateT.pure]
      · rw [Hax.forFold, if_pos hge]; simpa [ControlFlow.merge] using ha
    · obtain ⟨env', hrun, ha'⟩ := hstep (n + 1) lo env aval ha
      rw [denoteForLoop', if_neg hge, if_neg (Nat.succ_ne_zero n)]
      simp only [bind, StateT.bind, StateT.run, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, StateT.pure] at hrun ⊢
      rw [hrun]
      cases hg : g lo aval with
      | Break w =>
        rw [hg] at ha'
        rw [Hax.forFold, if_neg hge, hg]
        simp only [ControlFlow.isBreak, ControlFlow.merge, if_true]
        exact ⟨env', rfl, ha'⟩
      | Continue w =>
        rw [hg] at ha'
        obtain ⟨env'', hrec, ha3⟩ := ih (lo + 1) hi env' w ha' (by omega)
        rw [Hax.forFold, if_neg hge, hg]
        simp only [ControlFlow.isBreak, ControlFlow.merge, Nat.add_sub_cancel]
        simp only [bind, StateT.bind, StateT.run, modify, modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, pure, StateT.pure] at hrec
        exact ⟨env'', hrec, ha3⟩

/-! ## Environment-threading loop induction (return fold)

The lift to the return fold. One subtlety the plain case lacks: the
ControlFlow-aware `denote'` *short-circuits* `controlFlow` values, so the
encoded early return `cfBreak (cfBreak v)` collapses, under `denote'`, to the
*one-level* `controlFlow true v` (the inner break is absorbed). This is exactly
the `denoteForLoop'Return` early-return tag, and after consumption it still
corresponds to the runtime's two-level `Break (Break v)` → `earlyRet v`. So the
per-iteration body step is encoded by `encReturnStep` below (one level for early
return, two for loop break), and the loop result is compared after
`consumeForFoldReturn` via `retOutcome`. -/

/-- Value encoding of a return-fold body step, as `denote'` produces it for the
    encoded body: continue → `controlFlow false`, loop break → two-level
    `controlFlow true (controlFlow false)`, early return → one-level
    `controlFlow true` (the `denote'` short-circuit of `cfBreak (cfBreak ·)`). -/
def encReturnStep : ControlFlow (ControlFlow Value Value) Value → Value
  | .Continue acc => .controlFlow false acc
  | .Break (.Continue v) => .controlFlow true (.controlFlow false v)
  | .Break (.Break v) => .controlFlow true v

/-- The denote outcome each consumed return-fold result corresponds to:
    normal completion → `unit` (accumulator is in the env), loop break → the
    break value, early return → the propagated `controlFlow true v`. -/
def retOutcome : FoldReturnResult Value Value Value → Outcome
  | .done _ => .val .unit
  | .broke v => .val v
  | .earlyRet v => .val (.controlFlow true v)

set_option linter.unusedSimpArgs false in
/-- `denoteForLoop'Return` over an encoded body agrees with `Hax.forFoldReturn`
    consumed by the nested match (`consumeForFoldReturn`), mapped to the denote
    outcome by `retOutcome`. The return analog of `denoteForLoop'_eq_forFold`,
    exercising both `ControlFlow` levels. `hER` records that early-return values
    are data (not `controlFlow`), so they classify as an early return rather than
    a loop break. -/
theorem denoteForLoop'Return_eq_forFoldReturn
    (bi : Builtins) (var a : String) (body : ImpExpr)
    (g : Int → Value → ControlFlow (ControlFlow Value Value) Value)
    (hstep : ∀ (fuel : Nat) (i : Int) (env : Env) (aval : Value), env a = some aval →
        ∃ env', (denote' bi fuel body).run (Env.extend env var (.int i))
              = (.val (encReturnStep (g i aval)), env')
          ∧ (∀ acc, g i aval = .Continue acc → env' a = some acc))
    (hER : ∀ (i : Int) (av v : Value), g i av = .Break (.Break v) → v.isControlFlow = false) :
    ∀ (fuel : Nat) (lo hi : Int) (env : Env) (aval : Value),
      env a = some aval → (hi - lo).toNat ≤ fuel →
      ∃ env'',
        (denoteForLoop'Return bi fuel var lo hi body).run env
          = (retOutcome (consumeForFoldReturn (Hax.forFoldReturn lo hi aval g)), env'') := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi env aval ha hfuel
    have hge : lo ≥ hi := by omega
    refine ⟨env, ?_⟩
    rw [denoteForLoop'Return, if_pos hge, Hax.forFoldReturn, if_pos hge]
    simp [consumeForFoldReturn, retOutcome, StateT.run, pure, StateT.pure]
  | succ n ih =>
    intro lo hi env aval ha hfuel
    by_cases hge : lo ≥ hi
    · refine ⟨env, ?_⟩
      rw [denoteForLoop'Return, if_pos hge, Hax.forFoldReturn, if_pos hge]
      simp [consumeForFoldReturn, retOutcome, StateT.run, pure, StateT.pure]
    · obtain ⟨env', hrun, hacc⟩ := hstep (n + 1) lo env aval ha
      rw [denoteForLoop'Return, if_neg hge, if_neg (Nat.succ_ne_zero n)]
      simp only [bind, StateT.bind, StateT.run, modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, StateT.pure] at hrun ⊢
      rw [hrun]
      rw [Hax.forFoldReturn, if_neg hge]
      cases hg : g lo aval with
      | Continue acc =>
        have hacc' : env' a = some acc := hacc acc hg
        obtain ⟨env'', hrec⟩ := ih (lo + 1) hi env' acc hacc' (by omega)
        simp only [hg, encReturnStep, Nat.add_sub_cancel]
        simp only [bind, StateT.bind, StateT.run, modify, modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, pure, StateT.pure] at hrec
        exact ⟨env'', hrec⟩
      | Break br =>
        cases br with
        | Continue v =>
          simp only [hg, encReturnStep, consumeForFoldReturn, retOutcome]
          exact ⟨env', rfl⟩
        | Break v =>
          have hvcf : v.isControlFlow = false := hER lo aval v hg
          simp only [hg, encReturnStep, consumeForFoldReturn, retOutcome]
          refine ⟨env', ?_⟩
          cases v <;> simp_all [Value.isControlFlow, StateT.run, pure, StateT.pure]

end Hax

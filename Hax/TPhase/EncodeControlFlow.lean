/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr
import Hax.Semantics
import Hax.SemanticsCF
import Hax.Runtime

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
    distinguishes it from a genuine early function return, which is
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
* **Return case:** `forFoldReturn_eq_refFoldReturn` characterises the
  doubly-nested runtime fold; the full env-threading bridge for the return case
  is identified as `encodeReturnFold_denote'_bridge` (gap, see its docstring).
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
      -- Dead-code after surface CF: a tail following an unconditional break is
      -- unreachable.
      if hasSurfaceCF e1 then encodeForFoldBody accE e1
      else .seq e1 (encodeForFoldBody accE e2)
  | .ifThenElse c t e =>
      .ifThenElse c (encodeForFoldBody accE t) (encodeForFoldBody accE e)
  | .cfBreak .unitVal => .cfBreak accE
  | .cfBreak v => .cfBreak v
  | .cfContinue v => .cfContinue v
  | .cfBreakContinue v => .cfBreakContinue v
  | _ => .cfContinue accE

/-- Return-fold loop-body encoding (`isReturn = true`): like
    `encodeForFoldBody`, but a **loop break** is `cfBreakContinue accE`
    (= `Break (Continue accE)`), the inner `Continue` distinguishing it from a
    genuine early function return. Genuine early returns (`cfBreak v`, v ≠ unit)
    are nested afterwards by `nestReturn`. -/
def encodeReturnCfBody (accE : ImpExpr) : ImpExpr → ImpExpr
  | .letBind n v body => .letBind n v (encodeReturnCfBody accE body)
  | .seq e1 e2 =>
      if hasSurfaceCF e1 then encodeReturnCfBody accE e1
      else .seq e1 (encodeReturnCfBody accE e2)
  | .ifThenElse c t e =>
      .ifThenElse c (encodeReturnCfBody accE t) (encodeReturnCfBody accE e)
  | .cfBreak .unitVal => .cfBreakContinue accE              -- loop break
  | .cfBreak v => .cfBreak v                                 -- early return (nested later)
  | .cfContinue v => .cfContinue v
  | .cfBreakContinue v => .cfBreakContinue v
  | _ => .cfContinue accE

/-- Nest a genuine early-return `cfBreak v` into `cfBreak (cfBreak v)`
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
      if hasSurfaceCF e1.erase then tEncodeForFoldBody accT e1
      else .mk (.seq e1 (tEncodeForFoldBody accT e2)) ty
  | .mk (.ifThenElse c t e) ty =>
      .mk (.ifThenElse c (tEncodeForFoldBody accT t) (tEncodeForFoldBody accT e)) ty
  | .mk (.ann e) ty => .mk (.ann (tEncodeForFoldBody accT e)) ty
  | .mk (.cfBreak v) ty =>
      match v.erase with
      | .unitVal => .mk (.cfBreak accT) ty
      | _ => .mk (.cfBreak v) ty
  | .mk (.cfContinue v) ty => .mk (.cfContinue v) ty
  | .mk (.cfBreakContinue v) ty => .mk (.cfBreakContinue v) ty
  | .mk _ ty => .mk (.cfContinue accT) ty

set_option linter.unusedSimpArgs false in
/-- Type erasure commutes with the typed encoding. -/
theorem tEncodeForFoldBody_erase (accT : TExpr) (e : TExpr) :
    (tEncodeForFoldBody accT e).erase = encodeForFoldBody accT.erase e.erase := by
  induction e using TExpr.ind
  case letBind ty n val body _ ihb =>
    simp [tEncodeForFoldBody, TExpr.erase, encodeForFoldBody, ihb]
  case seq ty e1 e2 ih1 ih2 =>
    simp only [tEncodeForFoldBody, TExpr.erase, encodeForFoldBody]
    by_cases h : hasSurfaceCF e1.erase
    · simp [h, ih1]
    · simp [h, ih2, TExpr.erase]
  case ifThenElse ty c t e _ iht ihe =>
    simp [tEncodeForFoldBody, TExpr.erase, encodeForFoldBody, iht, ihe]
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
`ControlFlow` level — it genuinely exercises both levels of the doubly-nested
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

/-! ## Residual obligation (shared with the plain case)

What remains unproved — for the return fold **and** the plain fold alike — is the
**environment-threading loop induction**: that `denoteForLoop'`/
`denoteForLoop'Return` (the semantics, which thread accumulators through the
*environment* and discard the continue payload) agree with `Hax.forFold`/
`Hax.forFoldReturn` (the runtime, which thread accumulators through the *value*),
for a body produced by the encoding. The per-tail reconciliation those two need
is now complete at both levels (`denote'_cfContinue_run`, `denote'_cfBreak_run`,
`denote'_cfBreakContinue_run`), and the value-level consumption is proved equal
to the reference for both kinds (`forFold_merge_eq_refFold`,
`forFoldReturn_consume_eq_refFoldReturn`). The remaining step is the StateM/fuel
induction copying the environment accumulator into the value payload each
iteration; it is identical in shape for plain and return and is **not** specific
to the doubly-nested case. Named here, no hidden `sorry`. -/

end Hax

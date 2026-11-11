/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import HaxLean.PrettyPrintT
public import HaxLean.PrettyPrintT
public meta import HaxLean.Range.Heads
public import HaxLean.RuntimeM

/-!
# Loop invariants of the source, from the export to the emitted invariant

A `for` loop of the shape of the hax export of `hax_lib::loop_invariant!(|i| φ)` (the call
`_internal_loop_invariant` on a closure, first statement of the loop body, as in
`hax-contracts-test/hax_frontend_export.json`), followed through each stage:

* the adapter (`HaxAdapter.tLoopInvBody`) turns the call into the statement
  `Range.invStmt φ`;
* the typed pipeline (`tPipelineFull`) keeps the statement at the head of the `forFold` body;
* the range checker accepts the clamp loop with the invariant and refuses it without, with no
  inferred annotation;
* the emitter removes the statement from the rendered body (`stripInvStmts`) and prints the
  invariant as `f_loopInv_0` (`loopInvDefs`), the invariant argument of
  `Hax.foldRangeM_spec` in the proof that the emitted function does not panic.
-/

set_option autoImplicit false

namespace HaxLean.Range.LoopInvariantTest

open Hax

/-- The invariant `0 ≤ acc ∧ acc ≤ 1000`. -/
def φ : ImpExpr :=
  .app "&&" [.app "Le" [.lit (.int 0), .var "acc"], .app "Le" [.var "acc", .lit (.int 1000)]]

/-- The body of the clamp loop after its invariant: `if acc < 1000 { acc += 1 }`. -/
def step : ImpExpr :=
  .seq (.ifThenElse (.app "Lt" [.var "acc", .lit (.int 1000)])
    (.seq (.assign "acc" (.app "Add#32" [.var "acc", .lit (.int 1)])) .unitVal) .unitVal)
    .unitVal

/-- The loop body as the export gives it: the invariant call on the closure `|i| φ`. -/
def exportBody : ImpExpr :=
  .seq (.app "_internal_loop_invariant" [.lam ["i"] φ]) step

/-- The clamp function with the loop body `b`. -/
def clamp (b : ImpExpr) : ImpExpr :=
  .letBind "acc" (.lit (.int 0)) (.seq (.forLoop "i" (.lit (.int 0)) (.var "n") b) (.var "acc"))

-- The adapter's head is the checker's, and the call becomes `Range.invStmt φ`.
#guard HaxAdapter.loopInvariantHead == Range.loopInvHead
#guard (HaxAdapter.tLoopInvBody "i" (TExpr.ofImpExpr exportBody)).erase ==
  .seq (Range.invStmt φ) step

/-- The clamp function after the adapter and the typed pipeline, with or without the
    invariant. -/
def piped (withInv : Bool) : ImpExpr :=
  let b := if withInv then (HaxAdapter.tLoopInvBody "i" (TExpr.ofImpExpr exportBody)).erase
    else step
  (tPipelineFull [] (TExpr.ofImpExpr (clamp b))).erase

-- The pipeline keeps the invariant at the head of the `forFold` body.
#guard match piped true with
  | .letBind _ _ (.seq (.forFold _ _ _ b) _) => Range.bodyInv? b == some φ
  | _ => false

-- With the invariant the checker accepts the loop; without it, and with no inferred
-- annotation, it refuses the checked addition.
#guard (Range.check (Range.stdSpec [] [] true) [] [("n", .num (0, 2 ^ 64 - 1))]
  (piped true)).isSome
#guard (Range.check (Range.stdSpec [] [] true) [] [("n", .num (0, 2 ^ 64 - 1))]
  (piped false)).isNone

-- The rendered body has no invariant statement, and the invariant is `clamp_loopInv_0`.
#guard (loopInvariants (stripInvStmts (piped true))).isEmpty
#guard loopInvDefs "clamp" [("n", .int)] (fun _ => none) [] (loopInvariants (piped true)) ==
  "/-- The loop invariant 0 of `clamp`, from `hax_lib::loop_invariant!`. -/\n" ++
  "def clamp_loopInv_0 :=\n  fun (i : Int) acc => " ++
  "(Hax.band (Hax.le (0 : Int) acc) (Hax.le acc (1000 : Int))) = true\n"

end HaxLean.Range.LoopInvariantTest

/-! The emitted function and invariant, and the proof that the function does not panic with
the invariant as the argument of the loop rule. -/

namespace HaxLean.Range.LoopInvariantOut

open _root_.Std.WP Lean.Order

/-- The emitted clamp function. -/
def clamp (n : Int) :=
  do
    let acc := (0 : Int)
    Hax.foldRangeM (0 : Int) n acc fun _i acc => do
      let acc ← do
        if Hax.lt acc (1000 : Int) then
          let acc ← Hax.addM_w 32 acc (1 : Int)
          pure acc
        else
          pure acc
      pure acc

/-- The loop invariant 0 of `clamp`, from `hax_lib::loop_invariant!`. -/
def clamp_loopInv_0 :=
  fun (_i : Int) acc => (Hax.band (Hax.le (0 : Int) acc) (Hax.le acc (1000 : Int))) = true

/-- The emitted clamp function does not panic: the loop rule with the emitted invariant. -/
theorem clamp_noPanic (n : Int) : ⦃True⦄ clamp n ⦃fun _ => True⦄ := by
  unfold clamp
  set_option experimental.vcgen true in
  vcgen [Hax.foldRangeM_spec 0 n (0 : Int) _ clamp_loopInv_0] <;>
    simp_all [clamp_loopInv_0, Hax.band, Hax.lt, Hax.le, Hax.add] <;> omega

end HaxLean.Range.LoopInvariantOut

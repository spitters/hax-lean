/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.AST
import Hax.Value
import Hax.Features
import Hax.Semantics
import Hax.Phase.DropReferences
import Hax.Phase.LocalMutation
import Hax.Phase.FunctionalizeLoops
import Hax.Phase.CfIntoMonads
import Hax.Pipeline

/-!
# Test Programs

Concrete `ImpExpr` programs inspired by the hax test suite, testing each
compiler phase. Each test verifies:
1. Feature predicates via boolean checkers
2. Phase transformations produce expected output properties
3. Denotational semantics produce expected values

## Test Programs (from hax tests)

| Test | Rust equivalent | Exercises |
|------|----------------|-----------|
| `simpleMut` | `let mut x = 0; x = 5; x` | assign |
| `sumRange` | `for i in 0..n { acc += i; }` | forLoop, assign |
| `earlyRet` | `if x > 0 { return x; } 0` | earlyReturn |
| `borrowDeref` | `let y = &x; *y + 1` | borrow, deref |
| `loopBreak` | `for i in 0..10 { if i > 5 { break; } }` | forLoop, break_ |
| `questionMark` | `let v = x?; Ok(v + 1)` | questionMark |
| `whileLoop` | `while cond { body; }` | whileLoop |
| `combined` | mutation + loop + early return | all features |
-/

namespace Hax.Tests

open Hax

/-! ## Test Programs -/

/-- `let mut x = 0; x = 5; x` → should evaluate to 5 -/
def simpleMut : ImpExpr :=
  .letBind "x" (.lit (.int 0))
    (.seq (.assign "x" (.lit (.int 5)))
      (.var "x"))

/-- `let y = &x; *y + 1` where x = 10 → should evaluate to 11 -/
def borrowDeref : ImpExpr :=
  .letBind "y" (.borrow (.var "x"))
    (.app "add" [.deref (.var "y"), .lit (.int 1)])

/-- `if x > 0 { return x; } 0` -/
def earlyRet : ImpExpr :=
  .seq
    (.ifThenElse
      (.app "gt" [.var "x", .lit (.int 0)])
      (.earlyReturn (.var "x"))
      .unitVal)
    (.lit (.int 0))

/-- `for i in 0..n { acc = acc + i; } acc`
    with acc initialized to 0. -/
def sumRange : ImpExpr :=
  .letBind "acc" (.lit (.int 0))
    (.seq
      (.forLoop "i" (.lit (.int 0)) (.var "n")
        (.assign "acc" (.app "add" [.var "acc", .var "i"])))
      (.var "acc"))

/-- `for i in 0..10 { if i > 5 { break; } } 0` -/
def loopBreak : ImpExpr :=
  .seq
    (.forLoop "i" (.lit (.int 0)) (.lit (.int 10))
      (.ifThenElse (.app "gt" [.var "i", .lit (.int 5)])
        (.break_ none)
        .unitVal))
    (.lit (.int 0))

/-- `let v = x?; Ok(v + 1)` -/
def questionMarkTest : ImpExpr :=
  .letBind "v" (.questionMark (.var "x"))
    (.app "Ok" [.app "add" [.var "v", .lit (.int 1)]])

/-- `while x > 0 { x = x - 1; }` -/
def whileTest : ImpExpr :=
  .whileLoop
    (.app "gt" [.var "x", .lit (.int 0)])
    (.assign "x" (.app "sub" [.var "x", .lit (.int 1)]))

/-- Combined: mutation + loop + early return -/
def combined : ImpExpr :=
  .letBind "result" (.lit (.int 0))
    (.seq
      (.forLoop "i" (.lit (.int 0)) (.var "n")
        (.seq
          (.assign "result" (.app "add" [.var "result", .var "i"]))
          (.ifThenElse (.app "gt" [.var "result", .lit (.int 100)])
            (.earlyReturn (.var "result"))
            .unitVal)))
      (.var "result"))

/-! ## Feature Predicate Tests -/

-- simpleMut has assign (mutation) but no references, loops, or early exit
#eval checkNoReferences simpleMut  -- true
#eval checkNoMutation simpleMut    -- false (has assign)
#eval checkNoLoops simpleMut       -- true
#eval checkNoEarlyExit simpleMut   -- true

-- borrowDeref has borrow/deref but nothing else
#eval checkNoReferences borrowDeref -- false
#eval checkNoMutation borrowDeref   -- true
#eval checkNoLoops borrowDeref      -- true
#eval checkNoEarlyExit borrowDeref  -- true

-- earlyRet has earlyReturn
#eval checkNoReferences earlyRet  -- true
#eval checkNoMutation earlyRet    -- true
#eval checkNoLoops earlyRet       -- true
#eval checkNoEarlyExit earlyRet   -- false

-- sumRange has forLoop and assign
#eval checkNoReferences sumRange  -- true
#eval checkNoMutation sumRange    -- false (has assign)
#eval checkNoLoops sumRange       -- false (has forLoop)
#eval checkNoEarlyExit sumRange   -- true

-- loopBreak has forLoop and break
#eval checkNoReferences loopBreak -- true
#eval checkNoMutation loopBreak   -- true
#eval checkNoLoops loopBreak      -- false
#eval checkNoEarlyExit loopBreak  -- true

-- questionMarkTest has questionMark
#eval checkNoEarlyExit questionMarkTest -- false

-- whileTest has whileLoop and assign
#eval checkNoLoops whileTest      -- false
#eval checkNoMutation whileTest   -- false

-- combined has everything
#eval checkFullyFunctional combined  -- false

/-! ## Pipeline Tests -/

-- After pipeline, all programs should be fully functional
#eval checkFullyFunctional (pipeline simpleMut)         -- true
#eval checkFullyFunctional (pipeline borrowDeref)       -- true
#eval checkFullyFunctional (pipeline earlyRet)          -- true
#eval checkFullyFunctional (pipeline sumRange)          -- true
#eval checkFullyFunctional (pipeline loopBreak)         -- true
#eval checkFullyFunctional (pipeline questionMarkTest)  -- true
#eval checkFullyFunctional (pipeline whileTest)         -- true
#eval checkFullyFunctional (pipeline combined)          -- true

/-! ## Semantics Tests -/

/-- Run a program with given environment bindings and return the outcome. -/
def run (fuel : Nat) (bindings : List (String × Value)) (e : ImpExpr) : Outcome :=
  let env := bindings.foldl (fun acc (n, v) => acc.extend n v) Env.empty
  (denote defaultBuiltins fuel e env).1

-- simpleMut: let mut x = 0; x = 5; x → 5
#eval run 10 [] simpleMut  -- Outcome.val (Value.int 5)

-- borrowDeref: let y = &x; *y + 1 with x = 10 → 11
#eval run 10 [("x", .int 10)] borrowDeref  -- Outcome.val (Value.int 11)

-- earlyRet: if x > 0 { return x; } 0
#eval run 10 [("x", .int 42)] earlyRet  -- Outcome.earlyRet (Value.int 42)
#eval run 10 [("x", .int 0)] earlyRet   -- Outcome.val (Value.int 0)
#eval run 10 [("x", .int (-5))] earlyRet -- Outcome.val (Value.int 0)

-- sumRange: sum 0..5 = 0+1+2+3+4 = 10
#eval run 100 [("n", .int 5)] sumRange  -- Outcome.val (Value.int 10)

-- sumRange: sum 0..0 = 0
#eval run 100 [("n", .int 0)] sumRange  -- Outcome.val (Value.int 0)

-- loopBreak: loop 0..10, break when i > 5
#eval run 100 [] loopBreak  -- Outcome.val (Value.int 0)

-- questionMark with Ok value
#eval run 10 [("x", .result true (.int 5))] questionMarkTest
  -- Outcome.val (Value.result true (Value.int 6))

-- questionMark with Err value → early return
#eval run 10 [("x", .result false (.int 99))] questionMarkTest
  -- Outcome.earlyRet (Value.result false (Value.int 99))

-- whileTest: count down from 3
#eval run 100 [("x", .int 3)] whileTest  -- Outcome.val (Value.unit)

/-! ## Phase-by-Phase Transformation Tests -/

-- Phase 1: dropReferences removes borrow/deref
#eval checkNoReferences (dropReferences borrowDeref)  -- true
-- Original semantics preserved
#eval run 10 [("x", .int 10)] (dropReferences borrowDeref)
  -- Outcome.val (Value.int 11) — same as original

-- Phase 2: localMutation removes assign
#eval checkNoMutation (localMutation [] simpleMut)  -- true

-- Phase 3: functionalizeLoops removes loops
#eval checkNoLoops (functionalizeLoops sumRange)  -- true
#eval checkNoLoops (functionalizeLoops loopBreak)  -- true
-- Phase 3 uses nested encoding for loops with earlyReturn
#eval checkNoLoops (functionalizeLoops combined)  -- true
#eval checkFullyFunctional (pipeline combined)    -- true

-- Phase 4: cfIntoMonads removes early exit
#eval checkNoEarlyExit (cfIntoMonads earlyRet)  -- true
#eval checkNoEarlyExit (cfIntoMonads questionMarkTest)  -- true

/-! ## Pipeline Semantics Preservation Tests

For programs without loops or early exits, the pipeline preserves
denotational semantics exactly. -/

-- simpleMut through pipeline: mutation is the only feature,
-- localMutation preserves semantics
#eval run 10 [] (pipeline simpleMut)
  -- Should give val (int 5), same as original

-- borrowDeref through pipeline: dropReferences preserves semantics
#eval run 10 [("x", .int 10)] (pipeline borrowDeref)
  -- Should give val (int 11), same as original

/-! ## Theorem-Level Tests

Verify key properties as theorems (checked by Lean's kernel). -/

example : NoReferences (dropReferences borrowDeref) :=
  dropReferences_noRefs borrowDeref

example : NoMutation (localMutation [] simpleMut) :=
  localMutation_noMut [] simpleMut

example : NoLoops (functionalizeLoops sumRange) :=
  functionalizeLoops_noLoops sumRange

example : NoEarlyExit (cfIntoMonads earlyRet) :=
  cfIntoMonads_noEarlyExit earlyRet

example : FullyFunctional (pipeline simpleMut) :=
  pipeline_fullyFunctional simpleMut

example : FullyFunctional (pipeline combined) :=
  pipeline_fullyFunctional combined

/-- End-to-end: pipeline preserves semantics for loop-free,
    early-exit-free programs. -/
example (fuel : Nat) : denote defaultBuiltins fuel (pipeline simpleMut) =
    denote defaultBuiltins fuel simpleMut := by
  apply pipeline_correct
  · -- NoLoops after phases 1-2
    simp [mutatedVars]
    exact .letBind .lit (.seq (.seq (.letBind .lit .var) .unitVal) .var)
  · -- NoEarlyExit after phases 1-2
    simp [mutatedVars]
    exact .letBind .lit (.seq (.seq (.letBind .lit .var) .unitVal) .var)

end Hax.Tests

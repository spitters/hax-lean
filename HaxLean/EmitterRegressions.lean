/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import HaxLean.PrettyPrint
public import HaxLean.PrettyPrint

/-!
# Emitter regressions: loop-carried variables

Each check pins an accumulator-analysis verdict on a body shape that once
rendered with a `Unit` accumulator, discarding the loop's state.
-/

@[expose] public section

namespace Hax.EmitterRegressions

/-- A rotation: no right-hand side names its own target, yet `h` and `g` are
    loop-carried because an earlier statement read them. `t` is written before
    it is read and is local. -/
def rotation : ImpExpr :=
  .seq (.letBind "t" (.var "h") (.var "t"))
    (.seq (.letBind "h" (.var "g") (.var "h"))
      (.letBind "g" (.var "f") (.var "g")))

#guard extractAccumulators rotation == ["h", "g"]

/-- A conditional subtract under a `while true`: the guard reads `r`, the branch
    rebinds it through a temporary and continues. -/
def condSubtract : ImpExpr :=
  .ifThenElse (.app "Ge" [(.app "cmp256" [(.var "r"), (.var "P")]), (.lit (ImpLit.int 0))])
    (.letBind "_tup" (.app "sub256" [(.var "r"), (.var "P")])
      (.letBind "s" (.proj (.var "_tup") 0)
        (.letBind "_" (.proj (.var "_tup") 1)
          (.seq (.seq (.letBind "r" (.var "s") (.var "r")) .unitVal) .unitVal))))
    (.seq (.cfBreak .unitVal) .unitVal)

#guard extractWhileAccumulators condSubtract == ["r"]

/-- A Rust block in statement position arrives as `let _ := <block>; ()`; a
    rebind of an outer name inside the block is loop-carried. -/
def statementBlock : ImpExpr :=
  .letBind "_" (.letBind "coeffs" (.app "from_elem" [(.lit (.int 0)), (.var "n")])
      (.seq (.seq (.letBind "result"
          (.app "array_update" [(.var "result"), (.var "col"), (.var "coeffs")])
          (.var "result")) .unitVal) .unitVal))
    .unitVal

#guard extractAccumulators statementBlock == ["result"]

/-- A name written before it is ever read is local, not loop-carried. -/
def freshLocal : ImpExpr :=
  .seq (.letBind "tmp" (.var "x") (.var "tmp"))
    (.letBind "y" (.app "f" [(.var "tmp")]) (.app "g" [(.var "y")]))

#guard !(extractAccumulators freshLocal).contains "tmp"

/-- A carry chain: `carry` is read by the first statement and rebound by the
    second, from the loop index. Its pre-loop value is live, and the rebind
    names the index, so no initializer is hoisted before the loop. -/
def carryShift : ImpExpr :=
  .seq (.letBind "result"
      (.app "array_update" [(.var "result"), (.var "i"),
        (.app "bitor" [(.app "shl" [(.app "index" [(.var "a"), (.var "i")]), (.lit (.int 1))]),
          (.var "carry")])])
      (.var "result"))
    (.letBind "carry"
      (.app "shr" [(.app "index" [(.var "a"), (.var "i")]), (.lit (.int 7))])
      (.var "carry"))

#guard extractAccumulators carryShift == ["result", "carry"]
#guard accInitOverrides ["result", "carry"] carryShift ["i"] == []

/-- A fresh assignment that names only the loop index is not hoisted either. -/
def indexInit : ImpExpr :=
  .seq (.letBind "x" (.app "index" [(.var "a"), (.var "i")]) (.var "x"))
    (.letBind "y" (.app "f" [(.var "x"), (.var "y")]) (.var "y"))

#guard accInitOverrides ["x", "y"] indexInit ["i"] == []

/-- A `forFoldReturn` body with a `continue` and a function return, and no
    loop-level `break`. -/
def returnOnly : ImpExpr :=
  .ifThenElse (.var "c") (.cfBreak (.cfBreak (.var "r")))
    (.cfContinue (.tuple [(.var "a"), (.var "b")]))

#guard !hasCfBreakContinue returnOnly
#guard hasCfBreakContinue (.seq returnOnly (.cfBreakContinue .unitVal))

-- hax's loop-state placeholder `0` under a struct type renders as `default`.
#guard toLean (.typeAscription (.lit (.int 0)) "Array (Int) × Int") == "(default : Array (Int) × Int)"
#guard !(toLean (.typeAscription (.lit (.int 0)) "Int")).startsWith "(default"

end Hax.EmitterRegressions

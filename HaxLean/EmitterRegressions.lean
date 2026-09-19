/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import HaxLean.PrettyPrint
public import HaxLean.PrettyPrint
public meta import HaxLean.PrettyPrintT
public import HaxLean.PrettyPrintT

/-!
# Emitter regressions

Pins on the emitter's analyses and rendering: the accumulators the analysis
reports for loop body shapes whose state must be carried, and the projection
paths of tuple destructuring chains, which follow the tuple's arity.
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

/-- The adapter's lowering of `let (a, _, c) = f(); ...` followed by a read of
    `c`: a destructuring chain over a three-component tuple, in statement
    position. -/
def tripleDestr : ImpExpr :=
  .seq
    (.letBind "_tup" (.app "f" [])
      (.letBind "a" (.proj (.var "_tup") 0)
        (.letBind "_" (.proj (.var "_tup") 1)
          (.letBind "c" (.proj (.var "_tup") 2) .unitVal))))
    (.var "c")

/-- The same chain over a pair. -/
def pairDestr : ImpExpr :=
  .seq
    (.letBind "_tup" (.app "f" [])
      (.letBind "a" (.proj (.var "_tup") 0)
        (.letBind "_" (.proj (.var "_tup") 1) .unitVal)))
    (.var "a")

-- Components of a right-nested triple are `.1`, `.2.1` and `.2.2`.
#guard toLean tripleDestr 1 ==
  "  let _tup := f\n  let a := _tup.1\n  let _ := _tup.2.1\n  let c := _tup.2.2\n  c"
#guard toLean pairDestr 1 == "  let _tup := f\n  let a := _tup.1\n  let _ := _tup.2\n  a"
-- A chain in tail position renders as a tuple pattern.
#guard toLean (.letBind "_tup" (.app "f" [])
    (.letBind "a" (.proj (.var "_tup") 0) (.letBind "b" (.proj (.var "_tup") 1)
      (.letBind "c" (.proj (.var "_tup") 2) (.var "c"))))) 1 ==
  "  let (a, b, c) := f\n  c"
-- A projection with no destructuring chain: component `0` renders, a later
-- component is refused. This is the untyped fallback, unchanged by the
-- typed `.proj` marker below: it only fires when the receiver's tuple
-- arity cannot be recovered from a `TExpr.ty` annotation.
#guard toLean (.proj (.var "t") 0) == "t.1"
#guard toLean (.proj (.var "t") 1) == "(hax_unsupported_tuple_projection t 1)"

/-! ## Typed tuple projection outside a destructuring chain

`markNamedProj` (`PrettyPrintT.lean`) rewrites a `TExpr.proj e i` node whose
receiver `e` carries a known tuple type into the same `::proj::<path>`
marker `markProjChainWith` emits for a destructuring chain, so a component
past `0` renders via the recovered arity instead of the untyped fallback's
refusal above. -/

/-- A pair-typed variable, projected at component `1` with no destructuring
    chain (e.g. `let s := t.1` after a call whose hax type is a 2-tuple, as
    in `let (was_square, s) = sqrt_ratio_m1(..)` when only `s` is used
    further down). -/
def pairProjTyped : TExpr :=
  .mk (.proj (.mk (.var "t") (.tuple [.unknown, .unknown])) 1) .unknown

#guard toLean (markNamedProj pairProjTyped).erase == "t.2"

/-- A triple-typed variable, projected at components `1` and `2`. -/
def tripleProjTyped1 : TExpr :=
  .mk (.proj (.mk (.var "t") (.tuple [.unknown, .unknown, .unknown])) 1) .unknown

def tripleProjTyped2 : TExpr :=
  .mk (.proj (.mk (.var "t") (.tuple [.unknown, .unknown, .unknown])) 2) .unknown

#guard toLean (markNamedProj tripleProjTyped1).erase == "t.2.1"
#guard toLean (markNamedProj tripleProjTyped2).erase == "t.2.2"

/-- A nested projection: component `1` of a pair that is itself component
    `1` of a triple, i.e. `(t.2.1).2` — `markNamedProj` recurses into the
    receiver before checking its type, so the inner and outer projections
    are each rewritten from the tuple type at their own site. -/
def nestedProjTyped : TExpr :=
  let inner := .mk (.proj (.mk (.var "t") (.tuple [.unknown, .tuple [.unknown, .unknown], .unknown])) 1)
    (.tuple [.unknown, .unknown])
  .mk (.proj inner 1) .unknown

#guard toLean (markNamedProj nestedProjTyped).erase == "(t.2.1).2"

end Hax.EmitterRegressions

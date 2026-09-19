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
public meta import HaxLean.ThreadMutations
public import HaxLean.ThreadMutations

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

/-! ## `tDestructure`'s tail projection, marker-based

`tDestructure` (`HaxLean/ThreadMutations.lean`) rebinds the variables of a
branch-mutation join from the right-nested tuple `_mtup`. Its recursion
threads the tail (`_mtup.2`, `(_mtup.2).2`, …) into the next call as a
`::proj::.2` marker rather than a bare `TExpr.proj _ 1`: a bare `.proj e i`
node is read by the untyped `.proj` fallback as a flat index into an
n-ary tuple, valid only at `i = 0`, whereas the marker states directly
"the second component of this pair" — the meaning index `1` always has in
the right-nested encoding, at any depth. -/

/-- Two mutated variables: `_mtup = (h, block)`, `h` at the head (renders via
    the untyped `.proj` fallback's `i = 0` case) and `block` at the tail
    (renders via the `::proj::.2` marker). -/
def destr2 : TExpr :=
  tDestructure ["h", "block"] (.mk (.var "_mtup") .unknown) (.mk (.var "cont") .unknown)

#guard toLean (markNamedProj destr2).erase 1 == "  let h := _mtup.1\n  let block := _mtup.2\n  cont"

/-- Three mutated variables: the second and third both go through the
    marker, one recursion level apart, so `c`'s marker wraps `b`'s. -/
def destr3 : TExpr :=
  tDestructure ["a", "b", "c"] (.mk (.var "_mtup") .unknown) (.mk (.var "cont") .unknown)

#guard toLean (markNamedProj destr3).erase 1 ==
  "  let a := _mtup.1\n  let b := (_mtup.2).1\n  let c := (_mtup.2).2\n  cont"

/-! ## `tDestructure` behind its own `_mtup` binding

`destr2`/`destr3` above destructure a free `_mtup`; the branch-mutation
rewrite (`ThreadMutations.tThreadMut`) always destructures a `_mtup` it
just bound to the joined branches' value (`ThreadMutations.lean`, the
`.letBind "_mtup" ifE (tDestructure m …)` construction). That extra
binding is what `extractTupleDestr` (`PrettyPrint.lean`) inspects to
decide whether the whole chain collapses to a tuple pattern
`let (a, b) := ifE`: at two components the chain's tail binds directly to
a `::proj::.2`-marked `_mtup`, which `extractTupleDestr` still recognises
component-by-component, so it collapses. At three or more components the
middle components project a marker that is itself wrapped in another
marker, which `extractTupleDestr` does not follow; it refuses the
collapse and each binding renders on its own line through the markers
`destr3` already pins, with `_mtup` itself bound to `ifE`. -/

/-- Two components behind a `_mtup` binding collapse to a tuple pattern. -/
def destr2Wrapped : TExpr :=
  .mk (.letBind "_mtup" (.mk (.var "ifE") .unknown)
    (tDestructure ["h", "block"] (.mk (.var "_mtup") .unknown) (.mk (.var "cont") .unknown)))
    .unknown

#guard toLean (markNamedProj destr2Wrapped).erase 1 ==
  "  let (h, block) := ifE\n  cont"

/-- Three components behind a `_mtup` binding do not collapse: `_mtup` is
    bound to `ifE` and each component projects it, rather than the first
    component aliasing to the whole of `ifE`. -/
def destr3Wrapped : TExpr :=
  .mk (.letBind "_mtup" (.mk (.var "ifE") .unknown)
    (tDestructure ["a", "b", "c"] (.mk (.var "_mtup") .unknown) (.mk (.var "cont") .unknown)))
    .unknown

#guard toLean (markNamedProj destr3Wrapped).erase 1 ==
  "  let _mtup := ifE\n  let a := _mtup.1\n  let b := (_mtup.2).1\n  let c := (_mtup.2).2\n  cont"

/-! ## Erased newtype constructor calls

`struct Scalar(pub(crate) [u8; 32])` is an erased newtype: `buildNewtypeMap`
(`HaxAdapter.lean`) records it as `("Scalar", <inner type>)`, and the printer
turns that into `abbrev Scalar_T := Array (Int)` plus the definitional unwrap
`«Scalar.0» x := x`. A constructor call `Scalar(bytes)` in a source body
(`from_bytes_secret(bytes) -> Self { Scalar(bytes) }`) is the identity on
`bytes`; without a definition for `Scalar` its call head reads as an unknown
function, and lands in the generated `Deps` class. -/

def scalarCtorFn : TExpr :=
  .mk (.lam ["bytes"] (.mk (.app "Scalar" [.mk (.var "bytes") .unknown]) .unknown)) .unknown

def scalarNewtypes : HaxAdapter.NewtypeMap := [("Scalar", .array (.uint .w8) 32)]

-- The `Deps` class generated for a module whose only call is an erased
-- newtype constructor has no fields: the constructor is excluded from the
-- dependency computation (`newtypeCtorNames` in `generatePreambleTyped`).
#guard (generatePreambleTyped [("from_bytes_secret", scalarCtorFn)] "Test" []
    [] [] [] (newtypes := scalarNewtypes)).1 ==
  "\n/-- External dependencies for Test extraction (auto-generated). -/\nclass TestDeps where\n\n"

-- The newtype preamble emits the identity constructor `Scalar` alongside the
-- unwrap `«Scalar.0»`: applying one to the other is the printed round trip
-- `«Scalar.0» (Scalar x) = x`, both definitionally `x`. The call site
-- `Scalar bytes` in `from_bytes_secret`'s body is unaffected — it is not
-- rewritten, just resolved by the new `Scalar` definition.
#guard toLeanCertifiedFileTyped [("from_bytes_secret", scalarCtorFn)] "Test" [] [] []
    (newtypes := scalarNewtypes) ==
  "/-\n  Auto-generated by haxpipeT --emit-certified (typed extraction pipeline)\n  Surface code + ImpExpr literals for agreement proofs.\n-/\nimport HaxLean.Runtime\nimport HaxLean.AST\nimport HaxLean.Semantics\n\nset_option linter.unusedVariables false\nset_option maxRecDepth 2048\nset_option maxHeartbeats 6400000\n\nnamespace Test\n\nopen Hax\n\n-- All emitted functions are `noncomputable`: extracted bodies may\n-- depend on Runtime axioms (sha256, bridgeCast, ...) which the Lean\n-- code generator rejects. Verification doesn't require execution.\nnoncomputable section\n\n/-- Newtype tuple-struct aliases: transparent type equalities\n    with definitional `.0` unwraps and definitional constructors. Inner\n    types may themselves be axiomatized (see the axiom block above). -/\nabbrev Scalar := Array (Int)\nnoncomputable def «Scalar.0» (x : Scalar) : Array (Int) := x\nnoncomputable def Scalar (x : Array (Int)) : Scalar := x\n\n\n/-- External dependencies for Test extraction (auto-generated). -/\nclass TestDeps where\n\n\nmutual\n\ndef from_bytes_secret :=\n(fun bytes => Scalar bytes)\n\ndef from_bytes_secret_impExpr : ImpExpr :=\n  (.lam [\"bytes\"] (.app \"Scalar\" [(.var \"bytes\")]))\n\nend\n\nend  -- noncomputable section\n\nend Test\n"

end Hax.EmitterRegressions

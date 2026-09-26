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

/-- A triple-typed variable, projected at component `1`. -/
def tripleProjTyped1 : TExpr :=
  .mk (.proj (.mk (.var "t") (.tuple [.unknown, .unknown, .unknown])) 1) .unknown

/-- A triple-typed variable, projected at component `2`. -/
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
turns that into the transparent alias `abbrev Scalar := Array (Int)` plus the
definitional unwrap `«Scalar.0» x := x` and the definitional constructor
`«Scalar.mk» x := x`. A constructor call `Scalar(bytes)` in a source body
(`from_bytes_secret(bytes) -> Self { Scalar(bytes) }`) is the identity on
`bytes`; without a definition its call head reads as an unknown function, and
lands in the generated `Deps` class. The constructor is named `«Scalar.mk»`
rather than `Scalar`, which the alias holds. -/

/-- `fn from_bytes_secret(bytes) -> Self { Scalar(bytes) }`, with the source
    constructor name at the call head. -/
def scalarCtorFn : TExpr :=
  .mk (.lam ["bytes"] (.mk (.app "Scalar" [.mk (.var "bytes") .unknown]) .unknown)) .unknown

/-- The newtype map of a crate whose one erased newtype is `Scalar([u8; 32])`. -/
def scalarNewtypes : HaxAdapter.NewtypeMap := [("Scalar", .array (.uint .w8) 32)]

-- The `Deps` class generated for a module whose only call is an erased
-- newtype constructor has no fields: the constructor is excluded from the
-- dependency computation (`newtypeCtorNames` in `generatePreambleTyped`).
#guard (generatePreambleTyped [("from_bytes_secret", scalarCtorFn)] "Test" []
    [] [] [] (newtypes := scalarNewtypes)).1 ==
  "\n/-- External dependencies for Test extraction (auto-generated). -/\nclass TestDeps where\n\n"

-- The newtype preamble emits three declarations under three distinct names:
-- the alias `Scalar`, the unwrap `«Scalar.0»` and the identity constructor
-- `«Scalar.mk»`. The call site in `from_bytes_secret`'s body carries the
-- constructor name, in the surface rendering and in both literals.
#guard toLeanCertifiedFileTyped [("from_bytes_secret", scalarCtorFn)] "Test" [] [] []
    (newtypes := scalarNewtypes) ==
  "/-\n  Auto-generated by haxpipeT --emit-certified (typed extraction pipeline)\n  Surface code + ImpExpr and TExpr literals for agreement proofs.\n-/\nimport HaxLean.Runtime\nimport HaxLean.AST\nimport HaxLean.TExpr\nimport HaxLean.Semantics\n\n"
  ++ moduleDocstring "Test" "" false 1 []
  ++ "\nset_option linter.unusedVariables false\nset_option maxRecDepth 2048\n\nnamespace Test\n\nopen Hax\n\n-- All emitted functions are `noncomputable`: extracted bodies may\n-- depend on Runtime axioms (sha256, bridgeCast, ...) which the Lean\n-- code generator rejects. Verification doesn't require execution.\nnoncomputable section\n\n/-- Newtype tuple-struct aliases: transparent type equalities\n    with definitional `.0` unwraps and definitional constructors. Inner\n    types may themselves be axiomatized (see the axiom block above). -/\nabbrev Scalar := Array (Int)\nnoncomputable def «Scalar.0» (x : Scalar) : Array (Int) := x\nnoncomputable def «Scalar.mk» (x : Array (Int)) : Scalar := x\n\n\n/-- External dependencies for Test extraction (auto-generated). -/\nclass TestDeps where\n\n\n/-- Type annotations shared by the `TExpr` literals. -/\nabbrev ty_0 : ImpType := .unknown\n\nmutual\n\ndef from_bytes_secret :=\n(fun bytes => «Scalar.mk» bytes)\n\ndef from_bytes_secret_impExpr : ImpExpr :=\n  (.lam [\"bytes\"] (.app \"Scalar.mk\" [(.var \"bytes\")]))\n\ndef from_bytes_secret_texpr : TExpr :=\n  (.mk (.lam [\"bytes\"] (.mk (.app \"Scalar.mk\" [(.mk (.var \"bytes\") ty_0)]) ty_0)) ty_0)\n\nend\n\nexample : from_bytes_secret_texpr.erase = from_bytes_secret_impExpr := rfl\n\nend  -- noncomputable section\n\nend Test\n"

/-! ## Operator methods on a type parameter

A generic type parameter is parsed as `.slice .int` (`Array (Int)` at the
surface). A trait method with an operator name called on it — `Mul::mul` of
`primeir_hax::Field` — is an external function, so it renders bare and enters
the `Deps` class; the same head on an integer or `Bool` operand is the runtime
builtin. The `ImpExpr` literal carries the untagged head in both cases. -/

/-- The adapter's type of an erased type parameter. -/
def typeParamTy : ImpType := .slice .int

/-- `a * b` on a type parameter. -/
def mulOnTypeParam : TExpr :=
  .mk (.app "mul" [.mk (.var "a") typeParamTy, .mk (.var "b") typeParamTy]) typeParamTy

/-- `a * b` on `u64`. -/
def mulOnU64 : TExpr :=
  .mk (.app "mul" [.mk (.var "a") (.uint .w64), .mk (.var "b") (.uint .w64)]) (.uint .w64)

/-- `a == b` on `bool`. -/
def eqOnBool : TExpr :=
  .mk (.app "eq" [.mk (.var "a") .bool, .mk (.var "b") .bool]) .bool

#guard toLean (markDepOperators mulOnTypeParam).erase == "mul a b"
#guard toLean (markDepOperators mulOnU64).erase == "Hax.mul a b"
#guard toLean (markDepOperators eqOnBool).erase == "Hax.beq a b"
#guard toLeanImpExpr (unmarkDepOperators (markDepOperators mulOnTypeParam).erase) ==
  "(.app \"mul\" [(.var \"a\"), (.var \"b\")])"

/-- `fn f(a: F, b: F) -> F { a * b }`, in the adapter's parameter encoding. -/
def mulFnTypeParam : TExpr :=
  .mk (.letBind "a" (.mk (.var "a") typeParamTy)
    (.mk (.letBind "b" (.mk (.var "b") typeParamTy) mulOnTypeParam) typeParamTy)) typeParamTy

/-- `fn f(a: u64, b: u64) -> u64 { a * b }`. -/
def mulFnU64 : TExpr :=
  .mk (.letBind "a" (.mk (.var "a") (.uint .w64))
    (.mk (.letBind "b" (.mk (.var "b") (.uint .w64)) mulOnU64) (.uint .w64))) (.uint .w64)

-- The type-parameter `mul` is a `Deps` field with the surface types of its
-- call site; the `u64` `mul` is a runtime builtin and the class is empty.
#guard (generatePreambleTyped [("f", markDepOperators mulFnTypeParam)] "Test" [] [] [] []).1 ==
  "\n/-- External dependencies for Test extraction (auto-generated from typed TExpr). -/\nclass TestDeps where\n  mul (a : Array (Int)) (b : Array (Int)) : Array (Int)\n\nexport TestDeps (mul)\n\nvariable [TestDeps]\n\n"
#guard (generatePreambleTyped [("f", markDepOperators mulFnU64)] "Test" [] [] [] []).1 ==
  "\n/-- External dependencies for Test extraction (auto-generated). -/\nclass TestDeps where\n\n"

-- The rendered definition and its literal, from the file printer.
#guard ((toLeanCertifiedFileTyped [("f", mulFnTypeParam)] "Test" [] [] []).splitOn
  "def f (a : Array (Int)) (b : Array (Int)) : Array (Int) :=\nmul a b\n\ndef f_impExpr : ImpExpr :=\n  (.letBind \"a\" (.var \"a\") (.letBind \"b\" (.var \"b\") (.app \"mul\" [(.var \"a\"), (.var \"b\")])))\n").length == 2
#guard ((toLeanCertifiedFileTyped [("f", mulFnU64)] "Test" [] [] []).splitOn
  "def f (a : Int) (b : Int) :=\nHax.mul a b\n").length == 2

/-! ## Dependency-crate names the export also defines

A `DefId` is named by the last segment of its path, so a function of a
dependency crate and a function of the exported crate can claim one name.
`Hax.HaxAdapter.extractDefIdName` qualifies the dependency one with its parent
module, which keeps it out of the emitted definitions and so routes it to the
`Deps` class. These pins fix the rule on both sides: the qualification applies
to a dependency name the export defines, and to nothing else. -/

open Lean in
/-- A `DefId` path segment `{data: {<ns>: <name>}}`. -/
def defIdSeg (ns nm : String) : Json :=
  Json.mkObj [("data", Json.mkObj [(ns, Json.str nm)])]

open Lean in
/-- A `DefId` in `krate` with the given path segments. -/
def mkDefIdJson (krate : String) (segs : List Json) : Json :=
  Json.mkObj [("krate", Json.str krate), ("path", Json.arr segs.toArray)]

open Lean in
/-- A top-level `Fn` item of `krate`, in module `mod`, named `nm`. -/
def fnItemJson (krate mod nm : String) : Json :=
  Json.mkObj
    [("kind", Json.mkObj [("Fn", Json.mkObj [])]),
     ("def_id", mkDefIdJson krate [defIdSeg "TypeNs" mod, defIdSeg "ValueNs" nm])]

open Lean in
/-- An export of `ristretto255_hax` defining `scalar::scalar_add` and
    `group::point_add`. -/
def shadowExport : Json :=
  Json.arr #[fnItemJson "ristretto255_hax" "scalar" "scalar_add",
             fnItemJson "ristretto255_hax" "group" "point_add"]

#guard (Hax.HaxAdapter.localCrateOfExport shadowExport).krates == ["ristretto255_hax"]
#guard (Hax.HaxAdapter.localCrateOfExport shadowExport).fnNames.contains "scalar_add"
#guard Hax.HaxAdapter.shadowsLocalFn
  (Hax.HaxAdapter.localCrateOfExport shadowExport) "libcrux_specs_hax" "scalar_add"
#guard !Hax.HaxAdapter.shadowsLocalFn
  (Hax.HaxAdapter.localCrateOfExport shadowExport) "libcrux_specs_hax" "scalar_mul_mod_l"
#guard !Hax.HaxAdapter.shadowsLocalFn
  (Hax.HaxAdapter.localCrateOfExport shadowExport) "ristretto255_hax" "scalar_add"
#guard !Hax.HaxAdapter.shadowsLocalFn
  (Hax.HaxAdapter.localCrateOfExport shadowExport) "core" "scalar_add"

/-- `libcrux_specs_hax::edwards25519::scalar_add`, which `shadowExport` shadows. -/
def depScalarAdd : Lean.Json :=
  mkDefIdJson "libcrux_specs_hax"
    [defIdSeg "TypeNs" "edwards25519", defIdSeg "ValueNs" "scalar_add"]

/-- `libcrux_specs_hax::edwards25519::scalar_mul_mod_l`, which it does not. -/
def depScalarMul : Lean.Json :=
  mkDefIdJson "libcrux_specs_hax"
    [defIdSeg "TypeNs" "edwards25519", defIdSeg "ValueNs" "scalar_mul_mod_l"]

/-- `core::slice::len`, a runtime builtin whose bare name is the table key. -/
def coreSliceLen : Lean.Json :=
  mkDefIdJson "core" [defIdSeg "TypeNs" "slice", defIdSeg "ValueNs" "len"]

/-- The exporting crate's own `scalar::scalar_add`. -/
def localScalarAdd : Lean.Json :=
  mkDefIdJson "ristretto255_hax"
    [defIdSeg "TypeNs" "scalar", defIdSeg "ValueNs" "scalar_add"]

/-- An exporting crate that also defines `len`. -/
def shadowCrate : Hax.HaxAdapter.LocalCrate :=
  { krates := ["ristretto255_hax"], fnNames := ["scalar_add", "point_add", "len"] }

#guard Hax.HaxAdapter.extractDefIdName depScalarAdd [] shadowCrate == "edwards25519_scalar_add"
#guard Hax.HaxAdapter.extractDefIdName depScalarMul [] shadowCrate == "scalar_mul_mod_l"
#guard Hax.HaxAdapter.extractDefIdName localScalarAdd [] shadowCrate == "scalar_add"
#guard Hax.HaxAdapter.extractDefIdName coreSliceLen [] shadowCrate == "len"
#guard Hax.HaxAdapter.extractDefIdName depScalarAdd == "scalar_add"

/-! ## A trait `impl` resolved against a `Deps` field of one type

A trait `impl` the crate defines is emitted at the concrete self type, and its
method bodies reach the wrapped type through trait methods and associated
constants of a further `impl`, which stays opaque. Where the crate is also
generic over the trait, its generic functions use those same names at a type
parameter. The `Deps` class carries one field, hence one type, per name, so the
two readings have to print alike: they do when the wrapped type is transparent
at the surface, and they do not when it is a type the export does not define
and the emitter declares as an axiom.

`Hax.traitImplDepTypeConflicts` separates the two, over both the methods and
the associated constants. A non-empty answer is
`HaxAdapter.parseHaxFileWithTExpr`'s `resolveTraitImpls := false`, under which
the `impl` contributes no definition and all of its methods reach `Deps`. -/

/-- The wrapped type, an ADT the export does not define. -/
def wrappedTy : ImpType := .adt "Fe51" []

/-- `fn inv(self: W) -> W { W(self.0.inv()) }`, as the trait-`impl` resolution
    emits it: `inv` of the wrapped type, at that type. -/
def implInvDef : TExpr :=
  .mk (.letBind "self" (.mk (.var "self") wrappedTy)
    (.mk (.app "inv" [.mk (.var "self") wrappedTy]) wrappedTy)) wrappedTy

/-- `fn inv0<F: Field>(x: F) -> F { x.inv() }`: the same name at a type
    parameter. -/
def genericInvDef : TExpr :=
  .mk (.letBind "x" (.mk (.var "x") typeParamTy)
    (.mk (.app "inv" [.mk (.var "x") typeParamTy]) typeParamTy)) typeParamTy

/-- The two of them, as the adapter hands them to the preamble. -/
def wrapperDefs : List (String × TExpr) :=
  [("Field_inv", implInvDef), ("inv0", genericInvDef)]

/-- The struct lookup of an export that defines no struct of that name: the
    wrapped type is an axiom and prints as its own name. -/
def opaqueInner : String → Option String := fun _ => none

/-- The struct lookup of an export whose wrapped type is a newtype over a limb
    array, which prints as the type parameter does. -/
def transparentInner : String → Option String :=
  fun n => if n == "Fe51" then some "Array Int" else none

#guard traitImplDepTypeConflicts wrapperDefs ["Field_inv"] opaqueInner == ["inv"]
#guard traitImplDepTypeConflicts wrapperDefs ["Field_inv"] transparentInner == []
-- Read with the `impl` opaque, the method body is not a definition and the one
-- remaining site fixes the field's type.
#guard traitImplDepTypeConflicts [("inv0", genericInvDef)] [] opaqueInner == []
-- A name the export defines is not a field of `Deps`.
#guard traitImplDepTypeConflicts (("inv", genericInvDef) :: wrapperDefs)
  ["Field_inv"] opaqueInner == []

/-- The `impl`'s associated constant, read at the concrete self type. -/
def implConstDef : TExpr :=
  .mk (.letBind "self" (.mk (.var "self") wrappedTy)
    (.mk (.var "Z") wrappedTy)) wrappedTy

/-- The same constant at a type parameter. -/
def genericConstDef : TExpr :=
  .mk (.letBind "x" (.mk (.var "x") typeParamTy)
    (.mk (.var "Z") typeParamTy)) typeParamTy

#guard traitImplDepTypeConflicts
  [("SqrtRatio_z", implConstDef), ("map_to_curve", genericConstDef)]
  ["SqrtRatio_z"] opaqueInner == ["Z"]
#guard traitImplDepTypeConflicts
  [("SqrtRatio_z", implConstDef), ("map_to_curve", genericConstDef)]
  ["SqrtRatio_z"] transparentInner == []

/-! ### The wrapped type of an emitted newtype alias

The newtype block is emitted from the crate's struct declarations, so
`abbrev <Name> := <Inner>` and the two definitional wrappers name the wrapped
type whichever definitions survive to the emit. When the wrapped type is opaque
and nothing else names it — which is what reading a crate with its trait
`impl`s opaque leaves behind, the `impl` method bodies having been the only
sites at the concrete type — the axiom block is still what gives the alias a
right-hand side. -/

/-- The emitted file of a crate that defines `inv0` and one newtype, where no
    body, signature or `Deps` field names the wrapped type. -/
def newtypeFile (inner : ImpType) : String :=
  toLeanCertifiedFileTyped [("inv0", genericInvDef)] "Test" [] []
    [("inv0", genericInvDef)] [("Fe51H2C", inner)]

#guard ((newtypeFile wrappedTy).splitOn "axiom Fe51 : Type").length == 2
#guard ((newtypeFile wrappedTy).splitOn "abbrev Fe51H2C := Fe51\n").length == 2
-- A wrapped type the surface prints structurally is declared by the alias
-- itself and takes no axiom.
#guard ((newtypeFile (.array (.uint .w64) 5)).splitOn "axiom Fe51 : Type").length == 1
#guard ((newtypeFile (.array (.uint .w64) 5)).splitOn
  "abbrev Fe51H2C := Array (Int)\n").length == 2

/-! ### Module docstring and elaboration options of the emitted header

The generated file carries a module docstring in the `/-! ... -/` form with a
`## Main definitions` section, placed after the imports, and sets only the
recursion depth the nested literals need. The docstring is derived from the
emit: the crate, the `Deps` class and whether the definitions stand under its
`variable` binder, the number of extracted functions, and the types left as
`axiom`. -/

/-- The emitted file of the erased-newtype crate above, whose `Deps` class has
    no fields. -/
def scalarCtorFile : String :=
  toLeanCertifiedFileTyped [("from_bytes_secret", scalarCtorFn)] "Test" [] [] []
    (newtypes := scalarNewtypes)

#guard ((newtypeFile wrappedTy).splitOn "\n/-!\n# `Test`: haxpipeT extraction\n").length == 2
#guard ((newtypeFile wrappedTy).splitOn "\n## Main definitions\n").length == 2
#guard ((scalarCtorFile.splitOn "\n## Main definitions\n")).length == 2

-- The header sets no heartbeat budget: every extraction elaborates inside the
-- 200000 default, and the recursion depth is the one option the nested
-- `ImpExpr`/`TExpr` literals need.
#guard ((newtypeFile wrappedTy).splitOn "maxHeartbeats").length == 1
#guard (scalarCtorFile.splitOn "maxHeartbeats").length == 1
#guard ((newtypeFile wrappedTy).splitOn "set_option maxRecDepth 2048\n").length == 2

-- The `Deps` class is named either way, and the parametricity claim follows the
-- `variable` binder: a class with fields carries one, an empty class does not.
#guard ((moduleDocstring "Test" "test-hax" true 3 []).splitOn
  "variable [TestDeps]").length == 2
#guard ((moduleDocstring "Test" "test-hax" false 3 []).splitOn
  "the class has no fields").length == 2
#guard (scalarCtorFile.splitOn "the class has no fields").length == 2

-- The opaque types of the emit are named, the crate is named when the caller
-- supplies one, and the function count agrees in number.
#guard ((newtypeFile wrappedTy).splitOn "instantiate: `Fe51`.").length == 2
#guard ((moduleDocstring "Test" "test-hax" true 3 []).splitOn "`test-hax`").length == 2
#guard ((moduleDocstring "Test" "" true 3 []).splitOn "extraction of the crate,").length == 2
#guard ((moduleDocstring "Test" "t-hax" true 1 []).splitOn
  "1 extracted function:").length == 2
#guard ((moduleDocstring "Test" "t-hax" true 2 []).splitOn
  "2 extracted functions:").length == 2

/-! ### Trait-to-class emission

`--emit-classes` (`Hax.ClassEmit`) renders each trait as a class, keeps a
generic function generic over its trait bounds, renders each trait `impl` as
an instance, and orders definitions and instances so that each instance stands
between the definitions it names and the ones that use it. The pins below run
on a synthetic trait `Ring` over a supertrait `Base`. -/

open ClassEmit in
/-- `trait Ring: Base { const ZERO: Self; fn add(self, rhs: Self) -> Self; }`
    in the export form of a hax `Trait` item, with its type parameter kept. -/
def ringTraitJson : Lean.Json :=
  let self : Lean.Json := Lean.Json.mkObj [("id", 1), ("value",
    Lean.Json.mkObj [("Param", Lean.Json.mkObj [("index", 0), ("name", "Self")])])]
  let base : Lean.Json := Lean.Json.mkObj [("kind", Lean.Json.mkObj [("value",
    Lean.Json.mkObj [("Trait", Lean.Json.mkObj [("trait_ref", Lean.Json.mkObj [("value",
      Lean.Json.mkObj [("def_id", Lean.Json.mkObj [("contents", Lean.Json.mkObj [("value",
        Lean.Json.mkObj [("krate", "k"), ("path", Lean.Json.arr #[Lean.Json.mkObj
          [("data", Lean.Json.mkObj [("TypeNs", "Base")])]])])])])])])])])])]
  let item (name : String) (kind : Lean.Json) : Lean.Json :=
    Lean.Json.mkObj [("ident", Lean.Json.arr #[name, .null]), ("kind", kind)]
  let zero := item "ZERO" (Lean.Json.mkObj [("Const", Lean.Json.arr #[self, .null])])
  let add := item "add" (Lean.Json.mkObj [("RequiredFn", Lean.Json.arr #[
    Lean.Json.mkObj [("decl", Lean.Json.mkObj [("inputs", Lean.Json.arr #[self, self]),
      ("output", Lean.Json.mkObj [("Return", self)])])],
    Lean.Json.arr #[Lean.Json.arr #["self", .null], Lean.Json.arr #["rhs", .null]]])])
  keepTypeParams (Lean.Json.arr #[Lean.Json.mkObj [
    ("kind", Lean.Json.mkObj [("Trait", Lean.Json.arr #["NotConst", "No", "Safe",
      Lean.Json.arr #["Ring", .null], Lean.Json.mkObj [], Lean.Json.arr #[base],
      Lean.Json.arr #[zero, add]])]),
    ("owner_id", Lean.Json.mkObj [("contents", Lean.Json.mkObj [("value",
      Lean.Json.mkObj [("krate", "k")])])])]])

/-- The plan for a crate generic over `Ring`: `Ring` and `Base` as classes, `add`
    exported, `f<F: Ring>` generic, a generic struct `P<F>`, and one `impl Ring
    for Fe`. -/
def ringHooks : ClassEmit.ClassHooks :=
  { traits := ClassEmit.orderTraits
      ({ name := "Base", krate := "k" } :: ClassEmit.parseTraitDefs ringTraitJson)
    exports := [("Ring", ["add"])]
    genericFns := [{ name := "f", typeParams := ["F"], bounds := [("Ring", "F")] }]
    genericStructs := [("P", ["F"])]
    instances := [{ trait := "Ring", selfTy := .adt "Fe" [],
                    fields := [("ZERO", "Ring_ZERO"), ("add", "Ring_add")] }] }

-- A type parameter is kept as a named type variable only in a rewritten export.
#guard match HaxAdapter.parseHaxType (Lean.Json.mkObj [("value",
    Lean.Json.mkObj [("Param", Lean.Json.mkObj [("index", 0), ("name", "F")])])]) with
  | .slice .int => true | _ => false
#guard match HaxAdapter.parseHaxType (ClassEmit.keepTypeParams (Lean.Json.mkObj [("value",
    Lean.Json.mkObj [("Param", Lean.Json.mkObj [("index", 0), ("name", "F")])])])) with
  | .typeVar "F" => true | _ => false

-- The trait definition is read with its supertrait, constant and method, and
-- follows its supertrait.
#guard ringHooks.traits.map (·.name) == ["Base", "Ring"]
#guard ((ringHooks.renderClasses (fun _ => none)).splitOn
  "class Ring (Self : Type) extends Base Self where\n  ZERO : Self\n  add (self : Self) (rhs : Self) : Self").length == 2
#guard ((ringHooks.renderClasses (fun _ => none)).splitOn "export Ring (add)").length == 2

/-- The `Alias` node of the projection `P::NttForm` of the trait `PolyRing` on
    the type parameter `P`. -/
def nttFormProjJson (param : String) : Lean.Json :=
  let defId (path : List String) : Lean.Json := Lean.Json.mkObj [("contents",
    Lean.Json.mkObj [("value", Lean.Json.mkObj [("krate", "k"), ("path",
      Lean.Json.arr (path.toArray.map fun s =>
        Lean.Json.mkObj [("data", Lean.Json.mkObj [("TypeNs", .str s)])]))])])]
  Lean.Json.mkObj [("kind", Lean.Json.mkObj [("Projection", Lean.Json.mkObj [
    ("impl_expr", Lean.Json.mkObj [("trait", Lean.Json.mkObj [("value", Lean.Json.mkObj [
      ("value", Lean.Json.mkObj [
        ("def_id", defId ["poly", "PolyRing"]),
        ("generic_args", Lean.Json.arr #[Lean.Json.mkObj [("Type", Lean.Json.mkObj [
          ("value", Lean.Json.mkObj [("Param", Lean.Json.mkObj [("index", 0),
            ("name", .str param)])])])]])])])])]),
    ("assoc_item", Lean.Json.mkObj [("def_id", defId ["poly", "PolyRing", "NttForm"])])])])]

-- A projection on `Self` is the class field; a projection on another type
-- parameter is the class field applied to it.
#guard ClassEmit.selfAssocName (nttFormProjJson "Self") == some "NttForm"
#guard ClassEmit.paramAssocType (nttFormProjJson "Self") == none
#guard ClassEmit.paramAssocType (nttFormProjJson "R") == some "(PolyRing.NttForm R)"
#guard match HaxAdapter.parseHaxType (ClassEmit.keepTypeParams (Lean.Json.mkObj
    [("value", Lean.Json.mkObj [("Alias", nttFormProjJson "R")])])) with
  | .typeVar "(PolyRing.NttForm R)" => true | _ => false

-- A trait that both the trait export and the crate export define is planned
-- and rendered once.
#guard (ClassEmit.plan ringTraitJson ringTraitJson).traits.map (·.name) == ["Ring"]
#guard (((ClassEmit.plan ringTraitJson ringTraitJson).renderClasses (fun _ => none)).splitOn
  "class Ring ").length == 2

-- A generic struct renders at its type arguments; the default plan leaves the
-- lookup as it was.
#guard (ImpType.adt "P" [.typeVar "F"]).toLeanTypeStrSurface (ringHooks.wrapLookup opaqueInner)
  == "P_T F"
#guard (ImpType.adt "P" [.adt "Fe51" []]).toLeanTypeStrSurface
  (ringHooks.wrapLookup transparentInner) == "P_T (Array Int)"
#guard (ImpType.adt "P" [.typeVar "F"]).toLeanTypeStrSurface
  (({} : ClassEmit.ClassHooks).wrapLookup opaqueInner) == "P"

-- A generic function takes its type parameters and bounds as binders.
#guard ringHooks.addBinders "f" "def f (x : F) :=\nx\n"
  == "def f {F : Type} [Inhabited F] [Ring F] (x : F) :=\nx\n"
#guard ringHooks.addBinders "g" "def g (x : Int) :=\nx\n" == "def g (x : Int) :=\nx\n"

-- The instance names the `impl`'s definitions and fills its supertrait field by
-- instance resolution.
#guard ringHooks.renderInstance (fun _ => none) ringHooks.instances.head!
  == "instance : Ring Fe where\n  toBase := inferInstance\n  ZERO := Ring_ZERO\n  add := Ring_add\n"

-- The instance stands after the definitions it names and before the concrete
-- definition that calls the generic one; a cycle leaves the order to `mutual`.
#guard (ringHooks.orderBody (fun _ => none)
    [("user", "U", ["f"]), ("f", "F", ["add"]), ("Ring_add", "A", []),
     ("Ring_ZERO", "Z", [])]).map (·.map (·.take 1 |>.toString))
  == some ["F", "A", "Z", "i", "U"]
#guard (ringHooks.orderBody (fun _ => none)
    [("a", "A", ["b"]), ("b", "B", ["a"])]).isNone

/-- The typed literal of `fn demo<R: PolyRing>(a_hat: R::NttForm, s: R) -> R::NttForm`
    with its parameters bound to themselves, as the adapter reads it from an export
    rewritten by `keepTypeParams`. -/
def projParamDef : TExpr :=
  let nttTy : ImpType := .typeVar "(PolyRing.NttForm R)"
  .mk (.letBind "a_hat" (.mk (.var "a_hat") nttTy)
    (.mk (.letBind "s" (.mk (.var "s") (.typeVar "R")) (.mk (.var "a_hat") nttTy)) nttTy)) nttTy

-- A parameter typed by a type parameter or by an associated type of one is
-- annotated in the surface signature, the associated type as the class field
-- applied to the parameter.
#guard (toLeanDefTyped "demo" projParamDef projParamDef.erase).startsWith
  "def demo (a_hat : (PolyRing.NttForm R)) (s : R) :=\n"

/-- A read of the associated constant `Field::ZERO` whose `in_trait.impl` atom has
    the kind `atom`, as the `contents` of a hax expression node. -/
def assocConstReadJson (atom : String) : Lean.Json :=
  let seg (k v : String) : Lean.Json := Lean.Json.mkObj [("data", Lean.Json.mkObj [(k, .str v)])]
  Lean.Json.mkObj [("contents", Lean.Json.mkObj [("NamedConst", Lean.Json.mkObj [
    ("item", Lean.Json.mkObj [("value", Lean.Json.mkObj [
      ("def_id", Lean.Json.mkObj [("contents", Lean.Json.mkObj [("value", Lean.Json.mkObj [
        ("krate", "k"), ("path", Lean.Json.arr #[seg "TypeNs" "Field", seg "ValueNs" "ZERO"]),
        ("kind", "AssocConst")])])]),
      ("in_trait", Lean.Json.mkObj [("impl", Lean.Json.mkObj [(atom, Lean.Json.mkObj [])])])])])])])]

-- In the class mode a read of an associated constant through a trait bound is a
-- nullary call of the class constant; the default mode reads it as a variable, and
-- a read through a `Concrete` atom stays a variable in both modes.
#guard match HaxAdapter.parseHaxTExpr (assocConstReadJson "LocalBound")
    { localBoundConstCalls := true } with
  | .ok (.mk (.app "ZERO" []) _) => true | _ => false
#guard match HaxAdapter.parseHaxTExpr (assocConstReadJson "LocalBound") with
  | .ok (.mk (.var "ZERO") _) => true | _ => false
#guard match HaxAdapter.parseHaxTExpr (assocConstReadJson "Concrete")
    { localBoundConstCalls := true } with
  | .ok (.mk (.var "ZERO") _) => true | _ => false

end Hax.EmitterRegressions

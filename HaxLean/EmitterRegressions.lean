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
  ++ "\nset_option linter.unusedVariables false\nset_option maxRecDepth 2048\n\nnamespace Test\n\nopen Hax\n\n-- All emitted functions are `noncomputable`: extracted bodies may\n-- depend on Runtime axioms (sha256, bridgeCast, ...) which the Lean\n-- code generator rejects. Verification doesn't require execution.\nnoncomputable section\n\n/-- Newtype tuple-struct aliases: transparent type equalities\n    with definitional `.0` unwraps and definitional constructors. Inner\n    types may themselves be axiomatized (see the axiom block above). -/\nabbrev Scalar := Array (Int)\nnoncomputable def «Scalar.0» (x : Scalar) : Array (Int) := x\nnoncomputable def «Scalar.mk» (x : Array (Int)) : Scalar := x\n\n\n/-- External dependencies for Test extraction (auto-generated). -/\nclass TestDeps where\n\n\n/-- Type annotations shared by the `TExpr` literals. -/\nabbrev ty_0 : ImpType := .unknown\n\nmutual\n\ndef from_bytes_secret :=\n(fun bytes => «Scalar.mk» bytes)\n\nend\n\ndef from_bytes_secret_impExpr : ImpExpr :=\n  (.lam [\"bytes\"] (.app \"Scalar.mk\" [(.var \"bytes\")]))\n\ndef from_bytes_secret_texpr : TExpr :=\n  (.mk (.lam [\"bytes\"] (.mk (.app \"Scalar.mk\" [(.mk (.var \"bytes\") ty_0)]) ty_0)) ty_0)\n\nexample : from_bytes_secret_texpr.erase = from_bytes_secret_impExpr := rfl\n\nend  -- noncomputable section\n\nend Test\n"

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
  "def f (a : Array (Int)) (b : Array (Int)) : Array (Int) :=\nmul a b\n\nend\n\ndef f_impExpr : ImpExpr :=\n  (.letBind \"a\" (.var \"a\") (.letBind \"b\" (.var \"b\") (.app \"mul\" [(.var \"a\"), (.var \"b\")])))\n").length == 2
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

-- The `mutual` block closes before the first `ImpExpr` literal, so each
-- literal is a separate command with its own heartbeat budget.
#guard (scalarCtorFile.splitOn "\nend\n\ndef from_bytes_secret_impExpr : ImpExpr").length == 2
#guard (((scalarCtorFile.splitOn "_texpr : TExpr").getD 1 "").splitOn "\nend\n").length == 1

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

/-! ## A `&mut self` setter writing an element of a `Vec` field

`fn set(&mut self, i: usize, val: u64) { self.cells[i] = val; }` on
`struct Trace { width: usize, height: usize, cells: Vec<u64> }`. For a `Vec`
field hax gives the place `self.cells[i]` as the overloaded call
`*IndexMut::index_mut(&mut (*self).cells, i)`. The parse lowers the write to an
assignment of `self` to a functional update of its `cells` field, which makes
`Trace_set` a write-back function: its body ends in `self`, and a call
`Trace_set(&mut t, …)` in statement position rebinds `t`. -/

open Lean in
/-- A hax expression node with the given `contents`. -/
def haxNode (contents : Json) : Json := Json.mkObj [("contents", contents)]

open Lean in
/-- A read of the local variable `n`. -/
def haxVarRef (n : String) : Json :=
  haxNode (Json.mkObj [("VarRef", Json.mkObj [("id", Json.mkObj [("name", Json.str n)])])])

open Lean in
/-- The place `self.cells[i]` as hax exports it for a `Vec` field:
    `*IndexMut::index_mut(&mut (*self).cells, i)`. -/
def traceCellPlaceJson : Json :=
  let selfDeref := haxNode (Json.mkObj [("Deref", Json.mkObj [("arg", haxVarRef "self")])])
  let cellsField := haxNode (Json.mkObj [("Field", Json.mkObj [
    ("field", mkDefIdJson "plonky3_hax"
      [defIdSeg "TypeNs" "air", defIdSeg "TypeNs" "Trace", defIdSeg "ValueNs" "cells"]),
    ("lhs", selfDeref)])])
  let borrowMut := haxNode (Json.mkObj [("Borrow", Json.mkObj [("arg", cellsField)])])
  let indexMutFn := haxNode (Json.mkObj [("GlobalName", Json.mkObj [
    ("item", Json.mkObj [("def_id", mkDefIdJson "core"
      [defIdSeg "TypeNs" "ops", defIdSeg "TypeNs" "index", defIdSeg "TypeNs" "IndexMut",
       defIdSeg "ValueNs" "index_mut"])])])])
  let call := haxNode (Json.mkObj [("Call", Json.mkObj [
    ("fun", indexMutFn), ("args", Json.arr #[borrowMut, haxVarRef "i"])])])
  haxNode (Json.mkObj [("Deref", Json.mkObj [("arg", call)])])

open Lean in
/-- The statement `self.cells[i] = val`. -/
def traceSetAssignJson : Json :=
  haxNode (Json.mkObj [("Assign", Json.mkObj [
    ("lhs", traceCellPlaceJson), ("rhs", haxVarRef "val")])])

/-- Field layout of `Trace`. -/
def traceFields : StructFieldNames := [("Trace", ["width", "height", "cells"])]

/-- The parse of `self.cells[i] = val` under `traceFields`. -/
def traceSetAssign : TExpr :=
  match HaxAdapter.parseHaxTExpr traceSetAssignJson { structFields := traceFields } with
  | .ok e => e
  | .error _ => .mk .unitVal .unit

-- The write is an assignment of `self`: `cells` (position 2 of 3) updated at `i`.
#guard traceSetAssign.erase == .assign "self" (.app "struct_update#Trace#2#3"
  [.var "self", .app "array_update"
    [.app ".cells" [.deref (.var "self")], .var "i", .var "val"]])

/-- `fn set(&mut self, i: usize, val: u64)`. -/
def traceSetSig : FnTypeInfo :=
  ⟨[("self", .ref (.adt "Trace" []) true), ("i", .int), ("val", .int)], .unit⟩

/-- `set`'s body: the assignment, then `()`. -/
def traceSetBody : TExpr := .mk (.seq traceSetAssign (.mk .unitVal .unit)) .unit

/-- The write-back table of an export holding `Trace_set` alone. -/
def traceWriteFns : List (String × List Nat × List String × Bool) :=
  mutWriteFns traceFields [("Trace_set", traceSetSig)] [("Trace_set", traceSetBody)]

#guard traceWriteFns == [("Trace_set", [0], ["self"], false)]

-- The definition returns the updated `self`.
#guard (tReturnMutParams ["self"] false traceSetBody).erase ==
  .seq (.assign "self" (.app "struct_update#Trace#2#3"
    [.var "self", .app "array_update"
      [.app ".cells" [.deref (.var "self")], .var "i", .var "val"]])) (.var "self")

/-- `t.set(0, v); t` — the caller: a statement-position call, then a read of `t`. -/
def traceSetCaller : TExpr :=
  .mk (.seq
    (.mk (.app "Trace_set" [.mk (.borrow (.mk (.var "t") (.adt "Trace" [])))
        (.ref (.adt "Trace" []) true),
      .mk (.lit (.int 0)) .int, .mk (.var "v") .int]) .unit)
    (.mk (.var "t") (.adt "Trace" []))) (.adt "Trace" [])

-- The call site rebinds `t` to the call's result.
#guard (tRebindMutCalls traceFields (mutWriteTable traceWriteFns) [] traceSetCaller).erase ==
  .seq (.assign "t" (.app "Trace_set" [.borrow (.var "t"), .lit (.int 0), .var "v"]))
    (.var "t")

/-! ## A `Vec` passed to a `&mut [T]` parameter

A `Vec` variable `v` passed where `&mut [T]` is expected, as in
`ntt(&mut coeffs, ω)` with `coeffs : Vec<u64>`, reaches hax as the deref
coercion `&mut *DerefMut::deref_mut(&mut v)`. The parse reads the argument as
the place `v`, so a write-back callee rebinds `v` and the dropped-write-back
check has nothing to report. A `deref_mut` feeding a callee outside the
write-back rewrite (`split_at_mut`, which splits the place in two), or bound to
a name, is still reported. -/

open Lean in
/-- A hax expression node with the given type and `contents`. -/
def haxNodeT (ty contents : Json) : Json :=
  Json.mkObj [("ty", ty), ("contents", contents)]

open Lean in
/-- The type `&mut t`. -/
def refMutTyJson (t : Json) : Json :=
  Json.mkObj [("Ref", Json.arr #[Json.mkObj [("kind", Json.str "ReErased")], t, Json.bool true])]

open Lean in
/-- The type `Vec<u64>`. -/
def vecTyJson : Json :=
  Json.mkObj [("Adt", Json.mkObj [
    ("def_id", mkDefIdJson "alloc" [defIdSeg "TypeNs" "vec", defIdSeg "TypeNs" "Vec"]),
    ("generic_args", Json.arr #[])])]

open Lean in
/-- The type `[u64]`. -/
def sliceTyJson : Json :=
  Json.mkObj [("Slice", Json.mkObj [
    ("generic_args", Json.arr #[Json.mkObj [("Type", Json.mkObj [("Uint", Json.str "U64")])]])])]

open Lean in
/-- The function item `krate::segs`. -/
def haxFnJson (krate : String) (segs : List Json) : Json :=
  haxNode (Json.mkObj [("GlobalName", Json.mkObj [
    ("item", Json.mkObj [("def_id", mkDefIdJson krate segs)])])])

open Lean in
/-- `&mut *DerefMut::deref_mut(&mut v)` for `v : Vec<u64>`, typed `&mut [u64]`. -/
def derefMutVecArgJson (v : String) : Json :=
  let borrowV := haxNodeT (refMutTyJson vecTyJson)
    (Json.mkObj [("Borrow", Json.mkObj [("arg", haxVarRef v)])])
  let derefMutFn := haxFnJson "core"
    [defIdSeg "TypeNs" "ops", defIdSeg "TypeNs" "deref", defIdSeg "TypeNs" "DerefMut",
     defIdSeg "ValueNs" "deref_mut"]
  let call := haxNodeT (refMutTyJson sliceTyJson)
    (Json.mkObj [("Call", Json.mkObj [("fun", derefMutFn), ("args", Json.arr #[borrowV])])])
  let deref := haxNodeT sliceTyJson (Json.mkObj [("Deref", Json.mkObj [("arg", call)])])
  haxNodeT (refMutTyJson sliceTyJson) (Json.mkObj [("Borrow", Json.mkObj [("arg", deref)])])

open Lean in
/-- The call `f(&mut *deref_mut(&mut v), x)` of the crate function `ntt::f`. -/
def derefMutCallJson (f v x : String) : Json :=
  haxNode (Json.mkObj [("Call", Json.mkObj [
    ("fun", haxFnJson "plonky3_hax" [defIdSeg "TypeNs" "ntt", defIdSeg "ValueNs" f]),
    ("args", Json.arr #[derefMutVecArgJson v, haxVarRef x])])])

/-- The typed parse of a hax expression, `()` on a parse error. -/
def parseT (j : Lean.Json) : TExpr :=
  match HaxAdapter.parseHaxTExpr j {} with
  | .ok e => e
  | .error _ => .mk .unitVal .unit

/-- `ntt(&mut coeffs, omega)` with `coeffs : Vec<u64>`. -/
def nttVecCall : TExpr := parseT (derefMutCallJson "ntt" "coeffs" "omega")

-- The `deref_mut` re-borrow is gone; the argument's root is `coeffs`.
#guard nttVecCall.erase ==
  .app "ntt" [.borrow (.deref (.borrow (.var "coeffs"))), .var "omega"]

/-- `fn ntt(vals: &mut [u64], omega: u64)`. -/
def nttSig : FnTypeInfo :=
  ⟨[("vals", .ref (.slice (.uint .w64)) true), ("omega", .uint .w64)], .unit⟩

-- In statement position the call rebinds `coeffs`, and nothing is dropped.
#guard (tRebindMutCalls [] [("ntt", 0)] [] nttVecCall).erase ==
  .assign "coeffs" (.app "ntt" [.borrow (.deref (.borrow (.var "coeffs"))), .var "omega"])
#guard tDroppedMutCalls [("ntt", nttSig)] [] [("ntt", 0)] [] nttVecCall == []

/-- `coeffs.split_at_mut(h)` with `coeffs : Vec<u64>`: the two halves are
    separate places, which the write-back rewrite does not thread. -/
def splitAtMutVecCall : TExpr := parseT (derefMutCallJson "split_at_mut" "coeffs" "h")

#guard tDroppedMutCalls [("ntt", nttSig)] [] [("ntt", 0)] [] splitAtMutVecCall ==
  [("split_at_mut", [0])]

/-- `let r: &mut [u64] = &mut coeffs; r`: the re-borrow bound to a name stays a
    `deref_mut` call, whose target a later write through `r` does not reach. -/
def derefMutLet : TExpr :=
  .mk (.letBind "r" (parseT (derefMutVecArgJson "coeffs")) (.mk (.var "r") .unknown)) .unknown

#guard tDroppedMutCalls [] [] [] [] derefMutLet == [("deref_mut", [0])]

/-! ## `swap` on a `&mut [T]` place

In `fn ntt(vals: &mut [u64], ω)`, the statement `vals.swap(i, j)` reaches hax as
the `core` slice method call `swap(&mut *vals, i, j)`. The parse reads it as the
assignment of `vals` to the array with cells `i` and `j` exchanged, guarded by
both indices being in range (`tSliceSwap`); the rewritten form passes no `&mut`
argument, and the definition returns the updated `vals`. A crate function of
the same name is left a call and reported. -/

open Lean in
/-- `&mut *v` for a variable `v : &mut [u64]`, typed `&mut [u64]`. -/
def reborrowSliceArgJson (v : String) : Json :=
  let var := haxNodeT (refMutTyJson sliceTyJson)
    (Json.mkObj [("VarRef", Json.mkObj [("id", Json.mkObj [("name", Json.str v)])])])
  let deref := haxNodeT sliceTyJson (Json.mkObj [("Deref", Json.mkObj [("arg", var)])])
  haxNodeT (refMutTyJson sliceTyJson) (Json.mkObj [("Borrow", Json.mkObj [("arg", deref)])])

open Lean in
/-- `v.swap(i, j)` for `v : &mut [u64]`: the call
    `core::slice::<impl [T]>::swap(&mut *v, i, j)`. -/
def sliceSwapCallJson (v i j : String) : Json :=
  let swapFn := haxFnJson "core"
    [defIdSeg "TypeNs" "slice", Json.mkObj [("data", Json.str "Impl")],
     defIdSeg "ValueNs" "swap"]
  haxNode (Json.mkObj [("Call", Json.mkObj [("fun", swapFn),
    ("args", Json.arr #[reborrowSliceArgJson v, haxVarRef i, haxVarRef j])])])

/-- `vals.swap(i, j)` with `vals : &mut [u64]`. -/
def sliceSwapCall : TExpr := parseT (sliceSwapCallJson "vals" "i" "j")

/-- The value of `vals` read through its reference. -/
def valsDeref : ImpExpr := .deref (.var "vals")

-- The call is the rebinding of `vals` to the swapped array.
#guard sliceSwapCall.erase ==
  .assign "vals" (.ifThenElse
    (.app "&&" [.app "Lt" [.var "i", .app "len" [valsDeref]],
                .app "Lt" [.var "j", .app "len" [valsDeref]]])
    (.app "array_update"
      [.app "array_update" [valsDeref, .var "i", .app "index" [valsDeref, .var "j"]],
       .var "j", .app "index" [valsDeref, .var "i"]])
    valsDeref)

-- Nothing is dropped, whether or not `swap` is in the write-back table.
#guard tDroppedMutCalls [("ntt", nttSig)] [] [("ntt", 0)] [] sliceSwapCall == []
#guard tDroppedMutCalls [] [] builtinWriteTable [] sliceSwapCall == []

-- The definition returns the updated `vals`.
#guard (tReturnMutParams ["vals"] false sliceSwapCall).erase ==
  .seq sliceSwapCall.erase (.var "vals")

/-- `swap(&mut coeffs, h)` for a crate function `ntt::swap`: not the slice method. -/
def crateSwapCall : TExpr := parseT (derefMutCallJson "swap" "coeffs" "h")

#guard tDroppedMutCalls [] [] [] [] crateSwapCall == [("swap", [0])]

/-! ## `reverse` and `Vec::remove` on a `&mut` place

`path.reverse()` with `path : Vec<u64>` reaches hax as the `core` slice method
call `reverse(&mut *deref_mut(&mut path))`; the parse reads it as the
assignment `path := slice_reverse path` (`tSliceReverse`). `self.cells.remove(i)` on
`Trace` reaches hax as `alloc::vec::Vec::remove(&mut (*self).cells, i)`; the
parse binds the pair `vec_remove (*self).cells i` of the removed element and the
shortened vector, rebinds `self` to `self` with `cells` set to the vector, and
returns the element (`tVecRemove`). Neither form passes a `&mut` argument. -/

open Lean in
/-- `path.reverse()` for `path : Vec<u64>`: the call
    `core::slice::<impl [T]>::reverse(&mut *deref_mut(&mut path))`. -/
def sliceReverseCallJson (v : String) : Json :=
  let revFn := haxFnJson "core"
    [defIdSeg "TypeNs" "slice", Json.mkObj [("data", Json.str "Impl")],
     defIdSeg "ValueNs" "reverse"]
  haxNode (Json.mkObj [("Call", Json.mkObj [("fun", revFn),
    ("args", Json.arr #[derefMutVecArgJson v])])])

/-- `path.reverse()` with `path : Vec<u64>`. -/
def sliceReverseCall : TExpr := parseT (sliceReverseCallJson "path")

-- The call is the rebinding of `path` to its reverse.
#guard sliceReverseCall.erase == .assign "path" (.app "slice_reverse" [.var "path"])

-- It renders as the runtime function, not as a `Deps` field.
#guard runtimeName "slice_reverse" == "Hax.slice_reverse" && isAlwaysBuiltin "slice_reverse"
#guard runtimeName "vec_remove" == "Hax.vec_remove" && isAlwaysBuiltin "vec_remove"

-- Nothing is dropped.
#guard tDroppedMutCalls [] [] [] [] sliceReverseCall == []

open Lean in
/-- `self.cells.remove(i)` on `Trace`: the call
    `alloc::vec::<impl Vec<T>>::remove(&mut (*self).cells, i)`. -/
def traceRemoveCallJson : Json :=
  let selfDeref := haxNode (Json.mkObj [("Deref", Json.mkObj [("arg", haxVarRef "self")])])
  let cellsField := haxNodeT vecTyJson (Json.mkObj [("Field", Json.mkObj [
    ("field", mkDefIdJson "plonky3_hax"
      [defIdSeg "TypeNs" "air", defIdSeg "TypeNs" "Trace", defIdSeg "ValueNs" "cells"]),
    ("lhs", selfDeref)])])
  let borrowMut := haxNodeT (refMutTyJson vecTyJson)
    (Json.mkObj [("Borrow", Json.mkObj [("arg", cellsField)])])
  let removeFn := haxFnJson "alloc"
    [defIdSeg "TypeNs" "vec", Json.mkObj [("data", Json.str "Impl")],
     defIdSeg "ValueNs" "remove"]
  haxNode (Json.mkObj [("Call", Json.mkObj [("fun", removeFn),
    ("args", Json.arr #[borrowMut, haxVarRef "i"])])])

/-- The parse of `self.cells.remove(i)` under `traceFields`. -/
def traceRemoveCall : TExpr :=
  match HaxAdapter.parseHaxTExpr traceRemoveCallJson { structFields := traceFields } with
  | .ok e => e
  | .error _ => .mk .unitVal .unit

-- The write to `self` is kept and the value is the removed element.
#guard traceRemoveCall.erase ==
  .letBind "_removed" (.app "vec_remove" [.app ".cells" [.deref (.var "self")], .var "i"])
    (.seq (.assign "self" (.app "struct_update#Trace#2#3"
        [.var "self", .proj (.var "_removed") 1]))
      (.proj (.var "_removed") 0))

-- Nothing is dropped.
#guard tDroppedMutCalls [] traceFields [] [] traceRemoveCall == []

/-- `fn take(&mut self, i: usize) -> u64 { self.cells.remove(i) }`. -/
def traceTakeSig : FnTypeInfo :=
  ⟨[("self", .ref (.adt "Trace" []) true), ("i", .int)], .uint .w64⟩

-- `take` is a write-back function of `self` with a value result.
#guard mutWriteFns traceFields [("Trace_take", traceTakeSig)]
  [("Trace_take", traceRemoveCall)] == [("Trace_take", [0], ["self"], true)]

/-- `alloc::vec::Vec::remove` applied to a `Vec` variable `v`. -/
def vecRemoveVarCall : TExpr :=
  let vTy : ImpType := .adt "Vec" [.uint .w64]
  let v : TExpr := .mk (.var "v") vTy
  let arg : TExpr := .mk (.borrow v) (.ref vTy true)
  match HaxAdapter.tVecRemove [] arg (.mk (.var "i") .int) with
  | some k => .mk k (.uint .w64)
  | none => .mk .unitVal .unit

-- `v` is rebound to the vector without the element, which is the value.
#guard vecRemoveVarCall.erase ==
  .letBind "_removed" (.app "vec_remove" [.var "v", .var "i"])
    (.seq (.assign "v" (.proj (.var "_removed") 1)) (.proj (.var "_removed") 0))

/-! ## A write to a field of a `Vec` element of a `&mut` parameter

`state.stash[si].leaf = new_leaf` on `struct Oram { stash: Vec<Entry>, depth }`,
with `Entry { id, leaf }` and a second struct `Pos { id, leaf }` declaring the
same field names. hax gives the place as the field `leaf` of
`*index_mut(&mut (*state).stash, si)`. The parse resolves `leaf` through the
element's type `Entry` and lowers the write to an assignment of `state`: the
`stash` field updated at `si` by the element with `leaf` replaced
(`tElemFieldPlaceAssign`). A place no arm lowers, such as `state.a.b` where no
struct declares the fields `a` and `b`, is refused by the parse. -/

/-- Field layouts of `Oram`, `Entry` and `Pos`. -/
def oramFields : StructFieldNames :=
  [("Oram", ["stash", "depth"]), ("Entry", ["id", "leaf"]), ("Pos", ["id", "leaf"])]

open Lean in
/-- The type `types::Entry`. -/
def entryTyJson : Json :=
  Json.mkObj [("Adt", Json.mkObj [
    ("def_id", mkDefIdJson "pathoram_hax" [defIdSeg "TypeNs" "types", defIdSeg "TypeNs" "Entry"]),
    ("generic_args", Json.arr #[])])]

open Lean in
/-- The field `f` of `Oram`/`Entry`, as the `field` of a hax `Field` node. -/
def oramFieldIdJson (s f : String) : Json :=
  mkDefIdJson "pathoram_hax" [defIdSeg "TypeNs" "types", defIdSeg "TypeNs" s, defIdSeg "ValueNs" f]

open Lean in
/-- The statement `state.stash[si].leaf = v`. -/
def stashLeafAssignJson : Json :=
  let stateDeref := haxNode (Json.mkObj [("Deref", Json.mkObj [("arg", haxVarRef "state")])])
  let stashField := haxNodeT vecTyJson (Json.mkObj [("Field", Json.mkObj [
    ("field", oramFieldIdJson "Oram" "stash"), ("lhs", stateDeref)])])
  let borrowMut := haxNodeT (refMutTyJson vecTyJson)
    (Json.mkObj [("Borrow", Json.mkObj [("arg", stashField)])])
  let indexMutFn := haxFnJson "core"
    [defIdSeg "TypeNs" "ops", defIdSeg "TypeNs" "index", defIdSeg "TypeNs" "IndexMut",
     defIdSeg "ValueNs" "index_mut"]
  let call := haxNodeT (refMutTyJson entryTyJson) (Json.mkObj [("Call", Json.mkObj [
    ("fun", indexMutFn), ("args", Json.arr #[borrowMut, haxVarRef "si"])])])
  let elem := haxNodeT entryTyJson (Json.mkObj [("Deref", Json.mkObj [("arg", call)])])
  let place := haxNode (Json.mkObj [("Field", Json.mkObj [
    ("field", oramFieldIdJson "Entry" "leaf"), ("lhs", elem)])])
  haxNode (Json.mkObj [("Assign", Json.mkObj [("lhs", place), ("rhs", haxVarRef "v")])])

/-- The parse of `state.stash[si].leaf = v` under `oramFields`. -/
def stashLeafAssign : Except String TExpr :=
  HaxAdapter.parseHaxTExpr stashLeafAssignJson { structFields := oramFields }

/-- The place `state.stash[si]`, read from the field `stash` of `state`. -/
def stashElem : ImpExpr := .app "index" [.app ".stash" [.deref (.var "state")], .var "si"]

-- The write is kept: `state` is rebound with element `si` of `stash` updated at
-- `leaf` (position 1 of `Entry`'s 2 fields).
#guard match stashLeafAssign with
  | .ok e => e.erase == .assign "state" (.app "struct_update#Oram#0#2"
      [.var "state", .app "array_update"
        [.app ".stash" [.deref (.var "state")], .var "si",
         .app "struct_update#Entry#1#2" [stashElem, .var "v"]]])
  | .error _ => false

open Lean in
/-- The statement `state.a.b = v`, with fields `a` and `b` that no struct of
    `oramFields` declares. -/
def nestedFieldAssignJson : Json :=
  let stateDeref := haxNode (Json.mkObj [("Deref", Json.mkObj [("arg", haxVarRef "state")])])
  let aField := haxNode (Json.mkObj [("Field", Json.mkObj [
    ("field", oramFieldIdJson "Oram" "a"), ("lhs", stateDeref)])])
  let bField := haxNode (Json.mkObj [("Field", Json.mkObj [
    ("field", oramFieldIdJson "A" "b"), ("lhs", aField)])])
  haxNode (Json.mkObj [("Assign", Json.mkObj [("lhs", bField), ("rhs", haxVarRef "v")])])

-- The parse refuses the write rather than drop it.
#guard match HaxAdapter.parseHaxTExpr nestedFieldAssignJson { structFields := oramFields } with
  | .ok _ => false
  | .error _ => true

/-! ## Assignment places lowered by `tPlaceAssign`

The places the specific arms of the parse do not cover and the general lowering
`tPlaceAssign` does: a compound assignment to an element of an element
(`shares[0][i] ^= v`, Picnic), the same through the `index_mut` of a `Vec` of
arrays (`result[j][k] ^= v`, SoftSpoken), and a field whose name two structs
declare, written through a `&mut` parameter (`state.root_key = v`, resolved
by the type of `*state`). -/

open Lean in
/-- The binary operator node `op(lhs, rhs)` as the `op`, `lhs`, `rhs` of an
    `AssignOp`. -/
def assignOpJson (op : String) (lhs rhs : Json) : Json :=
  haxNode (Json.mkObj [("AssignOp", Json.mkObj [("op", Json.str op), ("lhs", lhs), ("rhs", rhs)])])

open Lean in
/-- `a[i]` for hax expressions `a` and `i`. -/
def haxIndexJson (a i : Json) : Json :=
  haxNode (Json.mkObj [("Index", Json.mkObj [("lhs", a), ("index", i)])])

/-- The typed parse of a hax expression under `oramFields`, `()` on a parse
    error. -/
def parseOram (j : Lean.Json) : TExpr :=
  match HaxAdapter.parseHaxTExpr j { structFields := oramFields } with
  | .ok e => e
  | .error _ => .mk .unitVal .unit

/-- `shares[0][i] ^= v`. -/
def sharesXorAssign : TExpr :=
  parseOram (assignOpJson "BitXorAssign"
    (haxIndexJson (haxIndexJson (haxVarRef "shares") (haxVarRef "z")) (haxVarRef "i"))
    (haxVarRef "v"))

/-- The element `shares[z][i]`. -/
def sharesElem : ImpExpr := .app "index" [.app "index" [.var "shares", .var "z"], .var "i"]

-- `shares` is rebound with row `z` updated at `i` by the combined value.
#guard match sharesXorAssign.erase with
  | .assign "shares" (.app "array_update" [.var "shares", .var "z",
      .app "array_update" [.app "index" [.var "shares", .var "z"], .var "i",
        .app _ [e, .var "v"]]]) => e == sharesElem
  | _ => false

open Lean in
/-- `(*index_mut(&mut result, j))[k] ^= v` for `result : Vec<[u8; n]>`. -/
def vecRowXorAssign : TExpr :=
  let borrowRes := haxNodeT (refMutTyJson vecTyJson)
    (Json.mkObj [("Borrow", Json.mkObj [("arg", haxVarRef "result")])])
  let indexMutFn := haxFnJson "core"
    [defIdSeg "TypeNs" "ops", defIdSeg "TypeNs" "index", defIdSeg "TypeNs" "IndexMut",
     defIdSeg "ValueNs" "index_mut"]
  let call := haxNode (Json.mkObj [("Call", Json.mkObj [
    ("fun", indexMutFn), ("args", Json.arr #[borrowRes, haxVarRef "j"])])])
  let row := haxNode (Json.mkObj [("Deref", Json.mkObj [("arg", call)])])
  parseOram (assignOpJson "BitXorAssign" (haxIndexJson row (haxVarRef "k")) (haxVarRef "v"))

-- `result` is rebound with row `j` updated at `k`.
#guard match vecRowXorAssign.erase with
  | .assign "result" (.app "array_update" [.var "result", .var "j",
      .app "array_update" [.app "index" [.var "result", .var "j"], .var "k", _]]) => true
  | _ => false

/-- Field layouts with the field `root_key` declared by two structs. -/
def ratchetFields : StructFieldNames :=
  [("State", ["root_key", "epoch"]), ("Keys", ["root_key"])]

open Lean in
/-- The type `types::State`. -/
def stateTyJson : Json :=
  Json.mkObj [("Adt", Json.mkObj [
    ("def_id", mkDefIdJson "spqr" [defIdSeg "TypeNs" "types", defIdSeg "TypeNs" "State"]),
    ("generic_args", Json.arr #[])])]

open Lean in
/-- `state.root_key = v` for `state : &mut State`: the field of `*state`. -/
def rootKeyAssign : TExpr :=
  let stateDeref := haxNodeT stateTyJson (Json.mkObj [("Deref", Json.mkObj [("arg", haxVarRef "state")])])
  let field := haxNode (Json.mkObj [("Field", Json.mkObj [
    ("field", mkDefIdJson "spqr" [defIdSeg "TypeNs" "types", defIdSeg "TypeNs" "State",
      defIdSeg "ValueNs" "root_key"]),
    ("lhs", stateDeref)])])
  match HaxAdapter.parseHaxTExpr
      (haxNode (Json.mkObj [("Assign", Json.mkObj [("lhs", field), ("rhs", haxVarRef "v")])]))
      { structFields := ratchetFields } with
  | .ok e => e
  | .error _ => .mk .unitVal .unit

-- `state` is rebound with field 0 of `State` replaced.
#guard rootKeyAssign.erase ==
  .assign "state" (.app "struct_update#State#0#2" [.deref (.var "state"), .var "v"])

/-! ## `&mut` calls brought into the write-back fragment

* A call with a value result and a `&mut` argument stored into an element
  (`tmp[i] = wots_chain(…, adrs)`, SLH-DSA) or returned as a block's tail
  (`blake2b_finalize(&mut state)`, Argon2) is bound by a `let`
  (`tHoistMutCalls`), a tuple-form call site.
* A callee outside the export with one `&mut` variable argument and result
  `()` (`jade_sha256(&mut out, input)`, the FFI hash) is a single-form
  write-back function (`externalWriteTable`).
* A `&mut state.h` argument whose field name two structs declare (Classic
  McEliece) is resolved by the type of `state` (`tQualifyWritebackFields`). -/

/-- The type `[u8; 32]`. -/
def bytes32 : ImpType := .array (.uint .w8) 32

/-- `tmp = array_update tmp i (chain(x, &mut adrs))` with a value result. -/
def chainIntoElem : TExpr :=
  let adrsTy : ImpType := .adt "Adrs" []
  let call : TExpr := .mk (.app "chain"
    [.mk (.var "x") bytes32, .mk (.borrow (.mk (.var "adrs") adrsTy)) (.ref adrsTy true)]) bytes32
  .mk (.assign "tmp" (.mk (.app "array_update"
    [.mk (.var "tmp") .unknown, .mk (.var "i") .int, call]) .unknown)) .unit

-- The call is bound first; the element write stores the bound value.
#guard (tHoistMutCalls [] chainIntoElem).erase ==
  .letBind "_mutcall" (.app "chain" [.var "x", .borrow (.var "adrs")])
    (.assign "tmp" (.app "array_update" [.var "tmp", .var "i", .var "_mutcall"]))

-- With `chain` a tuple-form write-back function of its `&mut` argument, nothing
-- is dropped once the call is bound.
#guard tDroppedMutCalls [] [] [] [("chain", [1], true)] (tHoistMutCalls [] chainIntoElem) == []
#guard tDroppedMutCalls [] [] [] [("chain", [1], true)] chainIntoElem == [("chain", [1])]

/-- `let s := init; finalize(&mut s)`: a value call as the tail of a block. -/
def finalizeTail : TExpr :=
  let sTy : ImpType := .adt "St" []
  .mk (.letBind "s" (.mk (.var "init") sTy)
    (.mk (.app "finalize" [.mk (.borrow (.mk (.var "s") sTy)) (.ref sTy true)]) bytes32)) bytes32

-- The tail call is bound by a `let` whose body is the bound value.
#guard (tHoistMutCalls [] finalizeTail).erase ==
  .letBind "s" (.var "init")
    (.letBind "_mutcall" (.app "finalize" [.borrow (.var "s")]) (.var "_mutcall"))
#guard tDroppedMutCalls [] [] [] [("finalize", [0], true)] (tHoistMutCalls [] finalizeTail) == []

/-- `jade_sha256(&mut out, input); out` with `jade_sha256` outside the export. -/
def ffiHashCall : TExpr :=
  .mk (.seq
    (.mk (.app "jade_sha256" [.mk (.borrow (.mk (.var "out") bytes32)) (.ref bytes32 true),
      .mk (.var "input") .unknown]) .unit)
    (.mk (.var "out") bytes32)) bytes32

-- `jade_sha256` is a single-form write-back function of position 0.
#guard externalWriteTable [("sha256", ffiHashCall)] == [("jade_sha256", 0)]

-- The call rebinds `out`, is typed as `out`, and nothing is dropped.
#guard (tRebindMutCalls [] [("jade_sha256", 0)] []
    (tRetypeExtWriters [("jade_sha256", 0)] ffiHashCall)).erase ==
  .seq (.assign "out" (.app "jade_sha256" [.borrow (.var "out"), .var "input"])) (.var "out")
#guard match tRetypeExtWriters [("jade_sha256", 0)] ffiHashCall with
  | .mk (.seq (.mk (.app _ _) ty) _) _ => ty == bytes32
  | _ => false
#guard tDroppedMutCalls [] [] [("jade_sha256", 0)] [] ffiHashCall == []

/-- Two structs declaring a field `h`. -/
def shaFields : StructFieldNames := [("Sha", ["h", "buf"]), ("Toy", ["h"])]

/-- `compress(&mut state.h, block)` with `state : Sha`. -/
def compressField : TExpr :=
  let shaTy : ImpType := .adt "Sha" []
  let place : TExpr := .mk (.app ".h" [.mk (.var "state") shaTy]) (.array (.uint .w32) 8)
  .mk (.app "compress" [.mk (.borrow place) (.ref (.array (.uint .w32) 8) true),
    .mk (.var "block") .unknown]) .unit

-- By name the field does not resolve, so the call is reported.
#guard tDroppedMutCalls [] shaFields [("compress", 0)] [] compressField == [("compress", [0])]

-- Qualified by the type of `state`, the call rebinds `state`, and the
-- projection is renamed `Sha.h`.
#guard tDroppedMutCalls [] shaFields [("compress", 0)] []
    (tQualifyWritebackFields shaFields compressField) == []
#guard (tUnqualifyFieldHeads (tRebindMutCalls shaFields [("compress", 0)] []
    (tQualifyWritebackFields shaFields compressField))).erase ==
  .assign "state" (.app "struct_update#Sha#0#2" [.var "state",
    .app "compress" [.borrow (.app "Sha.h" [.var "state"]), .var "block"]])

/-! ## A `Vec` element compound assignment, a `return` in a write-back function,
    and a trait method named like a local function

* `data[k] ^= v` for `data : Vec<u8>` (SoftSpoken `xor_reduce`): the place
  `*index_mut(&mut data, k)` is read as `index data k` typed `u8`, not with the
  call's type `&mut u8`, so the combined value `BitXor#8(data[k], v)` passes no
  `&mut` argument.
* `return e` in a value-returning write-back function (`hkdf_sha256_expand`,
  which returns `Err` early) returns `(e, okm)`, as its tail does
  (`tReturnMutParamsAtReturns`).
* `ops.finish_login()` on `ops : O` with `O: OpaqueLoginOps`, in a crate that
  also defines a function `finish_login` (OPAQUE): the trait method is named
  `OpaqueLoginOps_finish_login`, so the call does not reach the function. -/

open Lean in
/-- `data[k] ^= v` for `data : Vec<u8>`, with the `index_mut` call typed
    `&mut u8`. -/
def vecByteXorAssign : TExpr :=
  let u8Ty := Json.mkObj [("Uint", Json.str "U8")]
  let borrowData := haxNodeT (refMutTyJson vecTyJson)
    (Json.mkObj [("Borrow", Json.mkObj [("arg", haxVarRef "data")])])
  let indexMutFn := haxFnJson "core"
    [defIdSeg "TypeNs" "ops", defIdSeg "TypeNs" "index", defIdSeg "TypeNs" "IndexMut",
     defIdSeg "ValueNs" "index_mut"]
  let call := haxNodeT (refMutTyJson u8Ty) (Json.mkObj [("Call", Json.mkObj [
    ("fun", indexMutFn), ("args", Json.arr #[borrowData, haxVarRef "k"])])])
  let elem := haxNodeT u8Ty (Json.mkObj [("Deref", Json.mkObj [("arg", call)])])
  parseOram (assignOpJson "BitXorAssign" elem (haxVarRef "v"))

-- The write rebinds `data`, and no call passes a `&mut` argument.
#guard match vecByteXorAssign.erase with
  | .assign "data" (.app "array_update" [.var "data", .var "k", _]) => true
  | _ => false
#guard tDroppedMutCalls [] [] [] [] vecByteXorAssign == []

/-- `if bad { return err }; tail` in a function writing back `okm`. -/
def earlyErrBody : TExpr :=
  .mk (.seq
    (.mk (.ifThenElse (.mk (.var "bad") .bool)
      (.mk (.earlyReturn (.mk (.var "err") .unknown)) .unknown) (.mk .unitVal .unit)) .unit)
    (.mk (.var "ok") .unknown)) .unknown

-- Both exits carry `okm`: the `return` by `tReturnMutParamsAtReturns`, the tail
-- by `tReturnMutParams`.
#guard (tReturnMutParams ["okm"] true (tReturnMutParamsAtReturns ["okm"] true earlyErrBody)).erase
  == .seq (.ifThenElse (.var "bad") (.earlyReturn (.tuple [.var "err", .var "okm"])) .unitVal)
      (.tuple [.var "ok", .var "okm"])

open Lean in
/-- The `DefId` of the method `finish_login` declared by the trait
    `typestate_fsm::OpaqueLoginOps`. -/
def traitMethodDefIdJson : Json :=
  let segs := [defIdSeg "TypeNs" "typestate_fsm", defIdSeg "TypeNs" "OpaqueLoginOps",
    defIdSeg "ValueNs" "finish_login"]
  let parent := Json.mkObj [("contents", Json.mkObj [("value", Json.mkObj [
    ("krate", Json.str "opaque_hax"), ("kind", Json.str "Trait"),
    ("path", Json.arr (segs.take 2).toArray)])])]
  Json.mkObj [("krate", Json.str "opaque_hax"), ("kind", Json.str "AssocFn"),
    ("path", Json.arr segs.toArray), ("parent", parent)]

-- With a local function `finish_login`, the trait method is qualified by its
-- trait; without one, it keeps its short name.
#guard HaxAdapter.extractDefIdName traitMethodDefIdJson []
    { krates := ["opaque_hax"], fnNames := ["finish_login"] } == "OpaqueLoginOps_finish_login"
#guard HaxAdapter.extractDefIdName traitMethodDefIdJson []
    { krates := ["opaque_hax"], fnNames := [] } == "finish_login"

/-! ## Enum variants named like structs, write-back tuple bindings, tail loops
    of a different accumulator shape, and builtin writes of a parameter

* `LoginOutcome::Aborted(Aborted)` (OPAQUE typestate): the variant is written
  `LoginOutcome::Aborted`, which renders as the constructor
  `LoginOutcome.Aborted`, not the struct `Aborted`.
* `let v := _wb.2; let r := _wb.1` after a tuple-form call (SLH-DSA
  `let sig = wots_sign(…, &mut wots_adrs)`) binds the components out of order;
  it is not collapsed to the pattern `let (v, r) := call`, which would swap
  them.
* A `while` loop, or a `for` loop carrying more accumulators, at the tail of a
  `for` body with one accumulator (SoftSpoken `xor_reduce`,
  `pprf_reconstruct`): the tail returns the outer accumulator.
* A parameter written only by `copy_from_slice` into a range of it
  (`hkdf_sha256_expand`'s `okm`): with the builtin table in the write-back
  analysis its function is a write-back function. -/

open Lean in
/-- `LoginOutcome::Aborted(Aborted)`: the variant of the enum
    `typestate_fsm::LoginOutcome` applied to a value of the struct `Aborted`. -/
def abortedVariantJson : Json :=
  let segs := [defIdSeg "TypeNs" "typestate_fsm", defIdSeg "TypeNs" "LoginOutcome"]
  let parent := Json.mkObj [("contents", Json.mkObj [("value", Json.mkObj [
    ("krate", Json.str "opaque_hax"), ("kind", Json.str "Enum"),
    ("path", Json.arr segs.toArray)])])]
  let variant := Json.mkObj [("krate", Json.str "opaque_hax"), ("kind", Json.str "Variant"),
    ("path", Json.arr (segs ++ [defIdSeg "TypeNs" "Aborted"]).toArray), ("parent", parent)]
  let abortedTy := Json.mkObj [("Adt", Json.mkObj [
    ("def_id", mkDefIdJson "opaque_hax" [defIdSeg "TypeNs" "typestate_fsm",
      defIdSeg "TypeNs" "Aborted"]),
    ("generic_args", Json.arr #[])])]
  let inner := haxNodeT abortedTy (Json.mkObj [("VarRef", Json.mkObj [
    ("id", Json.mkObj [("name", Json.str "a")])])])
  haxNode (Json.mkObj [("Adt", Json.mkObj [("info", Json.mkObj [("variant", variant)]),
    ("fields", Json.arr #[Json.mkObj [("value", inner)]])])])

-- The construction's head is the qualified variant.
#guard (parseT abortedVariantJson).erase == .app "LoginOutcome::Aborted" [.var "a"]

/-- The write-back binding chain `let v := _wb.2; let r := _wb.0; body`. -/
def wbChain : ImpExpr :=
  .letBind "v" (.app "::proj::.2" [.var "_wb"]) (.letBind "r" (.proj (.var "_wb") 0) (.var "body"))

-- Out of order: no tuple pattern. In order: the pattern `(r, v)`.
#guard (extractTupleDestr "_wb" wbChain).isNone
#guard extractTupleDestr "_wb"
    (.letBind "r" (.proj (.var "_wb") 0) (.letBind "v" (.app "::proj::.2" [.var "_wb"]) (.var "b")))
  == some (["r", "v"], .var "b")

-- A tail `while` loop is followed by the outer accumulator.
#guard wrapTailFoldForOuterAccs ["data"] (.whileFold (.lit (.bool true)) (.var "w")) ==
  .seq (.whileFold (.lit (.bool true)) (.var "w")) (.var "data")

/-- A `for` loop carrying `sib_idx` and `leaves`. -/
def twoAccFold : ImpExpr :=
  .forFold "i" (.lit (.int 0)) (.var "q")
    (.seq (.seq (.letBind "sib_idx" (.app "Add" [.var "sib_idx", .lit (.int 1)]) (.var "sib_idx"))
        .unitVal)
      (.seq (.letBind "leaves" (.app "array_update" [.var "leaves", .var "i", .var "s"])
        (.var "leaves")) .unitVal))

-- At the tail of a `for` body carrying `leaves` alone, it is destructured and
-- `leaves` is returned.
#guard match wrapTailFoldForOuterAccs ["leaves"] twoAccFold with
  | .letBind "_innerTuple" _ _ => true
  | _ => false

/-- `fn fill(okm: &mut [u8], src: &[u8], n: usize)`. -/
def fillSig : FnTypeInfo :=
  ⟨[("okm", .ref (.slice (.uint .w8)) true), ("src", .unknown), ("n", .int)], .unit⟩

/-- `okm[0..n].copy_from_slice(src)`. -/
def fillBody : TExpr :=
  let okm : TExpr := .mk (.var "okm") (.ref (.slice (.uint .w8)) true)
  let range : TExpr := .mk (.app "Range" [.mk (.lit (.int 0)) .int, .mk (.var "n") .int]) .unknown
  let place : TExpr := .mk (.app "index_mut" [.mk (.borrow (.mk (.deref okm) .unknown)) .unknown,
    range]) .unknown
  .mk (.app "copy_from_slice" [.mk (.borrow (.mk (.deref place) .unknown))
    (.ref (.slice (.uint .w8)) true), .mk (.var "src") .unknown]) .unit

-- With the builtin table, `fill` writes back `okm`; without it, it does not.
#guard mutWriteFnsExt [] [("fill", fillSig)] [("fill", fillBody)] builtinWriteTable ==
  [("fill", [0], ["okm"], false)]
#guard mutWriteFns [] [("fill", fillSig)] [("fill", fillBody)] == []

/-! ### Unit structs

A struct the crate defines with no fields (`pub struct HkdfOutputTooLong;`) is
emitted as a fieldless `structure HkdfOutputTooLong_T` and the definition
`HkdfOutputTooLong : HkdfOutputTooLong_T`, never as an `axiom` type with its
value a `Deps` field. The struct parser reads the `Unit` variant data and the
empty `Tuple` variant data as a struct with no fields. -/

section UnitStructs

open Lean

/-- A hax `Struct` item named `name` whose variant data is `variantData`. -/
def structItemJson (name : String) (variantData : Json) : Json :=
  Json.mkObj [("kind", Json.mkObj [("Struct", Json.arr
    #[Json.arr #[Json.str name, Json.null], Json.null, variantData])])]

/-- `pub struct HkdfOutputTooLong;`. -/
def unitStructJson : Json :=
  structItemJson "HkdfOutputTooLong" (Json.mkObj [("Unit", Json.arr #[Json.null, Json.null])])

/-- `pub struct Empty();`. -/
def emptyTupleStructJson : Json :=
  structItemJson "Empty" (Json.mkObj [("Tuple", Json.arr #[Json.arr #[], Json.null])])

#guard (HaxAdapter.parseStructDefsFromJson (Json.arr #[unitStructJson, emptyTupleStructJson])).map
  (fun si => (si.name, si.fields.length)) == [("HkdfOutputTooLong", 0), ("Empty", 0)]

/-- The unit struct `HkdfOutputTooLong` as a type. -/
def unitStructTy : ImpType := .adt "HkdfOutputTooLong" []

/-- `fn expand(n: usize) -> Result<(), HkdfOutputTooLong> { Err(HkdfOutputTooLong) }`
    after the adapter: the construction is the nullary call of the struct's
    name. -/
def unitStructErrFn : TExpr :=
  .mk (.letBind "n" (.mk (.var "n") .int)
    (.mk (.app "Err" [.mk (.app "HkdfOutputTooLong" []) unitStructTy])
      (.result .unit unitStructTy))) (.result .unit unitStructTy)

/-- The emitted file of a crate defining the unit struct and `expand`. -/
def unitStructFile : String :=
  toLeanCertifiedFileTyped [("expand", unitStructErrFn)] "Test"
    [("HkdfOutputTooLong", [])] []

#guard ((unitStructFile.splitOn
  "structure HkdfOutputTooLong_T where\n  deriving Inhabited, BEq, Repr\n").length) == 2
#guard ((unitStructFile.splitOn
  "def HkdfOutputTooLong : HkdfOutputTooLong_T := {}").length) == 2
-- No `axiom` for the crate-defined type, and no `Deps` field for its value.
#guard ((unitStructFile.splitOn "axiom HkdfOutputTooLong").length) == 1
#guard ((unitStructFile.splitOn "\n  HkdfOutputTooLong :").length) == 1
-- A type the crate does not define stays an `axiom`.
#guard ((toLeanCertifiedFileTyped [("expand", unitStructErrFn)] "Test" [] []).splitOn
  "axiom HkdfOutputTooLong").length == 2

/-! ### Tuple structs

A tuple struct with exactly one field is a newtype. A tuple struct with several
fields is a struct with the positional fields `0`, `1`, …, all of them kept;
its constructor binds them as `«0»`, `«1»`, …. -/

/-- A positional field `idx` of type `u32`. -/
def tupleFieldJson (idx : String) : Json :=
  Json.mkObj [("ident", Json.arr #[Json.str idx, Json.null]),
    ("ty", Json.mkObj [("value", Json.mkObj [("Uint", Json.str "U32")])])]

/-- `pub struct W(u32);`. -/
def newtypeStructJson : Json :=
  structItemJson "W" (Json.mkObj [("Tuple",
    Json.arr #[Json.arr #[tupleFieldJson "0"], Json.null])])

/-- `pub struct Pair(u32, u32);`. -/
def pairStructJson : Json :=
  structItemJson "Pair" (Json.mkObj [("Tuple",
    Json.arr #[Json.arr #[tupleFieldJson "0", tupleFieldJson "1"], Json.null])])

-- The one-field tuple struct is a newtype and not a struct.
#guard (HaxAdapter.buildNewtypeMap (Json.arr #[newtypeStructJson])).map (·.1) == ["W"]
#guard (HaxAdapter.parseStructDefsFromJson (Json.arr #[newtypeStructJson])).isEmpty
-- The two-field tuple struct is a struct with both fields and not a newtype.
#guard (HaxAdapter.buildNewtypeMap (Json.arr #[pairStructJson])).isEmpty
#guard (HaxAdapter.parseStructDefsFromJson (Json.arr #[pairStructJson])).map
  (fun si => (si.name, si.fields.map (·.name))) == [("Pair", ["0", "1"])]

/-- The struct metadata of `Pair`. -/
def pairMeta : StructMeta :=
  (HaxAdapter.parseStructDefsFromJson (Json.arr #[pairStructJson])).map fun si =>
    (si.name, si.fields.map fun fi => (fi.name, fi.typeTag, fi.impType))

/-- `fn swap(p: Pair) -> Pair { Pair(p.1, p.0) }`. -/
def pairSwapFn : TExpr :=
  let pairTy : ImpType := .adt "Pair" []
  let p : TExpr := .mk (.var "p") pairTy
  .mk (.letBind "p" p
    (.mk (.app "Pair" [.mk (.app ".1" [p]) (.uint .w32), .mk (.app ".0" [p]) (.uint .w32)])
      pairTy)) pairTy

/-- The emitted file of a crate defining `Pair` and `swap`. -/
def pairFile : String :=
  toLeanCertifiedFileTyped [("swap", pairSwapFn)] "Test" pairMeta []

#guard ((pairFile.splitOn "def Pair («0» : ").length) == 2
#guard ((pairFile.splitOn " := («0», «1»)").length) == 2
#guard ((pairFile.splitOn "axiom Pair").length) == 1
-- Both positional projections are emitted, at the first and second component.
#guard ((pairFile.splitOn "0» (x : Pair_T) := x.1\n").length) == 2
#guard ((pairFile.splitOn "1» (x : Pair_T) := x.2\n").length) == 2
end UnitStructs

end Hax.EmitterRegressions

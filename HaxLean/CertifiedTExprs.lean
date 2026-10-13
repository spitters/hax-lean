/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.CLI
public import HaxLean.PrettyPrintT
public import HaxLean.TPipeline
public import HaxLean.InlineClosures
public import HaxLean.ThreadMutations

/-!
# The typed extraction of a hax export

The phases `haxpipeT --hax --emit-certified` (`HaxLean/MainT.lean`) runs on a hax frontend
export before it renders the extraction module, and the `TExpr` literals of that module.

## Main definitions

* `dedupByName`: the first entry of each name.
* `typedDefsOfExport`: the typed definitions of an export, read again with every trait
  `impl` opaque when `traitImplDepTypeConflicts` names a conflict.
* `writebackOf`: the write-back normalisation of `ThreadMutations` and its tables.
* `postPipeline`: the write-back rewrite, `tLowerClosureCalls`, `tThreadMut`,
  `tPipelineFull` and `tUnqualifyFieldHeads` of each definition.
* `certifiedTExprs`: the terms `haxpipeT --hax --emit-certified` prints as the `f_texpr`
  literals of an extraction module (`certifiedLiteralTExprs`), from the export text.
-/

@[expose] public section

open Lean (Json)

namespace Hax

/-- Keep the first entry for each name, in first-occurrence order.

The export is read through `parseHaxExport`, which lists each item once, but
two items can still define the same name. `toLeanCertifiedFileTyped` keeps the
first definition of each name before rendering; applying the same rule here
keeps the later ones out of the pipeline, the erasure and the validator. -/
def dedupByName {α : Type} (xs : List (String × α)) : List (String × α) :=
  let step (acc : Array (String × α) × List String) (p : String × α) :
      Array (String × α) × List String :=
    if acc.2.contains p.1 then acc else (acc.1.push p, p.1 :: acc.2)
  (xs.foldl step (#[], [])).1.toList

/-- The typed definitions of an export, each name kept once (`dedupByName`). -/
structure TypedDefs where
  /-- The signatures of the definitions. -/
  fnTypes : List (String × HaxAdapter.FnTypeInfo)
  /-- The definitions with the types of the export. -/
  rawTdefs : List (String × TExpr)
  /-- The definitions prepared for the typed pipeline. -/
  procTdefs : List (String × TExpr)
  /-- The definitions of the methods of the crate's trait `impl`s. -/
  traitImplNames : List String
  /-- The `Deps` names `traitImplDepTypeConflicts` finds used at two types. -/
  depTypeConflicts : List String

/-- The typed definitions of the export `inputJson` (`HaxAdapter.parseHaxFileWithTExpr`).

A `Deps` field has one type, so every site that uses the name has to agree on it.
Resolving the crate's trait `impl`s emits their method bodies at the concrete self type,
and those bodies read the trait items of a further `impl` that stays opaque; where the
crate is also generic over the trait, the same names are used at a type parameter and the
two readings do not print as one type. When `traitImplDepTypeConflicts` names such a
conflict, the export is read again with every trait `impl` opaque, which is uniform.
Under `classMode` (`--emit-classes`) the names a generic function calls through a trait
bound are class items rather than `Deps` fields, the conflict does not arise and the
`impl`s stay resolved. -/
def typedDefsOfExport (inputJson : Json) (structMeta : StructMeta)
    (structFields : StructFieldNames) (newtypes : HaxAdapter.NewtypeMap)
    (classMode : Bool := false) (nominalKrates : List String := []) :
    Except String TypedDefs := do
  let (_expr, fnTypes, rawTdefs, procTdefs) ←
    HaxAdapter.parseHaxFileWithTExpr inputJson structFields
      (traitImplConsts := classMode) (nominalKrates := nominalKrates)
  let fnTypes := dedupByName fnTypes
  let rawTdefs := dedupByName rawTdefs
  let procTdefs := dedupByName procTdefs
  let traitImplNames :=
    ((HaxAdapter.buildTraitImplMethodMap inputJson).map (·.2.2)).eraseDups
  let depTypeConflicts :=
    if traitImplNames.isEmpty || classMode then []
    else
      let erased := procTdefs.map fun (n, te) => (n, te.erase)
      let sl := mkStructLookup structMeta (computeStructPassthrough structMeta erased)
      -- The `Deps` names are the unqualified heads (`--nominal-crates`).
      let raw := rawTdefs.map fun (n, te) =>
        (n, HaxAdapter.tUnqualifyNominalHeads nominalKrates te)
      traitImplDepTypeConflicts raw traitImplNames sl (newtypes.map (·.1))
  if depTypeConflicts.isEmpty then
    pure { fnTypes, rawTdefs, procTdefs, traitImplNames, depTypeConflicts }
  else
    let (_expr, fnTypes, rawTdefs, procTdefs) ←
      HaxAdapter.parseHaxFileWithTExpr inputJson structFields
        (resolveTraitImpls := false) (nominalKrates := nominalKrates)
    pure { fnTypes := dedupByName fnTypes, rawTdefs := dedupByName rawTdefs,
           procTdefs := dedupByName procTdefs, traitImplNames, depTypeConflicts }

/-- The write-back normalisation of a crate's definitions and its tables. -/
structure Writeback where
  /-- The definitions after `tHoistMutCalls`, `tQualifyWritebackFields` and
      `tRetypeExtWriters`. -/
  procTdefs : List (String × TExpr)
  /-- The write-back functions of the crate (`mutWriteFnsExt`). -/
  writeFns : List (String × List Nat × List String × Bool)
  /-- The single-parameter rebind table of the call sites. -/
  writers : List (String × Nat)
  /-- The tuple-form rebind table of the call sites. -/
  tupWriters : List (String × List Nat × Bool)
  /-- The written parameters and result flag of each write-back function. -/
  writeReturns : List (String × List String × Bool)
  /-- The calls through `&mut` outside the write-back rewrite, by caller. -/
  dropped : List (String × String × List Nat)

/-- The write-back normalisation of `ThreadMutations` on `procTdefs`.

Calls outside the write-back fragment are first brought into it (`tHoistMutCalls`,
`tQualifyWritebackFields`, `externalWriteTable`). A parameter written only through a
builtin write (`copy_from_slice` into `okm[a..b]`) makes its function a write-back
function too. The builtin and external tables are appended to the call-site rebind table
only, not to `writeReturns`: `tReturnMutParams` rewrites a callee to return its written
parameters, and these callees have no body in the export to rewrite. -/
def writebackOf (structFields : StructFieldNames)
    (fnTypes : List (String × HaxAdapter.FnTypeInfo)) (procTdefs : List (String × TExpr)) :
    Writeback :=
  let procTdefs := procTdefs.map fun (n, te) =>
    (n, tQualifyWritebackFields structFields (tHoistMutCalls fnTypes te))
  let extWriters := externalWriteTable procTdefs
  let procTdefs := procTdefs.map fun (n, te) => (n, tRetypeExtWriters extWriters te)
  let writeFns :=
    mutWriteFnsExt structFields fnTypes procTdefs (extWriters ++ builtinWriteTable)
  let writers := mutWriteTable writeFns ++ builtinWriteTable ++ extWriters
  let tupWriters := mutWriteTupleTable writeFns
  let writeReturns := mutWriteReturns writeFns
  let dropped := procTdefs.flatMap fun (n, te) =>
    (tDroppedMutCalls fnTypes structFields writers tupWriters te).map fun d => (n, d)
  { procTdefs, writeFns, writers, tupWriters, writeReturns, dropped }

/-- The definitions after the typed pipeline: each `&mut` write-back turned into an
    assignment (`tRebindMutCalls` at the call, `tReturnMutParams` at the definition; the
    call rewrite runs first, so a body whose own tail is a write-back call is an
    assignment before `tReplaceTail` reaches it), `Fn::call` of let-bound closures
    lowered (`tLowerClosureCalls`), mutations threaded across `if` joins (`tThreadMut`),
    then `tPipelineFull` and `tUnqualifyFieldHeads`. -/
def postPipeline (structFields : StructFieldNames) (newtypes : HaxAdapter.NewtypeMap)
    (w : Writeback) : List (String × TExpr) :=
  w.procTdefs.map fun (n, te) =>
    let ret := (w.writeReturns.lookup n).getD ([], false)
    let te := tReturnMutParams ret.1 ret.2 (tReturnMutParamsAtReturns ret.1 ret.2
      (tRebindMutCalls structFields w.writers w.tupWriters te))
    (n, tUnqualifyFieldHeads
      (tPipelineFull newtypes (tThreadMut true (tLowerClosureCalls [] te))))

/-- The typed extraction of the functions of a hax frontend export: the terms
    `haxpipeT --hax --emit-certified` prints as `f_texpr` literals, by name, in the order of
    the extraction module, under no `--emit-classes`, no `--emit-contracts` and no function
    filter; `nominalKrates` is the option `--nominal-crates`. An error names a call through
    `&mut` outside the write-back rewrite, for which `haxpipeT` emits no module, or the
    reason the export does not parse. -/
def certifiedTExprs (input : String) (nominalKrates : List String := []) :
    Except String (List (String × TExpr)) := do
  let inputJson ← parseHaxExport input
  let inputJson := ContractEmit.dropContractItems false inputJson
  let structMeta := structMetaOfJson inputJson
  let newtypes := HaxAdapter.buildNewtypeMap inputJson
  let structFields : StructFieldNames :=
    structMeta.map fun (sname, fields) => (sname, fields.map (·.1))
  let td ← typedDefsOfExport inputJson structMeta structFields newtypes
    (nominalKrates := nominalKrates)
  let w := writebackOf structFields td.fnTypes td.procTdefs
  if let some (n, (f, ps)) := w.dropped.head? then
    throw (s!"`{n}` calls `{f}` through `&mut` (parameter positions {ps}) outside the " ++
      s!"write-back rewrite ({w.dropped.length} such calls); haxpipeT emits no extraction")
  pure <| certifiedLiteralTExprs td.rawTdefs "Generated" structMeta td.fnTypes
    (postPipeline structFields newtypes w) newtypes (nominalKrates := nominalKrates)

end Hax

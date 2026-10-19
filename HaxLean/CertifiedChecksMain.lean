/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.CertifiedTExprs

/-!
# The certified-checks report

The root of `lake exe certified-checks`, imported by no module. For every function of the
hax frontend exports named on the command line, the program computes the typed extraction
of `Hax.certifiedTExprs` step by step and prints, for each pass of that extraction that is
not a refinement under `denote'`, whether the pass changes the function's term:

```
certified-checks PATH...
```

A `PATH` is a hax frontend export (`hax_frontend_export.json`), a directory holding one, or
a directory whose immediate subdirectories hold one. The crate of an export is the name of
its directory.

## Output

One header line, then one tab-separated row per crate and function: the crate, the function,
and one column per pass holding `same` or `changed`. A crate whose export does not parse, or
which has a call through `&mut` outside the write-back rewrite (no extraction), has one row
with function `-` and the reason. The last lines count the functions each pass changes.

## The compared passes

* `wrapMatchArmsCF`: `tWrapMatchArmsCF` inside `tPipelineFull`, applied to `tPipeline` of the
  term `postPipeline` passes to `tPipelineFull`.
* `initFoldAccums`: `tInitMissingFoldAccums []` on the term of `postPipeline`
  (`emitLiteralTerms`).
* `deadCF`, `ifElseAssign`, `mutationDiscard`: the passes of `Canonicalize.canonicalize` of
  those names, each on the output of the passes before it in `canonicalize`
  (`canonicalizePanic` runs between `deadCF` and `ifElseAssign`), from the erasure of
  `literalStructSteps` (`literalSteps`).
* `retypeGuard`: the `retypeWith` term `t` of `certifiedLiterals` on the literal `e`;
  `same` when `t.erase == e`, `changed` when the printed strings of `t.erase` and `e` agree
  and the terms differ, `none` when the printed strings differ (the definition has no
  `TExpr` literal).

The typed terms are compared through their erasures, with the `BEq` instance of `ImpExpr`.
-/

@[expose] public section

namespace Hax.CertifiedChecks

open Lean (Json)

/-- The names of the compared passes, in the order of the columns. -/
def passNames : List String :=
  ["wrapMatchArmsCF", "initFoldAccums", "deadCF", "ifElseAssign", "mutationDiscard",
   "retypeGuard"]

/-- `same` when the two terms are equal, `changed` otherwise. -/
def status (before after : ImpExpr) : String :=
  if before == after then "same" else "changed"

/-- The status of each compared pass, by function, in the order of the extraction module.
    The steps are those of `certifiedTExprs` under its default options. -/
def passRows (input : String) : Except String (List (String × List String)) := do
  let inputJson ← parseHaxExport input
  let inputJson := ContractEmit.dropContractItems false inputJson
  let structMeta := structMetaOfJson inputJson
  let newtypes := HaxAdapter.buildNewtypeMap inputJson
  let structFields : StructFieldNames :=
    structMeta.map fun (sname, fields) => (sname, fields.map (·.1))
  let td ← typedDefsOfExport inputJson structMeta structFields newtypes
  let w := writebackOf structFields td.fnTypes td.procTdefs
  if let some (n, (f, ps)) := w.dropped.head? then
    throw (s!"`{n}` calls `{f}` through `&mut` (parameter positions {ps}) outside the " ++
      s!"write-back rewrite ({w.dropped.length} such calls)")
  -- The `tWrapMatchArmsCF` step of `tPipelineFull`, on the term `postPipeline` passes to it.
  let wrapStatus : List (String × String) := w.procTdefs.map fun (n, te) =>
    let ret := (w.writeReturns.lookup n).getD ([], false)
    let te := tReturnMutParams ret.1 ret.2 (tReturnMutParamsAtReturns ret.1 ret.2
      (tRebindMutCalls structFields w.writers w.tupWriters te))
    let p := tPipeline (tThreadMut true (tLowerClosureCalls [] te))
    (n, status p.erase (tWrapMatchArmsCF p).erase)
  let procTdefs := postPipeline structFields newtypes w
  -- `certifiedLiteralTExprs` as `certifiedTExprs` calls it.
  let prep := certifiedPrep td.rawTdefs "Generated" structMeta td.fnTypes procTdefs newtypes
  let fnTypes := td.fnTypes
  -- `tInitMissingFoldAccums []` of `emitLiteralTerms`.
  let initStatus : List (String × String) := prep.literalProc.map fun (n, te) =>
    (n, status te.erase (tInitMissingFoldAccums [] te).erase)
  -- The canonicalisation of `literalSteps`, pass by pass.
  let literalSrc := emitLiteralTerms structMeta fnTypes prep.literalRaw prep.literalProc
  let canonStatus : List (String × List String) := literalSrc.map fun (n, t) =>
    let e0 := t.erase
    let e1 := Canonicalize.canonicalizeDeadCFBindings e0
    let e2 := Canonicalize.canonicalizePanic e1
    let e3 := Canonicalize.canonicalizeIfElseAssign e2
    let e4 := Canonicalize.canonicalizeMutationDiscard e3
    (n, [status e0 e1, status e2 e3, status e3 e4])
  -- The `retypeWith` guard of `certifiedLiterals`.
  let literalDefs := emitLiteralBodies structMeta fnTypes prep.newStructMap
    prep.projConflicts prep.literalRaw prep.literalProc
    (literalIdentityHeads structMeta newtypes)
  let retypeStatus : List (String × String) := literalDefs.map fun (n, e) =>
    let src := (literalSrc.find? (·.1 == n) |>.map (·.2)).getD unknownTExpr
    let t := retypeWith e src
    let s :=
      if toLeanImpExpr t.erase != toLeanImpExpr e then "none"
      else if t.erase == e then "same" else "changed"
    (n, s)
  let get (xs : List (String × String)) (n : String) : String := (xs.lookup n).getD "absent"
  pure <| prep.literalProc.map fun (n, _) =>
    let canon := (canonStatus.lookup n).getD ["absent", "absent", "absent"]
    (n, [get wrapStatus n, get initStatus n] ++ canon ++ [get retypeStatus n])

/-- The export files a command-line path names, each with its crate: the path itself when
    it is a file, `PATH/hax_frontend_export.json` when that file exists, otherwise that file
    in each immediate subdirectory of `PATH`, sorted by name. -/
def exportsOf (path : System.FilePath) : IO (List (String × System.FilePath)) := do
  let crateOf (f : System.FilePath) : String :=
    (f.parent.bind (·.fileName)).getD f.toString
  if ← path.isDir then
    let own := path / "hax_frontend_export.json"
    if ← own.pathExists then
      return [(crateOf own, own)]
    let entries ← path.readDir
    let mut acc : Array (String × System.FilePath) := #[]
    for d in entries do
      let f := d.path / "hax_frontend_export.json"
      if ← f.pathExists then
        acc := acc.push (crateOf f, f)
    return (acc.qsort (fun a b => a.1 < b.1)).toList
  else
    return [(crateOf path, path)]

/-- The command line: the report on standard output. -/
def run (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: certified-checks PATH..."
    return 1
  IO.println ("crate\tfunction\t" ++ "\t".intercalate passNames)
  let mut counts : Array Nat := Array.replicate passNames.length 0
  let mut fns : Nat := 0
  for a in args do
    for (crate, f) in ← exportsOf a do
      let input ← IO.FS.readFile f
      match passRows input with
      | .error msg =>
        IO.println s!"{crate}\t-\terror: {msg.replace "\n" " "}"
      | .ok rows =>
        for (n, ss) in rows do
          fns := fns + 1
          IO.println s!"{crate}\t{n}\t{"\t".intercalate ss}"
          let mut i := 0
          for s in ss do
            if s == "changed" then
              counts := counts.modify i (· + 1)
            i := i + 1
  IO.println s!"# functions: {fns}"
  for (p, c) in passNames.zip counts.toList do
    IO.println s!"# changed by {p}: {c}"
  return 0

end Hax.CertifiedChecks

/-- The entry point of `lake exe certified-checks`. -/
def main (args : List String) : IO UInt32 :=
  Hax.CertifiedChecks.run args

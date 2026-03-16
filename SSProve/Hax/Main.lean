/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.CLI

/-!
# haxpipe CLI — Verified Hax Pipeline

The stable `haxpipe` entry point. Shared infrastructure is in `CLI.lean`.
-/

open SSProve.Hax
open Lean (toJson)

def main (args : List String) : IO UInt32 := do
  let opts := parseArgs args

  if opts.help then
    IO.println helpText
    return 0

  let input ← readInput opts.inputFile

  let (expr, fnTypes, callRetTypes, callSigs, varRefTypes) ←
    if opts.haxFormat && (opts.emitMode == "certified" || opts.emitMode == "debug-meta") then
      parseHaxInputWithTypes input
    else do
      let e ← if opts.haxFormat then parseHaxInput input else parseExpr input
      pure (e, [], [], [], [])

  let structMeta ← if opts.haxFormat && (opts.emitMode == "certified" || opts.emitMode == "debug-meta") then
      parseHaxStructMeta input
    else pure []

  let expr := match opts.filterFns with
    | some fns => filterExpr fns expr
    | none => expr

  let warnings := HaxAdapter.validateExtraction expr
  if !warnings.isEmpty then
    for w in warnings do
      IO.eprintln s!"WARNING: {w}"
    IO.eprintln s!"Total warnings: {warnings.length}"

  let result := if opts.extended then pipelineExt expr else pipeline expr

  match opts.validateFile with
  | some vfile =>
    let expectedInput ← IO.FS.readFile vfile
    let expected ← if opts.haxFormat then parseHaxInput expectedInput else parseExpr expectedInput
    match diffExpr "" result expected with
    | none =>
      IO.println "PASS: Pipeline output matches expected output."
      return 0
    | some diff =>
      IO.eprintln s!"FAIL: {diff}"
      return 1
  | none =>
    IO.eprintln s!"DEBUG: emitMode = '{opts.emitMode}'"
    match opts.emitMode with
    | "json" =>
      IO.println ((toJson result).pretty)
    | "bridge" =>
      let fnNames := extractFnNames expr
      IO.println (toHaxBridgeTemplate opts.name fnNames)
    | "debug-meta" =>
      IO.eprintln s!"DEBUG: entering debug-meta branch"
      let fnDefs := extractFnDefs result
      let defs := if fnDefs.isEmpty then [(opts.name, result)] else fnDefs
      IO.eprintln s!"DEBUG: defs count = {defs.length}"
      let sl : String → Option String := fun n =>
        let passthrough := computeStructPassthrough structMeta defs
        mkStructLookup structMeta passthrough n
      IO.eprintln s!"=== STRUCT META ({structMeta.length} structs) ==="
      for (sname, fields) in structMeta do
        IO.eprintln s!"  struct {sname} -> {sl sname |>.getD "none"}:"
        for (fname, ftag, fty) in fields do
          IO.eprintln s!"    {fname} : tag={ftag}, leanType={fty.toLeanTypeStr sl}"
      IO.eprintln s!"=== CALL SIGS ({callSigs.length} sigs) ==="
      for (name, sig) in callSigs do
        let args := sig.paramTypes.map fun (n, t) => s!"{n}:{t.toLeanTypeStr sl}"
        IO.eprintln s!"  {name}({", ".intercalate args}) -> {sig.retType.toLeanTypeStr sl}"
      IO.eprintln s!"=== CALL RET TYPES ({callRetTypes.length} types) ==="
      for (name, ty) in callRetTypes do
        IO.eprintln s!"  {name} -> {ty.toLeanTypeStr sl}"
    | "certified" =>
      let fnDefs := extractFnDefs result
      let defs := if fnDefs.isEmpty then [(opts.name, result)] else fnDefs
      -- Emit field name collision warnings to stderr
      let collisionWarnings := detectFieldCollisions structMeta
      for w in collisionWarnings do
        IO.eprintln s!"WARNING: {w}"
      IO.println (toLeanCertifiedFile defs opts.name structMeta fnTypes callRetTypes callSigs varRefTypes)
    | _ =>
      IO.println (toLeanDef opts.name result)
    return 0

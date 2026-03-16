/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.CLI

/-!
# haxpipeT CLI — Typed Hax Pipeline

Typed variant of `haxpipe`. Can be iterated on independently.
Changes here or in `PrettyPrintT.lean` (future) won't affect `haxpipe`.

Currently identical to haxpipe. The typed emission will be added here
by replacing `toLeanCertifiedFile` with a typed version.
-/

open SSProve.Hax

def main (args : List String) : IO UInt32 := do
  let opts := parseArgs args
  if opts.help then
    IO.println "haxpipeT: typed hax pipeline (same interface as haxpipe)"
    return 0
  let input ← readInput opts.inputFile
  let (expr, fnTypes, callRetTypes, callSigs, varRefTypes) ←
    if opts.haxFormat && opts.emitMode == "certified" then
      parseHaxInputWithTypes input
    else do
      let e ← if opts.haxFormat then parseHaxInput input else parseExpr input
      pure (e, [], [], [], [])
  let structMeta ← if opts.haxFormat && opts.emitMode == "certified" then
      parseHaxStructMeta input
    else pure []
  let expr := match opts.filterFns with
    | some fns => filterExpr fns expr
    | none => expr
  let result := if opts.extended then pipelineExt expr else pipeline expr
  match opts.emitMode with
  | "certified" =>
    let fnDefs := extractFnDefs result
    let defs := if fnDefs.isEmpty then [(opts.name, result)] else fnDefs
    -- TODO: Replace with typed version that threads struct types
    IO.println (toLeanCertifiedFile defs opts.name structMeta fnTypes callRetTypes callSigs varRefTypes)
  | _ =>
    IO.println (toLeanDef opts.name result)
  return 0

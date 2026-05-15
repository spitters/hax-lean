/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.CLI
import Hax.PrettyPrintT
import Hax.TPipeline

/-!
# haxpipeT CLI — Typed Extraction Pipeline

Uses `parseHaxTExpr` to preserve types from hax JSON at every subexpression,
then routes through `tPipeline` (typed verified pipeline) and `toLeanCertifiedFileTyped`
(type-directed code generation).

## Architecture

```
hax JSON → parseHaxFileWithTExpr → List (name × TExpr)
                                       │
                              ┌────────┘
                              ↓
                    tPipeline (each TExpr)
                              │
                              ↓
              toLeanCertifiedFileTyped → Lean source
```

For `--emit-certified`, the typed path uses TExpr types for:
- Parameter type annotations (from TExpr.ty on param bindings)
- Deps class field signatures (from call-site TExpr.ty)
- No heuristic type recovery needed

Other emit modes (`lean`, `json`, `bridge`) fall back to the **deprecated**
untyped path (`Hax.PrettyPrint.toLeanCertifiedFile`, since 2026-05-14). New
consumers should use `--emit-certified --hax`. See `Hax/PrettyPrint.lean`
module docstring for the removal plan.
-/

-- Intentional calls into the deprecated untyped emitter for the fallback
-- emit modes (`--emit-lean`, `--emit-certified` without `--hax-format`).
-- A runtime warning is emitted on stderr at the call sites below.
set_option linter.deprecated false

open Hax
open Lean (toJson Json)

/-- Parse hax JSON input into typed TExprs.
    Returns (untyped ImpExpr, fnTypes, raw TExprs with hax types, processed TExprs for pipeline). -/
def parseHaxInputTyped (input : String) :
    IO (ImpExpr × List (String × HaxAdapter.FnTypeInfo)
        × List (String × TExpr) × List (String × TExpr)) := do
  let json ← IO.ofExcept (Json.parseVerified input)
  IO.ofExcept (HaxAdapter.parseHaxFileWithTExpr json)

def main (args : List String) : IO UInt32 := do
  let opts := parseArgs args

  if opts.help then
    IO.println helpText
    return 0

  let input ← readInput opts.inputFile

  -- === TYPED PATH: parse into TExpr with full type preservation ===
  let useTypedPath := opts.haxFormat && opts.emitMode == "certified"

  if useTypedPath then
    let (_expr, fnTypes, rawTdefs, procTdefs) ← parseHaxInputTyped input
    let structMeta ← parseHaxStructMeta input

    -- Filter if requested
    let rawTdefs := match opts.filterFns with
      | some fns => rawTdefs.filter fun (p : String × TExpr) =>
          fns.any (fun f => p.1.endsWith f || p.1 == f)
      | none => rawTdefs
    let procTdefs := match opts.filterFns with
      | some fns => procTdefs.filter fun (p : String × TExpr) =>
          fns.any (fun f => p.1.endsWith f || p.1 == f)
      | none => procTdefs

    -- Apply typed pipeline to processed TExprs (for rendering)
    -- `tPipelineWithCFWrap`: applies `tPipeline` then `tWrapMatchArmsCF`
    -- to wrap fall-through match arms with `cfContinue` when sibling arms
    -- have `cfBreak`. The wrap pass is verified (NoReferences-preserving
    -- at the untyped layer; helper-lemma erase commutativity at the
    -- typed layer; see `Hax/Phase/WrapMatchArms.lean` and
    -- `Hax/TPhase/WrapMatchArms.lean`).
    let postPipelineTdefs := procTdefs.map fun (n, te) => (n, tPipelineWithCFWrap te)

    -- Validate via erasure
    let erased := postPipelineTdefs.map fun (n, te) => (n, te.erase)
    let allWarnings := erased.foldl (fun acc (_, e) =>
      acc ++ HaxAdapter.validateExtraction e) ([] : List String)
    if !allWarnings.isEmpty then
      for w in allWarnings do
        IO.eprintln s!"WARNING: {w}"
      IO.eprintln s!"Total warnings: {allWarnings.length}"

    -- Generate typed certified output (rawTdefs for param annotations, postPipelineTdefs for bodies)
    -- rawTdefs has hax types preserved (for deps class + param annotations)
    -- postPipelineTdefs has pipeline-transformed bodies (for rendering)
    IO.println (toLeanCertifiedFileTyped rawTdefs opts.name structMeta fnTypes postPipelineTdefs)
    return 0

  -- === UNTYPED PATH: same as haxpipe (for non-certified emit modes) ===
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
      -- DEPRECATED 2026-05-14: --emit-certified without --hax-format routes
      -- through the untyped pipeline. All production extractions use
      -- `--emit-certified --hax` (typed path). See PrettyPrint.lean module
      -- docstring for removal plan.
      IO.eprintln "WARNING: --emit-certified without --hax-format uses the deprecated untyped pipeline (since 2026-05-14). Add --hax to use the typed path (PrettyPrintT.toLeanCertifiedFileTyped)."
      let fnDefs := extractFnDefs result
      let defs := if fnDefs.isEmpty then [(opts.name, result)] else fnDefs
      IO.println (toLeanCertifiedFile defs opts.name structMeta fnTypes callRetTypes callSigs varRefTypes)
    | _ =>
      -- --emit-lean: surface code only (no ImpExpr literals). Route through
      -- the same module-file emitter as --emit-certified so each Rust fn
      -- becomes its own top-level `def` with proper parameters, instead of
      -- collapsing everything into one nested-let `def`.
      -- DEPRECATED 2026-05-14: --emit-lean is the untyped pipeline.
      -- No production consumer; the typed path (--emit-certified --hax)
      -- supersedes it.
      IO.eprintln "WARNING: --emit-lean uses the deprecated untyped pipeline (since 2026-05-14). Use --emit-certified --hax for production extraction."
      let fnDefs := extractFnDefs result
      let defs := if fnDefs.isEmpty then [(opts.name, result)] else fnDefs
      IO.println (toLeanCertifiedFile defs opts.name structMeta fnTypes
                    callRetTypes callSigs varRefTypes (withImpExprs := false))
    return 0

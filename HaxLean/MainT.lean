/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import HaxLean.CLI
import HaxLean.Secrecy
import HaxLean.PrettyPrintT
import HaxLean.TPipeline
import HaxLean.InlineClosures
import HaxLean.ThreadMutations

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

/-- Keep the first entry for each name, in first-occurrence order.

A hax export lists every function twice over: once as a top-level `Fn` item
and once inside each enclosing `Mod` item, whose sub-item list repeats the
whole module. The adapter walks both, so a function nested `d` modules deep
arrives `d + 1` times. `toLeanCertifiedFileTyped` drops the repeats by name
before rendering, so they contribute nothing to the output; applying the same
rule here keeps them out of the pipeline, the erasure and the validator. -/
def dedupByName {α : Type} (xs : List (String × α)) : List (String × α) :=
  let step (acc : Array (String × α) × List String) (p : String × α) :
      Array (String × α) × List String :=
    if acc.2.contains p.1 then acc else (acc.1.push p, p.1 :: acc.2)
  (xs.foldl step (#[], [])).1.toList

/-- Elapsed milliseconds since `start`, reported on stderr under `label`.
    Returns the current clock so the caller can chain phases. -/
def phaseTick (label : String) (start : Nat) : IO Nat := do
  let now ← IO.monoMsNow
  IO.eprintln s!"TIMING {label}: {now - start} ms"
  return now

def main (args : List String) : IO UInt32 := do
  let opts := parseArgs args

  if opts.help then
    IO.println helpText
    return 0

  let t0 ← IO.monoMsNow
  let input ← readInput opts.inputFile

  -- === TYPED PATH: parse into TExpr with full type preservation ===
  let useTypedPath := opts.haxFormat && opts.emitMode == "certified"

  if useTypedPath then
    let t ← phaseTick "read-input" t0
    -- One JSON parse feeds every consumer below. Tokenizing and parsing a
    -- whole-crate export is the dominant cost of the run, and the input is
    -- immutable, so the parse is hoisted here. The small metadata tables are
    -- derived first; `parseHaxFileWithTExpr` is the last use of `inputJson`,
    -- so the JSON tree is released before the pipeline runs.
    let inputJson ← IO.ofExcept (Json.parseVerified input)
    let t ← phaseTick "json-parse" t
    let structMeta := structMetaOfJson inputJson
    let newtypes := HaxAdapter.buildNewtypeMap inputJson
    let enumMeta := HaxAdapter.parseEnumDefsFromJson inputJson
    let aliasMeta := HaxAdapter.parseTypeAliasDefsFromJson inputJson
    IO.eprintln s!"INFO structs={structMeta.length} newtypes={newtypes.length} enums={enumMeta.length} aliases={aliasMeta.length}"
    let t ← phaseTick "metadata" t
    let (_expr, fnTypes, rawTdefs, procTdefs) ←
      IO.ofExcept (HaxAdapter.parseHaxFileWithTExpr inputJson)
    let fnTypes := dedupByName fnTypes
    let rawTdefs := dedupByName rawTdefs
    let procTdefs := dedupByName procTdefs
    IO.eprintln s!"INFO defs={procTdefs.length}"
    let t ← phaseTick "adapter-to-texpr" t

    -- Filter if requested
    let rawTdefs := match opts.filterFns with
      | some fns => rawTdefs.filter fun (p : String × TExpr) =>
          fns.any (fun f => p.1.endsWith f || p.1 == f)
      | none => rawTdefs
    let procTdefs := match opts.filterFns with
      | some fns => procTdefs.filter fun (p : String × TExpr) =>
          fns.any (fun f => p.1.endsWith f || p.1 == f)
      | none => procTdefs

    -- Apply typed pipeline to processed TExprs (for rendering).
    -- `tPipelineFull` composes:
    --   tPipeline → tWrapMatchArmsCF → tElideToNamedProj newtypes
    -- The newtype-elision pass rewrites `.app ".0" [x]` to `.namedProj T x`
    -- when `x : T` is a newtype struct, so the renderer can emit a
    -- type-aware unwrap `«T.0» x` instead of the polymorphic-identity
    -- `«.0»`. Pass is verified (`tElideToNamedProj_erase`).
    -- Pre-pipeline normalizations: turn each `&mut` write-back into an
    -- assignment (`tRebindMutCalls` at the call, `tReturnMutParam` at the
    -- definition, both reading the signature table below), lower `Fn::call` of
    -- let-bound `.lam` closures to direct applications, and thread mutations
    -- across `if`-statement joins. The call rewrite runs before the definition
    -- rewrite: a body whose own tail is a write-back call has to be an
    -- assignment before `tReplaceTail` reaches it, or the call is dropped as a
    -- pure value.
    let writeFns := mutWriteFns fnTypes procTdefs
    let writers := mutWriteTable writeFns
    let writeParams := mutWriteParams writeFns
    IO.eprintln s!"INFO mut-writeback-fns={writers.length}/{(mutWriteCandidates fnTypes).length}"
    let postPipelineTdefs := procTdefs.map fun (n, te) =>
      let te := tReturnMutParam (writeParams.lookup n) (tRebindMutCalls writers te)
      (n, tPipelineFull newtypes (tThreadMut true (tLowerClosureCalls [] te)))
    IO.eprintln s!"INFO pipeline-defs={postPipelineTdefs.length}"
    let t ← phaseTick "tPipelineFull" t

    -- Validate via erasure
    let erased := postPipelineTdefs.map fun (n, te) => (n, te.erase)
    let allWarnings := erased.foldl (fun acc (_, e) =>
      acc ++ HaxAdapter.validateExtraction e) ([] : List String)
    IO.eprintln s!"INFO warnings={allWarnings.length}"
    let t ← phaseTick "erase-validate" t
    if !allWarnings.isEmpty then
      for w in allWarnings do
        IO.eprintln s!"WARNING: {w}"
      IO.eprintln s!"Total warnings: {allWarnings.length}"

    -- Generate typed certified output (rawTdefs for param annotations, postPipelineTdefs for bodies)
    -- rawTdefs has hax types preserved (for deps class + param annotations)
    -- postPipelineTdefs has pipeline-transformed bodies (for rendering)
    -- IF/CT transfer (phase 2): emit the source-declared secret bindings as an
    -- additive `<name>_secrecy` def, recognized from secret-integer newtypes
    -- (`HaxLean/Secrecy.lean`). The source is the per-function parameter types
    -- (`FnTypeInfo.paramTypes`, pre-newtype-unwrap), which carry a secret `U8`
    -- (or a `[U8; n]`/`&[U8]` buffer of them) as an `.adt "U8"`. Consumed by
    -- `SourceSecrecy` on the CatCrypt side; empty until a kernel adopts the
    -- secret-integer discipline. Additive, so it does not disturb the existing
    -- `_haxpipe.lean` format.
    let paramBindings := fnTypes.flatMap (fun p => p.2.paramTypes)
    let secretNames := (secrecyOfBindings paramBindings).eraseDups
    let secrecyLit := "[" ++ ", ".intercalate (secretNames.map (fun s => "\"" ++ s ++ "\"")) ++ "]"
    let secrecyDef := s!"\n/-- Source-declared secret bindings (IF/CT transfer): binding names whose Rust\ntype is a secret integer. Consumed by `SourceSecrecy` on the CatCrypt side. -/\ndef {opts.name}_secrecy : List String := {secrecyLit}\n"
    let rendered :=
      toLeanCertifiedFileTyped rawTdefs opts.name structMeta fnTypes postPipelineTdefs
        newtypes enumMeta aliasMeta ++ secrecyDef
    IO.eprintln s!"INFO output-bytes={rendered.length}"
    let _ ← phaseTick "render" t
    IO.println rendered
    let _ ← phaseTick "total" t0
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
        mkStructLookup structMeta passthrough (clashSet := []) n
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

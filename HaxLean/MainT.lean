/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.CLI
public import HaxLean.Secrecy
public import HaxLean.PrettyPrintT
public import HaxLean.TPipeline
public import HaxLean.InlineClosures
public import HaxLean.ThreadMutations

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

@[expose] public section

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

The export is read through `parseHaxExport`, which lists each item once, but
two items can still define the same name. `toLeanCertifiedFileTyped` keeps the
first definition of each name before rendering; applying the same rule here
keeps the later ones out of the pipeline, the erasure and the validator. -/
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
    let inputJson ← IO.ofExcept (parseHaxExport input)
    let t ← phaseTick "json-parse" t
    -- `--emit-classes`: keep the type parameters of both exports as named
    -- type variables and plan the classes, instances and generic binders
    -- (`Hax.ClassEmit`). Without the flag the plan is empty and nothing below
    -- consults it.
    -- The predicate items of hax-lib contracts are never ordinary definitions
    -- (`ContractEmit.dropContractItems`); under `--emit-contracts` the
    -- contracts are read from the exports before the items are dropped, and
    -- the lemma functions are dropped too.
    let (inputJson, classHooks, contractSrcs) ← match opts.emitClasses with
      | none =>
        pure (ContractEmit.dropContractItems opts.emitContracts inputJson,
          ({} : ClassEmit.ClassHooks),
          if opts.emitContracts then [inputJson] else [])
      | some traitFile => do
        let traitJson ← IO.ofExcept (parseHaxExport (← IO.FS.readFile traitFile))
        let inputKept := ClassEmit.keepTypeParams inputJson
        let traitKept := ClassEmit.keepTypeParams traitJson
        let inputJson := ContractEmit.dropContractItems opts.emitContracts inputKept
        let hooks := ClassEmit.plan
          (ContractEmit.dropContractItems opts.emitContracts traitKept) inputJson
        IO.eprintln s!"INFO classes={hooks.traits.length} class-items={hooks.classItemNames.length} generic-fns={hooks.genericFns.length} generic-structs={hooks.genericStructs.length} instances={hooks.instances.length}"
        pure (inputJson, hooks, if opts.emitContracts then [inputKept, traitKept] else [])
    let classMode := classHooks.enabled
    -- The naming context of the contracts' calls and definitions, taken here
    -- so the export need not outlive the parse.
    let contractNaming : List String × HaxAdapter.LocalCrate :=
      if contractSrcs.isEmpty then ([], {})
      else (HaxAdapter.fnNameCollisions inputJson, HaxAdapter.localCrateOfExport inputJson)
    let structMeta := structMetaOfJson inputJson
    let newtypes := HaxAdapter.buildNewtypeMap inputJson
    let enumMeta := HaxAdapter.parseEnumDefsFromJson inputJson
    let aliasMeta := HaxAdapter.parseTypeAliasDefsFromJson inputJson
    IO.eprintln s!"INFO structs={structMeta.length} newtypes={newtypes.length} enums={enumMeta.length} aliases={aliasMeta.length}"
    let t ← phaseTick "metadata" t
    -- Struct-field layout for the assignment lowering and the `&mut`
    -- write-back rewrite: struct name → field names in declaration order.
    let structFields : StructFieldNames :=
      structMeta.map fun (sname, fields) => (sname, fields.map (·.1))
    let (_expr, fnTypes, rawTdefs, procTdefs) ←
      IO.ofExcept (HaxAdapter.parseHaxFileWithTExpr inputJson structFields
        (traitImplConsts := classMode) (nominalKrates := opts.nominalKrates))
    let fnTypes := dedupByName fnTypes
    let rawTdefs := dedupByName rawTdefs
    let procTdefs := dedupByName procTdefs
    -- A `Deps` field has one type, so every site that uses the name has to
    -- agree on it. Resolving the crate's trait `impl`s emits their method
    -- bodies at the concrete self type, and those bodies read the trait items
    -- of a further `impl` that stays opaque; where the crate is also generic
    -- over the trait, the same names are used at a type parameter and the two
    -- readings do not print as one type. The export is then read with every
    -- trait `impl` opaque, which is uniform.
    let traitImplNames :=
      ((HaxAdapter.buildTraitImplMethodMap inputJson).map (·.2.2)).eraseDups
    -- Under `--emit-classes` the names a generic function calls through a trait
    -- bound are class items rather than `Deps` fields, so the conflict does
    -- not arise and the `impl`s stay resolved.
    let depTypeConflicts :=
      if traitImplNames.isEmpty || classMode then []
      else
        let erased := procTdefs.map fun (n, te) => (n, te.erase)
        let sl := mkStructLookup structMeta (computeStructPassthrough structMeta erased)
        -- The `Deps` names are the unqualified heads (`--nominal-crates`).
        let raw := rawTdefs.map fun (n, te) =>
          (n, HaxAdapter.tUnqualifyNominalHeads opts.nominalKrates te)
        traitImplDepTypeConflicts raw traitImplNames sl (newtypes.map (·.1))
    let (fnTypes, rawTdefs, procTdefs) ←
      if depTypeConflicts.isEmpty then pure (fnTypes, rawTdefs, procTdefs)
      else do
        IO.eprintln s!"INFO trait-impl-opaque: the `Deps` names {depTypeConflicts} are used at two types; every trait `impl` of the crate keeps opaque methods"
        let (_expr, fnTypes, rawTdefs, procTdefs) ←
          IO.ofExcept (HaxAdapter.parseHaxFileWithTExpr inputJson structFields
            (resolveTraitImpls := false) (nominalKrates := opts.nominalKrates))
        pure (dedupByName fnTypes, dedupByName rawTdefs, dedupByName procTdefs)
    IO.eprintln s!"INFO defs={procTdefs.length} trait-impl-defs={traitImplNames.length} dep-type-conflicts={depTypeConflicts.length}"
    let t ← phaseTick "adapter-to-texpr" t

    -- Filter if requested. Under `--emit-contracts` the filter also keeps the
    -- definitions the selected contracts name (`ContractEmit.referencedNames`).
    let selected : String → Bool := fun n => match opts.filterFns with
      | some fns => fns.any (fun f => n.endsWith f || n == f)
      | none => true
    let contractRefs : List String :=
      if contractSrcs.isEmpty || opts.filterFns.isNone then []
      else ContractEmit.referencedNames contractSrcs contractNaming.1 contractNaming.2 selected
    let rawTdefs := match opts.filterFns with
      | some _ => rawTdefs.filter fun (p : String × TExpr) =>
          selected p.1 || contractRefs.contains p.1
      | none => rawTdefs
    let procTdefs := match opts.filterFns with
      | some _ => procTdefs.filter fun (p : String × TExpr) =>
          selected p.1 || contractRefs.contains p.1
      | none => procTdefs
    -- Under a filter, an instance whose fields name a definition the filter
    -- left out is left out too.
    let classHooks := match opts.filterFns with
      | some _ =>
        let kept := rawTdefs.map (·.1)
        { classHooks with instances := classHooks.instances.filter fun inst =>
            inst.fields.all fun (_, d) => kept.contains d }
      | none => classHooks

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
    -- Calls outside the write-back fragment are first brought into it
    -- (`tHoistMutCalls`, `tQualifyWritebackFields`, `externalWriteTable`); see
    -- the normalisation section of `ThreadMutations`.
    let procTdefs := procTdefs.map fun (n, te) =>
      (n, tQualifyWritebackFields structFields (tHoistMutCalls fnTypes te))
    let extWriters := externalWriteTable procTdefs
    let procTdefs := procTdefs.map fun (n, te) => (n, tRetypeExtWriters extWriters te)
    -- A parameter written only through a builtin write (`copy_from_slice`
    -- into `okm[a..b]`) makes its function a write-back function too.
    let writeFns :=
      mutWriteFnsExt structFields fnTypes procTdefs (extWriters ++ builtinWriteTable)
    -- The builtin and external tables are appended to the call-site rebind
    -- table only, not to `writeReturns`: `tReturnMutParams` rewrites a callee
    -- to return its written parameters, and these callees have no body in the
    -- export to rewrite.
    let writers := mutWriteTable writeFns ++ builtinWriteTable ++ extWriters
    let tupWriters := mutWriteTupleTable writeFns
    let writeReturns := mutWriteReturns writeFns
    IO.eprintln s!"INFO mut-writeback-fns={writers.length + tupWriters.length}/{(mutWriteCandidates fnTypes).length + builtinWriteTable.length}"
    -- A call through `&mut` that the rewrite leaves as a plain call keeps its
    -- effect inside the callee: the emitted surface would ignore the
    -- computation. Refuse to emit unless asked to.
    let dropped := procTdefs.flatMap fun (n, te) =>
      (tDroppedMutCalls fnTypes structFields writers tupWriters te).map fun d => (n, d)
    for (n, (f, ps)) in dropped do
      IO.eprintln s!"ERROR dropped-writeback: `{n}` calls `{f}` through `&mut` (parameter positions {ps}) outside the write-back rewrite; the effect of the call does not reach the caller. The rewrite covers a callee with one `&mut` parameter and result `()` applied to a variable, a field place or a slice range, and a callee with several `&mut` parameters or a value result applied to variables, called in `let`, assignment or statement position."
    IO.eprintln s!"INFO dropped-writeback-calls={dropped.length}"
    if !dropped.isEmpty && !opts.allowDroppedWriteback then
      IO.eprintln "haxpipeT: no output; pass --allow-dropped-writeback to emit anyway"
      return 1
    let postPipelineTdefs := procTdefs.map fun (n, te) =>
      let ret := (writeReturns.lookup n).getD ([], false)
      let te := tReturnMutParams ret.1 ret.2 (tReturnMutParamsAtReturns ret.1 ret.2
        (tRebindMutCalls structFields writers tupWriters te))
      (n, tUnqualifyFieldHeads
        (tPipelineFull newtypes (tThreadMut true (tLowerClosureCalls [] te))))
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
    -- The per-function secrecy of the crate (`HaxLean/Secrecy.lean`): for each
    -- function with a parameter or a result holding a secret value, its parameters
    -- with their secrecy, read off the parameter types before newtype unwrapping
    -- (`FnTypeInfo.paramTypes`) and the field types of the crate's structs.
    let fieldTypes : FieldTypes :=
      structMeta.map fun (sname, fields) => (sname, fields.map fun (f, _, ty) => (f, ty))
    let fnSec := crateSecrecy fieldTypes fnTypes
    let secrecyLit := "[" ++ ",\n    ".intercalate (fnSec.map FnSecrecy.toLean) ++ "]"
    let secrecyDef := s!"\n/-- The per-function secrecy of the crate: each function with a parameter or a\nresult holding a secret value, with the secrecy of each parameter and of the result.\nA function not listed has no secret parameter and a public result. -/\ndef {opts.name}_fnSecrecy : List Hax.FnSecrecy :=\n  {secrecyLit}\n"
    -- The crate the export was taken from: the directory holding
    -- `hax_frontend_export.json`, which is the crate root `cargo hax json` ran
    -- in. Empty when the export arrives on stdin, and then the module docstring
    -- names no crate.
    let crateName := match opts.inputFile with
      | some p => ((System.FilePath.mk p).parent.bind (·.fileName)).getD ""
      | none => ""
    -- `--emit-contracts`: the contracts of the emitted definitions, and the
    -- contract fields of the classes and instances. A clause outside the
    -- predicate language stops the run.
    let (contractPlan, classHooks) ←
      if contractSrcs.isEmpty then pure (({} : ContractEmit.Plan), classHooks)
      else
        -- The type invariants of the contracts are read through the crate's
        -- newtypes and struct field types.
        let tyEnv : ContractEmit.TyEnv :=
          { newtypes := newtypes,
            structs := structMeta.map fun (s, fs) => (s, fs.map (·.2.2)) }
        match ContractEmit.build contractSrcs contractNaming.1 contractNaming.2
            (rawTdefs.map (·.1)) selected writeReturns classHooks tyEnv with
        | .ok r => pure r
        | .error errs => do
          for e in errs do
            IO.eprintln s!"ERROR contract: {e}"
          IO.eprintln "haxpipeT: no output; a contract clause is outside the predicate language"
          return 1
    IO.eprintln s!"INFO contracts={contractPlan.fns.length} lemmas={contractPlan.lemmas.length} contract-traits={classHooks.contractMethods.length}"
    let rendered :=
      toLeanCertifiedFileTyped rawTdefs opts.name structMeta fnTypes postPipelineTdefs
        newtypes enumMeta aliasMeta (mutWriteTupleReturns writeFns)
        (crateName := crateName) (emitLowCT := opts.emitLowCT)
        (classHooks := classHooks) (contracts := contractPlan)
        (nominalKrates := opts.nominalKrates) ++ secrecyDef
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

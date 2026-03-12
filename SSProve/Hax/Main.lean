/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.Json
import SSProve.Hax.HaxAdapter
import SSProve.Hax.PrettyPrint
import SSProve.Hax.Pipeline

/-!
# haxpipe CLI — Verified Hax Pipeline

A command-line tool that reads hax AST (JSON), runs the verified 5-phase
pipeline, and outputs Lean 4 source code or transformed JSON.

## Usage

```
haxpipe [OPTIONS] [INPUT_FILE]

Options:
  --emit-lean     Output Lean 4 source code (default)
  --emit-json     Output transformed AST as JSON
  --validate FILE Compare pipeline output with expected output from FILE
  --extended      Use the 5-phase pipeline (with ExplicitMonadic)
  --hax           Input is in hax's native JSON format (Decorated<ExprKind>)
  --help          Show this help message

If INPUT_FILE is omitted or "-", reads from stdin.
```
-/

open SSProve.Hax
open Lean (Json ToJson FromJson toJson fromJson?)

/-- Read input from file or stdin. -/
def readInput (path : Option String) : IO String := do
  match path with
  | none | some "-" => do
    let stdin ← IO.getStdin
    stdin.readToEnd
  | some p => IO.FS.readFile p

/-- Parse JSON string into ImpExpr (our native format). -/
def parseExpr (input : String) : IO ImpExpr := do
  let json ← IO.ofExcept (Json.parse input)
  IO.ofExcept (fromJson? json : Except String ImpExpr)

/-- Parse JSON string from hax's native format into ImpExpr.
    Handles both the full `hax_frontend_export.json` (array of items)
    and a single `Decorated<ExprKind>` (one expression). -/
def parseHaxInput (input : String) : IO ImpExpr := do
  let json ← IO.ofExcept (Json.parse input)
  IO.ofExcept (HaxAdapter.parseHaxFile json)

/-- Command-line options. -/
structure Options where
  emitMode : String := "lean"  -- "lean" | "json"
  inputFile : Option String := none
  validateFile : Option String := none
  extended : Bool := false
  haxFormat : Bool := false
  help : Bool := false
  name : String := "result"
  filterFns : Option (List String) := none  -- only include these functions

/-- Parse command-line arguments. -/
def parseArgs (args : List String) : Options :=
  go args {}
where
  go : List String → Options → Options
    | [], opts => opts
    | "--emit-lean" :: rest, opts => go rest { opts with emitMode := "lean" }
    | "--emit-json" :: rest, opts => go rest { opts with emitMode := "json" }
    | "--emit-bridge" :: rest, opts => go rest { opts with emitMode := "bridge" }
    | "--emit-certified" :: rest, opts => go rest { opts with emitMode := "certified" }
    | "--validate" :: file :: rest, opts =>
      go rest { opts with validateFile := some file }
    | "--extended" :: rest, opts => go rest { opts with extended := true }
    | "--hax" :: rest, opts => go rest { opts with haxFormat := true }
    | "--help" :: _, opts => { opts with help := true }
    | "--name" :: n :: rest, opts => go rest { opts with name := n }
    | "--filter" :: fns :: rest, opts =>
      go rest { opts with filterFns := some (fns.splitOn ",") }
    | arg :: rest, opts =>
      if arg.startsWith "--" then go rest opts  -- skip unknown flags
      else go rest { opts with inputFile := some arg }

def helpText : String :=
"haxpipe — Verified Hax Pipeline (Lean 4)

USAGE:
  haxpipe [OPTIONS] [INPUT_FILE]

OPTIONS:
  --emit-lean       Output Lean 4 source code (default)
  --emit-json       Output transformed AST as JSON
  --emit-bridge     Output HaxBridge template for SSProve
  --validate FILE   Compare pipeline output with expected output from FILE
  --extended        Use 5-phase pipeline (with ExplicitMonadic)
  --hax             Input is in hax's native JSON format (Decorated<ExprKind>)
  --name NAME       Name for the generated definition (default: result)
  --filter FN,FN    Only include matching functions (comma-separated)
  --help            Show this help message

INPUT:
  JSON-encoded ImpExpr (default) or hax Decorated<ExprKind> (with --hax).
  Reads from stdin if no file specified (or \"-\").

EXAMPLES:
  echo '{\"var\": \"x\"}' | haxpipe
  haxpipe --emit-json input.json
  haxpipe --validate expected.json input.json
  haxpipe --extended --name my_fn input.json
  haxpipe --hax hax_dump.json
"

/-- Compare two ImpExprs structurally and report first difference. -/
partial def diffExpr (path : String) (e1 e2 : ImpExpr) : Option String :=
  if e1 == e2 then none
  else
    let j1 := toJson e1
    let j2 := toJson e2
    some s!"Mismatch at {path}:\n  pipeline: {j1.pretty}\n  expected: {j2.pretty}"

/-- Extract top-level let-binding names from an expression. -/
def extractFnNames : ImpExpr → List String
  | .letBind n _ body => n :: extractFnNames body
  | .seq e1 e2 => extractFnNames e1 ++ extractFnNames e2
  | _ => []

/-- Extract top-level let-binding (name, value) pairs from an expression. -/
def extractFnDefs : ImpExpr → List (String × ImpExpr)
  | .letBind n val body => (n, val) :: extractFnDefs body
  | .seq e1 e2 => extractFnDefs e1 ++ extractFnDefs e2
  | _ => []

/-- Filter a top-level expression to only include let-bindings whose
    name matches the filter list. Other expression forms pass through unchanged. -/
def filterExpr (fns : List String) : ImpExpr → ImpExpr
  | .letBind n val body =>
    if fns.any (fun f => n.endsWith f || n == f) then
      .letBind n val (filterExpr fns body)
    else filterExpr fns body
  | .seq e1 e2 => .seq (filterExpr fns e1) (filterExpr fns e2)
  | e => e

def main (args : List String) : IO UInt32 := do
  let opts := parseArgs args

  if opts.help then
    IO.println helpText
    return 0

  -- Read and parse input
  let input ← readInput opts.inputFile
  let expr ← if opts.haxFormat then parseHaxInput input else parseExpr input

  -- Apply function filter if specified
  let expr := match opts.filterFns with
    | some fns => filterExpr fns expr
    | none => expr

  -- Run extraction validation
  let warnings := HaxAdapter.validateExtraction expr
  if !warnings.isEmpty then
    for w in warnings do
      IO.eprintln s!"WARNING: {w}"
    IO.eprintln s!"Total warnings: {warnings.length}"

  -- Run the verified pipeline
  let result := if opts.extended then pipelineExt expr else pipeline expr

  -- Handle output mode
  match opts.validateFile with
  | some vfile =>
    -- Validation mode: compare with expected output
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
    match opts.emitMode with
    | "json" =>
      IO.println ((toJson result).pretty)
    | "bridge" =>
      let fnNames := extractFnNames expr
      IO.println (toHaxBridgeTemplate opts.name fnNames)
    | "certified" =>
      -- Extract individual function definitions for certified output
      let fnDefs := extractFnDefs result
      let defs := if fnDefs.isEmpty then [(opts.name, result)] else fnDefs
      IO.println (toLeanCertifiedFile defs opts.name)
    | _ =>
      IO.println (toLeanDef opts.name result)
    return 0

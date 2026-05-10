/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr
import Hax.PrettyPrint
import Hax.Pipeline
import Hax.HaxAdapter

/-!
# Typed Pretty-Printer for TExpr

Uses the type annotations preserved by `parseHaxTExpr` to make all type
decisions, replacing ~500 lines of heuristic type recovery in `PrettyPrint.lean`.

## Architecture

```
TExpr ─[tPipeline]→ TExpr ─[toLeanCertifiedFileTyped]→ Lean source
                                │
                     uses e.ty for:
                     - parameter annotations
                     - deps class signatures
                     - cast function selection
                     - struct projection disambiguation
```

The actual expression rendering delegates to `toLean` (via `TExpr.erase`),
since the rendering logic for folds, control flow, etc. is unchanged.
Only the _type decisions_ change: they come from `TExpr.ty` instead of
heuristic analysis.
-/

namespace Hax

/-! ## TExpr Type Utilities -/

/-- Collect all app calls in a TExpr: (functionName, argCount, argTypes, returnType). -/
private partial def collectTAppCalls : TExpr → List (String × Nat × List ImpType × ImpType)
  | .mk (.app f args) ty =>
    let argTypes := args.map (·.ty)
    (f, args.length, argTypes, ty) :: args.foldl (fun acc a => acc ++ collectTAppCalls a) []
  | .mk (.letBind _ v body) _ => collectTAppCalls v ++ collectTAppCalls body
  | .mk (.seq e1 e2) _ => collectTAppCalls e1 ++ collectTAppCalls e2
  | .mk (.ifThenElse c t e) _ =>
    collectTAppCalls c ++ collectTAppCalls t ++ collectTAppCalls e
  | .mk (.tuple elems) _ => elems.foldl (fun acc e => acc ++ collectTAppCalls e) []
  | .mk (.proj e _) _ => collectTAppCalls e
  | .mk (.match_ scrut arms) _ =>
    collectTAppCalls scrut ++ arms.foldl (fun acc (_, b) => acc ++ collectTAppCalls b) []
  | .mk (.forLoop _ lo hi body) _ | .mk (.forLoopRev _ lo hi body) _
  | .mk (.forFold _ lo hi body) _ | .mk (.forFoldRev _ lo hi body) _
  | .mk (.forFoldReturn _ lo hi body) _ | .mk (.forFoldRevReturn _ lo hi body) _ =>
    collectTAppCalls lo ++ collectTAppCalls hi ++ collectTAppCalls body
  | .mk (.whileLoop c body) _ | .mk (.whileFold c body) _ | .mk (.whileFoldReturn c body) _ =>
    collectTAppCalls c ++ collectTAppCalls body
  | .mk (.borrow e) _ | .mk (.deref e) _ | .mk (.assign _ e) _
  | .mk (.earlyReturn e) _ | .mk (.questionMark e) _
  | .mk (.cfBreak e) _ | .mk (.cfContinue e) _ | .mk (.cfBreakContinue e) _ =>
    collectTAppCalls e
  | .mk (.break_ (some e)) _ => collectTAppCalls e
  | _ => []

/-- Collect free variable references in a TExpr with their types. -/
partial def collectTFreeVars (bound : List String := []) :
    TExpr → List (String × ImpType)
  | .mk (.var n) ty => if bound.contains n then [] else [(n, ty)]
  | .mk (.app _ args) _ => args.foldl (fun acc a => acc ++ collectTFreeVars bound a) []
  | .mk (.letBind n (.mk (.var v) _) body) _ =>
    if n == v then collectTFreeVars (n :: bound) body
    else (if bound.contains v then [] else [(v, .unknown)]) ++ collectTFreeVars (n :: bound) body
  | .mk (.letBind n v body) _ =>
    collectTFreeVars bound v ++ collectTFreeVars (n :: bound) body
  | .mk (.seq a b) _ => collectTFreeVars bound a ++ collectTFreeVars bound b
  | .mk (.ifThenElse c t e) _ =>
    collectTFreeVars bound c ++ collectTFreeVars bound t ++ collectTFreeVars bound e
  | .mk (.tuple es) _ => es.foldl (fun acc e => acc ++ collectTFreeVars bound e) []
  | .mk (.proj e _) _ => collectTFreeVars bound e
  | .mk (.match_ scrut arms) _ =>
    let allVarPats := arms.all fun (p, _) => match p with
      | .varPat _ => true | .wildcard => true | _ => false
    let patFreeVars := if allVarPats then
      arms.filterMap fun (p, _) => match p with
        | .varPat n => if bound.contains n then none else some (n, ImpType.unknown) | _ => none
    else []
    collectTFreeVars bound scrut ++ patFreeVars ++
    arms.foldl (fun acc (_, b) => acc ++ collectTFreeVars bound b) []
  | .mk (.forLoop _ lo hi body) _ | .mk (.forLoopRev _ lo hi body) _
  | .mk (.forFold _ lo hi body) _ | .mk (.forFoldRev _ lo hi body) _
  | .mk (.forFoldReturn _ lo hi body) _ | .mk (.forFoldRevReturn _ lo hi body) _ =>
    collectTFreeVars bound lo ++ collectTFreeVars bound hi ++ collectTFreeVars bound body
  | .mk (.whileLoop c body) _
  | .mk (.whileFold c body) _ | .mk (.whileFoldReturn c body) _ =>
    collectTFreeVars bound c ++ collectTFreeVars bound body
  | .mk (.borrow e) _ | .mk (.deref e) _
  | .mk (.earlyReturn e) _ | .mk (.questionMark e) _
  | .mk (.cfBreak e) _ | .mk (.cfContinue e) _ | .mk (.cfBreakContinue e) _ =>
    collectTFreeVars bound e
  | .mk (.assign _ rhs) _ => collectTFreeVars bound rhs
  | .mk (.break_ (some e)) _ => collectTFreeVars bound e
  | _ => []

/-- Extract leading identity let-bindings (let x := x) from a TExpr as parameters
    with their types. -/
private def extractTParams : TExpr → List (String × ImpType) × TExpr
  | .mk (.letBind n (.mk (.var v) ty) body) outerTy =>
    if n == v then
      let (ps, rest) := extractTParams body
      ((n, ty) :: ps, rest)
    else ([], .mk (.letBind n (.mk (.var v) ty) body) outerTy)
  | e => ([], e)

/-! ## Typed Deps Class Generation -/

/-- Best-effort merge of two ImpTypes: prefer non-unknown.
    When both are known, prefer the first. -/
private def mergeType (a b : ImpType) : ImpType :=
  if a.isUnknown then b else a

/-- Convert an ImpType to Lean type string for the deps class.
    Uses structLookup for ADT resolution.
    Unknown/Unit map to "Array Int" to match the untyped pipeline default. -/
private def depTypeStr (ty : ImpType) (sl : String → Option String) : String :=
  match ty with
  | .unknown => "Array Int"  -- no type info; match untyped default
  | .unit => "Array Int"     -- side-effect functions; match untyped default
  | _ => ty.toLeanTypeStrSurface sl

set_option linter.unusedVariables false in
/-- Generate the deps class and struct definitions using typed information from TExprs.
    This replaces `generatePreamble` by using types directly from the TExpr tree
    instead of ~300 lines of heuristic detection.
    `processedDefs`: post-pipeline ImpExpr defs (with qualified projections etc.)
    for structural analysis. If empty, erases `tdefs`. -/
def generatePreambleTyped (tdefs : List (String × TExpr))
    (moduleName : String) (structMeta : StructMeta := [])
    (fnTypes : List (String × HaxAdapter.FnTypeInfo) := [])
    (processedDefs : List (String × ImpExpr) := [])
    : String × List (String × String) :=
  -- Use processed defs for structural analysis (qualified projections etc.)
  let defs := if processedDefs.isEmpty then tdefs.map fun (n, te) => (n, te.erase) else processedDefs
  let definedNames := defs.map (·.1)
  let structNames := structMeta.map (·.1)
  let structIsPassthrough := computeStructPassthrough structMeta defs
  let structLookup := mkStructLookup structMeta structIsPassthrough

  -- App names from processed defs (has qualified projections)
  let allCalls := defs.foldl (fun acc (_, e) => acc ++ collectAppCalls e) []
  let allAppNames := allCalls.map (·.1) |>.eraseDups

  -- Typed call info from raw TExprs (for deps class type annotations)
  let allTCalls := tdefs.foldl (fun acc (_, te) => acc ++ collectTAppCalls te) []

  -- Free variables from processed defs (structural analysis)
  let allFreeVars := defs.foldl (fun acc (fname, e) =>
    acc ++ collectFreeVars [fname] e) ([] : List String)
  let freeVarDeps := allFreeVars.eraseDups.filter fun v =>
    !definedNames.contains v &&
    !structNames.contains v && !isFieldProjection v &&
    !allAppNames.contains v

  -- Typed free var info from TExprs (for type annotations in deps class)
  let allTFreeVars := tdefs.foldl (fun acc (fname, te) =>
    acc ++ collectTFreeVars [fname] te) ([] : List (String × ImpType))
  let allTFreeVarsDedup := allTFreeVars.foldl (fun (acc : List (String × ImpType)) (n, ty) =>
    if acc.any (·.1 == n) then acc else acc ++ [(n, ty)]) []

  -- All dependency names (function calls + free variables)
  let allNamesWithVars := (allAppNames ++ freeVarDeps).eraseDups
  let deps := allNamesWithVars.filter fun f =>
    !definedNames.contains f &&
    !structNames.contains f && !isFieldProjection f &&
    (!isAlwaysBuiltin f || freeVarDeps.contains f)

  -- === Generate struct definitions ===
  -- Reuse existing PrettyPrint struct generation (it's structural, not heuristic)
  let allCalls := defs.foldl (fun acc (_, e) => acc ++ collectAppCalls e) []
  let sortedStructMeta := structMeta.toArray.qsort (fun a b => a.2.length > b.2.length) |>.toList
  let (structDefs, _, projConflicts) := sortedStructMeta.foldl
    (fun (acc, emittedProjs, conflicts) (sname, fields) =>
      if fields.isEmpty then (acc, emittedProjs, conflicts)
      else
        let isUsed := allAppNames.contains sname
        let isPassthrough := structIsPassthrough.any fun (n, pt) => n == sname && pt
        let tupleT := structTupleType structMeta fields structLookup
        let projectionsUsed := fields.any fun (fname, _, _) =>
          allAppNames.contains s!".{fname}" || allAppNames.contains s!"{sname}.{fname}"
        let ctorDefs := if isUsed || projectionsUsed then
          if isPassthrough then
            let paramDecls := fields.map fun (fname, ftag, fty) =>
              let leanType := typeTagToLean structMeta ftag fty structLookup
              s!"({sanitizeName fname} : {leanType})"
            let paramStr := " ".intercalate paramDecls
            let arrayField := (fields.find? fun (_, ftag, _) => ftag != "int").map (·.1)
            let retField := sanitizeName (arrayField.getD fields.head!.1)
            [s!"/-- Struct constructor (pass-through, auto-generated). -/\ndef {sanitizeName sname} {paramStr} : Array Int := {retField}"]
          else
            let paramDecls := fields.map fun (fname, ftag, fty) =>
              let leanType := typeTagToLean structMeta ftag fty structLookup
              s!"({sanitizeName fname} : {leanType})"
            let paramStr := " ".intercalate paramDecls
            let tupleStr := ", ".intercalate (fields.map fun (fname, _, _) => sanitizeName fname)
            let ctorDef := if fields.length == 1 then
                s!"def {sanitizeName sname} {paramStr} : {tupleT} := {sanitizeName fields.head!.1}"
              else
                s!"def {sanitizeName sname} {paramStr} : {tupleT} := ({tupleStr})"
            [s!"/-- Struct constructor + projections (auto-generated from Rust struct). -/\n{ctorDef}"]
        else []
        let (projDefs, emittedProjs') := (fields.zip (List.range fields.length)).foldl
          (fun (pdefs, ep) ((fname, _ftag, _fty), i) =>
            let projName := s!".{fname}"
            let qualName := s!"{sname}.{fname}"
            let unqualUsed := allAppNames.contains projName
            let qualUsed := allAppNames.contains qualName
            if unqualUsed || qualUsed then
              let emitName := if qualUsed then qualName else projName
              if !ep.contains projName then
                if !isPassthrough then
                  let path := projPath i fields.length
                  (pdefs ++ [s!"def «{emitName}» (x : {tupleT}) := x{path}"], ep ++ [projName])
                else
                  (pdefs ++ [s!"def «{emitName}» (x : Array Int) := x"], ep ++ [projName])
              else
                if !isPassthrough then
                  let path := projPath i fields.length
                  (pdefs ++ [s!"def «{qualName}» (x : {tupleT}) := x{path}"], ep)
                else
                  (pdefs ++ [s!"def «{qualName}» (x : Array Int) := x"], ep)
            else (pdefs, ep))
          ([], emittedProjs)
        let newConflicts := (fields.zip (List.range fields.length)).foldl
          (fun cs ((fname, _, _), _) =>
            let projName := s!".{fname}"
            let qualName := s!"{sname}.{fname}"
            let unqualUsed := allAppNames.contains projName
            if unqualUsed && emittedProjs.contains projName then
              cs ++ [(projName, qualName)]
            else cs) ([] : List (String × String))
        (acc ++ ctorDefs ++ projDefs, emittedProjs', conflicts ++ newConflicts))
    ([], ([] : List String), ([] : List (String × String)))

  -- === Generate deps class using TYPED information ===
  -- Names that should NEVER be classified as Int-returning (collection operations)
  let collectionOps := ["iter", "map", "collect", "filter", "zip", "fold",
    "flat_map", "chain", "take", "skip", "enumerate", "rev", "sort",
    "into_iter", "next", "deref"]
  -- Build a map: depName → (maxArity, bestArgTypes, bestRetType)
  -- by scanning the TExpr calls directly
  let depInfo : List (String × Nat × List ImpType × ImpType) := deps.map fun d =>
    -- Find all calls to this dep
    let calls := allTCalls.filter (·.1 == d)
    -- For free-var deps (0-arity), use untyped arity from call collection
    let maxArityFromCalls := calls.foldl (fun acc (_, n, _, _) => max acc n) 0
    let untypedArity := allCalls.filter (·.1 == d) |>.map (·.2)
      |>.foldl (fun acc a => max acc a) 0
    let maxArity := max maxArityFromCalls untypedArity
    -- For free-var deps (0-arity), use the typed var reference type
    let freeVarTy := allTFreeVarsDedup.find? (·.1 == d) |>.map (·.2) |>.getD .unknown
    -- Best arg types: merge across all call sites (prefer non-unknown)
    let bestArgs := (List.range maxArity).map fun i =>
      calls.foldl (fun acc (_, _, argTys, _) =>
        match argTys.toArray[i]? with
        | some ty => mergeType acc ty
        | none => acc) ImpType.unknown
    -- Best return type: merge across call sites and free-var refs
    let bestRet := calls.foldl (fun acc (_, _, _, retTy) =>
      mergeType acc retTy) freeVarTy
    (d, maxArity, bestArgs, bestRet)

  let depsStr := if depInfo.isEmpty then ""
    else
      let depsClassName := s!"{moduleName}Deps"
      let letters := #["a", "b", "c", "d", "e", "f", "g", "h"]
      -- All ImpExpr bodies for heuristic fallback on unknown types
      let allExprs := defs.map (·.2)
      let fields := depInfo.map fun (d, arity, argTypes, retType) =>
        let retStr := depTypeStr retType structLookup
        -- u128 is always Array Int in the extraction model (byte array, not scalar)
        let retStr := match retType with
          | .uint .w128 | .sint .w128 => "Array Int"
          | _ => retStr
        -- Override: collection operations always return Array Int
        let retStr := if collectionOps.contains d && retStr == "Int" then "Array Int" else retStr
        if arity == 0 then
          -- u128 is always Array Int in the extraction model (byte array, not scalar)
          let isWideInt := match retType with
            | .uint .w128 | .sint .w128 => true | _ => false
          let usedAsInt := allExprs.any (isVarUsedAsInt d)
          -- Check struct projections on this variable (e.g., .x, .y applied to d)
          let structTypeFromVar := allExprs.findSome? fun e =>
            structMeta.findSome? fun ((sname, fields) : String × List (String × String × ImpType)) =>
              let projUsed : Bool := fields.any fun (fname, _, _) =>
                checkProjOnVar d s!".{fname}" e ||
                checkProjOnVar d s!"{sname}.{fname}" e
              if projUsed == true then structLookup sname else none
          let retStr := match structTypeFromVar with
            | some st => st  -- struct projections detected: use struct type
            | none =>
              if isWideInt then "Array Int"  -- u128 always byte array
              else if retType.isUnknown then
                if usedAsInt then "Int" else "Array Int"
              else if retStr == "Int" && !usedAsInt then retStr  -- trust TExpr type
              else retStr
          s!"  {sanitizeName d} : {retStr}"
        else
          -- Default arg type: match untyped pipeline's logic
          let hasArrayArg := argTypes.any fun ty =>
            match ty with
            | .array _ _ | .slice _ | .adt "Vec" _ => true | _ => false
          let defaultArgType := if retStr == "Int" && !hasArrayArg then "Int" else "Array Int"
          let paramStr := (List.range arity).map (fun i =>
            let letter := if h : i < letters.size then letters[i] else s!"x{i}"
            let ty := match argTypes.toArray[i]? with
              | some impTy => if impTy.isUnknown then defaultArgType else depTypeStr impTy structLookup
              | none => defaultArgType
            s!"({letter} : {ty})") |> " ".intercalate
          s!"  {sanitizeName d} {paramStr} : {retStr}"
      let exportList := depInfo.map (fun (d, _, _, _) => sanitizeName d) |> " ".intercalate
      s!"/-- External dependencies for {moduleName} extraction (auto-generated from typed TExpr). -/\nclass {depsClassName} where\n{"\n".intercalate fields}\n\nexport {depsClassName} ({exportList})\n\nvariable [{depsClassName}]\n"

  -- Assemble preamble
  let parts := (if structDefs.isEmpty then [] else structDefs) ++
               (if depsStr.isEmpty then [] else [depsStr])
  let result := if parts.isEmpty then ""
    else "\n" ++ "\n\n".intercalate parts ++ "\n"
  (result, projConflicts)

/-! ## Typed Definition Generator -/

/-- Generate a Lean 4 definition using types from the raw TExpr for parameter
    annotations and a post-pipeline ImpExpr for the body rendering.
    `rawTe` has hax types preserved (for param annotations).
    `pipelinedBody` is the post-pipeline ImpExpr (for rendering). -/
def toLeanDefTyped (name : String) (rawTe : TExpr) (pipelinedBody : ImpExpr)
    (structLookup : String → Option String := fun _ => none)
    (structMeta : StructMeta := [])
    (allFnTypes : List (String × HaxAdapter.FnTypeInfo) := [])
    (boolNames : List String := []) : String :=
  let (tparams, _rawBody) := extractTParams rawTe
  -- Use the pipelined body, but strip leading param bindings (same as extractParams on ImpExpr)
  let rec stripParamBindings : ImpExpr → ImpExpr
    | .letBind n (.var v) rest => if n == v then stripParamBindings rest else .letBind n (.var v) rest
    | e => e
  let body := stripParamBindings pipelinedBody
  let paramStr := if tparams.isEmpty then ""
    else " " ++ " ".intercalate (tparams.map fun (p, ty) =>
      let sn := sanitizeName p
      -- Use the type directly from TExpr when it's known
      if ty.isUnknown then sn
      else
        -- Use surface types (Int/Array Int) for compatibility with untyped Runtime.
        -- Width-aware types (UInt16, Vector) are preserved in ImpExpr literals.
        let tyStr := ty.toLeanTypeStrSurface structLookup
        if tyStr == "Int" || tyStr.startsWith "Array" then s!"({sn} : {tyStr})"
        else if tyStr == "Bool" then s!"({sn} : Bool)"
        else if (tyStr.splitOn " × ").length > 1 then s!"({sn} : {tyStr})"
        else sn)
  let bodyStr := toLean body 1 boolNames
  s!"def {sanitizeName name}{paramStr} :=\n{bodyStr}\n"

/-! ## Typed Struct New Expansion

`procTdefs` lose type info due to the erase/lift roundtrip in `parseHaxItemTExpr`.
But `rawTdefs` preserve hax JSON types. We collect struct types for `new()` calls
from rawTdefs, then apply the rewrites to ImpExpr defs after erasure. -/

/-- Resolve an ImpType to a struct in the metadata.
    Matches `.adt name _` against struct names (full path or short name). -/
private def resolveStructFromType (ty : ImpType) (structMeta : StructMeta)
    : Option (String × List (String × String × ImpType)) :=
  match ty with
  | .adt name _ =>
    match structMeta.find? (·.1 == name) with
    | some s => some s
    | none =>
      let shortName := match name.splitOn "::" with
        | [] => name
        | segs => segs.getLast!
      structMeta.find? (·.1 == shortName)
  | _ => none

/-- Collect struct names from `new()` calls in a raw TExpr (which has types from hax JSON). -/
private partial def collectNewStructTypes (structMeta : StructMeta) : TExpr → List String
  | .mk (.app "new" []) ty =>
    match resolveStructFromType ty structMeta with
    | some (sname, _) => [sname]
    | none => []
  | .mk (.app _ args) _ => args.foldl (fun acc a => acc ++ collectNewStructTypes structMeta a) []
  | .mk (.letBind _ v body) _ =>
    collectNewStructTypes structMeta v ++ collectNewStructTypes structMeta body
  | .mk (.seq a b) _ =>
    collectNewStructTypes structMeta a ++ collectNewStructTypes structMeta b
  | .mk (.ifThenElse c t e) _ =>
    collectNewStructTypes structMeta c ++ collectNewStructTypes structMeta t ++
    collectNewStructTypes structMeta e
  | .mk (.tuple es) _ => es.foldl (fun acc e => acc ++ collectNewStructTypes structMeta e) []
  | .mk (.proj e _) _ => collectNewStructTypes structMeta e
  | .mk (.match_ scrut arms) _ =>
    collectNewStructTypes structMeta scrut ++
    arms.foldl (fun acc (_, b) => acc ++ collectNewStructTypes structMeta b) []
  | .mk (.forFold _ lo hi body) _ | .mk (.forFoldRev _ lo hi body) _
  | .mk (.forFoldReturn _ lo hi body) _ | .mk (.forFoldRevReturn _ lo hi body) _ =>
    collectNewStructTypes structMeta lo ++ collectNewStructTypes structMeta hi ++
    collectNewStructTypes structMeta body
  | .mk (.whileFold c body) _ | .mk (.whileFoldReturn c body) _ =>
    collectNewStructTypes structMeta c ++ collectNewStructTypes structMeta body
  | .mk (.cfBreak e) _ | .mk (.cfContinue e) _ | .mk (.cfBreakContinue e) _ =>
    collectNewStructTypes structMeta e
  | _ => []

/-- Build a per-function map of struct types used in `new()` calls.
    Uses rawTdefs which preserve types from hax JSON. -/
def buildNewStructMap (rawTdefs : List (String × TExpr)) (structMeta : StructMeta)
    : List (String × List String) :=
  rawTdefs.filterMap fun (fname, te) =>
    let types := (collectNewStructTypes structMeta te).eraseDups
    if types.isEmpty then none else some (fname, types)

/-- Generate a default-value ImpExpr for a struct field.
    - "int" fields → literal 0
    - "array" fields → Hax.repeat_ 0 size (size from ImpType) -/
private def defaultFieldImpExpr (tag : String) (fty : ImpType) : ImpExpr :=
  if tag == "int" then .lit (.int 0)
  else
    let size := match fty with
      | .array _ len => len
      | _ => 0
    -- Use "repeat" not "Hax.repeat_": the toLean renderer applies runtimeName mapping
    .app "repeat" [.lit (.int 0), .lit (.int size)]

/-- Rewrite `new()` in an ImpExpr using a struct name from the typed map.
    Replaces `.app "new" []` with `StructName defaultField1 defaultField2 ...`. -/
partial def rewriteNewFromStructMap (sname : String) (fields : List (String × String × ImpType))
    : ImpExpr → ImpExpr
  | .app "new" [] =>
    let defaultArgs := fields.map fun (_, tag, fty) => defaultFieldImpExpr tag fty
    .app sname defaultArgs
  | .app f args => .app f (args.map (rewriteNewFromStructMap sname fields))
  | .letBind n v body =>
    .letBind n (rewriteNewFromStructMap sname fields v)
      (rewriteNewFromStructMap sname fields body)
  | .seq a b =>
    .seq (rewriteNewFromStructMap sname fields a)
      (rewriteNewFromStructMap sname fields b)
  | .ifThenElse c t e =>
    .ifThenElse (rewriteNewFromStructMap sname fields c)
      (rewriteNewFromStructMap sname fields t)
      (rewriteNewFromStructMap sname fields e)
  | .tuple es => .tuple (es.map (rewriteNewFromStructMap sname fields))
  | .proj e i => .proj (rewriteNewFromStructMap sname fields e) i
  | .match_ scrut arms =>
    .match_ (rewriteNewFromStructMap sname fields scrut)
      (arms.map fun (p, b) => (p, rewriteNewFromStructMap sname fields b))
  | .forFold v lo hi body =>
    .forFold v (rewriteNewFromStructMap sname fields lo)
      (rewriteNewFromStructMap sname fields hi)
      (rewriteNewFromStructMap sname fields body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (rewriteNewFromStructMap sname fields lo)
      (rewriteNewFromStructMap sname fields hi)
      (rewriteNewFromStructMap sname fields body)
  | .whileFold c body =>
    .whileFold (rewriteNewFromStructMap sname fields c)
      (rewriteNewFromStructMap sname fields body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (rewriteNewFromStructMap sname fields lo)
      (rewriteNewFromStructMap sname fields hi)
      (rewriteNewFromStructMap sname fields body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (rewriteNewFromStructMap sname fields lo)
      (rewriteNewFromStructMap sname fields hi)
      (rewriteNewFromStructMap sname fields body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (rewriteNewFromStructMap sname fields c)
      (rewriteNewFromStructMap sname fields body)
  | .cfBreak e => .cfBreak (rewriteNewFromStructMap sname fields e)
  | .cfContinue e => .cfContinue (rewriteNewFromStructMap sname fields e)
  | .cfBreakContinue e => .cfBreakContinue (rewriteNewFromStructMap sname fields e)
  | e => e

/-! ## Full Typed Certified File Generator -/

/-- Generate a complete certified Lean 4 file from typed TExpr definitions.
    `rawTdefs` has types preserved from hax JSON (for deps class + param annotations).
    `procTdefs` (optional) has pipeline-processed TExprs (for body rendering).
    If `procTdefs` is empty, bodies are rendered from rawTdefs (erased + pipelined). -/
def toLeanCertifiedFileTyped (rawTdefs : List (String × TExpr))
    (moduleName : String := "Generated")
    (structMeta : StructMeta := [])
    (fnTypes : List (String × HaxAdapter.FnTypeInfo) := [])
    (procTdefs : List (String × TExpr) := []) : String :=
  -- Deduplicate raw and proc
  let rawTdefs := rawTdefs.foldl (fun (acc : List (String × TExpr)) (n, te) =>
    if acc.any (·.1 == n) then acc else acc ++ [(n, te)]) []
  let procTdefs := procTdefs.foldl (fun (acc : List (String × TExpr)) (n, te) =>
    if acc.any (·.1 == n) then acc else acc ++ [(n, te)]) []
  -- Build struct-new mapping from rawTdefs (which have types from hax JSON)
  let newStructMap := buildNewStructMap rawTdefs structMeta
  -- For body rendering: use proc TExprs if provided, otherwise erase raw and pipeline
  let defs : List (String × ImpExpr) :=
    if procTdefs.isEmpty then
      -- Erase raw TExprs and apply pipeline
      let rawDefs := rawTdefs.map fun (n, te) => (n, te.erase)
      rawDefs.map fun (n, e) => (n, pipeline e)
    else
      procTdefs.map fun (n, te) => (n, te.erase)
  -- Canonicalization passes (Hax.Canonicalize): drop dead CF bindings,
  -- rewrite panic to unit, normalise _assign discard. After this, the
  -- corresponding detection logic in `toLean` is redundant.
  let defs := defs.map fun (n, e) => (n, Hax.Canonicalize.canonicalize e)
  -- Apply typed passes (struct projection disambiguation, etc.)
  let (defs, fnTypes) := applyTypedPasses defs structMeta fnTypes []
  let structIsPassthrough := computeStructPassthrough structMeta defs
  let structLookup := mkStructLookup structMeta structIsPassthrough
  let ambiguousFields := findAmbiguousFields structMeta
  let defs := if ambiguousFields.isEmpty then defs
    else defs.map fun (n, e) => (n, qualifyProjections structMeta ambiguousFields e e)
  -- Pre-process: rewrite `new args` to struct constructor calls (handles non-empty args)
  let defs := if structMeta.isEmpty then defs
    else defs.map fun (n, e) => (n, rewriteNewToStructCtor structMeta e)
  -- Rewrite `new()` (zero-arg) using struct types from rawTdefs
  -- (procTdefs lose types due to erase/lift roundtrip, but rawTdefs preserve them)
  let defs := if newStructMap.isEmpty then defs
    else defs.map fun (fname, e) =>
      match newStructMap.find? (·.1 == fname) with
      | some (_, [sname]) =>
        -- Unambiguous: all new() calls in this function use one struct type
        match structMeta.find? (·.1 == sname) with
        | some (_, fields) => (fname, rewriteNewFromStructMap sname fields e)
        | none => (fname, e)
      | _ => (fname, e)
  -- Pre-process: rewrite `from_elem ZERO n` for struct arrays
  let defs := if structMeta.isEmpty then defs
    else defs.map fun (n, e) =>
      let fnRetType := fnTypes.find? (·.1 == n) |>.map (·.2.retType)
      let fnRetTypes := match fnRetType with
        | some ty => [(n, ty)]
        | none => []
      (n, rewriteStructFromElem structMeta fnRetTypes defs e)
  -- Fix projection paths for tuples with arity > 2
  let callRetTypes := fnTypes.filterMap fun (n, ti) =>
    if !ti.retType.isUnknown then some (n, ti.retType) else none
  let structArities := structMeta.map fun (sname, fields) => (sname, fields.length)
  let depRetArities := callRetTypes.filterMap fun (dname, retTy) =>
    match retTy with
    | .tuple elems => if elems.length > 2 then some (dname, elems.length) else none
    | _ => none
  let allExprs := defs.map (·.2)
  let usageArities := defs.foldl (fun acc (_, e) =>
    let calls := collectAppCalls e
    let callNames := calls.map (·.1) |>.eraseDups
    acc ++ callNames.filterMap fun fname =>
      let arity := allExprs.foldl (fun a expr => max a (detectReturnArity fname expr)) 0
      if arity > 2 then some (fname, arity) else none) ([] : List (String × Nat))
  let arityMap := (structArities ++ depRetArities ++ usageArities).eraseDups
  let defs := if arityMap.isEmpty then defs
    else defs.map fun (n, e) => (n, fixProjectionPaths arityMap e)
  -- Pass T-A: insert `let v := 0` before any fold whose accumulator
  -- references a variable not bound in the enclosing scope. (Defined
  -- at PrettyPrint.lean:4117 but historically unwired.)
  let defs := defs.map fun (n, e) => (n, initMissingFoldAccums [] e)
  -- Generate preamble: struct definitions use post-passes defs (for qualified names),
  -- deps class uses typed information from raw TExprs.
  let (preamble, projConflicts) := generatePreambleTyped rawTdefs moduleName structMeta fnTypes (processedDefs := defs)
  -- Rewrite function body projection references for conflicts
  let defs := if projConflicts.isEmpty then defs
    else defs.map fun (n, e) =>
      let e' := projConflicts.foldl (fun expr (unqual, qual) =>
        rewriteAppName unqual qual expr) e
      (n, e')
  -- Compute dependency names for post-processing
  let definedNames := defs.map (·.1)
  let structNames := structMeta.map (·.1)
  let allCalls := defs.foldl (fun acc (_, e) => acc ++ collectAppCalls e) []
  let allAppNames := allCalls.map (·.1) |>.eraseDups
  let allFreeVars := defs.foldl (fun acc (fname, e) =>
    acc ++ collectFreeVars [fname] e) ([] : List String)
  let freeVarDeps := allFreeVars.eraseDups.filter fun v =>
    !definedNames.contains v &&
    !structNames.contains v && !isFieldProjection v &&
    !allAppNames.contains v
  let allNamesWithVars := (allAppNames ++ freeVarDeps).eraseDups
  let depNames := allNamesWithVars.filter fun f =>
    !definedNames.contains f &&
    !structNames.contains f && !isFieldProjection f &&
    !isAlwaysBuiltin f
  -- Detect guard-recursion for `partial`
  let needsPartial := defs.any fun (n, e) =>
    let rec stripParams : ImpExpr → ImpExpr
      | .letBind _ (.var _) b => stripParams b
      | e => e
    hasGuardRecursion n (stripParams e)
  -- Compute Bool-returning function names from TExpr types (for condToLean type-directed rendering)
  -- Compute Bool-returning function names from TExpr types
  let boolNames := fnTypes.filterMap fun (n, ti) =>
    match ti.retType with | .bool => some n | _ => none
  let header := s!"/-\n  Auto-generated by haxpipeT --emit-certified (typed extraction pipeline)\n  Surface code + ImpExpr literals for agreement proofs.\n-/\nimport Hax.Runtime\nimport Hax.AST\nimport Hax.Semantics\n\nset_option linter.unusedVariables false\nset_option maxRecDepth 2048\nset_option maxHeartbeats 6400000\n\nnamespace {moduleName}\n\nopen Hax\n{preamble}\nmutual\n\n"
  let body := "\n".intercalate (defs.map fun (n, e) =>
    let fnTi := fnTypes.find? (·.1 == n) |>.map (·.2)
    -- Use rawTdefs for parameter type annotations, defs (post-pipeline ImpExpr) for body
    let surfaceDef := match rawTdefs.find? (·.1 == n) with
      | some (_, rawTe) => toLeanDefTyped n rawTe e (structLookup := structLookup) (structMeta := structMeta) (allFnTypes := fnTypes) (boolNames := boolNames)
      | none => toLeanDef n e (fnTypeInfo := fnTi) (structLookup := structLookup) (structMeta := structMeta) (allFnTypes := fnTypes)
    let surfaceDef := if needsPartial then surfaceDef.replace "def " "partial def " else surfaceDef
    s!"{surfaceDef}")
  let impExprs := "\n".intercalate (defs.map fun (n, e) =>
    let impExprDef := toLeanImpExprDef n e
    let impExprDef := if needsPartial then impExprDef.replace "def " "partial def " else impExprDef
    s!"{impExprDef}")
  let footer := s!"\n{impExprs}\nend\n\nend {moduleName}\n"
  fixDepReferences (header ++ body ++ footer) depNames

end Hax

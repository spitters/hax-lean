/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.TExpr
import Hax.PrettyPrint
import Hax.Pipeline
import Hax.HaxAdapter
import Hax.TPhase.AnnotateLets
import Hax.TPhase.InitFoldAccums
import Hax.TPhase.QualifyProjections
import Hax.TPhase.RewriteNewToStructCtor
import Hax.TPhase.RewriteStructFromElem
import Hax.TPhase.FixProjectionPaths

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
  -- Fold / for-loop constructors bind the loop variable in their body;
  -- the bound list must include `v` for the body traversal, otherwise the
  -- loop index leaks as a "free var" and is misclassified as a Deps method.
  | .mk (.forLoop v lo hi body) _ | .mk (.forLoopRev v lo hi body) _
  | .mk (.forFold v lo hi body) _ | .mk (.forFoldRev v lo hi body) _
  | .mk (.forFoldReturn v lo hi body) _ | .mk (.forFoldRevReturn v lo hi body) _ =>
    collectTFreeVars bound lo ++ collectTFreeVars bound hi ++ collectTFreeVars (v :: bound) body
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

    Unknown maps to "Array Int" to match the untyped pipeline default.
    Unit is preserved as "Unit" for argument positions (Rust does pass
    `()` literals — e.g. `result.ok_or(())`). The legacy "side-effect
    function" Unit→ArrayInt mapping is only applied to RETURN types
    where `.unit` typically means hax-erased side-effects, not a
    semantic Unit. Callers pass `(isReturn := true)` for return types. -/
private def depTypeStr (ty : ImpType) (sl : String → Option String)
    (isReturn : Bool := false) : String :=
  match ty with
  | .unknown => "Array Int"  -- no type info; match untyped default
  | .unit => if isReturn then "Array Int" else "Unit"
  | _ => ty.toLeanTypeStrSurface sl

set_option linter.unusedVariables false in
/-- Generate the deps class and struct definitions using typed information from TExprs.
    This replaces `generatePreamble` by using types directly from the TExpr tree
    instead of ~300 lines of heuristic detection.
    `processedDefs`: post-pipeline ImpExpr defs (with qualified projections etc.)
    for structural analysis. If empty, erases `tdefs`.

    Return value:
    - `preamble` : the emitted preamble text (struct defs + Deps class)
    - `projConflicts` : projection-name conflicts to resolve
    - `clashSet` : opaque ADT names that collide with a Deps method name
      (these must be emitted as `axiom <Name>_T : Type` to avoid the
      type-vs-function ambiguity at the namespace level). -/
def generatePreambleTyped (tdefs : List (String × TExpr))
    (moduleName : String) (structMeta : StructMeta := [])
    (fnTypes : List (String × HaxAdapter.FnTypeInfo) := [])
    (processedDefs : List (String × ImpExpr) := [])
    : String × List (String × String) × List String :=
  -- Use processed defs for structural analysis (qualified projections etc.)
  let defs := if processedDefs.isEmpty then tdefs.map fun (n, te) => (n, te.erase) else processedDefs
  let definedNames := defs.map (·.1)
  let structNames := structMeta.map (·.1)
  let structIsPassthrough := computeStructPassthrough structMeta defs
  let baseStructLookup := mkStructLookup structMeta structIsPassthrough
  -- Compute opaque-ADT-vs-Deps-method clashes: when a type used in a Deps
  -- signature has the same short name as a Deps method, emit the axiom
  -- with a `_T` suffix and route every type reference through that suffix.
  -- Without this, `axiom VectorCommitment : Type` would collide with
  -- `class XDeps where VectorCommitment : Array Int → VectorCommitment`
  -- once the field is `export`ed at the top level.
  let allTCallsForClash := tdefs.foldl (fun acc (_, te) => acc ++ collectTAppCalls te) []
  let allOpaqueForClash :=
    let fromCalls := allTCallsForClash.foldl (fun acc (_, _, argTys, retTy) =>
      let argOpaque := argTys.foldl (fun a t => a ++ t.collectOpaqueAdtNames baseStructLookup) []
      acc ++ argOpaque ++ retTy.collectOpaqueAdtNames baseStructLookup) ([] : List String)
    let fromFnTypes := fnTypes.foldl (fun acc (_, ti) =>
      acc ++ ti.paramTypes.foldl (fun a (_, t) => a ++ t.collectOpaqueAdtNames baseStructLookup) []
          ++ ti.retType.collectOpaqueAdtNames baseStructLookup) ([] : List String)
    (fromCalls ++ fromFnTypes).eraseDups
  let clashDepsNames := allTCallsForClash.map (·.1) |>.eraseDups |>.map sanitizeName
  let clashSet : List String := allOpaqueForClash.filter (clashDepsNames.contains)
  -- Augmented lookup: clash names resolve to their `_T` alias (a fresh
  -- axiom emitted at the top of the file). Non-clash struct lookups go
  -- through the base lookup unchanged.
  let structLookup : String → Option String := fun name =>
    let short := ImpType.sanitizeAdtShortName name
    if clashSet.contains short then some s!"{short}_T"
    else baseStructLookup name

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
    -- Filter out the renderer's marker functions (`::namedProj::T`).
    -- These are TCB-emitted into the post-pipeline ImpExpr to
    -- communicate type info to `toLean`; they are not real Deps
    -- methods and must not appear in the Deps class. The legacy
    -- `::annot::T` marker was retired by P1 in favour of the
    -- first-class `ImpExpr.typeAscription` AST node, which never
    -- appears as an `.app` head so this filter doesn't see it.
    !f.startsWith "::" &&
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
        -- Emit a type abbreviation `abbrev <sname>_T := <tupleT>` so per-field
        -- projection signatures don't repeat the full nested tuple type. Lean
        -- treats `abbrev` transparently, so this is purely cosmetic and
        -- non-passthrough structs benefit the most. Skipped for empty / unused
        -- structs and for passthrough structs (which use raw `Array Int`).
        let abbrevName := s!"{sanitizeName sname}_T"
        let hasAnyEmit := isUsed || projectionsUsed
        let abbrevDefs := if hasAnyEmit && !isPassthrough then
            [s!"/-- Tuple-encoded type for Rust struct `{sname}` (auto-generated). -/\nabbrev {abbrevName} := {tupleT}"]
          else []
        let typeRef := if !isPassthrough && hasAnyEmit then abbrevName else tupleT
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
                s!"def {sanitizeName sname} {paramStr} : {typeRef} := {sanitizeName fields.head!.1}"
              else
                s!"def {sanitizeName sname} {paramStr} : {typeRef} := ({tupleStr})"
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
                  (pdefs ++ [s!"def «{emitName}» (x : {typeRef}) := x{path}"], ep ++ [projName])
                else
                  (pdefs ++ [s!"def «{emitName}» (x : Array Int) := x"], ep ++ [projName])
              else
                if !isPassthrough then
                  let path := projPath i fields.length
                  (pdefs ++ [s!"def «{qualName}» (x : {typeRef}) := x{path}"], ep)
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
        (acc ++ abbrevDefs ++ ctorDefs ++ projDefs, emittedProjs', conflicts ++ newConflicts))
    ([], ([] : List String), ([] : List (String × String)))

  -- === Generate deps class using TYPED information ===
  -- Names that should NEVER be classified as Int-returning (collection operations).
  -- NB: `next` is not here — Rust's `Iterator::next` returns `Option<T>`,
  -- not a collection. Forcing it to `Array Int` breaks Option pattern
  -- matching in extracted while-let-Some loops.
  let collectionOps := ["iter", "map", "collect", "filter", "zip", "fold",
    "flat_map", "chain", "take", "skip", "enumerate", "rev", "sort",
    "into_iter", "deref"]
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

  let depsStr := if depInfo.isEmpty then
      -- Emit an empty deps class anyway so that downstream SurfaceDeps
      -- files referencing `<X>Deps` continue to compile (they may carry
      -- structure beyond the instance — opaque types, theorems, ...).
      let depsClassName := s!"{moduleName}Deps"
      s!"/-- External dependencies for {moduleName} extraction (auto-generated). -/\nclass {depsClassName} where\n"
    else
      let depsClassName := s!"{moduleName}Deps"
      let letters := #["a", "b", "c", "d", "e", "f", "g", "h"]
      -- All ImpExpr bodies for heuristic fallback on unknown types
      let allExprs := defs.map (·.2)
      let fields := depInfo.map fun (d, arity, argTypes, retType) =>
        let retStr := depTypeStr retType structLookup (isReturn := true)
        -- u128 / i128 is always Array Int when it's a *function result* (byte
        -- array, not scalar). For 0-arity dep constants the representation
        -- depends on how the constant is used — `Hax.sub MAX 4` needs MAX
        -- as `Int`, not `Array Int`, so we defer the u128 override to the
        -- usedAsInt/usedAsArray heuristic below.
        let retStr := match retType, arity with
          | .uint .w128, n | .sint .w128, n => if n > 0 then "Array Int" else retStr
          | _, _ => retStr
        -- Override: collection operations always return Array Int
        let retStr := if collectionOps.contains d && retStr == "Int" then "Array Int" else retStr
        if arity == 0 then
          let isWideInt := match retType with
            | .uint .w128 | .sint .w128 => true | _ => false
          let usedAsInt := allExprs.any (isVarUsedAsInt d)
          -- Positive array evidence: `.len` / `.iter` projections on this var.
          -- Unknown-typed 0-arity deps in Rust are almost always scalar
          -- constants (e.g. `u128::MAX`, `i32::MIN`) — collection refs come
          -- through as typed `.array`/`.slice` ADT refs, not `.unknown`.
          let usedAsArray := allExprs.any fun e =>
            checkProjOnVar d "len" e || checkProjOnVar d "iter" e
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
              -- u128/i128 0-arity: prefer Int when used arithmetically
              -- (`Hax.sub MAX 4` etc.); fall back to Array Int when there's
              -- positive evidence it's used as a byte array (`.len`/`.iter`).
              if isWideInt then
                if usedAsArray then "Array Int"
                else if usedAsInt then "Int"
                else "Array Int"  -- byte-array default for w128 with no signal
              else if retType.isUnknown then
                -- Unknown-typed 0-arity deps: switch to `Int` only when
                -- there's positive evidence the constant is used in scalar
                -- arithmetic (`Hax.sub MAX 4` etc.). For everything else,
                -- keep the historical `Array Int` default — opaque deps
                -- typically represent struct constants (e.g. SPDZ `ZERO`
                -- / `ONE` are `FieldElement`, a passthrough struct that
                -- prints as `Array Int`).
                if usedAsArray then "Array Int"
                else if usedAsInt then "Int"
                else "Array Int"
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
  (result, projConflicts, clashSet)

/-! ## Step 3: Let-Binding Type Annotation Injection

The decision of WHICH let-bindings receive a type ascription is made by
the verified pass `Hax.tAnnotateLetBindings` (`Hax/TPhase/AnnotateLets.lean`),
which marks them with the denotation-identity `.ann` constructor. That
pass has the formal property:

```
(tAnnotateLetBindings e).erase = e.erase
```

so it carries no semantic obligation.

This module's job is purely to RENDER the marker: walk the post-pipeline
`TExpr` to find `.ann` nodes on let-RHSs and produce a name→type-string
map for the ImpExpr injection. -/

/-- Walk a post-pipeline `TExpr` and collect `(letBindingName, tyStr)`
    pairs for every let-binding whose RHS is wrapped in `.ann`.

    Decisions of WHICH bindings to wrap come from the verified pass
    `tAnnotateLetBindings`; this function only translates those
    decisions into the rendering layer's representation. The
    ascription type is pre-rendered via `sl` (struct-lookup) here so
    that downstream `injectLetTypeAnnotations` emits ready-to-render
    strings inside `ImpExpr.typeAscription` nodes. -/
partial def collectLetBindingTypes (sl : String → Option String) :
    TExpr → List (String × String)
  | .mk (.letBind n (.mk (.ann inner) annTy) body) _ =>
    -- This let-RHS was marked for annotation by the verified pass.
    -- The pass is conservative — it marks any non-trivial ImpType.
    -- The renderer then makes the final call: skip if the type
    -- stringifies to `Int` (a stdlib-collapse outcome, e.g.
    -- `core::macros::AssertKind` → `Int`), since an `: Int`
    -- ascription would be useless or harmful.
    let tyStr := annTy.toLeanTypeStrSurface sl
    let here := if tyStr == "Int" then [] else [(n, tyStr)]
    here ++ collectLetBindingTypes sl inner ++ collectLetBindingTypes sl body
  | .mk (.letBind _ val body) _ =>
    collectLetBindingTypes sl val ++ collectLetBindingTypes sl body
  | .mk (.app _ args) _ => args.foldl (fun acc a => acc ++ collectLetBindingTypes sl a) []
  | .mk (.seq a b) _ => collectLetBindingTypes sl a ++ collectLetBindingTypes sl b
  | .mk (.ifThenElse c t e) _ =>
    collectLetBindingTypes sl c ++ collectLetBindingTypes sl t ++ collectLetBindingTypes sl e
  | .mk (.tuple es) _ => es.foldl (fun acc e => acc ++ collectLetBindingTypes sl e) []
  | .mk (.proj e _) _ => collectLetBindingTypes sl e
  | .mk (.match_ scrut arms) _ =>
    collectLetBindingTypes sl scrut ++
    arms.foldl (fun acc (_, b) => acc ++ collectLetBindingTypes sl b) []
  | .mk (.forFold _ lo hi body) _ | .mk (.forFoldRev _ lo hi body) _
  | .mk (.forFoldReturn _ lo hi body) _ | .mk (.forFoldRevReturn _ lo hi body) _ =>
    collectLetBindingTypes sl lo ++ collectLetBindingTypes sl hi ++ collectLetBindingTypes sl body
  | .mk (.whileFold c body) _ | .mk (.whileFoldReturn c body) _ =>
    collectLetBindingTypes sl c ++ collectLetBindingTypes sl body
  | .mk (.borrow e) _ | .mk (.deref e) _ => collectLetBindingTypes sl e
  | .mk (.cfBreak e) _ | .mk (.cfContinue e) _ | .mk (.cfBreakContinue e) _ =>
    collectLetBindingTypes sl e
  | .mk (.ann e) _ => collectLetBindingTypes sl e
  | _ => []

/-- Inject `ImpExpr.typeAscription` wrappers into letBind RHSs in an
    ImpExpr body, using the given name→tyStr map. The renderer
    (`Hax.PrettyPrint.toLean`) consumes the wrapper as `(val : T)`.

    Replaces the legacy `::annot::<TyStr>` string-prefix `.app` marker
    (P1, 2026-05-19); the marker is now a first-class AST node that
    can't be confused with a function call whose name happens to
    start with `::`. -/
partial def injectLetTypeAnnotations (typeMap : List (String × String)) :
    ImpExpr → ImpExpr
  | .letBind n val body =>
    let val' := injectLetTypeAnnotations typeMap val
    let body' := injectLetTypeAnnotations typeMap body
    -- Skip annotation for param-shadow patterns (`let n := var n`).
    -- The typeMap is keyed by name; when the same name is bound twice
    -- (e.g. `let p1 := p1; let p1 := g1_decompress p1`), the param-shadow
    -- and the real reassignment share the entry. The param-shadow's RHS
    -- has the parameter's actual type — annotating it with the later
    -- shadowing's type is a type error (regression seen on EUDIW BLS
    -- `pairing_check`, where `let p1 := p1` got ascribed to the decompress
    -- result type `Array Int × Array Int × Bool`).
    let isParamShadow := match val' with | .var v => v == n | _ => false
    match typeMap.find? (·.1 == n), isParamShadow with
    | some (_, tyStr), false => .letBind n (.typeAscription val' tyStr) body'
    | _, _ => .letBind n val' body'
  | .app f args => .app f (args.map (injectLetTypeAnnotations typeMap))
  | .seq a b => .seq (injectLetTypeAnnotations typeMap a) (injectLetTypeAnnotations typeMap b)
  | .ifThenElse c t e =>
    .ifThenElse (injectLetTypeAnnotations typeMap c)
                (injectLetTypeAnnotations typeMap t)
                (injectLetTypeAnnotations typeMap e)
  | .tuple es => .tuple (es.map (injectLetTypeAnnotations typeMap))
  | .proj e i => .proj (injectLetTypeAnnotations typeMap e) i
  | .match_ scrut arms => .match_ (injectLetTypeAnnotations typeMap scrut)
      (arms.map fun (p, b) => (p, injectLetTypeAnnotations typeMap b))
  | .forFold v lo hi body =>
    .forFold v (injectLetTypeAnnotations typeMap lo)
               (injectLetTypeAnnotations typeMap hi)
               (injectLetTypeAnnotations typeMap body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (injectLetTypeAnnotations typeMap lo)
                  (injectLetTypeAnnotations typeMap hi)
                  (injectLetTypeAnnotations typeMap body)
  | .whileFold c body =>
    .whileFold (injectLetTypeAnnotations typeMap c)
               (injectLetTypeAnnotations typeMap body)
  | .borrow e => .borrow (injectLetTypeAnnotations typeMap e)
  | .deref e => .deref (injectLetTypeAnnotations typeMap e)
  | .cfBreak e => .cfBreak (injectLetTypeAnnotations typeMap e)
  | .cfContinue e => .cfContinue (injectLetTypeAnnotations typeMap e)
  | .cfBreakContinue e => .cfBreakContinue (injectLetTypeAnnotations typeMap e)
  | e => e

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
  let (tparams, rawBody) := extractTParams rawTe
  -- Use the pipelined body, but strip leading param bindings (same as extractParams on ImpExpr)
  let rec stripParamBindings : ImpExpr → ImpExpr
    | .letBind n (.var v) rest => if n == v then stripParamBindings rest else .letBind n (.var v) rest
    | e => e
  -- Step 3: apply the verified annotation pass to mark let-RHSs with
  -- `.ann`, then walk the marked TExpr to collect (name → typeStr)
  -- pairs for the renderer. The pass `tAnnotateLetBindings` is proven
  -- denotation-preserving (see `Hax/TPhase/AnnotateLets.lean`); this
  -- module only translates its decisions into ImpExpr injections.
  let annotatedRawTe := tAnnotateLetBindings rawTe
  let letTypes := collectLetBindingTypes structLookup annotatedRawTe
  let body := stripParamBindings (injectLetTypeAnnotations letTypes pipelinedBody)
  -- Return-type annotation: rawBody.ty is the function's return type per
  -- hax JSON. Emit `: T` after the param list when known AND non-trivial
  -- AND all params have annotations (Lean's explicit-return mode requires
  -- all binders to be resolvable before body elaboration). This is needed
  -- for ε-inference when the body returns `Except.ok x` and similar
  -- Option/Result returns.
  -- Skipped cases:
  --   - Unknown / Int: defaults, no extra info
  --   - Unit: hax often annotates side-effect-y functions as `.unit`
  --     return even though the body's last expression is non-Unit
  --     (the unit-ness is hax-erased semantic, not a real type)
  --   - Any param missing a type annotation: switching to explicit
  --     return-type mode in Lean disables body-driven param inference
  -- A param is annotated only if the renderer below produces `(p : T)`.
  -- Mirror that logic to predict whether all params will have explicit
  -- types — otherwise emitting `: RetT` triggers Lean's no-body-inference
  -- mode and the un-annotated param fails to elaborate.
  let isParamAnnotated (ty : ImpType) : Bool :=
    if ty.isUnknown then false
    else
      let s := ty.toLeanTypeStrSurface structLookup
      s == "Int" || s.startsWith "Array" || s == "Bool" || (s.splitOn " × ").length > 1
  let allParamsTyped := tparams.all fun (_, ty) => isParamAnnotated ty
  let retTyStr : String :=
    let ty := rawBody.ty
    let s := ty.toLeanTypeStrSurface structLookup
    if ty.isUnknown || s == "Int" || s == "Unit" || !allParamsTyped then ""
    else s!" : {s}"
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
        -- Axiom-typed parameters (single-token uppercase-start names like
        -- `Commitment_T`, `VectorCommitment_T`, `SchnorrProof`) also need
        -- annotation — otherwise Lean's binder-type inference fails
        -- when the body never uses the param.
        else if tyStr != "Unit" && tyStr.length > 0 && tyStr.front.isUpper then
          s!"({sn} : {tyStr})"
        else sn)
  let bodyStr := toLean body 1 boolNames
  s!"def {sanitizeName name}{paramStr}{retTyStr} :=\n{bodyStr}\n"

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

/-- TCB pre-process: rewrite `.namedProj T x` to `.app "::namedProj::T" [x]`
    so the renderer can recognize newtype `.0` projections via the
    function-name marker after erasure. This is the bridge between the
    verified `.namedProj` constructor and the TCB renderer. -/
partial def markNamedProj : TExpr → TExpr
  | .mk (.namedProj tname e) ty =>
    .mk (.app s!"::namedProj::{tname}" [markNamedProj e]) ty
  | .mk (.app f args) ty => .mk (.app f (args.map markNamedProj)) ty
  | .mk (.letBind n v b) ty => .mk (.letBind n (markNamedProj v) (markNamedProj b)) ty
  | .mk (.tuple es) ty => .mk (.tuple (es.map markNamedProj)) ty
  | .mk (.proj e i) ty => .mk (.proj (markNamedProj e) i) ty
  | .mk (.ifThenElse c t e) ty =>
    .mk (.ifThenElse (markNamedProj c) (markNamedProj t) (markNamedProj e)) ty
  | .mk (.match_ s arms) ty =>
    .mk (.match_ (markNamedProj s) (arms.map fun (p, e) => (p, markNamedProj e))) ty
  | .mk (.seq a b) ty => .mk (.seq (markNamedProj a) (markNamedProj b)) ty
  | .mk (.borrow e) ty => .mk (.borrow (markNamedProj e)) ty
  | .mk (.deref e) ty => .mk (.deref (markNamedProj e)) ty
  | .mk (.assign n r) ty => .mk (.assign n (markNamedProj r)) ty
  | .mk (.forLoop v l h b) ty =>
    .mk (.forLoop v (markNamedProj l) (markNamedProj h) (markNamedProj b)) ty
  | .mk (.forLoopRev v l h b) ty =>
    .mk (.forLoopRev v (markNamedProj l) (markNamedProj h) (markNamedProj b)) ty
  | .mk (.whileLoop c b) ty => .mk (.whileLoop (markNamedProj c) (markNamedProj b)) ty
  | .mk (.break_ (some e)) ty => .mk (.break_ (some (markNamedProj e))) ty
  | .mk (.earlyReturn e) ty => .mk (.earlyReturn (markNamedProj e)) ty
  | .mk (.questionMark e) ty => .mk (.questionMark (markNamedProj e)) ty
  | .mk (.forFold v l h b) ty =>
    .mk (.forFold v (markNamedProj l) (markNamedProj h) (markNamedProj b)) ty
  | .mk (.forFoldRev v l h b) ty =>
    .mk (.forFoldRev v (markNamedProj l) (markNamedProj h) (markNamedProj b)) ty
  | .mk (.whileFold c b) ty => .mk (.whileFold (markNamedProj c) (markNamedProj b)) ty
  | .mk (.forFoldReturn v l h b) ty =>
    .mk (.forFoldReturn v (markNamedProj l) (markNamedProj h) (markNamedProj b)) ty
  | .mk (.forFoldRevReturn v l h b) ty =>
    .mk (.forFoldRevReturn v (markNamedProj l) (markNamedProj h) (markNamedProj b)) ty
  | .mk (.whileFoldReturn c b) ty => .mk (.whileFoldReturn (markNamedProj c) (markNamedProj b)) ty
  | .mk (.cfBreak e) ty => .mk (.cfBreak (markNamedProj e)) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue (markNamedProj e)) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (markNamedProj e)) ty
  | .mk (.ann e) ty => .mk (.ann (markNamedProj e)) ty
  | e => e

/-- Generate a complete certified Lean 4 file from typed TExpr definitions.
    `rawTdefs` has types preserved from hax JSON (for deps class + param annotations).
    `procTdefs` (optional) has pipeline-processed TExprs (for body rendering).
    If `procTdefs` is empty, bodies are rendered from rawTdefs (erased + pipelined).
    `newtypes` is the JSON-derived newtype map; the renderer uses it to emit
    `abbrev T_T := <Inner>` aliases plus definitional `«T.0»` unwraps. -/
def toLeanCertifiedFileTyped (rawTdefs : List (String × TExpr))
    (moduleName : String := "Generated")
    (structMeta : StructMeta := [])
    (fnTypes : List (String × HaxAdapter.FnTypeInfo) := [])
    (procTdefs : List (String × TExpr) := [])
    (newtypes : HaxAdapter.NewtypeMap := [])
    (enumMeta : List HaxAdapter.EnumInfo := []) : String :=
  -- Deduplicate raw and proc
  let rawTdefs := rawTdefs.foldl (fun (acc : List (String × TExpr)) (n, te) =>
    if acc.any (·.1 == n) then acc else acc ++ [(n, te)]) []
  let procTdefs := procTdefs.foldl (fun (acc : List (String × TExpr)) (n, te) =>
    if acc.any (·.1 == n) then acc else acc ++ [(n, te)]) []
  -- Build struct-new mapping from rawTdefs (which have types from hax JSON)
  let newStructMap := buildNewStructMap rawTdefs structMeta
  -- TCB pre-process: rewrite `.namedProj T x` in the post-pipeline TExpr
  -- to `.app "::namedProj::T" [x]` (via the top-level `markNamedProj`)
  -- so the renderer (operating on ImpExpr after erasure) can recognize
  -- newtype-specific `.0` projections via the marker function-name.
  let procTdefs := procTdefs.map fun (n, te) => (n, markNamedProj te)
  -- Apply the typed init-fold-accums phase BEFORE erase, so the
  -- accumulator init insertions happen on the type-rich TExpr.
  -- Erase-preservation: `Hax.TPhase.tInitMissingFoldAccums_erase`
  -- proves `(tInitMissingFoldAccums bound e).erase = initMissingFoldAccums bound e.erase`.
  let procTdefs := procTdefs.map fun (n, te) =>
    (n, tInitMissingFoldAccums [] te)
  -- Typed phases (run BEFORE erase so type-dependent rewrites use direct
  -- `TExpr.ty` annotations instead of post-erase heuristics). The
  -- equivalent untyped passes downstream become idempotent no-ops because
  -- the patterns they detect (`.app ".field"`, `.app "new" args`,
  -- `.app "from_elem" ..`, `.app ".N" ..` for N>1) have already been
  -- rewritten at the TExpr level. Each typed phase has a documented
  -- erase-preservation property (theorem deferred pending a `WellTyped`
  -- predicate).
  let ambiguousFields := findAmbiguousFields structMeta
  let procTdefs := if ambiguousFields.isEmpty then procTdefs
    else procTdefs.map fun (n, te) =>
      (n, tQualifyProjections structMeta ambiguousFields te te)
  let procTdefs := if structMeta.isEmpty then procTdefs
    else procTdefs.map fun (n, te) => (n, tRewriteNewToStructCtor structMeta te)
  let procTdefs := if structMeta.isEmpty then procTdefs
    else procTdefs.map fun (n, te) =>
      let fnRetType := fnTypes.find? (·.1 == n) |>.map (·.2.retType)
      let fnRetTypes := match fnRetType with
        | some ty => if ty.isUnknown then [] else [(n, ty)]
        | none => []
      (n, tRewriteStructFromElem structMeta fnRetTypes procTdefs te)
  let procTdefs := procTdefs.map fun (n, te) => (n, tFixProjectionPaths te)
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
  -- The four type-dependent post-erase rewriters
  -- (`qualifyProjections`, `rewriteNewToStructCtor`,
  -- `rewriteStructFromElem`, `fixProjectionPaths`) were removed here on
  -- 2026-05-18 after the typed pipeline gained full coverage. The typed
  -- analogs run on TExpr before erase using direct `arg.ty` annotations
  -- (see `Hax.TPhase.{QualifyProjections,RewriteNewToStructCtor,
  -- RewriteStructFromElem,FixProjectionPaths}`).
  --
  -- The fix that unblocked deletion: `tRewriteStructFromElem` now
  -- unwraps `.ann` type-ascription wrappers around `from_elem` calls,
  -- which the hax JSON adapter inserts for macro expansions like
  -- `vec![T::ZERO; n]`. Without the unwrap, the typed phase silently
  -- missed those calls and we depended on the untyped fallback (SPDZ).
  --
  -- The zero-arg `new()` rewriter (`rewriteNewFromStructMap`) is kept —
  -- it consumes per-function struct mapping from `rawTdefs` that the
  -- typed phase doesn't reconstruct (the typed `tRewriteNewToStructCtor`
  -- skips empty-args calls).
  let defs := if newStructMap.isEmpty then defs
    else defs.map fun (fname, e) =>
      match newStructMap.find? (·.1 == fname) with
      | some (_, [sname]) =>
        match structMeta.find? (·.1 == sname) with
        | some (_, fields) => (fname, rewriteNewFromStructMap sname fields e)
        | none => (fname, e)
      | _ => (fname, e)
  -- Generate preamble: struct definitions use post-passes defs (for qualified names),
  -- deps class uses typed information from raw TExprs.
  let (preamble, projConflicts, axiomClashSet) := generatePreambleTyped rawTdefs moduleName structMeta fnTypes (processedDefs := defs)
  -- Keep the BASE structLookup (no clash augment) for opaque-ADT
  -- collection — augmenting it would make collectOpaqueAdtNames treat
  -- clashing names as known structs and skip them, leaving `Commitment_T`
  -- referenced but unaxiomed.
  let baseStructLookup := structLookup
  -- Augmented structLookup: clash names route to their `_T` alias.
  -- Used for body emission (toLeanDefTyped) so let-binding type
  -- ascriptions render as `(val : Commitment_T)` instead of
  -- `(val : Commitment)` (which would resolve to the Deps function).
  let structLookup : String → Option String := fun name =>
    let short := ImpType.sanitizeAdtShortName name
    if axiomClashSet.contains short then some s!"{short}_T"
    else baseStructLookup name
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
    !f.startsWith "::" &&  -- exclude renderer markers
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
  -- Step 2: collect opaque ADT names from every type the emit references
  -- and emit `axiom <Name> : Type` declarations. With this, Deps signatures
  -- can name cipher / block / newtype types instead of collapsing to `Int`.
  let collectFromFnTypeInfoT (ti : HaxAdapter.FnTypeInfo) : List String :=
    ti.paramTypes.foldl (fun acc (_, t) => acc ++ t.collectOpaqueAdtNames baseStructLookup) []
      ++ ti.retType.collectOpaqueAdtNames baseStructLookup
  let opaqueFromFnTypes := fnTypes.foldl (fun acc (_, ti) =>
    acc ++ collectFromFnTypeInfoT ti) ([] : List String)
  -- Also walk every external call's argument and return types so opaque
  -- ADTs referenced only by Deps-class signatures (not by local return
  -- types) are axiomed. Without this, types like `Commitment` in
  -- `class XDeps where f : ... → Commitment` would be unresolved.
  -- Uses baseStructLookup (not the clash-augmented one) so clash names
  -- still survive the "known struct" filter.
  let allTCallsAxiom := rawTdefs.foldl (fun acc (_, te) => acc ++ collectTAppCalls te) []
  let opaqueFromCalls := allTCallsAxiom.foldl (fun acc (_, _, argTys, retTy) =>
    let argOpaque := argTys.foldl (fun a t => a ++ t.collectOpaqueAdtNames baseStructLookup) []
    acc ++ argOpaque ++ retTy.collectOpaqueAdtNames baseStructLookup) ([] : List String)
  -- Apply the clash-rename: names colliding with a Deps method are emitted
  -- as `axiom <Name>_T : Type` and the augmented structLookup inside
  -- generatePreambleTyped routes type references to `<Name>_T`. This
  -- preserves the body's ability to call the Deps method by its plain
  -- name while keeping the type unambiguous.
  let renameForClash (n : String) : String :=
    if axiomClashSet.contains n then s!"{n}_T" else n
  -- Newtype-T aliases: for each `(name, innerImpType)` in `newtypes`,
  -- the `<name>_T` axiom is REPLACED by an `abbrev <name>_T := <Inner>`
  -- so that `«<name>.0» x` (a definitional unwrap) returns `<Inner>`
  -- rather than the opaque alias. Build the set of clashed-renamed
  -- newtype names so we can filter them out of the axiom emission.
  let newtypeRenamed : List (String × String) :=  -- (T_T-name, renderedInner)
    newtypes.map fun (n, innerTy) =>
      let aliasName := renameForClash n  -- e.g. "VectorCommitment_T"
      let innerStr := innerTy.toLeanTypeStrSurface baseStructLookup
      (aliasName, innerStr)
  let isNewtypeAlias (s : String) : Bool := newtypeRenamed.any (·.1 == s)
  -- Names defined by `inductive` (Rust user enums) should NOT be emitted
  -- as axioms; they have real constructors below.
  let isEnum (s : String) : Bool := enumMeta.any fun e => e.name == s || s == s!"{e.name}_T"
  let allOpaque := (opaqueFromFnTypes ++ opaqueFromCalls).eraseDups.map renameForClash
  let allOpaque := (allOpaque.filter (fun n => !isNewtypeAlias n && !isEnum n)).eraseDups
  let axiomsBlock := if allOpaque.isEmpty then ""
    else "/-- Opaque types extracted from hax JSON. Concrete instances are\n    provided by the protocol's bridge-adapter at the CatCrypt surface. -/\n"
      ++ "\n".intercalate (allOpaque.map fun n => s!"axiom {n} : Type") ++ "\n\n"
  -- Inductive datatypes for user-defined Rust enums (unit variants only;
  -- payloads not yet supported). Emitting `inductive T : Type where ...`
  -- gives pattern matches `match x with | .Variant => ...` real
  -- constructors to resolve, where `axiom T : Type` would leave them
  -- unresolved.
  let inductiveBlock : String :=
    if enumMeta.isEmpty then ""
    else
      let lines := enumMeta.map fun ei =>
        let variants := ei.variants.map (fun v =>
          if v.payload.isEmpty then s!"  | {v.name}"
          else
            -- Render `| Name : T1 → T2 → ... → MyEnum` for payload variants.
            let payloadStrs := v.payload.map fun ty =>
              let s := ty.toLeanTypeStrSurface baseStructLookup
              if (s.splitOn " × ").length > 1 || (s.splitOn " → ").length > 1
                then s!"({s})" else s
            let arrowChain := " → ".intercalate (payloadStrs ++ [ei.name])
            s!"  | {v.name} : {arrowChain}") |> "\n".intercalate
        s!"inductive {ei.name} : Type where\n{variants}\n  deriving Inhabited, BEq"
      "/-- Rust enum definitions extracted from hax JSON. -/\n"
        ++ "\n\n".intercalate lines ++ "\n\n"
  -- Newtype preamble: emit `abbrev <T>_T := <Inner>` and the
  -- definitional unwrap `def «<T>.0» x := x` per newtype.
  let newtypeBlock : String :=
    if newtypeRenamed.isEmpty then ""
    else
      let lines := newtypeRenamed.map fun (aliasName, innerStr) =>
        -- Original short name (without `_T`): used for the projection name
        let bareName := if aliasName.endsWith "_T" then aliasName.dropRight 2 else aliasName
        s!"abbrev {aliasName} := {innerStr}\nnoncomputable def «{bareName}.0» (x : {aliasName}) : {innerStr} := x"
      "/-- Newtype tuple-struct aliases: transparent type equalities\n    with definitional `.0` unwraps. Inner types may themselves be\n    axiomatized (see the axiom block above). -/\n"
        ++ "\n".intercalate lines ++ "\n\n"
  let header := s!"/-\n  Auto-generated by haxpipeT --emit-certified (typed extraction pipeline)\n  Surface code + ImpExpr literals for agreement proofs.\n-/\nimport Hax.Runtime\nimport Hax.AST\nimport Hax.Semantics\n\nset_option linter.unusedVariables false\nset_option maxRecDepth 2048\nset_option maxHeartbeats 6400000\n\nnamespace {moduleName}\n\nopen Hax\n\n-- All emitted functions are `noncomputable`: extracted bodies may\n-- depend on Runtime axioms (sha256, bridgeCast, ...) which the Lean\n-- code generator rejects. Verification doesn't require execution.\nnoncomputable section\n\n{inductiveBlock}{axiomsBlock}{newtypeBlock}{preamble}\nmutual\n\n"
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
  let footer := s!"\n{impExprs}\nend\n\nend  -- noncomputable section\n\nend {moduleName}\n"
  fixDepReferences (header ++ body ++ footer) depNames

end Hax

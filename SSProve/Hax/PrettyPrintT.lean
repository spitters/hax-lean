/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.PrettyPrint

/-!
# Typed Code Generation Module for haxpipeT

`PrettyPrintT.lean` extends the frozen `PrettyPrint.lean` with type-aware
rewrite passes. It imports `PrettyPrint.lean` (via `CLI.lean`) and overrides
only `toLeanCertifiedFile` with `toLeanCertifiedFileT`.

## Three additional passes

1. **initMissingFoldAccums**: When a fold accumulator tuple `(a, b)` references
   a variable `b` not bound in the enclosing scope, inserts `let b := (0 : Int)`
   before the fold. Fixes BLS `q_hat` issue.

2. **dropConflictingParamTypes**: When a locally-defined function has struct-typed
   params (e.g., `G1Affine`) but is called with `Array Int` args, removes the
   param type from `fnTypes` so the definition won't get a conflicting annotation.
   Fixes BLS `pairing_check` type mismatch.

3. **qualifyProjectionsFromUsage**: When an ambiguous projection like `.items` is
   applied to an expression whose struct type can be inferred from array element
   constructors (e.g., `Hax.push arr (WordVec ...)`), qualifies it correctly.
   Fixes SoftSpokenOT projection disambiguation.
-/

namespace SSProve.Hax

open SSProve.Hax

/-! ## Pass A: Initialize missing fold accumulators -/

/-- Collect all variable names bound by let-bindings in the top-level of an expression.
    Used to track scope for fold accumulator analysis. -/
private partial def collectBoundNames : ImpExpr → List String
  | .letBind n _ body => n :: collectBoundNames body
  | .seq a b => collectBoundNames a ++ collectBoundNames b
  | _ => []

/-- Extract accumulator variable names from a fold body by detecting mutation patterns.
    Mirrors the logic in PrettyPrint.extractAccumulators. -/
private partial def extractAccumNamesFromBody : ImpExpr → List String
  | .seq (.seq a b) c => extractAccumNamesFromBody (.seq a (.seq b c))
  | .seq (.letBind n _ (.var v)) rest =>
    if n == v && !n.startsWith "_assign" then
      let restAccs := extractAccumNamesFromBody rest
      if restAccs.contains n then restAccs else n :: restAccs
    else extractAccumNamesFromBody rest
  | .seq (.ifThenElse _ thn _) rest =>
    let thnAccs := extractCondMuts thn |>.filter (!·.startsWith "_assign")
    let restAccs := extractAccumNamesFromBody rest
    (thnAccs ++ restAccs).eraseDups
  | .seq _ rest => extractAccumNamesFromBody rest
  | .letBind n _ (.var v) =>
    if n == v && !n.startsWith "_assign" then [n] else []
  | .letBind _ _ body => extractAccumNamesFromBody body
  | .ifThenElse _ thn _ =>
    (extractCondMuts thn).filter (!·.startsWith "_assign") |>.eraseDups
  | _ => []
where
  extractCondMuts : ImpExpr → List String
    | .seq (.seq a b) c => extractCondMuts (.seq a (.seq b c))
    | .seq (.letBind n _ (.var v)) rest =>
      if n == v then n :: extractCondMuts rest else extractCondMuts rest
    | .seq .unitVal rest => extractCondMuts rest
    | .seq _ rest => extractCondMuts rest
    | .letBind n _ (.var v) => if n == v then [n] else []
    | .letBind _ _ body => extractCondMuts body
    | .unitVal => []
    | _ => []

/-- Walk an ImpExpr and insert `let v := (0 : Int)` before any fold whose
    accumulator (extracted from the body's mutation patterns) references a
    variable `v` not bound in the enclosing scope.
    `bound` tracks names bound by enclosing let-bindings. -/
private partial def initMissingFoldAccums (bound : List String := []) : ImpExpr → ImpExpr
  | .letBind n v body =>
    let v' := initMissingFoldAccums bound v
    let body' := initMissingFoldAccums (n :: bound) body
    .letBind n v' body'
  | .seq a b =>
    let a' := initMissingFoldAccums bound a
    let boundsFromA := collectBoundNames a
    .seq a' (initMissingFoldAccums (bound ++ boundsFromA) b)
  -- forFold: extract accumulators from body, check for free variables
  | .forFold v lo hi body =>
    let lo' := initMissingFoldAccums bound lo
    let hi' := initMissingFoldAccums bound hi
    let body' := initMissingFoldAccums (v :: bound) body
    let fold := ImpExpr.forFold v lo' hi' body'
    -- Extract accumulator names from the body (mutation patterns)
    let accumNames := extractAccumNamesFromBody body'
    let freeAccums := accumNames.filter fun n => !bound.contains n
    -- Insert let-bindings for free accumulator variables before the fold
    freeAccums.foldr (fun fv expr => .letBind fv (.lit (.int 0)) expr) fold
  | .forFoldRev v lo hi body =>
    let lo' := initMissingFoldAccums bound lo
    let hi' := initMissingFoldAccums bound hi
    let body' := initMissingFoldAccums (v :: bound) body
    let fold := ImpExpr.forFoldRev v lo' hi' body'
    let accumNames := extractAccumNamesFromBody body'
    let freeAccums := accumNames.filter fun n => !bound.contains n
    freeAccums.foldr (fun fv expr => .letBind fv (.lit (.int 0)) expr) fold
  | .forFoldReturn v lo hi body =>
    let lo' := initMissingFoldAccums bound lo
    let hi' := initMissingFoldAccums bound hi
    let body' := initMissingFoldAccums (v :: bound) body
    let fold := ImpExpr.forFoldReturn v lo' hi' body'
    let accumNames := extractAccumNamesFromBody body'
    let freeAccums := accumNames.filter fun n => !bound.contains n
    freeAccums.foldr (fun fv expr => .letBind fv (.lit (.int 0)) expr) fold
  | .forFoldRevReturn v lo hi body =>
    let lo' := initMissingFoldAccums bound lo
    let hi' := initMissingFoldAccums bound hi
    let body' := initMissingFoldAccums (v :: bound) body
    let fold := ImpExpr.forFoldRevReturn v lo' hi' body'
    let accumNames := extractAccumNamesFromBody body'
    let freeAccums := accumNames.filter fun n => !bound.contains n
    freeAccums.foldr (fun fv expr => .letBind fv (.lit (.int 0)) expr) fold
  | .ifThenElse c t e =>
    .ifThenElse (initMissingFoldAccums bound c)
      (initMissingFoldAccums bound t) (initMissingFoldAccums bound e)
  | .match_ scrut arms =>
    .match_ (initMissingFoldAccums bound scrut)
      (arms.map fun (p, b) => (p, initMissingFoldAccums bound b))
  | .whileFold c body =>
    .whileFold (initMissingFoldAccums bound c) (initMissingFoldAccums bound body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (initMissingFoldAccums bound c) (initMissingFoldAccums bound body)
  | .tuple es => .tuple (es.map (initMissingFoldAccums bound))
  | .proj e i => .proj (initMissingFoldAccums bound e) i
  | .app f args => .app f (args.map (initMissingFoldAccums bound))
  | .cfBreak e => .cfBreak (initMissingFoldAccums bound e)
  | .cfContinue e => .cfContinue (initMissingFoldAccums bound e)
  | .cfBreakContinue e => .cfBreakContinue (initMissingFoldAccums bound e)
  | e => e

/-! ## Pass B: Drop conflicting param type annotations -/

/-- Collect all call sites for a function, returning the argument lists. -/
private partial def collectCallArgs (fname : String) : ImpExpr → List (List ImpExpr)
  | .app f args =>
    let sub := args.foldl (fun acc a => acc ++ collectCallArgs fname a) []
    if f == fname then [args] ++ sub else sub
  | .letBind _ v body =>
    collectCallArgs fname v ++ collectCallArgs fname body
  | .seq a b => collectCallArgs fname a ++ collectCallArgs fname b
  | .ifThenElse c t e =>
    collectCallArgs fname c ++ collectCallArgs fname t ++ collectCallArgs fname e
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    collectCallArgs fname lo ++ collectCallArgs fname hi ++
    collectCallArgs fname body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    collectCallArgs fname lo ++ collectCallArgs fname hi ++
    collectCallArgs fname body
  | .whileFold c body | .whileFoldReturn c body =>
    collectCallArgs fname c ++ collectCallArgs fname body
  | .match_ scrut arms =>
    collectCallArgs fname scrut ++
    arms.foldl (fun acc (_, b) => acc ++ collectCallArgs fname b) []
  | .tuple es => es.foldl (fun acc e => acc ++ collectCallArgs fname e) []
  | .proj e _ => collectCallArgs fname e
  | .cfBreak e | .cfContinue e | .cfBreakContinue e => collectCallArgs fname e
  | _ => []

/-- Unwrap ImpType.ref wrappers to get the inner type. -/
private def unwrapRef : ImpType → ImpType
  | .ref inner _ => unwrapRef inner
  | ty => ty

/-- Check if a type resolves to a struct tuple (not just Array Int or Int). -/
private def isStructTupleType (ty : ImpType) (structLookup : String → Option String)
    (_structMeta : StructMeta := []) : Bool :=
  let ty := unwrapRef ty
  match ty with
  | .adt name _ =>
    match structLookup name with
    | some s => (s.splitOn " × ").length > 1  -- has product type
    | none =>
      -- Try short name (last segment of Rust path)
      let shortName := match name.splitOn "::" with
        | [] => name
        | segs => segs.getLast!
      match structLookup shortName with
      | some s => (s.splitOn " × ").length > 1
      | none => false
  | .tuple elems => elems.length > 1
  | _ => false

/-- Deduplicate fnTypes: for each function name, if callSigs has non-struct
    types but fnTypes has struct types, replace the fnTypes entry with a version
    that uses the callSigs param types. Also dedup to keep only one entry per name.
    This fixes cases where hax extracts both a trait method and concrete impl
    with different type signatures. -/
def reconcileFnTypes
    (defs : List (String × ImpExpr))
    (fnTypes : List (String × HaxAdapter.FnTypeInfo))
    (structMeta : StructMeta)
    (structLookup : String → Option String)
    (callSigs : List (String × HaxAdapter.FnTypeInfo) := []) :
    List (String × HaxAdapter.FnTypeInfo) :=
  let definedNames := defs.map (·.1)
  -- For each defined function with struct-typed params, check if callSigs disagrees
  -- If so, prefer callSigs types (which reflect how the function is actually called)
  let reconciled := fnTypes.map fun (fname, ti) =>
    if !definedNames.contains fname then (fname, ti)
    else
      let hasStructParams := ti.paramTypes.any fun (_, pty) =>
        isStructTupleType pty structLookup
      if !hasStructParams then (fname, ti)
      else
        match callSigs.find? (·.1 == fname) with
        | some (_, callTi) =>
          -- If callSigs has non-struct params but fnTypes has struct params,
          -- merge: keep original param names, use callSigs types
          let callHasStruct := callTi.paramTypes.any fun (_, pty) =>
            isStructTupleType pty structLookup
          if callHasStruct then (fname, ti)
          else
            -- Build merged param types: original names + callSig types
            let indexed := (List.range ti.paramTypes.length).zip ti.paramTypes
            let newParamTypes := indexed.map fun (i, (pname, _)) =>
              match callTi.paramTypes[i]? with
              | some (_, callPty) => (pname, callPty)
              | none => (pname, ImpType.int)  -- fallback: treat as Int
            let newRetType := if callTi.retType.isUnknown then ti.retType else callTi.retType
            (fname, { paramTypes := newParamTypes, retType := newRetType })
        | none => (fname, ti)
  -- Deduplicate: keep first entry for each name
  reconciled.foldl (fun (acc : List (String × HaxAdapter.FnTypeInfo)) (n, ti) =>
    if acc.any (·.1 == n) then acc else acc ++ [(n, ti)]) []

/-! ## Pass C: Type-aware projection qualification from usage -/

/-- Detect the struct constructor used with `Hax.push arr (StructName ...)` patterns.
    Returns a list of (arrayVarName, structName) pairs. -/
private partial def detectArrayElementTypes : ImpExpr → List (String × String)
  | .app "push" [.var arr, .app ctor _] =>
    -- push arr (StructName args) → arr contains StructName elements
    [(arr, ctor)]
  | .letBind _ v body =>
    detectArrayElementTypes v ++ detectArrayElementTypes body
  | .seq a b => detectArrayElementTypes a ++ detectArrayElementTypes b
  | .ifThenElse c t e =>
    detectArrayElementTypes c ++ detectArrayElementTypes t ++ detectArrayElementTypes e
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    detectArrayElementTypes lo ++ detectArrayElementTypes hi ++
    detectArrayElementTypes body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    detectArrayElementTypes lo ++ detectArrayElementTypes hi ++
    detectArrayElementTypes body
  | .whileFold c body | .whileFoldReturn c body =>
    detectArrayElementTypes c ++ detectArrayElementTypes body
  | .match_ scrut arms =>
    detectArrayElementTypes scrut ++
    arms.foldl (fun acc (_, b) => acc ++ detectArrayElementTypes b) []
  | .app _ args => args.foldl (fun acc a => acc ++ detectArrayElementTypes a) []
  | .tuple es => es.foldl (fun acc e => acc ++ detectArrayElementTypes e) []
  | _ => []

/-- Detect the struct type from `let x := StructName args` patterns. -/
private partial def detectLetBindStructTypes : ImpExpr → List (String × String)
  | .letBind n (.app ctor _) body =>
    [(n, ctor)] ++ detectLetBindStructTypes body
  | .letBind _ v body =>
    detectLetBindStructTypes v ++ detectLetBindStructTypes body
  | .seq a b => detectLetBindStructTypes a ++ detectLetBindStructTypes b
  | .ifThenElse c t e =>
    detectLetBindStructTypes c ++ detectLetBindStructTypes t ++
    detectLetBindStructTypes e
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    detectLetBindStructTypes lo ++ detectLetBindStructTypes hi ++
    detectLetBindStructTypes body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    detectLetBindStructTypes lo ++ detectLetBindStructTypes hi ++
    detectLetBindStructTypes body
  | .whileFold c body | .whileFoldReturn c body =>
    detectLetBindStructTypes c ++ detectLetBindStructTypes body
  | .match_ scrut arms =>
    detectLetBindStructTypes scrut ++
    arms.foldl (fun acc (_, b) => acc ++ detectLetBindStructTypes b) []
  | _ => []

/-- Given a map of (array_var → element_struct_type), rewrite ambiguous
    projections on `Hax.index arr idx` to use the correct qualified name.

    E.g., if `copath` maps to `WordVec` and we see:
      `«BoolVec.items» (Hax.index copath level)`
    or `«.items» (Hax.index copath level)`,
    rewrite to `«WordVec.items» (Hax.index copath level)`.

    Also handles direct variable projections: if `x` maps to struct `S`,
    then `.items x` becomes `S.items x`. -/
private partial def qualifyProjectionsFromUsage
    (arrayElemTypes : List (String × String))
    (varStructTypes : List (String × String))
    (structMeta : StructMeta)
    (ambiguousFields : List String) : ImpExpr → ImpExpr
  | .app projName [.app "index" [.var arr, idx]] =>
    -- Projection on array element: check if array has known element type
    let fieldName := if projName.startsWith "." then projName.drop 1
      else if projName.contains '.' then
        match projName.splitOn "." with | _ :: f :: _ => f | _ => projName
      else projName
    if ambiguousFields.contains fieldName then
      match arrayElemTypes.find? (·.1 == arr) with
      | some (_, structName) =>
        -- Check if this struct actually has this field
        let hasField := structMeta.any fun (sn, fields) =>
          sn == structName && fields.any (·.1 == fieldName)
        if hasField then
          .app s!"{structName}.{fieldName}"
            [.app "index" [.var arr,
              qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields idx]]
        else
          .app projName
            [.app "index" [.var arr,
              qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields idx]]
      | none =>
        .app projName
          [.app "index" [.var arr,
            qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields idx]]
    else
      .app projName
        [.app "index" [.var arr,
          qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields idx]]
  | .app projName [.app "Hax.index" [.var arr, idx]] =>
    -- Same for Hax.index variant
    let fieldName := if projName.startsWith "." then projName.drop 1
      else if projName.contains '.' then
        match projName.splitOn "." with | _ :: f :: _ => f | _ => projName
      else projName
    if ambiguousFields.contains fieldName then
      match arrayElemTypes.find? (·.1 == arr) with
      | some (_, structName) =>
        let hasField := structMeta.any fun (sn, fields) =>
          sn == structName && fields.any (·.1 == fieldName)
        if hasField then
          .app s!"{structName}.{fieldName}"
            [.app "Hax.index" [.var arr,
              qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields idx]]
        else
          .app projName
            [.app "Hax.index" [.var arr,
              qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields idx]]
      | none =>
        .app projName
          [.app "Hax.index" [.var arr,
            qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields idx]]
    else
      .app projName
        [.app "Hax.index" [.var arr,
          qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields idx]]
  -- Direct variable projection: .items x where x has known struct type
  | .app projName [.var v] =>
    let fieldName := if projName.startsWith "." then projName.drop 1
      else if projName.contains '.' then
        match projName.splitOn "." with | _ :: f :: _ => f | _ => projName
      else projName
    if ambiguousFields.contains fieldName then
      match varStructTypes.find? (·.1 == v) with
      | some (_, structName) =>
        let hasField := structMeta.any fun (sn, fields) =>
          sn == structName && fields.any (·.1 == fieldName)
        if hasField then .app s!"{structName}.{fieldName}" [.var v]
        else .app projName [.var v]
      | none => .app projName [.var v]
    else .app projName [.var v]
  | .app f args =>
    .app f (args.map (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields))
  | .letBind n v body =>
    .letBind n
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields v)
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields body)
  | .seq a b =>
    .seq (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields a)
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields b)
  | .ifThenElse c t e =>
    .ifThenElse
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields c)
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields t)
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields e)
  | .tuple es =>
    .tuple (es.map (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields))
  | .proj e i =>
    .proj (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields e) i
  | .match_ scrut arms =>
    .match_ (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields scrut)
      (arms.map fun (p, b) =>
        (p, qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields b))
  | .forFold v lo hi body =>
    .forFold v
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields lo)
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields hi)
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields lo)
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields hi)
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields body)
  | .whileFold c body =>
    .whileFold
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields c)
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields lo)
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields hi)
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields lo)
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields hi)
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields body)
  | .whileFoldReturn c body =>
    .whileFoldReturn
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields c)
      (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields body)
  | .cfBreak e =>
    .cfBreak (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields e)
  | .cfContinue e =>
    .cfContinue (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields e)
  | .cfBreakContinue e =>
    .cfBreakContinue (qualifyProjectionsFromUsage arrayElemTypes varStructTypes structMeta ambiguousFields e)
  | e => e

/-- Propagate return element types: when a function call result is bound to a
    variable, and that function is known to return arrays of a specific struct type,
    record the variable as containing that struct type. -/
private partial def propagateReturnElemTypes
    (funcRetElemTypes : List (String × String)) : ImpExpr → List (String × String)
  | .letBind varName (.app fname _) body =>
    let fromCall := match funcRetElemTypes.find? (·.1 == fname) with
      | some (_, sn) => [(varName, sn)]
      | none => []
    fromCall ++ propagateReturnElemTypes funcRetElemTypes body
  | .letBind _ v body =>
    propagateReturnElemTypes funcRetElemTypes v ++
    propagateReturnElemTypes funcRetElemTypes body
  | .seq a b =>
    propagateReturnElemTypes funcRetElemTypes a ++
    propagateReturnElemTypes funcRetElemTypes b
  | .ifThenElse c t e =>
    propagateReturnElemTypes funcRetElemTypes c ++
    propagateReturnElemTypes funcRetElemTypes t ++
    propagateReturnElemTypes funcRetElemTypes e
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    propagateReturnElemTypes funcRetElemTypes lo ++
    propagateReturnElemTypes funcRetElemTypes hi ++
    propagateReturnElemTypes funcRetElemTypes body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    propagateReturnElemTypes funcRetElemTypes lo ++
    propagateReturnElemTypes funcRetElemTypes hi ++
    propagateReturnElemTypes funcRetElemTypes body
  | .whileFold c body | .whileFoldReturn c body =>
    propagateReturnElemTypes funcRetElemTypes c ++
    propagateReturnElemTypes funcRetElemTypes body
  | .match_ scrut arms =>
    propagateReturnElemTypes funcRetElemTypes scrut ++
    arms.foldl (fun acc (_, b) => acc ++ propagateReturnElemTypes funcRetElemTypes b) []
  | _ => []

/-! ## Pass D: Fix fold accumulator type for unit-valued outer folds

When a forFoldReturn's inner body returns `()` as its fold value but the outer
fold expects a non-Unit accumulator, there's a type mismatch. Detect patterns
where foldRange uses `()` as accumulator but the body uses cfBreak/cfContinue. -/

-- (Reserved for future use if needed)

/-- Find field names that appear in multiple structs (ambiguous projections). -/
private def findAmbiguousFieldsT (structMeta : StructMeta) : List String :=
  let allFields := structMeta.foldl (fun acc (_, fields) =>
    acc ++ fields.map (·.1)) []
  let dupes := allFields.filter fun f =>
    Nat.blt 1 (allFields.filter (· == f)).length
  dupes.eraseDups

/-! ## Main entry point: `toLeanCertifiedFileT` -/

/-- Typed variant of `toLeanCertifiedFile`. Applies additional type-aware
    AST rewrite passes before delegating to the standard certified file emitter.

    The passes are:
    1. `initMissingFoldAccums` — fix uninitialized fold accumulator variables
    2. `dropConflictingParamTypes` — strip struct type annotations that conflict
       with call-site types
    3. `qualifyProjectionsFromUsage` — resolve ambiguous projections using
       array element type inference
-/
def toLeanCertifiedFileT (defs : List (String × ImpExpr))
    (moduleName : String := "Generated")
    (structMeta : StructMeta := [])
    (fnTypes : List (String × HaxAdapter.FnTypeInfo) := [])
    (callRetTypes : List (String × ImpType) := [])
    (callSigs : List (String × HaxAdapter.FnTypeInfo) := [])
    (varRefTypes : List (String × ImpType) := []) : String :=
  -- Pass A: Fix missing fold accumulators
  let defs := defs.map fun (n, e) =>
    -- Collect function parameters as initially bound names
    let rec getParams : ImpExpr → List String
      | .letBind pn (.var pv) body => if pn == pv then pn :: getParams body else []
      | _ => []
    let params := getParams e
    (n, initMissingFoldAccums params e)
  -- Pass B: Drop conflicting param type annotations
  let structIsPassthrough := computeStructPassthrough structMeta defs
  let structLookup := mkStructLookup structMeta structIsPassthrough
  let fnTypes := reconcileFnTypes defs fnTypes structMeta structLookup callSigs
  -- Pass C: Qualify projections from usage (array element types)
  let ambiguousFields := findAmbiguousFieldsT structMeta
  let defs := if ambiguousFields.isEmpty then defs
    else
      let structNames := structMeta.map (·.1)
      -- Collect array element types and variable struct types across all defs
      let arrayElemTypes := defs.foldl (fun acc (_, e) =>
        acc ++ detectArrayElementTypes e) []
      let varStructTypes := defs.foldl (fun acc (_, e) =>
        acc ++ detectLetBindStructTypes e) []
      -- Filter to only include known struct names
      let arrayElemTypes := arrayElemTypes.filter fun (_, sn) => structNames.contains sn
      let varStructTypes := varStructTypes.filter fun (_, sn) => structNames.contains sn
      -- Cross-function propagation: for each function that pushes StructName into
      -- a returned array, find call sites where the result is bound to a variable.
      -- That variable then also contains StructName elements.
      -- Step 1: For each function, determine what struct type its return array contains.
      -- A function returns StructName elements if it pushes StructName into any array
      -- that's the return value.
      let funcRetElemTypes := defs.filterMap fun (fname, e) =>
        -- Find the last array variable that has push operations with struct constructors
        let pushTypes := detectArrayElementTypes e
        let structPushes := pushTypes.filter fun (_, sn) => structNames.contains sn
        match structPushes.head? with
        | some (_, sn) => some (fname, sn)
        | none => none
      -- Step 2: Find call sites where these functions' results are bound to variables
      let crossFuncElemTypes := defs.foldl (fun acc (_, e) =>
        acc ++ propagateReturnElemTypes funcRetElemTypes e) []
      let allArrayElemTypes := (arrayElemTypes ++ crossFuncElemTypes).eraseDups
      let allVarStructTypes := (varStructTypes ++ crossFuncElemTypes).eraseDups
      if allArrayElemTypes.isEmpty && allVarStructTypes.isEmpty then defs
      else defs.map fun (n, e) =>
        (n, qualifyProjectionsFromUsage allArrayElemTypes allVarStructTypes structMeta ambiguousFields e)
  -- Delegate to the standard certified file emitter
  toLeanCertifiedFile defs moduleName structMeta fnTypes callRetTypes callSigs varRefTypes

end SSProve.Hax

/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.TExpr
public import HaxLean.AnfLowCT
public import HaxLean.PrettyPrint
public import HaxLean.Pipeline
public import HaxLean.HaxAdapter
public import HaxLean.TPhase.AnnotateLets
public import HaxLean.TPhase.InitFoldAccums
public import HaxLean.TPhase.QualifyProjections
public import HaxLean.TPhase.RewriteNewToStructCtor
public import HaxLean.TPhase.RewriteStructFromElem
public import HaxLean.TPhase.FixProjectionPaths

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

@[expose] public section

namespace Hax

/-! ## TExpr Type Utilities -/

/-- Collect all app calls in a TExpr: (functionName, argCount, argTypes, returnType). -/
partial def collectTAppCalls : TExpr → List (String × Nat × List ImpType × ImpType)
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
  -- `.ann e ty` is a type-ascription wrapper; recurse into the payload
  -- so calls beneath the ascription are still discovered.
  | .mk (.ann e) _ => collectTAppCalls e
  | _ => []

/-- Collect names bound by an `ImpPat`. These are introduced as locals
    in the arm body and must extend `bound` for free-var collection. -/
partial def patBinders : ImpPat → List String
  | .varPat n => [n]
  | .tuplePat pats => pats.foldl (fun acc p => acc ++ patBinders p) []
  | .somePat p | .okPat p | .errPat p => patBinders p
  | .ctorPat _ args => args.foldl (fun acc p => acc ++ patBinders p) []
  | .wildcard | .litPat _ | .nonePat => []

/-- Collect free variable references in a TExpr with their types.

    `.ann e ty` wrappers (inserted by `tAnnotateLetBindings`) carry a
    type ascription on `e`. When `e` is a free var (e.g.
    `(ZERO : FieldElement)`), the `.ann`'s outer type is the var's
    effective type — better than the var's intrinsic `.ty` (which is
    often `.unknown` for opaque 0-arity deps). We special-case that
    here so the deps-class renderer can infer `ZERO : FieldElement`
    instead of falling back to `Array Int`.

    For non-var `.ann e` payloads, just recurse into `e` (the outer
    annotation type doesn't directly apply to deeper vars). -/
partial def collectTFreeVars (bound : List String := []) :
    TExpr → List (String × ImpType)
  | .mk (.var n) ty => if bound.contains n then [] else [(n, ty)]
  | .mk (.ann (.mk (.var n) varTy)) annTy =>
    -- Prefer the .ann's outer type when the var's own ty is unknown
    -- (typical for opaque-dep refs whose import-time type is lost).
    let ty := if varTy.isUnknown then annTy else varTy
    if bound.contains n then [] else [(n, ty)]
  | .mk (.ann e) _ => collectTFreeVars bound e
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
    -- Enum-variant heuristic: when all arms are bare `varPat _` (no
    -- structure), the names are likely enum tag references that the
    -- renderer rewrites to `if Hax.beq scrut TAG then …`. Those tags
    -- need to surface as Deps. Pattern-bound vars inside any other
    -- pattern shape (tuplePat, somePat, ctorPat, …) are local
    -- destructure binders and must NOT leak as free vars.
    let allVarPats := arms.all fun (p, _) => match p with
      | .varPat _ => true | .wildcard => true | _ => false
    let patFreeVars := if allVarPats then
      arms.filterMap fun (p, _) => match p with
        | .varPat n => if bound.contains n then none else some (n, ImpType.unknown) | _ => none
    else []
    collectTFreeVars bound scrut ++ patFreeVars ++
    arms.foldl (fun acc (p, b) =>
      acc ++ collectTFreeVars (bound ++ patBinders p) b) []
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
  -- A lambda binds its params in its body; collect captures only.
  | .mk (.lam ps body) _ => collectTFreeVars (ps ++ bound) body
  | _ => []

/-- Extract leading identity let-bindings (let x := x) from a TExpr as parameters
    with their types. -/
def extractTParams : TExpr → List (String × ImpType) × TExpr
  | .mk (.letBind n (.mk (.var v) ty) body) outerTy =>
    if n == v then
      let (ps, rest) := extractTParams body
      ((n, ty) :: ps, rest)
    else ([], .mk (.letBind n (.mk (.var v) ty) body) outerTy)
  | e => ([], e)

/-! ## Typed Deps Class Generation -/

/-- Best-effort merge of two ImpTypes: prefer non-unknown.
    When both are known, prefer the first. -/
def mergeType (a b : ImpType) : ImpType :=
  if a.isUnknown then b else a

/-- Convert an ImpType to Lean type string for the deps class.
    Uses structLookup for ADT resolution.

    Unknown maps to "Array Int" to match the untyped pipeline default.
    Unit is preserved as "Unit" for argument positions (Rust does pass
    `()` literals — e.g. `result.ok_or(())`). The legacy "side-effect
    function" Unit→ArrayInt mapping is only applied to RETURN types
    where `.unit` typically means hax-erased side-effects, not a
    semantic Unit. Callers pass `(isReturn := true)` for return types. -/
def depTypeStr (ty : ImpType) (sl : String → Option String)
    (isReturn : Bool := false) : String :=
  match ty with
  | .unknown => "Array Int"  -- no type info; match untyped default
  | .unit => if isReturn then "Array Int" else "Unit"
  | _ => ty.toLeanTypeStrSurface sl

/-! ## Operator calls on a type parameter

A Rust trait method with an operator name (`Mul::mul`, `Add::add`, `Neg::neg`,
`PartialEq::eq`, …) arrives as the same app head as the integer operator. On an
integer or `Bool` operand the head is a runtime builtin (`Hax.mul`, `Hax.beq`);
on a type-parameter operand it is an external function of the extraction and
belongs to the generated `Deps` class, like any other unresolved trait method.
The adapter parses a generic type parameter as `.slice .int` (an erased `F`
prints as `Array (Int)`), and no Rust operator is defined on a slice of
integers, so that type at the operand identifies the call. -/

/-- The app heads that name a Rust operator method, in the lowercase form of a
    trait-method call and the capitalized form of the binary-op node. -/
def depOperatorNames : List String :=
  ["add", "sub", "mul", "div", "rem", "neg",
   "eq", "ne", "lt", "le", "gt", "ge",
   "not", "and", "or",
   "shl", "shr", "bitand", "bitor", "bitxor", "bitnot",
   "Add", "Sub", "Mul", "Div", "Rem", "Neg",
   "Eq", "Ne", "Lt", "Le", "Gt", "Ge",
   "Not", "And", "Or",
   "Shl", "Shr", "BitAnd", "BitOr", "BitXor"]

/-- The tag appended to an operator head whose operand is a type parameter:
    `mul#dep`. `widthAwareRuntime` renders the tagged head as the bare name. -/
def depOpTag : String := "dep"

/-- Whether an app head is a tagged operator call (`mul#dep`). -/
def isDepOpHead (f : String) : Bool :=
  match f.splitOn "#" with
  | [op, tag] => tag == depOpTag && depOperatorNames.contains op
  | _ => false

/-- The operator name under a `#dep` tag; other heads are returned unchanged. -/
def depOpBaseName (f : String) : String :=
  if isDepOpHead f then (f.splitOn "#").head! else f

/-- Whether a type is the adapter's encoding of a generic type parameter,
    `.slice .int`, under any number of references. -/
def isErasedTypeParam : ImpType → Bool
  | .ref inner _ => isErasedTypeParam inner
  | .slice .int => true
  | _ => false

/-- Tag every operator-named app whose operand is a type parameter with
    `#dep`. The operand type is the first argument's; when that is unknown
    the result type stands in (the operand and result types of an arithmetic
    operator coincide, and a comparison's `Bool` result never qualifies). An
    integer, `Bool` or unknown operand leaves the head unchanged. -/
partial def markDepOperators : TExpr → TExpr
  | .mk (.app f args) ty =>
    let args' := args.map markDepOperators
    let operandTy := match args.head? with
      | some a => if a.ty.isUnknown then ty else a.ty
      | none => ty
    let f' := if depOperatorNames.contains f && isErasedTypeParam operandTy
      then s!"{f}#{depOpTag}" else f
    .mk (.app f' args') ty
  | .mk (.letBind n v b) ty => .mk (.letBind n (markDepOperators v) (markDepOperators b)) ty
  | .mk (.lam ps b) ty => .mk (.lam ps (markDepOperators b)) ty
  | .mk (.tuple es) ty => .mk (.tuple (es.map markDepOperators)) ty
  | .mk (.proj e i) ty => .mk (.proj (markDepOperators e) i) ty
  | .mk (.ifThenElse c t e) ty =>
    .mk (.ifThenElse (markDepOperators c) (markDepOperators t) (markDepOperators e)) ty
  | .mk (.match_ s arms) ty =>
    .mk (.match_ (markDepOperators s) (arms.map fun (p, e) => (p, markDepOperators e))) ty
  | .mk (.seq a b) ty => .mk (.seq (markDepOperators a) (markDepOperators b)) ty
  | .mk (.borrow e) ty => .mk (.borrow (markDepOperators e)) ty
  | .mk (.deref e) ty => .mk (.deref (markDepOperators e)) ty
  | .mk (.assign n r) ty => .mk (.assign n (markDepOperators r)) ty
  | .mk (.forLoop v l h b) ty =>
    .mk (.forLoop v (markDepOperators l) (markDepOperators h) (markDepOperators b)) ty
  | .mk (.forLoopRev v l h b) ty =>
    .mk (.forLoopRev v (markDepOperators l) (markDepOperators h) (markDepOperators b)) ty
  | .mk (.whileLoop c b) ty => .mk (.whileLoop (markDepOperators c) (markDepOperators b)) ty
  | .mk (.break_ (some e)) ty => .mk (.break_ (some (markDepOperators e))) ty
  | .mk (.earlyReturn e) ty => .mk (.earlyReturn (markDepOperators e)) ty
  | .mk (.questionMark e) ty => .mk (.questionMark (markDepOperators e)) ty
  | .mk (.forFold v l h b) ty =>
    .mk (.forFold v (markDepOperators l) (markDepOperators h) (markDepOperators b)) ty
  | .mk (.forFoldRev v l h b) ty =>
    .mk (.forFoldRev v (markDepOperators l) (markDepOperators h) (markDepOperators b)) ty
  | .mk (.whileFold c b) ty => .mk (.whileFold (markDepOperators c) (markDepOperators b)) ty
  | .mk (.forFoldReturn v l h b) ty =>
    .mk (.forFoldReturn v (markDepOperators l) (markDepOperators h) (markDepOperators b)) ty
  | .mk (.forFoldRevReturn v l h b) ty =>
    .mk (.forFoldRevReturn v (markDepOperators l) (markDepOperators h) (markDepOperators b)) ty
  | .mk (.whileFoldReturn c b) ty =>
    .mk (.whileFoldReturn (markDepOperators c) (markDepOperators b)) ty
  | .mk (.cfBreak e) ty => .mk (.cfBreak (markDepOperators e)) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue (markDepOperators e)) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (markDepOperators e)) ty
  | .mk (.ann e) ty => .mk (.ann (markDepOperators e)) ty
  | .mk (.namedProj t e) ty => .mk (.namedProj t (markDepOperators e)) ty
  | e => e

/-- Remove the `#dep` tags of `markDepOperators` from an erased body: the
    `ImpExpr` literal emitted for the agreement proof carries the untagged
    heads. -/
def unmarkDepOperators (e : ImpExpr) : ImpExpr :=
  depOperatorNames.foldl (fun acc op => rewriteAppName s!"{op}#{depOpTag}" op acc) e

set_option linter.unusedVariables false in
/-- Walk a (post-pipeline) `TExpr` and collect `(varName, annType)` pairs
    from every `.ann (.var v) ty` pattern. These are the type ascriptions
    inserted by `tAnnotateLetBindings` on let-binding RHSs; pulling them
    here lets the deps-class renderer recover types for 0-arity opaque
    consts (e.g. `Self::ONE`) whose `.var`-level type info was lost
    during the hax import / pipeline roundtrip. -/
partial def collectAnnVarTypes : TExpr → List (String × ImpType)
  | .mk (.ann (.mk (.var n) _)) annTy => [(n, annTy)]
  | .mk (.ann e) _ => collectAnnVarTypes e
  | .mk (.app _ args) _ => args.foldl (fun acc a => acc ++ collectAnnVarTypes a) []
  | .mk (.letBind _ v body) _ => collectAnnVarTypes v ++ collectAnnVarTypes body
  | .mk (.seq a b) _ => collectAnnVarTypes a ++ collectAnnVarTypes b
  | .mk (.ifThenElse c t e) _ =>
    collectAnnVarTypes c ++ collectAnnVarTypes t ++ collectAnnVarTypes e
  | .mk (.tuple es) _ => es.foldl (fun acc e => acc ++ collectAnnVarTypes e) []
  | .mk (.proj e _) _ => collectAnnVarTypes e
  | .mk (.match_ scrut arms) _ =>
    collectAnnVarTypes scrut ++ arms.foldl (fun acc (_, b) => acc ++ collectAnnVarTypes b) []
  | .mk (.forLoop _ lo hi body) _ | .mk (.forLoopRev _ lo hi body) _
  | .mk (.forFold _ lo hi body) _ | .mk (.forFoldRev _ lo hi body) _
  | .mk (.forFoldReturn _ lo hi body) _ | .mk (.forFoldRevReturn _ lo hi body) _ =>
    collectAnnVarTypes lo ++ collectAnnVarTypes hi ++ collectAnnVarTypes body
  | .mk (.whileLoop c body) _ | .mk (.whileFold c body) _ | .mk (.whileFoldReturn c body) _ =>
    collectAnnVarTypes c ++ collectAnnVarTypes body
  | .mk (.borrow e) _ | .mk (.deref e) _ | .mk (.assign _ e) _
  | .mk (.earlyReturn e) _ | .mk (.questionMark e) _
  | .mk (.cfBreak e) _ | .mk (.cfContinue e) _ | .mk (.cfBreakContinue e) _ =>
    collectAnnVarTypes e
  | .mk (.break_ (some e)) _ => collectAnnVarTypes e
  | _ => []

/-! ## One `Deps` field, one type

A name the export does not define becomes a field of the generated `Deps`
class, and a field has a single type. Every site that uses the name has to
agree on it.

A trait `impl` the crate defines is emitted as top-level definitions at the
concrete self type (`HaxAdapter.buildTraitImplMethodMap`). Its method bodies
reach the self type's components through the trait methods and associated
constants of a *further* `impl` — of a dependency crate, or of a type the
export does not define — which stay opaque. When the crate is also generic
over the same trait, its generic functions call those same names at a type
parameter, which the adapter parses as `.slice .int`. The two readings of one
name are then two types, and only one of them can be the field's.

Whether they are two types is a question about the emitted surface, not about
the hax types: a newtype over `[u64; 5]` and a type parameter both print as
`Array (Int)` and agree, while a newtype over a type the export does not define
prints as that type's axiom and does not. `depTypeStr` with the preamble's
struct lookup is the printer that decides it. -/

/-- The emitted signature of one call site: its argument types and its result
    type, as the `Deps` class would print them.

    `mkStructLookup` spells the collapsed array type of a pass-through struct
    `Array Int` and `ImpType.toLeanTypeStrSurface` spells it `Array (Int)`; the
    two are one Lean type, so the key carries one spelling. -/
def depSiteKey (argTys : List ImpType) (retTy : ImpType)
    (sl : String → Option String) : String :=
  let key := " → ".intercalate
    (argTys.map (fun t => depTypeStr t sl) ++ [depTypeStr retTy sl true])
  key.replace "Array Int" "Array (Int)"

/-- The `Deps` names that two sites of the same arity use at two emitted types,
    where a method body of a trait `impl` is one of the sites.

    `traitImplDefNames` are the definitions the trait-`impl` resolution
    contributes (the `buildTraitImplMethodMap` names); `sl` is the preamble's
    struct lookup and `newtypeCtorNames` the erased newtype constructors, both
    read exactly as `generatePreambleTyped` reads them. An empty result means
    every `Deps` field has one type, and the `impl`s can be resolved as they
    are; a non-empty one is `HaxAdapter.parseHaxFileWithTExpr`'s
    `resolveTraitImpls := false`. -/
def traitImplDepTypeConflicts (tdefs : List (String × TExpr))
    (traitImplDefNames : List String) (sl : String → Option String)
    (newtypeCtorNames : List String := []) : List String :=
  let definedNames := tdefs.map (·.1)
  -- The `Deps`-field filter of `generatePreambleTyped`, minus the free-var and
  -- lambda-name refinements: a name here is a candidate field, and a name the
  -- filter admits too freely only adds sites that agree.
  let isDepName (f : String) : Bool :=
    !definedNames.contains f && !isFieldProjection f && !f.startsWith "::"
      && (f.splitOn "::").length == 1 && !newtypeCtorNames.contains f
      && (!isAlwaysBuiltin f || isDepOpHead f)
  let sites : List (String × Nat × String × Bool) :=
    tdefs.foldl (init := []) fun acc (fname, te) =>
      let fromTraitImpl := traitImplDefNames.contains fname
      let calls := (collectTAppCalls te).map fun (f, arity, argTys, retTy) =>
        (f, arity, depSiteKey argTys retTy sl, fromTraitImpl)
      let vars := (collectTFreeVars [fname] te).map fun (v, ty) =>
        (v, 0, depSiteKey [] ty sl, fromTraitImpl)
      acc ++ calls ++ vars
  let sites := sites.filter fun (f, _, _, _) => isDepName f
  -- Compared per arity: a name read as a call in one place and as a value in
  -- another describes two different fields, not a disagreement about one.
  let namesAndArities := (sites.map fun (f, arity, _, _) => (f, arity)).eraseDups
  (namesAndArities.filterMap fun (f, arity) =>
    let atArity := sites.filter fun (g, m, _, _) => g == f && m == arity
    let keys := (atArity.map fun (_, _, k, _) => k).eraseDups
    if keys.length > 1 && atArity.any (fun (_, _, _, fromImpl) => fromImpl) then some f
    else none).eraseDups

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
    (procTdefs : List (String × TExpr) := [])
    (newtypes : HaxAdapter.NewtypeMap := [])
    : String × List (String × String) × List String :=
  -- Use processed defs for structural analysis (qualified projections etc.)
  let defs := if processedDefs.isEmpty then tdefs.map fun (n, te) => (n, te.erase) else processedDefs
  let definedNames := defs.map (·.1)
  let structNames := structMeta.map (·.1)
  -- Erased newtype constructors (`struct T(Inner)`, called as `T(x)`) are
  -- rendered as the identity function `«T.mk»` defined by the newtype
  -- preamble (`toLeanCertifiedFileTyped`'s `newtypeBlock`), not as an
  -- unknown call — they must not surface as a `Deps` field. The filter keys
  -- on the source name `T`, which the call sites still carry at this point.
  let newtypeCtorNames := newtypes.map (·.1)
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
  -- axiom or abbrev emitted at the top of the file). For non-clash names,
  -- delegate to a clash-aware version of mkStructLookup so that struct
  -- bodies INLINED via resolveStructType also route clashing field-types
  -- to `<name>_T` instead of expanding them (which would re-introduce the
  -- raw `FieldElement` reference that collides with the Deps method).
  let clashedBaseLookup := mkStructLookup structMeta structIsPassthrough clashSet
  let structLookup : String → Option String := fun name =>
    let short := ImpType.sanitizeAdtShortName name
    if clashSet.contains short then some s!"{short}_T"
    else clashedBaseLookup name
  -- (Use `structLookup` below; `clashedBaseLookup` is exposed so callers
  -- that consult `baseStructLookup` for clash-naïve collection still get
  -- the clash-unaware version.)

  -- App names from processed defs (has qualified projections)
  let allCalls := defs.foldl (fun acc (_, e) => acc ++ collectAppCalls e) []
  let allAppNames := allCalls.map (·.1) |>.eraseDups
  -- Let-bound `.lam` names are local functions (`let f := fun … => …`), applied
  -- by name after closure-call lowering — they must NOT surface as Deps methods.
  let lamNames := procTdefs.foldl (fun acc (_, te) => acc ++ tLamBoundNames te) []
    |>.eraseDups

  -- Typed call info from raw TExprs (for deps class type annotations)
  let allTCalls := tdefs.foldl (fun acc (_, te) => acc ++ collectTAppCalls te) []

  -- Free variables from processed defs (structural analysis)
  let allFreeVars := defs.foldl (fun acc (fname, e) =>
    acc ++ collectFreeVars [fname] e) ([] : List String)
  let freeVarDeps := allFreeVars.eraseDups.filter fun v =>
    !definedNames.contains v &&
    !structNames.contains v && !isFieldProjection v &&
    !allAppNames.contains v && !lamNames.contains v

  -- Typed free var info from TExprs (for type annotations in deps class).
  -- We pull from two sources:
  --   1. `tdefs` (rawTdefs from hax JSON) — `.var n ty` annotations preserved
  --      from the import. Some 0-arity opaque consts (e.g. `Self::ONE` whose
  --      body is a complex const expression) end up with `ty = .unknown`
  --      here.
  --   2. `procTdefs` (post-pipeline TExprs with `.ann` wrappers from
  --      `tAnnotateLetBindings`) — the `.ann` wrapper carries the let-binding
  --      RHS type, which is the var's effective type at that call site.
  -- We combine both and prefer non-unknown types during dedup.
  let allTFreeVars := tdefs.foldl (fun acc (fname, te) =>
    acc ++ collectTFreeVars [fname] te) ([] : List (String × ImpType))
  let annVarTypes := procTdefs.foldl (fun acc (_, te) =>
    acc ++ collectAnnVarTypes te) ([] : List (String × ImpType))
  let allTFreeVarsCombined := allTFreeVars ++ annVarTypes
  -- Dedup with type preference: when the same var appears multiple times with
  -- different types, prefer a non-unknown type over `.unknown`.
  let allTFreeVarsDedup := allTFreeVarsCombined.foldl (fun (acc : List (String × ImpType)) (n, ty) =>
    match acc.find? (·.1 == n) with
    | none => acc ++ [(n, ty)]
    | some (_, existingTy) =>
      if existingTy.isUnknown && !ty.isUnknown then
        acc.map (fun (n', t') => if n' == n then (n', ty) else (n', t'))
      else acc) []

  -- All dependency names (function calls + free variables)
  let allNamesWithVars := (allAppNames ++ freeVarDeps).eraseDups
  let deps := allNamesWithVars.filter fun f =>
    !definedNames.contains f &&
    !structNames.contains f && !isFieldProjection f &&
    !lamNames.contains f &&
    -- Filter out the renderer's marker functions (`::namedProj::T`).
    -- These are TCB-emitted into the post-pipeline ImpExpr to
    -- communicate type info to `toLean`; they are not real Deps
    -- methods and must not appear in the Deps class. The legacy
    -- `::annot::T` marker was retired by P1 in favour of the
    -- first-class `ImpExpr.typeAscription` AST node, which never
    -- appears as an `.app` head so this filter doesn't see it.
    !f.startsWith "::" &&
    -- Qualified enum-variant heads (`E::V`) are constructors of the emitted
    -- inductive, not Deps methods.
    (f.splitOn "::").length == 1 &&
    -- Erased newtype constructors are defined by the newtype preamble
    -- (see `newtypeCtorNames` above), not opaque Deps methods.
    !newtypeCtorNames.contains f &&
    -- A `#dep`-tagged operator call is an external trait method
    -- (`markDepOperators`); its field is named by the bare operator.
    (!isAlwaysBuiltin f || freeVarDeps.contains f || isDepOpHead f)

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
        let projectionsUsed := (fields.any fun (fname, _, _) =>
            allAppNames.contains s!".{fname}" || allAppNames.contains s!"{sname}.{fname}")
          || allAppNames.any (·.startsWith s!"struct_update#{sname}#")
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
          s!"  {sanitizeName (depOpBaseName d)} : {retStr}"
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
          s!"  {sanitizeName (depOpBaseName d)} {paramStr} : {retStr}"
      let exportList := depInfo.map (fun (d, _, _, _) => sanitizeName (depOpBaseName d))
        |> " ".intercalate
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
    (boolNames : List String := [])
    (mutWriteRets : List (String × List String × Bool) := []) : String :=
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
  -- A tuple-form `&mut` write-back callee (`mutWriteRets`) returns its Rust
  -- result, when it carries one, paired with the parameters it writes back, so
  -- its annotation is the product of their types in that order. A component
  -- type the renderer cannot spell leaves the annotation off, as an
  -- unannotated parameter does.
  let retTyStr : String :=
    let ty := rawBody.ty
    let s := ty.toLeanTypeStrSurface structLookup
    match mutWriteRets.find? (·.1 == name) with
    | some (_, wbNames, hasRes) =>
      let comps : List (Option ImpType) :=
        (if hasRes then [some ty] else []) ++
          wbNames.map fun v => (tparams.find? (·.1 == v)).map (·.2)
      let strs : List (Option String) := comps.map fun t =>
        match t with
        | none => none
        | some t =>
          if t.isUnknown then none
          else
            let str := t.toLeanTypeStrSurface structLookup
            if str == "Unit" || str.isEmpty then none
            else if (str.splitOn " × ").length > 1 then some s!"({str})"
            else some str
      if !allParamsTyped || strs.isEmpty || strs.any (·.isNone) then ""
      else s!" : {" × ".intercalate (strs.filterMap id)}"
    | none =>
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
  let body := Hax.stripFunctionTailCfBreak body
  let bodyStr := toLean body 1 boolNames
  s!"def {sanitizeName name}{paramStr}{retTyStr} :=\n{bodyStr}\n"

/-! ## Typed Struct New Expansion

`procTdefs` lose type info due to the erase/lift roundtrip in `parseHaxItemTExpr`.
But `rawTdefs` preserve hax JSON types. We collect struct types for `new()` calls
from rawTdefs, then apply the rewrites to ImpExpr defs after erasure. -/

/-- Resolve an ImpType to a struct in the metadata.
    Matches `.adt name _` against struct names (full path or short name). -/
def resolveStructFromType (ty : ImpType) (structMeta : StructMeta)
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
partial def collectNewStructTypes (structMeta : StructMeta) : TExpr → List String
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
def defaultFieldImpExpr (tag : String) (fty : ImpType) : ImpExpr :=
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
    verified `.namedProj` constructor and the TCB renderer.

    Also rewrites a `.proj e i` node whose receiver `e` has a known tuple
    type (`e.ty = .tuple elems` with at least two elements) to the same
    `::proj::<path>` marker `markProjChainWith` uses for destructuring
    chains, with `path` the projection path of component `i` in an
    `elems.length`-ary right-nested tuple (`PrettyPrint.projPath`). This
    covers a `.proj` reachable from a typed receiver even outside a
    destructuring chain, so `toLean`'s untyped `.proj` fallback (which
    prints an unknown identifier for any component past `0`) is only
    reached when the receiver's tuple arity truly cannot be recovered
    from the hax-provided type. -/
partial def markNamedProj : TExpr → TExpr
  | .mk (.namedProj tname e) ty =>
    .mk (.app s!"::namedProj::{tname}" [markNamedProj e]) ty
  | .mk (.app f args) ty => .mk (.app f (args.map markNamedProj)) ty
  | .mk (.letBind n v b) ty => .mk (.letBind n (markNamedProj v) (markNamedProj b)) ty
  | .mk (.tuple es) ty => .mk (.tuple (es.map markNamedProj)) ty
  | .mk (.proj e i) ty =>
    let e' := markNamedProj e
    match e'.ty with
    | .tuple elems =>
      if elems.length ≥ 2 then .mk (.app s!"::proj::{projPath i elems.length}" [e']) ty
      else .mk (.proj e' i) ty
    | _ => .mk (.proj e' i) ty
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

/-! ## Certified Extraction: TExpr Literal Emitter

Emits the typed term of a generated definition as a Lean constructor term,
beside the `ImpExpr` literal that `TExpr.erase` maps it to. The types of the
nodes come from the pipelined `TExpr`; the tree comes from the emitted
`ImpExpr`, so the two literals agree by `rfl`. -/

/-- An `IntWidth` as Lean constructor syntax. -/
def widthToConstructor : IntWidth → String
  | .w8 => ".w8" | .w16 => ".w16" | .w32 => ".w32"
  | .w64 => ".w64" | .w128 => ".w128" | .wsize => ".wsize"

/-- An `ImpType` as Lean constructor syntax. -/
partial def impTypeToConstructor : ImpType → String
  | .bool => ".bool"
  | .int => ".int"
  | .uint w => s!"(.uint {widthToConstructor w})"
  | .sint w => s!"(.sint {widthToConstructor w})"
  | .unit => ".unit"
  | .str => ".str"
  | .tuple elems =>
    s!"(.tuple [{", ".intercalate (elems.map impTypeToConstructor)}])"
  | .option inner => s!"(.option {impTypeToConstructor inner})"
  | .result ok err =>
    s!"(.result {impTypeToConstructor ok} {impTypeToConstructor err})"
  | .controlFlow brk cont =>
    s!"(.controlFlow {impTypeToConstructor brk} {impTypeToConstructor cont})"
  | .adt name args =>
    s!"(.adt \"{name}\" [{", ".intercalate (args.map impTypeToConstructor)}])"
  | .fn params ret =>
    s!"(.fn [{", ".intercalate (params.map impTypeToConstructor)}] {impTypeToConstructor ret})"
  | .ref inner isMut => s!"(.ref {impTypeToConstructor inner} {isMut})"
  | .slice inner => s!"(.slice {impTypeToConstructor inner})"
  | .array inner len => s!"(.array {impTypeToConstructor inner} {len})"
  | .typeVar name => s!"(.typeVar \"{name}\")"
  | .unknown => ".unknown"

/-- The `TExpr` carrying no type information. -/
def unknownTExpr : TExpr := .mk .unitVal .unknown

/-- Drop the `.ann` markers at the root of a `TExpr`. -/
partial def stripTAnn : TExpr → TExpr
  | .mk (.ann e) _ => stripTAnn e
  | t => t

/-- Whether an `ImpExpr` and a `TExprKind` have the same head constructor.
    `.namedProj` heads the `.0` projection it erases to, and `.ann` heads a
    type ascription. -/
def sameHead : ImpExpr → TExprKind → Bool
  | .lit _, .lit _ => true
  | .var _, .var _ => true
  | .letBind _ _ _, .letBind _ _ _ => true
  | .lam _ _, .lam _ _ => true
  | .app f _, .namedProj _ _ => f == ".0"
  | .app _ _, .app _ _ => true
  | .tuple _, .tuple _ => true
  | .proj _ _, .proj _ _ => true
  | .ifThenElse _ _ _, .ifThenElse _ _ _ => true
  | .match_ _ _, .match_ _ _ => true
  | .unitVal, .unitVal => true
  | .seq _ _, .seq _ _ => true
  | .borrow _, .borrow _ => true
  | .deref _, .deref _ => true
  | .assign _ _, .assign _ _ => true
  | .forLoop _ _ _ _, .forLoop _ _ _ _ => true
  | .forLoopRev _ _ _ _, .forLoopRev _ _ _ _ => true
  | .whileLoop _ _, .whileLoop _ _ => true
  | .break_ _, .break_ _ => true
  | .continue_, .continue_ => true
  | .earlyReturn _, .earlyReturn _ => true
  | .questionMark _, .questionMark _ => true
  | .forFold _ _ _ _, .forFold _ _ _ _ => true
  | .forFoldRev _ _ _ _, .forFoldRev _ _ _ _ => true
  | .whileFold _ _, .whileFold _ _ => true
  | .forFoldReturn _ _ _ _, .forFoldReturn _ _ _ _ => true
  | .forFoldRevReturn _ _ _ _, .forFoldRevReturn _ _ _ _ => true
  | .whileFoldReturn _ _, .whileFoldReturn _ _ => true
  | .cfBreak _, .cfBreak _ => true
  | .cfContinue _, .cfContinue _ => true
  | .cfBreakContinue _, .cfBreakContinue _ => true
  | .typeAscription _ _, .ann _ => true
  | _, _ => false

/-- The immediate sub-expressions of a `TExpr`, in constructor order; a
    `match_`'s scrutinee comes first, followed by the arm bodies. -/
def tChildren : TExpr → List TExpr
  | .mk (.letBind _ v b) _ => [v, b]
  | .mk (.lam _ b) _ => [b]
  | .mk (.app _ args) _ => args
  | .mk (.tuple elems) _ => elems
  | .mk (.proj e _) _ => [e]
  | .mk (.ifThenElse c t e) _ => [c, t, e]
  | .mk (.match_ scrut arms) _ => scrut :: arms.map (·.2)
  | .mk (.seq a b) _ => [a, b]
  | .mk (.borrow e) _ => [e]
  | .mk (.deref e) _ => [e]
  | .mk (.assign _ r) _ => [r]
  | .mk (.forLoop _ l h b) _ => [l, h, b]
  | .mk (.forLoopRev _ l h b) _ => [l, h, b]
  | .mk (.whileLoop c b) _ => [c, b]
  | .mk (.break_ (some e)) _ => [e]
  | .mk (.earlyReturn e) _ => [e]
  | .mk (.questionMark e) _ => [e]
  | .mk (.forFold _ l h b) _ => [l, h, b]
  | .mk (.forFoldRev _ l h b) _ => [l, h, b]
  | .mk (.whileFold c b) _ => [c, b]
  | .mk (.forFoldReturn _ l h b) _ => [l, h, b]
  | .mk (.forFoldRevReturn _ l h b) _ => [l, h, b]
  | .mk (.whileFoldReturn c b) _ => [c, b]
  | .mk (.cfBreak e) _ => [e]
  | .mk (.cfContinue e) _ => [e]
  | .mk (.cfBreakContinue e) _ => [e]
  | .mk (.ann e) _ => [e]
  | .mk (.namedProj _ e) _ => [e]
  | _ => []

/-- Rebuild `e` as a `TExpr`, taking each node's type from the node of `t` at
    the same position when the two have the same head constructor and
    `.unknown` otherwise. The tree is `e`'s, so `TExpr.erase` maps the result
    back to `e` for every `e` without a `.typeAscription` node. -/
partial def retypeWith (e : ImpExpr) (t : TExpr) : TExpr :=
  let t := stripTAnn t
  let ok := sameHead e t.kind
  let ty := if ok then t.ty else .unknown
  let cs := if ok then tChildren t else []
  let sub (i : Nat) (x : ImpExpr) : TExpr := retypeWith x (cs.getD i unknownTExpr)
  match e with
  | .lit v => .mk (.lit v) ty
  | .var n => .mk (.var n) ty
  | .unitVal => .mk .unitVal ty
  | .continue_ => .mk .continue_ ty
  | .letBind n v b => .mk (.letBind n (sub 0 v) (sub 1 b)) ty
  | .lam ps b => .mk (.lam ps (sub 0 b)) ty
  | .app f args => .mk (.app f (args.mapIdx fun i a => sub i a)) ty
  | .tuple elems => .mk (.tuple (elems.mapIdx fun i a => sub i a)) ty
  | .proj x i => .mk (.proj (sub 0 x) i) ty
  | .ifThenElse c th el => .mk (.ifThenElse (sub 0 c) (sub 1 th) (sub 2 el)) ty
  | .match_ scrut arms =>
    .mk (.match_ (sub 0 scrut) (arms.mapIdx fun i (p, b) => (p, sub (i + 1) b))) ty
  | .seq a b => .mk (.seq (sub 0 a) (sub 1 b)) ty
  | .borrow x => .mk (.borrow (sub 0 x)) ty
  | .deref x => .mk (.deref (sub 0 x)) ty
  | .assign n r => .mk (.assign n (sub 0 r)) ty
  | .forLoop v l h b => .mk (.forLoop v (sub 0 l) (sub 1 h) (sub 2 b)) ty
  | .forLoopRev v l h b => .mk (.forLoopRev v (sub 0 l) (sub 1 h) (sub 2 b)) ty
  | .whileLoop c b => .mk (.whileLoop (sub 0 c) (sub 1 b)) ty
  | .break_ (some x) => .mk (.break_ (some (sub 0 x))) ty
  | .break_ none => .mk (.break_ none) ty
  | .earlyReturn x => .mk (.earlyReturn (sub 0 x)) ty
  | .questionMark x => .mk (.questionMark (sub 0 x)) ty
  | .forFold v l h b => .mk (.forFold v (sub 0 l) (sub 1 h) (sub 2 b)) ty
  | .forFoldRev v l h b => .mk (.forFoldRev v (sub 0 l) (sub 1 h) (sub 2 b)) ty
  | .whileFold c b => .mk (.whileFold (sub 0 c) (sub 1 b)) ty
  | .forFoldReturn v l h b => .mk (.forFoldReturn v (sub 0 l) (sub 1 h) (sub 2 b)) ty
  | .forFoldRevReturn v l h b =>
    .mk (.forFoldRevReturn v (sub 0 l) (sub 1 h) (sub 2 b)) ty
  | .whileFoldReturn c b => .mk (.whileFoldReturn (sub 0 c) (sub 1 b)) ty
  | .cfBreak x => .mk (.cfBreak (sub 0 x)) ty
  | .cfContinue x => .mk (.cfContinue (sub 0 x)) ty
  | .cfBreakContinue x => .mk (.cfBreakContinue (sub 0 x)) ty
  | .typeAscription x _ => .mk (.ann (sub 0 x)) ty

/-- Emit a `TExpr` as Lean constructor syntax. `tyName` supplies the
    abbreviation a file shares for a rendered type. -/
partial def toLeanTExpr (tyName : String → Option String) (t : TExpr) : String :=
  let rec' := toLeanTExpr tyName
  let kindStr :=
    match t.kind with
    | .lit l => s!"(.lit ({litToConstructor l}))"
    | .var n => s!"(.var \"{n}\")"
    | .unitVal => ".unitVal"
    | .continue_ => ".continue_"
    | .letBind n v b => s!"(.letBind \"{n}\" {rec' v} {rec' b})"
    | .lam ps b =>
      s!"(.lam [{", ".intercalate (ps.map (fun p => s!"\"{p}\""))}] {rec' b})"
    | .app f args => s!"(.app \"{f}\" [{", ".intercalate (args.map rec')}])"
    | .tuple elems => s!"(.tuple [{", ".intercalate (elems.map rec')}])"
    | .proj e i => s!"(.proj {rec' e} {i})"
    | .ifThenElse c th el => s!"(.ifThenElse {rec' c} {rec' th} {rec' el})"
    | .match_ scrut arms =>
      let armStrs := arms.map fun (p, body) =>
        s!"({patToConstructor p}, {rec' body})"
      s!"(.match_ {rec' scrut} [{", ".intercalate armStrs}])"
    | .seq a b => s!"(.seq {rec' a} {rec' b})"
    | .borrow e => s!"(.borrow {rec' e})"
    | .deref e => s!"(.deref {rec' e})"
    | .assign n r => s!"(.assign \"{n}\" {rec' r})"
    | .forLoop v l h b => s!"(.forLoop \"{v}\" {rec' l} {rec' h} {rec' b})"
    | .forLoopRev v l h b => s!"(.forLoopRev \"{v}\" {rec' l} {rec' h} {rec' b})"
    | .whileLoop c b => s!"(.whileLoop {rec' c} {rec' b})"
    | .break_ (some e) => s!"(.break_ (some {rec' e}))"
    | .break_ none => "(.break_ none)"
    | .earlyReturn e => s!"(.earlyReturn {rec' e})"
    | .questionMark e => s!"(.questionMark {rec' e})"
    | .forFold v l h b => s!"(.forFold \"{v}\" {rec' l} {rec' h} {rec' b})"
    | .forFoldRev v l h b => s!"(.forFoldRev \"{v}\" {rec' l} {rec' h} {rec' b})"
    | .whileFold c b => s!"(.whileFold {rec' c} {rec' b})"
    | .forFoldReturn v l h b =>
      s!"(.forFoldReturn \"{v}\" {rec' l} {rec' h} {rec' b})"
    | .forFoldRevReturn v l h b =>
      s!"(.forFoldRevReturn \"{v}\" {rec' l} {rec' h} {rec' b})"
    | .whileFoldReturn c b => s!"(.whileFoldReturn {rec' c} {rec' b})"
    | .cfBreak e => s!"(.cfBreak {rec' e})"
    | .cfContinue e => s!"(.cfContinue {rec' e})"
    | .cfBreakContinue e => s!"(.cfBreakContinue {rec' e})"
    | .ann e => s!"(.ann {rec' e})"
    | .namedProj n e => s!"(.namedProj \"{n}\" {rec' e})"
  let tyStr :=
    let s := impTypeToConstructor t.ty
    (tyName s).getD s
  s!"(.mk {kindStr} {tyStr})"

/-- The rendered type of every node of a `TExpr`, with multiplicity. -/
partial def collectTyStrs (t : TExpr) : List String :=
  impTypeToConstructor t.ty :: (tChildren t).foldl (fun acc c => acc ++ collectTyStrs c) []

/-- Abbreviation names, keyed by rendered type, for the types a file's `TExpr`
    literals repeat: those occurring at least twice whose rendering is longer
    than the name replacing it. -/
def mkTyAbbrevs (pfx : String) (tyStrs : List String) : List (String × String) :=
  let sorted := tyStrs.mergeSort (fun a b => a ≤ b)
  let grouped := sorted.foldl (fun acc s =>
    match acc with
    | (k, n) :: tl => if k == s then (k, n + 1) :: tl else (s, 1) :: acc
    | [] => [(s, 1)]) ([] : List (String × Nat))
  let shared := grouped.reverse.filter fun (s, n) => n ≥ 2 && s.length ≥ pfx.length + 3
  shared.mapIdx fun i (s, _) => (s, s!"{pfx}{i}")

/-- The `TExpr` literal of a generated definition. -/
def toLeanTExprDef (tyName : String → Option String) (name : String) (t : TExpr) : String :=
  s!"def {sanitizeName (name ++ "_texpr")} : TExpr :=\n  {toLeanTExpr tyName t}\n"

/-- The erasure identity between a definition's `TExpr` and `ImpExpr`
    literals. -/
def toLeanEraseExample (name : String) : String :=
  s!"example : {sanitizeName (name ++ "_texpr")}.erase = {sanitizeName (name ++ "_impExpr")} := rfl"

/-- Rewrite every newtype tuple-struct construction `.app T args` to
    `.app "T.mk" args`, the name the newtype preamble gives the definitional
    constructor. The bare name `T` belongs to the transparent alias
    `abbrev T := <Inner>`, so the constructor takes the `.mk` suffix, matching
    the `«T.0»` projection. -/
def rewriteNewtypeCtors (newtypes : HaxAdapter.NewtypeMap) (e : ImpExpr) : ImpExpr :=
  newtypes.foldl (fun expr (t, _) => rewriteAppName t s!"{t}.mk" expr) e

/-- The module docstring of a generated extraction, in the `/-! ... -/` form,
    with a trailing newline.

    `moduleName` is the namespace the extraction is emitted under, `crateName`
    the Rust crate the export came from (omitted from the text when empty),
    `depsParametric` says whether the `Deps` class has fields and therefore
    carries a `variable` binder the definitions stand under, `fnCount` is the
    number of extracted functions and `opaqueTypes` the types the extraction
    leaves as `axiom`. -/
def moduleDocstring (moduleName crateName : String) (depsParametric : Bool)
    (fnCount : Nat) (opaqueTypes : List String) : String :=
  let depsClassName := s!"{moduleName}Deps"
  let depsDoc :=
    if depsParametric then
      s!"* `{depsClassName}`: the operations the crate calls and does not define. Every\n  definition below stands under `variable [{depsClassName}]`, so each is\n  parametric in an instance of it, which the consuming side supplies."
    else
      s!"* `{depsClassName}`: the operations the crate calls and does not define. The\n  extraction found none, so the class has no fields; it is emitted because the\n  consuming side names it."
  let opaqueDoc :=
    if opaqueTypes.isEmpty then ""
    else
      let names := String.intercalate ", " (opaqueTypes.map fun n => s!"`{n}`")
      s!"\n* Types the crate does not define, left as `axiom` for the consuming side to\n  instantiate: {names}."
  let crateDesc :=
    if crateName.isEmpty then "the crate" else s!"the Rust crate `{crateName}`"
  let fnWord := if fnCount == 1 then "function" else "functions"
  s!"/-!\n# `{moduleName}`: haxpipeT extraction\n\nThe haxpipeT extraction of {crateDesc},\ntaken from its hax frontend export. Each extracted function gives a Lean\ndefinition, the `ImpExpr` literal of its body and, where the definition's term\nerases to one, the `TExpr` literal carrying its node types; an `example` per\npair states the erasure identity `f_texpr.erase = f_impExpr`.\n\n## Main definitions\n\n{depsDoc}\n* `f`, `f_impExpr` and `f_texpr` for each of the {fnCount} extracted {fnWord}: the\n  surface definition, the literal of its erased body, and the typed literal.{opaqueDoc}\n\nThis file is generated. Extracting the crate again overwrites it, so an edit\nmade here does not survive; change the Rust source or the emitter.\n-/\n"

/-- The `anfLowCT`-normalised companion of a `_impExpr` literal: the same body
    in the let-normalised fragment `CatCrypt.Crypto.Hax.haxToLowCT` reads. -/
def toLeanImpExprAnfDef (name : String) (e : ImpExpr) : String :=
  s!"def {sanitizeName (name ++ "_impExprAnf")} : ImpExpr :=\n  {toLeanImpExpr (anfLowCT e)}\n"

/-- The `LowCT` lowering of the normalised literal. -/
def toLeanLowCTDef (name : String) : String :=
  s!"def {sanitizeName (name ++ "_lowct")} : Option LowCT :=\n  haxToLowCT {sanitizeName (name ++ "_impExprAnf")}\n"

/-- Generate a complete certified Lean 4 file from typed TExpr definitions.
    `rawTdefs` has types preserved from hax JSON (for deps class + param annotations).
    `procTdefs` (optional) has pipeline-processed TExprs (for body rendering).
    If `procTdefs` is empty, bodies are rendered from rawTdefs (erased + pipelined).
    `newtypes` is the JSON-derived newtype map; the renderer uses it to emit
    `abbrev T_T := <Inner>` aliases plus definitional `«T.0»` unwraps.
    `crateName` is the Rust crate the export was taken from; it appears in the
    module docstring and is omitted from it when empty.
    `emitLowCT` adds, beside each verbatim `_impExpr` literal, its
    `anfLowCT`-normalised form and the `haxToLowCT` lowering of that form; the
    file then imports the CatCrypt modules those two definitions name. -/
def toLeanCertifiedFileTyped (rawTdefs : List (String × TExpr))
    (moduleName : String := "Generated")
    (structMeta : StructMeta := [])
    (fnTypes : List (String × HaxAdapter.FnTypeInfo) := [])
    (procTdefs : List (String × TExpr) := [])
    (newtypes : HaxAdapter.NewtypeMap := [])
    (enumMeta : List HaxAdapter.EnumInfo := [])
    (aliasMeta : List HaxAdapter.TypeAliasInfo := [])
    (mutWriteRets : List (String × List String × Bool) := [])
    (crateName : String := "")
    (emitLowCT : Bool := false) : String :=
  -- Deduplicate raw and proc
  let rawTdefs := rawTdefs.foldl (fun (acc : List (String × TExpr)) (n, te) =>
    if acc.any (·.1 == n) then acc else acc ++ [(n, te)]) []
  let procTdefs := procTdefs.foldl (fun (acc : List (String × TExpr)) (n, te) =>
    if acc.any (·.1 == n) then acc else acc ++ [(n, te)]) []
  -- Operator calls on a type parameter are tagged `#dep` in both TExpr
  -- families: the raw one supplies the `Deps` signature, the processed one
  -- the rendered body. The literal below is emitted untagged.
  let rawTdefs := rawTdefs.map fun (n, te) => (n, markDepOperators te)
  let procTdefs := procTdefs.map fun (n, te) => (n, markDepOperators te)
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
  -- The typed terms the `TExpr` literals take their node types from: the
  -- pipelined ones when present, the raw ones otherwise.
  let srcTdefs : List (String × TExpr) :=
    if procTdefs.isEmpty then rawTdefs else procTdefs
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
  let (preamble, projConflicts, axiomClashSet) := generatePreambleTyped rawTdefs moduleName structMeta fnTypes (processedDefs := defs) (procTdefs := procTdefs) (newtypes := newtypes)
  -- Keep the BASE structLookup (no clash augment) for opaque-ADT
  -- collection — augmenting it would make collectOpaqueAdtNames treat
  -- clashing names as known structs and skip them, leaving `Commitment_T`
  -- referenced but unaxiomed.
  let baseStructLookup := structLookup
  -- Clash-aware base lookup: `mkStructLookup` threads clashSet into
  -- `resolveStructType`, so inlined struct bodies route clashing field
  -- types to `<name>_T` instead of expanding them.
  let clashedBaseLookup := mkStructLookup structMeta structIsPassthrough axiomClashSet
  -- Augmented structLookup: clash names route to their `_T` alias.
  -- Used for body emission (toLeanDefTyped) so let-binding type
  -- ascriptions render as `(val : Commitment_T)` instead of
  -- `(val : Commitment)` (which would resolve to the Deps function).
  let structLookup : String → Option String := fun name =>
    let short := ImpType.sanitizeAdtShortName name
    if axiomClashSet.contains short then some s!"{short}_T"
    else clashedBaseLookup name
  -- Rewrite function body projection references for conflicts
  let defs := if projConflicts.isEmpty then defs
    else defs.map fun (n, e) =>
      let e' := projConflicts.foldl (fun expr (unqual, qual) =>
        rewriteAppName unqual qual expr) e
      (n, e')
  -- Newtype constructor call sites take the `«T.mk»` name the newtype
  -- preamble declares. This runs after `generatePreambleTyped`, whose
  -- `Deps`-field filter keys on the source name `T`.
  let defs := if newtypes.isEmpty then defs
    else defs.map fun (n, e) => (n, rewriteNewtypeCtors newtypes e)
  -- Compute dependency names for post-processing
  let definedNames := defs.map (·.1)
  let structNames := structMeta.map (·.1)
  let allCalls := defs.foldl (fun acc (_, e) => acc ++ collectAppCalls e) []
  let allAppNames := allCalls.map (·.1) |>.eraseDups
  let lamNames := procTdefs.foldl (fun acc (_, te) => acc ++ tLamBoundNames te) []
    |>.eraseDups
  let allFreeVars := defs.foldl (fun acc (fname, e) =>
    acc ++ collectFreeVars [fname] e) ([] : List String)
  let freeVarDeps := allFreeVars.eraseDups.filter fun v =>
    !definedNames.contains v &&
    !structNames.contains v && !isFieldProjection v &&
    !allAppNames.contains v && !lamNames.contains v
  let allNamesWithVars := (allAppNames ++ freeVarDeps).eraseDups
  let depNames := allNamesWithVars.filter fun f =>
    !definedNames.contains f &&
    !structNames.contains f && !isFieldProjection f &&
    !lamNames.contains f &&
    !f.startsWith "::" &&  -- exclude renderer markers
    !isAlwaysBuiltin f
  -- Detect guard-recursion for `partial`
  let needsPartial := defs.any fun (n, e) =>
    let rec stripParams : ImpExpr → ImpExpr
      | .letBind _ (.var _) b => stripParams b
      | e => e
    hasGuardRecursion n (stripParams e)
  -- `TExpr` literals: the emitted `ImpExpr` tree carrying the node types of
  -- the typed term. A definition whose rebuilt term does not print the same
  -- `ImpExpr` as its literal — a `.typeAscription` node, which no `TExpr`
  -- constructor erases to — is left without one.
  let texprs : List (String × TExpr) := defs.filterMap fun (n, e0) =>
    let e := unmarkDepOperators e0
    let src := (srcTdefs.find? (·.1 == n) |>.map (·.2)).getD unknownTExpr
    let t := retypeWith e src
    if toLeanImpExpr t.erase == toLeanImpExpr e then some (n, t) else none
  let tyPfx :=
    if (definedNames ++ structNames ++ allAppNames).any (·.startsWith "ty_")
      then "impTy_" else "ty_"
  let tyAbbrevs := mkTyAbbrevs tyPfx (texprs.foldl (fun acc (_, t) => acc ++ collectTyStrs t) [])
  let tyName : String → Option String := fun s =>
    (tyAbbrevs.find? (·.1 == s)).map (·.2)
  let texprTyBlock := if tyAbbrevs.isEmpty then "" else
    "/-- Type annotations shared by the `TExpr` literals. -/\n"
      ++ "\n".intercalate (tyAbbrevs.map fun (s, n) => s!"abbrev {n} : ImpType := {s}")
      ++ "\n\n"
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
  -- And every newtype's inner type, which `newtypeBlock` below names in an
  -- `abbrev <Name> := <Inner>` and in the two definitional wrappers. The
  -- newtype block is emitted from the crate's struct declarations, so it names
  -- the inner type whether or not any body or signature that survives to the
  -- emit mentions it; an opaque inner type reached only that way still needs
  -- its `axiom`, or the alias has no right-hand side.
  let opaqueFromNewtypes := newtypes.foldl (fun acc (_, innerTy) =>
    acc ++ innerTy.collectOpaqueAdtNames baseStructLookup) ([] : List String)
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
  -- `pub type X = T` aliases get emitted as `abbrev X := T`.  Filter their
  -- names out of the axiom set (so we don't emit `axiom Scalar : Type` AND
  -- `abbrev Scalar := Vector UInt8 32` for the same name).
  let isTypeAlias (s : String) : Bool := aliasMeta.any (·.name == s)
  let allOpaque :=
    (opaqueFromFnTypes ++ opaqueFromCalls ++ opaqueFromNewtypes).eraseDups.map renameForClash
  let allOpaque := (allOpaque.filter (fun n =>
    !isNewtypeAlias n && !isEnum n && !isTypeAlias n)).eraseDups
  let axiomsBlock := if allOpaque.isEmpty then ""
    else "/-- Opaque types extracted from hax JSON. Concrete instances are\n    provided by the protocol's bridge-adapter at the CatCrypt surface. -/\n"
      ++ "\n".intercalate (allOpaque.map fun n => s!"axiom {n} : Type") ++ "\n\n"
  -- `pub type X = T` aliases emitted as `abbrev X := T`. Hax resolves
  -- aliases at field-use sites, so these are top-level human-readable
  -- bindings rather than affecting downstream struct field types.
  -- When the body is an ADT referencing a known struct, emit `<Name>_T`
  -- (the tuple-encoded abbrev) instead of inlining the tuple structure,
  -- so cross-references between aliased and unaliased Rust types remain
  -- visible in the Lean output.
  let renderAliasBody (ty : ImpType) : String :=
    match ty with
    | .adt name _ =>
      let short := ImpType.sanitizeAdtShortName name
      if structMeta.any (·.1 == short) then s!"{short}_T"
      else ty.toLeanTypeStrPrecise baseStructLookup
    | _ => ty.toLeanTypeStrPrecise baseStructLookup
  let typeAliasBlock : String :=
    if aliasMeta.isEmpty then ""
    else
      let lines := aliasMeta.map fun a =>
        s!"abbrev {a.name} := {renderAliasBody a.body}"
      "/-- `pub type` aliases extracted from hax JSON. Bodies use the resolved\n    underlying type because hax inlines aliases at field-use sites. -/\n"
        ++ "\n".intercalate lines ++ "\n\n"
  -- Inductive datatypes for user-defined Rust enums. Emitting
  -- `inductive T : Type where ...` gives pattern matches
  -- `match x with | .Variant => ...` real constructors to resolve, where
  -- `axiom T : Type` would leave them unresolved.
  let inductiveBlock : String :=
    if enumMeta.isEmpty then ""
    else
      let lines := enumMeta.map fun ei =>
        -- Render `| Name : T1 → T2 → ... → MyEnum` for payload variants.
        -- Payload types go through the clash-augmented `structLookup`, not
        -- `baseStructLookup`: a payload whose type collides with a Deps method
        -- is axiomed as `<name>_T` (see `allOpaque`), so rendering it bare
        -- would reference a name that does not exist. Rust unit structs used as
        -- payloads — `enum E { V(V) }` over `pub struct V;` — are the case that
        -- bites.
        let renderPayload (ty : ImpType) : String :=
          let s := ty.toLeanTypeStrSurface structLookup
          if (s.splitOn " × ").length > 1 || (s.splitOn " → ").length > 1
            then s!"({s})" else s
        let variants := ei.variants.map (fun v =>
          if v.payload.isEmpty then s!"  | {v.name}"
          else
            let arrowChain := " → ".intercalate ((v.payload.map renderPayload) ++ [ei.name])
            s!"  | {v.name} : {arrowChain}") |> "\n".intercalate
        -- An opaque payload is `axiom <T>_T : Type`, which carries no instances,
        -- so an enum over one cannot derive them either.
        let hasOpaquePayload := ei.variants.any fun v =>
          v.payload.any fun ty => allOpaque.contains (renderPayload ty)
        let derivingClause := if hasOpaquePayload then "" else "\n  deriving Inhabited, BEq"
        s!"inductive {ei.name} : Type where\n{variants}{derivingClause}"
      "/-- Rust enum definitions extracted from hax JSON. -/\n"
        ++ "\n\n".intercalate lines ++ "\n\n"
  -- Newtype preamble: emit the alias `abbrev <T> := <Inner>`, the
  -- definitional unwrap `def «<T>.0» x := x`, and the definitional
  -- constructor wrap `def «<T>.mk» x := x` (the inverse of `«<T>.0»`) per
  -- newtype. Hax erases the newtype at the type level, so a source call
  -- `T(x)` is the identity on `x`; without this definition the call's head
  -- would be an unknown function and fall into the `Deps` class (see
  -- `newtypeCtorNames` in `generatePreambleTyped`, which excludes it from
  -- that computation). The constructor carries the `.mk` suffix because the
  -- alias already holds the bare name whenever the clash rename does not
  -- move it to `<T>_T`; `rewriteNewtypeCtors` above rewrites the call sites
  -- to match.
  let newtypeBlock : String :=
    if newtypeRenamed.isEmpty then ""
    else
      let lines := newtypeRenamed.map fun (aliasName, innerStr) =>
        -- Original short name (without `_T`): used for the projection name
        -- and the constructor name.
        let bareName := if aliasName.endsWith "_T" then aliasName.dropRight 2 else aliasName
        s!"abbrev {aliasName} := {innerStr}\nnoncomputable def «{bareName}.0» (x : {aliasName}) : {innerStr} := x\nnoncomputable def «{bareName}.mk» (x : {innerStr}) : {aliasName} := x"
      "/-- Newtype tuple-struct aliases: transparent type equalities\n    with definitional `.0` unwraps and definitional constructors. Inner\n    types may themselves be axiomatized (see the axiom block above). -/\n"
        ++ "\n".intercalate lines ++ "\n\n"
  -- The `Deps` class carries a `variable` binder exactly when it has fields,
  -- so the preamble decides whether the module docstring may call the
  -- definitions parametric in it.
  let depsParametric :=
    (preamble.splitOn s!"variable [{moduleName}Deps]").length > 1
  let moduleDoc := moduleDocstring moduleName crateName depsParametric defs.length allOpaque
  -- The runtime, the AST and the reference semantics are imported under their
  -- `HaxLean.*` names. A bare `Hax.*` module name would resolve against the
  -- upstream `Hax` Rust repo when it is a Lake dependency, whose
  -- `proof-libs/lean/Hax/` has no `Runtime.lean`. The untyped path's
  -- standalone preamble (`PrettyPrint.lean`) is separate. The module docstring
  -- goes between the imports and the options, where `port-to-module.sh` on the
  -- consuming side expects it.
  -- Under `--emit-lowct` the file also names the compiler-side lowering, so it
  -- imports the two CatCrypt modules `_lowct` refers to and opens their
  -- namespaces.
  let lowCTImports :=
    if emitLowCT then
      "import CatCrypt.Crypto.Jasmin.LowCT\nimport CatCrypt.Crypto.Hax.HaxToLowCT\n"
    else ""
  let lowCTOpens :=
    if emitLowCT then
      "open CatCrypt.Crypto.Hax\nopen CatCrypt.Crypto.Jasmin.LowCT\n"
    else ""
  let header := s!"/-\n  Auto-generated by haxpipeT --emit-certified (typed extraction pipeline)\n  Surface code + ImpExpr and TExpr literals for agreement proofs.\n-/\nimport HaxLean.Runtime\nimport HaxLean.AST\nimport HaxLean.TExpr\nimport HaxLean.Semantics\n{lowCTImports}\n{moduleDoc}\nset_option linter.unusedVariables false\nset_option maxRecDepth 2048\n\nnamespace {moduleName}\n\nopen Hax\n{lowCTOpens}\n-- All emitted functions are `noncomputable`: extracted bodies may\n-- depend on Runtime axioms (sha256, bridgeCast, ...) which the Lean\n-- code generator rejects. Verification doesn't require execution.\nnoncomputable section\n\n{axiomsBlock}{inductiveBlock}{newtypeBlock}{preamble}\n{typeAliasBlock}{texprTyBlock}mutual\n\n"
  let body := "\n".intercalate (defs.map fun (n, e) =>
    let fnTi := fnTypes.find? (·.1 == n) |>.map (·.2)
    -- Use rawTdefs for parameter type annotations, defs (post-pipeline ImpExpr) for body
    let surfaceDef := match rawTdefs.find? (·.1 == n) with
      | some (_, rawTe) => toLeanDefTyped n rawTe e (structLookup := structLookup) (structMeta := structMeta) (allFnTypes := fnTypes) (boolNames := boolNames) (mutWriteRets := mutWriteRets)
      | none => toLeanDef n e (fnTypeInfo := fnTi) (structLookup := structLookup) (structMeta := structMeta) (allFnTypes := fnTypes)
    let surfaceDef := if needsPartial then surfaceDef.replace "def " "partial def " else surfaceDef
    s!"{surfaceDef}")
  let impExprs := "\n".intercalate (defs.map fun (n, e) =>
    let impExprDef := toLeanImpExprDef n (unmarkDepOperators e)
    let impExprDef := if needsPartial then impExprDef.replace "def " "partial def " else impExprDef
    s!"{impExprDef}")
  -- A `partial def` is opaque, so the erasure identity is emitted only for a
  -- file whose literals are ordinary definitions.
  let texprBlock := if texprs.isEmpty then "" else
    let ds := "\n".intercalate (texprs.map fun (n, t) =>
      let d := toLeanTExprDef tyName n t
      if needsPartial then d.replace "def " "partial def " else d)
    s!"{ds}\n"
  let exampleBlock := if texprs.isEmpty || needsPartial then "" else
    "\n".intercalate (texprs.map fun (n, _) => toLeanEraseExample n) ++ "\n\n"
  let lowCTBlock :=
    if !emitLowCT then "" else
    let ds := "\n".intercalate (defs.map fun (n, e) =>
      let anfDef := toLeanImpExprAnfDef n (unmarkDepOperators e)
      let anfDef := if needsPartial then anfDef.replace "def " "partial def " else anfDef
      let lowDef := toLeanLowCTDef n
      let lowDef := if needsPartial then lowDef.replace "def " "partial def " else lowDef
      s!"{anfDef}\n{lowDef}")
    s!"{ds}\n"
  let footer :=
    s!"\n{impExprs}\n{lowCTBlock}{texprBlock}end\n\n{exampleBlock}end  -- noncomputable section\n\nend {moduleName}\n"
  fixDepReferences (header ++ body ++ footer) depNames

end Hax

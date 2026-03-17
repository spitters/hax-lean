/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.AST
import SSProve.Hax.ImpType
import SSProve.Hax.TExpr
import Lean.Data.Json

/-!
# Hax AST Adapter

Maps hax's JSON AST format (`Decorated<ExprKind>`) to our `ImpExpr`/`TExpr`.

## Hax JSON format

Hax uses Rust serde with externally tagged enums. An expression is:
```json
{
  "ty": <TyKind>,
  "span": <Span>,
  "contents": {"VariantName": {field1: ..., field2: ...}},
  "hir_id": null | [usize, usize],
  "attributes": [...]
}
```

We extract `contents` (the ExprKind) and `ty`, ignoring `span`, `hir_id`, `attributes`.

## Mapping overview

| Hax ExprKind          | Our ImpExpr              |
|-----------------------|--------------------------|
| `VarRef {id}`         | `.var id.name`           |
| `Literal {lit, neg}`  | `.lit ...`               |
| `If {cond,then,...}`  | `.ifThenElse`            |
| `Call {fun,args,...}`  | `.app f args`            |
| `Let {expr,pat}`      | `.letBind`               |
| `Block {stmts,expr}`  | nested `.seq`            |
| `Match {scrutinee,..}`| `.match_`                |
| `Tuple {fields}`      | `.tuple`                 |
| `Assign {lhs,rhs}`    | `.assign`                |
| `Borrow {arg,...}`     | `.borrow`                |
| `Deref {arg}`          | `.deref`                 |
| `Loop {body}`          | `.whileLoop`             |
| `Break {value,...}`    | `.break_`                |
| `Continue {..}`        | `.continue_`             |
| `Return {value}`       | `.earlyReturn`           |
| `Field {lhs,field}`   | `.proj lhs field_index`  |
| `TupleField {lhs,..}` | `.proj lhs field`        |
| `Binary {op,lhs,rhs}` | `.app op [lhs,rhs]`     |
| `Unary {op,arg}`       | `.app op [arg]`         |
| `Adt(..)`              | `.app ctor [fields]`    |
| `Closure {body,...}`   | body (simplified)        |
| others                 | `.app "unknown" []`     |
-/

namespace SSProve.Hax.HaxAdapter

open Lean (Json ToJson FromJson toJson fromJson?)

/-- Extract the first key from a JSON object by trying common keys. -/
private def firstObjKey (j : Json) : Option String :=
  -- Try pretty-printing and extracting, or try known patterns
  let candidates := ["Add", "Sub", "Mul", "Div", "Rem", "Shl", "Shr",
    "BitAnd", "BitOr", "BitXor", "Eq", "Ne", "Lt", "Le", "Gt", "Ge",
    "Not", "Neg", "Offset"]
  candidates.findSome? fun k =>
    match j.getObjVal? k with
    | .ok _ => some k
    | _ => none

/-! ## Helper: extract name from hax identifiers -/

/-- Extract the last meaningful name from a hax `DefId` path.
    DefId JSON: `{"krate": "...", "path": [{"data": {"TypeNs": "..."}, "disambiguator": 0}, ...]}` -/
private partial def extractDefIdName (j : Json) : String :=
  -- hax DefId may be: {path: [...]} or {contents: {value: {path: [...]}}}
  -- Unwrap to find the object containing "path"
  let inner := match j.getObjVal? "contents" with
    | .ok c => match c.getObjVal? "value" with
      | .ok v => v
      | _ => c
    | _ => j
  match inner.getObjVal? "path" with
  | .ok (.arr segments) =>
    let names := segments.toList.filterMap fun seg =>
      match seg.getObjVal? "data" with
      | .ok (.str s) => some s  -- Simple string variant
      | .ok data =>
        -- Try {TypeNs: name} or {ValueNs: name} etc.
        match data.getObjVal? "TypeNs", data.getObjVal? "ValueNs" with
        | .ok (.str n), _ => some n
        | _, .ok (.str n) => some n
        | _, _ =>
          -- Try other Ns fields
          match data.getObjVal? "MacroNs", data.getObjVal? "LifetimeNs" with
          | .ok (.str n), _ => some n
          | _, .ok (.str n) => some n
          | _, _ => none
      | _ => none
    match names.getLast? with
    | some n => n
    | none =>
      match inner.getObjValAs? String "krate" with
      | .ok k => k
      | _ => "unknown"
  | _ =>
    match inner.getObjValAs? String "krate" with
    | .ok k => k
    | _ => "unknown"

/-- Extract a name from a hax `LocalIdent`.
    LocalIdent JSON: `{"name": "x", "id": ...}` -/
private def extractLocalIdentName (j : Json) : String :=
  match j.getObjValAs? String "name" with
  | .ok n => n
  | _ => "unknown"

/-- Extract the DefId name from an `item` JSON object.
    hax items have structure: `{id, value: {def_id: ...}}` or `{def_id: ...}`. -/
private partial def extractItemDefIdName (item : Json) (fallback : String) : String :=
  let defIdJ := match item.getObjVal? "value" with
    | .ok v => match v.getObjVal? "def_id" with
      | .ok d => some d
      | _ => item.getObjVal? "def_id" |>.toOption
    | _ => item.getObjVal? "def_id" |>.toOption
  match defIdJ with
  | some defId => extractDefIdName defId
  | none => fallback

/-- Extract a function name from a hax expression (for Call).
    If the callee is a GlobalName, extract its item's DefId name.
    Otherwise use a placeholder. -/
private partial def extractCallName (j : Json) : String :=
  -- j is the `fun` expression (a Decorated<ExprKind>)
  match j.getObjVal? "contents" with
  | .ok contents =>
    match contents.getObjVal? "GlobalName" with
    | .ok gn =>
      match gn.getObjVal? "item" with
      | .ok item => extractItemDefIdName item "unknown_fn"
      | _ => "unknown_fn"
    | _ => "indirect_call"
  | _ => "unknown_fn"

/-! ## Type mapping -/

/-- Map hax's BinOp to a string name. -/
private def binOpName (j : Json) : String :=
  match j with
  | .str s => s
  | _ =>
    -- BinOp is an enum: {"Add": null}, {"Sub": null}, etc.
    match firstObjKey j with
    | some k => k
    | none => "binop"

/-- Map hax's UnOp to a string name. -/
private def unOpName (j : Json) : String :=
  match j with
  | .str s => s
  | _ =>
    match firstObjKey j with
    | some k => k
    | none => "unop"

/-- Extract the constant length from a hax `{Const: ...}` generic arg.
    Format: `{Const: {contents: {Literal: {Int: {Uint: ["256", "Usize"]}}}}}` -/
private def extractConstLen (j : Json) : Option Nat :=
  let constJ := match j.getObjVal? "Const" with
    | .ok c => c
    | _ => j
  let contents := match constJ.getObjVal? "contents" with
    | .ok c => c
    | _ => constJ
  match contents.getObjVal? "Literal" with
  | .ok litJ =>
    match litJ.getObjVal? "Int" with
    | .ok intJ =>
      -- Try {Uint: ["256", "Usize"]} or {Int: ["256", "Isize"]}
      let tryVariant (key : String) : Option Nat :=
        match intJ.getObjVal? key with
        | .ok (.arr elems) =>
          match elems.toList.head? with
          | some (.str s) => s.toNat?
          | _ => none
        | _ => none
      (tryVariant "Uint").orElse fun _ => tryVariant "Int"
    | _ => none
  | _ => none

/-- Extract the last TypeNs name from a hax `def_id` path. -/
private def extractAdtPathName (adtInner : Json) : Option String :=
  -- adtInner is the {def_id, generic_args, ...} inside {id, value: ...}
  let defIdJ := match adtInner.getObjVal? "def_id" with
    | .ok d => d
    | _ => adtInner
  -- Navigate: def_id.contents.value.path
  let inner := match defIdJ.getObjVal? "contents" with
    | .ok c => match c.getObjVal? "value" with
      | .ok v => v
      | _ => c
    | _ => defIdJ
  match inner.getObjVal? "path" with
  | .ok (.arr segments) =>
    let names := segments.toList.filterMap fun seg =>
      match seg.getObjVal? "data" with
      | .ok data =>
        match data.getObjVal? "TypeNs" with
        | .ok (.str n) => some n
        | _ => match data.getObjVal? "ValueNs" with
          | .ok (.str n) => some n
          | _ => none
      | _ => none
    names.getLast?
  | _ => none

/-- Extract generic_args from an Adt/Array/Tuple inner value. -/
private def extractGenericArgs (adtInner : Json) : Array Json :=
  -- adtInner might be {id, value: {def_id, generic_args, ...}} or {def_id, generic_args, ...}
  let inner := match adtInner.getObjVal? "value" with
    | .ok v => v
    | _ => adtInner
  match inner.getObjValAs? (Array Json) "generic_args" with
  | .ok args => args
  | _ => #[]

/-- Map hax's TyKind to our ImpType.
    Hax types are wrapped as `{id: N, value: TyKind}`. -/
partial def parseHaxType (j : Json) : ImpType :=
  -- Unwrap {id, value} wrapper from hax JSON (primary format)
  let tyKind := match j.getObjVal? "value" with
    | .ok v => v
    | _ => match j.getObjVal? "kind" with
      | .ok k => k
      | _ => j
  match tyKind with
  | .str "Bool" => .bool
  | .str "Char" => .int  -- approximate
  | .str "Str" => .str
  | .str "Never" => .unknown
  | .str "Error" => .unknown
  | _ =>
    if let .ok inner := tyKind.getObjVal? "Int" then
      -- Signed integer: {"Int": "I8"} or {"Int": {"I32": null}} etc.
      match inner with
      | .str "I8"    => .sint .w8
      | .str "I16"   => .sint .w16
      | .str "I32"   => .sint .w32
      | .str "I64"   => .sint .w64
      | .str "I128"  => .sint .w128
      | .str "Isize" => .sint .wsize
      | _ =>
        -- Try externally-tagged enum: {"I32": null}
        if inner.getObjVal? "I8" |>.isOk then .sint .w8
        else if inner.getObjVal? "I16" |>.isOk then .sint .w16
        else if inner.getObjVal? "I32" |>.isOk then .sint .w32
        else if inner.getObjVal? "I64" |>.isOk then .sint .w64
        else if inner.getObjVal? "I128" |>.isOk then .sint .w128
        else if inner.getObjVal? "Isize" |>.isOk then .sint .wsize
        else .int  -- fallback to arbitrary precision
    else if let .ok inner := tyKind.getObjVal? "Uint" then
      -- Unsigned integer: {"Uint": "U8"} or {"Uint": {"U32": null}} etc.
      match inner with
      | .str "U8"    => .uint .w8
      | .str "U16"   => .uint .w16
      | .str "U32"   => .uint .w32
      | .str "U64"   => .uint .w64
      | .str "U128"  => .uint .w128
      | .str "Usize" => .uint .wsize
      | _ =>
        if inner.getObjVal? "U8" |>.isOk then .uint .w8
        else if inner.getObjVal? "U16" |>.isOk then .uint .w16
        else if inner.getObjVal? "U32" |>.isOk then .uint .w32
        else if inner.getObjVal? "U64" |>.isOk then .uint .w64
        else if inner.getObjVal? "U128" |>.isOk then .uint .w128
        else if inner.getObjVal? "Usize" |>.isOk then .uint .wsize
        else .int  -- fallback
    else if let .ok _ := tyKind.getObjVal? "Float" then .unknown  -- no float in our ImpType
    else if let .ok tupleRef := tyKind.getObjVal? "Tuple" then
      -- Tuple: {id, value: {def_id: ...<tuple_N>..., generic_args: [{Type: t1}, ...]}}
      let genArgs := extractGenericArgs tupleRef
      let elemTypes := genArgs.toList.filterMap fun ga =>
        match ga.getObjVal? "Type" with
        | .ok tyJ => some (parseHaxType tyJ)
        | _ => none
      if elemTypes.isEmpty then .unknown
      else .tuple elemTypes
    else if let .ok refData := tyKind.getObjVal? "Ref" then
      -- Ref(Region, Box<Ty>, Mutability)
      match refData with
      | .arr #[_, inner, mut_] =>
        .ref (parseHaxType inner) (mut_ == .str "Mut")
      | _ => .unknown
    else if let .ok sliceRef := tyKind.getObjVal? "Slice" then
      -- Slice: similar to Array but without const length
      let genArgs := extractGenericArgs sliceRef
      let elemType := genArgs.toList.findSome? fun ga =>
        match ga.getObjVal? "Type" with
        | .ok tyJ => some (parseHaxType tyJ)
        | _ => none
      match elemType with
      | some et => .slice et
      | none => .slice .unknown
    else if let .ok _paramData := tyKind.getObjVal? "Param" then
      -- Generic type parameter: in the untyped extraction model,
      -- crypto type params are almost always byte arrays.
      -- Map to slice (Array Int) as a safe default.
      .slice .int
    else if let .ok arrayRef := tyKind.getObjVal? "Array" then
      -- Array: {id, value: {def_id: ...<array>..., generic_args: [{Type: elemTy}, {Const: len}]}}
      let genArgs := extractGenericArgs arrayRef
      let elemType := genArgs.toList.findSome? fun ga =>
        match ga.getObjVal? "Type" with
        | .ok tyJ => some (parseHaxType tyJ)
        | _ => none
      let len := genArgs.toList.findSome? extractConstLen
      match elemType with
      | some et => .array et (len.getD 0)
      | none => .array .unknown (len.getD 0)
    else if let .ok adtRef := tyKind.getObjVal? "Adt" then
      -- Adt: {id, value: {def_id, generic_args, ...}}
      let adtInner := match adtRef.getObjVal? "value" with
        | .ok v => v
        | _ => adtRef
      let pathName := extractAdtPathName adtInner
      let genArgs := extractGenericArgs adtRef
      let typeArgs := genArgs.toList.filterMap fun ga =>
        match ga.getObjVal? "Type" with
        | .ok tyJ => some (parseHaxType tyJ)
        | _ => none
      match pathName with
      | some n => .adt n typeArgs
      | none => .adt "unknown" typeArgs
    else if let .ok _ := tyKind.getObjVal? "Arrow" then .unknown
    else .unknown

/-! ## Pattern mapping -/

/-- Map hax's `Decorated<PatKind>` to our `ImpPat`. -/
partial def parseHaxPat (j : Json) : ImpPat :=
  -- j is Decorated<PatKind>: {contents: PatKind, ty: ..., span: ...}
  let patKind := match j.getObjVal? "contents" with
    | .ok c => c
    | _ => j
  match patKind with
  | .str "Wild" => .wildcard
  | .str "Missing" => .wildcard
  | .str "Never" => .wildcard
  | _ =>
    if let .ok bindData := patKind.getObjVal? "Binding" then
      match bindData.getObjVal? "var" with
      | .ok varJ => .varPat (extractLocalIdentName varJ)
      | _ => .wildcard
    else if let .ok derefData := patKind.getObjVal? "Deref" then
      -- Deref pattern: unwrap to inner subpattern
      match derefData.getObjVal? "subpattern" with
      | .ok subpat => parseHaxPat subpat
      | _ => .wildcard
    else if let .ok tupleData := patKind.getObjVal? "Tuple" then
      match tupleData.getObjValAs? (Array Json) "subpatterns" with
      | .ok pats => .tuplePat (pats.toList.map parseHaxPat)
      | _ => .wildcard
    else if let .ok constData := patKind.getObjVal? "Constant" then
      -- Constant pattern: try to extract the literal value
      match constData.getObjVal? "value" with
      | .ok valJ => parseConstantPat valJ
      | _ => .wildcard
    else if let .ok variantData := patKind.getObjVal? "Variant" then
      -- Variant pattern: use the variant info
      match variantData.getObjVal? "info" with
      | .ok info =>
        -- hax JSON: info.variant is a DefId (not a string "variant_name")
        let name := match info.getObjVal? "variant" with
          | .ok variantDefId => extractDefIdName variantDefId
          | _ => match info.getObjValAs? String "variant_name" with
            | .ok n => n
            | _ => "Variant"
        -- Get subpatterns
        let subpats := match variantData.getObjValAs? (Array Json) "subpatterns" with
          | .ok fps => fps.toList.filterMap fun fp =>
            match fp.getObjVal? "pattern" with
            | .ok p => some (parseHaxPat p)
            | _ => none
          | _ => []
        match name, subpats with
        | "Some", [p] => .somePat p
        | "None", [] => .nonePat
        | "Ok", [p] => .okPat p
        | "Err", [p] => .errPat p
        | _, _ => .varPat name  -- approximate: treat as a binding
      | _ => .wildcard
    else if let .ok orData := patKind.getObjVal? "Or" then
      -- Or pattern: take the first alternative (simplified)
      match orData.getObjValAs? (Array Json) "pats" with
      | .ok pats => match pats.toList.head? with
        | some p => parseHaxPat p
        | none => .wildcard
      | _ => .wildcard
    else if let .ok ascData := patKind.getObjVal? "AscribeUserType" then
      match ascData.getObjVal? "subpattern" with
      | .ok p => parseHaxPat p
      | _ => .wildcard
    else .wildcard
where
  parseConstantPat (j : Json) : ImpPat :=
    -- ConstantExpr might contain a literal
    match j.getObjVal? "contents" with
    | .ok (.str "Unit") => .litPat .unit
    | .ok contents =>
      if let .ok litData := contents.getObjVal? "Literal" then
        parseLitPat litData
      else .wildcard
    | _ => .wildcard
  parseLitPat (j : Json) : ImpPat :=
    if let .ok b := j.getObjValAs? Bool "Bool" then .litPat (.bool b)
    else if let .ok intData := j.getObjVal? "Int" then
      match intData with
      -- Format: "Int": [n, suffix]
      | .arr #[n, _] =>
        match n.getStr? with
        | .ok s => match s.toInt? with
          | some n => .litPat (.int n)
          | none => .wildcard
        | _ => .wildcard
      -- Format: "Int": {"Uint": [n, suffix]} or "Int": {"Int": [n, suffix]}
      | _ =>
        let tryUint := intData.getObjVal? "Uint"
        let tryInt := intData.getObjVal? "Int"
        match tryUint.toOption.orElse fun _ => tryInt.toOption with
        | some (.arr #[n, _]) =>
          match n.getStr? with
          | .ok s => match s.toInt? with
            | some n => .litPat (.int n)
            | none => .wildcard
          | _ => .wildcard
        | _ => .wildcard
    else .wildcard

/-! ## Expression mapping -/

/-- Map hax's `Decorated<ExprKind>` JSON to our `ImpExpr`.
    Strips metadata (span, hir_id, attributes), keeping only the expression and type. -/
partial def parseHaxExpr (j : Json) : Except String ImpExpr := do
  -- Extract the ExprKind from the Decorated wrapper
  let contents ← j.getObjVal? "contents"
  parseExprKind contents
where
  /-- Parse a hax ExprKind (externally tagged enum). -/
  parseExprKind (j : Json) : Except String ImpExpr := do
    -- Unit variants come as plain strings
    match j with
    | .str "Todo" => return .app "hax_unsupported_Todo" []  -- will cause Lean compile error
    | _ => pure ()

    -- Struct variants: {"VariantName": {fields...}}
    if let .ok data := j.getObjVal? "VarRef" then
      let name := match data.getObjVal? "id" with
        | .ok id => extractLocalIdentName id
        | _ => "unknown_var"
      return .var name

    else if let .ok data := j.getObjVal? "GlobalName" then
      let name := match data.getObjVal? "item" with
        | .ok item => extractItemDefIdName item "global"
        | _ => "global"
      return .var name

    else if let .ok data := j.getObjVal? "Literal" then
      return parseLiteral data

    else if let .ok data := j.getObjVal? "If" then
      let cond ← parseHaxExpr (← data.getObjVal? "cond")
      let thn ← parseHaxExpr (← data.getObjVal? "then")
      let els ← match data.getObjVal? "else_opt" with
        | .ok (.null) => pure .unitVal
        | .ok elsJ => parseHaxExpr elsJ
        | _ => pure .unitVal
      return .ifThenElse cond thn els

    else if let .ok data := j.getObjVal? "Call" then
      let funName := extractCallName (← data.getObjVal? "fun")
      let argsJ ← data.getObjValAs? (Array Json) "args"
      let args ← argsJ.toList.mapM parseHaxExpr
      return .app funName args

    else if let .ok data := j.getObjVal? "Let" then
      let rhs ← parseHaxExpr (← data.getObjVal? "expr")
      let pat := match data.getObjVal? "pat" with
        | .ok p => parseHaxPat p
        | _ => .wildcard
      -- Handle tuple destructuring: let (a, b) = rhs → let _tup := rhs; let a := _tup.1; let b := _tup.2
      match pat with
      | .tuplePat pats =>
        let tmpName := "_tup"
        let bindings := (pats.zip (List.range pats.length)).map fun (p, i) =>
          let name := match p with
            | .varPat n => if n.startsWith "_" then "_" else n
            | _ => "_"
          (name, ImpExpr.proj (.var tmpName) i)
        let inner := bindings.foldr (fun (n, proj) acc => .letBind n proj acc) .unitVal
        return .letBind tmpName rhs inner
      | .varPat n =>
        return .letBind n rhs .unitVal
      | _ =>
        return .letBind "_let" rhs .unitVal

    else if let .ok data := j.getObjVal? "Block" then
      -- Block: {stmts: [...], expr: Option<Expr>, ...}
      -- #[serde(flatten)] means Block fields are inlined into the ExprKind
      let stmts ← match data.getObjValAs? (Array Json) "stmts" with
        | .ok ss => ss.toList.mapM parseStmt
        | _ => pure []
      let tail ← match data.getObjVal? "expr" with
        | .ok (.null) => pure .unitVal
        | .ok e => parseHaxExpr e
        | _ => pure .unitVal
      return stmtsToSeq stmts tail

    else if let .ok data := j.getObjVal? "Match" then
      let scrut ← parseHaxExpr (← data.getObjVal? "scrutinee")
      let armsJ ← data.getObjValAs? (Array Json) "arms"
      let arms ← armsJ.toList.mapM parseArm
      return .match_ scrut arms

    else if let .ok data := j.getObjVal? "Tuple" then
      let fieldsJ ← data.getObjValAs? (Array Json) "fields"
      let fields ← fieldsJ.toList.mapM parseHaxExpr
      if fields.isEmpty then return .unitVal
      return .tuple fields

    else if let .ok data := j.getObjVal? "Array" then
      let fieldsJ ← data.getObjValAs? (Array Json) "fields"
      let fields ← fieldsJ.toList.mapM parseHaxExpr
      return .app "array_lit" fields

    else if let .ok data := j.getObjVal? "Assign" then
      let lhs ← parseHaxExpr (← data.getObjVal? "lhs")
      let rhs ← parseHaxExpr (← data.getObjVal? "rhs")
      -- Strip deref wrappers from LHS (references erased by dropReferences)
      let rec stripD : ImpExpr → ImpExpr
        | .deref e => stripD e
        | e => e
      let lhs' : ImpExpr := stripD lhs
      let getVarName : ImpExpr → String
        | .var n => n
        | .deref (.var n) => n
        | _ => "_assign"
      match lhs' with
      | .var n => return .assign n rhs
      -- Array element assignment: arr[i] = v → assign arr (array_update arr i v)
      | .app "index" [arr, idx] =>
        let arrName := getVarName (stripD arr)
        return .assign arrName (.app "array_update" [arr, idx, rhs])
      | _ => return .assign "_assign" rhs

    else if let .ok data := j.getObjVal? "AssignOp" then
      let rawOp := match data.getObjVal? "op" with
        | .ok opJ => binOpName opJ
        | _ => "op"
      -- Strip "Assign" suffix to get base op (BitXorAssign → BitXor)
      let op := if rawOp.endsWith "Assign" then rawOp.dropRight 6 else rawOp
      let lhs ← parseHaxExpr (← data.getObjVal? "lhs")
      let rhs ← parseHaxExpr (← data.getObjVal? "rhs")
      -- Strip deref wrappers from LHS
      let rec stripD2 : ImpExpr → ImpExpr
        | .deref e => stripD2 e
        | e => e
      let lhs' : ImpExpr := stripD2 lhs
      match lhs' with
      | .var n => return .assign n (.app op [lhs, rhs])
      | .app "index" [arr, idx] =>
        -- arr[i] op= v → assign arr (array_update arr idx (op(arr[i], v)))
        let arrName := match stripD2 arr with
          | .var n => n | .deref (.var n) => n | _ => "_assign"
        return .assign arrName (.app "array_update" [arr, idx, .app op [lhs, rhs]])
      | _ => return .assign "_assign" (.app op [lhs, rhs])

    else if let .ok data := j.getObjVal? "Borrow" then
      let arg ← parseHaxExpr (← data.getObjVal? "arg")
      return .borrow arg

    else if let .ok data := j.getObjVal? "Deref" then
      let arg ← parseHaxExpr (← data.getObjVal? "arg")
      return .deref arg

    else if let .ok data := j.getObjVal? "Loop" then
      let body ← parseHaxExpr (← data.getObjVal? "body")
      -- hax Loop is a general loop (while true), not a for-range
      return .whileLoop (.lit (.bool true)) body

    else if let .ok data := j.getObjVal? "Break" then
      let value ← match data.getObjVal? "value" with
        | .ok (.null) => pure none
        | .ok v => return .break_ (some (← parseHaxExpr v))
        | _ => pure none
      return .break_ value

    else if let .ok _data := j.getObjVal? "Continue" then
      return .continue_

    else if let .ok data := j.getObjVal? "Return" then
      let value ← match data.getObjVal? "value" with
        | .ok (.null) => pure .unitVal
        | .ok v => parseHaxExpr v
        | _ => pure .unitVal
      return .earlyReturn value

    else if let .ok data := j.getObjVal? "Binary" then
      let op := match data.getObjVal? "op" with
        | .ok opJ => binOpName opJ
        | _ => "binop"
      let lhs ← parseHaxExpr (← data.getObjVal? "lhs")
      let rhs ← parseHaxExpr (← data.getObjVal? "rhs")
      return .app op [lhs, rhs]

    else if let .ok data := j.getObjVal? "LogicalOp" then
      let op := match data.getObjVal? "op" with
        | .ok (.str "And") => "&&"
        | .ok (.str "Or") => "||"
        | _ => "logical_op"
      let lhs ← parseHaxExpr (← data.getObjVal? "lhs")
      let rhs ← parseHaxExpr (← data.getObjVal? "rhs")
      return .app op [lhs, rhs]

    else if let .ok data := j.getObjVal? "Unary" then
      let op := match data.getObjVal? "op" with
        | .ok opJ => unOpName opJ
        | _ => "unop"
      let arg ← parseHaxExpr (← data.getObjVal? "arg")
      return .app op [arg]

    else if let .ok data := j.getObjVal? "Field" then
      let lhs ← parseHaxExpr (← data.getObjVal? "lhs")
      let fieldName := match data.getObjVal? "field" with
        | .ok fj => extractDefIdName fj
        | _ => "field"
      return .app ("." ++ fieldName) [lhs]

    else if let .ok data := j.getObjVal? "TupleField" then
      let lhs ← parseHaxExpr (← data.getObjVal? "lhs")
      let idx := match data.getObjValAs? Nat "field" with
        | .ok n => n
        | _ => 0
      return .proj lhs idx

    else if let .ok data := j.getObjVal? "Index" then
      let lhs ← parseHaxExpr (← data.getObjVal? "lhs")
      let index ← parseHaxExpr (← data.getObjVal? "index")
      return .app "index" [lhs, index]

    else if let .ok data := j.getObjVal? "Cast" then
      -- Cast: emit as app "cast" so the pretty-printer can select the right
      -- width-specific cast function using the TExpr type annotation.
      let source ← parseHaxExpr (← data.getObjVal? "source")
      return .app "cast" [source]

    else if let .ok data := j.getObjVal? "Use" then
      parseHaxExpr (← data.getObjVal? "source")

    else if let .ok data := j.getObjVal? "NeverToAny" then
      parseHaxExpr (← data.getObjVal? "source")

    else if let .ok data := j.getObjVal? "Box" then
      parseHaxExpr (← data.getObjVal? "value")

    else if let .ok data := j.getObjVal? "Adt" then
      parseAdtExpr data

    else if let .ok data := j.getObjVal? "Closure" then
      -- Approximate: just use the body
      parseHaxExpr (← data.getObjVal? "body")

    else if let .ok data := j.getObjVal? "Repeat" then
      let value ← parseHaxExpr (← data.getObjVal? "value")
      let count ← match data.getObjVal? "count" with
        | .ok countJ => parseHaxExpr countJ
        | _ => pure (.lit (.int 0))
      return .app "repeat" [value, count]

    else if let .ok data := j.getObjVal? "PlaceTypeAscription" then
      parseHaxExpr (← data.getObjVal? "source")

    else if let .ok data := j.getObjVal? "ValueTypeAscription" then
      parseHaxExpr (← data.getObjVal? "source")

    else if let .ok data := j.getObjVal? "PointerCoercion" then
      parseHaxExpr (← data.getObjVal? "source")

    else if let .ok _data := j.getObjVal? "ConstBlock" then
      return .app "const_block" []

    else if let .ok data := j.getObjVal? "NamedConst" then
      let name := match data.getObjVal? "item" with
        | .ok item => extractItemDefIdName item "const"
        | _ => "const"
      return .var name

    else if let .ok _data := j.getObjVal? "ConstParam" then
      return .var "const_param"

    else if let .ok data := j.getObjVal? "ConstRef" then
      let name := match data.getObjVal? "id" with
        | .ok id => match id.getObjValAs? String "name" with
          | .ok n => n
          | _ => "const_ref"
        | _ => "const_ref"
      return .var name

    else if let .ok data := j.getObjVal? "StaticRef" then
      let name := match data.getObjVal? "def_id" with
        | .ok defId => extractDefIdName defId
        | _ => "static"
      return .var name

    else if let .ok data := j.getObjVal? "Yield" then
      let value ← parseHaxExpr (← data.getObjVal? "value")
      return .app "yield" [value]

    else if let .ok s := j.getObjVal? "Todo" then
      let msg := match s with
        | .str m => m
        | _ => "todo"
      return .app ("todo:" ++ msg) []

    else
      throw s!"unknown hax ExprKind: {j.pretty}"

  /-- Parse a hax literal. -/
  parseLiteral (data : Json) : ImpExpr :=
    -- Literal { lit: Spanned<LitKind>, neg: bool }
    let neg := match data.getObjValAs? Bool "neg" with
      | .ok true => true
      | _ => false
    let litKind := match data.getObjVal? "lit" with
      | .ok spanned => match spanned.getObjVal? "node" with
        | .ok n => n
        | _ => spanned
      | _ => data
    if let .ok b := litKind.getObjValAs? Bool "Bool" then .lit (.bool b)
    else if let .ok intData := litKind.getObjVal? "Int" then
      -- Format 1: "Int": [n_string, suffix]
      -- Format 2: "Int": {"Uint": [n_string, suffix]} or {"Int": [n_string, suffix]}
      let nArr := match intData with
        | .arr a => some a
        | _ =>
          let tryUint := intData.getObjVal? "Uint"
          let tryInt := intData.getObjVal? "Int"
          match (tryUint.toOption.orElse fun _ => tryInt.toOption) with
          | some (.arr a) => some a
          | _ => none
      match nArr with
      | some #[nJ, _] =>
        let n := match nJ.getStr? with
          | .ok s => s.toInt?.getD 0
          | _ => match nJ.getNat? with
            | .ok n => n
            | _ => 0
        .lit (.int (if neg then -n else n))
      | _ => .lit (.int 0)
    else if let .ok bsData := litKind.getObjVal? "ByteStr" then
      -- ByteStr: [[byte0, byte1, ...], "Cooked"]
      match bsData with
      | .arr #[.arr bytes, _] =>
        let byteExprs : List ImpExpr := (bytes.toList.filterMap fun b =>
          match b.getNat? with
          | .ok n => some (ImpExpr.lit (.int n))
          | _ => none)
        .app "array_lit" byteExprs
      | _ => .app "array_lit" []
    else if let .ok _strData := litKind.getObjVal? "Str" then
      -- Str: string literal → opaque in untyped extraction
      .app "literal" []
    else .app "literal" []  -- char, float, etc.

  /-- Parse a hax Stmt (from Block). -/
  parseStmt (j : Json) : Except String ImpExpr := do
    let kind ← j.getObjVal? "kind"
    -- StmtKind is an enum with variants like Expr, Let
    if let .ok data := kind.getObjVal? "Expr" then
      match data.getObjVal? "expr" with
      | .ok e => parseHaxExpr e
      | _ => return .unitVal
    else if let .ok data := kind.getObjVal? "Let" then
      let pat := match data.getObjVal? "pattern" with
        | .ok p => parseHaxPat p
        | _ => .wildcard
      let init ← match data.getObjVal? "initializer" with
        | .ok (.null) => pure .unitVal
        | .ok e => parseHaxExpr e
        | _ => pure .unitVal
      -- Handle tuple destructuring: let (a, b) = rhs → let _tup := rhs; let a := _tup.1; let b := _tup.2
      -- Uses nested letBind so stmtsToSeq can connect the tail properly.
      match pat with
      | .tuplePat pats =>
        let tmpName := "_tup"
        let bindings := (pats.zip (List.range pats.length)).map fun (p, i) =>
          let name := match p with
            | .varPat n => if n.startsWith "_" then "_" else n
            | _ => "_"
          (name, ImpExpr.proj (.var tmpName) i)
        -- Build nested letBinds: letBind _tup rhs (letBind a _tup.0 (letBind b _tup.1 unitVal))
        let inner := bindings.foldr (fun (n, proj) acc => .letBind n proj acc) .unitVal
        return .letBind tmpName init inner
      | .varPat n =>
        return .letBind n init .unitVal  -- body filled in by stmtsToSeq
      | _ =>
        return .letBind "_let" init .unitVal
    else
      return .unitVal

  /-- Replace the deepest unitVal in a letBind chain with a continuation.
      letBind a v1 (letBind b v2 unitVal) → letBind a v1 (letBind b v2 cont) -/
  replaceDeepestUnit (e : ImpExpr) (cont : ImpExpr) : ImpExpr :=
    match e with
    | .letBind n v .unitVal => .letBind n v cont
    | .letBind n v body => .letBind n v (replaceDeepestUnit body cont)
    | _ => .seq e cont

  /-- Convert a list of statement expressions into nested seq/letBind. -/
  stmtsToSeq (stmts : List ImpExpr) (tail : ImpExpr) : ImpExpr :=
    match stmts with
    | [] => tail
    | [s] => replaceDeepestUnit s tail
    | s :: rest => replaceDeepestUnit s (stmtsToSeq rest tail)

  /-- Parse a hax Arm (from Match). -/
  parseArm (j : Json) : Except String (ImpPat × ImpExpr) := do
    let pat := match j.getObjVal? "pattern" with
      | .ok p => parseHaxPat p
      | _ => .wildcard
    let body ← match j.getObjVal? "body" with
      | .ok b => parseHaxExpr b
      | _ => pure .unitVal
    return (pat, body)

  /-- Parse a hax AdtExpr (struct/enum construction). -/
  parseAdtExpr (j : Json) : Except String ImpExpr := do
    -- hax JSON: info.variant is a DefId, info.type_namespace is a DefId
    let name := match j.getObjVal? "info" with
      | .ok info => match info.getObjVal? "variant" with
        | .ok variantDefId => extractDefIdName variantDefId
        | _ => match info.getObjVal? "type_namespace" with
          | .ok nsDefId => extractDefIdName nsDefId
          | _ => match info.getObjValAs? String "variant_name" with
            | .ok n => n
            | _ => "Adt"
      | _ => "Adt"
    let fields ← match j.getObjValAs? (Array Json) "fields" with
      | .ok fs => fs.toList.mapM fun fj =>
        match fj.getObjVal? "value" with
        | .ok v => parseHaxExpr v
        | _ => pure .unitVal
      | _ => pure []
    return .app name fields

/-! ## For-Loop Reconstruction

Hax desugars `for i in lo..hi { body }` into an iterator pattern:
```
match into_iter(Range { start: lo, end: hi }) {
  iter => loop {
    match next(&mut iter) {
      None => break,
      Some(i) => body
    }
  }
}
```

We reconstruct this back to `forLoop` / `forLoopRev` by pattern-matching
on the parsed `ImpExpr`. This mirrors the OCaml hax engine's
`phase_reconstruct_for_loops.ml`.

### Reversed ranges

`for i in (lo..hi).rev()` appears as `into_iter(rev(Range { ... }))`.
We detect `rev` in the call chain and emit `forLoopRev`. -/

/-- Check if a function name is `into_iter` (possibly qualified). -/
private def isIntoIter (f : String) : Bool :=
  f == "into_iter" || f.endsWith "into_iter" ||
  f.endsWith "IntoIterator::into_iter"

/-- Check if a function name is `Iterator::next` (possibly qualified). -/
private def isIterNext (f : String) : Bool :=
  f == "next" || f.endsWith "next" ||
  f.endsWith "Iterator::next" || f.endsWith "Iterator__next"

/-- Check if a function name is `rev` (possibly qualified). -/
private def isRev (f : String) : Bool :=
  f == "rev" || f.endsWith "rev" || f.endsWith "Iterator::rev"

/-- Try to extract Range bounds from a constructor call.
    Hax represents `Range { start, end }` as `app "Range" [lo, hi]`
    or as `app "Range::new" [lo, hi]` or as `tuple [lo, hi]` wrapping. -/
private def tryExtractRange (e : ImpExpr) : Option (ImpExpr × ImpExpr) :=
  match e with
  | .app f [lo, hi] =>
    if f == "Range" || f.endsWith "Range" || f == "new" || f == "Range::new"
    then some (lo, hi)
    else none
  | .tuple [lo, hi] => some (lo, hi)  -- Range as tuple
  | _ => none

/-- Information about a recognized iterator expression. -/
private inductive IterInfo where
  | range (lo hi : ImpExpr) (reversed : Bool)
  | collection (coll : ImpExpr)

/-- Try to extract iterator info from the scrutinee of the outer match.
    Recognizes: `into_iter(Range(lo, hi))` and `into_iter(rev(Range(lo, hi)))`. -/
private def tryExtractIterator (e : ImpExpr) : Option IterInfo :=
  match e with
  | .app f [arg] =>
    if isIntoIter f then
      -- Direct range: into_iter(Range(lo, hi))
      match tryExtractRange arg with
      | some (lo, hi) => some (.range lo hi false)
      | none =>
        -- Reversed range: into_iter(rev(Range(lo, hi)))
        match arg with
        | .app g [inner] =>
          if isRev g then
            match tryExtractRange inner with
            | some (lo, hi) => some (.range lo hi true)
            | none => none
          -- iter(collection) wrapped in into_iter
          else if g == "iter" || g.endsWith "iter" then
            some (.collection inner)
          else
            -- Bare collection: into_iter(collection)
            some (.collection arg)
        | _ =>
          -- Bare collection (variable or other expr): into_iter(collection)
          some (.collection arg)
    else if isRev f then
      -- rev(into_iter(Range(lo, hi)))
      match e with
      | .app _ [.app g [inner]] =>
        if isIntoIter g then
          match tryExtractRange inner with
          | some (lo, hi) => some (.range lo hi true)
          | none => none
        else none
      | _ => none
    else none
  | _ => none

/-- Try to extract the loop variable and body from the inner match on `next()`.
    Pattern: `match next(&mut iter) { None => break, Some(i) => body }` -/
private def tryExtractNextMatch (innerBody : ImpExpr) (iterVar : String) :
    Option (String × ImpExpr) :=
  -- The inner body may be wrapped in seq, letBind, or be a direct match
  match innerBody with
  | .match_ scrut arms =>
    -- Check scrutinee calls next on the iterator
    let isNext := match scrut with
      | .app f _ => isIterNext f
      | _ => false
    if !isNext then none
    else
      -- Look for None → break, Some(varPat v) → body pattern
      -- The arms may be in either order
      let findSome := arms.findSome? fun (pat, body) =>
        match pat with
        | .somePat (.varPat v) => some (v, body)
        | .somePat .wildcard => some ("_iter_unused", body)
        | .varPat v =>
          -- Sometimes hax uses a binding pattern for Some
          -- Check if there's a destructure in the body
          some (v, body)
        | _ => none
      let hasBreak := arms.any fun (pat, body) =>
        match pat with
        | .nonePat | .wildcard => match body with
          | .break_ _ => true
          | _ => false
        | _ => false
      match findSome, hasBreak with
      | some (v, body), true => some (v, body)
      | _, _ => none
  -- Wrapped in letBind: let _ = match ... ; rest
  | .letBind _ inner rest =>
    match tryExtractNextMatch inner iterVar with
    | some r => some r
    | none => tryExtractNextMatch rest iterVar
  | .seq e1 e2 =>
    match tryExtractNextMatch e1 iterVar with
    | some r => some r
    | none => tryExtractNextMatch e2 iterVar
  | _ => none

/-- Reconstruct for-loops from desugared iterator patterns in a single expression.
    Recursively traverses the expression, looking for the characteristic
    `match(into_iter(Range(...))) { iter => loop { match(next(iter)) { ... } } }`
    pattern produced by Rust's for-loop desugaring. -/
partial def reconstructForLoops : ImpExpr → ImpExpr
  | .match_ scrut arms =>
    match tryExtractIterator scrut, arms with
    | some (.range lo hi reversed),
      [(.varPat _iterVar, .whileLoop (.lit (.bool true)) innerBody)] =>
      -- Found the pattern! Extract the loop var from the inner next() match
      let lo' := reconstructForLoops lo
      let hi' := reconstructForLoops hi
      match tryExtractNextMatch innerBody _iterVar with
      | some (loopVar, body) =>
        let body' := reconstructForLoops body
        if reversed then .forLoopRev loopVar lo' hi' body'
        else .forLoop loopVar lo' hi' body'
      | none =>
        -- Inner match didn't match — fall through to regular match
        .match_ (reconstructForLoops scrut) (arms.map fun (p, e) => (p, reconstructForLoops e))
    | some (.collection coll),
      [(.varPat _iterVar, .whileLoop (.lit (.bool true)) innerBody)] =>
      -- Collection iteration: for elem in collection
      -- → forLoop "_i" 0 (len collection) (let elem := index collection _i; body)
      let coll' := reconstructForLoops coll
      match tryExtractNextMatch innerBody _iterVar with
      | some (loopVar, body) =>
        let body' := reconstructForLoops body
        let idxVar := "_ci"
        let loopBody := .letBind loopVar (.app "index" [coll', .var idxVar]) body'
        .forLoop idxVar (.lit (.int 0)) (.app "len" [coll']) loopBody
      | none =>
        .match_ (reconstructForLoops scrut) (arms.map fun (p, e) => (p, reconstructForLoops e))
    | _, _ =>
      .match_ (reconstructForLoops scrut) (arms.map fun (p, e) => (p, reconstructForLoops e))
  -- Recursive descent into all other constructors
  | .lit v => .lit v
  | .var n => .var n
  | .letBind n v b => .letBind n (reconstructForLoops v) (reconstructForLoops b)
  | .app f args => .app f (args.map reconstructForLoops)
  | .tuple es => .tuple (es.map reconstructForLoops)
  | .proj e i => .proj (reconstructForLoops e) i
  | .ifThenElse c t e => .ifThenElse (reconstructForLoops c) (reconstructForLoops t) (reconstructForLoops e)
  | .unitVal => .unitVal
  | .seq e1 e2 => .seq (reconstructForLoops e1) (reconstructForLoops e2)
  | .borrow e => .borrow (reconstructForLoops e)
  | .deref e => .deref (reconstructForLoops e)
  | .assign n rhs => .assign n (reconstructForLoops rhs)
  | .forLoop v lo hi body => .forLoop v (reconstructForLoops lo) (reconstructForLoops hi) (reconstructForLoops body)
  | .forLoopRev v lo hi body => .forLoopRev v (reconstructForLoops lo) (reconstructForLoops hi) (reconstructForLoops body)
  | .whileLoop c body => .whileLoop (reconstructForLoops c) (reconstructForLoops body)
  | .break_ (some e) => .break_ (some (reconstructForLoops e))
  | .break_ none => .break_ none
  | .continue_ => .continue_
  | .earlyReturn e => .earlyReturn (reconstructForLoops e)
  | .questionMark e => .questionMark (reconstructForLoops e)
  | .forFold v lo hi body => .forFold v (reconstructForLoops lo) (reconstructForLoops hi) (reconstructForLoops body)
  | .forFoldRev v lo hi body => .forFoldRev v (reconstructForLoops lo) (reconstructForLoops hi) (reconstructForLoops body)
  | .whileFold c body => .whileFold (reconstructForLoops c) (reconstructForLoops body)
  | .forFoldReturn v lo hi body => .forFoldReturn v (reconstructForLoops lo) (reconstructForLoops hi) (reconstructForLoops body)
  | .forFoldRevReturn v lo hi body => .forFoldRevReturn v (reconstructForLoops lo) (reconstructForLoops hi) (reconstructForLoops body)
  | .whileFoldReturn c body => .whileFoldReturn (reconstructForLoops c) (reconstructForLoops body)
  | .cfBreak e => .cfBreak (reconstructForLoops e)
  | .cfContinue e => .cfContinue (reconstructForLoops e)
  | .cfBreakContinue e => .cfBreakContinue (reconstructForLoops e)

/-! ## Compound Assignment Normalization

Hax sometimes emits compound assignments (`state[3] ^= k0`) as `Call` expressions
to trait methods like `BitXorAssign::bitxor_assign`, producing `app "BitXorAssign" [lhs, rhs]`.
These should be `assign` nodes for the pipeline's LocalMutation phase to process correctly.

We normalize:
- `app "XAssign" [var x, rhs]` → `assign x (app "X" [var x, rhs])`
- `app "XAssign" [index(arr, i), rhs]` → `assign arr (app "array_update" [var arr, i, app "X" [index(arr, i), rhs]])`
-/

/-- Strip the "Assign" suffix from a compound op name to get the base op.
    Returns `none` if not a compound assign op. -/
private def stripAssignSuffix (f : String) : Option String :=
  let pairs := [
    ("AddAssign", "Add"), ("SubAssign", "Sub"), ("MulAssign", "Mul"),
    ("DivAssign", "Div"), ("RemAssign", "Rem"),
    ("BitXorAssign", "BitXor"), ("BitOrAssign", "BitOr"), ("BitAndAssign", "BitAnd"),
    ("ShlAssign", "Shl"), ("ShrAssign", "Shr")]
  pairs.findSome? fun (cmpd, base) => if f == cmpd then some base else none

/-- Strip deref wrappers (references are erased by dropReferences phase). -/
private def stripDeref : ImpExpr → ImpExpr
  | .deref e => stripDeref e
  | e => e

/-- Extract the variable name from an lvalue expression. -/
private def extractLValueName : ImpExpr → String
  | .var n => n
  | .deref (.var n) => n
  | .deref (.deref (.var n)) => n
  | .app "index" (.var n :: _) => n
  | .app "index" (.deref (.var n) :: _) => n
  | .app "index" (.deref (.deref (.var n)) :: _) => n
  | _ => "_assign"

/-- Normalize compound assignment ops in an expression.
    Converts `app "XAssign" [target, val]` into proper `assign` nodes
    that the pipeline's LocalMutation phase can process. -/
partial def normalizeAssignOps : ImpExpr → ImpExpr
  | .app f [target, val] =>
    match stripAssignSuffix f with
    | some baseOp =>
      let target' := normalizeAssignOps target
      let val' := normalizeAssignOps val
      let name := extractLValueName target'
      match stripDeref target' with
      | .app "index" [arr, idx] =>
        -- Array element mutation: arr = array_update(arr, idx, X(arr[idx], val))
        .assign name (.app "array_update" [arr, idx, .app baseOp [target', val']])
      | _ =>
        -- Simple variable mutation: x = X(x, val)
        .assign name (.app baseOp [target', val'])
    | none => .app f [normalizeAssignOps target, normalizeAssignOps val]
  | .app f args => .app f (args.map normalizeAssignOps)
  | .lit v => .lit v
  | .var n => .var n
  | .unitVal => .unitVal
  | .letBind n v b => .letBind n (normalizeAssignOps v) (normalizeAssignOps b)
  | .tuple es => .tuple (es.map normalizeAssignOps)
  | .proj e i => .proj (normalizeAssignOps e) i
  | .ifThenElse c t e =>
    .ifThenElse (normalizeAssignOps c) (normalizeAssignOps t) (normalizeAssignOps e)
  | .match_ s arms =>
    .match_ (normalizeAssignOps s) (arms.map fun (p, b) => (p, normalizeAssignOps b))
  | .seq e1 e2 => .seq (normalizeAssignOps e1) (normalizeAssignOps e2)
  | .borrow e => .borrow (normalizeAssignOps e)
  | .deref e => .deref (normalizeAssignOps e)
  | .assign n rhs => .assign n (normalizeAssignOps rhs)
  | .forLoop v lo hi body =>
    .forLoop v (normalizeAssignOps lo) (normalizeAssignOps hi) (normalizeAssignOps body)
  | .forLoopRev v lo hi body =>
    .forLoopRev v (normalizeAssignOps lo) (normalizeAssignOps hi) (normalizeAssignOps body)
  | .whileLoop c body => .whileLoop (normalizeAssignOps c) (normalizeAssignOps body)
  | .break_ (some e) => .break_ (some (normalizeAssignOps e))
  | .break_ none => .break_ none
  | .continue_ => .continue_
  | .earlyReturn e => .earlyReturn (normalizeAssignOps e)
  | .questionMark e => .questionMark (normalizeAssignOps e)
  | .forFold v lo hi body =>
    .forFold v (normalizeAssignOps lo) (normalizeAssignOps hi) (normalizeAssignOps body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (normalizeAssignOps lo) (normalizeAssignOps hi) (normalizeAssignOps body)
  | .whileFold c body => .whileFold (normalizeAssignOps c) (normalizeAssignOps body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (normalizeAssignOps lo) (normalizeAssignOps hi) (normalizeAssignOps body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (normalizeAssignOps lo) (normalizeAssignOps hi) (normalizeAssignOps body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (normalizeAssignOps c) (normalizeAssignOps body)
  | .cfBreak e => .cfBreak (normalizeAssignOps e)
  | .cfContinue e => .cfContinue (normalizeAssignOps e)
  | .cfBreakContinue e => .cfBreakContinue (normalizeAssignOps e)

/-! ## Full hax export file parsing

The `hax_frontend_export.json` produced by `cargo hax json` is a top-level **array** of
items. Each item has `{def_id, owner_id, span, vis_span, kind, attributes, visibility}`.
The `kind` field is an externally-tagged enum:

- `"Fn"`: `{ident: [name, span], generics, def: {header, params, ret, body}}`
  where `body` is a `Decorated<ExprKind>` that `parseHaxExpr` handles.
- `"Const"`: `[ident_pair, generics, ty, body]` where `body` is `Decorated<ExprKind>`.
- `"TyAlias"`, `"Mod"`, `"Use"`, `"ExternCrate"`: skipped.
-/

/-- Extract the function name from a hax `Fn` item's `ident` field.
    Format: `[name_string, span_object]`. -/
private def extractFnName (ident : Json) : String :=
  match ident with
  | .arr elems => match elems.toList.head? with
    | some (.str n) => n
    | _ => "unknown_fn"
  | _ => "unknown_fn"

/-- Extract parameter names from a hax function definition's `params` array.
    Each param has `{pat: Decorated<PatKind>, ty: ...}`.
    Returns the list of parameter names (from Binding patterns). -/
private def extractParamNames (params : Array Json) : List String :=
  params.toList.filterMap fun p =>
    match p.getObjVal? "pat" with
    | .ok patJ =>
      let contents := match patJ.getObjVal? "contents" with
        | .ok c => c
        | _ => patJ
      match contents.getObjVal? "Binding" with
      | .ok bindData =>
        match bindData.getObjVal? "var" with
        | .ok varJ => match varJ.getObjValAs? String "name" with
          | .ok n => some n
          | _ => none
        | _ => none
      | _ => none
    | _ => none

/-- Per-function type information extracted from hax JSON.
    Re-exported from ImpType for convenience. -/
abbrev FnTypeInfo := SSProve.Hax.FnTypeInfo

/-- Extract parameter names and types from a hax function definition's `params` array.
    Each param has `{pat: Decorated<PatKind>, ty: {id, value: TyKind}}`. -/
private def extractParamTypes (params : Array Json) : List (String × ImpType) :=
  params.toList.filterMap fun p =>
    let name := match p.getObjVal? "pat" with
      | .ok patJ =>
        let contents := match patJ.getObjVal? "contents" with
          | .ok c => c
          | _ => patJ
        match contents.getObjVal? "Binding" with
        | .ok bindData =>
          match bindData.getObjVal? "var" with
          | .ok varJ => varJ.getObjValAs? String "name" |>.toOption
          | _ => none
        | _ => none
      | _ => none
    let ty := match p.getObjVal? "ty" with
      | .ok tyJ => parseHaxType tyJ
      | _ => .unknown
    name.map (·, ty)

/-- Wrap a function body in parameter bindings.
    Emits `letBind "param" (var "param") body` for each parameter,
    which the pipeline processes as identity bindings.
    The `extractFnDefs` in Main.lean then extracts these as function parameters. -/
private def wrapParams (params : List String) (body : ImpExpr) : ImpExpr :=
  params.foldr (fun p acc => .letBind p (.var p) acc) body

/-- Parse a single top-level item from `hax_frontend_export.json`.
    Returns `some (name, body)` for `Fn` and `Const` items, `none` for others. -/
partial def parseHaxItem (j : Json) : Except String (Option (String × ImpExpr)) := do
  let kind ← j.getObjVal? "kind"
  -- Fn: {ident: [name, span], generics: {...}, def: {header, params, ret, body}}
  if let .ok fnData := kind.getObjVal? "Fn" then
    let name := match fnData.getObjVal? "ident" with
      | .ok ident => extractFnName ident
      | _ => "unknown_fn"
    -- Extract parameter names
    let paramNames := match fnData.getObjVal? "def" with
      | .ok def_ => match def_.getObjValAs? (Array Json) "params" with
        | .ok params => extractParamNames params
        | _ => []
      | _ => []
    let body ← match fnData.getObjVal? "def" with
      | .ok def_ => parseHaxExpr (← def_.getObjVal? "body")
      | _ => throw s!"Fn item '{name}' missing def.body"
    let processed := normalizeAssignOps (reconstructForLoops body)
    -- Wrap body in identity let-bindings for parameters so the pretty printer
    -- can detect them and emit proper function signatures.
    let wrapped := if paramNames.isEmpty then processed else wrapParams paramNames processed
    return some (name, wrapped)
  -- Const: [ident_pair, generics, ty, body]
  else if let .ok (.arr constData) := kind.getObjVal? "Const" then
    let name := match constData.toList with
      | (.arr ident) :: _ => extractFnName (.arr ident)
      | _ => "unknown_const"
    let body ← match constData.toList[3]? with
      | some bodyJ => parseHaxExpr bodyJ
      | none => throw s!"Const item '{name}' missing body"
    return some (name, normalizeAssignOps (reconstructForLoops body))
  -- Skip: Mod, Use, ExternCrate, TyAlias
  else return none

/-- Parse a single top-level item with type information.
    Returns `some (name, body, fnTypeInfo)` for `Fn` items, `none` for others. -/
partial def parseHaxItemWithTypes (j : Json) :
    Except String (Option (String × ImpExpr × FnTypeInfo)) := do
  let kind ← j.getObjVal? "kind"
  if let .ok fnData := kind.getObjVal? "Fn" then
    let name := match fnData.getObjVal? "ident" with
      | .ok ident => extractFnName ident
      | _ => "unknown_fn"
    let def_ := match fnData.getObjVal? "def" with
      | .ok d => some d
      | _ => none
    let paramNames := match def_ with
      | some d => match d.getObjValAs? (Array Json) "params" with
        | .ok params => extractParamNames params
        | _ => []
      | none => []
    let paramTypes := match def_ with
      | some d => match d.getObjValAs? (Array Json) "params" with
        | .ok params => extractParamTypes params
        | _ => []
      | none => []
    let retType := match def_ with
      | some d => match d.getObjVal? "ret" with
        | .ok retJ => parseHaxType retJ
        | _ => .unknown
      | none => .unknown
    let body ← match def_ with
      | some d => parseHaxExpr (← d.getObjVal? "body")
      | none => throw s!"Fn item '{name}' missing def.body"
    let processed := normalizeAssignOps (reconstructForLoops body)
    let wrapped := if paramNames.isEmpty then processed else wrapParams paramNames processed
    return some (name, wrapped, ⟨paramTypes, retType⟩)
  else if let .ok (.arr constData) := kind.getObjVal? "Const" then
    let name := match constData.toList with
      | (.arr ident) :: _ => extractFnName (.arr ident)
      | _ => "unknown_const"
    let body ← match constData.toList[3]? with
      | some bodyJ => parseHaxExpr bodyJ
      | none => throw s!"Const item '{name}' missing body"
    return some (name, normalizeAssignOps (reconstructForLoops body), ⟨[], .unknown⟩)
  else return none

/-- Parse a full hax export with per-function type information.
    Returns both the combined ImpExpr and a list of (name, FnTypeInfo).
    Recurses into Mod items to find nested functions/constants. -/
partial def parseHaxFileWithTypes (j : Json) :
    Except String (ImpExpr × List (String × FnTypeInfo)) := do
  let rec parseItemsWithTypes (items : List Json) :
      Except String (List (String × ImpExpr × FnTypeInfo)) := do
    let mut result : List (String × ImpExpr × FnTypeInfo) := []
    for item in items do
      -- Try parsing as Fn/Const
      match ← parseHaxItemWithTypes item with
      | some r => result := result ++ [r]
      | none =>
        -- Recurse into Mod items
        let kind := (item.getObjVal? "kind").toOption
        match kind with
        | some kindJ =>
          -- Try Mod: kind.Mod = [name_data, [sub_items]]
          match kindJ.getObjVal? "Mod" with
          | .ok (.arr modData) =>
            match modData.toList[1]? with
            | some subJ =>
              match subJ with
              | .arr subItems =>
                let sub ← parseItemsWithTypes subItems.toList
                result := result ++ sub
              | _ => pure ()
            | _ => pure ()
          | .ok modData =>
            -- Mod might also be an object with items field
            match modData.getObjValAs? (Array Json) "items" with
            | .ok subItems =>
              let sub ← parseItemsWithTypes subItems.toList
              result := result ++ sub
            | _ => pure ()
          | _ =>
            -- Skip Impl blocks for now (methods may lack bodies)
            pure ()
        | none => pure ()
    return result
  match j with
  | .arr items =>
    let parsed ← parseItemsWithTypes items.toList
    match parsed with
    | [] => throw "no functions or constants found in hax export"
    | _ =>
      let expr := parsed.foldr (fun (name, body, _) acc => .letBind name body acc) .unitVal
      let fnTypes := parsed.map fun (name, _, ti) => (name, ti)
      return (expr, fnTypes)
  | _ =>
    return (normalizeAssignOps (reconstructForLoops (← parseHaxExpr j)), [])

/-- Collect return types for all function calls from the hax JSON expression tree.
    Walks the raw JSON (before ImpExpr conversion) and extracts `ty` from each Call node.
    Returns a map: functionName → ImpType (return type). -/
partial def collectCallReturnTypes (j : Json) : List (String × ImpType) :=
  match j with
  | .obj _ =>
    -- Check if this node has a Call in contents
    let callTypes := match j.getObjVal? "contents" with
      | .ok contents =>
        match contents.getObjVal? "Call" with
        | .ok callData =>
          let funName := extractCallName (match callData.getObjVal? "fun" with
            | .ok f => f | _ => .null)
          let retType := match j.getObjVal? "ty" with
            | .ok tyJ => parseHaxType tyJ
            | _ => .unknown
          if funName != "unknown_fn" && funName != "indirect_call" && !retType.isUnknown then
            [(funName, retType)]
          else []
        | _ => []
      | _ => []
    -- Recurse into all object values
    let childTypes := j.getObj?.toOption.map (fun obj =>
      obj.toList.flatMap fun (_, v) => collectCallReturnTypes v) |>.getD []
    callTypes ++ childTypes
  | .arr items => items.toList.flatMap collectCallReturnTypes
  | _ => []

/-- Collect full type signatures (argument types + return type) for function calls
    from the hax JSON expression tree. For each Call node, extracts the `ty` of each
    argument and the `ty` of the call itself (return type).
    Returns: functionName → FnTypeInfo (paramTypes named "arg0".."argN", retType). -/
partial def collectCallSignatures (j : Json) : List (String × FnTypeInfo) :=
  match j with
  | .obj _ =>
    let callSigs := match j.getObjVal? "contents" with
      | .ok contents =>
        match contents.getObjVal? "Call" with
        | .ok callData =>
          let funName := extractCallName (match callData.getObjVal? "fun" with
            | .ok f => f | _ => .null)
          let retType := match j.getObjVal? "ty" with
            | .ok tyJ => parseHaxType tyJ
            | _ => .unknown
          let argTypes := match callData.getObjValAs? (Array Json) "args" with
            | .ok args =>
              let argList := args.toList
              (argList.zip (List.range argList.length)).map fun (arg, i) =>
                let ty := match arg.getObjVal? "ty" with
                  | .ok tyJ => parseHaxType tyJ
                  | _ => .unknown
                (s!"arg{i}", ty)
            | _ => []
          if funName != "unknown_fn" && funName != "indirect_call" then
            [(funName, ⟨argTypes, retType⟩)]
          else []
        | _ => []
      | _ => []
    let childSigs := j.getObj?.toOption.map (fun obj =>
      obj.toList.flatMap fun (_, v) => collectCallSignatures v) |>.getD []
    callSigs ++ childSigs
  | .arr items => items.toList.flatMap collectCallSignatures
  | _ => []

/-- Extract call signatures from a single hax JSON item (Fn). -/
private partial def extractCallSigsItem (item : Json) : List (String × FnTypeInfo) :=
  match item.getObjVal? "kind" with
  | .ok kind =>
    match kind.getObjVal? "Fn" with
    | .ok fnData =>
      match fnData.getObjVal? "def" with
      | .ok d => match d.getObjVal? "body" with
        | .ok body => collectCallSignatures body
        | _ => []
      | _ => []
    | _ =>
      -- Also check Const items
      match kind.getObjVal? "Const" with
      | .ok (.arr constData) =>
        match constData.toList[3]? with
        | some bodyJ => collectCallSignatures bodyJ
        | none => []
      | _ => []
  | _ => []

/-- Extract call signatures from a full hax export JSON.
    Returns deduplicated map: functionName → FnTypeInfo.
    When multiple call sites exist, keeps the one with the most non-unknown arg types. -/
partial def extractCallSignaturesFromFile (j : Json) : List (String × FnTypeInfo) :=
  let raw : List (String × FnTypeInfo) := match j with
    | Json.arr items => items.toList.flatMap fun item =>
      extractCallSigsItem item ++
      -- Also recurse into Mod items
      (match item.getObjVal? "kind" with
       | .ok kind =>
         match kind.getObjVal? "Mod" with
         | .ok (Json.arr modData) =>
           match modData.toList[1]? with
           | some (Json.arr subItems) => subItems.toList.flatMap extractCallSigsItem
           | _ => []
         | _ => []
       | _ => ([] : List (String × FnTypeInfo)))
    | _ => []
  -- Deduplicate: for each function name, pick the best type info
  -- (most non-unknown param types, then non-unknown return type)
  raw.foldl (fun (acc : List (String × FnTypeInfo)) ((name, ti) : String × FnTypeInfo) =>
    match acc.find? (·.1 == name) with
    | some (_, existTi) =>
      let existKnown := existTi.paramTypes.filter (fun (_, t) => !t.isUnknown) |>.length
      let existScore := existKnown + (if existTi.retType.isUnknown then 0 else 1)
      let newKnown := ti.paramTypes.filter (fun (_, t) => !t.isUnknown) |>.length
      let newScore := newKnown + (if ti.retType.isUnknown then 0 else 1)
      if newScore > existScore then
        acc.map fun (n, t) => if n == name then (n, ti) else (n, t)
      else acc
    | none => acc ++ [(name, ti)]) []

/-- Collect types of free variable references from hax JSON expression tree.
    For standalone variable references (VarRef) that are not function call targets,
    extracts `ty` to determine whether a free var dep should be Int, Array Int, etc.
    Returns: variableName → ImpType. -/
partial def collectVarRefTypes (j : Json) : List (String × ImpType) :=
  match j with
  | .obj _ =>
    let varTypes := match j.getObjVal? "contents" with
      | .ok contents =>
        -- Handle GlobalVar references
        let globalVarTypes := match contents.getObjVal? "GlobalVar" with
          | .ok varData =>
            let varName := match varData.getObjVal? "id" with
              | .ok id => match id.getObjValAs? String "name" with
                | .ok n => n
                | _ => "unknown"
              | _ => "unknown"
            let ty := match j.getObjVal? "ty" with
              | .ok tyJ => parseHaxType tyJ
              | _ => .unknown
            if varName != "unknown" && !ty.isUnknown then [(varName, ty)] else []
          | _ => ([] : List (String × ImpType))
        -- Handle StaticRef references (static constants like AEGIS_C0)
        let staticRefTypes := match contents.getObjVal? "StaticRef" with
          | .ok data =>
            let varName := match data.getObjVal? "def_id" with
              | .ok defId => extractDefIdName defId
              | _ => "unknown"
            let ty := match j.getObjVal? "ty" with
              | .ok tyJ => parseHaxType tyJ
              | _ => .unknown
            if varName != "unknown" && varName != "static" && !ty.isUnknown
            then [(varName, ty)] else []
          | _ => ([] : List (String × ImpType))
        globalVarTypes ++ staticRefTypes
      | _ => ([] : List (String × ImpType))
    let childTypes := j.getObj?.toOption.map (fun obj =>
      obj.toList.flatMap fun (_, v) => collectVarRefTypes v) |>.getD []
    varTypes ++ childTypes
  | .arr items => items.toList.flatMap collectVarRefTypes
  | _ => []

/-- Extract var ref types from a single hax JSON item. -/
private partial def extractVarRefTypesItem (item : Json) : List (String × ImpType) :=
  match item.getObjVal? "kind" with
  | .ok kind =>
    match kind.getObjVal? "Fn" with
    | .ok fnData =>
      match fnData.getObjVal? "def" with
      | .ok d => match d.getObjVal? "body" with
        | .ok body => collectVarRefTypes body
        | _ => []
      | _ => []
    | _ =>
      match kind.getObjVal? "Const" with
      | .ok (.arr constData) =>
        match constData.toList[3]? with
        | some bodyJ => collectVarRefTypes bodyJ
        | none => []
      | _ => []
  | _ => []

/-- Extract variable reference types from a full hax export JSON.
    Returns deduplicated map: variableName → ImpType. -/
partial def extractVarRefTypesFromFile (j : Json) : List (String × ImpType) :=
  let raw : List (String × ImpType) := match j with
    | Json.arr items => items.toList.flatMap fun item =>
      extractVarRefTypesItem item ++
      (match item.getObjVal? "kind" with
       | .ok kind =>
         match kind.getObjVal? "Mod" with
         | .ok (Json.arr modData) =>
           match modData.toList[1]? with
           | some (Json.arr subItems) => subItems.toList.flatMap extractVarRefTypesItem
           | _ => []
         | _ => []
       | _ => ([] : List (String × ImpType)))
    | _ => []
  raw.foldl (fun (acc : List (String × ImpType)) ((name, ty) : String × ImpType) =>
    if acc.any (·.1 == name) then acc else acc ++ [(name, ty)]) []

/-- Extract call return types from a single hax JSON item (Fn). -/
private partial def extractCallRetTypesItem (item : Json) : List (String × ImpType) :=
  match item.getObjVal? "kind" with
  | .ok kind =>
    match kind.getObjVal? "Fn" with
    | .ok fnData =>
      match fnData.getObjVal? "def" with
      | .ok d => match d.getObjVal? "body" with
        | .ok body => collectCallReturnTypes body
        | _ => []
      | _ => []
    | _ => []
  | _ => []

/-- Extract call return types from a full hax export JSON.
    Returns deduplicated map: functionName → ImpType. -/
partial def extractCallReturnTypesFromFile (j : Json) : List (String × ImpType) :=
  let raw := match j with
    | .arr items => items.toList.flatMap extractCallRetTypesItem
    | _ => []
  -- Deduplicate: keep first occurrence per function name
  raw.foldl (fun acc (name, ty) =>
    if acc.any (·.1 == name) then acc else acc ++ [(name, ty)]) []

/-- Validate that an ImpExpr contains no unsupported/dangerous patterns
    that could produce vacuous proofs. Returns a list of warnings. -/
partial def validateExtraction (e : ImpExpr) (path : String := "") : List String :=
  match e with
  | .app f args =>
    let selfWarns :=
      if f.startsWith "hax_unsupported_" then
        [s!"{path}: unsupported hax construct '{f}' — extraction is incomplete"]
      else if f == "literal" then
        [s!"{path}: unsupported literal type — extraction is incomplete"]
      else if f.startsWith "todo:" then
        [s!"{path}: hax Todo '{f}' — Rust code was not translated"]
      else []
    selfWarns ++ args.flatMap (fun a => validateExtraction a path)
  | .letBind n v b =>
    validateExtraction v (path ++ "/" ++ n) ++ validateExtraction b path
  | .seq e1 e2 => validateExtraction e1 path ++ validateExtraction e2 path
  | .ifThenElse c t el =>
    validateExtraction c path ++ validateExtraction t path ++ validateExtraction el path
  | .match_ s arms =>
    validateExtraction s path ++
      arms.flatMap (fun (_, b) => validateExtraction b path)
  | .tuple es => es.flatMap (fun e => validateExtraction e path)
  | .proj e _ => validateExtraction e path
  | .forLoop _ lo hi b | .forLoopRev _ lo hi b
  | .forFold _ lo hi b | .forFoldRev _ lo hi b
  | .forFoldReturn _ lo hi b | .forFoldRevReturn _ lo hi b =>
    validateExtraction lo path ++ validateExtraction hi path ++
      validateExtraction b path
  | .whileLoop c b | .whileFold c b | .whileFoldReturn c b =>
    validateExtraction c path ++ validateExtraction b path
  | .borrow e | .deref e | .assign _ e | .break_ (some e)
  | .earlyReturn e | .questionMark e
  | .cfBreak e | .cfContinue e | .cfBreakContinue e =>
    validateExtraction e path
  | _ => []

/-- Parse a full `hax_frontend_export.json` (top-level array of items).
    Combines all `Fn` and `Const` items into nested `letBind`s. -/
partial def parseHaxFile (j : Json) : Except String ImpExpr := do
  match j with
  | .arr items =>
    let parsed ← items.toList.filterMapM parseHaxItem
    match parsed with
    | [] => throw "no functions or constants found in hax export"
    | _ => return parsed.foldr (fun (name, body) acc => .letBind name body acc) .unitVal
  | _ =>
    -- Single Decorated<ExprKind> — use the existing single-expression parser
    return normalizeAssignOps (reconstructForLoops (← parseHaxExpr j))

/-- Parse and validate a hax export. Returns the ImpExpr and any warnings.
    Warnings indicate incomplete translation (Todo, unsupported literals, etc.)
    that could make downstream proofs vacuous. -/
partial def parseHaxFileValidated (j : Json) : Except String (ImpExpr × List String) := do
  let expr ← parseHaxFile j
  let warnings := validateExtraction expr
  return (expr, warnings)

/-- Extract the type from a hax Decorated JSON node's `ty` field. -/
private def extractNodeType (j : Json) : ImpType :=
  match j.getObjVal? "ty" with
  | .ok tyJ => parseHaxType tyJ
  | _ => .unknown

/-- Parse a hax `Decorated<ExprKind>` JSON directly into a `TExpr`,
    preserving the type annotation from every JSON node's `ty` field.
    This is the principled typed extraction: every subexpression carries
    its Rust type, eliminating the need for heuristic type recovery. -/
partial def parseHaxTExpr (j : Json) : Except String TExpr := do
  let ty := extractNodeType j
  let contents ← j.getObjVal? "contents"
  let kind ← parseTExprKind contents j
  return TExpr.mk kind ty
where
  /-- Parse a hax ExprKind into a TExprKind, recursing into sub-expressions
      with full type preservation. `parentJ` is the enclosing Decorated node
      (used to access `ty` for the current node). -/
  parseTExprKind (j _parentJ : Json) : Except String TExprKind := do
    -- Unit variants
    match j with
    | .str "Todo" => return .app "hax_unsupported_Todo" []
    | _ => pure ()

    if let .ok data := j.getObjVal? "VarRef" then
      let name := match data.getObjVal? "id" with
        | .ok id => extractLocalIdentName id
        | _ => "unknown_var"
      return .var name

    else if let .ok data := j.getObjVal? "GlobalName" then
      let name := match data.getObjVal? "item" with
        | .ok item => extractItemDefIdName item "global"
        | _ => "global"
      return .var name

    else if let .ok data := j.getObjVal? "Literal" then
      return .lit (parseTLiteral data)

    else if let .ok data := j.getObjVal? "If" then
      let cond ← parseHaxTExpr (← data.getObjVal? "cond")
      let thn ← parseHaxTExpr (← data.getObjVal? "then")
      let els ← match data.getObjVal? "else_opt" with
        | .ok (.null) => pure (TExpr.mk .unitVal .unit)
        | .ok elsJ => parseHaxTExpr elsJ
        | _ => pure (TExpr.mk .unitVal .unit)
      return .ifThenElse cond thn els

    else if let .ok data := j.getObjVal? "Call" then
      let funName := extractCallName (← data.getObjVal? "fun")
      let argsJ ← data.getObjValAs? (Array Json) "args"
      let args ← argsJ.toList.mapM parseHaxTExpr
      return .app funName args

    else if let .ok data := j.getObjVal? "Let" then
      let rhs ← parseHaxTExpr (← data.getObjVal? "expr")
      let pat := match data.getObjVal? "pat" with
        | .ok p => parseHaxPat p
        | _ => .wildcard
      match pat with
      | .tuplePat pats =>
        let tmpName := "_tup"
        let bindings := (pats.zip (List.range pats.length)).map fun (p, i) =>
          let name := match p with
            | .varPat n => if n.startsWith "_" then "_" else n
            | _ => "_"
          (name, TExpr.mk (.proj (TExpr.mk (.var tmpName) rhs.ty) i) .unknown)
        let inner := bindings.foldr (fun (n, proj) acc =>
          TExpr.mk (.letBind n proj acc) .unknown) (TExpr.mk .unitVal .unit)
        return .letBind tmpName rhs inner
      | .varPat n =>
        return .letBind n rhs (TExpr.mk .unitVal .unit)
      | _ =>
        return .letBind "_let" rhs (TExpr.mk .unitVal .unit)

    else if let .ok data := j.getObjVal? "Block" then
      let stmts ← match data.getObjValAs? (Array Json) "stmts" with
        | .ok ss => ss.toList.mapM parseTStmt
        | _ => pure []
      let tail ← match data.getObjVal? "expr" with
        | .ok (.null) => pure (TExpr.mk .unitVal .unit)
        | .ok e => parseHaxTExpr e
        | _ => pure (TExpr.mk .unitVal .unit)
      return (tStmtsToSeq stmts tail).kind

    else if let .ok data := j.getObjVal? "Match" then
      let scrut ← parseHaxTExpr (← data.getObjVal? "scrutinee")
      let armsJ ← data.getObjValAs? (Array Json) "arms"
      let arms ← armsJ.toList.mapM parseTArm
      return .match_ scrut arms

    else if let .ok data := j.getObjVal? "Tuple" then
      let fieldsJ ← data.getObjValAs? (Array Json) "fields"
      let fields ← fieldsJ.toList.mapM parseHaxTExpr
      if fields.isEmpty then return .unitVal
      return .tuple fields

    else if let .ok data := j.getObjVal? "Array" then
      let fieldsJ ← data.getObjValAs? (Array Json) "fields"
      let fields ← fieldsJ.toList.mapM parseHaxTExpr
      return .app "array_lit" fields

    else if let .ok data := j.getObjVal? "Assign" then
      let lhs ← parseHaxTExpr (← data.getObjVal? "lhs")
      let rhs ← parseHaxTExpr (← data.getObjVal? "rhs")
      let rec stripD : TExpr → TExpr
        | .mk (.deref e) _ => stripD e
        | e => e
      let lhs' := stripD lhs
      let getVarName : TExpr → String
        | .mk (.var n) _ => n
        | .mk (.deref (.mk (.var n) _)) _ => n
        | _ => "_assign"
      match lhs'.kind with
      | .var n => return .assign n rhs
      | .app "index" [arr, idx] =>
        let arrName := getVarName (stripD arr)
        return .assign arrName (TExpr.mk (.app "array_update" [arr, idx, rhs]) rhs.ty)
      | _ => return .assign "_assign" rhs

    else if let .ok data := j.getObjVal? "AssignOp" then
      let rawOp := match data.getObjVal? "op" with
        | .ok opJ => binOpName opJ
        | _ => "op"
      let op := if rawOp.endsWith "Assign" then rawOp.dropRight 6 else rawOp
      let lhs ← parseHaxTExpr (← data.getObjVal? "lhs")
      let rhs ← parseHaxTExpr (← data.getObjVal? "rhs")
      let rec stripD2 : TExpr → TExpr
        | .mk (.deref e) _ => stripD2 e
        | e => e
      let lhs' := stripD2 lhs
      match lhs'.kind with
      | .var n => return .assign n (TExpr.mk (.app op [lhs, rhs]) lhs.ty)
      | .app "index" [arr, idx] =>
        let arrName := match (stripD2 arr).kind with
          | .var n => n | _ => "_assign"
        return .assign arrName (TExpr.mk (.app "array_update" [arr, idx, TExpr.mk (.app op [lhs, rhs]) lhs.ty]) arr.ty)
      | _ => return .assign "_assign" (TExpr.mk (.app op [lhs, rhs]) lhs.ty)

    else if let .ok data := j.getObjVal? "Borrow" then
      let arg ← parseHaxTExpr (← data.getObjVal? "arg")
      return .borrow arg

    else if let .ok data := j.getObjVal? "Deref" then
      let arg ← parseHaxTExpr (← data.getObjVal? "arg")
      return .deref arg

    else if let .ok data := j.getObjVal? "Loop" then
      let body ← parseHaxTExpr (← data.getObjVal? "body")
      return .whileLoop (TExpr.mk (.lit (.bool true)) .bool) body

    else if let .ok data := j.getObjVal? "Break" then
      let value ← match data.getObjVal? "value" with
        | .ok (.null) => pure none
        | .ok v => return .break_ (some (← parseHaxTExpr v))
        | _ => pure none
      return .break_ value

    else if let .ok _data := j.getObjVal? "Continue" then
      return .continue_

    else if let .ok data := j.getObjVal? "Return" then
      let value ← match data.getObjVal? "value" with
        | .ok (.null) => pure (TExpr.mk .unitVal .unit)
        | .ok v => parseHaxTExpr v
        | _ => pure (TExpr.mk .unitVal .unit)
      return .earlyReturn value

    else if let .ok data := j.getObjVal? "Binary" then
      let op := match data.getObjVal? "op" with
        | .ok opJ => binOpName opJ
        | _ => "binop"
      let lhs ← parseHaxTExpr (← data.getObjVal? "lhs")
      let rhs ← parseHaxTExpr (← data.getObjVal? "rhs")
      return .app op [lhs, rhs]

    else if let .ok data := j.getObjVal? "LogicalOp" then
      let op := match data.getObjVal? "op" with
        | .ok (.str "And") => "&&"
        | .ok (.str "Or") => "||"
        | _ => "logical_op"
      let lhs ← parseHaxTExpr (← data.getObjVal? "lhs")
      let rhs ← parseHaxTExpr (← data.getObjVal? "rhs")
      return .app op [lhs, rhs]

    else if let .ok data := j.getObjVal? "Unary" then
      let op := match data.getObjVal? "op" with
        | .ok opJ => unOpName opJ
        | _ => "unop"
      let arg ← parseHaxTExpr (← data.getObjVal? "arg")
      return .app op [arg]

    else if let .ok data := j.getObjVal? "Field" then
      let lhs ← parseHaxTExpr (← data.getObjVal? "lhs")
      let fieldName := match data.getObjVal? "field" with
        | .ok fj => extractDefIdName fj
        | _ => "field"
      return .app ("." ++ fieldName) [lhs]

    else if let .ok data := j.getObjVal? "TupleField" then
      let lhs ← parseHaxTExpr (← data.getObjVal? "lhs")
      let idx := match data.getObjValAs? Nat "field" with
        | .ok n => n
        | _ => 0
      return .proj lhs idx

    else if let .ok data := j.getObjVal? "Index" then
      let lhs ← parseHaxTExpr (← data.getObjVal? "lhs")
      let index ← parseHaxTExpr (← data.getObjVal? "index")
      return .app "index" [lhs, index]

    else if let .ok data := j.getObjVal? "Cast" then
      let source ← parseHaxTExpr (← data.getObjVal? "source")
      return .app "cast" [source]

    else if let .ok data := j.getObjVal? "Use" then
      return (← parseHaxTExpr (← data.getObjVal? "source")).kind

    else if let .ok data := j.getObjVal? "NeverToAny" then
      return (← parseHaxTExpr (← data.getObjVal? "source")).kind

    else if let .ok data := j.getObjVal? "Box" then
      return (← parseHaxTExpr (← data.getObjVal? "value")).kind

    else if let .ok data := j.getObjVal? "Adt" then
      parseTAdtExpr data

    else if let .ok data := j.getObjVal? "Closure" then
      return (← parseHaxTExpr (← data.getObjVal? "body")).kind

    else if let .ok data := j.getObjVal? "Repeat" then
      let value ← parseHaxTExpr (← data.getObjVal? "value")
      let count ← match data.getObjVal? "count" with
        | .ok countJ => parseHaxTExpr countJ
        | _ => pure (TExpr.mk (.lit (.int 0)) .int)
      return .app "repeat" [value, count]

    else if let .ok data := j.getObjVal? "PlaceTypeAscription" then
      return (← parseHaxTExpr (← data.getObjVal? "source")).kind

    else if let .ok data := j.getObjVal? "ValueTypeAscription" then
      return (← parseHaxTExpr (← data.getObjVal? "source")).kind

    else if let .ok data := j.getObjVal? "PointerCoercion" then
      return (← parseHaxTExpr (← data.getObjVal? "source")).kind

    else if let .ok _data := j.getObjVal? "ConstBlock" then
      return .app "const_block" []

    else if let .ok data := j.getObjVal? "NamedConst" then
      let name := match data.getObjVal? "item" with
        | .ok item => extractItemDefIdName item "const"
        | _ => "const"
      return .var name

    else if let .ok _data := j.getObjVal? "ConstParam" then
      return .var "const_param"

    else if let .ok data := j.getObjVal? "ConstRef" then
      let name := match data.getObjVal? "id" with
        | .ok id => match id.getObjValAs? String "name" with
          | .ok n => n
          | _ => "const_ref"
        | _ => "const_ref"
      return .var name

    else if let .ok data := j.getObjVal? "StaticRef" then
      let name := match data.getObjVal? "def_id" with
        | .ok defId => extractDefIdName defId
        | _ => "static"
      return .var name

    else if let .ok data := j.getObjVal? "Yield" then
      let value ← parseHaxTExpr (← data.getObjVal? "value")
      return .app "yield" [value]

    else if let .ok s := j.getObjVal? "Todo" then
      let msg := match s with
        | .str m => m
        | _ => "todo"
      return .app ("todo:" ++ msg) []

    else
      throw s!"unknown hax ExprKind: {j.pretty}"

  /-- Parse a hax literal into ImpLit. -/
  parseTLiteral (data : Json) : ImpLit :=
    let neg := match data.getObjValAs? Bool "neg" with
      | .ok true => true
      | _ => false
    let litKind := match data.getObjVal? "lit" with
      | .ok spanned => match spanned.getObjVal? "node" with
        | .ok n => n
        | _ => spanned
      | _ => data
    if let .ok b := litKind.getObjValAs? Bool "Bool" then .bool b
    else if let .ok intData := litKind.getObjVal? "Int" then
      let nArr := match intData with
        | .arr a => some a
        | _ =>
          let tryUint := intData.getObjVal? "Uint"
          let tryInt := intData.getObjVal? "Int"
          match (tryUint.toOption.orElse fun _ => tryInt.toOption) with
          | some (.arr a) => some a
          | _ => none
      match nArr with
      | some #[nJ, _] =>
        let n := match nJ.getStr? with
          | .ok s => s.toInt?.getD 0
          | _ => match nJ.getNat? with
            | .ok n => n
            | _ => 0
        .int (if neg then -n else n)
      | _ => .int 0
    else if let .ok _bsData := litKind.getObjVal? "ByteStr" then
      -- ByteStr not representable as single ImpLit; use int 0 as placeholder
      .int 0
    else .unit  -- char, float, etc.

  /-- Parse a hax Stmt into TExpr. -/
  parseTStmt (j : Json) : Except String TExpr := do
    let kind ← j.getObjVal? "kind"
    if let .ok data := kind.getObjVal? "Expr" then
      match data.getObjVal? "expr" with
      | .ok e => parseHaxTExpr e
      | _ => return TExpr.mk .unitVal .unit
    else if let .ok data := kind.getObjVal? "Let" then
      let pat := match data.getObjVal? "pattern" with
        | .ok p => parseHaxPat p
        | _ => .wildcard
      let init ← match data.getObjVal? "initializer" with
        | .ok (.null) => pure (TExpr.mk .unitVal .unit)
        | .ok e => parseHaxTExpr e
        | _ => pure (TExpr.mk .unitVal .unit)
      match pat with
      | .tuplePat pats =>
        let tmpName := "_tup"
        let bindings := (pats.zip (List.range pats.length)).map fun (p, i) =>
          let name := match p with
            | .varPat n => if n.startsWith "_" then "_" else n
            | _ => "_"
          (name, TExpr.mk (.proj (TExpr.mk (.var tmpName) init.ty) i) .unknown)
        let inner := bindings.foldr (fun (n, proj) acc =>
          TExpr.mk (.letBind n proj acc) .unknown) (TExpr.mk .unitVal .unit)
        return TExpr.mk (.letBind tmpName init inner) .unknown
      | .varPat n =>
        return TExpr.mk (.letBind n init (TExpr.mk .unitVal .unit)) .unknown
      | _ =>
        return TExpr.mk (.letBind "_let" init (TExpr.mk .unitVal .unit)) .unknown
    else
      return TExpr.mk .unitVal .unit

  /-- Replace the deepest unitVal in a TExpr letBind chain with a continuation. -/
  tReplaceDeepestUnit (e : TExpr) (cont : TExpr) : TExpr :=
    match e.kind with
    | .letBind n v (.mk .unitVal _) => TExpr.mk (.letBind n v cont) e.ty
    | .letBind n v body => TExpr.mk (.letBind n v (tReplaceDeepestUnit body cont)) e.ty
    | _ => TExpr.mk (.seq e cont) cont.ty

  /-- Convert a list of TExpr statements into nested seq/letBind. -/
  tStmtsToSeq (stmts : List TExpr) (tail : TExpr) : TExpr :=
    match stmts with
    | [] => tail
    | [s] => tReplaceDeepestUnit s tail
    | s :: rest => tReplaceDeepestUnit s (tStmtsToSeq rest tail)

  /-- Parse a hax Arm into (ImpPat, TExpr). -/
  parseTArm (j : Json) : Except String (ImpPat × TExpr) := do
    let pat := match j.getObjVal? "pattern" with
      | .ok p => parseHaxPat p
      | _ => .wildcard
    let body ← match j.getObjVal? "body" with
      | .ok b => parseHaxTExpr b
      | _ => pure (TExpr.mk .unitVal .unit)
    return (pat, body)

  /-- Parse a hax AdtExpr into TExprKind. -/
  parseTAdtExpr (j : Json) : Except String TExprKind := do
    let name := match j.getObjVal? "info" with
      | .ok info => match info.getObjVal? "variant" with
        | .ok variantDefId => extractDefIdName variantDefId
        | _ => match info.getObjVal? "type_namespace" with
          | .ok nsDefId => extractDefIdName nsDefId
          | _ => match info.getObjValAs? String "variant_name" with
            | .ok n => n
            | _ => "Adt"
      | _ => "Adt"
    let fields ← match j.getObjValAs? (Array Json) "fields" with
      | .ok fs => fs.toList.mapM fun fj =>
        match fj.getObjVal? "value" with
        | .ok v => parseHaxTExpr v
        | _ => pure (TExpr.mk .unitVal .unit)
      | _ => pure []
    return .app name fields

/-- Reconstruct for-loops in a TExpr (typed version of `reconstructForLoops`).
    Since the loop pattern recognition is structural, we erase to ImpExpr,
    apply the untyped pass, then re-attach the root type.
    Inner types are lost (set to .unknown) but the root type is preserved. -/
def reconstructForLoopsTExpr (te : TExpr) : TExpr :=
  let imp := te.erase
  let imp' := reconstructForLoops imp
  TExpr.ofImpExpr imp'

/-- Normalize compound assignment ops in a TExpr (typed version). -/
def normalizeAssignOpsTExpr (te : TExpr) : TExpr :=
  let imp := te.erase
  let imp' := normalizeAssignOps imp
  TExpr.ofImpExpr imp'

/-- Parse a single hax Fn item into a typed TExpr with full type information.
    Returns `some (name, texpr, fnTypeInfo)` for Fn items. -/
partial def parseHaxItemTExpr (j : Json) :
    Except String (Option (String × TExpr × FnTypeInfo)) := do
  let kind ← j.getObjVal? "kind"
  if let .ok fnData := kind.getObjVal? "Fn" then
    let name := match fnData.getObjVal? "ident" with
      | .ok ident => extractFnName ident
      | _ => "unknown_fn"
    let def_ := match fnData.getObjVal? "def" with
      | .ok d => some d
      | _ => none
    let paramNames := match def_ with
      | some d => match d.getObjValAs? (Array Json) "params" with
        | .ok params => extractParamNames params
        | _ => []
      | none => []
    let paramTypes := match def_ with
      | some d => match d.getObjValAs? (Array Json) "params" with
        | .ok params => extractParamTypes params
        | _ => []
      | none => []
    let retType := match def_ with
      | some d => match d.getObjVal? "ret" with
        | .ok retJ => parseHaxType retJ
        | _ => .unknown
      | none => .unknown
    let body ← match def_ with
      | some d => parseHaxTExpr (← d.getObjVal? "body")
      | none => throw s!"Fn item '{name}' missing def.body"
    -- Apply for-loop reconstruction and assign normalization (via erase/lift roundtrip)
    let processed := normalizeAssignOpsTExpr (reconstructForLoopsTExpr body)
    -- Wrap body in identity let-bindings for parameters
    let wrapped := if paramNames.isEmpty then processed
      else paramNames.foldr (fun p acc =>
        let paramTy := match paramTypes.find? (·.1 == p) with
          | some (_, ty) => ty | none => .unknown
        TExpr.mk (.letBind p (TExpr.mk (.var p) paramTy) acc) processed.ty) processed
    return some (name, wrapped, ⟨paramTypes, retType⟩)
  else if let .ok (.arr constData) := kind.getObjVal? "Const" then
    let name := match constData.toList with
      | (.arr ident) :: _ => extractFnName (.arr ident)
      | _ => "unknown_const"
    let body ← match constData.toList[3]? with
      | some bodyJ => parseHaxTExpr bodyJ
      | none => throw s!"Const item '{name}' missing body"
    let processed := normalizeAssignOpsTExpr (reconstructForLoopsTExpr body)
    return some (name, processed, ⟨[], .unknown⟩)
  else return none

/-- Parse a full hax export file into typed TExprs.
    Returns (combined TExpr as ImpExpr for backward compat, fnTypes, and the typed defs list). -/
partial def parseHaxFileWithTExpr (j : Json) :
    Except String (ImpExpr × List (String × FnTypeInfo) × List (String × TExpr)) := do
  let rec parseItemsTExpr (items : List Json) :
      Except String (List (String × TExpr × FnTypeInfo)) := do
    let mut result : List (String × TExpr × FnTypeInfo) := []
    for item in items do
      match ← parseHaxItemTExpr item with
      | some r => result := result ++ [r]
      | none =>
        let kind := (item.getObjVal? "kind").toOption
        match kind with
        | some kindJ =>
          match kindJ.getObjVal? "Mod" with
          | .ok (.arr modData) =>
            match modData.toList[1]? with
            | some subJ =>
              match subJ with
              | .arr subItems =>
                let sub ← parseItemsTExpr subItems.toList
                result := result ++ sub
              | _ => pure ()
            | _ => pure ()
          | .ok modData =>
            match modData.getObjValAs? (Array Json) "items" with
            | .ok subItems =>
              let sub ← parseItemsTExpr subItems.toList
              result := result ++ sub
            | _ => pure ()
          | _ => pure ()
        | none => pure ()
    return result
  match j with
  | .arr items =>
    let parsed ← parseItemsTExpr items.toList
    match parsed with
    | [] => throw "no functions or constants found in hax export"
    | _ =>
      let expr := parsed.foldr (fun (name, te, _) acc => .letBind name te.erase acc) .unitVal
      let fnTypes := parsed.map fun (name, _, ti) => (name, ti)
      let texprs := parsed.map fun (name, te, _) => (name, te)
      return (expr, fnTypes, texprs)
  | _ =>
    let te ← parseHaxTExpr j
    let processed := normalizeAssignOpsTExpr (reconstructForLoopsTExpr te)
    return (processed.erase, [], [("expr", processed)])

/-! ## Struct Definition Extraction

Parse struct definitions from `hax_frontend_export.json` to generate
correct preambles (struct constructors, projections, dependency classes). -/

/-- A field in a Rust struct. -/
structure FieldInfo where
  name : String
  /-- "int" for integer scalars, "array" for Array/Vec types,
      or a struct name for nested struct types. -/
  typeTag : String
  /-- Full parsed type (when available from hax JSON). -/
  impType : ImpType := .unknown
  deriving Inhabited

/-- A Rust struct definition with its fields in order. -/
structure StructInfo where
  name : String
  fields : List FieldInfo
  deriving Inhabited

/-- Classify a hax type JSON value into "int", "array", or a struct name. -/
private def classifyFieldType (tyVal : Json) : String :=
  -- Uint types: {"Uint": "U8"}, {"Uint": "U16"}, etc.
  if tyVal.getObjVal? "Uint" |>.isOk then "int"
  -- Int types: {"Int": "I8"}, etc.
  else if tyVal.getObjVal? "Int" |>.isOk then "int"
  -- Usize
  else if tyVal.getObjVal? "Usize" |>.isOk then "int"
  -- Bool
  else if tyVal.getObjVal? "Bool" |>.isOk then "int"
  -- Param: generic type parameter (e.g., `E` in `struct Foo<E> { field: E }`)
  -- In crypto crates, generic params are almost always byte arrays.
  -- Classify as "array" (safe default; will get `Array Int` type).
  else if tyVal.getObjVal? "Param" |>.isOk then "array"
  -- Array: {"Array": {id: ..., value: ...}}
  else if tyVal.getObjVal? "Array" |>.isOk then "array"
  -- Slice
  else if tyVal.getObjVal? "Slice" |>.isOk then "array"
  -- Vec (common in hax)
  else if ((toString tyVal).splitOn "Vec").length > 1 then "array"
  -- Adt referencing another struct
  else if let .ok adtJ := tyVal.getObjVal? "Adt" then
    -- Try to extract the struct name from the def_id path
    -- Navigate: Adt{id,value} → value.def_id.contents.value.path
    let structName := do
      let v ← adtJ.getObjVal? "value"
      let did ← v.getObjVal? "def_id"
      let c ← did.getObjVal? "contents"
      let vi ← c.getObjVal? "value"
      let path ← vi.getObjValAs? (Array Json) "path"
      let name := path.foldl (fun (acc : String) (p : Json) =>
        match p.getObjVal? "data" with
        | .ok d => match d.getObjVal? "TypeNs" with
          | .ok (.str n) => n
          | _ => acc
        | _ => acc) ""
      if name.isEmpty then .error "empty" else .ok name
    match structName with
    | .ok n => n
    | .error _ => "array"
  else "array"  -- default to array for unknown types

/-- Parse struct definitions from a hax JSON export array.
    Returns a list of `StructInfo` for all struct items. -/
partial def parseStructDefs (items : List Json) : List StructInfo :=
  let parseOneStruct (structData : Array Json) : Option StructInfo :=
    let name := match structData.toList with
      | (Json.arr nameSpan) :: _ => match nameSpan.toList with
        | (Json.str n) :: _ => n
        | _ => ""
      | _ => ""
    if name.isEmpty then none
    else
      let variantData := structData.toList[2]?
      match variantData with
      | some vd =>
        let structFields := vd.getObjVal? "Struct" |>.toOption
        match structFields with
        | some sf =>
          let fieldsJ := sf.getObjValAs? (Array Json) "fields" |>.toOption
          match fieldsJ with
          | some fields =>
            let fieldInfos := fields.toList.filterMap fun fj =>
              let ident := match fj.getObjVal? "ident" with
                | Except.ok (Json.arr identPair) => match identPair.toList with
                  | (Json.str n) :: _ => n
                  | _ => ""
                | _ => ""
              if ident.isEmpty then none
              else
                let ty := (fj.getObjVal? "ty").toOption
                let typeTag := match ty with
                  | some tyJ =>
                    let tyVal := (tyJ.getObjVal? "value").toOption
                    match tyVal with
                    | some v => classifyFieldType v
                    | none => "array"
                  | none => "array"
                let impTy := match ty with
                  | some tyJ => parseHaxType tyJ
                  | none => ImpType.unknown
                some { name := ident, typeTag := typeTag, impType := impTy : FieldInfo }
            some { name := name, fields := fieldInfos : StructInfo }
          | none => none
        | none => none
      | none => none
  items.foldl (fun acc item =>
    let kind := (item.getObjVal? "kind").toOption
    match kind with
    | some kindJ =>
      -- Recurse into Mod items: kind.Mod = [name_data, [sub_items]]
      let modStructs := match kindJ.getObjVal? "Mod" with
        | Except.ok (Json.arr modData) =>
          match modData.toList[1]? with
          | some (Json.arr subItems) => parseStructDefs subItems.toList
          | _ => []
        | _ => []
      let thisStruct := match kindJ.getObjVal? "Struct" with
        | Except.ok (Json.arr sd) => parseOneStruct sd
        | _ => none
      acc ++ modStructs ++ thisStruct.toList
    | none => acc) []

/-- Parse struct defs from a top-level hax JSON (array of items). -/
def parseStructDefsFromJson (j : Json) : List StructInfo :=
  let raw := match j with
    | .arr items => parseStructDefs items.toList
    | _ => []
  -- Deduplicate by struct name (keep first occurrence)
  raw.foldl (fun acc si =>
    if acc.any (·.name == si.name) then acc else acc ++ [si]) []

end SSProve.Hax.HaxAdapter

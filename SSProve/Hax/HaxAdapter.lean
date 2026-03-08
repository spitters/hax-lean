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
  -- Try to get the path and extract the last segment's name
  match j.getObjVal? "path" with
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
      match j.getObjValAs? String "krate" with
      | .ok k => k
      | _ => "unknown"
  | _ =>
    match j.getObjValAs? String "krate" with
    | .ok k => k
    | _ => "unknown"

/-- Extract a name from a hax `LocalIdent`.
    LocalIdent JSON: `{"name": "x", "id": ...}` -/
private def extractLocalIdentName (j : Json) : String :=
  match j.getObjValAs? String "name" with
  | .ok n => n
  | _ => "unknown"

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
      | .ok item =>
        match item.getObjVal? "def_id" with
        | .ok defId => extractDefIdName defId
        | _ => "unknown_fn"
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

/-- Map hax's TyKind to our ImpType. Simplified — complex types become `.unknown`. -/
partial def parseHaxType (j : Json) : ImpType :=
  -- Ty is a struct with a hash-consed `kind` field, or might be the TyKind directly
  let tyKind := match j.getObjVal? "kind" with
    | .ok k => k
    | _ => j
  match tyKind with
  | .str "Bool" => .bool
  | .str "Char" => .int  -- approximate
  | .str "Str" => .str
  | .str "Never" => .unknown
  | .str "Error" => .unknown
  | _ =>
    if let .ok _ := tyKind.getObjVal? "Int" then .int
    else if let .ok _ := tyKind.getObjVal? "Uint" then .int
    else if let .ok _ := tyKind.getObjVal? "Float" then .unknown  -- no float in our ImpType
    else if let .ok inner := tyKind.getObjVal? "Tuple" then
      -- Tuple wraps an ItemRef; we'd need to resolve it. Approximate.
      .unknown
    else if let .ok refData := tyKind.getObjVal? "Ref" then
      -- Ref(Region, Box<Ty>, Mutability)
      match refData with
      | .arr #[_, inner, mut_] =>
        .ref (parseHaxType inner) (mut_ == .str "Mut")
      | _ => .unknown
    else if let .ok _ := tyKind.getObjVal? "Slice" then .unknown
    else if let .ok paramData := tyKind.getObjVal? "Param" then
      match paramData.getObjValAs? String "name" with
      | .ok n => .typeVar n
      | _ => .unknown
    else if let .ok _ := tyKind.getObjVal? "Adt" then .unknown
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
        let name := match info.getObjValAs? String "variant_name" with
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
      | .arr #[n, _] =>
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
    | .str "Todo" => return .unitVal  -- placeholder for unhandled
    | _ => pure ()

    -- Struct variants: {"VariantName": {fields...}}
    if let .ok data := j.getObjVal? "VarRef" then
      let name := match data.getObjVal? "id" with
        | .ok id => extractLocalIdentName id
        | _ => "unknown_var"
      return .var name

    else if let .ok data := j.getObjVal? "GlobalName" then
      let name := match data.getObjVal? "item" with
        | .ok item => match item.getObjVal? "def_id" with
          | .ok defId => extractDefIdName defId
          | _ => "global"
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
      let name := match pat with
        | .varPat n => n
        | _ => "_let"
      -- Let in hax is a pattern-matching let, not a let-in-body.
      -- It's used inside blocks. We'll approximate as letBind with unitVal body.
      return .letBind name rhs .unitVal

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
      let name := match lhs with
        | .var n => n
        | _ => "_assign"
      return .assign name rhs

    else if let .ok data := j.getObjVal? "AssignOp" then
      let op := match data.getObjVal? "op" with
        | .ok opJ => binOpName opJ
        | _ => "op"
      let lhs ← parseHaxExpr (← data.getObjVal? "lhs")
      let rhs ← parseHaxExpr (← data.getObjVal? "rhs")
      let name := match lhs with
        | .var n => n
        | _ => "_assign"
      return .assign name (.app op [lhs, rhs])

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
      -- Cast: just pass through the source (our AST doesn't represent casts)
      parseHaxExpr (← data.getObjVal? "source")

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
      return .app "repeat" [value]

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
        | .ok item => match item.getObjVal? "def_id" with
          | .ok defId => extractDefIdName defId
          | _ => "const"
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
      match intData with
      | .arr #[nJ, _] =>
        let n := match nJ.getStr? with
          | .ok s => s.toInt?.getD 0
          | _ => match nJ.getNat? with
            | .ok n => n
            | _ => 0
        .lit (.int (if neg then -n else n))
      | _ => .lit (.int 0)
    else .app "literal" []  -- char, float, string, etc.

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
      let name := match pat with
        | .varPat n => n
        | _ => "_let"
      let init ← match data.getObjVal? "initializer" with
        | .ok (.null) => pure .unitVal
        | .ok e => parseHaxExpr e
        | _ => pure .unitVal
      return .letBind name init .unitVal  -- body filled in by stmtsToSeq
    else
      return .unitVal

  /-- Convert a list of statement expressions into nested seq/letBind. -/
  stmtsToSeq (stmts : List ImpExpr) (tail : ImpExpr) : ImpExpr :=
    match stmts with
    | [] => tail
    | [s] =>
      match s with
      | .letBind n v .unitVal => .letBind n v tail
      | _ => .seq s tail
    | s :: rest =>
      match s with
      | .letBind n v .unitVal => .letBind n v (stmtsToSeq rest tail)
      | _ => .seq s (stmtsToSeq rest tail)

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
    let name := match j.getObjVal? "info" with
      | .ok info => match info.getObjValAs? String "variant_name" with
        | .ok n => n
        | _ => match info.getObjValAs? String "type_name" with
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

/-- Parse a hax expression and also extract the type, returning a TExpr. -/
partial def parseHaxTExpr (j : Json) : Except String TExpr := do
  let expr ← parseHaxExpr j
  let ty := match j.getObjVal? "ty" with
    | .ok tyJ => parseHaxType tyJ
    | _ => .unknown
  return TExpr.ofImpExpr expr ty
where
  /-- Lift an ImpExpr to TExpr with a given type (applied to the root, unknown for sub-exprs). -/
  TExpr.ofImpExpr (e : ImpExpr) (ty : ImpType) : TExpr :=
    .mk (liftKind e) ty
  liftKind (e : ImpExpr) : TExprKind :=
    match e with
    | .lit v => .lit v
    | .var n => .var n
    | .unitVal => .unitVal
    | .continue_ => .continue_
    | .letBind n v b => .letBind n (TExpr.ofImpExpr v .unknown) (TExpr.ofImpExpr b .unknown)
    | .app f args => .app f (args.map fun a => TExpr.ofImpExpr a .unknown)
    | .tuple es => .tuple (es.map fun e => TExpr.ofImpExpr e .unknown)
    | .proj e i => .proj (TExpr.ofImpExpr e .unknown) i
    | .ifThenElse c t e => .ifThenElse (TExpr.ofImpExpr c .unknown) (TExpr.ofImpExpr t .unknown) (TExpr.ofImpExpr e .unknown)
    | .match_ s arms => .match_ (TExpr.ofImpExpr s .unknown) (arms.map fun (p, b) => (p, TExpr.ofImpExpr b .unknown))
    | .seq e1 e2 => .seq (TExpr.ofImpExpr e1 .unknown) (TExpr.ofImpExpr e2 .unknown)
    | .borrow e => .borrow (TExpr.ofImpExpr e .unknown)
    | .deref e => .deref (TExpr.ofImpExpr e .unknown)
    | .assign n rhs => .assign n (TExpr.ofImpExpr rhs .unknown)
    | .forLoop v lo hi body => .forLoop v (TExpr.ofImpExpr lo .unknown) (TExpr.ofImpExpr hi .unknown) (TExpr.ofImpExpr body .unknown)
    | .whileLoop c body => .whileLoop (TExpr.ofImpExpr c .unknown) (TExpr.ofImpExpr body .unknown)
    | .break_ none => .break_ none
    | .break_ (some e) => .break_ (some (TExpr.ofImpExpr e .unknown))
    | .earlyReturn e => .earlyReturn (TExpr.ofImpExpr e .unknown)
    | .questionMark e => .questionMark (TExpr.ofImpExpr e .unknown)
    | .forFold v lo hi body => .forFold v (TExpr.ofImpExpr lo .unknown) (TExpr.ofImpExpr hi .unknown) (TExpr.ofImpExpr body .unknown)
    | .whileFold c body => .whileFold (TExpr.ofImpExpr c .unknown) (TExpr.ofImpExpr body .unknown)
    | .forFoldReturn v lo hi body => .forFoldReturn v (TExpr.ofImpExpr lo .unknown) (TExpr.ofImpExpr hi .unknown) (TExpr.ofImpExpr body .unknown)
    | .whileFoldReturn c body => .whileFoldReturn (TExpr.ofImpExpr c .unknown) (TExpr.ofImpExpr body .unknown)
    | .cfBreak e => .cfBreak (TExpr.ofImpExpr e .unknown)
    | .cfContinue e => .cfContinue (TExpr.ofImpExpr e .unknown)
    | .cfBreakContinue e => .cfBreakContinue (TExpr.ofImpExpr e .unknown)

end SSProve.Hax.HaxAdapter

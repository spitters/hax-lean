/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.ClassEmit

/-!
# hax-lib contracts

The opt-in `--emit-contracts` mode of haxpipeT, after the F* backend of hax.

hax-lib encodes a contract as a separate predicate function. The attribute
`#[requires(φ)]` or `#[ensures(|r| ψ)]` on a function `f` expands to a function
`requires` (resp. `ensures`) over the inputs of `f` (and its result, and the
final value of each `&mut` input), tagged `Uid(uid)`, and tags `f` with
`AssociatedItem { role, item: uid }`. In the hax frontend export these tags are
attributes `#[_hax::json("…")]` holding an `AttrPayload` as JSON
(`itemPayloads`). `#[hax_lib::lemma]` tags a function `Lemma`.

This module reads those payloads and renders:

* for a function `f` with a contract, the definitions `f_requires` and
  `f_ensures`, the translations of the predicate bodies to `Prop`, and
  `f_contract : Prop`, the statement that every input satisfying `f_requires`
  gives a result of the surface definition `f` satisfying `f_ensures`;
* for a lemma `g`, `g_stmt : Prop`, its statement;
* under `--emit-classes`, for each trait with a contract on a method or on a
  method of one of its `impl`s: a precondition field `m_pre` and a
  postcondition field `m_post` in the class of the trait
  (`ClassHooks.contractMethods`), the trait's own clauses `T.m_requires` and
  `T.m_ensures`, and the class `T.Contract Self` of refinement obligations of an
  instance: the trait's precondition implies the instance's, the instance's
  postcondition implies the trait's, and the method satisfies the instance's
  pre- and postcondition. Each instance supplies its `impl`'s own clauses as
  the two fields, or `True` for a clause the `impl` does not state.

Statements are `Prop` definitions: the proofs belong to a hand-written file,
since extracting the crate again overwrites the generated one. The requires
clause of `f` is the guard under which an ascent correspondence (`FnCorres`)
relates the literal of `f` to the surface definition, so `f_contract` carries
over to the literal.

A predicate body is read over the mathematical integers: the surface types
render every machine integer as `Int`, the hax-lib embedding `lift`/`to_int`
is the identity, and `int!(n)` is the numeral `n`. Arithmetic is `Int`
arithmetic, which agrees with the machine operation where that does not
overflow. The body language is comparisons, arithmetic, the Boolean and
hax-lib `Prop` connectives, `forall`/`exists` over a closure, `if`, `let`,
calls of emitted definitions, and literals; any other construct is an error
naming the item (`renderExpr`).

The predicate items and the items hax-lib marks `late_skip` (the `const _`
block around a predicate and the `future` helper) are never ordinary
definitions (`dropContractItems`).
-/

@[expose] public section

namespace Hax.ContractEmit

open Lean (Json)
open Hax.HaxAdapter (parseHaxType parseHaxTExpr parseHaxPat extractFnName
  extractDefIdName defIdLeafName ImplSelfTypeMap)
open Hax.ClassEmit (ClassHooks TraitDef ImplInstance argTypeStr resultBinderName
  typeParamNames)

/-! ## Payloads -/

/-- The hax-lib payloads of an item: each attribute `#[_hax::json("…")]` of
    the item's own attribute list (`attributes.attributes`), parsed as JSON.
    The attribute's tokens are a string literal whose contents are the
    payload. -/
def itemPayloads (item : Json) : List Json :=
  let attrs : List Json := match item.getObjVal? "attributes" with
    | .ok a => match a.getObjValAs? (Array Json) "attributes" with
      | .ok xs => xs.toList
      | _ => []
    | _ => []
  attrs.filterMap fun a => do
    let u ← (a.getObjVal? "Unparsed").toOption
    let path ← (u.getObjValAs? String "path").toOption
    guard (path == "_hax::json")
    let args ← (u.getObjVal? "args").toOption
    let d ← (args.getObjVal? "Delimited").toOption
    let toks ← (d.getObjValAs? String "tokens").toOption
    let lit ← (Json.parse toks).toOption
    let s ← lit.getStr?.toOption
    (Json.parse s).toOption

/-- The uid of a `Uid` payload. -/
def payloadUid (p : Json) : Option String := do
  let u ← (p.getObjVal? "Uid").toOption
  (u.getObjValAs? String "uid").toOption

/-- The role and the target uid of an `AssociatedItem` payload. -/
def payloadAssoc (p : Json) : Option (String × String) := do
  let a ← (p.getObjVal? "AssociatedItem").toOption
  let role ← (a.getObjValAs? String "role").toOption
  let it ← (a.getObjVal? "item").toOption
  let uid ← (it.getObjValAs? String "uid").toOption
  pure (role, uid)

/-- Whether a payload is `Lemma`. -/
def payloadIsLemma (p : Json) : Bool := p == Json.str "Lemma"

/-- Whether a payload is `ItemStatus(Included { late_skip: true })`. -/
def payloadLateSkip (p : Json) : Bool :=
  match p.getObjVal? "ItemStatus" with
  | .ok s => match s.getObjVal? "Included" with
    | .ok i => (i.getObjValAs? Bool "late_skip").toOption == some true
    | _ => false
  | _ => false

/-- The uid of the item associated with an item under `role`
    (`"Requires"` or `"Ensures"`). -/
def assocUid (item : Json) (role : String) : Option String :=
  (itemPayloads item).findSome? fun p => do
    let (r, uid) ← payloadAssoc p
    guard (r == role)
    pure uid

/-! ## Predicate items out of the ordinary definitions -/

/-- Whether an item is a predicate item of a contract (`Uid`) or an item
    hax-lib marks `late_skip`. With `lemmas`, a `Lemma` item also counts. -/
def isContractItem (lemmas : Bool) (item : Json) : Bool :=
  (itemPayloads item).any fun p =>
    (payloadUid p).isSome || payloadLateSkip p || (lemmas && payloadIsLemma p)

/-- The export without its contract items (`isContractItem`), at the top
    level and in the item lists of `Mod` items. -/
partial def dropContractItems (lemmas : Bool) (j : Json) : Json :=
  match j with
  | .arr xs =>
    .arr ((xs.filter fun it => !isContractItem lemmas it).map fun it =>
      match it.getObjVal? "kind" with
      | .ok k =>
        match k.getObjVal? "Mod" with
        | .ok (.arr md) =>
          it.setObjVal! "kind" (k.setObjVal! "Mod" (.arr (md.modify 1 (dropContractItems lemmas))))
        | .ok md =>
          match md.getObjVal? "items" with
          | .ok items =>
            it.setObjVal! "kind"
              (k.setObjVal! "Mod" (md.setObjVal! "items" (dropContractItems lemmas items)))
          | _ => it
        | _ => it
      | _ => it)
  | _ => j

/-- Every JSON object below `j` with an item attribute record (an
    `attributes` object holding an `attributes` list) and at least one hax-lib
    payload: the items, trait items and impl items of an export at any depth,
    including the items nested in a function body or a `const` block. -/
partial def payloadItems (j : Json) (acc : Array Json := #[]) : Array Json :=
  match j with
  | .arr xs => xs.foldl (fun a x => payloadItems x a) acc
  | .obj t =>
    let acc := if (itemPayloads j).isEmpty then acc else acc.push j
    t.toList.foldl (fun a (_, v) => payloadItems v a) acc
  | _ => acc

/-! ## Predicates -/

/-- The parts of a function item: its `generics`, its parameters and its body.
    A top-level item holds the parameters and body under `kind.Fn.def`, an
    `impl` item under `kind.Fn`. -/
def fnParts (item : Json) : Option (Json × Array Json × Json) := do
  let k ← (item.getObjVal? "kind").toOption
  let fnData ← (k.getObjVal? "Fn").toOption
  let defLike := (fnData.getObjVal? "def").toOption.getD fnData
  let generics := ((fnData.getObjVal? "generics").toOption <|>
    (item.getObjVal? "generics").toOption).getD .null
  let params ← (defLike.getObjValAs? (Array Json) "params").toOption
  let body := (defLike.getObjVal? "body").toOption.getD .null
  pure (generics, params, body)

/-- The name a pattern binds: the variable of a binding, `_` otherwise. -/
def patName : ImpPat → String
  | .varPat n => n
  | _ => "_"

/-- The parameters of a function, with a tuple pattern over a tuple type
    split into its components (the final parameter of an `ensures` predicate
    binds the final values of the `&mut` inputs and the result as one
    tuple). -/
def expandParams (params : Array Json) : List (String × ImpType) :=
  params.toList.flatMap fun p =>
    let ty := match p.getObjVal? "ty" with
      | .ok t => parseHaxType t
      | _ => .unknown
    let pat := match p.getObjVal? "pat" with
      | .ok pj => parseHaxPat pj
      | _ => .wildcard
    match pat, ty with
    | .tuplePat ps, .tuple ts =>
      if ps.length == ts.length then (ps.zip ts).map fun (q, t) => (patName q, t)
      else [(patName pat, ty)]
    | q, t => [(patName q, t)]

/-- Whether a type is the unit type. -/
def isUnitTy : ImpType → Bool
  | .unit => true
  | .tuple [] => true
  | _ => false

/-- Rewrite each call `Int::_unsafe_from_str("n")` (the expansion of
    `int!(n)`) below an expression node to the integer literal `n`. -/
partial def rewriteIntLits (j : Json) : Json :=
  match j with
  | .arr xs => .arr (xs.map rewriteIntLits)
  | .obj t =>
    let asLit : Option Json := do
      let c ← (j.getObjVal? "contents").toOption
      let call ← (c.getObjVal? "Call").toOption
      let f ← (call.getObjVal? "fun").toOption
      guard ((f.compress.splitOn "_unsafe_from_str").length > 1)
      let s ← findStr call
      guard (s.toList.all Char.isDigit && !s.isEmpty)
      let lit := Json.mkObj [("Literal", Json.mkObj [
        ("lit", Json.mkObj [("node", Json.mkObj [("Int", .arr #[.str s, .str "Unsuffixed"])])]),
        ("neg", .bool false)])]
      pure (j.setObjVal! "contents" lit)
    match asLit with
    | some l => l
    | none => Json.mkObj (t.toList.map fun (k, v) => (k, rewriteIntLits v))
  | _ => j
where
  /-- The first string literal `{"Str": [s, _]}` below a node. -/
  findStr : Json → Option String
    | .arr xs => xs.toList.findSome? findStr
    | j@(.obj t) =>
      match j.getObjVal? "Str" with
      | .ok (.arr a) => match (a[0]? : Option Json) with
        | some (.str s) => some s
        | _ => none
      | _ => t.toList.findSome? fun (_, v) => findStr v
    | _ => none

/-! ## Rendering a predicate body -/

/-- A rendered subexpression: a proposition, or a term with its type. -/
inductive Rendered where
  | prop (s : String)
  | term (s : String) (ty : ImpType)
  deriving Inhabited

/-- Whether a type is the hax-lib `Prop`. -/
def isHaxProp : ImpType → Bool
  | .adt n _ => n == "Prop" || n.endsWith "::Prop" || n.endsWith ".Prop"
  | _ => false

/-- The rendered subexpression as a proposition: a Boolean term `b` is
    `b = true`, a hax-lib `Prop` term is itself. -/
def Rendered.asProp : Rendered → Except String String
  | .prop s => pure s
  | .term s .bool => pure s!"({s} = true)"
  | .term s ty => if isHaxProp ty then pure s else
      throw s!"the term `{s}` is used as a proposition"

/-- The rendered subexpression as a term: a proposition `p` is `decide p`. -/
def Rendered.asTerm : Rendered → String
  | .prop s => s!"(decide {s})"
  | .term s _ => s

/-- The operator name without its width tag (`Div#i32` is `Div`). -/
def baseOp (f : String) : String := (f.splitOn "#").headD f

/-- A short description of an expression form, for error messages. -/
def kindTag : TExprKind → String
  | .match_ .. => "match"
  | .proj .. => "tuple or field projection"
  | .tuple .. => "tuple"
  | .lam .. => "closure outside forall/exists"
  | .assign .. => "assignment"
  | .forLoop .. | .forLoopRev .. | .whileLoop .. => "loop"
  | .earlyReturn .. => "return"
  | .questionMark .. => "`?`"
  | _ => "expression form"

/-- The body of a predicate as Lean text. `callable` holds the definitions a
    call may name. An expression outside the language the module docstring
    lists is an error. -/
partial def renderExpr (callable : List String) (e : TExpr) : Except String Rendered := do
  match e.kind with
  | .lit (.bool true) => pure (.prop "True")
  | .lit (.bool false) => pure (.prop "False")
  | .lit (.int n) => pure (.term (if n < 0 then s!"({n})" else s!"{n}") e.ty)
  | .lit (.uintLit _ n) => pure (.term s!"{n}" e.ty)
  | .lit (.sintLit _ n) => pure (.term (if n < 0 then s!"({n})" else s!"{n}") e.ty)
  | .lit .unit | .unitVal | .tuple [] => pure (.term "()" .unit)
  | .var n => pure (.term (sanitizeName n) e.ty)
  | .deref a | .borrow a | .ann a => renderExpr callable a
  | .seq a b =>
    match a.kind with
    | .unitVal => renderExpr callable b
    | _ => throw "a statement sequence"
  | .letBind n v b =>
    let v ← renderExpr callable v
    match ← renderExpr callable b with
    | .prop s => pure (.prop s!"(let {sanitizeName n} := {v.asTerm}; {s})")
    | .term s ty => pure (.term s!"(let {sanitizeName n} := {v.asTerm}; {s})" ty)
  | .ifThenElse c t f =>
    let c ← (← renderExpr callable c).asProp
    match ← renderExpr callable t, ← renderExpr callable f with
    | .prop t, .prop f => pure (.prop s!"(({c} → {t}) ∧ (¬{c} → {f}))")
    | t, f => pure (.term s!"(if {c} then {t.asTerm} else {f.asTerm})" e.ty)
  | .app f args => renderApp (baseOp f) args e.ty
  | k => throw s!"unsupported {kindTag k}"
where
  /-- A call or an operator application. -/
  renderApp (f : String) (args : List TExpr) (ty : ImpType) : Except String Rendered := do
    let arith : List (List String × String) :=
      [(["Add", "add"], "+"), (["Sub", "sub"], "-"), (["Mul", "mul"], "*"),
       (["Div", "div"], "/"), (["Rem", "rem"], "%")]
    let cmp : List (List String × String) :=
      [(["Lt", "lt"], "<"), (["Le", "le"], "≤"), (["Gt", "gt"], ">"), (["Ge", "ge"], "≥")]
    let conn : List (List String × String) :=
      [(["&&", "and", "BitAnd", "bitand"], "∧"), (["||", "or", "BitOr", "bitor"], "∨"),
       (["implies"], "→")]
    let identity := ["lift", "to_int", "into", "from", "from_bool", "to_prop", "clone"]
    if callable.contains f then
      let as ← args.mapM (renderExpr callable)
      if as.isEmpty then return .term (sanitizeName f) ty
      return .term s!"({sanitizeName f} {" ".intercalate (as.map (·.asTerm))})" ty
    match args with
    | [a, b] =>
      if let some (_, op) := arith.find? (·.1.contains f) then
        let a ← renderExpr callable a
        let b ← renderExpr callable b
        return .term s!"({a.asTerm} {op} {b.asTerm})" ty
      if let some (_, op) := cmp.find? (·.1.contains f) then
        let a ← renderExpr callable a
        let b ← renderExpr callable b
        return .prop s!"({a.asTerm} {op} {b.asTerm})"
      if f == "Eq" || f == "eq" || f == "Ne" || f == "ne" then
        let a ← renderExpr callable a
        let b ← renderExpr callable b
        let isEq := f == "Eq" || f == "eq"
        match a, b with
        | .prop p, .prop q =>
          return .prop (if isEq then s!"({p} ↔ {q})" else s!"(¬({p} ↔ {q}))")
        | _, _ =>
          return .prop s!"({a.asTerm} {if isEq then "=" else "≠"} {b.asTerm})"
      if let some (_, op) := conn.find? (·.1.contains f) then
        let a ← (← renderExpr callable a).asProp
        let b ← (← renderExpr callable b).asProp
        return .prop s!"({a} {op} {b})"
      throw s!"call of `{f}`"
    | [a] =>
      if identity.contains f then return ← renderExpr callable a
      if f == "Not" || f == "not" then
        let a ← (← renderExpr callable a).asProp
        return .prop s!"(¬{a})"
      if f == "Neg" || f == "neg" then
        let a ← renderExpr callable a
        return .term s!"(-{a.asTerm})" ty
      if f == "forall" || f == "exists" then
        match a.kind with
        | .lam [x] body =>
          let q := if f == "forall" then "∀" else "∃"
          let b ← (← renderExpr callable body).asProp
          return .prop s!"({q} {sanitizeName x}, {b})"
        | _ => throw s!"`{f}` over an argument that is not a one-parameter closure"
      throw s!"call of `{f}`"
    | _ => throw s!"call of `{f}`"

/-- A parsed and rendered predicate: its type parameters, its parameters and
    its body as a proposition. -/
structure Pred where
  typeParams : List String := []
  params : List (String × ImpType)
  body : String
  deriving Inhabited

/-- The predicate item with a given uid, parsed and rendered. -/
def renderPred (preds : List (String × Json)) (implMap : ImplSelfTypeMap)
    (callable : List String) (uid : String) : Except String Pred := do
  let some item := preds.lookup uid | throw s!"no predicate item has the uid {uid}"
  let some (generics, params, body) := fnParts item | throw "the predicate item is not a function"
  let te ← parseHaxTExpr (rewriteIntLits body) implMap
  let r ← renderExpr callable te
  let s ← r.asProp
  pure { typeParams := typeParamNames generics, params := expandParams params, body := s }

/-! ## The plan -/

/-- The contract of a free function. -/
structure FnContract where
  /-- The emitted name of the function. -/
  fn : String
  /-- The function's parameters. -/
  params : List (String × ImpType)
  requires : Option Pred := none
  ensures : Option Pred := none
  /-- The arguments of `fn_ensures`: the function's arguments followed by the
      final values of the `&mut` parameters and the result, read from `out`,
      the value of the surface definition. -/
  ensArgs : List String := []
  deriving Inhabited

/-- A `#[hax_lib::lemma]` function. -/
structure LemmaStmt where
  name : String
  params : List (String × ImpType)
  requires : Option String := none
  formula : String
  deriving Inhabited

/-- The contracts rendered after the definitions. -/
structure Plan where
  fns : List FnContract := []
  lemmas : List LemmaStmt := []
  deriving Inhabited

/-- Binders `(x : T)` for parameters under a struct lookup. -/
def bindersStr (sl : String → Option String) (ps : List (String × ImpType)) : String :=
  String.join (ps.map fun (p, ty) =>
    s!" ({sanitizeName p} : {if ty.isUnknown then "_" else ty.toLeanTypeStrSurface sl})")

/-- The arguments of a predicate applied to the arguments `lead` of its
    function and the further arguments `extra`. The `ensures` predicate of a
    function without parameters has a first parameter of unit type; it
    receives `()`. -/
def predArgs (p : Pred) (lead extra : List String) : Except String (List String) := do
  let args :=
    if lead.isEmpty && p.params.length == extra.length + 1 &&
        (p.params.head?.map (isUnitTy ·.2)).getD false then
      "()" :: extra
    else lead ++ extra
  if args.length != p.params.length then
    throw s!"the predicate has {p.params.length} parameters, the function supplies {args.length}"
  pure args

/-- An application `f a₁ … aₙ`, parenthesized. -/
def appStr (f : String) (args : List String) : String :=
  if args.isEmpty then f else s!"({f} {" ".intercalate args})"

/-- The type parameter binders of a predicate that its parameter types
    mention, `{T : Type}`. -/
def predTypeBinders (p : Pred) : List String :=
  p.typeParams.filter fun t => p.params.any fun (_, ty) =>
    ((ty.toLeanTypeStrSurface).splitOn t).length > 1

/-- A predicate definition. -/
def renderPredDef (sl : String → Option String) (doc name extraBinders : String)
    (p : Pred) : String :=
  let tb := String.join ((predTypeBinders p).map fun t => s!" \{{t} : Type}")
  s!"/-- {doc} -/\ndef {name}{tb}{extraBinders}{bindersStr sl p.params} : Prop :=\n  {p.body}\n"

/-- The definitions of a function contract: `f_requires`, `f_ensures` and the
    statement `f_contract`. `generic` holds the binders of a generic function. -/
def renderFnContract (sl : String → Option String) (hooks : ClassHooks)
    (c : FnContract) : String :=
  let g := hooks.genericFns.find? (·.name == c.fn)
  let gb := match g with
    | some g =>
      let contracts := g.bounds.filter fun (t, _) => hooks.contractMethods.any (·.1 == t)
      " " ++ g.binders ++ String.join (contracts.map fun (t, p) => s!" [{t}.Contract {p}]")
    | none => ""
  let f := sanitizeName c.fn
  let names := c.params.map fun (p, _) => sanitizeName p
  let reqDef := match c.requires with
    | some p => renderPredDef sl s!"The `requires` clause of `{c.fn}`." s!"{f}_requires" gb p
    | none => ""
  let ensDef := match c.ensures with
    | some p => renderPredDef sl s!"The `ensures` clause of `{c.fn}`." s!"{f}_ensures" gb p
    | none => ""
  let stmt : Option String := do
    let _ ← c.ensures
    let call := appStr f names
    let hyp := match c.requires with
      | some _ => s!"{appStr s!"{f}_requires" names} → "
      | none => ""
    let concl := s!"let out := {call}; {appStr s!"{f}_ensures" c.ensArgs}"
    let binders := gb ++ bindersStr sl c.params
    let q := if binders.isEmpty then "" else s!"∀{binders}, "
    pure s!"/-- The contract of `{c.fn}`: every input satisfying `{f}_requires` gives a\n    result of `{c.fn}` satisfying `{f}_ensures`. -/\ndef {f}_contract : Prop :=\n  {q}{hyp}{concl}\n"
  reqDef ++ ensDef ++ stmt.getD ""

/-- The statement of a lemma. -/
def renderLemma (sl : String → Option String) (l : LemmaStmt) : String :=
  let binders := bindersStr sl l.params
  let q := if binders.isEmpty then "" else s!"∀{binders}, "
  let hyp := match l.requires with
    | some r => s!"{r} → "
    | none => ""
  s!"/-- The statement of the lemma `{l.name}`. -/\ndef {sanitizeName l.name}_stmt : Prop :=\n  {q}{hyp}{l.formula}\n"

/-- The contracts of a plan, rendered after the definitions. -/
def renderPlan (sl : String → Option String) (hooks : ClassHooks) (p : Plan) : String :=
  let parts := p.fns.map (renderFnContract sl hooks) ++ p.lemmas.map (renderLemma sl)
  if parts.isEmpty then "" else "\n".intercalate parts ++ "\n"

/-! ## Traits -/

/-- The contract clauses of one trait method. -/
structure MethodContract where
  method : String
  requires : Option Pred := none
  ensures : Option Pred := none
  deriving Inhabited

/-- The trait-level definitions and the `Contract` class of a trait. -/
def renderTraitContract (sl : String → Option String) (td : TraitDef)
    (ms : List MethodContract) : Except String String := do
  let t := td.name
  let mut defs : List String := []
  let mut fields : List String := []
  for (m, ps, r) in td.methods do
    let mc := (ms.find? (·.method == m)).getD { method := m }
    let mn := sanitizeName m
    let names := ps.map fun (p, _) => sanitizeName p
    let res := resultBinderName (ps.map (·.1))
    let binders := bindersStr sl ps
    let q (bs : String) : String := if bs.isEmpty then "" else s!"∀{bs}, "
    let self := "(Self := Self)"
    let field (f : String) (args : List String) : String :=
      appStr s!"{t}.{f} {self}" args
    let predCall (p : Pred) (name : String) (args : List String) : String :=
      let tyArgs := (predTypeBinders p).map fun tv => s!"({tv} := Self)"
      appStr name (tyArgs ++ args)
    if let some p := mc.requires then
      defs := defs ++ [renderPredDef sl s!"The `requires` clause of the method `{m}` of the trait `{t}`."
        s!"{t}.{mn}_requires" "" p]
      let args ← predArgs p names []
      fields := fields ++ [s!"  {mn}_pre_of_requires : {q binders}{predCall p s!"{t}.{mn}_requires" args} → {field s!"{mn}_pre" names}"]
    if let some p := mc.ensures then
      defs := defs ++ [renderPredDef sl s!"The `ensures` clause of the method `{m}` of the trait `{t}`."
        s!"{t}.{mn}_ensures" "" p]
      let args ← predArgs p names [res]
      let bs := binders ++ s!" ({res} : {r.toLeanTypeStrSurface sl})"
      fields := fields ++ [s!"  {mn}_ensures_of_post : {q bs}{field s!"{mn}_post" (names ++ [res])} → {predCall p s!"{t}.{mn}_ensures" args}"]
    fields := fields ++ [s!"  {mn}_sound : {q binders}{field s!"{mn}_pre" names} → {field s!"{mn}_post" (names ++ [field mn names])}"]
  let cls := s!"/-- The contract obligations of an instance of `{t}`: each method's\n    precondition field is implied by the trait's `requires` clause, its\n    postcondition field implies the trait's `ensures` clause, and the method\n    satisfies its precondition and postcondition fields. -/\nclass {t}.Contract (Self : Type) [{t} Self] : Prop where\n" ++ "\n".intercalate fields ++ "\n"
  pure ("\n".intercalate defs ++ (if defs.isEmpty then "" else "\n") ++ cls)

/-- The precondition and postcondition fields of an instance of a trait with
    contract methods, from the `impl`'s own clauses of each method (`True` for
    a clause the `impl` does not state). -/
def instanceContractFields (td : TraitDef) (ms : List MethodContract) :
    Except String (List (String × String)) := do
  let mut out : List (String × String) := []
  for (m, ps, _) in td.methods do
    let mc := (ms.find? (·.method == m)).getD { method := m }
    let mn := sanitizeName m
    let n := ps.length
    let lam (p : Option Pred) (arity : Nat) : Except String String := do
      match p with
      | none =>
        pure (if arity == 0 then "True"
          else s!"fun {" ".intercalate (List.replicate arity "_")} => True")
      | some p =>
        -- The unit parameter of a method without parameters is dropped.
        let params :=
          if n == 0 && p.params.length == arity + 1 &&
              (p.params.head?.map (isUnitTy ·.2)).getD false then p.params.drop 1
          else p.params
        if params.length != arity then
          throw s!"the clause of `{m}` has {params.length} parameters, the method {arity}"
        if arity == 0 then pure p.body
        else pure s!"fun {" ".intercalate (params.map fun (x, _) => sanitizeName x)} => {p.body}"
    out := out ++ [(s!"{mn}_pre", ← lam mc.requires n), (s!"{mn}_post", ← lam mc.ensures (n + 1))]
  pure out

/-! ## Building the plan -/

/-- The interning id of an item's `owner_id`. -/
def ownerId (it : Json) : Option Nat := do
  let oid ← (it.getObjVal? "owner_id").toOption
  let c ← (oid.getObjVal? "contents").toOption
  (c.getObjValAs? Nat "id").toOption

/-- The short name of the trait an `impl` item implements. -/
def implTraitName (impl : Json) : Option String := do
  let tr ← (impl.getObjVal? "of_trait").toOption
  let tv ← (tr.getObjVal? "value").toOption
  let defId ← (tv.getObjVal? "def_id").toOption
  defIdLeafName defId

/-- The contract clauses of the methods of a trait or `impl` item list. -/
def methodContracts (preds : List (String × Json)) (implMap : ImplSelfTypeMap)
    (callable : List String) (ctx : String) (items : List Json) :
    List MethodContract × List String :=
  items.foldl (init := ([], [])) fun (acc, errs) it =>
    let m := match it.getObjVal? "ident" with
      | .ok i => extractFnName i
      | _ => "unknown_fn"
    let one (role : String) : Option Pred × List String :=
      match assocUid it role with
      | none => (none, [])
      | some uid => match renderPred preds implMap callable uid with
        | .ok p => (some p, [])
        | .error e => (none, [s!"{ctx}::{m} {role.toLower}: {e}"])
    let (r, e1) := one "Requires"
    let (s, e2) := one "Ensures"
    if r.isNone && s.isNone then (acc, errs ++ e1 ++ e2)
    else (acc ++ [{ method := m, requires := r, ensures := s }], errs ++ e1 ++ e2)

/-- Build the contracts of an extraction.

    `srcs` are the exports the contracts are read from (the crate's and, under
    `--emit-classes`, the trait export), `collisions` and `localCrate` the
    naming context of the crate's export without its contract items
    (`HaxAdapter.fnNameCollisions`, `HaxAdapter.localCrateOfExport`), `emitted`
    the names of the emitted definitions, `selected`
    the `--filter` predicate on names, `writeReturns` the write-back table
    (`ThreadMutations.mutWriteReturns`: per function, the `&mut` parameters it
    returns and whether it returns a Rust result besides) and `hooks` the class
    plan. Returns the plan and the class plan with its contract fields, or the
    list of clauses outside the predicate language. -/
def build (srcs : List Json) (collisions : List String)
    (localCrate : HaxAdapter.LocalCrate) (emitted : List String)
    (selected : String → Bool) (writeReturns : List (String × List String × Bool))
    (hooks : ClassHooks) : Except (List String) (Plan × ClassHooks) := do
  let items := (srcs.foldl (fun acc j => payloadItems j acc) #[]).toList
  let preds : List (String × Json) := items.filterMap fun it => do
    let uid ← (itemPayloads it).findSome? payloadUid
    pure (uid, it)
  let implMap : ImplSelfTypeMap := { collisions, localCrate }
  let mut errs : List String := []
  let mut fns : List FnContract := []
  let mut lemmas : List LemmaStmt := []
  let mut seen : List String := []
  -- Free functions and lemmas: items with a `visibility` and a `Fn` kind.
  for it in items do
    if (it.getObjVal? "visibility").toOption.isNone then continue
    let some (_, params, _) := fnParts it | continue
    let pls := itemPayloads it
    let baseName := match (it.getObjVal? "kind").toOption >>= (·.getObjVal? "Fn" |>.toOption) with
      | some fnData => match fnData.getObjVal? "ident" with
        | .ok i => extractFnName i
        | _ => "unknown_fn"
      | none => "unknown_fn"
    let name := if collisions.contains baseName then
        match it.getObjVal? "def_id" with
        | .ok d => extractDefIdName d collisions
        | _ => baseName
      else baseName
    if seen.contains name then continue
    let fparams := expandParams params
    if pls.any payloadIsLemma then
      seen := name :: seen
      if !selected name then continue
      let some uid := assocUid it "Ensures" | continue
      match renderPred preds implMap emitted uid with
      | .error e => errs := errs ++ [s!"lemma `{name}`: {e}"]
      | .ok p =>
        let req : Except String (Option String) := match assocUid it "Requires" with
          | none => pure none
          | some u => (renderPred preds implMap emitted u).map (some ·.body)
        match req with
        | .error e => errs := errs ++ [s!"lemma `{name}` requires: {e}"]
        | .ok r =>
          let lps := p.params.take fparams.length
          let l : LemmaStmt := { name := name, params := lps, requires := r, formula := p.body }
          lemmas := lemmas ++ [l]
      continue
    let rU := assocUid it "Requires"
    let eU := assocUid it "Ensures"
    if rU.isNone && eU.isNone then continue
    seen := name :: seen
    if !emitted.contains name then continue
    let r : Except String (Option Pred) := match rU with
      | none => pure none
      | some u => (renderPred preds implMap emitted u).map some
    let e : Except String (Option Pred) := match eU with
      | none => pure none
      | some u => (renderPred preds implMap emitted u).map some
    match r, e with
    | .error m, _ => errs := errs ++ [s!"`{name}` requires: {m}"]
    | _, .error m => errs := errs ++ [s!"`{name}` ensures: {m}"]
    | .ok r, .ok e =>
      let names := fparams.map fun (p, _) => sanitizeName p
      -- The final values of the `&mut` parameters and the result, read from
      -- the surface definition's value `out`: a write-back function returns
      -- its Rust result, when it carries one, and the parameters it writes, in
      -- that order (`ThreadMutations.tReturnMutParams`).
      let muts := fparams.filterMap fun (p, ty) =>
        match ty with
        | .ref _ true => some p
        | _ => none
      let (wb, hasRes) := (writeReturns.lookup name).getD ([], false)
      let comps := (if hasRes then ["_res"] else []) ++ wb
      let k := comps.length
      let comp (i : Nat) : String :=
        if k == 1 then "out"
        else if i + 1 < k then "out" ++ String.join (List.replicate i ".2") ++ ".1"
        else "out" ++ String.join (List.replicate i ".2")
      let futures := muts.map fun p => match comps.findIdx? (· == p) with
        | some i => comp i
        | none => sanitizeName p
      let result := if wb.isEmpty then "out" else if hasRes then comp 0 else "()"
      let reqOk : Except String Unit := match r with
        | some p =>
          if p.params.length == fparams.length then pure ()
          else throw s!"`{name}` requires: {p.params.length} parameters for {fparams.length} inputs"
        | none => pure ()
      let ensArgs : Except String (List String) := match e with
        | none => pure []
        | some p =>
          predArgs p names futures <|> predArgs p names (futures ++ [result])
            |>.mapError fun _ => s!"`{name}` ensures: {p.params.length} parameters for {fparams.length} inputs and {muts.length} `&mut` inputs"
      match reqOk, ensArgs with
      | .error m, _ | _, .error m => errs := errs ++ [m]
      | .ok (), .ok ensArgs =>
        fns := fns ++ [{ fn := name, params := fparams, requires := r, ensures := e, ensArgs }]
  -- Traits and their `impl`s, under `--emit-classes`.
  let traitNames := hooks.traits.map (·.name)
  let mut traitMs : List (String × List MethodContract) := []
  let mut implMs : List (Nat × String × List MethodContract) := []
  let mut seenT : List String := []
  let mut seenI : List Nat := []
  for j in srcs do
    for it in ClassEmit.allItems j do
      let some k := (it.getObjVal? "kind").toOption | continue
      if let .ok (.arr tr) := k.getObjVal? "Trait" then
        let tn := extractFnName (tr[3]?.getD .null)
        if !traitNames.contains tn || seenT.contains tn || !selected tn then continue
        seenT := tn :: seenT
        let tItems := match (tr[6]? : Option Json) with
          | some (.arr xs) => xs.toList
          | _ => []
        let (ms, es) := methodContracts preds implMap [] tn tItems
        errs := errs ++ es
        if !ms.isEmpty then traitMs := traitMs ++ [(tn, ms)]
      else if let .ok impl := k.getObjVal? "Impl" then
        let some tn := implTraitName impl | continue
        let some iid := ownerId it | continue
        if !traitNames.contains tn || seenI.contains iid || !selected tn then continue
        seenI := iid :: seenI
        let iItems := match impl.getObjValAs? (Array Json) "items" with
          | .ok xs => xs.toList
          | _ => []
        let (ms, es) := methodContracts preds implMap emitted s!"impl {tn}" iItems
        errs := errs ++ es
        if !ms.isEmpty then implMs := implMs ++ [(iid, tn, ms)]
  -- A trait carries contract fields when it or one of its `impl`s states a
  -- clause.
  let contractTraits := (traitMs.map (·.1) ++ implMs.map (·.2.1)).eraseDups
  let tds := hooks.traits.filter fun td => contractTraits.contains td.name
  let mut instances : List ImplInstance := []
  for inst in hooks.instances do
    match tds.find? (·.name == inst.trait) with
    | none => instances := instances ++ [inst]
    | some td =>
      let ms := ((implMs.find? (·.1 == inst.implId)).map (·.2.2)).getD []
      match instanceContractFields td ms with
      | .ok fs => instances := instances ++ [{ inst with contractFields := fs }]
      | .error e =>
        errs := errs ++ [s!"impl {inst.trait}: {e}"]
        instances := instances ++ [inst]
  let texts : (String → Option String) → Except String String := fun sl => do
    let parts ← tds.mapM fun td =>
      renderTraitContract sl td (((traitMs.find? (·.1 == td.name)).map (·.2)).getD [])
    pure ("\n".intercalate parts)
  -- The trait texts are checked once under the identity lookup; their errors
  -- come from the predicate shapes, which do not depend on the lookup.
  if let .error e := texts (fun _ => none) then errs := errs ++ [e]
  if !errs.isEmpty then throw errs
  let hooks := { hooks with
    instances
    contractMethods := tds.map fun td => (td.name, td.methods.map (·.1))
    contractText := fun sl => match texts sl with
      | .ok s => if s.isEmpty then "" else s ++ "\n"
      | .error _ => "" }
  pure ({ fns, lemmas }, hooks)

end Hax.ContractEmit

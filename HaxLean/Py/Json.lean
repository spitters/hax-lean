/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import Lean.Data.Json
public import HaxLean.Py.AST
public import HaxLean.JsonSize
import Std.Data.DTreeMap.Raw.Lemmas
import all Lean.Data.Json.Basic

/-!
# Reading the JSON dump of a Python parse tree

`PyModule.fromJson?` reads the JSON dump of a CPython 3.12 `ast.Module`
(top level `{"python": [3, 12, micro], "file": ..., "module": ...}`) into a
`PyModule`; `PyModule.toJson` writes a `PyModule` in the same schema. A node
is a JSON object with its CPython class name under `"_type"`, its `_fields`
by name and its span under `lineno`, `col_offset`, `end_lineno`,
`end_col_offset`; the reader looks fields up by name and does not depend on
key order.

The reader refuses, with the node concerned and its position where it has
one: an interpreter version other than 3.12, a node class outside the
subset of `HaxLean.Py.AST`, a constant other than `bool`, `int`, `str` and
`None`, a function with parameters other than positional ones, and a
function with type parameters.

`PyModule.fromJson_toJson` states that reading a written module returns it.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Py

open Lean (Json JsonNumber)

/-- A refusal of the reader: the `_type` or field concerned, the position of
the enclosing node where it has one, and a message. -/
structure PyReadError where
  node : String
  pos : Option Pos
  msg : String
  deriving Repr, Inhabited

/-- The reader monad. -/
abbrev ReadM := Except PyReadError

namespace Read

/-- The value of field `k` of node `j` (of class `ty`). -/
def field (ty : String) (j : Json) (k : String) : ReadM Json :=
  match j.getObjVal? k with
  | .ok v => .ok v
  | .error _ => .error ⟨ty, none, s!"missing field {k}"⟩

/-- A string. -/
def str (ty : String) (k : String) : Json → ReadM String
  | .str s => .ok s
  | _ => .error ⟨ty, none, s!"field {k}: string expected"⟩

/-- A natural number: a JSON integer with exponent 0 and a non-negative
mantissa. -/
def nat (ty : String) (k : String) : Json → ReadM Nat
  | .num ⟨.ofNat n, 0⟩ => .ok n
  | _ => .error ⟨ty, none, s!"field {k}: natural number expected"⟩

/-- An optional string: `null` or a string. -/
def optStr (ty : String) (k : String) : Json → ReadM (Option String)
  | .null => .ok none
  | .str s => .ok (some s)
  | _ => .error ⟨ty, none, s!"field {k}: string or null expected"⟩

/-- A list. -/
def list (ty : String) (k : String) : Json → ReadM (List Json)
  | .arr a => .ok a.toList
  | _ => .error ⟨ty, none, s!"field {k}: list expected"⟩

/-- The class name `_type` of a node. -/
def typeOf (j : Json) : ReadM String := do
  str "node" "_type" (← field "node" j "_type")

/-- The span of a node of class `ty`. -/
def readPos (ty : String) (j : Json) : ReadM Pos := do
  let l ← nat ty "lineno" (← field ty j "lineno")
  let c ← nat ty "col_offset" (← field ty j "col_offset")
  let el ← nat ty "end_lineno" (← field ty j "end_lineno")
  let ec ← nat ty "end_col_offset" (← field ty j "end_col_offset")
  return ⟨l, c, el, ec⟩

/-- A result paired, when successful, with a property that every successful
result has. -/
def attachOk {α : Type} {P : α → Prop} (r : ReadM α) (H : ∀ v, r = .ok v → P v) :
    ReadM {v : α // P v} :=
  match r, H with
  | .ok v, H => .ok ⟨v, H v rfl⟩
  | .error e, _ => .error e

theorem field_decreases {ty : String} {j : Json} {k : String} {v : Json}
    (h : field ty j k = .ok v) : sizeOf v < sizeOf j := by
  unfold field at h
  split at h
  · cases h
    exact JsonSize.getObjVal?_decreases (by assumption)
  · cases h

theorem list_field_decreases {ty : String} {j : Json} {k : String} {l : List Json}
    (h : (do list ty k (← field ty j k)) = .ok l) : sizeOf l < sizeOf j := by
  cases hf : field ty j k with
  | error e => rw [hf] at h; cases h
  | ok v =>
    rw [hf] at h
    have h1 := field_decreases hf
    cases v with
    | arr a =>
      cases h
      cases a
      simp only [Json.arr.sizeOf_spec, Array.mk.sizeOf_spec] at h1
      dsimp only
      omega
    | _ => cases h

/-- Field `k` of `j`, with the bound on its size used for recursion. -/
def child (ty : String) (j : Json) (k : String) : ReadM {v : Json // sizeOf v < sizeOf j} :=
  attachOk (field ty j k) fun _ h => field_decreases h

/-- The list in field `k` of `j`, with the bound on its size used for
recursion. -/
def children (ty : String) (j : Json) (k : String) :
    ReadM {l : List Json // sizeOf l < sizeOf j} :=
  attachOk (do list ty k (← field ty j k)) fun _ h => list_field_decreases h

/-- The reading of each element of a list. -/
def readList {α : Type} (f : Json → ReadM α) : List Json → ReadM (List α)
  | [] => .ok []
  | x :: xs => do return (← f x) :: (← readList f xs)

/-- The reading of `null` as `none` and of any other value by `f`. -/
def readOpt {α : Type} (f : Json → ReadM α) : Json → ReadM (Option α)
  | .null => .ok none
  | v => some <$> f v

/-- Field `k` of node `j` is `null` or an empty list. -/
def requireEmpty (ty : String) (j : Json) (k : String) : ReadM Unit := do
  match ← field ty j k with
  | .null => .ok ()
  | .arr a => if a.isEmpty then .ok () else .error ⟨ty, none, s!"field {k} must be empty"⟩
  | _ => .error ⟨ty, none, s!"field {k} must be empty"⟩

/-- A field-less node of class `ty` read by `f`; `what` names the expected kind. -/
def readTag {α : Type} (what : String) (f : String → Option α) (j : Json) : ReadM α := do
  let ty ← typeOf j
  match f ty with
  | some a => .ok a
  | none => .error ⟨ty, none, s!"{what} expected"⟩

end Read

/-! ## Operators -/

/-- The CPython class name of a binary operator. -/
def PyBinOp.toName : PyBinOp → String
  | .add => "Add" | .sub => "Sub" | .mult => "Mult" | .matMult => "MatMult"
  | .div => "Div" | .mod => "Mod" | .pow => "Pow" | .lShift => "LShift"
  | .rShift => "RShift" | .bitOr => "BitOr" | .bitXor => "BitXor"
  | .bitAnd => "BitAnd" | .floorDiv => "FloorDiv"

/-- The binary operator of a CPython class name. -/
def PyBinOp.ofName : String → Option PyBinOp
  | "Add" => some .add | "Sub" => some .sub | "Mult" => some .mult
  | "MatMult" => some .matMult | "Div" => some .div | "Mod" => some .mod
  | "Pow" => some .pow | "LShift" => some .lShift | "RShift" => some .rShift
  | "BitOr" => some .bitOr | "BitXor" => some .bitXor | "BitAnd" => some .bitAnd
  | "FloorDiv" => some .floorDiv
  | _ => none

/-- The CPython class name of a unary operator. -/
def PyUnaryOp.toName : PyUnaryOp → String
  | .invert => "Invert" | .not => "Not" | .uAdd => "UAdd" | .uSub => "USub"

/-- The unary operator of a CPython class name. -/
def PyUnaryOp.ofName : String → Option PyUnaryOp
  | "Invert" => some .invert | "Not" => some .not | "UAdd" => some .uAdd
  | "USub" => some .uSub
  | _ => none

/-- The CPython class name of a boolean operator. -/
def PyBoolOp.toName : PyBoolOp → String
  | .and => "And" | .or => "Or"

/-- The boolean operator of a CPython class name. -/
def PyBoolOp.ofName : String → Option PyBoolOp
  | "And" => some .and | "Or" => some .or
  | _ => none

/-- The CPython class name of a comparison operator. -/
def PyCmpOp.toName : PyCmpOp → String
  | .eq => "Eq" | .notEq => "NotEq" | .lt => "Lt" | .ltE => "LtE" | .gt => "Gt"
  | .gtE => "GtE" | .is => "Is" | .isNot => "IsNot" | .in_ => "In" | .notIn => "NotIn"

/-- The comparison operator of a CPython class name. -/
def PyCmpOp.ofName : String → Option PyCmpOp
  | "Eq" => some .eq | "NotEq" => some .notEq | "Lt" => some .lt | "LtE" => some .ltE
  | "Gt" => some .gt | "GtE" => some .gtE | "Is" => some .is | "IsNot" => some .isNot
  | "In" => some .in_ | "NotIn" => some .notIn
  | _ => none

theorem PyBinOp.ofName_toName (o : PyBinOp) : PyBinOp.ofName o.toName = some o := by
  cases o <;> rfl

theorem PyUnaryOp.ofName_toName (o : PyUnaryOp) : PyUnaryOp.ofName o.toName = some o := by
  cases o <;> rfl

theorem PyBoolOp.ofName_toName (o : PyBoolOp) : PyBoolOp.ofName o.toName = some o := by
  cases o <;> rfl

theorem PyCmpOp.ofName_toName (o : PyCmpOp) : PyCmpOp.ofName o.toName = some o := by
  cases o <;> rfl

/-! ## Writer -/

namespace Write

/-- A natural number as a JSON integer. -/
def nat (n : Nat) : Json := .num ⟨.ofNat n, 0⟩

/-- The span fields of a node. -/
def posFields (p : Pos) : List (String × Json) :=
  [("lineno", nat p.line), ("col_offset", nat p.col),
   ("end_lineno", nat p.endLine), ("end_col_offset", nat p.endCol)]

/-- A node of class `ty` with the given fields. -/
def node (ty : String) (fields : List (String × Json)) : Json :=
  Json.mkObj (("_type", .str ty) :: fields)

/-- A field-less node of class `ty`: an operator or a context. -/
def tag (ty : String) : Json := node ty []

/-- The context `Load`. -/
def load : Json := tag "Load"

/-- An optional value: `null` or the value written by `f`. -/
def opt {α : Type} (f : α → Json) : Option α → Json
  | none => .null
  | some a => f a

/-- An optional string. -/
def optStr : Option String → Json
  | none => .null
  | some s => .str s

/-- The value of a constant. -/
def const : PyConst → Json
  | .bool b => .bool b
  | .int n => .num ⟨n, 0⟩
  | .str s => .str s
  | .none => .null

end Write

/-! ## Expressions -/

open Read in
mutual

/-- The reader of an expression node. -/
def readExpr (j : Json) : ReadM PyExpr := do
  let ty ← typeOf j
  let p ← readPos ty j
  match ty with
  | "Name" => return .name p (← str ty "id" (← field ty j "id"))
  | "Constant" =>
    match ← field ty j "value" with
    | .bool b => return .const p (.bool b)
    | .num ⟨n, 0⟩ => return .const p (.int n)
    | .str s => return .const p (.str s)
    | .null => return .const p .none
    | _ => throw ⟨ty, some p, "unsupported constant"⟩
  | "BinOp" => do
    let ⟨l, _⟩ ← child ty j "left"
    let op ← readTag "binary operator" PyBinOp.ofName (← field ty j "op")
    let ⟨r, _⟩ ← child ty j "right"
    return .binOp p (← readExpr l) op (← readExpr r)
  | "UnaryOp" => do
    let op ← readTag "unary operator" PyUnaryOp.ofName (← field ty j "op")
    let ⟨e, _⟩ ← child ty j "operand"
    return .unaryOp p op (← readExpr e)
  | "BoolOp" => do
    let op ← readTag "boolean operator" PyBoolOp.ofName (← field ty j "op")
    let ⟨vs, _⟩ ← children ty j "values"
    return .boolOp p op (← readExprs vs)
  | "Compare" => do
    let ⟨l, _⟩ ← child ty j "left"
    let ops ← readList (readTag "comparison operator" PyCmpOp.ofName)
      (← list ty "ops" (← field ty j "ops"))
    let ⟨cs, _⟩ ← children ty j "comparators"
    return .compare p (← readExpr l) ops (← readExprs cs)
  | "IfExp" => do
    let ⟨c, _⟩ ← child ty j "test"
    let ⟨t, _⟩ ← child ty j "body"
    let ⟨e, _⟩ ← child ty j "orelse"
    return .ifExp p (← readExpr c) (← readExpr t) (← readExpr e)
  | "Call" => do
    let ⟨f, _⟩ ← child ty j "func"
    let ⟨as, _⟩ ← children ty j "args"
    let ⟨ks, _⟩ ← children ty j "keywords"
    return .call p (← readExpr f) (← readExprs as) (← readKws ks)
  | "Attribute" => do
    let ⟨v, _⟩ ← child ty j "value"
    let a ← str ty "attr" (← field ty j "attr")
    return .attribute p (← readExpr v) a
  | "Subscript" => do
    let ⟨v, _⟩ ← child ty j "value"
    let ⟨s, _⟩ ← child ty j "slice"
    return .subscript p (← readExpr v) (← readExpr s)
  | "Tuple" => do
    let ⟨es, _⟩ ← children ty j "elts"
    return .tuple p (← readExprs es)
  | _ => throw ⟨ty, some p, "expression outside the subset"⟩
termination_by sizeOf j

/-- The reader of a list of expression nodes. -/
def readExprs : List Json → ReadM (List PyExpr)
  | [] => .ok []
  | x :: xs => do return (← readExpr x) :: (← readExprs xs)
termination_by l => sizeOf l

/-- The reader of a `keyword` node. -/
def readKw (j : Json) : ReadM PyKeyword := do
  let ty ← typeOf j
  if ty ≠ "keyword" then throw ⟨ty, none, "keyword expected"⟩
  let p ← readPos ty j
  let a ← optStr ty "arg" (← field ty j "arg")
  let ⟨v, _⟩ ← child ty j "value"
  return .mk p a (← readExpr v)
termination_by sizeOf j

/-- The reader of a list of `keyword` nodes. -/
def readKws : List Json → ReadM (List PyKeyword)
  | [] => .ok []
  | x :: xs => do return (← readKw x) :: (← readKws xs)
termination_by l => sizeOf l

end

open Write in
mutual

/-- The writer of an expression node. -/
def PyExpr.toJson : PyExpr → Json
  | .name p id => node "Name" ([("id", .str id), ("ctx", load)] ++ posFields p)
  | .const p c => node "Constant" ([("value", const c), ("kind", .null)] ++ posFields p)
  | .binOp p l op r => node "BinOp"
      ([("left", l.toJson), ("op", tag op.toName), ("right", r.toJson)] ++ posFields p)
  | .unaryOp p op e => node "UnaryOp"
      ([("op", tag op.toName), ("operand", e.toJson)] ++ posFields p)
  | .boolOp p op vs => node "BoolOp"
      ([("op", tag op.toName), ("values", .arr (PyExpr.listToJson vs).toArray)] ++
        posFields p)
  | .compare p l ops cs => node "Compare"
      ([("left", l.toJson), ("ops", .arr (ops.map fun o => tag o.toName).toArray),
        ("comparators", .arr (PyExpr.listToJson cs).toArray)] ++ posFields p)
  | .ifExp p c t e => node "IfExp"
      ([("test", c.toJson), ("body", t.toJson), ("orelse", e.toJson)] ++ posFields p)
  | .call p f as ks => node "Call"
      ([("func", f.toJson), ("args", .arr (PyExpr.listToJson as).toArray),
        ("keywords", .arr (PyKeyword.listToJson ks).toArray)] ++ posFields p)
  | .attribute p v a => node "Attribute"
      ([("value", v.toJson), ("attr", .str a), ("ctx", load)] ++ posFields p)
  | .subscript p v s => node "Subscript"
      ([("value", v.toJson), ("slice", s.toJson), ("ctx", load)] ++ posFields p)
  | .tuple p es => node "Tuple"
      ([("elts", .arr (PyExpr.listToJson es).toArray), ("ctx", load)] ++ posFields p)

/-- The writer of a list of expression nodes. -/
def PyExpr.listToJson : List PyExpr → List Json
  | [] => []
  | e :: es => e.toJson :: PyExpr.listToJson es

/-- The writer of a `keyword` node. -/
def PyKeyword.toJson : PyKeyword → Json
  | .mk p a v => node "keyword" ([("arg", optStr a), ("value", v.toJson)] ++ posFields p)

/-- The writer of a list of `keyword` nodes. -/
def PyKeyword.listToJson : List PyKeyword → List Json
  | [] => []
  | k :: ks => k.toJson :: PyKeyword.listToJson ks

end

/-! ## Round trip -/

theorem getObjVal?_mkObj {kvs : List (String × Json)} (k : String)
    (hd : kvs.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq)) :
    (Json.mkObj kvs).getObjVal? k = match kvs.lookup k with
      | some v => .ok v
      | none => .error s!"property not found: {k}" := by
  cases hl : kvs.lookup k with
  | some v =>
    have hm : (k, v) ∈ kvs := by
      obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp hl
      simp
    have h : (Std.TreeMap.Raw.ofList kvs compare).get? k = some v :=
      Std.DTreeMap.Raw.Const.get?_ofList_of_mem (k := k) (by simp) hd hm
    simp only [Json.mkObj, Json.getObjVal?, h]
    rfl
  | none =>
    have hc : (kvs.map Prod.fst).contains k = false := by
      simp only [List.lookup_eq_none_iff, bne_iff_ne, ne_eq] at hl
      simp only [List.contains_eq_mem, List.mem_map, decide_eq_false_iff_not, not_exists,
        not_and]
      intro x hx hk
      exact hl x hx hk.symm
    have h : (Std.TreeMap.Raw.ofList kvs compare).get? k = none :=
      Std.DTreeMap.Raw.Const.get?_ofList_of_contains_eq_false hc
    simp only [Json.mkObj, Json.getObjVal?, h]
    rfl

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

theorem map_ok {ε α β : Type} (a : α) (f : α → β) :
    (f <$> (Except.ok a : Except ε α)) = .ok (f a) := rfl

theorem pure_eq_ok {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

theorem nat_write (ty k : String) (n : Nat) : Read.nat ty k (Write.nat n) = .ok n := rfl

theorem attachOk_ok {α : Type} {P : α → Prop} (a : α) (H : ∀ v, Except.ok a = .ok v → P v) :
    Read.attachOk (.ok a) H = .ok ⟨a, H a rfl⟩ := rfl

/-- The CPython class name of an expression. -/
def PyExpr.typeName : PyExpr → String
  | .name .. => "Name" | .const .. => "Constant" | .binOp .. => "BinOp"
  | .unaryOp .. => "UnaryOp" | .boolOp .. => "BoolOp" | .compare .. => "Compare"
  | .ifExp .. => "IfExp" | .call .. => "Call" | .attribute .. => "Attribute"
  | .subscript .. => "Subscript" | .tuple .. => "Tuple"

theorem typeOf_exprToJson (e : PyExpr) : Read.typeOf e.toJson = .ok e.typeName := by
  cases e <;> simp (disch := simp) [PyExpr.toJson, Write.node, Write.posFields,
    Read.typeOf, Read.field, Read.str, getObjVal?_mkObj, List.lookup, ok_bind, PyExpr.typeName]

theorem readPos_exprToJson (ty : String) (e : PyExpr) : Read.readPos ty e.toJson = .ok e.pos := by
  cases e <;> simp (disch := simp) [PyExpr.toJson, Write.node, Write.posFields,
    Read.readPos, Read.field, nat_write, getObjVal?_mkObj, List.lookup, ok_bind, map_ok,
    PyExpr.pos]

theorem readList_map {α : Type} (f : Json → ReadM α) (g : α → Json)
    (h : ∀ a, f (g a) = .ok a) (l : List α) : Read.readList f (l.map g) = .ok l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [Read.readList, h, ih, ok_bind, map_ok]

theorem readTag_node {α : Type} (w : String) (f : String → Option α) (s : String) (a : α)
    (h : f s = some a) : Read.readTag w f (Write.tag s) = .ok a := by
  simp (disch := simp) [Read.readTag, Read.typeOf, Read.field, Read.str, Write.tag, Write.node,
    getObjVal?_mkObj, List.lookup, ok_bind, h]

theorem readTag_binOp (w : String) (o : PyBinOp) :
    Read.readTag w PyBinOp.ofName (Write.tag o.toName) = .ok o :=
  readTag_node _ _ _ _ (PyBinOp.ofName_toName o)

theorem readTag_unaryOp (w : String) (o : PyUnaryOp) :
    Read.readTag w PyUnaryOp.ofName (Write.tag o.toName) = .ok o :=
  readTag_node _ _ _ _ (PyUnaryOp.ofName_toName o)

theorem readTag_boolOp (w : String) (o : PyBoolOp) :
    Read.readTag w PyBoolOp.ofName (Write.tag o.toName) = .ok o :=
  readTag_node _ _ _ _ (PyBoolOp.ofName_toName o)

theorem readTag_cmpOp (w : String) (o : PyCmpOp) :
    Read.readTag w PyCmpOp.ofName (Write.tag o.toName) = .ok o :=
  readTag_node _ _ _ _ (PyCmpOp.ofName_toName o)

theorem optStr_write (ty k : String) (a : Option String) :
    Read.optStr ty k (Write.optStr a) = .ok a := by
  cases a <;> rfl

/-- The rewriting set of the round-trip proofs: field lookups in written
nodes. -/
macro "py_rt" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (disch := simp) [Write.node, Write.posFields, Read.field, Read.str,
      Read.child, Read.children, Read.list, getObjVal?_mkObj, List.lookup, ok_bind, map_ok,
      attachOk_ok, readTag_binOp, readTag_unaryOp, readTag_boolOp, readTag_cmpOp,
      optStr_write, pure_eq_ok, $ts,*])

mutual

theorem readExpr_toJson : ∀ e : PyExpr, readExpr e.toJson = .ok e
  | .name p id => by
    rw [readExpr]
    simp only [typeOf_exprToJson, readPos_exprToJson, ok_bind, PyExpr.typeName, PyExpr.pos]
    py_rt [PyExpr.toJson]
  | .const p c => by
    rw [readExpr]
    simp only [typeOf_exprToJson, readPos_exprToJson, ok_bind, PyExpr.typeName, PyExpr.pos]
    cases c <;> py_rt [PyExpr.toJson, Write.const]
  | .binOp p l op r => by
    rw [readExpr]
    simp only [typeOf_exprToJson, readPos_exprToJson, ok_bind, PyExpr.typeName, PyExpr.pos]
    py_rt [PyExpr.toJson, readExpr_toJson l, readExpr_toJson r]
  | .unaryOp p op e => by
    rw [readExpr]
    simp only [typeOf_exprToJson, readPos_exprToJson, ok_bind, PyExpr.typeName, PyExpr.pos]
    py_rt [PyExpr.toJson, readExpr_toJson e]
  | .boolOp p op vs => by
    rw [readExpr]
    simp only [typeOf_exprToJson, readPos_exprToJson, ok_bind, PyExpr.typeName, PyExpr.pos]
    py_rt [PyExpr.toJson, readExprs_toJson vs]
  | .compare p l ops cs => by
    rw [readExpr]
    simp only [typeOf_exprToJson, readPos_exprToJson, ok_bind, PyExpr.typeName, PyExpr.pos]
    py_rt [PyExpr.toJson, readExpr_toJson l, readExprs_toJson cs,
      readList_map _ _ (readTag_cmpOp "comparison operator") ops]
  | .ifExp p c t e => by
    rw [readExpr]
    simp only [typeOf_exprToJson, readPos_exprToJson, ok_bind, PyExpr.typeName, PyExpr.pos]
    py_rt [PyExpr.toJson, readExpr_toJson c, readExpr_toJson t, readExpr_toJson e]
  | .call p f as ks => by
    rw [readExpr]
    simp only [typeOf_exprToJson, readPos_exprToJson, ok_bind, PyExpr.typeName, PyExpr.pos]
    py_rt [PyExpr.toJson, readExpr_toJson f, readExprs_toJson as, readKws_toJson ks]
  | .attribute p v a => by
    rw [readExpr]
    simp only [typeOf_exprToJson, readPos_exprToJson, ok_bind, PyExpr.typeName, PyExpr.pos]
    py_rt [PyExpr.toJson, readExpr_toJson v]
  | .subscript p v s => by
    rw [readExpr]
    simp only [typeOf_exprToJson, readPos_exprToJson, ok_bind, PyExpr.typeName, PyExpr.pos]
    py_rt [PyExpr.toJson, readExpr_toJson v, readExpr_toJson s]
  | .tuple p es => by
    rw [readExpr]
    simp only [typeOf_exprToJson, readPos_exprToJson, ok_bind, PyExpr.typeName, PyExpr.pos]
    py_rt [PyExpr.toJson, readExprs_toJson es]

theorem readExprs_toJson : ∀ es : List PyExpr, readExprs (PyExpr.listToJson es) = .ok es
  | [] => by simp only [PyExpr.listToJson]; rw [readExprs]
  | e :: es => by
    simp only [PyExpr.listToJson]
    rw [readExprs]
    simp [readExpr_toJson e, readExprs_toJson es, ok_bind, map_ok]

theorem readKw_toJson : ∀ k : PyKeyword, readKw k.toJson = .ok k
  | .mk p a v => by
    rw [readKw]
    py_rt [PyKeyword.toJson, Read.typeOf, Read.readPos, nat_write, readExpr_toJson v]

theorem readKws_toJson : ∀ ks : List PyKeyword, readKws (PyKeyword.listToJson ks) = .ok ks
  | [] => by simp only [PyKeyword.listToJson]; rw [readKws]
  | k :: ks => by
    simp only [PyKeyword.listToJson]
    rw [readKws]
    simp [readKw_toJson k, readKws_toJson ks, ok_bind, map_ok]

end

theorem readOpt_exprToJson (o : Option PyExpr) :
    Read.readOpt readExpr (Write.opt PyExpr.toJson o) = .ok o := by
  rcases o with _ | e
  · rfl
  · have h : ∃ kvs, e.toJson = .obj kvs := by
      cases e <;> exact ⟨_, rfl⟩
    obtain ⟨kvs, hk⟩ := h
    simp only [Write.opt, Read.readOpt, hk]
    simp [← hk, readExpr_toJson, map_ok]

/-! ## Statements and modules -/

open Read in
/-- The reader of an `arg` node. -/
def readArg (j : Json) : ReadM PyArg := do
  let ty ← typeOf j
  if ty ≠ "arg" then throw ⟨ty, none, "parameter expected"⟩
  let p ← readPos ty j
  let n ← str ty "arg" (← field ty j "arg")
  let a ← readOpt readExpr (← field ty j "annotation")
  return ⟨p, n, a⟩

open Read in
/-- The reader of an `arguments` node: positional parameters only. -/
def readArguments (j : Json) : ReadM (List PyArg) := do
  let ty ← typeOf j
  if ty ≠ "arguments" then throw ⟨ty, none, "parameters expected"⟩
  requireEmpty ty j "posonlyargs"
  requireEmpty ty j "vararg"
  requireEmpty ty j "kwonlyargs"
  requireEmpty ty j "kw_defaults"
  requireEmpty ty j "kwarg"
  requireEmpty ty j "defaults"
  readList readArg (← list ty "args" (← field ty j "args"))

open Read in
/-- The reader of an `alias` node. -/
def readAlias (j : Json) : ReadM PyAlias := do
  let ty ← typeOf j
  if ty ≠ "alias" then throw ⟨ty, none, "imported name expected"⟩
  let p ← readPos ty j
  let n ← str ty "name" (← field ty j "name")
  let a ← optStr ty "asname" (← field ty j "asname")
  return ⟨p, n, a⟩

open Read in
/-- The field `type_params` of node `j` is absent, `null` or empty. -/
def noTypeParams (ty : String) (j : Json) : ReadM Unit :=
  match j.getObjVal? "type_params" with
  | .error _ => .ok ()
  | .ok _ => requireEmpty ty j "type_params"

/-- The `simple` flag of an `AnnAssign`: the integer 1 or 0. -/
def readSimple (ty : String) : Json → ReadM Bool
  | .num ⟨.ofNat 1, 0⟩ => .ok true
  | .num ⟨.ofNat 0, 0⟩ => .ok false
  | _ => .error ⟨ty, none, "field simple: 0 or 1 expected"⟩

open Read in
mutual

/-- The reader of a statement node. -/
def readStmt (j : Json) : ReadM PyStmt := do
  let ty ← typeOf j
  let p ← readPos ty j
  match ty with
  | "FunctionDef" => do
    let n ← str ty "name" (← field ty j "name")
    let ps ← readArguments (← field ty j "args")
    let ⟨b, _⟩ ← children ty j "body"
    let ds ← readExprs (← list ty "decorator_list" (← field ty j "decorator_list"))
    let r ← readOpt readExpr (← field ty j "returns")
    noTypeParams ty j
    return .functionDef p n ps (← readStmts b) ds r
  | "Assign" => do
    let ts ← readExprs (← list ty "targets" (← field ty j "targets"))
    let v ← readExpr (← field ty j "value")
    return .assign p ts v
  | "AnnAssign" => do
    let t ← readExpr (← field ty j "target")
    let a ← readExpr (← field ty j "annotation")
    let v ← readOpt readExpr (← field ty j "value")
    let s ← readSimple ty (← field ty j "simple")
    return .annAssign p t a v s
  | "For" => do
    let t ← readExpr (← field ty j "target")
    let i ← readExpr (← field ty j "iter")
    let ⟨b, _⟩ ← children ty j "body"
    let ⟨o, _⟩ ← children ty j "orelse"
    return .forStmt p t i (← readStmts b) (← readStmts o)
  | "If" => do
    let c ← readExpr (← field ty j "test")
    let ⟨b, _⟩ ← children ty j "body"
    let ⟨o, _⟩ ← children ty j "orelse"
    return .ifStmt p c (← readStmts b) (← readStmts o)
  | "Return" => return .ret p (← readOpt readExpr (← field ty j "value"))
  | "Expr" => return .expr p (← readExpr (← field ty j "value"))
  | "ImportFrom" => do
    let m ← optStr ty "module" (← field ty j "module")
    let ns ← readList readAlias (← list ty "names" (← field ty j "names"))
    let l ← nat ty "level" (← field ty j "level")
    return .importFrom p m ns l
  | "Pass" => return .pass p
  | _ => throw ⟨ty, some p, "statement outside the subset"⟩
termination_by sizeOf j

/-- The reader of a list of statement nodes. -/
def readStmts : List Json → ReadM (List PyStmt)
  | [] => .ok []
  | x :: xs => do return (← readStmt x) :: (← readStmts xs)
termination_by l => sizeOf l

end

/-- The reader of the JSON dump of a Python 3.12 module. -/
def PyModule.fromJson? (j : Json) : ReadM PyModule := do
  let ver ← Read.list "python" "python" (← Read.field "python" j "python")
  let micro ← match ver with
    | [ma, mi, mc] => do
      let ma ← Read.nat "python" "python" ma
      let mi ← Read.nat "python" "python" mi
      let mc ← Read.nat "python" "python" mc
      if ma = 3 ∧ mi = 12 then pure mc
      else throw ⟨"python", none, s!"Python 3.12 expected, found {ma}.{mi}"⟩
    | _ => throw ⟨"python", none, "version triple expected"⟩
  let file ← Read.str "file" "file" (← Read.field "file" j "file")
  let m ← Read.field "module" j "module"
  let ty ← Read.typeOf m
  if ty ≠ "Module" then throw ⟨ty, none, "module expected"⟩
  let body ← readStmts (← Read.list ty "body" (← Read.field ty m "body"))
  return ⟨micro, file, body⟩

open Write in
/-- The writer of an `arg` node. -/
def PyArg.toJson (a : PyArg) : Json :=
  node "arg" ([("arg", .str a.name), ("annotation", opt PyExpr.toJson a.annotation),
    ("type_comment", .null)] ++ posFields a.pos)

open Write in
/-- The writer of the `arguments` node of positional parameters `ps`. -/
def PyArg.listToArguments (ps : List PyArg) : Json :=
  node "arguments" [("posonlyargs", .arr #[]), ("args", .arr (ps.map PyArg.toJson).toArray),
    ("vararg", .null), ("kwonlyargs", .arr #[]), ("kw_defaults", .arr #[]), ("kwarg", .null),
    ("defaults", .arr #[])]

open Write in
/-- The writer of an `alias` node. -/
def PyAlias.toJson (a : PyAlias) : Json :=
  node "alias" ([("name", .str a.name), ("asname", optStr a.asname)] ++ posFields a.pos)

/-- The `simple` flag of an `AnnAssign` as the integer 1 or 0. -/
def Write.simple (b : Bool) : Json := Write.nat (if b then 1 else 0)

open Write in
mutual

/-- The writer of a statement node. -/
def PyStmt.toJson : PyStmt → Json
  | .functionDef p n ps b ds r => node "FunctionDef"
      ([("name", .str n), ("args", PyArg.listToArguments ps),
        ("body", .arr (PyStmt.listToJson b).toArray),
        ("decorator_list", .arr (PyExpr.listToJson ds).toArray),
        ("returns", opt PyExpr.toJson r), ("type_comment", .null),
        ("type_params", .arr #[])] ++ posFields p)
  | .assign p ts v => node "Assign"
      ([("targets", .arr (PyExpr.listToJson ts).toArray), ("value", v.toJson),
        ("type_comment", .null)] ++ posFields p)
  | .annAssign p t a v s => node "AnnAssign"
      ([("target", t.toJson), ("annotation", a.toJson), ("value", opt PyExpr.toJson v),
        ("simple", simple s)] ++ posFields p)
  | .forStmt p t i b o => node "For"
      ([("target", t.toJson), ("iter", i.toJson), ("body", .arr (PyStmt.listToJson b).toArray),
        ("orelse", .arr (PyStmt.listToJson o).toArray), ("type_comment", .null)] ++ posFields p)
  | .ifStmt p c b o => node "If"
      ([("test", c.toJson), ("body", .arr (PyStmt.listToJson b).toArray),
        ("orelse", .arr (PyStmt.listToJson o).toArray)] ++ posFields p)
  | .ret p v => node "Return" ([("value", opt PyExpr.toJson v)] ++ posFields p)
  | .expr p v => node "Expr" ([("value", v.toJson)] ++ posFields p)
  | .importFrom p m ns l => node "ImportFrom"
      ([("module", optStr m), ("names", .arr (ns.map PyAlias.toJson).toArray),
        ("level", nat l)] ++ posFields p)
  | .pass p => node "Pass" (posFields p)

/-- The writer of a list of statement nodes. -/
def PyStmt.listToJson : List PyStmt → List Json
  | [] => []
  | s :: ss => s.toJson :: PyStmt.listToJson ss

end

/-- The writer of a module in the schema `PyModule.fromJson?` reads. -/
def PyModule.toJson (m : PyModule) : Json :=
  Json.mkObj [("python", .arr #[Write.nat 3, Write.nat 12, Write.nat m.micro]),
    ("file", .str m.file),
    ("module", Write.node "Module"
      [("body", .arr (PyStmt.listToJson m.body).toArray), ("type_ignores", .arr #[])])]

/-- The CPython class name of a statement. -/
def PyStmt.typeName : PyStmt → String
  | .functionDef .. => "FunctionDef" | .assign .. => "Assign" | .annAssign .. => "AnnAssign"
  | .forStmt .. => "For" | .ifStmt .. => "If" | .ret .. => "Return" | .expr .. => "Expr"
  | .importFrom .. => "ImportFrom" | .pass .. => "Pass"

theorem typeOf_stmtToJson (s : PyStmt) : Read.typeOf s.toJson = .ok s.typeName := by
  cases s <;> simp (disch := simp) [PyStmt.toJson, Write.node, Write.posFields,
    Read.typeOf, Read.field, Read.str, getObjVal?_mkObj, List.lookup, ok_bind, PyStmt.typeName]

theorem readPos_stmtToJson (ty : String) (s : PyStmt) : Read.readPos ty s.toJson = .ok s.pos := by
  cases s <;> simp (disch := simp) [PyStmt.toJson, Write.node, Write.posFields,
    Read.readPos, Read.field, nat_write, getObjVal?_mkObj, List.lookup, ok_bind, map_ok,
    PyStmt.pos]

theorem readArg_toJson (a : PyArg) : readArg a.toJson = .ok a := by
  rw [readArg]
  py_rt [PyArg.toJson, Read.typeOf, Read.readPos, nat_write, readOpt_exprToJson]

theorem readArguments_toJson (ps : List PyArg) :
    readArguments (PyArg.listToArguments ps) = .ok ps := by
  rw [readArguments]
  py_rt [PyArg.listToArguments, Read.typeOf, Read.requireEmpty,
    readList_map _ _ readArg_toJson ps]

theorem readAlias_toJson (a : PyAlias) : readAlias a.toJson = .ok a := by
  rw [readAlias]
  py_rt [PyAlias.toJson, Read.typeOf, Read.readPos, nat_write]

theorem simple_write (ty : String) (b : Bool) : readSimple ty (Write.simple b) = .ok b := by
  cases b <;> rfl

mutual

theorem readStmt_toJson : ∀ s : PyStmt, readStmt s.toJson = .ok s
  | .functionDef p n ps b ds r => by
    rw [readStmt]
    simp only [typeOf_stmtToJson, readPos_stmtToJson, ok_bind, PyStmt.typeName, PyStmt.pos]
    py_rt [PyStmt.toJson, noTypeParams, Read.requireEmpty, readArguments_toJson,
      readExprs_toJson, readOpt_exprToJson, readStmts_toJson b]
  | .assign p ts v => by
    rw [readStmt]
    simp only [typeOf_stmtToJson, readPos_stmtToJson, ok_bind, PyStmt.typeName, PyStmt.pos]
    py_rt [PyStmt.toJson, readExprs_toJson, readExpr_toJson]
  | .annAssign p t a v s => by
    rw [readStmt]
    simp only [typeOf_stmtToJson, readPos_stmtToJson, ok_bind, PyStmt.typeName, PyStmt.pos]
    py_rt [PyStmt.toJson, readExpr_toJson, readOpt_exprToJson, simple_write]
  | .forStmt p t i b o => by
    rw [readStmt]
    simp only [typeOf_stmtToJson, readPos_stmtToJson, ok_bind, PyStmt.typeName, PyStmt.pos]
    py_rt [PyStmt.toJson, readExpr_toJson, readStmts_toJson b, readStmts_toJson o]
  | .ifStmt p c b o => by
    rw [readStmt]
    simp only [typeOf_stmtToJson, readPos_stmtToJson, ok_bind, PyStmt.typeName, PyStmt.pos]
    py_rt [PyStmt.toJson, readExpr_toJson, readStmts_toJson b, readStmts_toJson o]
  | .ret p v => by
    rw [readStmt]
    simp only [typeOf_stmtToJson, readPos_stmtToJson, ok_bind, PyStmt.typeName, PyStmt.pos]
    py_rt [PyStmt.toJson, readOpt_exprToJson]
  | .expr p v => by
    rw [readStmt]
    simp only [typeOf_stmtToJson, readPos_stmtToJson, ok_bind, PyStmt.typeName, PyStmt.pos]
    py_rt [PyStmt.toJson, readExpr_toJson]
  | .importFrom p m ns l => by
    rw [readStmt]
    simp only [typeOf_stmtToJson, readPos_stmtToJson, ok_bind, PyStmt.typeName, PyStmt.pos]
    py_rt [PyStmt.toJson, nat_write, readList_map _ _ readAlias_toJson ns]
  | .pass p => by
    rw [readStmt]
    simp only [typeOf_stmtToJson, readPos_stmtToJson, ok_bind, PyStmt.typeName, PyStmt.pos]
    rfl

theorem readStmts_toJson : ∀ ss : List PyStmt, readStmts (PyStmt.listToJson ss) = .ok ss
  | [] => by simp only [PyStmt.listToJson]; rw [readStmts]
  | s :: ss => by
    simp only [PyStmt.listToJson]
    rw [readStmts]
    simp [readStmt_toJson s, readStmts_toJson ss, ok_bind, map_ok]

end

/-- Reading a written module returns it. -/
theorem PyModule.fromJson_toJson : ∀ m : PyModule, PyModule.fromJson? (PyModule.toJson m) = .ok m
  | ⟨micro, file, body⟩ => by
    rw [PyModule.fromJson?]
    py_rt [PyModule.toJson, Read.typeOf, nat_write, readStmts_toJson]

end Hax.Py

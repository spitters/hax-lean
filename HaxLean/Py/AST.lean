/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import Lean.Data.Json

/-!
# Python parse-tree subset

The nodes of the CPython 3.12 `ast` module that the Python front reads, as a
Lean syntax tree. Every node of a statement or an expression carries its
source span `Pos` (`lineno`, `col_offset`, `end_lineno`, `end_col_offset`).

Every Python binary, unary, boolean and comparison operator is a constructor;
the restriction to the front's subset is the type checker's job, which refuses
an operator outside the subset at its position. The fields `ctx`,
`type_comment`, `type_ignores` and the `kind` of a constant are not
represented. A function's parameters are positional (`arguments.args`).

`PyExpr` is nested through `List PyExpr` and mutual with `PyKeyword`;
`PyStmt` is nested through `List PyStmt`. `PyExpr.ind` and `PyStmt.ind` are
their induction principles with hypotheses for list elements.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Py

/-- A source span: `lineno`, `col_offset`, `end_lineno`, `end_col_offset`. -/
structure Pos where
  line : Nat
  col : Nat
  endLine : Nat
  endCol : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A constant of the subset: `bool`, `int`, `str` or `None`. -/
inductive PyConst where
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | none
  deriving Repr, DecidableEq, Inhabited

/-- The binary operators of `ast.operator`. -/
inductive PyBinOp where
  | add | sub | mult | matMult | div | mod | pow
  | lShift | rShift | bitOr | bitXor | bitAnd | floorDiv
  deriving Repr, DecidableEq, Inhabited

/-- The unary operators of `ast.unaryop`. -/
inductive PyUnaryOp where
  | invert | not | uAdd | uSub
  deriving Repr, DecidableEq, Inhabited

/-- The boolean operators of `ast.boolop`. -/
inductive PyBoolOp where
  | and | or
  deriving Repr, DecidableEq, Inhabited

/-- The comparison operators of `ast.cmpop`. -/
inductive PyCmpOp where
  | eq | notEq | lt | ltE | gt | gtE | is | isNot | in_ | notIn
  deriving Repr, DecidableEq, Inhabited

mutual

/-- The expressions of the subset (`ast.expr`). -/
inductive PyExpr where
  /-- `Name(id)`. -/
  | name (pos : Pos) (id : String)
  /-- `Constant(value)`. -/
  | const (pos : Pos) (c : PyConst)
  /-- `BinOp(left, op, right)`. -/
  | binOp (pos : Pos) (left : PyExpr) (op : PyBinOp) (right : PyExpr)
  /-- `UnaryOp(op, operand)`. -/
  | unaryOp (pos : Pos) (op : PyUnaryOp) (operand : PyExpr)
  /-- `BoolOp(op, values)`. -/
  | boolOp (pos : Pos) (op : PyBoolOp) (values : List PyExpr)
  /-- `Compare(left, ops, comparators)`. -/
  | compare (pos : Pos) (left : PyExpr) (ops : List PyCmpOp) (comparators : List PyExpr)
  /-- `IfExp(test, body, orelse)`: `body if test else orelse`. -/
  | ifExp (pos : Pos) (test body orelse : PyExpr)
  /-- `Call(func, args, keywords)`. -/
  | call (pos : Pos) (func : PyExpr) (args : List PyExpr) (keywords : List PyKeyword)
  /-- `Attribute(value, attr)`. -/
  | attribute (pos : Pos) (value : PyExpr) (attr : String)
  /-- `Subscript(value, slice)`. -/
  | subscript (pos : Pos) (value : PyExpr) (slice : PyExpr)
  /-- `Tuple(elts)`. -/
  | tuple (pos : Pos) (elts : List PyExpr)

/-- A keyword argument `keyword(arg, value)`; `arg = none` is `**value`. -/
inductive PyKeyword where
  | mk (pos : Pos) (arg : Option String) (value : PyExpr)

end

deriving instance Repr for PyExpr, PyKeyword
deriving instance Inhabited for PyExpr

/-- The source span of an expression. -/
def PyExpr.pos : PyExpr → Pos
  | .name p _ | .const p _ | .binOp p _ _ _ | .unaryOp p _ _ | .boolOp p _ _
  | .compare p _ _ _ | .ifExp p _ _ _ | .call p _ _ _ | .attribute p _ _
  | .subscript p _ _ | .tuple p _ => p

/-- The value of a keyword argument. -/
def PyKeyword.value : PyKeyword → PyExpr
  | .mk _ _ v => v

/-- Induction principle for `PyExpr` with hypotheses for the elements of its
lists and the values of its keyword arguments. -/
@[elab_as_elim]
theorem PyExpr.ind {motive : PyExpr → Prop}
    (name : ∀ p id, motive (.name p id))
    (const : ∀ p c, motive (.const p c))
    (binOp : ∀ p l op r, motive l → motive r → motive (.binOp p l op r))
    (unaryOp : ∀ p op e, motive e → motive (.unaryOp p op e))
    (boolOp : ∀ p op vs, (∀ v, v ∈ vs → motive v) → motive (.boolOp p op vs))
    (compare : ∀ p l ops cs, motive l → (∀ c, c ∈ cs → motive c) →
        motive (.compare p l ops cs))
    (ifExp : ∀ p c t e, motive c → motive t → motive e → motive (.ifExp p c t e))
    (call : ∀ p f args kws, motive f → (∀ a, a ∈ args → motive a) →
        (∀ k, k ∈ kws → motive k.value) → motive (.call p f args kws))
    (attr : ∀ p e a, motive e → motive (.attribute p e a))
    (subscript : ∀ p e s, motive e → motive s → motive (.subscript p e s))
    (tuple : ∀ p es, (∀ e, e ∈ es → motive e) → motive (.tuple p es))
    (e : PyExpr) : motive e :=
  go e
where
  go : (e : PyExpr) → motive e
    | .name p id => name p id
    | .const p c => const p c
    | .binOp p l op r => binOp p l op r (go l) (go r)
    | .unaryOp p op e => unaryOp p op e (go e)
    | .boolOp p op vs => boolOp p op vs (goList vs)
    | .compare p l ops cs => compare p l ops cs (go l) (goList cs)
    | .ifExp p c t e => ifExp p c t e (go c) (go t) (go e)
    | .call p f args kws => call p f args kws (go f) (goList args) (goKws kws)
    | .attribute p e a => attr p e a (go e)
    | .subscript p e s => subscript p e s (go e) (go s)
    | .tuple p es => tuple p es (goList es)
  goList : (es : List PyExpr) → ∀ a, a ∈ es → motive a
    | _ :: _, _, .head _ => go _
    | _ :: es, a, .tail _ h => goList es a h
  goKws : (kws : List PyKeyword) → ∀ k, k ∈ kws → motive k.value
    | .mk _ _ v :: _, _, .head _ => go v
    | _ :: kws, k, .tail _ h => goKws kws k h

/-- A positional parameter `arg(arg, annotation)`. -/
structure PyArg where
  pos : Pos
  name : String
  annotation : Option PyExpr
  deriving Repr, Inhabited

/-- An imported name `alias(name, asname)`. -/
structure PyAlias where
  pos : Pos
  name : String
  asname : Option String
  deriving Repr, DecidableEq, Inhabited

/-- The statements of the subset (`ast.stmt`). -/
inductive PyStmt where
  /-- `FunctionDef(name, args, body, decorator_list, returns)` with positional
  parameters only. -/
  | functionDef (pos : Pos) (name : String) (params : List PyArg) (body : List PyStmt)
      (decorators : List PyExpr) (returns : Option PyExpr)
  /-- `Assign(targets, value)`: `t₁ = ... = tₙ = value`. -/
  | assign (pos : Pos) (targets : List PyExpr) (value : PyExpr)
  /-- `AnnAssign(target, annotation, value, simple)`. -/
  | annAssign (pos : Pos) (target annotation : PyExpr) (value : Option PyExpr)
      (simple : Bool)
  /-- `For(target, iter, body, orelse)`. -/
  | forStmt (pos : Pos) (target iter : PyExpr) (body orelse : List PyStmt)
  /-- `If(test, body, orelse)`. -/
  | ifStmt (pos : Pos) (test : PyExpr) (body orelse : List PyStmt)
  /-- `Return(value)`. -/
  | ret (pos : Pos) (value : Option PyExpr)
  /-- `Expr(value)`: an expression statement. -/
  | expr (pos : Pos) (value : PyExpr)
  /-- `ImportFrom(module, names, level)`. -/
  | importFrom (pos : Pos) (module : Option String) (names : List PyAlias) (level : Nat)
  /-- `Pass()`. -/
  | pass (pos : Pos)
  deriving Repr, Inhabited

/-- The source span of a statement. -/
def PyStmt.pos : PyStmt → Pos
  | .functionDef p .. | .assign p .. | .annAssign p .. | .forStmt p .. | .ifStmt p ..
  | .ret p _ | .expr p _ | .importFrom p .. | .pass p => p

/-- Induction principle for `PyStmt` with hypotheses for the statements of
its bodies. -/
@[elab_as_elim]
theorem PyStmt.ind {motive : PyStmt → Prop}
    (functionDef : ∀ p n ps body ds r, (∀ s, s ∈ body → motive s) →
        motive (.functionDef p n ps body ds r))
    (assign : ∀ p ts v, motive (.assign p ts v))
    (annAssign : ∀ p t a v s, motive (.annAssign p t a v s))
    (forStmt : ∀ p t i body orelse, (∀ s, s ∈ body → motive s) →
        (∀ s, s ∈ orelse → motive s) → motive (.forStmt p t i body orelse))
    (ifStmt : ∀ p c body orelse, (∀ s, s ∈ body → motive s) →
        (∀ s, s ∈ orelse → motive s) → motive (.ifStmt p c body orelse))
    (ret : ∀ p v, motive (.ret p v))
    (expr : ∀ p v, motive (.expr p v))
    (importFrom : ∀ p m ns l, motive (.importFrom p m ns l))
    (pass : ∀ p, motive (.pass p))
    (s : PyStmt) : motive s :=
  go s
where
  go : (s : PyStmt) → motive s
    | .functionDef p n ps body ds r => functionDef p n ps body ds r (goList body)
    | .assign p ts v => assign p ts v
    | .annAssign p t a v s => annAssign p t a v s
    | .forStmt p t i body orelse => forStmt p t i body orelse (goList body) (goList orelse)
    | .ifStmt p c body orelse => ifStmt p c body orelse (goList body) (goList orelse)
    | .ret p v => ret p v
    | .expr p v => expr p v
    | .importFrom p m ns l => importFrom p m ns l
    | .pass p => pass p
  goList : (ss : List PyStmt) → ∀ s, s ∈ ss → motive s
    | _ :: _, _, .head _ => go _
    | _ :: ss, s, .tail _ h => goList ss s h

/-- A Python 3.12 module: the micro version of the interpreter that parsed it,
the source file name and the body. The major and minor versions are 3 and 12
(`PyModule.version`). -/
structure PyModule where
  micro : Nat
  file : String
  body : List PyStmt
  deriving Repr, Inhabited

/-- The interpreter version `(3, 12, micro)` of a module. -/
def PyModule.version (m : PyModule) : Nat × Nat × Nat := (3, 12, m.micro)

end Hax.Py

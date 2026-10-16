/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import HaxLean.Py.AST
public import HaxLean.ImpType

/-!
# Types of the Python subset

The types of the typed Python subset, the module environment, local contexts
and the declarative typing rules: `HasTy env Γ e τ` for expressions and
`StmtsOk env top Γ ss Γ'` for statement lists.

The rules are syntax-directed. The side condition of each rule is a typing
table (`binOpTy`, `cmpTy`, `methodTy`, `nameCallTy`, ...), a total function
from the types of the subterms (and the literal values of the operands, for
the coercion of an `int` literal) to the type of the node or to the
`RefusalKind` of the first condition it violates. The algorithmic checker
`pyCheck` (`HaxLean.Py.Check`) evaluates the same tables.

* `PyTy` — `bool`, `int`, words `U8` ... `U64`, arrays, tuples, field
  elements, secret words and secret Booleans.
* `ModEnv` — imported names, constants `N : Final = n`, field classes
  `F = field(p)`, the signatures of the functions defined so far and the
  names reserved at module level.
* `Ctx` — the local names in scope with their types, and the loop variables.
* `HasTy`, `HasTys` — typing of expressions and expression lists.
* `StmtOk`, `StmtsOk` — typing of statements; `top` says whether a first
  binding is allowed (the top level of a function body or of a loop body).
* `FnOk` — a function body: statements followed by one `return e` whose
  type is the annotated result.
* `fnSigOk` — the conditions on a function definition: its name, the entry
  layout, the placement of an entry's array result, the call depth of an
  entry, and the array element types of a function that is not an entry.
* `stmtsDepth` — the length of the longest chain of calls from a body.
* `CheckedModule.WellTyped` — every function of a checked module whose body
  is checked satisfies `FnOk`, and every function `fnSigOk`.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Py

/-! ## Types -/

/-- The types of the subset. `int` is the type of literals, loop variables
and index arithmetic; `secret` is applied to words; `secretBool` is the
result of a comparison of secrets. -/
inductive PyTy where
  | bool
  | int
  | word (w : IntWidth)
  | array (elem : PyTy) (n : Nat)
  | tuple (ts : List PyTy)
  | field (p : Nat)
  | secret (t : PyTy)
  | secretBool
  deriving Repr, Inhabited

namespace PyTy

mutual

/-- Structural equality test of types. -/
def beq : PyTy → PyTy → Bool
  | .bool, .bool | .int, .int | .secretBool, .secretBool => true
  | .word w, .word w' => decide (w = w')
  | .array e n, .array e' n' => beq e e' && decide (n = n')
  | .tuple ts, .tuple ts' => beqList ts ts'
  | .field p, .field p' => decide (p = p')
  | .secret t, .secret t' => beq t t'
  | _, _ => false

/-- Structural equality test of type lists. -/
def beqList : List PyTy → List PyTy → Bool
  | [], [] => true
  | t :: ts, t' :: ts' => beq t t' && beqList ts ts'
  | _, _ => false

end

mutual

theorem beq_refl : (a : PyTy) → beq a a = true
  | .bool | .int | .secretBool | .word _ | .field _ => by simp [beq]
  | .array e _ => by simp [beq, beq_refl e]
  | .tuple ts => by simp [beq, beqList_refl ts]
  | .secret t => by simp [beq, beq_refl t]

theorem beqList_refl : (ts : List PyTy) → beqList ts ts = true
  | [] => by simp [beqList]
  | t :: ts => by simp [beqList, beq_refl t, beqList_refl ts]

end

mutual

theorem eq_of_beq : (a b : PyTy) → beq a b = true → a = b
  | .bool, b, h | .int, b, h | .secretBool, b, h | .word _, b, h | .field _, b, h => by
      cases b <;> simp_all [beq]
  | .array e n, b, h => by
      cases b <;> simp only [beq, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq,
        PyTy.array.injEq] at h ⊢
      exact ⟨eq_of_beq e _ h.1, h.2⟩
  | .tuple ts, b, h => by
      cases b <;> simp only [beq, reduceCtorEq, PyTy.tuple.injEq] at h ⊢
      exact eq_of_beqList ts _ h
  | .secret t, b, h => by
      cases b <;> simp only [beq, reduceCtorEq, PyTy.secret.injEq] at h ⊢
      exact eq_of_beq t _ h

theorem eq_of_beqList : (ts ts' : List PyTy) → beqList ts ts' = true → ts = ts'
  | [], ts', h => by cases ts' <;> simp_all [beqList]
  | t :: ts, ts', h => by
      cases ts' <;> simp only [beqList, Bool.and_eq_true, reduceCtorEq, List.cons.injEq] at h ⊢
      exact ⟨eq_of_beq t _ h.1, eq_of_beqList ts _ h.2⟩

end

instance : DecidableEq PyTy := fun a b =>
  if h : beq a b = true then isTrue (eq_of_beq a b h)
  else isFalse fun e => h (e ▸ beq_refl a)

/-- The width and secrecy of a public or secret word. -/
def wordOf : PyTy → Option (IntWidth × Bool)
  | .word w => some (w, false)
  | .secret (.word w) => some (w, true)
  | _ => none

/-- The modulus of a field element. -/
def fieldOf : PyTy → Option Nat
  | .field p => some p
  | _ => none

/-- The types a local name may hold: `bool`, words, secret words, field
elements and arrays. -/
def storable : PyTy → Bool
  | .bool | .word _ | .field _ | .secret (.word _) | .array _ _ => true
  | _ => false

/-- The scalar types of an entry function's layout: words, field elements
and secret words. -/
def abiScalar : PyTy → Bool
  | .word _ | .field _ | .secret (.word _) => true
  | _ => false

/-- A parameter type of an entry function: an ABI scalar or an array of them. -/
def abiParam : PyTy → Bool
  | .array t _ => t.abiScalar
  | t => t.abiScalar

/-- A result type of an entry function: a word, a field element or an array
of ABI scalars. -/
def abiResult : PyTy → Bool
  | .word _ | .field _ => true
  | .array t _ => t.abiScalar
  | _ => false

/-- A parameter or result type of a module function that is not an entry: a
non-array type, or an array of 64-bit elements (`U64`, `Secret[U64]` or field
elements), the element types the callee typing `modFnElem` of the compiler's
module chain (`NFChain.lean`) accepts. -/
def calleeOk : PyTy → Bool
  | .array (.word .w64) _ | .array (.secret (.word .w64)) _ | .array (.field _) _ => true
  | .array _ _ => false
  | _ => true

end PyTy

/-- The word type of width `w`, secret when `s`. -/
def mkWord (w : IntWidth) (s : Bool) : PyTy :=
  if s then .secret (.word w) else .word w

/-- The width of the word class `U8`, `U16`, `U32` or `U64`. -/
def wordName? : String → Option IntWidth
  | "U8" => some .w8
  | "U16" => some .w16
  | "U32" => some .w32
  | "U64" => some .w64
  | _ => none

/-- The names `from catcrypt_py import` may bring into scope. -/
def catcryptNames : List String :=
  ["U8", "U16", "U32", "U64", "Array", "Secret", "field", "select", "entry", "linked"]

/-! ## Refusal kinds -/

/-- The conditions of the subset, one constructor per refusal. -/
inductive RefusalKind where
  /-- The module does not start with a docstring. -/
  | noDocstring
  /-- A module-level statement other than an import, a constant, a field
  class or a function definition. -/
  | moduleStmt
  /-- An import from a module other than `typing` and `catcrypt_py`, or a
  relative import. -/
  | importModule
  /-- An imported name the module does not export to the subset. -/
  | importName
  /-- An import with `as`. -/
  | importAlias
  /-- A name used without its import. -/
  | notImported
  /-- A module constant whose value is not an `int` literal `≥ 0`. -/
  | constantValue
  /-- A field class `field(p)` with `p` outside `(1, 2^64)`. -/
  | fieldModulus
  /-- A module-level name defined twice. -/
  | duplicateName
  /-- A decorator other than `entry`, `linked` and `linked(name="...")`, or
  more than one decorator. -/
  | decorator
  /-- A parameter or a result without annotation. -/
  | missingAnnotation
  /-- An annotation outside the type forms of the subset. -/
  | annotation
  /-- A `tuple[...]` annotation. -/
  | tupleAnnotation
  /-- An array length that is neither a literal nor a constant name. -/
  | arrayLength
  /-- Two parameters with one name. -/
  | duplicateParam
  /-- An entry function with more than six parameters, or a parameter or
  result type outside the entry layout. -/
  | entryAbi
  /-- A function body whose last statement is not `return e`. -/
  | noReturn
  /-- A `return` before the last statement. -/
  | returnNotLast
  /-- A returned value whose type is not the annotated result. -/
  | returnType
  /-- A nested function definition. -/
  | nestedDef
  /-- An import inside a function. -/
  | importInFunction
  /-- An expression statement other than a docstring. -/
  | exprStmt
  /-- An assignment target other than a name or a tuple. -/
  | assignTarget
  /-- A chained assignment `a = b = e`. -/
  | chainedAssign
  /-- A tuple target `x, y = e`. -/
  | tupleTarget
  /-- An annotated assignment without value. -/
  | annAssignForm
  /-- An annotation whose type is not the type of the value. -/
  | annMismatch
  /-- An annotated assignment of a name already bound. -/
  | annotatedRebind
  /-- An assignment of a loop variable. -/
  | loopVarRebound
  /-- An assignment changing the type of a name. -/
  | typeChange
  /-- A first binding inside an arm of `if`. -/
  | bindInBranch
  /-- A local name that is a module-level, imported or reserved name. -/
  | shadowsName
  /-- A binding of a value of type `int`, `secretBool` or a tuple. -/
  | notStorable
  /-- A `for` target other than a name. -/
  | forTarget
  /-- A `for` loop with an `else` clause. -/
  | forElse
  /-- A loop iterator other than `range(...)` or `reversed(range(...))`. -/
  | loopHead
  /-- A loop bound other than an `int` literal below `2^64`, a constant, a
  loop variable or a public word name. -/
  | loopBound
  /-- A loop variable already bound. -/
  | loopVarBound
  /-- A condition that is not a `bool`. -/
  | conditionType
  /-- A condition on a secret. -/
  | secretCondition
  /-- A name read before its binding, or outside its scope. -/
  | unboundName
  /-- A string or `None` constant in an expression. -/
  | constant
  /-- An operator outside the subset. -/
  | operator
  /-- An operand of a type the operator does not take. -/
  | operandType
  /-- Word operands of two widths, or field elements of two moduli. -/
  | widthMismatch
  /-- An `int` literal outside the range of the word or field it is coerced to. -/
  | literalRange
  /-- A non-literal `int` expression outside an index, a loop bound, a word
  constructor or a comparison with an `int`. -/
  | intContext
  /-- An array index that is a secret. -/
  | secretIndex
  /-- A shift or rotation amount that is a secret. -/
  | secretAmount
  /-- An index or amount of a type other than `int` or a word. -/
  | indexType
  /-- A comparison chain `a < b < c`. -/
  | comparisonChain
  /-- An ordering comparison of field elements. -/
  | fieldOrder
  /-- An operand of `and`, `or` that is not a `bool`. -/
  | boolOperand
  /-- The arms of `a if c else b` of two types, or of type `int` or
  `secretBool`. -/
  | branchType
  /-- A method outside the subset, or on a receiver of another type. -/
  | method
  /-- A method call with arguments of the wrong number or type. -/
  | methodArgs
  /-- A call of something other than a name or a method. -/
  | callee
  /-- A call whose arguments do not match the callee's signature. -/
  | callArgs
  /-- A call of a function defined later in the module, or of itself. -/
  | forwardCall
  /-- A keyword argument in a call. -/
  | keyword
  /-- An attribute read other than a method call. -/
  | attribute
  /-- A word constructor applied to something other than an `int`. -/
  | wordCtor
  /-- A `select` whose arguments do not have the types of the subset. -/
  | select
  /-- A `cast` whose argument is not a word class. -/
  | cast
  /-- A tuple whose elements are not storable. -/
  | tupleElem
  /-- An `int` literal or module constant outside `[0, 2^64)` in an index, a
  shift or rotation amount, `int` arithmetic or an `int` comparison, or as the
  value of a module constant. -/
  | intLiteral
  /-- A parameter or result of a function that is neither an entry nor linked
  whose type is an array of elements narrower than 64 bits. -/
  | calleeArray
  /-- An entry function whose longest chain of calls of functions that are not
  linked is longer than `maxCallDepth`. -/
  | callDepth
  /-- A function named after a call head of the front (`frontHeadNames`). -/
  | fnName
  /-- A local or parameter whose name starts with `__anorm`. -/
  | anormName
  /-- An entry function with six parameters whose result is an array of a
  length no array parameter has. -/
  | entryResult
  deriving Repr, DecidableEq, Inhabited

/-! ## Environments and contexts -/

/-- The signature of a module function: named, typed parameters, the result,
whether it is an entry, whether it is linked (with the optional name given by
`linked(name="...")`), and the length of the longest chain of calls of
functions that are not linked from its body (`stmtsDepth`). -/
structure FnSig where
  params : List (String × PyTy)
  result : PyTy
  entry : Bool
  linked : Option (Option String)
  depth : Nat := 0
  deriving Repr, Inhabited

/-- The entry layout condition: at most six parameters of ABI parameter types
and an ABI result. -/
def FnSig.entryAbiOk (s : FnSig) : Bool :=
  decide (s.params.length ≤ 6) && s.params.all (·.2.abiParam) && s.result.abiResult

/-- The placement of an entry's array result: the layout `mkResult` of the
census (`CensusCore.lean`) reads an array result of length `n` from an array
parameter of length `n`, or else from a further output parameter in the next
of the six argument registers; an array result of an entry with six
parameters needs an array parameter of its length. -/
def FnSig.entryResultOk (s : FnSig) : Bool :=
  match s.result with
  | .array _ n =>
    decide (s.params.length < 6) || s.params.any fun p =>
      match p.2 with
      | .array _ m => decide (m = n)
      | _ => false
  | _ => true

/-- The parameter and result types of a function that is not an entry satisfy
`PyTy.calleeOk`. -/
def FnSig.calleeOk (s : FnSig) : Bool :=
  s.params.all (·.2.calleeOk) && s.result.calleeOk

/-- The bound on the longest chain of calls from an entry: the rounds of
inlining `inlineRounds` of the census module (`CensusCore.lean`). -/
def maxCallDepth : Nat := 4

/-- The names a module function may not have: the array operations `index`,
`len`, `array_update`, `repeat` and `array_lit`, `range_incl_end`, and the
identifiers among the call heads of the front's tables `hax64BinTable`,
`hax64UnTable`, `hax64CmpTable`, `hax64BitTable` and `hax64TerTable`
(`ImpToNF.lean` of the compiler) with their width tags removed. The typing
`crateSigOf` of a module looks a call head up among the module's functions
before the tables, so a function of one of these names would capture the
operation. -/
def frontHeadNames : List String :=
  ["index", "len", "array_update", "repeat", "array_lit", "range_incl_end",
    "wrapping_add", "wrapping_sub", "wrapping_mul", "BitAnd", "BitOr", "BitXor", "Shl", "Shr",
    "rotate_right", "rotate_left", "shl", "shr", "mulhi", "Add", "Sub", "Mul",
    "Not", "wrapping_neg", "cast",
    "Eq", "eq", "Ne", "ne", "Lt", "lt", "Le", "le", "Gt", "gt", "Ge", "ge",
    "select"]

/-- The conditions on a function definition with name `name` and signature
`s`: the name is not in `frontHeadNames`; an entry satisfies the layout
condition and `entryResultOk` and has call depth at most `maxCallDepth`; a
function that is neither an entry nor linked satisfies `calleeOk`. -/
def fnSigOk (name : String) (s : FnSig) : Except RefusalKind Unit :=
  if name ∈ frontHeadNames then .error .fnName
  else if s.entry then
    if !s.entryAbiOk then .error .entryAbi
    else if !s.entryResultOk then .error .entryResult
    else if maxCallDepth < s.depth then .error .callDepth
    else .ok ()
  else if s.linked.isNone && !s.calleeOk then .error .calleeArray
  else .ok ()

/-- An entry accepted by `fnSigOk` satisfies the layout condition. -/
theorem fnSigOk_entryAbi {name : String} {s : FnSig} (h : fnSigOk name s = .ok ())
    (he : s.entry = true) : s.entryAbiOk = true := by
  unfold fnSigOk at h
  repeat' split at h
  all_goals simp_all

/-- The module environment. -/
structure ModEnv where
  imports : List String
  consts : List (String × Nat)
  fields : List (String × Nat)
  fns : List (String × FnSig)
  reserved : List String
  deriving Repr, Inhabited

/-- The module-level names defined so far. -/
def ModEnv.defined (env : ModEnv) : List String :=
  env.imports ++ env.consts.map (·.1) ++ env.fields.map (·.1) ++ env.fns.map (·.1)

/-- A local context: the names in scope with their types, and the loop
variables among them. -/
structure Ctx where
  vars : List (String × PyTy)
  loopVars : List String
  deriving Repr, Inhabited

/-- The type of a local name. -/
def Ctx.lookup (Γ : Ctx) (x : String) : Option PyTy := List.lookup x Γ.vars

/-- The context with `x : τ` bound. -/
def Ctx.bind (Γ : Ctx) (x : String) (τ : PyTy) : Ctx :=
  { Γ with vars := (x, τ) :: Γ.vars }

/-- The context with the loop variable `i : int` bound. -/
def Ctx.bindLoop (Γ : Ctx) (i : String) : Ctx :=
  { vars := (i, .int) :: Γ.vars, loopVars := i :: Γ.loopVars }

/-- The context of a function body: its parameters. -/
def Ctx.ofParams (ps : List (String × PyTy)) : Ctx := { vars := ps, loopVars := [] }

/-! ## Typing tables -/

/-- The literal value of an expression: an `int` constant or a module
constant name. -/
def litVal (env : ModEnv) : PyExpr → Option Int
  | .const _ (.int n) => some n
  | .name _ x => (List.lookup x env.consts).map Int.ofNat
  | _ => none

/-- The type of a name: a local, or a module constant of type `int`. -/
def nameTy (env : ModEnv) (Γ : Ctx) (x : String) : Except RefusalKind PyTy :=
  match Γ.lookup x with
  | some τ => .ok τ
  | none =>
    match List.lookup x env.consts with
    | some _ => .ok .int
    | none => .error .unboundName

/-- The type of a constant. -/
def constTy : PyConst → Except RefusalKind PyTy
  | .bool _ => .ok .bool
  | .int _ => .ok .int
  | _ => .error .constant

/-- Whether the `int` literal `n` is a value of a word of width `w`. -/
def litFits (w : IntWidth) (n : Int) : Bool := decide (0 ≤ n) && decide (n < 2 ^ w.bits)

/-- The width and secrecy of a word operation whose word operand has width
`w` and secrecy `s` and whose other operand has type `τ` and literal value
`l`: an `int` literal in range is coerced. -/
def coerceLit (w : IntWidth) (s : Bool) (τ : PyTy) (l : Option Int) :
    Except RefusalKind (IntWidth × Bool) :=
  match τ, l with
  | .int, some n => if litFits w n then .ok (w, s) else .error .literalRange
  | .int, none => .error .intContext
  | _, _ => .error .operandType

/-- The width and secrecy of the operands of a binary word operation; an
`int` literal operand is coerced, and a secret operand makes the result
secret. -/
def wordOperands (τl : PyTy) (ll : Option Int) (τr : PyTy) (lr : Option Int) :
    Except RefusalKind (IntWidth × Bool) :=
  match τl.wordOf, τr.wordOf with
  | some (w, s), some (w', s') => if w = w' then .ok (w, s || s') else .error .widthMismatch
  | some (w, s), none => coerceLit w s τr lr
  | none, some (w, s) => coerceLit w s τl ll
  | none, none => .error .operandType

/-- Whether an `int` literal `n` is an element of the field of modulus `p`. -/
def coerceFieldLit (p : Nat) (τ : PyTy) (l : Option Int) : Except RefusalKind Nat :=
  match τ, l with
  | .int, some n => if decide (0 ≤ n) && decide (n < p) then .ok p else .error .literalRange
  | .int, none => .error .intContext
  | _, _ => .error .operandType

/-- The modulus of the operands of a binary field operation; an `int`
literal operand is coerced. -/
def fieldOperands (τl : PyTy) (ll : Option Int) (τr : PyTy) (lr : Option Int) :
    Except RefusalKind Nat :=
  match τl.fieldOf, τr.fieldOf with
  | some p, some p' => if p = p' then .ok p else .error .widthMismatch
  | some p, none => coerceFieldLit p τr lr
  | none, some p => coerceFieldLit p τl ll
  | none, none => .error .operandType

/-- The literal value of an `int` operand: none, or in `[0, 2^64)`, the range
of the integer literals the front types (`litInt` of `ImpToNF.lean`). -/
def intLitOk : Option Int → Except RefusalKind Unit
  | some n => if decide (0 ≤ n) && decide (n < 2 ^ 64) then .ok () else .error .intLiteral
  | none => .ok ()

/-- A shift or rotation amount: an `int` literal below `2^64` or a public word. -/
def amountOk (τ : PyTy) (l : Option Int) : Except RefusalKind Unit :=
  match τ, l with
  | .int, some n => if decide (0 ≤ n) then intLitOk (some n) else .error .literalRange
  | .int, none => .error .intContext
  | .word _, _ => .ok ()
  | .secret _, _ => .error .secretAmount
  | _, _ => .error .indexType

/-- An array index: an `int` expression, whose literal value is below `2^64`,
or a public word. -/
def indexOk : PyTy → Option Int → Except RefusalKind Unit
  | .int, l => intLitOk l
  | .word _, _ => .ok ()
  | .secret _, _ => .error .secretIndex
  | _, _ => .error .indexType

/-- The type of a binary operation from the types and literal values of its
operands. -/
def binOpTy (op : PyBinOp) (τl : PyTy) (ll : Option Int) (τr : PyTy) (lr : Option Int) :
    Except RefusalKind PyTy :=
  match op with
  | .add | .sub | .mult =>
    match τl, τr with
    | .int, .int => (intLitOk ll).bind fun _ => (intLitOk lr).map fun _ => .int
    | _, _ =>
      if τl.fieldOf.isSome || τr.fieldOf.isSome then
        (fieldOperands τl ll τr lr).map .field
      else (wordOperands τl ll τr lr).map fun ws => mkWord ws.1 ws.2
  | .bitAnd | .bitOr | .bitXor => (wordOperands τl ll τr lr).map fun ws => mkWord ws.1 ws.2
  | .lShift | .rShift =>
    match τl.wordOf with
    | some (w, s) => (amountOk τr lr).map fun _ => mkWord w s
    | none => .error .operandType
  | _ => .error .operator

/-- The type of a unary operation. -/
def unaryTy (op : PyUnaryOp) (τ : PyTy) : Except RefusalKind PyTy :=
  match op, τ with
  | .invert, τ =>
    match τ.wordOf with
    | some (w, s) => .ok (mkWord w s)
    | none => .error .operandType
  | .not, .bool => .ok .bool
  | .uSub, .field p => .ok (.field p)
  | .uAdd, _ => .error .operator
  | _, _ => .error .operandType

/-- The type of `and`, `or`: every operand is a `bool`. -/
def boolOpTy (τs : List PyTy) : Except RefusalKind PyTy :=
  if τs.all (· == .bool) then .ok .bool else .error .boolOperand

/-- The type of a single comparison. -/
def cmpTy (op : PyCmpOp) (τl : PyTy) (ll : Option Int) (τr : PyTy) (lr : Option Int) :
    Except RefusalKind PyTy :=
  match op with
  | .is | .isNot | .in_ | .notIn => .error .operator
  | _ =>
    match τl, τr with
    | .int, .int => (intLitOk ll).bind fun _ => (intLitOk lr).map fun _ => .bool
    | _, _ =>
      if τl.fieldOf.isSome || τr.fieldOf.isSome then
        match op with
        | .eq | .notEq => (fieldOperands τl ll τr lr).map fun _ => .bool
        | _ => .error .fieldOrder
      else (wordOperands τl ll τr lr).map fun ws => if ws.2 then .secretBool else .bool

/-- The type of a comparison node: exactly one operator and one comparator. -/
def compareTy (ops : List PyCmpOp) (τl : PyTy) (ll : Option Int) (τs : List PyTy)
    (ls : List (Option Int)) : Except RefusalKind PyTy :=
  match ops, τs, ls with
  | [op], [τr], [lr] => cmpTy op τl ll τr lr
  | _, _, _ => .error .comparisonChain

/-- A condition: a public `bool`. -/
def condOk : PyTy → Except RefusalKind Unit
  | .bool => .ok ()
  | .secretBool => .error .secretCondition
  | _ => .error .conditionType

/-- The type of `t if c else e`. -/
def ifExpTy (τc τt τe : PyTy) : Except RefusalKind PyTy := do
  condOk τc
  if τt = τe ∧ τt ≠ .int ∧ τt ≠ .secretBool then .ok τt else .error .branchType

/-- The type of `a[i]` from the types of `a` and `i` and the literal value of
`i`. -/
def indexTy (τa τi : PyTy) (li : Option Int) : Except RefusalKind PyTy :=
  match τa with
  | .array t _ => (indexOk τi li).map fun _ => t
  | _ => .error .operandType

/-- The type of a tuple expression of storable elements. -/
def tupleTy (τs : List PyTy) : Except RefusalKind PyTy :=
  if τs.all (·.storable) then .ok (.tuple τs) else .error .tupleElem

/-- The type of `x.cast(Uw)`. -/
def castTy (env : ModEnv) (args : List PyExpr) (τr : PyTy) : Except RefusalKind PyTy :=
  match args with
  | [.name _ x] =>
    match wordName? x with
    | some w =>
      if x ∈ env.imports then
        match τr.wordOf with
        | some (_, s) => .ok (mkWord w s)
        | none => .error .method
      else .error .notImported
    | none => .error .cast
  | _ => .error .cast

/-- The type of a method call other than `cast` from the receiver's type and
the types and literal values of the arguments. -/
def methodTy (m : String) (τr : PyTy) (τs : List PyTy) (ls : List (Option Int)) :
    Except RefusalKind PyTy :=
  match m with
  | "wrapping_add" | "wrapping_sub" | "wrapping_mul" =>
    match τs, ls with
    | [τ], [l] => (wordOperands τr none τ l).map fun ws => mkWord ws.1 ws.2
    | _, _ => .error .methodArgs
  | "wrapping_neg" =>
    match τs, τr.wordOf with
    | [], some (.w64, s) => .ok (mkWord .w64 s)
    | [], _ => .error .method
    | _, _ => .error .methodArgs
  | "mulhi" =>
    match τs, ls with
    | [τ], [l] =>
      match wordOperands τr none τ l with
      | .ok (.w64, s) => .ok (mkWord .w64 s)
      | .ok _ => .error .method
      | .error k => .error k
    | _, _ => .error .methodArgs
  | "rotate_left" | "rotate_right" =>
    match τs, ls, τr.wordOf with
    | [τ], [l], some (w, s) => (amountOk τ l).map fun _ => mkWord w s
    | [_], [_], none => .error .method
    | _, _, _ => .error .methodArgs
  | "set" =>
    match τr, τs, ls with
    | .array t n, [τi, τv], [li, _] => do
      indexOk τi li
      if τv = t then .ok (.array t n) else .error .methodArgs
    | .array _ _, _, _ => .error .methodArgs
    | _, _, _ => .error .method
  | "square" | "double" =>
    match τr, τs with
    | .field p, [] => .ok (.field p)
    | .field _, _ => .error .methodArgs
    | _, _ => .error .method
  | "declassify" =>
    match τr, τs with
    | .secret t, [] => .ok t
    | .secretBool, [] => .ok .bool
    | _, [] => .error .method
    | _, _ => .error .methodArgs
  | _ => .error .method

/-- The type of `select(c, a, b)`: on a public condition both arms have one
type; on a secret condition both arms are words of one width and the result
is secret. -/
def selectTy : List PyTy → Except RefusalKind PyTy
  | [.bool, a, b] => if a = b ∧ a ≠ .int ∧ a ≠ .secretBool then .ok a else .error .select
  | [.secretBool, a, b] =>
    match a.wordOf, b.wordOf with
    | some (w, _), some (w', _) => if w = w' then .ok (.secret (.word w)) else .error .select
    | _, _ => .error .select
  | _ => .error .select

/-- The type of a call of the name `f`: a word constructor, `select`, or a
module function defined earlier at its signature. -/
def nameCallTy (env : ModEnv) (f : String) (τs : List PyTy) (ls : List (Option Int)) :
    Except RefusalKind PyTy :=
  match wordName? f with
  | some w =>
    if f ∈ env.imports then
      match τs, ls with
      | [.int], [some n] => if litFits w n then .ok (.word w) else .error .literalRange
      | [.int], [none] => .ok (.word w)
      | _, _ => .error .wordCtor
    else .error .notImported
  | none =>
    if f = "select" then
      if "select" ∈ env.imports then selectTy τs else .error .notImported
    else
      match List.lookup f env.fns with
      | some sig => if τs = sig.params.map (·.2) then .ok sig.result else .error .callArgs
      | none => if f ∈ env.reserved then .error .forwardCall else .error .unboundName

/-! ## Typing rules for expressions -/

mutual

/-- `HasTy env Γ e τ`: the expression `e` has type `τ` in the module
environment `env` and the local context `Γ`. -/
inductive HasTy (env : ModEnv) (Γ : Ctx) : PyExpr → PyTy → Prop where
  | name {p : Pos} {x : String} {τ : PyTy} :
      nameTy env Γ x = .ok τ → HasTy env Γ (.name p x) τ
  | const {p : Pos} {c : PyConst} {τ : PyTy} :
      constTy c = .ok τ → HasTy env Γ (.const p c) τ
  | binOp {p : Pos} {l r : PyExpr} {op : PyBinOp} {τl τr τ : PyTy} :
      HasTy env Γ l τl → HasTy env Γ r τr →
      binOpTy op τl (litVal env l) τr (litVal env r) = .ok τ →
      HasTy env Γ (.binOp p l op r) τ
  | unaryOp {p : Pos} {op : PyUnaryOp} {e : PyExpr} {τe τ : PyTy} :
      HasTy env Γ e τe → unaryTy op τe = .ok τ → HasTy env Γ (.unaryOp p op e) τ
  | boolOp {p : Pos} {op : PyBoolOp} {vs : List PyExpr} {τs : List PyTy} {τ : PyTy} :
      HasTys env Γ vs τs → boolOpTy τs = .ok τ → HasTy env Γ (.boolOp p op vs) τ
  | compare {p : Pos} {l : PyExpr} {ops : List PyCmpOp} {cs : List PyExpr} {τl τ : PyTy}
      {τs : List PyTy} :
      HasTy env Γ l τl → HasTys env Γ cs τs →
      compareTy ops τl (litVal env l) τs (cs.map (litVal env)) = .ok τ →
      HasTy env Γ (.compare p l ops cs) τ
  | ifExp {p : Pos} {c t e : PyExpr} {τc τt τe τ : PyTy} :
      HasTy env Γ c τc → HasTy env Γ t τt → HasTy env Γ e τe → ifExpTy τc τt τe = .ok τ →
      HasTy env Γ (.ifExp p c t e) τ
  | cast {p q : Pos} {recv : PyExpr} {args : List PyExpr} {τr τ : PyTy} :
      HasTy env Γ recv τr → castTy env args τr = .ok τ →
      HasTy env Γ (.call p (.attribute q recv "cast") args []) τ
  | method {p q : Pos} {recv : PyExpr} {m : String} {args : List PyExpr} {τr τ : PyTy}
      {τs : List PyTy} :
      m ≠ "cast" → HasTy env Γ recv τr → HasTys env Γ args τs →
      methodTy m τr τs (args.map (litVal env)) = .ok τ →
      HasTy env Γ (.call p (.attribute q recv m) args []) τ
  | callName {p q : Pos} {f : String} {args : List PyExpr} {τs : List PyTy} {τ : PyTy} :
      HasTys env Γ args τs → nameCallTy env f τs (args.map (litVal env)) = .ok τ →
      HasTy env Γ (.call p (.name q f) args []) τ
  | subscript {p : Pos} {a i : PyExpr} {τa τi τ : PyTy} :
      HasTy env Γ a τa → HasTy env Γ i τi → indexTy τa τi (litVal env i) = .ok τ →
      HasTy env Γ (.subscript p a i) τ
  | tuple {p : Pos} {es : List PyExpr} {τs : List PyTy} {τ : PyTy} :
      HasTys env Γ es τs → tupleTy τs = .ok τ → HasTy env Γ (.tuple p es) τ

/-- `HasTys env Γ es τs`: the expressions `es` have the types `τs`. -/
inductive HasTys (env : ModEnv) (Γ : Ctx) : List PyExpr → List PyTy → Prop where
  | nil : HasTys env Γ [] []
  | cons {e : PyExpr} {es : List PyExpr} {τ : PyTy} {τs : List PyTy} :
      HasTy env Γ e τ → HasTys env Γ es τs → HasTys env Γ (e :: es) (τ :: τs)

end

/-! ## Statement tables -/

/-- Whether `x` has the prefix `__anorm` of the fresh names of the A-normal
form of the compiler, which no local or parameter may have. -/
def anormName (x : String) : Bool := x.startsWith "__anorm"

/-- The binding of `x` to a value of type `τ`: a rebinding keeps the type of
`x`; a first binding is allowed only where `top` holds, of a storable type,
and of a name that is neither reserved at module level nor an `anormName`. A
loop variable is not rebound. -/
def bindName (env : ModEnv) (top : Bool) (Γ : Ctx) (x : String) (τ : PyTy) :
    Except RefusalKind Ctx :=
  if x ∈ Γ.loopVars then .error .loopVarRebound
  else
    match Γ.lookup x with
    | some τ' => if τ' = τ then .ok Γ else .error .typeChange
    | none =>
      if !top then .error .bindInBranch
      else if x ∈ env.reserved then .error .shadowsName
      else if anormName x then .error .anormName
      else if !τ.storable then .error .notStorable
      else .ok (Γ.bind x τ)

/-- The names of a list of name expressions. -/
def namesOf : List PyExpr → Option (List String)
  | [] => some []
  | .name _ x :: es => (namesOf es).map (x :: ·)
  | _ => none

/-- The context after `targets = v` with `v : τ`: the target is one name. -/
def assignTy (env : ModEnv) (top : Bool) (Γ : Ctx) (targets : List PyExpr) (_v : PyExpr)
    (τ : PyTy) : Except RefusalKind Ctx :=
  match targets with
  | [.name _ x] => bindName env top Γ x τ
  | [.tuple _ _] => .error .tupleTarget
  | [_] => .error .assignTarget
  | _ => .error .chainedAssign

/-- An element type of an array annotation: a word class, a field class or
`Secret[Uw]`. -/
def parseScalar (env : ModEnv) : PyExpr → Except RefusalKind PyTy
  | .name _ x =>
    match wordName? x with
    | some w => if x ∈ env.imports then .ok (.word w) else .error .notImported
    | none =>
      match List.lookup x env.fields with
      | some p => .ok (.field p)
      | none => .error .annotation
  | .subscript _ (.name _ "Secret") (.name _ x) =>
    if "Secret" ∈ env.imports then
      match wordName? x with
      | some w => if x ∈ env.imports then .ok (.secret (.word w)) else .error .notImported
      | none => .error .annotation
    else .error .notImported
  | _ => .error .annotation

/-- The length of an array annotation: a literal `≥ 0` or a constant name. -/
def arrayLen (env : ModEnv) : PyExpr → Except RefusalKind Nat
  | .const _ (.int n) => if 0 ≤ n then .ok n.toNat else .error .arrayLength
  | .name _ x =>
    match List.lookup x env.consts with
    | some n => .ok n
    | none => .error .arrayLength
  | _ => .error .arrayLength

/-- A non-tuple annotation: a scalar or `Array[T, N]`. -/
def parseBase (env : ModEnv) : PyExpr → Except RefusalKind PyTy
  | .subscript _ (.name _ "Array") (.tuple _ [t, n]) =>
    if "Array" ∈ env.imports then
      (parseScalar env t).bind fun τ => (arrayLen env n).map fun k => .array τ k
    else .error .notImported
  | e => parseScalar env e

/-- An annotation: a scalar or `Array[T, N]`; `tuple[...]` is refused. -/
def parseAnn (env : ModEnv) : PyExpr → Except RefusalKind PyTy
  | .subscript _ (.name _ "tuple") _ => .error .tupleAnnotation
  | e => parseBase env e

/-- The context after `target: ann = v` with `v : τ`: a first binding of a
name at the annotated type. -/
def annAssignTy (env : ModEnv) (top : Bool) (Γ : Ctx) (target ann : PyExpr) (τ : PyTy) :
    Except RefusalKind Ctx :=
  match target with
  | .name _ x =>
    (parseAnn env ann).bind fun τa =>
      if τa ≠ τ then .error .annMismatch
      else if (Γ.lookup x).isSome then .error .annotatedRebind
      else bindName env top Γ x τ
  | _ => .error .assignTarget

/-- A loop bound: an `int` literal below `2^64`, a constant below `2^64`, a
loop variable or a public word name. -/
def boundOk (env : ModEnv) (Γ : Ctx) : PyExpr → Except RefusalKind Unit
  | .const _ (.int n) => if decide (0 ≤ n) && decide (n < 2 ^ 64) then .ok () else .error .loopBound
  | .name _ x =>
    match Γ.lookup x with
    | some .int | some (.word _) => .ok ()
    | some (.secret _) => .error .secretCondition
    | some _ => .error .loopBound
    | none =>
      match List.lookup x env.consts with
      | some n => if n < 2 ^ 64 then .ok () else .error .loopBound
      | none => .error .unboundName
  | _ => .error .loopBound

/-- `range(hi)` or `range(lo, hi)`. -/
def rangeOk (env : ModEnv) (Γ : Ctx) : PyExpr → Except RefusalKind Unit
  | .call _ (.name _ "range") [hi] [] => boundOk env Γ hi
  | .call _ (.name _ "range") [lo, hi] [] => (boundOk env Γ lo).bind fun _ => boundOk env Γ hi
  | _ => .error .loopHead

/-- A loop iterator: `range(...)` or `reversed(range(...))`. -/
def loopIterOk (env : ModEnv) (Γ : Ctx) : PyExpr → Except RefusalKind Unit
  | .call _ (.name _ "reversed") [r] [] => rangeOk env Γ r
  | e => rangeOk env Γ e

/-- The context of a loop body: the loop variable, unbound before, not
reserved and not an `anormName`, bound to `int`; no `else` clause. -/
def loopEntry (env : ModEnv) (Γ : Ctx) (target iter : PyExpr) (orelse : List PyStmt) :
    Except RefusalKind Ctx :=
  if !orelse.isEmpty then .error .forElse
  else
    match target with
    | .name _ i =>
      (loopIterOk env Γ iter).bind fun _ =>
        if (Γ.lookup i).isSome then .error .loopVarBound
        else if i ∈ env.reserved then .error .shadowsName
        else if anormName i then .error .anormName
        else .ok (Γ.bindLoop i)
    | _ => .error .forTarget

/-- A docstring: a string constant. -/
def isDocstring : PyExpr → Bool
  | .const _ (.str _) => true
  | _ => false

/-! ## Typing rules for statements -/

mutual

/-- `StmtOk env top Γ s Γ'`: the statement `s` is well typed in `Γ` and
leaves the context `Γ'`; `top` says whether first bindings are allowed. -/
inductive StmtOk (env : ModEnv) : Bool → Ctx → PyStmt → Ctx → Prop where
  | pass {top : Bool} {Γ : Ctx} {p : Pos} : StmtOk env top Γ (.pass p) Γ
  | doc {top : Bool} {Γ : Ctx} {p : Pos} {v : PyExpr} :
      isDocstring v = true → StmtOk env top Γ (.expr p v) Γ
  | assign {top : Bool} {Γ Γ' : Ctx} {p : Pos} {targets : List PyExpr} {v : PyExpr}
      {τ : PyTy} :
      HasTy env Γ v τ → assignTy env top Γ targets v τ = .ok Γ' →
      StmtOk env top Γ (.assign p targets v) Γ'
  | annAssign {top : Bool} {Γ Γ' : Ctx} {p : Pos} {target ann v : PyExpr} {simple : Bool}
      {τ : PyTy} :
      HasTy env Γ v τ → annAssignTy env top Γ target ann τ = .ok Γ' →
      StmtOk env top Γ (.annAssign p target ann (some v) simple) Γ'
  | forStmt {top : Bool} {Γ Γ₀ Γb : Ctx} {p : Pos} {target iter : PyExpr}
      {body orelse : List PyStmt} :
      loopEntry env Γ target iter orelse = .ok Γ₀ → StmtsOk env true Γ₀ body Γb →
      StmtOk env top Γ (.forStmt p target iter body orelse) Γ
  | ifStmt {top : Bool} {Γ Γ₁ Γ₂ : Ctx} {p : Pos} {c : PyExpr} {body orelse : List PyStmt}
      {τ : PyTy} :
      HasTy env Γ c τ → condOk τ = .ok () → StmtsOk env false Γ body Γ₁ →
      StmtsOk env false Γ₁ orelse Γ₂ → StmtOk env top Γ (.ifStmt p c body orelse) Γ₂

/-- `StmtsOk env top Γ ss Γ'`: the statements `ss` are well typed from `Γ`,
each in the context the previous one leaves. -/
inductive StmtsOk (env : ModEnv) : Bool → Ctx → List PyStmt → Ctx → Prop where
  | nil {top : Bool} {Γ : Ctx} : StmtsOk env top Γ [] Γ
  | cons {top : Bool} {Γ Γ₁ Γ₂ : Ctx} {s : PyStmt} {ss : List PyStmt} :
      StmtOk env top Γ s Γ₁ → StmtsOk env top Γ₁ ss Γ₂ → StmtsOk env top Γ (s :: ss) Γ₂

end

/-- A function body checked against parameters `Γ₀` and the result `τ`: its
last statement is `return e`, the statements before it are well typed from
`Γ₀`, and `e` has type `τ` in the context they leave. -/
def FnOk (env : ModEnv) (Γ₀ : Ctx) (τ : PyTy) (body : List PyStmt) : Prop :=
  ∃ p e Γ', body.getLast? = some (.ret p (some e)) ∧ StmtsOk env true Γ₀ body.dropLast Γ' ∧
    HasTy env Γ' e τ

/-! ## Call depth -/

/-- The depth of a call of the name `f` in a body checked in `env`: one more
than the depth of a module function that is not linked, `0` for any other
name. -/
def callDepthOf (env : ModEnv) (f : String) : Nat :=
  match List.lookup f env.fns with
  | some sig => if sig.linked.isNone then sig.depth + 1 else 0
  | none => 0

mutual

/-- The length of the longest chain of calls of module functions that are not
linked starting at a call in the expression. -/
def exprDepth (env : ModEnv) : PyExpr → Nat
  | .name .. | .const .. => 0
  | .binOp _ l _ r => max (exprDepth env l) (exprDepth env r)
  | .unaryOp _ _ e => exprDepth env e
  | .boolOp _ _ vs => exprsDepth env vs
  | .compare _ l _ cs => max (exprDepth env l) (exprsDepth env cs)
  | .ifExp _ c t e => max (exprDepth env c) (max (exprDepth env t) (exprDepth env e))
  | .call _ func args _ =>
    let d :=
      match func with
      | .name _ f => callDepthOf env f
      | _ => exprDepth env func
    max d (exprsDepth env args)
  | .attribute _ v _ => exprDepth env v
  | .subscript _ a i => max (exprDepth env a) (exprDepth env i)
  | .tuple _ es => exprsDepth env es

/-- The largest `exprDepth` of a list of expressions. -/
def exprsDepth (env : ModEnv) : List PyExpr → Nat
  | [] => 0
  | e :: es => max (exprDepth env e) (exprsDepth env es)

end

/-- The depth of an optional expression. -/
def optDepth (env : ModEnv) : Option PyExpr → Nat
  | some e => exprDepth env e
  | none => 0

mutual

/-- The length of the longest chain of calls of module functions that are not
linked starting at a call in the statement. -/
def stmtDepth (env : ModEnv) : PyStmt → Nat
  | .assign _ _ v => exprDepth env v
  | .annAssign _ _ _ v _ => optDepth env v
  | .forStmt _ _ iter body orelse =>
    max (exprDepth env iter) (max (stmtsDepth env body) (stmtsDepth env orelse))
  | .ifStmt _ c body orelse =>
    max (exprDepth env c) (max (stmtsDepth env body) (stmtsDepth env orelse))
  | .ret _ v => optDepth env v
  | .expr _ v => exprDepth env v
  | .functionDef .. | .importFrom .. | .pass _ => 0

/-- The largest `stmtDepth` of a list of statements: the call depth of a
function body. -/
def stmtsDepth (env : ModEnv) : List PyStmt → Nat
  | [] => 0
  | s :: ss => max (stmtDepth env s) (stmtsDepth env ss)

end

/-! ## Checked modules -/

/-- A checked function: its name and position, its signature, the module
environment its body is checked in (the functions defined before it) and
its original statements. -/
structure CheckedFn where
  name : String
  pos : Pos
  sig : FnSig
  env : ModEnv
  body : List PyStmt
  deriving Repr, Inhabited

/-- A checked module: the final environment and the functions in order of
definition. -/
structure CheckedModule where
  env : ModEnv
  fns : List CheckedFn
  deriving Repr, Inhabited

/-- A checked function is well typed: its name and signature satisfy
`fnSigOk`, its recorded depth is the call depth of its body, and a function
that is not linked has a body satisfying `FnOk`. -/
def CheckedFn.WellTyped (f : CheckedFn) : Prop :=
  fnSigOk f.name f.sig = .ok () ∧ f.sig.depth = stmtsDepth f.env f.body ∧
    (f.sig.linked = none → FnOk f.env (Ctx.ofParams f.sig.params) f.sig.result f.body)

/-- A well-typed entry satisfies the layout condition. -/
theorem CheckedFn.WellTyped.entryAbiOk {f : CheckedFn} (h : f.WellTyped)
    (he : f.sig.entry = true) : f.sig.entryAbiOk = true :=
  fnSigOk_entryAbi h.1 he

/-- Every function of a checked module is well typed. -/
def CheckedModule.WellTyped (cm : CheckedModule) : Prop := ∀ f ∈ cm.fns, f.WellTyped

end Hax.Py

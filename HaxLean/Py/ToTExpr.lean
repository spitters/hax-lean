/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import HaxLean.Py.CheckSound
public import HaxLean.ScalarOp
public import HaxLean.TExpr

/-!
# Translation of a checked Python module to typed imperative terms

`pyToTExpr` maps a module accepted by `pyCheck` to the constants and the
functions of the module as `TExpr` terms, with an `ImpType` on every node, in
the shapes the hax adapter produces before the pipeline: the parameter prelude
`letBind p (var p)`, `letBind` for a first binding, `seq (assign x e) rest` for
a rebinding, `seq (forLoop i lo hi body) rest`, `seq (ifThenElse c t e) rest`,
and calls `app head args` with the heads of the front's tables.

* `PyTy.toImp` — the `ImpType` of a type of the subset.
* `trExpr`, `trExprs` — expressions, typed by re-running `inferExpr`; an `int`
  literal takes the type of its position.
* `trStmt`, `trStmts` — statements as a list of `Step`s, assembled right-nested
  by `assemble`.
* `trBlock` — a complete body; an `if` with an arm ending in `return` is the
  last node, `ifThenElse c t e` whose arms are complete bodies, the arm that
  falls through followed by the statements after the `if`.
* `trFn`, `pyToTExpr` — function bodies with their prelude; the extraction
  `PyExtraction` with the constants, the function terms and the signatures.
* `PyImage` — the constructors the translation produces: no `match_`, `lam`,
  `borrow`, `deref`, early exit, `while`, `break`, `continue`, fold, control-flow
  or `typeAscription` node.
* `pyToTExpr_pyImage` — every function term of the extraction is in `PyImage`
  after erasure.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Py

/-! ## Types -/

mutual

/-- The `ImpType` of a type of the subset: `int` is the platform word, a field
element a 64-bit word, a secret the type of its value. -/
def PyTy.toImp : PyTy → ImpType
  | .bool => .bool
  | .int => .uint .wsize
  | .word w => .uint w
  | .array t n => .array t.toImp n
  | .tuple ts => .tuple (PyTy.toImpList ts)
  | .field _ => .uint .w64
  | .secret t => t.toImp
  | .secretBool => .bool

/-- The `ImpType`s of a list of types. -/
def PyTy.toImpList : List PyTy → List ImpType
  | [] => []
  | t :: ts => t.toImp :: PyTy.toImpList ts

end

/-- The type of a node of type `τ` at a position whose `int` literals take
the type `hint`: an `int` node takes `hint`, by default the platform word. -/
def tyAt (hint : Option ImpType) : PyTy → ImpType
  | .int => hint.getD (.uint .wsize)
  | τ => τ.toImp

/-- The type an `int` literal operand takes beside an operand of type `τ`:
the word type of a word, a 64-bit word beside a field element. -/
def coerceHint (τ : PyTy) : Option ImpType :=
  match τ.wordOf, τ.fieldOf with
  | some (w, _), _ => some (.uint w)
  | none, some _ => some (.uint .w64)
  | none, none => none

/-! ## Heads -/

/-- An error message with a source position. -/
def errAt {α : Type} (p : Pos) (msg : String) : Except String α :=
  .error s!"{msg} at {p.line}:{p.col}"

/-- A checker result with its refusal as a message. -/
def liftR {α : Type} : Except PyRefusal α → Except String α
  | .ok a => .ok a
  | .error r => .error s!"refusal {(repr r.kind).pretty}"

/-- The head of a binary operation with result type `τ`: `#size` arithmetic on
`int`, the tagged field operation on a field element, the word operation of
the result's width on a word. -/
def binHead (op : PyBinOp) (τ : PyTy) : Option String :=
  match τ, τ.fieldOf, τ.wordOf with
  | .int, _, _ =>
    match op with
    | .add => some "Add#size" | .sub => some "Sub#size" | .mult => some "Mul#size"
    | _ => none
  | _, some p, _ =>
    match op with
    | .add => some ("add#p" ++ toString p) | .sub => some ("sub#p" ++ toString p)
    | .mult => some ("mul#p" ++ toString p)
    | _ => none
  | _, none, some (w, _) =>
    let t := IntWidth.tag w
    match op with
    | .add => some ("Add#" ++ t) | .sub => some ("Sub#" ++ t) | .mult => some ("Mul#" ++ t)
    | .bitAnd => some ("BitAnd#" ++ t) | .bitOr => some ("BitOr#" ++ t)
    | .bitXor => some ("BitXor#" ++ t)
    | .lShift => some ("Shl#" ++ t) | .rShift => some ("Shr#" ++ t)
    | _ => none
  | _, none, none => none

/-- The head of a unary operation with result type `τ`. -/
def unHead (op : PyUnaryOp) (τ : PyTy) : Option String :=
  match op, τ.wordOf, τ.fieldOf with
  | .invert, some (w, _), _ => some ("Not#" ++ IntWidth.tag w)
  | .not, _, _ => some "Not"
  | .uSub, _, some p => some ("neg#p" ++ toString p)
  | _, _, _ => none

/-- The head of a comparison. -/
def cmpHead : PyCmpOp → Option String
  | .eq => some "Eq" | .notEq => some "Ne" | .lt => some "Lt" | .ltE => some "Le"
  | .gt => some "Gt" | .gtE => some "Ge"
  | _ => none

/-- Whether an operand of `and`, `or` evaluates without failure: names,
constants, and comparisons, negations, Boolean and bitwise operations and
conditional expressions of such operands. -/
def pureExpr : PyExpr → Bool
  | .name .. | .const .. => true
  | .compare _ l _ cs => pureExpr l && pureExprs cs
  | .unaryOp _ .not e => pureExpr e
  | .boolOp _ _ vs => pureExprs vs
  | .binOp _ l .bitAnd r | .binOp _ l .bitOr r | .binOp _ l .bitXor r => pureExpr l && pureExpr r
  | .ifExp _ c t e => pureExpr c && pureExpr t && pureExpr e
  | _ => false
where
  /-- Every expression of the list evaluates without failure. -/
  pureExprs : List PyExpr → Bool
    | [] => true
    | e :: es => pureExpr e && pureExprs es

/-- `c₁ and ... and cₙ` (`isAnd`) or `c₁ or ... or cₙ` right-nested: strict
`&&`, `||` when every operand to the right evaluates without failure (the flag
of each pair), `ifThenElse c d false`, `ifThenElse c true d` otherwise. -/
def boolChain (isAnd : Bool) : List (Bool × TExpr) → TExpr
  | [] => .mk (.lit (.bool isAnd)) .bool
  | [(_, x)] => x
  | (_, x) :: rest =>
    let d := boolChain isAnd rest
    if rest.all (·.1) then .mk (.app (if isAnd then "&&" else "||") [x, d]) .bool
    else if isAnd then .mk (.ifThenElse x d (.mk (.lit (.bool false)) .bool)) .bool
    else .mk (.ifThenElse x (.mk (.lit (.bool true)) .bool) d) .bool

/-- The head of a method call other than `cast` and `declassify` on a receiver
of type `τr` with result type `τ`. -/
def methodHead (m : String) (τr τ : PyTy) : Option String :=
  match m with
  | "wrapping_add" | "wrapping_sub" | "wrapping_mul" =>
    τ.wordOf.map fun ws => m ++ "#" ++ IntWidth.tag ws.1
  | "wrapping_neg" => some "wrapping_neg#64"
  | "mulhi" => some "mulhi#64"
  | "rotate_left" | "rotate_right" => τr.wordOf.map fun ws => m ++ "#" ++ IntWidth.tag ws.1
  | "set" => some "array_update"
  | "square" | "double" => τr.fieldOf.map fun p => m ++ "#p" ++ toString p
  | _ => none

/-- The type the `int` literal arguments of method `m` on a receiver of type
`τr` take: the receiver's word type for `wrapping_*` and `mulhi`. -/
def methodArgHint (m : String) (τr : PyTy) : Option ImpType :=
  match m with
  | "wrapping_add" | "wrapping_sub" | "wrapping_mul" | "mulhi" => coerceHint τr
  | _ => none

/-- A method call: `declassify()` is its receiver, `x.cast(Uw)` is `cast#w`,
any other method its head applied to the receiver and the arguments. -/
def methodNode (p : Pos) (m : String) (τr τ : PyTy) (r : TExpr) (as : List TExpr) :
    Except String TExpr :=
  if m = "declassify" then pure r
  else if m = "cast" then
    match τ.wordOf with
    | some (w, _) => pure (.mk (.app ("cast#" ++ IntWidth.tag w) [r]) (.uint w))
    | none => errAt p "cast"
  else
    match methodHead m τr τ with
    | some h => pure (.mk (.app h (r :: as)) τ.toImp)
    | none => errAt p s!"method {m}"

/-- The type the `int` literal argument of a call of `f` takes: a word
constructor applied to a literal gives the literal the word type. -/
def ctorHint (f : String) (args : List PyExpr) : Option ImpType :=
  match wordName? f, args with
  | some w, [.const _ (.int _)] => some (.uint w)
  | _, _ => none

/-- A call of the name `f` with translated arguments `as`: a word constructor
of a literal is the literal, of an `int` expression `cast#w`; `select(c, a, b)`
is `ifThenElse c a b`; a module or linked function is applied by name. -/
def nameNode (p : Pos) (f : String) (τ : PyTy) (args : List PyExpr) (as : List TExpr) :
    Except String TExpr :=
  match wordName? f with
  | some w =>
    match args, as with
    | [.const _ (.int _)], [a] => pure a
    | [_], [a] => pure (.mk (.app ("cast#" ++ IntWidth.tag w) [a]) (.uint w))
    | _, _ => errAt p s!"constructor {f}"
  | none =>
    if f = "select" then
      match as with
      | [c, a, b] => pure (.mk (.ifThenElse c a b) τ.toImp)
      | _ => errAt p "select"
    else pure (.mk (.app f as) τ.toImp)

/-! ## Expressions -/

mutual

/-- The typed term of an expression; `hint` is the type an `int` node takes. -/
def trExpr (env : ModEnv) (Γ : Ctx) (hint : Option ImpType) : PyExpr → Except String TExpr
  | .name p x => do
      let τ ← liftR (inferExpr env Γ (.name p x))
      pure (.mk (.var x) (tyAt hint τ))
  | .const p c =>
      match c with
      | .bool b => pure (.mk (.lit (.bool b)) .bool)
      | .int n => pure (.mk (.lit (.int n)) (hint.getD (.uint .wsize)))
      | _ => errAt p "constant"
  | .binOp p l op r => do
      let τl ← liftR (inferExpr env Γ l)
      let τr ← liftR (inferExpr env Γ r)
      let τ ← liftR (inferExpr env Γ (.binOp p l op r))
      let shift := op == .lShift || op == .rShift
      let l' ← trExpr env Γ (coerceHint τr) l
      let r' ← trExpr env Γ (if shift then none else coerceHint τl) r
      match binHead op τ with
      | some f => pure (.mk (.app f [l', r']) (tyAt hint τ))
      | none => errAt p "operator"
  | .unaryOp p op e => do
      let τ ← liftR (inferExpr env Γ (.unaryOp p op e))
      let e' ← trExpr env Γ none e
      match unHead op τ with
      | some f => pure (.mk (.app f [e']) (tyAt hint τ))
      | none => errAt p "operator"
  | .boolOp p op vs => do
      let _ ← liftR (inferExpr env Γ (.boolOp p op vs))
      let vs' ← trExprs env Γ none vs
      pure (boolChain (op == .and) ((vs.map pureExpr).zip vs'))
  | .compare p l ops cs => do
      let τl ← liftR (inferExpr env Γ l)
      let τs ← liftR (inferExprs env Γ cs)
      let τ ← liftR (inferExpr env Γ (.compare p l ops cs))
      let l' ← trExpr env Γ ((τs.head?.map coerceHint).join) l
      let cs' ← trExprs env Γ (coerceHint τl) cs
      match ops.head?.bind cmpHead with
      | some f => pure (.mk (.app f (l' :: cs')) (tyAt hint τ))
      | none => errAt p "comparison"
  | .ifExp p c t e => do
      let τ ← liftR (inferExpr env Γ (.ifExp p c t e))
      let c' ← trExpr env Γ none c
      let t' ← trExpr env Γ none t
      let e' ← trExpr env Γ none e
      pure (.mk (.ifThenElse c' t' e') (tyAt hint τ))
  | .call p func args kws =>
      match kws with
      | _ :: _ => errAt p "keyword argument"
      | [] =>
        match func with
        | .attribute _ recv m => do
            let τ ← liftR (inferExpr env Γ (.call p func args []))
            let τr ← liftR (inferExpr env Γ recv)
            let r ← trExpr env Γ none recv
            let as ← if m = "cast" then pure [] else trExprs env Γ (methodArgHint m τr) args
            methodNode p m τr τ r as
        | .name _ f => do
            let τ ← liftR (inferExpr env Γ (.call p func args []))
            let as ← trExprs env Γ (ctorHint f args) args
            nameNode p f τ args as
        | _ => errAt p "callee"
  | .attribute p _ a => errAt p s!"attribute {a}"
  | .subscript p a i => do
      let τ ← liftR (inferExpr env Γ (.subscript p a i))
      let a' ← trExpr env Γ none a
      let i' ← trExpr env Γ none i
      pure (.mk (.app "index" [a', i']) (tyAt hint τ))
  | .tuple p es => do
      let τ ← liftR (inferExpr env Γ (.tuple p es))
      let es' ← trExprs env Γ none es
      pure (.mk (.tuple es') (tyAt hint τ))

/-- The typed terms of a list of expressions, each at `hint`. -/
def trExprs (env : ModEnv) (Γ : Ctx) (hint : Option ImpType) :
    List PyExpr → Except String (List TExpr)
  | [] => pure []
  | e :: es => do
      let e' ← trExpr env Γ hint e
      let es' ← trExprs env Γ hint es
      pure (e' :: es')

end

/-! ## Statements -/

/-- A step of a statement list: a binding `letBind x e`, or an effect `seq e`. -/
inductive Step where
  | bind (x : String) (e : TExpr)
  | eff (e : TExpr)

/-- The term of a step. -/
def Step.term : Step → TExpr
  | .bind _ e | .eff e => e

/-- The right-nested term of a list of steps ending in `t`; each node has the
type of `t`. -/
def assemble : List Step → TExpr → TExpr
  | [], t => t
  | .bind x e :: ss, t => let b := assemble ss t; .mk (.letBind x e b) b.ty
  | .eff e :: ss, t => let b := assemble ss t; .mk (.seq e b) b.ty

/-- The unit value. -/
def unitT : TExpr := .mk .unitVal .unit

/-- The binding of `x` to `e`: `letBind` for a name not bound in `Γ`, `assign`
otherwise. -/
def bindStep (Γ : Ctx) (x : String) (e : TExpr) : Step :=
  if (Γ.lookup x).isNone then .bind x e else .eff (.mk (.assign x e) .unit)

/-- The bindings of the names `xs` (with their types) to the projections
`j, j+1, ...` of the tuple named `tmp`. -/
def unpackSteps (Γ : Ctx) (tmp : String) (tmpTy : ImpType) :
    Nat → List (String × PyTy) → List Step
  | _, [] => []
  | j, (x, t) :: xs =>
    bindStep Γ x (.mk (.proj (.mk (.var tmp) tmpTy) j) t.toImp) ::
      unpackSteps Γ tmp tmpTy (j + 1) xs

/-- The first name `base ++ k` not in `used`. -/
def freshName (used : List String) (base : String) : String :=
  match (List.range (used.length + 1)).find? (fun k => !used.contains (base ++ toString k)) with
  | some k => base ++ toString k
  | none => base

/-- The bounds of a loop iterator `range(hi)`, `range(lo, hi)` or
`reversed(range(...))`: the lower bound (`none` for `0`), the upper bound and
whether the loop is reversed. -/
def loopRange (p : Pos) : PyExpr → Except String (Option PyExpr × PyExpr × Bool)
  | .call _ (.name _ "reversed") [.call _ (.name _ "range") [hi] []] [] => pure (none, hi, true)
  | .call _ (.name _ "reversed") [.call _ (.name _ "range") [lo, hi] []] [] =>
    pure (some lo, hi, true)
  | .call _ (.name _ "range") [hi] [] => pure (none, hi, false)
  | .call _ (.name _ "range") [lo, hi] [] => pure (some lo, hi, false)
  | _ => errAt p "loop iterator"

/-- The term of a lower loop bound; `none` is the literal `0`. -/
def trLo (env : ModEnv) (Γ : Ctx) : Option PyExpr → Except String TExpr
  | some lo => trExpr env Γ none lo
  | none => pure (.mk (.lit (.int 0)) (.uint .wsize))

mutual

/-- The steps of a statement in the context `Γ`. -/
def trStmt (env : ModEnv) (Γ : Ctx) : PyStmt → Except String (List Step)
  | .pass _ => pure []
  | .expr p v => if isDocstring v then pure [] else errAt p "expression statement"
  | .assign p targets v =>
      match targets with
      | [.name _ x] => do
          let e ← trExpr env Γ none v
          pure [bindStep Γ x e]
      | [.tuple _ elts] => do
          let τ ← liftR (inferExpr env Γ v)
          let e ← trExpr env Γ none v
          match namesOf elts, τ with
          | some xs, .tuple ts =>
            let tmp := freshName (Γ.vars.map (·.1) ++ env.consts.map (·.1) ++ xs) "_tup"
            pure (.bind tmp e :: unpackSteps Γ tmp e.ty 0 (xs.zip ts))
          | _, _ => errAt p "tuple target"
      | _ => errAt p "assignment target"
  | .annAssign p target _ val _ =>
      match target, val with
      | .name _ x, some v => do
          let e ← trExpr env Γ none v
          pure [.bind x e]
      | _, _ => errAt p "annotated assignment"
  | .forStmt p target iter body orelse =>
      match target, orelse with
      | .name _ i, [] => do
          let r ← loopRange p iter
          let lo' ← trLo env Γ r.1
          let hi' ← trExpr env Γ none r.2.1
          let bs ← trStmts env true (Γ.bindLoop i) body
          let b := assemble bs unitT
          pure [.eff (.mk (if r.2.2 then .forLoopRev i lo' hi' b else .forLoop i lo' hi' b) .unit)]
      | _, _ => errAt p "loop"
  | .ifStmt _ c body orelse => do
      let c' ← trExpr env Γ none c
      let tb ← trStmts env false Γ body
      let Γ₁ ← liftR (checkStmts env false Γ body)
      let te ← trStmts env false Γ₁ orelse
      pure [.eff (.mk (.ifThenElse c' (assemble tb unitT) (assemble te unitT)) .unit)]
  | .ret p _ => errAt p "return before the last statement"
  | .functionDef p .. => errAt p "nested definition"
  | .importFrom p .. => errAt p "import in a function"

/-- The steps of a statement list, each statement in the context the previous
ones leave. -/
def trStmts (env : ModEnv) (top : Bool) (Γ : Ctx) : List PyStmt → Except String (List Step)
  | [] => pure []
  | s :: ss => do
      let a ← trStmt env Γ s
      let Γ₁ ← liftR (checkStmt env top Γ s)
      let b ← trStmts env top Γ₁ ss
      pure (a ++ b)

end

/-! ## Functions and modules -/

/-- The parameter prelude `letBind p (var p)` of each parameter around `body`. -/
def prelude (ps : List (String × PyTy)) (body : TExpr) : TExpr :=
  ps.foldr (fun p acc => .mk (.letBind p.1 (.mk (.var p.1) p.2.toImp) acc) acc.ty) body

/-- The term of a complete body from `Γ` (`BodyOk`), as `checkBlock` reads it:
`return e` is `e`; an `if` with an arm ending in a value is `ifThenElse`
whose arms are the term of that arm and the term of the other arm followed
by the statements after the `if` (`if c: A else: (B ++ rest)`), so no
statement after it and no early exit remains; any other statement is its
steps around the term of the rest. -/
def trBlock (env : ModEnv) (pos : Pos) (Γ : Ctx) : List PyStmt → Except String TExpr
  | [] => errAt pos "no return"
  | s :: rest =>
    match s, rest with
    | .ret _ (some e), [] => trExpr env Γ none e
    | .ifStmt p c body orelse, rest =>
        if stmtsReturn body || stmtsReturn orelse then do
          let c' ← trExpr env Γ none c
          if stmtsReturn body then do
            let t ← trBlock env pos Γ body
            if stmtsReturn orelse then
              match rest with
              | [] => do
                  let e ← trBlock env pos Γ orelse
                  pure (.mk (.ifThenElse c' t e) t.ty)
              | _ :: _ => errAt p "statement after a conditional whose arms return"
            else do
              let es ← trStmts env false Γ orelse
              let Γ₁ ← liftR (checkStmts env false Γ orelse)
              let r ← trBlock env pos Γ₁ rest
              pure (.mk (.ifThenElse c' t (assemble es r)) t.ty)
          else do
            let ts ← trStmts env false Γ body
            let Γ₁ ← liftR (checkStmts env false Γ body)
            let e ← trBlock env pos Γ orelse
            let r ← trBlock env pos Γ₁ rest
            pure (.mk (.ifThenElse c' (assemble ts r) e) e.ty)
        else do
          let a ← trStmt env Γ (.ifStmt p c body orelse)
          let Γ₁ ← liftR (checkStmt env true Γ (.ifStmt p c body orelse))
          let r ← trBlock env pos Γ₁ rest
          pure (assemble a r)
    | s, rest => do
        let a ← trStmt env Γ s
        let Γ₁ ← liftR (checkStmt env true Γ s)
        let r ← trBlock env pos Γ₁ rest
        pure (assemble a r)
termination_by ss => sizeOf ss

/-- The term of a function body: the prelude around the term of the body
(`trBlock`). -/
def trFn (f : CheckedFn) : Except String TExpr := do
  let b ← trBlock f.env f.pos (Ctx.ofParams f.sig.params) f.body
  pure (prelude f.sig.params b)

/-- The terms of the functions that are not linked, in module order. -/
def trFns : List CheckedFn → Except String (List (String × TExpr))
  | [] => pure []
  | f :: fs =>
    match f.sig.linked with
    | some _ => trFns fs
    | none => do
        let t ← trFn f
        let ts ← trFns fs
        pure ((f.name, t) :: ts)

/-- The signature of a module function: its name, its parameter and result
types, whether it is an entry, and whether it is linked (with the name given
by `linked(name="...")`). -/
structure PyFnSig where
  name : String
  info : FnTypeInfo
  entry : Bool
  linked : Option (Option String)

/-- The signature of a checked function. -/
def CheckedFn.pySig (f : CheckedFn) : PyFnSig :=
  { name := f.name
    info := ⟨f.sig.params.map fun p => (p.1, p.2.toImp), f.sig.result.toImp⟩
    entry := f.sig.entry
    linked := f.sig.linked }

/-- The extraction of a checked module: the constants as literals of the
platform word, the terms of the functions that are not linked, and the
signatures of all functions, each in module order. -/
structure PyExtraction where
  consts : List (String × TExpr)
  fns : List (String × TExpr)
  sigs : List PyFnSig

/-- The translation of a checked module to typed imperative terms. -/
def pyToTExpr (cm : CheckedModule) : Except String PyExtraction := do
  let fns ← trFns cm.fns
  pure { consts := cm.env.consts.map fun c => (c.1, .mk (.lit (.int c.2)) (.uint .wsize))
         fns := fns
         sigs := cm.fns.map CheckedFn.pySig }

/-! ## The image -/

/-- The terms built from literals, variables, `letBind`, calls, tuples,
projections, `ifThenElse`, the unit value, `seq`, `assign`, `forLoop` and
`forLoopRev`. -/
inductive PyImage : ImpExpr → Prop where
  | lit {v} : PyImage (.lit v)
  | var {n} : PyImage (.var n)
  | letBind {n val body} : PyImage val → PyImage body → PyImage (.letBind n val body)
  | app {f args} : (∀ a, a ∈ args → PyImage a) → PyImage (.app f args)
  | tuple {elems} : (∀ a, a ∈ elems → PyImage a) → PyImage (.tuple elems)
  | proj {e i} : PyImage e → PyImage (.proj e i)
  | ifThenElse {c t e} : PyImage c → PyImage t → PyImage e → PyImage (.ifThenElse c t e)
  | unitVal : PyImage .unitVal
  | seq {e1 e2} : PyImage e1 → PyImage e2 → PyImage (.seq e1 e2)
  | assign {n rhs} : PyImage rhs → PyImage (.assign n rhs)
  | forLoop {v lo hi body} : PyImage lo → PyImage hi → PyImage body →
      PyImage (.forLoop v lo hi body)
  | forLoopRev {v lo hi body} : PyImage lo → PyImage hi → PyImage body →
      PyImage (.forLoopRev v lo hi body)

/-! ## The translation lies in the image -/

private theorem errAt_ne_ok {α : Type} {p : Pos} {s : String} {a : α} : errAt p s ≠ .ok a := by
  simp [errAt]

private theorem pure_ok {α : Type} {a b : α} : (pure a : Except String α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

theorem PyImage.mkApp {f : String} {args : List TExpr} {ty : ImpType}
    (h : ∀ a, a ∈ args → PyImage a.erase) : PyImage (TExpr.mk (.app f args) ty).erase := by
  simp only [TExpr.erase, TExpr.eraseList_eq]
  exact .app fun a ha => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact h b hb

theorem boolChain_pyImage (isAnd : Bool) :
    (l : List (Bool × TExpr)) → (∀ p, p ∈ l → PyImage p.2.erase) →
      PyImage (boolChain isAnd l).erase
  | [], _ => by simp only [boolChain, TExpr.erase]; exact .lit
  | [(_, x)], h => by simpa [boolChain] using h _ (List.mem_singleton_self _)
  | (b, x) :: q :: rest, h => by
      have hx : PyImage x.erase := h (b, x) (by simp)
      have hd := boolChain_pyImage isAnd (q :: rest) fun p hp => h p (by simp_all)
      simp only [boolChain]
      split
      · exact PyImage.mkApp fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl <;> assumption
      · split <;> simp only [TExpr.erase] <;> exact .ifThenElse hx (by first | exact hd | exact .lit)
          (by first | exact hd | exact .lit)

theorem methodNode_pyImage {p : Pos} {m : String} {τr τ : PyTy} {r t : TExpr}
    {as : List TExpr} (hr : PyImage r.erase) (has : ∀ a, a ∈ as → PyImage a.erase)
    (h : methodNode p m τr τ r as = .ok t) : PyImage t.erase := by
  unfold methodNode at h
  split at h
  · exact (pure_ok.mp h) ▸ hr
  · split at h
    · split at h
      · rw [← pure_ok.mp h]
        exact PyImage.mkApp fun a ha => by simp_all
      · exact absurd h errAt_ne_ok
    · split at h
      · rw [← pure_ok.mp h]
        exact PyImage.mkApp fun a ha => by
          simp only [List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact hr
          · exact has a ha
      · exact absurd h errAt_ne_ok

theorem nameNode_pyImage {p : Pos} {f : String} {τ : PyTy} {args : List PyExpr} {t : TExpr}
    {as : List TExpr} (has : ∀ a, a ∈ as → PyImage a.erase)
    (h : nameNode p f τ args as = .ok t) : PyImage t.erase := by
  unfold nameNode at h
  split at h
  · split at h
    · exact (pure_ok.mp h) ▸ has _ (by simp)
    · rw [← pure_ok.mp h]
      exact PyImage.mkApp fun a ha => by simp_all
    · exact absurd h errAt_ne_ok
  · split at h
    · split at h
      · rw [← pure_ok.mp h]
        simp only [TExpr.erase]
        exact .ifThenElse (has _ (by simp)) (has _ (by simp)) (has _ (by simp))
      · exact absurd h errAt_ne_ok
    · rw [← pure_ok.mp h]
      exact PyImage.mkApp has

mutual

/-- Every term `trExpr` returns is in `PyImage` after erasure. -/
theorem trExpr_pyImage (env : ModEnv) (Γ : Ctx) :
    (e : PyExpr) → (hint : Option ImpType) → (t : TExpr) → trExpr env Γ hint e = .ok t →
      PyImage t.erase
  | .name p x, hint, t, h => by
      simp only [trExpr, bind_eq_ok, pure_ok] at h
      obtain ⟨_, _, rfl⟩ := h
      exact .var
  | .const p c, hint, t, h => by
      simp only [trExpr] at h
      split at h
      · rw [← pure_ok.mp h]; exact .lit
      · rw [← pure_ok.mp h]; exact .lit
      · exact absurd h errAt_ne_ok
  | .binOp p l op r, hint, t, h => by
      simp only [trExpr, bind_eq_ok] at h
      obtain ⟨_, _, _, _, _, _, l', hl, r', hr, h⟩ := h
      split at h
      · rw [← pure_ok.mp h]
        exact PyImage.mkApp fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · exact trExpr_pyImage env Γ l _ _ hl
          · exact trExpr_pyImage env Γ r _ _ hr
      · exact absurd h errAt_ne_ok
  | .unaryOp p op e, hint, t, h => by
      simp only [trExpr, bind_eq_ok] at h
      obtain ⟨_, _, e', he, h⟩ := h
      split at h
      · rw [← pure_ok.mp h]
        exact PyImage.mkApp fun a ha => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          subst ha
          exact trExpr_pyImage env Γ e _ _ he
      · exact absurd h errAt_ne_ok
  | .boolOp p op vs, hint, t, h => by
      simp only [trExpr, bind_eq_ok, pure_ok] at h
      obtain ⟨_, _, vs', hvs, rfl⟩ := h
      exact boolChain_pyImage _ _ fun q hq =>
        trExprs_pyImage env Γ vs none vs' hvs _ (List.of_mem_zip hq).2
  | .compare p l ops cs, hint, t, h => by
      simp only [trExpr, bind_eq_ok] at h
      obtain ⟨_, _, _, _, _, _, l', hl, cs', hcs, h⟩ := h
      split at h
      · rw [← pure_ok.mp h]
        exact PyImage.mkApp fun a ha => by
          simp only [List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact trExpr_pyImage env Γ l _ _ hl
          · exact trExprs_pyImage env Γ cs _ cs' hcs a ha
      · exact absurd h errAt_ne_ok
  | .ifExp p c t' e, hint, t, h => by
      simp only [trExpr, bind_eq_ok, pure_ok] at h
      obtain ⟨_, _, c', hc, t'', ht, e', he, rfl⟩ := h
      simp only [TExpr.erase]
      exact .ifThenElse (trExpr_pyImage env Γ c _ _ hc) (trExpr_pyImage env Γ t' _ _ ht)
        (trExpr_pyImage env Γ e _ _ he)
  | .call p func args kws, hint, t, h => by
      match kws, func with
      | _ :: _, _ => simp only [trExpr] at h; exact absurd h errAt_ne_ok
      | [], .attribute q recv m =>
          simp only [trExpr, bind_eq_ok] at h
          obtain ⟨_, _, _, _, r, hr, h⟩ := h
          have hr' := trExpr_pyImage env Γ recv _ _ hr
          by_cases hm : m = "cast"
          · simp only [hm, if_true, pure_bind] at h
            exact methodNode_pyImage hr' (by simp) h
          · simp only [hm, if_false, bind_eq_ok] at h
            obtain ⟨as, has, h⟩ := h
            exact methodNode_pyImage hr' (trExprs_pyImage env Γ args _ as has) h
      | [], .name q f =>
          simp only [trExpr, bind_eq_ok] at h
          obtain ⟨_, _, as, has, h⟩ := h
          exact nameNode_pyImage (trExprs_pyImage env Γ args _ as has) h
      | [], .const .. | [], .binOp .. | [], .unaryOp .. | [], .boolOp .. | [], .compare ..
      | [], .ifExp .. | [], .call .. | [], .subscript .. | [], .tuple .. =>
          simp only [trExpr] at h; exact absurd h errAt_ne_ok
  | .attribute p _ a, hint, t, h => by simp only [trExpr] at h; exact absurd h errAt_ne_ok
  | .subscript p a i, hint, t, h => by
      simp only [trExpr, bind_eq_ok, pure_ok] at h
      obtain ⟨_, _, a', ha, i', hi, rfl⟩ := h
      exact PyImage.mkApp fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact trExpr_pyImage env Γ a _ _ ha
        · exact trExpr_pyImage env Γ i _ _ hi
  | .tuple p es, hint, t, h => by
      simp only [trExpr, bind_eq_ok, pure_ok] at h
      obtain ⟨_, _, es', hes, rfl⟩ := h
      simp only [TExpr.erase, TExpr.eraseList_eq]
      exact .tuple fun a ha => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact trExprs_pyImage env Γ es _ es' hes b hb

/-- Every term of the list `trExprs` returns is in `PyImage` after erasure. -/
theorem trExprs_pyImage (env : ModEnv) (Γ : Ctx) :
    (es : List PyExpr) → (hint : Option ImpType) → (ts : List TExpr) →
      trExprs env Γ hint es = .ok ts → ∀ t, t ∈ ts → PyImage t.erase
  | [], hint, ts, h => by
      simp only [trExprs, pure_ok] at h
      subst h
      simp
  | e :: es, hint, ts, h => by
      simp only [trExprs, bind_eq_ok, pure_ok] at h
      obtain ⟨e', he, es', hes, rfl⟩ := h
      intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact trExpr_pyImage env Γ e _ _ he
      · exact trExprs_pyImage env Γ es _ es' hes t ht

end

theorem assemble_pyImage :
    (ss : List Step) → (t : TExpr) → (∀ s, s ∈ ss → PyImage s.term.erase) →
      PyImage t.erase → PyImage (assemble ss t).erase
  | [], _, _, ht => ht
  | .bind x e :: ss, t, h, ht => by
      simp only [assemble, TExpr.erase]
      exact .letBind (h (.bind x e) (by simp)) (assemble_pyImage ss t (fun s hs => h s (by simp [hs])) ht)
  | .eff e :: ss, t, h, ht => by
      simp only [assemble, TExpr.erase]
      exact .seq (h (.eff e) (by simp)) (assemble_pyImage ss t (fun s hs => h s (by simp [hs])) ht)

theorem bindStep_pyImage {Γ : Ctx} {x : String} {e : TExpr} (he : PyImage e.erase) :
    PyImage (bindStep Γ x e).term.erase := by
  unfold bindStep
  split
  · exact he
  · simp only [Step.term, TExpr.erase]; exact .assign he

theorem unpackSteps_pyImage (Γ : Ctx) (tmp : String) (tmpTy : ImpType) :
    (j : Nat) → (xs : List (String × PyTy)) →
      ∀ s, s ∈ unpackSteps Γ tmp tmpTy j xs → PyImage s.term.erase
  | _, [] => by simp [unpackSteps]
  | j, (x, t) :: xs => by
      intro s hs
      simp only [unpackSteps, List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact bindStep_pyImage (by simp only [TExpr.erase]; exact .proj .var)
      · exact unpackSteps_pyImage Γ tmp tmpTy (j + 1) xs s hs

mutual

/-- Every step `trStmt` returns has a term in `PyImage` after erasure. -/
theorem trStmt_pyImage (env : ModEnv) (Γ : Ctx) :
    (st : PyStmt) → (ss : List Step) → trStmt env Γ st = .ok ss →
      ∀ s, s ∈ ss → PyImage s.term.erase
  | .pass _, ss, h => by
      simp only [trStmt, pure_ok] at h; subst h; simp
  | .expr p v, ss, h => by
      simp only [trStmt] at h
      split at h
      · rw [← pure_ok.mp h]; simp
      · exact absurd h errAt_ne_ok
  | .assign p targets v, ss, h => by
      simp only [trStmt] at h
      split at h
      · simp only [bind_eq_ok, pure_ok] at h
        obtain ⟨e, he, rfl⟩ := h
        intro s hs
        simp only [List.mem_singleton] at hs
        subst hs
        exact bindStep_pyImage (trExpr_pyImage env Γ v _ _ he)
      · simp only [bind_eq_ok] at h
        obtain ⟨_, _, e, he, h⟩ := h
        split at h
        · rw [← pure_ok.mp h]
          intro s hs
          simp only [List.mem_cons] at hs
          rcases hs with rfl | hs
          · exact trExpr_pyImage env Γ v _ _ he
          · exact unpackSteps_pyImage Γ _ _ 0 _ s hs
        · exact absurd h errAt_ne_ok
      · exact absurd h errAt_ne_ok
  | .annAssign p target ann val simple, ss, h => by
      simp only [trStmt] at h
      split at h
      · simp only [bind_eq_ok, pure_ok] at h
        obtain ⟨e, he, rfl⟩ := h
        intro s hs
        simp only [List.mem_singleton] at hs
        subst hs
        exact trExpr_pyImage env Γ _ _ _ he
      · exact absurd h errAt_ne_ok
  | .forStmt p target iter body orelse, ss, h => by
      simp only [trStmt] at h
      split at h
      · simp only [bind_eq_ok, pure_ok] at h
        obtain ⟨r, _, lo', hlo, hi', hhi, bs, hbs, rfl⟩ := h
        have hlo' : PyImage lo'.erase := by
          unfold trLo at hlo
          split at hlo
          · exact trExpr_pyImage env Γ _ _ _ hlo
          · rw [← pure_ok.mp hlo]; exact .lit
        have hb := assemble_pyImage bs unitT (trStmts_pyImage env true _ body bs hbs)
          (by simp only [unitT, TExpr.erase]; exact .unitVal)
        have hhi' := trExpr_pyImage env Γ _ _ _ hhi
        intro s hs
        simp only [List.mem_singleton] at hs
        subst hs
        cases r.2.2
        · simp only [Step.term, TExpr.erase, Bool.false_eq_true, if_false]
          exact .forLoop hlo' hhi' hb
        · simp only [Step.term, TExpr.erase, if_true]
          exact .forLoopRev hlo' hhi' hb
      · exact absurd h errAt_ne_ok
  | .ifStmt p c body orelse, ss, h => by
      simp only [trStmt, bind_eq_ok, pure_ok] at h
      obtain ⟨c', hc, tb, htb, _, _, te, hte, rfl⟩ := h
      have hu : PyImage unitT.erase := by simp only [unitT, TExpr.erase]; exact .unitVal
      intro s hs
      simp only [List.mem_singleton] at hs
      subst hs
      simp only [Step.term, TExpr.erase]
      exact .ifThenElse (trExpr_pyImage env Γ c _ _ hc)
        (assemble_pyImage tb unitT (trStmts_pyImage env false Γ body tb htb) hu)
        (assemble_pyImage te unitT (trStmts_pyImage env false _ orelse te hte) hu)
  | .ret p _, ss, h => by simp only [trStmt] at h; exact absurd h errAt_ne_ok
  | .functionDef p .., ss, h => by simp only [trStmt] at h; exact absurd h errAt_ne_ok
  | .importFrom p .., ss, h => by simp only [trStmt] at h; exact absurd h errAt_ne_ok

/-- Every step `trStmts` returns has a term in `PyImage` after erasure. -/
theorem trStmts_pyImage (env : ModEnv) (top : Bool) (Γ : Ctx) :
    (sts : List PyStmt) → (ss : List Step) → trStmts env top Γ sts = .ok ss →
      ∀ s, s ∈ ss → PyImage s.term.erase
  | [], ss, h => by simp only [trStmts, pure_ok] at h; subst h; simp
  | st :: sts, ss, h => by
      simp only [trStmts, bind_eq_ok, pure_ok] at h
      obtain ⟨a, ha, _, _, b, hb, rfl⟩ := h
      intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact trStmt_pyImage env Γ st a ha s hs
      · exact trStmts_pyImage env top _ sts b hb s hs

end

theorem prelude_pyImage (ps : List (String × PyTy)) (body : TExpr)
    (h : PyImage body.erase) : PyImage (prelude ps body).erase := by
  induction ps with
  | nil => exact h
  | cons p ps ih =>
    simp only [prelude, List.foldr_cons] at ih ⊢
    simp only [TExpr.erase]
    exact .letBind .var ih

/-- Every term `trBlock` returns is in `PyImage` after erasure. -/
theorem trBlock_pyImage (env : ModEnv) (pos : Pos) :
    (Γ : Ctx) → (ss : List PyStmt) → (t : TExpr) → trBlock env pos Γ ss = .ok t →
      PyImage t.erase
  | Γ, [], t, h => by
      rw [trBlock.eq_def] at h
      exact absurd h errAt_ne_ok
  | Γ, s :: rest, t, h => by
      rw [trBlock.eq_def] at h
      simp only at h
      split at h
      · exact trExpr_pyImage env Γ _ _ _ h
      · rename_i p c body orelse
        split at h
        · simp only [bind_eq_ok] at h
          obtain ⟨c', hc, h⟩ := h
          have hc' := trExpr_pyImage env Γ c _ _ hc
          split at h
          · simp only [bind_eq_ok] at h
            obtain ⟨tb, htb, h⟩ := h
            have htb' := trBlock_pyImage env pos Γ body tb htb
            split at h
            · split at h
              · simp only [bind_eq_ok, pure_ok] at h
                obtain ⟨te, hte, rfl⟩ := h
                simp only [TExpr.erase]
                exact .ifThenElse hc' htb' (trBlock_pyImage env pos Γ orelse te hte)
              · exact absurd h errAt_ne_ok
            · simp only [bind_eq_ok, pure_ok] at h
              obtain ⟨es, hes, Γ₁, _, r, hr, rfl⟩ := h
              simp only [TExpr.erase]
              exact .ifThenElse hc' htb' (assemble_pyImage es r
                (trStmts_pyImage env false Γ orelse es hes) (trBlock_pyImage env pos Γ₁ rest r hr))
          · simp only [bind_eq_ok, pure_ok] at h
            obtain ⟨ts, hts, Γ₁, _, te, hte, r, hr, rfl⟩ := h
            simp only [TExpr.erase]
            exact .ifThenElse hc' (assemble_pyImage ts r
              (trStmts_pyImage env false Γ body ts hts) (trBlock_pyImage env pos Γ₁ rest r hr))
              (trBlock_pyImage env pos Γ orelse te hte)
        · simp only [bind_eq_ok, pure_ok] at h
          obtain ⟨a, ha, Γ₁, _, r, hr, rfl⟩ := h
          exact assemble_pyImage a r (trStmt_pyImage env Γ _ a ha)
            (trBlock_pyImage env pos Γ₁ rest r hr)
      · simp only [bind_eq_ok, pure_ok] at h
        obtain ⟨a, ha, Γ₁, _, r, hr, rfl⟩ := h
        exact assemble_pyImage a r (trStmt_pyImage env Γ _ a ha)
          (trBlock_pyImage env pos Γ₁ _ r hr)
termination_by _ ss => sizeOf ss

theorem trFn_pyImage {f : CheckedFn} {t : TExpr} (h : trFn f = .ok t) : PyImage t.erase := by
  unfold trFn at h
  simp only [bind_eq_ok, pure_ok] at h
  obtain ⟨b, hb, rfl⟩ := h
  exact prelude_pyImage _ _ (trBlock_pyImage _ _ _ _ b hb)

theorem trFns_pyImage :
    (fs : List CheckedFn) → (ts : List (String × TExpr)) → trFns fs = .ok ts →
      ∀ p, p ∈ ts → PyImage p.2.erase
  | [], ts, h => by simp only [trFns, pure_ok] at h; subst h; simp
  | f :: fs, ts, h => by
      simp only [trFns] at h
      split at h
      · exact trFns_pyImage fs ts h
      · simp only [bind_eq_ok, pure_ok] at h
        obtain ⟨t, ht, ts', hts, rfl⟩ := h
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact trFn_pyImage ht
        · exact trFns_pyImage fs ts' hts p hp

/-- Every function term of the extraction of a checked module is in
`PyImage` after erasure. -/
theorem pyToTExpr_pyImage {cm : CheckedModule} {x : PyExtraction} (h : pyToTExpr cm = .ok x) :
    ∀ p, p ∈ x.fns → PyImage p.2.erase := by
  simp only [pyToTExpr, bind_eq_ok, pure_ok] at h
  obtain ⟨fns, hfns, rfl⟩ := h
  exact trFns_pyImage cm.fns fns hfns

end Hax.Py

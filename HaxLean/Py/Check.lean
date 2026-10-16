/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import HaxLean.Py.Types

/-!
# The checker of the Python subset

`pyCheck` decides whether a parsed Python module lies in the typed subset of
the Python front and returns either the checked module or the first
violation, as a `PyRefusal` with its kind, its position and the names
concerned.

* `inferExpr` — the syntax-directed type of an expression; deterministic, so
  the translation can re-run it to type each node.
* `checkStmt`, `checkStmts` — the context a statement (list) leaves.
* `checkBody` — a function body: statements, then one `return e`.
* `checkSig`, `checkFn` — decorators, annotations, the conditions `fnSigOk`
  on the name, the signature and the call depth, and the body of a function
  definition.
* `checkTop`, `pyCheck` — the module: a docstring, imports from `typing` and
  `catcrypt_py`, constants, field classes and function definitions, each
  checked in the environment of the statements before it. A function calls
  only functions defined before it, so the call graph is acyclic.

The body of a `linked` function is a Python reference and is not checked;
its signature is.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Py

/-- A refusal: the condition violated, the position of the node, and the
names concerned. -/
structure PyRefusal where
  kind : RefusalKind
  pos : Option Pos
  names : List String
  deriving Repr, Inhabited

/-- A refusal of kind `k` at position `p`. -/
def refuse {α : Type} (p : Pos) (k : RefusalKind) (ns : List String) : Except PyRefusal α :=
  .error ⟨k, some p, ns⟩

/-- A table result, with a refusal placed at position `p`. -/
def liftK {α : Type} (p : Pos) (ns : List String) : Except RefusalKind α → Except PyRefusal α
  | .ok a => .ok a
  | .error k => .error ⟨k, some p, ns⟩

/-! ## Expressions -/

mutual

/-- The type of an expression, or the refusal of its first node outside the
subset. -/
def inferExpr (env : ModEnv) (Γ : Ctx) : PyExpr → Except PyRefusal PyTy
  | .name p x => liftK p [x] (nameTy env Γ x)
  | .const p c => liftK p [] (constTy c)
  | .binOp p l op r => do
      let τl ← inferExpr env Γ l
      let τr ← inferExpr env Γ r
      liftK p [] (binOpTy op τl (litVal env l) τr (litVal env r))
  | .unaryOp p op e => do
      let τ ← inferExpr env Γ e
      liftK p [] (unaryTy op τ)
  | .boolOp p _ vs => do
      let τs ← inferExprs env Γ vs
      liftK p [] (boolOpTy τs)
  | .compare p l ops cs => do
      let τl ← inferExpr env Γ l
      let τs ← inferExprs env Γ cs
      liftK p [] (compareTy ops τl (litVal env l) τs (cs.map (litVal env)))
  | .ifExp p c t e => do
      let τc ← inferExpr env Γ c
      let τt ← inferExpr env Γ t
      let τe ← inferExpr env Γ e
      liftK p [] (ifExpTy τc τt τe)
  | .call p func args kws =>
      match kws with
      | _ :: _ => refuse p .keyword []
      | [] =>
        match func with
        | .attribute _ recv m => do
            let τr ← inferExpr env Γ recv
            if m = "cast" then liftK p [m] (castTy env args τr)
            else do
              let τs ← inferExprs env Γ args
              liftK p [m] (methodTy m τr τs (args.map (litVal env)))
        | .name _ f => do
            let τs ← inferExprs env Γ args
            liftK p [f] (nameCallTy env f τs (args.map (litVal env)))
        | _ => refuse p .callee []
  | .attribute p _ a => refuse p .attribute [a]
  | .subscript p a i => do
      let τa ← inferExpr env Γ a
      let τi ← inferExpr env Γ i
      liftK p [] (indexTy τa τi (litVal env i))
  | .tuple p es => do
      let τs ← inferExprs env Γ es
      liftK p [] (tupleTy τs)

/-- The types of a list of expressions. -/
def inferExprs (env : ModEnv) (Γ : Ctx) : List PyExpr → Except PyRefusal (List PyTy)
  | [] => pure []
  | e :: es => do
      let τ ← inferExpr env Γ e
      let τs ← inferExprs env Γ es
      pure (τ :: τs)

end

/-! ## Statements -/

/-- The names of assignment targets, for refusals. -/
def targetNames : List PyExpr → List String
  | [] => []
  | .name _ x :: ts => x :: targetNames ts
  | _ :: ts => targetNames ts

mutual

/-- The context a statement leaves, or its refusal; first bindings are
allowed when `top`. -/
def checkStmt (env : ModEnv) (top : Bool) (Γ : Ctx) : PyStmt → Except PyRefusal Ctx
  | .pass _ => pure Γ
  | .expr p v => if isDocstring v then pure Γ else refuse p .exprStmt []
  | .assign p targets v => do
      let τ ← inferExpr env Γ v
      liftK p (targetNames targets) (assignTy env top Γ targets v τ)
  | .annAssign p target ann val _ =>
      match val with
      | some v => do
          let τ ← inferExpr env Γ v
          liftK p (targetNames [target]) (annAssignTy env top Γ target ann τ)
      | none => refuse p .annAssignForm []
  | .forStmt p target iter body orelse => do
      let Γ₀ ← liftK p (targetNames [target]) (loopEntry env Γ target iter orelse)
      let _ ← checkStmts env true Γ₀ body
      pure Γ
  | .ifStmt p c body orelse => do
      let τ ← inferExpr env Γ c
      liftK p [] (condOk τ)
      let Γ₁ ← checkStmts env false Γ body
      checkStmts env false Γ₁ orelse
  | .ret p _ => refuse p .returnNotLast []
  | .functionDef p n .. => refuse p .nestedDef [n]
  | .importFrom p .. => refuse p .importInFunction []

/-- The context a statement list leaves, or its first refusal. -/
def checkStmts (env : ModEnv) (top : Bool) (Γ : Ctx) : List PyStmt → Except PyRefusal Ctx
  | [] => pure Γ
  | s :: ss => do
      let Γ₁ ← checkStmt env top Γ s
      checkStmts env top Γ₁ ss

end

/-- A function body with parameters `Γ₀` and result `τ`: the last statement
is `return e`, the statements before it check from `Γ₀`, and `e` has type
`τ` in the context they leave. -/
def checkBody (env : ModEnv) (Γ₀ : Ctx) (τ : PyTy) (pos : Pos) (body : List PyStmt) :
    Except PyRefusal Unit :=
  match body.getLast? with
  | some (.ret p (some e)) => do
      let Γ' ← checkStmts env true Γ₀ body.dropLast
      let τe ← inferExpr env Γ' e
      if τe = τ then pure () else refuse p .returnType []
  | _ => refuse pos .noReturn []

/-! ## Function definitions -/

/-- The decorators of a function: whether it is an entry, and whether it is
linked (with the optional name of `linked(name="...")`). -/
def checkDecorators (env : ModEnv) (pos : Pos) :
    List PyExpr → Except PyRefusal (Bool × Option (Option String))
  | [] => pure (false, none)
  | [.name q "entry"] =>
    if "entry" ∈ env.imports then pure (true, none) else refuse q .notImported ["entry"]
  | [.name q "linked"] =>
    if "linked" ∈ env.imports then pure (false, some none) else refuse q .notImported ["linked"]
  | [.call q (.name _ "linked") [] [.mk _ (some "name") (.const _ (.str s))]] =>
    if "linked" ∈ env.imports then pure (false, some (some s))
    else refuse q .notImported ["linked"]
  | [d] => refuse d.pos .decorator []
  | _ => refuse pos .decorator []

/-- The parameters of a function: annotated, with distinct names that are
neither reserved at module level nor an `anormName`. -/
def checkParams (env : ModEnv) : List PyArg → List String →
    Except PyRefusal (List (String × PyTy))
  | [], _ => pure []
  | a :: as, seen => do
      if a.name ∈ seen then refuse a.pos .duplicateParam [a.name] else
      if a.name ∈ env.reserved then refuse a.pos .shadowsName [a.name] else
      if anormName a.name then refuse a.pos .anormName [a.name] else
      match a.annotation with
      | none => refuse a.pos .missingAnnotation [a.name]
      | some ann => do
          let τ ← liftK a.pos [a.name] (parseAnn env ann)
          let rest ← checkParams env as (a.name :: seen)
          pure ((a.name, τ) :: rest)

/-- The signature of a function definition. -/
def checkSig (env : ModEnv) (pos : Pos) (name : String) (params : List PyArg)
    (decorators : List PyExpr) (returns : Option PyExpr) : Except PyRefusal FnSig := do
  if name ∈ env.defined then refuse pos .duplicateName [name] else
  let (isEntry, linked) ← checkDecorators env pos decorators
  let ps ← checkParams env params []
  match returns with
  | none => refuse pos .missingAnnotation [name]
  | some r => do
      let τ ← liftK r.pos [name] (parseAnn env r)
      pure { params := ps, result := τ, entry := isEntry, linked := linked }

/-- A function definition checked in `env`: its signature with the call depth
of its body, the conditions `fnSigOk` and, unless it is linked, its body. -/
def checkFn (env : ModEnv) (pos : Pos) (name : String) (params : List PyArg)
    (body : List PyStmt) (decorators : List PyExpr) (returns : Option PyExpr) :
    Except PyRefusal CheckedFn := do
  let sig₀ ← checkSig env pos name params decorators returns
  let sig := { sig₀ with depth := stmtsDepth env body }
  liftK pos [name] (fnSigOk name sig)
  if sig.linked.isNone then checkBody env (Ctx.ofParams sig.params) sig.result pos body
  pure { name := name, pos := pos, sig := sig, env := env, body := body }

/-! ## Modules -/

/-- An imported name among `allowed`, without `as`. -/
def addImport (allowed : List String) (env : ModEnv) (a : PyAlias) : Except PyRefusal ModEnv :=
  if a.asname.isSome then refuse a.pos .importAlias [a.name]
  else if a.name ∉ allowed then refuse a.pos .importName [a.name]
  else if a.name ∈ env.imports then pure env
  else if a.name ∈ env.defined then refuse a.pos .duplicateName [a.name]
  else pure { env with imports := env.imports ++ [a.name] }

/-- `from typing import Final` or `from catcrypt_py import ...`. -/
def checkImport (env : ModEnv) (p : Pos) (m : Option String) (names : List PyAlias)
    (level : Nat) : Except PyRefusal ModEnv :=
  if level ≠ 0 then refuse p .importModule [] else
  match m with
  | some "typing" => names.foldlM (addImport ["Final"]) env
  | some "catcrypt_py" => names.foldlM (addImport catcryptNames) env
  | some x => refuse p .importModule [x]
  | none => refuse p .importModule []

/-- A module constant `N: Final = n` with `0 ≤ n < 2^64`. -/
def checkConst (env : ModEnv) (target ann : PyExpr) (val : Option PyExpr) :
    Except RefusalKind ModEnv :=
  match target, ann, val with
  | .name _ x, .name _ "Final", some (.const _ (.int n)) =>
    if "Final" ∉ env.imports then .error .notImported
    else if n < 0 then .error .constantValue
    else if 2 ^ 64 ≤ n then .error .intLiteral
    else if x ∈ env.defined then .error .duplicateName
    else .ok { env with consts := env.consts ++ [(x, n.toNat)] }
  | _, _, _ => .error .moduleStmt

/-- A field class `F = field(p)` with `1 < p < 2^64`. -/
def checkFieldDef (env : ModEnv) (targets : List PyExpr) (v : PyExpr) :
    Except RefusalKind ModEnv :=
  match targets, v with
  | [.name _ x], .call _ (.name _ "field") [.const _ (.int p)] [] =>
    if "field" ∉ env.imports then .error .notImported
    else if !(decide (1 < p) && decide (p < 2 ^ 64)) then .error .fieldModulus
    else if x ∈ env.defined then .error .duplicateName
    else .ok { env with fields := env.fields ++ [(x, p.toNat)] }
  | _, _ => .error .moduleStmt

/-- A module-level statement, checked in the environment and with the
functions of the statements before it. -/
def checkTopStmt (st : ModEnv × List CheckedFn) : PyStmt →
    Except PyRefusal (ModEnv × List CheckedFn)
  | .importFrom p m names level => do
      let env ← checkImport st.1 p m names level
      pure (env, st.2)
  | .annAssign p target ann val _ => do
      let env ← liftK p (targetNames [target]) (checkConst st.1 target ann val)
      pure (env, st.2)
  | .assign p targets v => do
      let env ← liftK p (targetNames targets) (checkFieldDef st.1 targets v)
      pure (env, st.2)
  | .functionDef p name params body decorators returns => do
      let f ← checkFn st.1 p name params body decorators returns
      pure ({ st.1 with fns := st.1.fns ++ [(name, f.sig)] }, st.2 ++ [f])
  | s => refuse s.pos .moduleStmt []

/-- The module-level statements, from left to right. -/
def checkTop : ModEnv × List CheckedFn → List PyStmt →
    Except PyRefusal (ModEnv × List CheckedFn)
  | st, [] => pure st
  | st, s :: ss => do
      let st' ← checkTopStmt st s
      checkTop st' ss

/-- The names bound at module level: imported names, constants, field
classes and functions. -/
def moduleNames : List PyStmt → List String
  | [] => []
  | .importFrom _ _ names _ :: ss => names.map (fun a => a.asname.getD a.name) ++ moduleNames ss
  | .annAssign _ (.name _ x) _ _ _ :: ss => x :: moduleNames ss
  | .assign _ targets _ :: ss => targetNames targets ++ moduleNames ss
  | .functionDef _ n .. :: ss => n :: moduleNames ss
  | _ :: ss => moduleNames ss

/-- The names no local may bind: `range`, `reversed`, and the module-level
names. -/
def reservedNames (body : List PyStmt) : List String :=
  "range" :: "reversed" :: moduleNames body

/-- The checker of the Python subset: a module docstring, then module-level
statements each checked in the environment of those before it. -/
def pyCheck (m : PyModule) : Except PyRefusal CheckedModule :=
  match m.body with
  | .expr _ v :: rest =>
    if isDocstring v then do
      let env₀ : ModEnv :=
        { imports := [], consts := [], fields := [], fns := [], reserved := reservedNames rest }
      let st ← checkTop (env₀, []) rest
      pure { env := st.1, fns := st.2 }
    else .error ⟨.noDocstring, some v.pos, []⟩
  | s :: _ => .error ⟨.noDocstring, some s.pos, []⟩
  | [] => .error ⟨.noDocstring, none, []⟩

end Hax.Py

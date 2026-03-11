/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.AST
import SSProve.Hax.ImpType

/-!
# Lean 4 Pretty-Printer for ImpExpr

Emits Lean 4 source code from post-pipeline `ImpExpr`.

Assumes a runtime library providing `Hax.forFold`, `Hax.whileFold`, etc.
The output can be compiled by Lean 4 given appropriate imports.

**Not imported by the proof library** — only used by the executable.
-/

namespace SSProve.Hax

/-- Indent by `n` levels (2 spaces each). -/
private def indent (n : Nat) : String :=
  String.ofList (List.replicate (2 * n) ' ')

/-- Sanitize a name for Lean 4: wrap in French quotes if needed. -/
private def sanitizeName (n : String) : String :=
  -- Lean keywords and names with special chars need quoting
  if n.isEmpty then "«»"
  else if n.any fun c => !c.isAlphanum && c != '_' && c != '\'' then s!"«{n}»"
  else
    match n with
    | "if" | "then" | "else" | "let" | "do" | "match" | "with" | "where"
    | "fun" | "return" | "for" | "in" | "while" | "break" | "continue"
    | "true" | "false" | "def" | "theorem" | "import" | "open" | "namespace"
    | "end" | "structure" | "inductive" | "class" | "instance" | "section"
    | "variable" | "axiom" | "by" | "have" | "show" | "sorry" | "Type"
    | "Prop" | "Sort" | "Set" | "mutual" | "noncomputable" | "private"
    | "protected" | "partial" | "unsafe" => s!"«{n}»"
    | _ => n

/-- Map builtin function names to qualified Lean 4 identifiers.
    Known builtins get `Hax.` prefix; constructors map to Lean equivalents. -/
private def runtimeName (f : String) : String :=
  match f with
  -- Arithmetic
  | "add" | "sub" | "mul" | "div" | "rem" | "neg" => s!"Hax.{f}"
  | "Add" | "Sub" | "Mul" | "Div" | "Rem" | "Neg" => s!"Hax.{f}"
  -- Comparison (eq/ne/not/and/or → prefixed names to avoid shadowing)
  | "eq" => "Hax.beq"
  | "ne" => "Hax.bne"
  | "not" => "Hax.bnot"
  | "and" => "Hax.band"
  | "or" => "Hax.bor"
  | "Eq" => "Hax.Eq"
  | "Ne" => "Hax.Ne"
  | "Not" => "Hax.Not"
  | "And" => "Hax.And"
  | "Or" => "Hax.Or"
  | "lt" | "le" | "gt" | "ge" => s!"Hax.{f}"
  | "Lt" | "Le" | "Gt" | "Ge" => s!"Hax.{f}"
  -- Bitwise
  | "shl" | "shr" | "bitand" | "bitor" | "bitxor" | "bitnot" => s!"Hax.{f}"
  | "Shl" | "Shr" | "BitAnd" | "BitOr" | "BitXor" => s!"Hax.{f}"
  -- Indexing
  | "index" => "Hax.index"
  -- Logical operators (from LogicalOp in hax AST)
  | "&&" => "Hax.band"
  | "||" => "Hax.bor"
  -- Option/Result constructors → Lean equivalents
  | "Some" => "some"
  | "None" => "none"
  | "Ok" => "Except.ok"
  | "Err" => "Except.error"
  -- Everything else: sanitize and pass through
  | _ => sanitizeName f

/-- Map an operator name and result type to a width-specific runtime function.
    Falls back to `runtimeName` when the type is not a fixed-width integer. -/
private def runtimeNameTyped (f : String) (ty : ImpType) : String :=
  match ty.intWidth? with
  | some w =>
    let suffix := if ty.isSigned then w.toSignedSuffix else w.toSuffix
    match f with
    -- Arithmetic
    | "Add" | "add" => s!"Hax.add_{suffix}"
    | "Sub" | "sub" => s!"Hax.sub_{suffix}"
    | "Mul" | "mul" => s!"Hax.mul_{suffix}"
    | "Div" | "div" => s!"Hax.div_{suffix}"
    | "Rem" | "rem" => s!"Hax.rem_{suffix}"
    | "Neg" | "neg" => s!"Hax.neg_{suffix}"
    -- Bitwise (only for unsigned; signed falls through to untyped)
    | "Shl" | "shl" => if ty.isSigned then runtimeName f else s!"Hax.shl_{suffix}"
    | "Shr" | "shr" => if ty.isSigned then runtimeName f else s!"Hax.shr_{suffix}"
    | "BitAnd" | "bitand" => if ty.isSigned then runtimeName f else s!"Hax.bitand_{suffix}"
    | "BitOr"  | "bitor"  => if ty.isSigned then runtimeName f else s!"Hax.bitor_{suffix}"
    | "BitXor" | "bitxor" => if ty.isSigned then runtimeName f else s!"Hax.bitxor_{suffix}"
    | "Not"    | "not"    => if ty.isSigned then runtimeName f else s!"Hax.bitnot_{suffix}"
    -- Comparison
    | "Eq" | "eq" => s!"Hax.eq_{suffix}"
    | "Ne" | "ne" => s!"Hax.ne_{suffix}"
    | "Lt" | "lt" => s!"Hax.lt_{suffix}"
    | "Le" | "le" => s!"Hax.le_{suffix}"
    | "Gt" | "gt" => s!"Hax.gt_{suffix}"
    | "Ge" | "ge" => s!"Hax.ge_{suffix}"
    -- Everything else: fall through to untyped
    | _ => runtimeName f
  | none => runtimeName f

/-- Select the cast function name based on source and target types. -/
private def castFnName (srcTy dstTy : ImpType) : String :=
  match srcTy.intWidth?, dstTy.intWidth? with
  | some sw, some dw =>
    let srcSuffix := if srcTy.isSigned then sw.toSignedSuffix else sw.toSuffix
    let dstSuffix := if dstTy.isSigned then dw.toSignedSuffix else dw.toSuffix
    if srcSuffix == dstSuffix then "id"
    else s!"Hax.cast_{srcSuffix}_{dstSuffix}"
  | _, _ => "id"  -- non-integer cast: identity

/-- Format an integer literal with a type annotation when the type is known. -/
private def litIntTyped (n : Int) (ty : ImpType) : String :=
  let numStr := if n < 0 then s!"({n})" else toString n
  match ty with
  | .uint w => s!"({numStr} : {w.toLeanType})"
  | .sint _ => s!"({numStr} : Int)"
  | _ => numStr

/-- Pretty-print a pattern. -/
private def patToLean : ImpPat → String
  | .wildcard => "_"
  | .litPat (.bool true) => "true"
  | .litPat (.bool false) => "false"
  | .litPat (.int n) => toString n
  | .litPat .unit => "()"
  | .litPat (.uintLit w n) => s!"({n} : {w.toLeanType})"
  | .litPat (.sintLit _ n) => s!"({n} : Int)"
  | .varPat n => sanitizeName n
  | .tuplePat ps => s!"({", ".intercalate (ps.map patToLean)})"
  | .somePat p => s!"some ({patToLean p})"
  | .nonePat => "none"
  | .okPat p => s!"Except.ok ({patToLean p})"
  | .errPat p => s!"Except.error ({patToLean p})"

/-- Is this expression simple enough to not need parentheses as an argument? -/
private def isAtom : ImpExpr → Bool
  | .lit _ | .var _ | .unitVal => true
  | .tuple _ => true  -- tuples have their own parens
  | _ => false

/-- Wrap in parentheses if needed. -/
private def parensIf (s : String) (needParens : Bool) : String :=
  if needParens then s!"({s})" else s

/-- Pretty-print an ImpExpr as Lean 4 source code.
    `lvl` is the current indentation level. -/
partial def toLean (e : ImpExpr) (lvl : Nat := 0) : String :=
  let ind := indent lvl
  let ind1 := indent (lvl + 1)
  match e with
  -- Literals
  | .lit (.bool true) => "true"
  | .lit (.bool false) => "false"
  | .lit (.int n) => if n < 0 then s!"({n})" else toString n
  | .lit .unit => "()"
  | .lit (.uintLit w n) => s!"({n} : {w.toLeanType})"
  | .lit (.sintLit _ n) =>
    let numStr := if n < 0 then s!"({n})" else toString n
    s!"({numStr} : Int)"
  | .unitVal => "()"

  -- Variables
  | .var n => sanitizeName n

  -- Let binding (multi-line)
  | .letBind n val body =>
    s!"{ind}let {sanitizeName n} := {toLean val 0}\n{toLean body lvl}"

  -- Function application
  | .app f args =>
    let fname := runtimeName f
    if args.isEmpty then fname
    else
      let argStrs := args.map fun a => parensIf (toLean a 0) (!isAtom a)
      s!"{fname} {" ".intercalate argStrs}"

  -- Tuple
  | .tuple elems =>
    s!"({", ".intercalate (elems.map fun e => toLean e 0)})"

  -- Projection
  | .proj e i =>
    s!"{parensIf (toLean e 0) (!isAtom e)}.{i}"

  -- Conditional
  | .ifThenElse c t e =>
    s!"{ind}if {toLean c 0} then\n{ind1}{toLean t (lvl + 1)}\n{ind}else\n{ind1}{toLean e (lvl + 1)}"

  -- Pattern match
  | .match_ scrut arms =>
    let armStrs := arms.map fun (p, body) =>
      s!"{ind}| {patToLean p} => {toLean body (lvl + 1)}"
    s!"{ind}match {toLean scrut 0} with\n{"\n".intercalate armStrs}"

  -- Sequence: flatten and emit as let-chain
  | .seq e1 e2 => seqToLean lvl e1 e2

  -- ControlFlow constructors (post-pipeline)
  | .cfBreak e =>
    s!"ControlFlow.Break {parensIf (toLean e 0) (!isAtom e)}"
  | .cfContinue e =>
    s!"ControlFlow.Continue {parensIf (toLean e 0) (!isAtom e)}"
  | .cfBreakContinue e =>
    s!"ControlFlow.Break (ControlFlow.Continue {parensIf (toLean e 0) (!isAtom e)})"

  -- Fold operations (post-pipeline)
  | .forFold v lo hi body =>
    s!"{ind}Hax.forFold {parensIf (toLean lo 0) (!isAtom lo)} {parensIf (toLean hi 0) (!isAtom hi)} () fun {sanitizeName v} _acc =>\n{ind1}{toLean body (lvl + 1)}"
  | .forFoldRev v lo hi body =>
    s!"{ind}Hax.forFoldRev {parensIf (toLean lo 0) (!isAtom lo)} {parensIf (toLean hi 0) (!isAtom hi)} () fun {sanitizeName v} _acc =>\n{ind1}{toLean body (lvl + 1)}"
  | .whileFold c body =>
    s!"{ind}Hax.whileFold () (fun _acc => {toLean c 0}) fun _acc =>\n{ind1}{toLean body (lvl + 1)}"
  | .forFoldReturn v lo hi body =>
    s!"{ind}Hax.forFoldReturn {parensIf (toLean lo 0) (!isAtom lo)} {parensIf (toLean hi 0) (!isAtom hi)} () fun {sanitizeName v} _acc =>\n{ind1}{toLean body (lvl + 1)}"
  | .forFoldRevReturn v lo hi body =>
    s!"{ind}Hax.forFoldRevReturn {parensIf (toLean lo 0) (!isAtom lo)} {parensIf (toLean hi 0) (!isAtom hi)} () fun {sanitizeName v} _acc =>\n{ind1}{toLean body (lvl + 1)}"
  | .whileFoldReturn c body =>
    s!"{ind}Hax.whileFoldReturn () (fun _acc => {toLean c 0}) fun _acc =>\n{ind1}{toLean body (lvl + 1)}"

  -- Pre-pipeline constructors (should not appear in output, but handle gracefully)
  | .borrow e => s!"(& {toLean e 0})"
  | .deref e => s!"(* {toLean e 0})"
  | .assign n rhs => s!"{sanitizeName n} := {toLean rhs 0}"
  | .forLoop v lo hi body =>
    s!"{ind}for {sanitizeName v} in {toLean lo 0} .. {toLean hi 0} do\n{ind1}{toLean body (lvl + 1)}"
  | .forLoopRev v lo hi body =>
    s!"{ind}for {sanitizeName v} in ({toLean lo 0} .. {toLean hi 0}).rev() do\n{ind1}{toLean body (lvl + 1)}"
  | .whileLoop c body =>
    s!"{ind}while {toLean c 0} do\n{ind1}{toLean body (lvl + 1)}"
  | .break_ none => "break"
  | .break_ (some e) => s!"break {toLean e 0}"
  | .continue_ => "continue"
  | .earlyReturn e => s!"return {toLean e 0}"
  | .questionMark e => s!"{parensIf (toLean e 0) (!isAtom e)}?"
where
  /-- Flatten seq chains into proper let-bindings. -/
  seqToLean (lvl : Nat) (e1 e2 : ImpExpr) : String :=
    let ind := indent lvl
    match e1, e2 with
    -- Skip unitVal in either position
    | .unitVal, _ => toLean e2 lvl
    | _, .unitVal => toLean e1 lvl
    -- Flatten left-nested seq: seq (seq a b) c → seq a (seq b c)
    | .seq a b, _ => seqToLean lvl a (.seq b e2)
    -- Lift letBind out of seq: seq (letBind n v body) e2 → let n := v; seq body e2
    | .letBind n v body, _ =>
      s!"{ind}let {sanitizeName n} := {toLean v 0}\n{seqToLean lvl body e2}"
    -- General case: discard e1's value
    | _, _ => s!"{ind}let _ := {toLean e1 0}\n{toLean e2 lvl}"

/-- Wrap the output in a Lean 4 definition. -/
def toLeanDef (name : String) (e : ImpExpr) : String :=
  let body := toLean e 1
  s!"def {sanitizeName name} :=\n{body}\n"

/-- Generate a complete Lean 4 file from pipeline output. -/
def toLeanFile (defs : List (String × ImpExpr))
    (moduleName : String := "Generated") : String :=
  let header := s!"/-\n  Auto-generated by haxpipe (verified hax pipeline)\n-/\nimport SSProve.Hax.Runtime\n\nnamespace {moduleName}\n\n"
  let body := "\n".intercalate (defs.map fun (n, e) => toLeanDef n e)
  let footer := s!"\nend {moduleName}\n"
  header ++ body ++ footer

/-! ## HaxBridge Template Generation

Generate SSProve HaxBridge boilerplate from extracted function names.

Two extraction paths are supported:
- **lean-refines** (pure): extracted functions go directly into Dependencies
- **hax** (RustM): need purity proofs, then extract into Dependencies

The template generates the direct Dependencies pattern. -/

/-- Generate a HaxBridge template for a protocol with given function names. -/
def toHaxBridgeTemplate (protocolName : String)
    (fnNames : List String) : String :=
  let sanitized := fnNames.map sanitizeName
  let ucModuleName := protocolName.replace "/" "."
  -- Direct Dependencies fields (pure functions from extraction)
  let depsFields := sanitized.map fun n =>
    s!"  {n} := {protocolName.toLower}_{n}  -- from extraction"
  s!"/-
Copyright (c) 2026 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Crypto.{ucModuleName}.Security
-- import SSProve.Crypto.{ucModuleName}.Extraction.{protocolName}_hax

/-!
# {protocolName} — Hax Bridge

Connects extracted implementation to the UC security proof.

## Architecture

Extracted pure functions plug directly into the Dependencies typeclass.
No intermediate PureCrypto record or RustM wrapping needed.
-/

set_option autoImplicit false

open SSProve.Core SSProve.Prob SSProve.Crypto
open scoped ENNReal

namespace {ucModuleName}

/-! ## Dependencies Instance -/

-- TODO: fill in from extraction (lean-refines or hax with purity proofs)
-- noncomputable instance concreteDeps :
--     {protocolName}Dependencies {protocolName}Witness where
--   keygen := ...  -- SPComp (randomness)
{"\n".intercalate depsFields}

/-! ## UC Security -/

-- TODO: instantiate the parametric UC theorem with concreteDeps
-- theorem {protocolName.toLower}_concrete_uc :
--     UCEmulates ... := {protocolName.toLower}_uc_secure ...

end {ucModuleName}
"

end SSProve.Hax

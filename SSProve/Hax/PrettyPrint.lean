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
    | "protected" | "partial" | "unsafe" | "prefix" | "hiding"
    | "macro" | "syntax" | "tactic" | "notation" | "scoped"
    | "deriving" | "extends" | "abbrev" | "opaque" | "at"
    | "eq" | "ne" | "lt" | "le" | "gt" | "ge" | "mod" | "not" | "or" | "and" => s!"«{n}»"
    | _ => n

/-- Map builtin function names to qualified Lean 4 identifiers.
    Known builtins get `Hax.` prefix; constructors map to Lean equivalents. -/
private def runtimeName (f : String) : String :=
  match f with
  -- Arithmetic (lowercase: Int-specific; capitalized: map to lowercase for untyped)
  | "add" | "sub" | "mul" | "div" | "rem" | "neg" => s!"Hax.{f}"
  | "Add" => "Hax.add" | "Sub" => "Hax.sub" | "Mul" => "Hax.mul"
  | "Div" => "Hax.div" | "Rem" => "Hax.rem" | "Neg" => "Hax.neg"
  -- Comparison (eq/ne/not/and/or → prefixed names to avoid shadowing)
  | "eq" | "Eq" => "Hax.beq"
  | "ne" | "Ne" => "Hax.bne"
  | "not" => "Hax.bnot"
  | "Not" => "Hax.bitnot"  -- Rust `!` on integers is bitwise complement
  | "and" | "And" => "Hax.band"
  | "or"  | "Or"  => "Hax.bor"
  | "lt" | "le" | "gt" | "ge" => s!"Hax.{f}"
  | "Lt" => "Hax.lt" | "Le" => "Hax.le"
  | "Gt" => "Hax.gt" | "Ge" => "Hax.ge"
  -- Bitwise (capitalized → lowercase Int versions for untyped path)
  | "shl" | "shr" | "bitand" | "bitor" | "bitxor" | "bitnot" => s!"Hax.{f}"
  | "Shl" => "Hax.shl" | "Shr" => "Hax.shr"
  | "BitAnd" => "Hax.bitand" | "BitOr" => "Hax.bitor" | "BitXor" => "Hax.bitxor"
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
  -- Collection operations
  | "array_lit" => "Hax.array_lit"
  | "repeat" => "Hax.repeat_"
  | "push" => "Hax.push"
  | "len" => "Hax.array_len"
  | "rotate_right" => "Hax.rotate_right"
  | "rotate_left" => "Hax.rotate_left"
  | "wrapping_add" => "Hax.wrapping_add"
  | "wrapping_sub" => "Hax.wrapping_sub"
  | "wrapping_mul" => "Hax.wrapping_mul"
  | "array_update" => "Hax.array_update"
  -- Cast (untyped fallback — typed path uses width-specific casts)
  | "cast" => "Hax.castVal"
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
    -- Wrapping arithmetic (Rust methods → same as regular width ops)
    | "wrapping_add" => s!"Hax.wrapping_add_{suffix}"
    | "wrapping_sub" => s!"Hax.wrapping_sub_{suffix}"
    | "wrapping_mul" => s!"Hax.wrapping_mul_{suffix}"
    -- Rotate
    | "rotate_left" => s!"Hax.rotate_left_{suffix}"
    | "rotate_right" => s!"Hax.rotate_right_{suffix}"
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

/-- Detect tuple destructuring pattern in letBind body.
    Pattern: letBind "a" (proj (var tmpName) 0) (letBind "b" (proj (var tmpName) 1) rest)
    Returns (field names, remaining body) or none. -/
private def extractTupleDestr (tmpName : String) : ImpExpr → Option (List String × ImpExpr)
  | .letBind n (.proj (.var v) _) rest =>
    if v == tmpName then
      match extractTupleDestr tmpName rest with
      | some (names, body) => some (n :: names, body)
      | none => some ([n], rest)
    else none
  | _ => none

/-- Check if an expression contains ControlFlow nodes (cfBreak/cfContinue/cfBreakContinue). -/
private partial def hasControlFlowNodes : ImpExpr → Bool
  | .cfBreak _ | .cfContinue _ | .cfBreakContinue _ => true
  | .letBind _ v b => hasControlFlowNodes v || hasControlFlowNodes b
  | .seq e1 e2 => hasControlFlowNodes e1 || hasControlFlowNodes e2
  | .ifThenElse c t e => hasControlFlowNodes c || hasControlFlowNodes t || hasControlFlowNodes e
  | .match_ _ arms => arms.any fun (_, b) => hasControlFlowNodes b
  | .app _ args => args.any hasControlFlowNodes
  | .tuple elems => elems.any hasControlFlowNodes
  | _ => false

/-- Extract mutation variable names and their RHS from a conditional then-branch.
    Returns list of (name, rhs) for patterns like `seq (letBind n rhs (var n)) rest`. -/
private partial def extractCondMutations : ImpExpr → List (String × ImpExpr)
  | .seq (.seq a b) c => extractCondMutations (.seq a (.seq b c))
  | .seq (.letBind n rhs (.var v)) rest =>
    if n == v then (n, rhs) :: extractCondMutations rest
    else extractCondMutations rest
  | .seq .unitVal rest => extractCondMutations rest
  | .seq _ rest => extractCondMutations rest
  | .letBind n rhs (.var v) => if n == v then [(n, rhs)] else []
  -- Recurse into non-mutation letBind (local variables before mutations)
  | .letBind _ _ body => extractCondMutations body
  | .unitVal => []
  | _ => []

/-- Extract accumulator variable names from a fold body.
    Looks for the localMutation pattern: `seq (letBind n rhs (var n)) rest`
    which came from `assign n rhs`. Returns unique names in order.
    Also looks inside `ifThenElse` branches for conditional mutations. -/
private partial def extractAccumulators : ImpExpr → List String
  | .seq (.seq a b) c => extractAccumulators (.seq a (.seq b c))
  | .seq (.letBind n _ (.var v)) rest =>
    if n == v then
      let restAccs := extractAccumulators rest
      if restAccs.contains n then restAccs else n :: restAccs
    else extractAccumulators rest
  -- Look inside conditional mutations for hidden accumulators
  | .seq (.ifThenElse _ thn _) rest =>
    let thnAccs := extractCondMutations thn |>.map (·.1)
    let restAccs := extractAccumulators rest
    let all := thnAccs ++ restAccs
    all.eraseDups
  | .seq _ rest => extractAccumulators rest
  | .letBind n _ (.var v) => if n == v then [n] else []
  -- Recurse into local let-bindings (non-mutation letBind)
  | .letBind _ _ body => extractAccumulators body
  -- Top-level ifThenElse (entire fold body is a conditional)
  | .ifThenElse _ thn _ =>
    let thnAccs := extractCondMutations thn |>.map (·.1)
    thnAccs.eraseDups
  | _ => []

/-- Transform a forFold body for accumulator-based rendering.
    Converts env-based mutation patterns to let-chain with accumulator return.

    Input (localMutation output):
      `seq (letBind "state" rhs (var "state")) unitVal`
    Output:
      `letBind "state" rhs (var "state")` -/
private partial def transformFoldBody (accs : List String) : ImpExpr → ImpExpr
  -- Flatten nested seq
  | .seq (.seq a b) c => transformFoldBody accs (.seq a (.seq b c))
  -- Mutation pattern: seq (letBind n rhs (var n)) rest → letBind n rhs (transform rest)
  | .seq (.letBind n val (.var v)) rest =>
    if n == v then .letBind n val (transformFoldBody accs rest)
    else .seq (.letBind n val (.var v)) (transformFoldBody accs rest)
  -- Conditional mutation: seq (ifThenElse cond thn unitVal) rest
  -- → letBind mutated vars with conditional values, then transform rest
  | .seq (.ifThenElse cond thn .unitVal) rest =>
    let muts := extractCondMutations thn
    if muts.isEmpty then
      .seq (.ifThenElse cond thn .unitVal) (transformFoldBody accs rest)
    else
      -- Build: let v1 := if cond then rhs1 else v1; let v2 := ...
      let body := transformFoldBody accs rest
      muts.foldr (fun (n, rhs) acc => .letBind n (.ifThenElse cond rhs (.var n)) acc) body
  -- Skip unitVal in seq
  | .seq .unitVal rest => transformFoldBody accs rest
  -- General seq: keep e1, transform rest
  | .seq e1 rest => .seq e1 (transformFoldBody accs rest)
  -- Non-mutation letBind: local variable, recurse into body
  | .letBind n val body => .letBind n val (transformFoldBody accs body)
  -- Top-level ifThenElse: entire fold body is a conditional
  -- Transform: if cond then <body-with-mutations> else <unchanged-accums>
  | .ifThenElse cond thn els =>
    let accReturn := match accs with
      | [a] => ImpExpr.var a
      | _ => .tuple (accs.map .var)
    let thn' := transformFoldBody accs thn
    let els' := if els == .unitVal then accReturn else transformFoldBody accs els
    .ifThenElse cond thn' els'
  -- Terminal: unitVal → accumulator return
  | .unitVal =>
    match accs with
    | [a] => .var a
    | _ => .tuple (accs.map .var)
  -- Terminal: var that's an accumulator → full accumulator return tuple
  | .var n =>
    if accs.contains n then
      match accs with
      | [a] => .var a
      | _ => .tuple (accs.map .var)
    else .var n
  -- Other terminal: leave as-is
  | e => e

/-- Simplify a fold body by removing trivial let-return patterns.
    `letBind n rhs (var n)` → `rhs` when `n` is the only accumulator.
    This avoids indentation issues with bare return values. -/
private def simplifyFoldBody : ImpExpr → ImpExpr
  | .letBind n val (.var v) => if n == v then val else .letBind n val (.var v)
  | e => e

/-- Format accumulator initial value and lambda parameter for fold rendering. -/
private def accStrings (accs : List String) : String × String :=
  if accs.isEmpty then ("()", "_acc")
  else if accs.length == 1 then
    let name := sanitizeName accs.head!
    (name, name)
  else
    let names := ", ".intercalate (accs.map sanitizeName)
    (s!"({names})", s!"({names})")

/-- Extract accumulators from a whileFold body.
    The body may be wrapped in an `ifThenElse` (from `while true { if cond ... else break }`),
    so we look inside the `thn` branch for mutation patterns.
    Also skips non-mutation `letBind` wrappers (e.g., `let block := ...`). -/
private partial def extractWhileAccumulators : ImpExpr → List String
  | .ifThenElse _ thn _ => extractWhileAccumulators thn
  | .letBind n _ (.var v) => if n == v then
      -- Mutation pattern at top level
      [n]
    else []
  | .letBind _ _ body => extractWhileAccumulators body
  | .seq (.seq a b) c => extractWhileAccumulators (.seq a (.seq b c))
  | e => extractAccumulators e

/-- Make an accumulator tuple expression from a list of variable names. -/
private def accTuple (accs : List String) : ImpExpr :=
  match accs with
  | [a] => .var a
  | _ => .tuple (accs.map .var)

/-- Transform the continue branch of a whileFold body.
    Same as `transformFoldBody` but wraps the final value in `cfContinue`. -/
private partial def transformWhileContinue (accs : List String) : ImpExpr → ImpExpr
  | .seq (.seq a b) c => transformWhileContinue accs (.seq a (.seq b c))
  | .seq (.letBind n val (.var v)) rest =>
    if n == v then .letBind n val (transformWhileContinue accs rest)
    else .seq (.letBind n val (.var v)) (transformWhileContinue accs rest)
  | .seq .unitVal rest => transformWhileContinue accs rest
  | .seq e1 rest => .seq e1 (transformWhileContinue accs rest)
  | .letBind n val body => .letBind n val (transformWhileContinue accs body)
  | .unitVal => .cfContinue (accTuple accs)
  | e => e

/-- Transform the break branch of a whileFold body.
    Replaces `cfBreak unitVal` with `cfBreak (accs)` so the break value
    carries the current accumulator state. -/
private partial def transformWhileBreak (accs : List String) : ImpExpr → ImpExpr
  | .cfBreak _ => .cfBreak (accTuple accs)
  | .seq e1 e2 => .seq (transformWhileBreak accs e1) (transformWhileBreak accs e2)
  | .ifThenElse c t e =>
    .ifThenElse c (transformWhileBreak accs t) (transformWhileBreak accs e)
  | e => e

/-- Transform a whileFold body for surface rendering.
    - In continue branches: replace trailing `unitVal` with `cfContinue (accs)`
    - In break branches: replace `cfBreak unitVal` with `cfBreak (accs)` -/
private partial def transformWhileFoldBody (accs : List String) : ImpExpr → ImpExpr
  | .ifThenElse c thn els =>
    .ifThenElse c (transformWhileContinue accs thn) (transformWhileBreak accs els)
  | .letBind n v body => .letBind n v (transformWhileFoldBody accs body)
  | e => transformWhileContinue accs e

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
  | .lit (.int n) => if n < 0 then s!"({n})" else s!"({n} : Int)"
  | .lit .unit => "()"
  | .lit (.uintLit w n) => s!"({n} : {w.toLeanType})"
  | .lit (.sintLit _ n) =>
    let numStr := if n < 0 then s!"({n})" else toString n
    s!"({numStr} : Int)"
  | .unitVal => "()"

  -- Variables
  | .var n => sanitizeName n

  -- Let binding: detect tuple destructuring pattern
  -- letBind "_tup" rhs (letBind "a" (proj (var "_tup") 0) (letBind "b" (proj (var "_tup") 1) body))
  -- → let (a, b) := rhs
  | .letBind n val body =>
    match extractTupleDestr n body with
    | some (names, rest) =>
      -- If only one field is non-wildcard, use projection instead of tuple pattern
      -- (avoids Lean metavariable inference issues with wildcards)
      let nonWild := (names.zip (List.range names.length)).filter fun (nm, _) => nm != "_"
      if nonWild.length == 1 then
        let (nm, idx) := nonWild.head!
        s!"{ind}let {sanitizeName nm} := ({toLean val 0}).{idx + 1}\n{toLean rest lvl}"
      else
        let nameStr := ", ".intercalate (names.map sanitizeName)
        s!"{ind}let ({nameStr}) := {toLean val 0}\n{toLean rest lvl}"
    | none =>
      s!"{ind}let {sanitizeName n} := {toLean val 0}\n{toLean body lvl}"

  -- Function application
  | .app "array_lit" args =>
    -- Emit as Lean array literal: #[a, b, c]
    let argStrs := args.map fun a => toLean a 0
    s!"#[{", ".intercalate argStrs}]"
  | .app f args =>
    let fname := runtimeName f
    if args.isEmpty then fname
    else
      let argStrs := args.map fun a => parensIf (toLean a 0) (!isAtom a)
      s!"{fname} {" ".intercalate argStrs}"

  -- Tuple
  | .tuple elems =>
    s!"({", ".intercalate (elems.map fun e => toLean e 0)})"

  -- Projection (Lean tuples use 1-indexed: .1, .2, etc.)
  | .proj e i =>
    s!"{parensIf (toLean e 0) (!isAtom e)}.{i + 1}"

  -- Conditional
  | .ifThenElse c t e =>
    -- When then-branch has ControlFlow but else is unitVal, else needs ControlFlow.Continue ()
    let eStr := if e == .unitVal && hasControlFlowNodes t then
        s!"{indent (lvl + 1)}ControlFlow.Continue ()"
      else toLean e (lvl + 1)
    s!"{ind}if {toLean c 0} then\n{ind1}{toLean t (lvl + 1)}\n{ind}else\n{ind1}{eStr}"

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
  | .forFold v lo hi body => renderFold lvl "foldRange" "forFold" v lo hi body
  | .forFoldRev v lo hi body => renderFold lvl "foldRangeRev" "forFoldRev" v lo hi body
  | .whileFold c body =>
    let accs := extractWhileAccumulators body
    let (initStr, paramStr) := accStrings accs
    if !accs.isEmpty then
      let body' := transformWhileFoldBody accs body
      -- Use _ for condition lambda (condition rarely uses accumulator names)
      s!"{ind}Hax.whileFold {initStr} (fun _ => {toLean c 0}) fun {paramStr} =>\n{ind1}{toLean body' 0}"
    else
      s!"{ind}Hax.whileFold () (fun _ => {toLean c 0}) fun _acc =>\n{ind1}{toLean body 0}"
  | .forFoldReturn v lo hi body =>
    let accs := extractAccumulators body
    let (initStr, paramStr) := accStrings accs
    s!"{ind}Hax.forFoldReturn {parensIf (toLean lo 0) (!isAtom lo)} {parensIf (toLean hi 0) (!isAtom hi)} {initStr} fun {sanitizeName v} {paramStr} =>\n{ind1}{toLean body 0}"
  | .forFoldRevReturn v lo hi body =>
    let accs := extractAccumulators body
    let (initStr, paramStr) := accStrings accs
    s!"{ind}Hax.forFoldRevReturn {parensIf (toLean lo 0) (!isAtom lo)} {parensIf (toLean hi 0) (!isAtom hi)} {initStr} fun {sanitizeName v} {paramStr} =>\n{ind1}{toLean body 0}"
  | .whileFoldReturn c body =>
    let accs := extractAccumulators body
    let (initStr, paramStr) := accStrings accs
    s!"{ind}Hax.whileFoldReturn {initStr} (fun {paramStr} => {toLean c 0}) fun {paramStr} =>\n{ind1}{toLean body 0}"

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
  /-- Render a forFold/forFoldRev with accumulator detection.
      Uses `Hax.foldRange` for simple folds (no ControlFlow),
      `Hax.forFold` for folds with break/continue. -/
  renderFold (lvl : Nat) (simpleName cfName : String)
      (v : String) (lo hi body : ImpExpr) : String :=
    let ind := indent lvl
    let ind1 := indent (lvl + 1)
    let accs := extractAccumulators body
    let (initStr, paramStr) := accStrings accs
    let loStr := parensIf (toLean lo 0) (!isAtom lo)
    let hiStr := parensIf (toLean hi 0) (!isAtom hi)
    if !hasControlFlowNodes body && !accs.isEmpty then
      -- Simple fold with accumulators, no ControlFlow
      let body' := simplifyFoldBody (transformFoldBody accs body)
      s!"{ind}Hax.{simpleName} {loStr} {hiStr} {initStr} fun {sanitizeName v} {paramStr} =>\n{ind1}{toLean body' 0}"
    else
      -- ControlFlow fold (has break/continue)
      s!"{ind}Hax.{cfName} {loStr} {hiStr} {initStr} fun {sanitizeName v} {paramStr} =>\n{ind1}{toLean body 0}"
  /-- Flatten seq chains into proper let-bindings. -/
  seqToLean (lvl : Nat) (e1 e2 : ImpExpr) : String :=
    let ind := indent lvl
    match e1, e2 with
    -- Skip unitVal in either position
    | .unitVal, _ => toLean e2 lvl
    | _, .unitVal => toLean e1 lvl
    -- Skip bare variable reads in seq (no side effects, from localMutation)
    | .var _, _ => toLean e2 lvl
    -- Flatten left-nested seq: seq (seq a b) c → seq a (seq b c)
    | .seq a b, _ => seqToLean lvl a (.seq b e2)
    -- Lift letBind out of seq: seq (letBind n v body) e2 → let n := v; seq body e2
    | .letBind n v body, _ =>
      s!"{ind}let {sanitizeName n} := {toLean v 0}\n{seqToLean lvl body e2}"
    -- Fold followed by reading an accumulator: bind fold result
    | .forFold _ _ _ body, _ => seqFold lvl e1 body e2
    | .forFoldRev _ _ _ body, _ => seqFold lvl e1 body e2
    | .whileFold _ body, _ => seqWhileFold lvl e1 body e2
    | .forFoldReturn _ _ _ body, _ => seqFold lvl e1 body e2
    | .forFoldRevReturn _ _ _ body, _ => seqFold lvl e1 body e2
    | .whileFoldReturn _ body, _ => seqWhileFold lvl e1 body e2
    -- Conditional mutation: if cond then {let x := rhs; x} else unitVal
    -- → let x := if cond then rhs else x
    | .ifThenElse cond thn .unitVal, _ =>
      let muts := extractCondMutations thn
      if muts.isEmpty then
        s!"{ind}let _ := {toLean e1 0}\n{toLean e2 lvl}"
      else if muts.length == 1 then
        let (name, rhs) := muts.head!
        s!"{ind}let {sanitizeName name} := if {toLean cond 0} then {toLean rhs 0} else {sanitizeName name}\n{toLean e2 lvl}"
      else
        let names := ", ".intercalate (muts.map fun (n, _) => sanitizeName n)
        let rhses := ", ".intercalate (muts.map fun (_, r) => toLean r 0)
        let olds := ", ".intercalate (muts.map fun (n, _) => sanitizeName n)
        s!"{ind}let ({names}) := if {toLean cond 0} then ({rhses}) else ({olds})\n{toLean e2 lvl}"
    -- General case: discard e1's value
    | _, _ => s!"{ind}let _ := {toLean e1 0}\n{toLean e2 lvl}"
  /-- Handle seq where the first expression is a fold.
      Binds the fold result to the accumulator variable(s). -/
  seqFold (lvl : Nat) (foldExpr body tail : ImpExpr) : String :=
    let ind := indent lvl
    let accs := extractAccumulators body
    if accs.isEmpty then
      s!"{ind}let _ := {toLean foldExpr 0}\n{toLean tail lvl}"
    else if accs.length == 1 then
      let acc := accs.head!
      -- If the tail just reads the accumulator, the fold IS the return value
      match tail with
      | .var n => if n == acc then toLean foldExpr lvl
                  else s!"{ind}let {sanitizeName acc} := {toLean foldExpr 0}\n{toLean tail lvl}"
      | _ => s!"{ind}let {sanitizeName acc} := {toLean foldExpr 0}\n{toLean tail lvl}"
    else
      let accStr := ", ".intercalate (accs.map sanitizeName)
      s!"{ind}let ({accStr}) := {toLean foldExpr 0}\n{toLean tail lvl}"
  /-- Handle seq where the first expression is a whileFold/whileFoldReturn.
      These return `ControlFlow β α` so we use `.merge` to extract the value.
      We split into two lets to help Lean's type inference. -/
  seqWhileFold (lvl : Nat) (foldExpr body tail : ImpExpr) : String :=
    let ind := indent lvl
    let accs := extractWhileAccumulators body
    if accs.isEmpty then
      s!"{ind}let _ := {toLean foldExpr 0}\n{toLean tail lvl}"
    else if accs.length == 1 then
      let acc := accs.head!
      match tail with
      | .var n => if n == acc then s!"{ind}({toLean foldExpr 0}).merge"
                  else s!"{ind}let _wf := {toLean foldExpr 0}\n{ind}let {sanitizeName acc} := _wf.merge\n{toLean tail lvl}"
      | _ => s!"{ind}let _wf := {toLean foldExpr 0}\n{ind}let {sanitizeName acc} := _wf.merge\n{toLean tail lvl}"
    else
      let accStr := ", ".intercalate (accs.map sanitizeName)
      s!"{ind}let _wf := {toLean foldExpr 0}\n{ind}let ({accStr}) := _wf.merge\n{toLean tail lvl}"

/-- Extract leading identity let-bindings (let x := x) as function parameters.
    These are emitted by HaxAdapter for Rust function parameters. -/
private def extractParams : ImpExpr → List String × ImpExpr
  | .letBind n (.var v) body =>
    if n == v && !n.startsWith "_" then
      let (ps, rest) := extractParams body
      (n :: ps, rest)
    else if n == v && n.startsWith "_" then
      -- Unused parameter: skip it entirely from the def signature
      let (ps, rest) := extractParams body
      (ps, rest)
    else ([], .letBind n (.var v) body)
  | e => ([], e)

/-- Collect variable names used as the first argument to `index` or `array_update`
    (i.e., used as arrays). These parameters need `Array Int` annotation. -/
private partial def collectArrayParams (params : List String) : ImpExpr → List String
  | .app "index" ((.var n) :: _) =>
    if params.contains n then [n] else []
  | .app "array_update" ((.var n) :: _) =>
    if params.contains n then [n] else []
  | .app _ args => args.flatMap (collectArrayParams params)
  | .letBind _ v body =>
    collectArrayParams params v ++ collectArrayParams params body
  | .seq a b => collectArrayParams params a ++ collectArrayParams params b
  | .ifThenElse c t e =>
    collectArrayParams params c ++ collectArrayParams params t ++ collectArrayParams params e
  | .forFold _ lo hi body =>
    collectArrayParams params lo ++ collectArrayParams params hi ++ collectArrayParams params body
  | .forFoldRev _ lo hi body =>
    collectArrayParams params lo ++ collectArrayParams params hi ++ collectArrayParams params body
  | .whileFold _ body =>
    collectArrayParams params body
  | .forFoldReturn _ lo hi body =>
    collectArrayParams params lo ++ collectArrayParams params hi ++ collectArrayParams params body
  | .forFoldRevReturn _ lo hi body =>
    collectArrayParams params lo ++ collectArrayParams params hi ++ collectArrayParams params body
  | .whileFoldReturn _ body =>
    collectArrayParams params body
  | .tuple elems => elems.flatMap (collectArrayParams params)
  | .match_ scrut arms =>
    collectArrayParams params scrut ++ arms.flatMap fun (_, b) => collectArrayParams params b
  | .proj e _ => collectArrayParams params e
  | _ => []

/-- Wrap the output in a Lean 4 definition with parameters.
    In certified (untyped) mode, annotates parameters to help type inference:
    parameters used with index/array_update get `Array Int`, others get no annotation. -/
def toLeanDef (name : String) (e : ImpExpr) (annotateTypes : Bool := false) : String :=
  let (params, body) := extractParams e
  let arrayParams := if annotateTypes then
      (collectArrayParams params body).eraseDups
    else []
  let paramStr := if params.isEmpty then ""
    else " " ++ " ".intercalate (params.map fun p =>
      let sn := sanitizeName p
      if annotateTypes && arrayParams.contains p then s!"({sn} : Array Int)"
      else sn)
  let bodyStr := toLean body 1
  s!"def {sanitizeName name}{paramStr} :=\n{bodyStr}\n"

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

/-! ## Certified Extraction: ImpExpr Literal Emitter

Emits the post-pipeline ImpExpr as a Lean constructor term.
Used together with the surface code to generate agreement proofs. -/

/-- Emit an ImpLit as Lean constructor syntax. -/
private def litToConstructor : ImpLit → String
  | .bool b => s!".bool {b}"
  | .int n => s!".int {n}"
  | .unit => ".unit"
  | .uintLit w n => s!".uintLit .{w.toSuffix} {n}"
  | .sintLit w n => s!".sintLit .{w.toSuffix} {n}"

/-- Emit an ImpPat as Lean constructor syntax. -/
private partial def patToConstructor : ImpPat → String
  | .wildcard => ".wildcard"
  | .litPat l => s!".litPat ({litToConstructor l})"
  | .varPat n => s!".varPat \"{n}\""
  | .tuplePat ps => s!".tuplePat [{", ".intercalate (ps.map patToConstructor)}]"
  | .somePat p => s!".somePat ({patToConstructor p})"
  | .nonePat => ".nonePat"
  | .okPat p => s!".okPat ({patToConstructor p})"
  | .errPat p => s!".errPat ({patToConstructor p})"

/-- Emit a post-pipeline ImpExpr as Lean constructor syntax.
    This embeds the AST as a Lean term for use in agreement proofs. -/
partial def toLeanImpExpr (e : ImpExpr) : String :=
  match e with
  | .lit l => s!"(.lit ({litToConstructor l}))"
  | .var n => s!"(.var \"{n}\")"
  | .unitVal => ".unitVal"
  | .letBind n v b =>
    s!"(.letBind \"{n}\" {toLeanImpExpr v} {toLeanImpExpr b})"
  | .app f args =>
    s!"(.app \"{f}\" [{", ".intercalate (args.map toLeanImpExpr)}])"
  | .tuple elems =>
    s!"(.tuple [{", ".intercalate (elems.map toLeanImpExpr)}])"
  | .proj e i => s!"(.proj {toLeanImpExpr e} {i})"
  | .ifThenElse c t e =>
    s!"(.ifThenElse {toLeanImpExpr c} {toLeanImpExpr t} {toLeanImpExpr e})"
  | .match_ scrut arms =>
    let armStrs := arms.map fun (p, body) =>
      s!"({patToConstructor p}, {toLeanImpExpr body})"
    s!"(.match_ {toLeanImpExpr scrut} [{", ".intercalate armStrs}])"
  | .seq e1 e2 => s!"(.seq {toLeanImpExpr e1} {toLeanImpExpr e2})"
  -- Post-pipeline fold constructors
  | .forFold v lo hi body =>
    s!"(.forFold \"{v}\" {toLeanImpExpr lo} {toLeanImpExpr hi} {toLeanImpExpr body})"
  | .forFoldRev v lo hi body =>
    s!"(.forFoldRev \"{v}\" {toLeanImpExpr lo} {toLeanImpExpr hi} {toLeanImpExpr body})"
  | .whileFold c body =>
    s!"(.whileFold {toLeanImpExpr c} {toLeanImpExpr body})"
  | .forFoldReturn v lo hi body =>
    s!"(.forFoldReturn \"{v}\" {toLeanImpExpr lo} {toLeanImpExpr hi} {toLeanImpExpr body})"
  | .forFoldRevReturn v lo hi body =>
    s!"(.forFoldRevReturn \"{v}\" {toLeanImpExpr lo} {toLeanImpExpr hi} {toLeanImpExpr body})"
  | .whileFoldReturn c body =>
    s!"(.whileFoldReturn {toLeanImpExpr c} {toLeanImpExpr body})"
  | .cfBreak e => s!"(.cfBreak {toLeanImpExpr e})"
  | .cfContinue e => s!"(.cfContinue {toLeanImpExpr e})"
  | .cfBreakContinue e => s!"(.cfBreakContinue {toLeanImpExpr e})"
  -- Pre-pipeline constructors (should not appear after pipeline)
  | .borrow e => s!"(.borrow {toLeanImpExpr e})"
  | .deref e => s!"(.deref {toLeanImpExpr e})"
  | .assign n rhs => s!"(.assign \"{n}\" {toLeanImpExpr rhs})"
  | .forLoop v lo hi body =>
    s!"(.forLoop \"{v}\" {toLeanImpExpr lo} {toLeanImpExpr hi} {toLeanImpExpr body})"
  | .forLoopRev v lo hi body =>
    s!"(.forLoopRev \"{v}\" {toLeanImpExpr lo} {toLeanImpExpr hi} {toLeanImpExpr body})"
  | .whileLoop c body =>
    s!"(.whileLoop {toLeanImpExpr c} {toLeanImpExpr body})"
  | .break_ (some e) => s!"(.break_ (some {toLeanImpExpr e}))"
  | .break_ none => "(.break_ none)"
  | .continue_ => ".continue_"
  | .earlyReturn e => s!"(.earlyReturn {toLeanImpExpr e})"
  | .questionMark e => s!"(.questionMark {toLeanImpExpr e})"

/-- Generate a certified extraction definition: ImpExpr literal. -/
def toLeanImpExprDef (name : String) (e : ImpExpr) : String :=
  s!"def {sanitizeName name}_impExpr : SSProve.Hax.ImpExpr :=\n  {toLeanImpExpr e}\n"

/-- Generate the full certified file: surface code + ImpExpr + agreement stub. -/
def toLeanCertifiedFile (defs : List (String × ImpExpr))
    (moduleName : String := "Generated") : String :=
  let header := s!"/-\n  Auto-generated by haxpipe --emit-certified (verified hax pipeline)\n  Surface code + ImpExpr literals for agreement proofs.\n-/\nimport SSProve.Hax.Runtime\nimport SSProve.Hax.AST\nimport SSProve.Hax.Semantics\n\nset_option linter.unusedVariables false\n\nnamespace {moduleName}\n\nopen SSProve.Hax\n\nmutual\n\n"
  let body := "\n".intercalate (defs.map fun (n, e) =>
    let surfaceDef := toLeanDef n e
    s!"{surfaceDef}")
  let impExprs := "\n".intercalate (defs.map fun (n, e) =>
    let impExprDef := toLeanImpExprDef n e
    s!"{impExprDef}")
  let footer := s!"\nend\n\n{impExprs}\nend {moduleName}\n"
  header ++ body ++ footer

end SSProve.Hax

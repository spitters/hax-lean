/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.AST
import SSProve.Hax.ImpType
import SSProve.Hax.HaxAdapter
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
    | "deriving" | "extends" | "abbrev" | "opaque" | "at" | "initialize"
    | "eq" | "ne" | "lt" | "le" | "gt" | "ge" | "mod" | "not" | "or" | "and"
    | "Or" | "And" | "Not" | "True" | "False" | "Eq" | "Ne" | "Nat" | "Int"
    | "Bool" | "String" | "Array" | "List" | "Option" | "IO" | "Monad"
    | "Pure" | "Bind" | "Functor" | "Unit" | "Prod" | "Sum" | "Fin"
    | "Empty" | "Decidable" | "Inhabited" | "Nonempty" => s!"«{n}»"
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
  | "Not" => "Hax.Not"  -- polymorphic: Bool → !, Int → bitwise complement
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
  -- Slice/mutation operations
  | "literal" => "Hax.literal"
  | "copy_from_slice" => "Hax.copy_from_slice"
  | "extend_from_slice" => "Hax.extend_from_slice"
  | "index_mut" => "Hax.index_mut"
  | "RangeTo" => "Hax.RangeTo"
  | "RangeFrom" => "Hax.RangeFrom"
  | "Range" => "Hax.Range"
  | "from" => "Hax.from_val"
  | "into_iter" => "Hax.into_iter"
  | "into_vec" => "Hax.into_vec"
  | "next" => "Hax.next"
  | "enumerate" => "Hax.enumerate"
  | "with_capacity" => "Hax.with_capacity"
  | "from_elem" => "Hax.from_elem"
  | "truncate" => "Hax.truncate"
  | "is_empty" => "Hax.is_empty"
  | "deref" => "Hax.deref"
  | "_assign" => "Hax.assign"
  | "count_ones" => "Hax.count_ones"
  | "assert_failed" => "Hax.assert_failed"
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
  match srcTy, dstTy with
  | .bool, _ =>
    -- Bool → Int/UInt: convert true→1, false→0
    "Hax.boolToInt"
  | _, _ =>
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
private partial def isAssertBlock : ImpExpr → Bool
  | .app f _ => f == "assert_failed" || f == "assert_failed'"
  | .match_ _ arms => arms.any fun (_, b) => isAssertBlock b
  | .ifThenElse _ t e => isAssertBlock t || isAssertBlock e
  | .letBind _ v b => isAssertBlock v || isAssertBlock b
  | .seq e1 e2 => isAssertBlock e1 || isAssertBlock e2
  | _ => false

/-- Check if an expression references a variable by name. -/
private partial def exprContainsVar (name : String) : ImpExpr → Bool
  | .var n => n == name
  | .app _ args => args.any (exprContainsVar name)
  | .tuple es => es.any (exprContainsVar name)
  | .letBind n v body => exprContainsVar name v || (n != name && exprContainsVar name body)
  | .seq a b => exprContainsVar name a || exprContainsVar name b
  | .ifThenElse c t e => exprContainsVar name c || exprContainsVar name t || exprContainsVar name e
  | .proj e _ => exprContainsVar name e
  | .match_ scrut arms =>
    exprContainsVar name scrut || arms.any fun (_, b) => exprContainsVar name b
  | _ => false

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

/-- Simplify a fold body by removing trivial let-return patterns.
    `letBind n rhs (var n)` → `rhs` when `n` is the only accumulator.
    This avoids indentation issues with bare return values. -/
private def simplifyFoldBody : ImpExpr → ImpExpr
  | .letBind n val (.var v) => if n == v then val else .letBind n val (.var v)
  | e => e

/-- Extract mutation variable names and their RHS from a conditional then-branch.
    Returns list of (name, rhs) for patterns like `seq (letBind n rhs (var n)) rest`. -/
private partial def extractCondAllBindings : ImpExpr → List (String × ImpExpr)
  | .seq (.seq a b) c => extractCondAllBindings (.seq a (.seq b c))
  | .seq (.letBind n rhs (.var v)) rest =>
    if n == v then (n, rhs) :: extractCondAllBindings rest
    else extractCondAllBindings rest
  | .seq .unitVal rest => extractCondAllBindings rest
  | .seq _ rest => extractCondAllBindings rest
  | .letBind n rhs (.var v) => if n == v then [(n, rhs)] else []
  -- Include non-mutation letBind as fresh bindings
  | .letBind n rhs body => (n, rhs) :: extractCondAllBindings body
  | .unitVal => []
  | _ => []

/-- Extract accumulator variable names from a fold body.
    Looks for the localMutation pattern: `seq (letBind n rhs (var n)) rest`
    which came from `assign n rhs`. Returns unique names in order.
    Also looks inside `ifThenElse` branches for conditional mutations. -/
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

/-- Transform a forFold body for accumulator-based rendering.
    Converts env-based mutation patterns to let-chain with accumulator return.

    Input (localMutation output):
      `seq (letBind "state" rhs (var "state")) unitVal`
    Output:
      `letBind "state" rhs (var "state")` -/
private partial def collectLetBindVars : ImpExpr → List String
  | .letBind n _ (.var v) =>
    if n == v then []  -- mutation pattern, not a fresh binding
    else [n]
  | .letBind n _ body => n :: collectLetBindVars body
  | .seq a b => collectLetBindVars a ++ collectLetBindVars b
  | .ifThenElse _ t e => collectLetBindVars t ++ collectLetBindVars e
  | _ => []

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

/-- Extract accumulator variable names from a fold body.
    Looks for the localMutation pattern: `seq (letBind n rhs (var n)) rest`
    which came from `assign n rhs`. Returns unique names in order.
    Filters out `_assign`-prefixed names which are intermediate mutation
    temporaries from nested field/index assignments (not real accumulators). -/
private partial def extractAccumulators : ImpExpr → List String
  | .seq (.seq a b) c => extractAccumulators (.seq a (.seq b c))
  | .seq (.letBind n _ (.var v)) rest =>
    if n == v && !n.startsWith "_assign" then
      let restAccs := extractAccumulators rest
      if restAccs.contains n then restAccs else n :: restAccs
    else extractAccumulators rest
  -- Look inside conditional mutations for hidden accumulators
  | .seq (.ifThenElse _ thn _) rest =>
    let thnAccs := extractCondMutations thn |>.map (·.1)
      |>.filter (!·.startsWith "_assign")
    let restAccs := extractAccumulators rest
    let all := thnAccs ++ restAccs
    all.eraseDups
  | .seq _ rest => extractAccumulators rest
  | .letBind n _ (.var v) =>
    if n == v && !n.startsWith "_assign" then [n] else []
  -- Recurse into local let-bindings (non-mutation letBind)
  | .letBind _ _ body => extractAccumulators body
  -- Top-level ifThenElse (entire fold body is a conditional)
  | .ifThenElse _ thn _ =>
    let thnAccs := extractCondMutations thn |>.map (·.1)
      |>.filter (!·.startsWith "_assign")
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
  | .letBind n _ (.var v) => if n == v && !n.startsWith "_assign" then
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

/-- Transform the break branch of a whileFold body.
    Replaces `cfBreak unitVal` and bare `unitVal` with `cfBreak (accs)` so the break value
    carries the current accumulator state. -/
private partial def transformWhileBreak (accs : List String) : ImpExpr → ImpExpr
  | .cfBreak _ => .cfBreak (accTuple accs)
  | .unitVal => .cfBreak (accTuple accs)
  | .seq (.cfBreak _) _ => .cfBreak (accTuple accs)  -- collapse redundant seq after cfBreak
  | .seq .unitVal rest => transformWhileBreak accs rest
  | .seq e1 e2 => .seq (transformWhileBreak accs e1) (transformWhileBreak accs e2)
  | .letBind n v body => .letBind n v (transformWhileBreak accs body)
  | .ifThenElse c t e =>
    .ifThenElse c (transformWhileBreak accs t) (transformWhileBreak accs e)
  | e => e

/-- Transform the continue branch of a whileFold body.
    Same as `transformFoldBody` but wraps the final value in `cfContinue`. -/
private partial def transformWhileContinue (accs : List String) : ImpExpr → ImpExpr
  | .seq (.seq a b) c => transformWhileContinue accs (.seq a (.seq b c))
  | .seq (.letBind n val (.var v)) rest =>
    if n == v then .letBind n val (transformWhileContinue accs rest)
    else .seq (.letBind n val (.var v)) (transformWhileContinue accs rest)
  | .seq .unitVal rest => transformWhileContinue accs rest
  -- Handle guard pattern: seq (ifThenElse cond <cfBreak> <unitVal>) rest
  -- This is a nested break-check inside the continue branch.
  -- The cfBreak side should break with accumulators, unitVal side falls through.
  | .seq (.ifThenElse c thn els) rest =>
    let thnHasCF := hasControlFlowNodes thn
    let elsHasCF := hasControlFlowNodes els
    if thnHasCF && !elsHasCF then
      -- then has cfBreak, else is fall-through → then breaks, else continues with rest
      .ifThenElse c (transformWhileBreak accs thn) (transformWhileContinue accs rest)
    else if !thnHasCF && elsHasCF then
      -- else has cfBreak, then is fall-through
      .ifThenElse c (transformWhileContinue accs rest) (transformWhileBreak accs els)
    else
      .seq (.ifThenElse c thn els) (transformWhileContinue accs rest)
  | .seq e1 rest => .seq e1 (transformWhileContinue accs rest)
  | .letBind n val body => .letBind n val (transformWhileContinue accs body)
  | .ifThenElse c thn els =>
    -- Nested if inside the continue branch of whileFold.
    -- If one sub-branch already has cfContinue, the other's unitVal is a break.
    let thnHasCF := hasControlFlowNodes thn
    let elsHasCF := hasControlFlowNodes els
    if thnHasCF && !elsHasCF then
      -- then has cfContinue, else is a break path
      .ifThenElse c thn (transformWhileBreak accs els)
    else if !thnHasCF && elsHasCF then
      -- else has cfContinue, then is a break path
      .ifThenElse c (transformWhileBreak accs thn) els
    else if !thnHasCF && !elsHasCF then
      -- Neither has CF: both should continue
      .ifThenElse c (transformWhileContinue accs thn) (transformWhileContinue accs els)
    else
      -- Both have CF: leave as-is
      .ifThenElse c thn els
  | .unitVal => .cfContinue (accTuple accs)
  | e => e

/-- Transform a whileFold body for surface rendering.
    - In continue branches: replace trailing `unitVal` with `cfContinue (accs)`
    - In break branches: replace `cfBreak unitVal` with `cfBreak (accs)` -/
private partial def transformWhileFoldBody (accs : List String) : ImpExpr → ImpExpr
  | .ifThenElse c thn els =>
    .ifThenElse c (transformWhileContinue accs thn) (transformWhileBreak accs els)
  | .letBind n v body => .letBind n v (transformWhileFoldBody accs body)
  | e => transformWhileContinue accs e

/-- Nest `.cfBreak` inside `forFoldReturn` bodies.
    In `forFoldReturn`, the body returns `ControlFlow (ControlFlow β γ) α`.
    An early function return `cfBreak val` becomes `cfBreak (cfBreak val)`.
    (Note: `cfBreakContinue val` already handles loop-break as `cfBreak (cfContinue val)`.) -/
private partial def nestCfBreakForReturn : ImpExpr → ImpExpr
  | .cfBreak v => .cfBreak (.cfBreak v)
  | .seq (.cfBreak v) .unitVal => .cfBreak (.cfBreak v)
  | .letBind n v body => .letBind n v (nestCfBreakForReturn body)
  | .seq a b => .seq (nestCfBreakForReturn a) (nestCfBreakForReturn b)
  | .ifThenElse c t e => .ifThenElse c (nestCfBreakForReturn t) (nestCfBreakForReturn e)
  | .match_ s arms => .match_ s (arms.map fun (p, b) => (p, nestCfBreakForReturn b))
  | e => e

/-- Check if a forFoldReturn body contains cfBreak (early return from function). -/
private partial def hasCfBreak : ImpExpr → Bool
  | .cfBreak _ => true
  | .cfBreakContinue _ => true
  | .letBind _ v b => hasCfBreak v || hasCfBreak b
  | .seq a b => hasCfBreak a || hasCfBreak b
  | .ifThenElse _ t e => hasCfBreak t || hasCfBreak e
  | .match_ _ arms => arms.any fun (_, b) => hasCfBreak b
  | _ => false

/-- Extract the cfBreak return value from an expression, looking through seq/unitVal wrappers.
    Returns the break value if the expression is essentially a cfBreak (early return),
    or none if it's not. -/
private def extractCfBreak : ImpExpr → Option ImpExpr
  | .cfBreak val => some val
  | .seq (.cfBreak val) .unitVal => some val
  | .cfContinue _ => none
  | .unitVal => none
  | .seq .unitVal rest => extractCfBreak rest
  | _ => none

/-- Check if an expression references a name as a function call (.app fname ...). -/
private partial def exprContainsApp (fname : String) : ImpExpr → Bool
  | .app f args => f == fname || args.any (exprContainsApp fname)
  | .letBind _ v body => exprContainsApp fname v || exprContainsApp fname body
  | .seq a b => exprContainsApp fname a || exprContainsApp fname b
  | .ifThenElse c t e => exprContainsApp fname c || exprContainsApp fname t || exprContainsApp fname e
  | .tuple es => es.any (exprContainsApp fname)
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    exprContainsApp fname lo || exprContainsApp fname hi || exprContainsApp fname body
  | .whileFold c body => exprContainsApp fname c || exprContainsApp fname body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    exprContainsApp fname lo || exprContainsApp fname hi || exprContainsApp fname body
  | .whileFoldReturn c body => exprContainsApp fname c || exprContainsApp fname body
  | .cfBreak e | .cfContinue e | .cfBreakContinue e => exprContainsApp fname e
  | .match_ scrut arms =>
    exprContainsApp fname scrut || arms.any fun (_, b) => exprContainsApp fname b
  | .proj e _ => exprContainsApp fname e
  | _ => false

/-- Check if `.app projName [.var varName]` appears in an expression.
    Used to detect struct projection usage on a specific variable. -/
private partial def checkProjOnVar (varName projName : String) : ImpExpr → Bool
  | .app f [.var v] => f == projName && v == varName
  | .app _ args => args.any (checkProjOnVar varName projName)
  | .letBind _ v body =>
    checkProjOnVar varName projName v || checkProjOnVar varName projName body
  | .seq a b => checkProjOnVar varName projName a || checkProjOnVar varName projName b
  | .ifThenElse c t e =>
    checkProjOnVar varName projName c || checkProjOnVar varName projName t ||
    checkProjOnVar varName projName e
  | .tuple es => es.any (checkProjOnVar varName projName)
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    checkProjOnVar varName projName lo || checkProjOnVar varName projName hi ||
    checkProjOnVar varName projName body
  | .whileFold c body =>
    checkProjOnVar varName projName c || checkProjOnVar varName projName body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    checkProjOnVar varName projName lo || checkProjOnVar varName projName hi ||
    checkProjOnVar varName projName body
  | .whileFoldReturn c body =>
    checkProjOnVar varName projName c || checkProjOnVar varName projName body
  | .match_ scrut arms =>
    checkProjOnVar varName projName scrut ||
    arms.any fun (_, b) => checkProjOnVar varName projName b
  | .cfBreak e | .cfContinue e | .cfBreakContinue e =>
    checkProjOnVar varName projName e
  | _ => false

/-- Helper for hasGuardRecursion: walk through letBind/seq chains. -/
private partial def hasGuardRecGo (fname : String) : ImpExpr → Bool
  | .letBind _ _ body => hasGuardRecGo fname body
  | .seq e1 rest =>
    -- Check if e1 contains ControlFlow (cfBreak) and rest calls fname
    (hasControlFlowNodes e1 && exprContainsApp fname rest)
    || hasGuardRecGo fname rest  -- try deeper in the seq chain
  | _ => false

/-- Check if a function body contains the early-return guard pattern:
    seq (ifThenElse cond <cfBreak> <unitVal/cfContinue>) rest
    AND the function calls itself (self-recursive). -/
private def hasGuardRecursion (fname : String) (e : ImpExpr) : Bool :=
  hasGuardRecGo fname e

/-- Is this expression simple enough to not need parentheses as an argument? -/
private def isAtom : ImpExpr → Bool
  | .lit _ | .var _ | .unitVal => true
  | .tuple _ => true  -- tuples have their own parens
  | _ => false

/-- Wrap in parentheses if needed. -/
private def parensIf (s : String) (needParens : Bool) : String :=
  if needParens then s!"({s})" else s

/-- Is this expression known to produce a Bool?
    Comparison operators, boolean literals, logical ops, and `Not` all return Bool.
    Unknown expressions (bare variables, arbitrary function calls) return false. -/
private def isKnownBool : ImpExpr → Bool
  | .lit (.bool _) => true
  | .app f _ => match f with
    | "eq" | "Eq" | "ne" | "Ne" | "lt" | "Lt" | "le" | "Le"
    | "gt" | "Gt" | "ge" | "Ge" | "beq" | "bne" => true
    | "and" | "And" | "or" | "Or" | "&&" | "||" => true
    | "not" | "Not" => true
    | _ => false
  | _ => false

/-- Check if an expression is a "leaf" — renders without `{indent lvl}` prefix.
    Leaf expressions need explicit indentation when they appear at the start of a line
    (e.g., as the final expression of a let-chain or fold body). -/
private def isLeafExpr : ImpExpr → Bool
  | .var _ | .lit _ | .unitVal | .app _ _ | .tuple _ => true
  | .cfBreak _ | .cfContinue _ | .cfBreakContinue _ => true
  | .proj _ _ => true
  | _ => false

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
  | .var "new" => "#[]"  -- Vec::new() → empty array literal (polymorphic)
  | .var n => sanitizeName n

  -- Skip dead ControlFlow let-bindings: let _ := cfBreak/cfContinue/cfBreakContinue (...) → just render body
  | .letBind n (.cfBreak _) body | .letBind n (.cfContinue _) body | .letBind n (.cfBreakContinue _) body =>
    if n.startsWith "_" then atLine body lvl
    else
      let ind := indent lvl
      s!"{ind}let {sanitizeName n} := (sorry : Unit)\n{atLine body lvl}"
  -- Let binding: detect tuple destructuring pattern
  -- letBind "_tup" rhs (letBind "a" (proj (var "_tup") 0) (letBind "b" (proj (var "_tup") 1) body))
  -- → let (a, b) := rhs
  | .letBind n val body =>
    match extractTupleDestr n body with
    | some (names, rest) =>
      -- If only one field is non-wildcard, use projection instead of tuple pattern
      -- (avoids Lean metavariable inference issues with wildcards)
      let nonWild : List (String × Nat) := (names.zip (List.range names.length)).filter fun (nm, _) => nm != "_"
      if nonWild.length == 1 then
        let (nm, idx) := nonWild.head!
        -- Use correct nested projection path for right-associated tuples
        let nFields := names.length
        let rec mkProjPath (i nn : Nat) : String :=
          if nn <= 1 then "" else if i == 0 then ".1"
          else if nn == 2 then ".2" else ".2" ++ mkProjPath (i - 1) (nn - 1)
        let path := mkProjPath idx nFields
        s!"{ind}let {sanitizeName nm} := ({toLean val 0}){path}\n{atLine rest lvl}"
      else
        let nameStr := ", ".intercalate (names.map sanitizeName)
        s!"{ind}let ({nameStr}) := {toLean val 0}\n{atLine rest lvl}"
    | none =>
      -- For compound values (if/else, match), put on next line with proper indentation
      -- to avoid branches appearing before the let-binding column
      let valStr := if isLeafExpr val then toLean val 0
                    else s!"\n{toLean val (lvl + 1)}"
      s!"{ind}let {sanitizeName n} := {valStr}\n{atLine body lvl}"

  -- Function application
  | .app "array_lit" args =>
    -- Emit as Lean array literal: #[a, b, c]
    let argStrs := args.map fun a => toLean a 0
    s!"#[{", ".intercalate argStrs}]"
  | .app "Not" [x] | .app "not" [x] =>
    -- For Bool args, use logical negation; for Int args, use polymorphic Hax.Not
    -- (Hax.Not uses HaxNot typeclass: Bool → !, Int → bitwise complement)
    if isKnownBool x then s!"(!{parensIf (toLean x 0) (!isAtom x)})"
    else s!"(Hax.Not {parensIf (toLean x 0) (!isAtom x)})"
  | .app f args =>
    -- Special-case: index/index_mut with range args → slice functions
    match f, args with
    | "index", [arr, .app "RangeTo" [n]] =>
      s!"Hax.slice_to {parensIf (toLean arr 0) (!isAtom arr)} {parensIf (toLean n 0) (!isAtom n)}"
    | "index", [arr, .app "RangeFrom" [n]] =>
      s!"Hax.slice_from {parensIf (toLean arr 0) (!isAtom arr)} {parensIf (toLean n 0) (!isAtom n)}"
    | "index", [arr, .app "Range" [lo, hi]] =>
      s!"Hax.slice_range {parensIf (toLean arr 0) (!isAtom arr)} {parensIf (toLean lo 0) (!isAtom lo)} {parensIf (toLean hi 0) (!isAtom hi)}"
    | "index_mut", [arr, .app "RangeTo" [n]] =>
      s!"Hax.slice_to {parensIf (toLean arr 0) (!isAtom arr)} {parensIf (toLean n 0) (!isAtom n)}"
    | "index_mut", [arr, .app "RangeFrom" [n]] =>
      s!"Hax.slice_from {parensIf (toLean arr 0) (!isAtom arr)} {parensIf (toLean n 0) (!isAtom n)}"
    | "index_mut", [arr, .app "Range" [lo, hi]] =>
      s!"Hax.slice_range {parensIf (toLean arr 0) (!isAtom arr)} {parensIf (toLean lo 0) (!isAtom lo)} {parensIf (toLean hi 0) (!isAtom hi)}"
    -- Special-case: collect(Range(lo, hi)) → Hax.range lo hi
    | "collect", [.app "Range" [lo, hi]] =>
      s!"Hax.range {parensIf (toLean lo 0) (!isAtom lo)} {parensIf (toLean hi 0) (!isAtom hi)}"
    -- Vec::new() → empty array literal (polymorphic)
    | "new", [] => "#[]"
    | _, _ =>
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
    -- Use max lvl 1 to avoid column-0 if-then-else inside let-bindings
    let ifLvl := max lvl 1
    let ifInd := indent ifLvl
    let ifInd1 := indent (ifLvl + 1)
    -- When then-branch has ControlFlow but else is unitVal, else needs Hax.cfContinue ()
    let eStr := if e == .unitVal && hasControlFlowNodes t then
        s!"{ifInd1}Hax.cfContinue ()"
      else toLean e (ifLvl + 1)
    let condStr := condToLean c
    -- When else is unitVal and then is non-ControlFlow, non-unit:
    -- Wrap then-branch in `let _ := ...; ()` so both branches return Unit.
    -- This handles assert/panic patterns (if !cond then panic(...) else ())
    -- and avoids type mismatches between non-Unit then and Unit else.
    if e == .unitVal && !hasControlFlowNodes t && t != .unitVal then
      s!"{ifInd}if {condStr} then\n{ifInd1}let _ := {toLean t (ifLvl + 1)}\n{ifInd1}()\n{ifInd}else\n{ifInd1}()"
    else
      s!"{ifInd}if {condStr} then\n{ifInd1}{toLean t (ifLvl + 1)}\n{ifInd}else\n{ifInd1}{eStr}"

  -- Pattern match
  | .match_ scrut arms =>
    -- When ALL patterns are .varPat (constant names, not constructors),
    -- convert to if-else chain since Lean 4 would treat them as fresh bindings
    let allVarPats := arms.all fun (p, _) => match p with
      | .varPat _ => true | .wildcard => true | _ => false
    if allVarPats && arms.length > 1 then
      let scrutStr := toLean scrut 0
      -- Use max lvl 1 to avoid column-0 if-chains inside let-bindings
      let ifLvl := max lvl 1
      let ifInd := indent ifLvl
      let ifInd1 := indent (ifLvl + 1)
      let rec ifChain (remaining : List (ImpPat × ImpExpr)) : String :=
        match remaining with
        | [] => s!"{ifInd}()" -- unreachable
        | [(_, body)] => toLean body (ifLvl + 1)
        | (p, body) :: rest =>
          match p with
          | .varPat n =>
            -- Parenthesize compound scrutinee to avoid multi-arg Hax.beq
            let scrutParen := if isAtom scrut then scrutStr else s!"({scrutStr})"
            s!"{ifInd}if Hax.beq {scrutParen} {sanitizeName n} then\n{ifInd1}{toLean body (ifLvl + 1)}\n{ifInd}else\n{ifInd1}{ifChain rest}"
          | _ => toLean body (ifLvl + 1) -- wildcard/fallback
      ifChain arms
    else
      -- Use max lvl 1 for match arms to ensure they're never at column 0
      -- (column 0 arms are mis-parsed when the match is inside a let-binding)
      let armLvl := max lvl 1
      let armInd := indent armLvl
      let armStrs := arms.map fun (p, body) =>
        s!"{armInd}| {patToLean p} => {toLean body (armLvl + 1)}"
      s!"{ind}match {toLean scrut 0} with\n{"\n".intercalate armStrs}"

  -- Sequence: flatten and emit as let-chain
  | .seq e1 e2 => seqToLean lvl e1 e2

  -- ControlFlow constructors (post-pipeline)
  | .cfBreak e =>
    -- Annotate `none` to avoid unresolvable implicit α in ControlFlow
    let eStr := match e with
      | .app "None" [] => "(none : Option (Array Int))"
      -- Bool values in cfBreak: annotate type to help Lean resolve ControlFlow
      | .lit (.bool true) => "(true : Bool)"
      | .lit (.bool false) => "(false : Bool)"
      | _ => parensIf (toLean e 0) (!isAtom e)
    s!"Hax.cfBreak {eStr}"
  | .cfContinue e =>
    s!"Hax.cfContinue {parensIf (toLean e 0) (!isAtom e)}"
  | .cfBreakContinue e =>
    s!"Hax.cfBreak (Hax.cfContinue {parensIf (toLean e 0) (!isAtom e)})"

  -- Fold operations (post-pipeline)
  | .forFold v lo hi body => renderFold lvl "foldRange" "forFold" v lo hi body
  | .forFoldRev v lo hi body => renderFold lvl "foldRangeRev" "forFoldRev" v lo hi body
  | .whileFold c body =>
    let accs := extractWhileAccumulators body
    -- Filter out loop-local variables: accumulators that are also freshly
    -- let-bound inside the body are loop-local (not from the enclosing scope)
    let localVars := collectLetBindVars body
    let accs := accs.filter fun a => !localVars.contains a
    let (initStr, paramStr) := accStrings accs
    if !accs.isEmpty then
      let body' := transformWhileFoldBody accs body
      -- Use _ for condition lambda (condition rarely uses accumulator names)
      s!"{ind}Hax.whileFold {initStr} (fun _ => {toLean c 0}) fun {paramStr} =>\n{atLine body' (lvl + 1)}"
    else
      s!"{ind}Hax.whileFold () (fun _ => {toLean c 0}) fun _acc =>\n{atLine body (lvl + 1)}"
  | .forFoldReturn v lo hi body =>
    let accs := extractAccumulators body
    let (initStr, paramStr) := accStrings accs
    let body' := nestCfBreakForReturn body
    s!"{ind}Hax.forFoldReturn {parensIf (toLean lo 0) (!isAtom lo)} {parensIf (toLean hi 0) (!isAtom hi)} {initStr} fun {sanitizeName v} {paramStr} =>\n{atLine body' (lvl + 1)}"
  | .forFoldRevReturn v lo hi body =>
    let accs := extractAccumulators body
    let (initStr, paramStr) := accStrings accs
    let body' := nestCfBreakForReturn body
    s!"{ind}Hax.forFoldRevReturn {parensIf (toLean lo 0) (!isAtom lo)} {parensIf (toLean hi 0) (!isAtom hi)} {initStr} fun {sanitizeName v} {paramStr} =>\n{atLine body' (lvl + 1)}"
  | .whileFoldReturn c body =>
    let accs := extractAccumulators body
    let localVars := collectLetBindVars body
    let accs := accs.filter fun a => !localVars.contains a
    let (initStr, paramStr) := accStrings accs
    -- Apply transformWhileFoldBody to ensure trailing bare expressions are wrapped in cfContinue
    let body' := if !accs.isEmpty then transformWhileFoldBody accs body else body
    -- Nest cfBreak for early returns (same as forFoldReturn)
    let body' := nestCfBreakForReturn body'
    s!"{ind}Hax.whileFoldReturn {initStr} (fun {paramStr} => {toLean c 0}) fun {paramStr} =>\n{atLine body' (lvl + 1)}"

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
  /-- Render at line start: adds indent prefix for leaf expressions that don't
      add their own `{indent lvl}` prefix (var, app, lit, tuple, cfBreak, etc.). -/
  atLine (expr : ImpExpr) (l : Nat) : String :=
    let s := toLean expr l
    if isLeafExpr expr then s!"{indent l}{s}" else s
  /-- Render an expression as a Bool condition for `if`.
      - Known-Bool expressions (comparisons, logical ops) pass through.
      - Function applications pass through (preamble functions return Bool).
      - `Not x` on a variable → `Hax.beq x (0 : Int)` (correct negation for Int).
      - `Not x` on a Bool expr → `!x`.
      - Bare variables → `Hax.bne x (0 : Int)` (forces Int, C-style truth). -/
  condToLean (c : ImpExpr) : String :=
    match c with
    | .app "Not" [x] | .app "not" [x] =>
      -- Not on a known-Bool or function call: use logical negation
      if isKnownBool x || x matches .app _ _ then
        s!"!{parensIf (toLean x 0) (!isAtom x)}"
      -- Not on a variable or other: use Hax.beq _ 0 for correct negation
      -- Don't annotate 0 with : Int — let Lean infer (works for Bool via OfNat)
      else s!"Hax.beq {parensIf (toLean x 0) (!isAtom x)} 0"
    | .app _ _ =>
      -- Function applications: either runtime op (known Bool) or preamble function
      toLean c 0
    | _ =>
      if isKnownBool c then toLean c 0
      else s!"Hax.bne {parensIf (toLean c 0) (!isAtom c)} 0"
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
      s!"{ind}Hax.{simpleName} {loStr} {hiStr} {initStr} fun {sanitizeName v} {paramStr} =>\n{atLine body' (lvl + 1)}"
    else if accs.isEmpty && !hasControlFlowNodes body then
      -- Unit-accumulator fold (side-effect loop): wrap body to return ()
      let bodyStr := if isLeafExpr body then toLean body 0
                     else s!"\n{toLean body (lvl + 2)}"
      s!"{ind}Hax.{simpleName} {loStr} {hiStr} {initStr} fun {sanitizeName v} {paramStr} =>\n{ind1}let _ := {bodyStr}\n{ind1}()"
    else
      -- ControlFlow fold (has break/continue)
      s!"{ind}Hax.{cfName} {loStr} {hiStr} {initStr} fun {sanitizeName v} {paramStr} =>\n{atLine body (lvl + 1)}"
  /-- Flatten seq chains into proper let-bindings. -/
  seqToLean (lvl : Nat) (e1 e2 : ImpExpr) : String :=
    let ind := indent lvl
    match e1, e2 with
    -- Skip unitVal in either position
    | .unitVal, _ => atLine e2 lvl
    | _, .unitVal => atLine e1 lvl
    -- Skip bare variable reads in seq (no side effects, from localMutation)
    | .var _, _ => atLine e2 lvl
    -- Flatten left-nested seq: seq (seq a b) c → seq a (seq b c)
    | .seq a b, _ => seqToLean lvl a (.seq b e2)
    -- Skip dead code: seq (letBind "_" (cfBreak ...) body) e2
    | .letBind n (.cfBreak _) body, _ =>
      if n.startsWith "_" then seqToLean lvl body e2
      else s!"{ind}let {sanitizeName n} := {toLean (.cfBreak (.cfBreak .unitVal)) 0}\n{seqToLean lvl body e2}"
    -- Lift letBind out of seq: seq (letBind n v body) e2 → let n := v; seq body e2
    | .letBind n v body, _ =>
      s!"{ind}let {sanitizeName n} := {toLean v 0}\n{seqToLean lvl body e2}"
    -- Fold followed by reading an accumulator: bind fold result
    | .forFold _ _ _ body, _ => seqFold lvl e1 body e2
    | .forFoldRev _ _ _ body, _ => seqFold lvl e1 body e2
    | .whileFold _ body, _ => seqWhileFold lvl e1 body e2
    | .forFoldReturn _ _ _ body, _ => seqFoldReturn lvl e1 body e2
    | .forFoldRevReturn _ _ _ body, _ => seqFoldReturn lvl e1 body e2
    | .whileFoldReturn _ body, _ => seqFoldReturn lvl e1 body e2
    -- Conditional mutation: if cond then {mutations} else ...
    -- Handles both one-sided (else unitVal) and two-sided conditionals
    | .ifThenElse cond thn els, _ =>
      -- Skip assert blocks (assert_eq!/assert! wrapped in if-true-then)
      if isAssertBlock e1 then atLine e2 lvl
      -- Early-return guard pattern:
      --   seq (ifThenElse cond <cfBreak val> <cfContinue/unitVal>) rest
      --   → if cond then val else rest
      -- This handles recursive functions with base-case guards.
      -- The cfBreak may be wrapped in seq: (seq (cfBreak val) unitVal)
      else match extractCfBreak thn, extractCfBreak els with
      | some retVal, none =>
        let ifLvl := max lvl 1
        let ifInd := indent ifLvl
        let ifInd1 := indent (ifLvl + 1)
        s!"{ifInd}if {condToLean cond} then\n{ifInd1}{toLean retVal (ifLvl + 1)}\n{ifInd}else\n{atLine e2 (ifLvl + 1)}"
      | none, some retVal =>
        -- Inverted: if cond then continue else break → if !cond then val else rest
        let ifLvl := max lvl 1
        let ifInd := indent ifLvl
        let ifInd1 := indent (ifLvl + 1)
        s!"{ifInd}if !({condToLean cond}) then\n{ifInd1}{toLean retVal (ifLvl + 1)}\n{ifInd}else\n{atLine e2 (ifLvl + 1)}"
      | _, _ =>
      if els == .unitVal then
        -- One-sided: if cond then {let x := rhs; x} else unitVal
        let allBindings := extractCondAllBindings thn
        if allBindings.isEmpty then
          let valStr := if isLeafExpr e1 then toLean e1 0 else s!"\n{toLean e1 (lvl + 1)}"
          s!"{ind}let _ := {valStr}\n{atLine e2 lvl}"
        else
          -- Use extractCondMutations to identify true mutations (letBind n rhs (var n) pattern).
          -- Everything else from extractCondAllBindings is a fresh local binding.
          let mutNames := (extractCondMutations thn).map (·.1)
          let freshBindings := allBindings.filter fun (n, _) => !mutNames.contains n
          let trueMuts := allBindings.filter fun (n, _) => mutNames.contains n
          -- Fresh bindings emitted unconditionally (pure local helpers, safe to compute always).
          let freshStr := freshBindings.map fun (name, rhs) =>
            s!"{ind}let {sanitizeName name} := {toLean rhs 0}"
          -- Phase 4 fix: detect self-referencing mutations.
          -- If a variable appears multiple times in trueMuts (fresh bind + mutation),
          -- the first occurrence is a default init emitted unconditionally.
          let seen : List String := []
          let (initStrs, condStrs, _) := trueMuts.foldl (fun (inits, conds, seen) (name, rhs) =>
            if seen.contains name then
              -- Already seen this name — emit as conditional mutation
              (inits, conds ++ [s!"{ind}let {sanitizeName name} := if {condToLean cond} then {toLean rhs 0} else {sanitizeName name}"], seen)
            else
              -- First occurrence: check if this name has a later mutation (self-ref fix)
              let hasDuplicate := (trueMuts.filter fun p => p.1 == name).length > 1
              if hasDuplicate then
                -- Emit first as unconditional init (prevents self-reference in else branch)
                (inits ++ [s!"{ind}let {sanitizeName name} := {toLean rhs 0}"], conds, name :: seen)
              else
                -- Normal: emit as conditional mutation
                (inits, conds ++ [s!"{ind}let {sanitizeName name} := if {condToLean cond} then {toLean rhs 0} else {sanitizeName name}"], name :: seen)
          ) (freshStr, [], seen)
          s!"{"\n".intercalate (initStrs ++ condStrs)}\n{atLine e2 lvl}"
      else
        -- Phase 5: Two-sided conditional mutation
        let thnMuts := extractCondMutations thn
        let elsMuts := extractCondMutations els
        -- Only merge if both branches are pure mutations (no local bindings)
        -- Local bindings in branches would be lost during merge
        let thnAllBindings := extractCondAllBindings thn
        let elsAllBindings := extractCondAllBindings els
        let thnHasLocals := thnAllBindings.length > thnMuts.length
        let elsHasLocals := elsAllBindings.length > elsMuts.length
        if (!thnMuts.isEmpty || !elsMuts.isEmpty) && !thnHasLocals && !elsHasLocals then
          -- Merge mutations from both branches
          let allNames := (thnMuts.map (·.1) ++ elsMuts.map (·.1)).eraseDups
          let mutStr := allNames.map fun name =>
            let thnRhs := (thnMuts.find? (·.1 == name)).map (·.2) |>.getD (.var name)
            let elsRhs := (elsMuts.find? (·.1 == name)).map (·.2) |>.getD (.var name)
            s!"{ind}let {sanitizeName name} := if {condToLean cond} then {toLean thnRhs 0} else {toLean elsRhs 0}"
          s!"{"\n".intercalate mutStr}\n{atLine e2 lvl}"
        else
          let valStr := if isLeafExpr e1 then toLean e1 0 else s!"\n{toLean e1 (lvl + 1)}"
          s!"{ind}let _ := {valStr}\n{atLine e2 lvl}"
    -- Skip dead ControlFlow expressions in seq (cfBreak/cfContinue/cfBreakContinue)
    | .cfBreak _, _ => atLine e2 lvl
    | .cfContinue _, _ => atLine e2 lvl
    | .cfBreakContinue _, _ => atLine e2 lvl
    -- General case: skip assert blocks, discard e1's value otherwise
    | _, _ =>
      -- Skip assert_eq!/assert! blocks (Rust runtime assertions with unsynthesizable types)
      if isAssertBlock e1 then atLine e2 lvl
      else
        let valStr := if isLeafExpr e1 then toLean e1 0 else s!"\n{toLean e1 (lvl + 1)}"
        s!"{ind}let _ := {valStr}\n{atLine e2 lvl}"
  /-- Handle seq where the first expression is a fold.
      Binds the fold result to the accumulator variable(s). -/
  seqFold (lvl : Nat) (foldExpr body tail : ImpExpr) : String :=
    let ind := indent lvl
    -- Render fold at current level so the body gets proper nesting,
    -- then strip the leading indent since we place it after 'let acc :='
    let foldStr := (toLean foldExpr lvl).trimLeft
    let accs := extractAccumulators body
    if accs.isEmpty then
      s!"{ind}let _ := {foldStr}\n{atLine tail lvl}"
    else if accs.length == 1 then
      let acc := accs.head!
      -- If the tail just reads the accumulator, the fold IS the return value
      match tail with
      | .var n => if n == acc then toLean foldExpr lvl
                  else s!"{ind}let {sanitizeName acc} := {foldStr}\n{atLine tail lvl}"
      | _ => s!"{ind}let {sanitizeName acc} := {foldStr}\n{atLine tail lvl}"
    else
      let accStr := ", ".intercalate (accs.map sanitizeName)
      s!"{ind}let ({accStr}) := {foldStr}\n{atLine tail lvl}"
  /-- Handle seq where the first expression is a whileFold/whileFoldReturn.
      These return `ControlFlow β α` so we use `.merge` to extract the value.
      We split into two lets to help Lean's type inference. -/
  seqWhileFold (lvl : Nat) (foldExpr body tail : ImpExpr) : String :=
    let ind := indent lvl
    let foldStr := (toLean foldExpr lvl).trimLeft
    let accs := extractWhileAccumulators body
    -- Filter out loop-local variables (same as in toLean whileFold case)
    let localVars := collectLetBindVars body
    let accs := accs.filter fun a => !localVars.contains a
    if accs.isEmpty then
      s!"{ind}let _ := {foldStr}\n{atLine tail lvl}"
    else if accs.length == 1 then
      let acc := accs.head!
      match tail with
      | .var n => if n == acc then s!"{ind}({foldStr}).merge"
                  else s!"{ind}let _wf := {foldStr}\n{ind}let {sanitizeName acc} := _wf.merge\n{atLine tail lvl}"
      | _ => s!"{ind}let _wf := {foldStr}\n{ind}let {sanitizeName acc} := _wf.merge\n{atLine tail lvl}"
    else
      let accStr := ", ".intercalate (accs.map sanitizeName)
      s!"{ind}let _wf := {foldStr}\n{ind}let ({accStr}) := _wf.merge\n{atLine tail lvl}"
  /-- Handle seq where the first expression is a forFoldReturn/forFoldRevReturn.
      These return `ControlFlow β (ControlFlow γ α)`.
      `.Break v` = early return, `.Continue (.Break v)` = loop break,
      `.Continue (.Continue acc)` = loop completed normally.
      When the body has cfBreak (early return), match on the result;
      otherwise fall through to `seqFold`. -/
  seqFoldReturn (lvl : Nat) (foldExpr body tail : ImpExpr) : String :=
    if hasCfBreak body then
      let ind := indent lvl
      let foldStr := (toLean foldExpr lvl).trimLeft
      let accs := extractAccumulators body
      let ind1 := indent (lvl + 1)
      -- Render the tail expression to detect its type for annotations
      let tailStr := (atLine tail (lvl + 1)).trimRight
      if accs.isEmpty then
        -- forFoldReturn returns ControlFlow β (ControlFlow γ Unit)
        -- We need to annotate to fix unresolvable γ
        s!"{ind}let _fr := {foldStr}\n{ind}match (show ControlFlow _ (ControlFlow Unit Unit) from _fr) with\n{ind}| .Break _v => _v\n{ind}| .Continue _ =>\n{atLine tail (lvl + 1)}"
      else
        let accStr := ", ".intercalate (accs.map sanitizeName)
        let destr := if accs.length == 1 then sanitizeName accs.head! else s!"({accStr})"
        -- If the tail is a Bool literal but Break returns Int, wrap in boolToInt
        let tailRendered := match tail with
          | .lit (.bool true) => s!"{ind1}Hax.boolToInt true"
          | .lit (.bool false) => s!"{ind1}Hax.boolToInt false"
          | _ => atLine tail (lvl + 1)
        s!"{ind}let _fr := {foldStr}\n{ind}match _fr with\n{ind}| .Break _v => _v\n{ind}| .Continue _cf =>\n{ind1}let {destr} := _cf.merge\n{tailRendered}"
    else
      seqFold lvl foldExpr body tail

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
    parameters used with index/array_update get `Array Int`, others get no annotation.
    When `fnTypeInfo` is provided, uses real types from hax JSON instead of heuristics. -/
def toLeanDef (name : String) (e : ImpExpr) (annotateTypes : Bool := false)
    (fnTypeInfo : Option HaxAdapter.FnTypeInfo := none)
    (structLookup : String → Option String := fun _ => none) : String :=
  let (params, body) := extractParams e
  let arrayParams := if annotateTypes && fnTypeInfo.isNone then
      (collectArrayParams params body).eraseDups
    else []
  let paramStr := if params.isEmpty then ""
    else " " ++ " ".intercalate (params.map fun p =>
      let sn := sanitizeName p
      -- Use real type from fnTypeInfo when available.
      -- Skip Bool (ImpExpr world uses Int for booleans via Hax.bne x 0).
      -- Skip Tuple (may be pass-through struct resolved to tuple by hax JSON).
      -- Annotate Int, Array, Slice, Adt (via structLookup) to prevent
      -- wrong inference (e.g., u16 param inferred as Array Int).
      match fnTypeInfo >>= fun ti => ti.paramTypes.find? (·.1 == p) with
      | some (_, .unknown) | some (_, .bool) | some (_, .tuple _) =>
        if annotateTypes && arrayParams.contains p then s!"({sn} : Array Int)"
        else sn
      | some (_, ty) =>
        -- In untyped (certified) mode, collapse integer types to Int
        -- to avoid conflicts with untyped runtime ops (Hax.add, etc.)
        let tyStr := ty.toLeanTypeStr structLookup
        if ty.isIntLike then s!"({sn} : Int)"
        else if tyStr == "Int" || tyStr == "Array Int" then s!"({sn} : {tyStr})"
        else if tyStr.startsWith "Array" && !(tyStr.splitOn " × ").length > 1 then s!"({sn} : {tyStr})"
        else if (tyStr.splitOn " × ").length > 1 then s!"({sn} : {tyStr})"  -- struct tuple type
        else sn  -- unknown/complex types: no annotation
      | none =>
        if annotateTypes && arrayParams.contains p then s!"({sn} : Array Int)"
        else sn)
  -- Don't annotate return types — they block param type inference
  -- when not all params are annotated. The param annotations for nested
  -- arrays are sufficient; Lean infers return types from the body.
  let retAnnotation := ""
  let bodyStr := toLean body 1
  s!"def {sanitizeName name}{paramStr}{retAnnotation} :=\n{bodyStr}\n"

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
  s!"def {sanitizeName (name ++ "_impExpr")} : SSProve.Hax.ImpExpr :=\n  {toLeanImpExpr e}\n"

/-! ## Auto-Preamble Generation

Analyzes extracted ImpExpr AST together with struct metadata from the
hax JSON to generate struct definitions, projections, and a dependency
type class for cross-crate function references. -/

/-- Check if a name is a runtime/builtin function (mapped by runtimeName). -/
private def isRuntimeName (f : String) : Bool :=
  match f with
  | "add" | "sub" | "mul" | "div" | "rem" | "neg"
  | "Add" | "Sub" | "Mul" | "Div" | "Rem" | "Neg"
  | "eq" | "Eq" | "ne" | "Ne" | "not" | "Not"
  | "and" | "And" | "or" | "Or" | "&&" | "||"
  | "lt" | "le" | "gt" | "ge" | "Lt" | "Le" | "Gt" | "Ge"
  | "shl" | "shr" | "bitand" | "bitor" | "bitxor" | "bitnot"
  | "Shl" | "Shr" | "BitAnd" | "BitOr" | "BitXor"
  | "index" | "array_lit" | "repeat" | "push" | "len"
  | "rotate_right" | "rotate_left"
  | "wrapping_add" | "wrapping_sub" | "wrapping_mul"
  | "array_update" | "cast" | "castVal"
  | "Some" | "None" | "Ok" | "Err"
  | "panic" | "literal" | "deref" | "copy_from_slice"
  | "extend_from_slice" | "truncate" | "sha256"
  | "with_capacity" | "into_vec" | "into_iter" | "next"
  | "from_elem" | "RangeTo" | "RangeFrom" | "Range" | "min" | "max"
  | "count_ones" | "assert_failed" | "index_mut" | "enumerate"
  | "is_empty" | "from" => true
  | _ => false

/-- Check if a name is ALWAYS a builtin runtime op and NEVER a cross-crate dep.
    This is the exclusion list from `generatePreamble`, factored out for reuse.
    Names like `mul` are NOT here because they can be cross-crate deps. -/
private def isAlwaysBuiltin (f : String) : Bool :=
  match f with
  | "index" | "array_update" | "repeat" | "array_lit" | "push" | "len"
  | "copy_from_slice" | "extend_from_slice" | "truncate"
  | "with_capacity" | "into_vec" | "into_iter" | "next" | "new"
  | "from_elem" | "RangeTo" | "RangeFrom" | "Range"
  | "count_ones" | "assert_failed" | "index_mut" | "enumerate" | "is_empty"
  | "from" | "literal" | "deref" | "cast" | "castVal"
  | "rotate_right" | "rotate_left"
  | "wrapping_add" | "wrapping_sub" | "wrapping_mul"
  | "panic" | "sha256" | "Some" | "None" | "Ok" | "Err"
  | "shl" | "shr" | "Shl" | "Shr"
  | "add" | "sub" | "div" | "rem" | "neg"
  | "Add" | "Sub" | "Div" | "Rem" | "Neg"
  | "bitand" | "bitor" | "bitxor" | "bitnot"
  | "BitAnd" | "BitOr" | "BitXor"
  | "eq" | "Eq" | "ne" | "Ne" | "not" | "Not"
  | "and" | "And" | "or" | "Or" | "&&" | "||"
  | "lt" | "le" | "gt" | "ge" | "Lt" | "Le" | "Gt" | "Ge"
  | "min" | "max" => true
  | _ => false

/-- Check if a name looks like a struct field projection (starts with "." or is "Struct.field"). -/
private def isFieldProjection (f : String) : Bool :=
  f.startsWith "." || f.contains '.'

/-- Collect free variables: `.var` names not bound by enclosing `letBind`.
    Returns (name, 0) pairs so they can be merged with `collectAppCalls` results. -/
private partial def collectFreeVars (bound : List String := []) : ImpExpr → List String
  | .var n => if bound.contains n then [] else [n]
  | .app _ args => args.foldl (fun acc a => acc ++ collectFreeVars bound a) []
  | .letBind n (.var v) body =>
    -- Parameter pattern: letBind n (var n) body — `n` is a param, not a free var
    if n == v then collectFreeVars (n :: bound) body
    else (if bound.contains v then [] else [v]) ++ collectFreeVars (n :: bound) body
  | .letBind n v body =>
    collectFreeVars bound v ++ collectFreeVars (n :: bound) body
  | .seq a b => collectFreeVars bound a ++ collectFreeVars bound b
  | .ifThenElse c t e =>
    collectFreeVars bound c ++ collectFreeVars bound t ++ collectFreeVars bound e
  | .tuple es => es.foldl (fun acc e => acc ++ collectFreeVars bound e) []
  | .proj e _ => collectFreeVars bound e
  | .match_ scrut arms =>
    -- When all arms use .varPat (enum variant match), collect pattern names as free vars
    -- since the surface code converts these to `if Hax.beq scrut VARIANT then ...`
    let allVarPats := arms.all fun (p, _) => match p with
      | .varPat _ => true | .wildcard => true | _ => false
    let patFreeVars := if allVarPats then
      arms.filterMap fun (p, _) => match p with
        | .varPat n => if bound.contains n then none else some n | _ => none
    else []
    collectFreeVars bound scrut ++ patFreeVars ++
    arms.foldl (fun acc (_, b) => acc ++ collectFreeVars bound b) []
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    collectFreeVars bound lo ++ collectFreeVars bound hi ++ collectFreeVars bound body
  | .whileFold c body => collectFreeVars bound c ++ collectFreeVars bound body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    collectFreeVars bound lo ++ collectFreeVars bound hi ++ collectFreeVars bound body
  | .whileFoldReturn c body => collectFreeVars bound c ++ collectFreeVars bound body
  | .cfBreak e | .cfContinue e | .cfBreakContinue e => collectFreeVars bound e
  | _ => []

/-- Collect all (function_name, arg_count) pairs from app calls in an expression. -/
private partial def collectAppCalls : ImpExpr → List (String × Nat)
  | .app f args => (f, args.length) :: args.foldl (fun acc a => acc ++ collectAppCalls a) []
  | .letBind _ v body => collectAppCalls v ++ collectAppCalls body
  | .seq a b => collectAppCalls a ++ collectAppCalls b
  | .ifThenElse c t e => collectAppCalls c ++ collectAppCalls t ++ collectAppCalls e
  | .tuple es => es.foldl (fun acc e => acc ++ collectAppCalls e) []
  | .proj e _ => collectAppCalls e
  | .match_ scrut arms =>
    collectAppCalls scrut ++ arms.foldl (fun acc (_, b) => acc ++ collectAppCalls b) []
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    collectAppCalls lo ++ collectAppCalls hi ++ collectAppCalls body
  | .whileFold c body => collectAppCalls c ++ collectAppCalls body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    collectAppCalls lo ++ collectAppCalls hi ++ collectAppCalls body
  | .whileFoldReturn c body => collectAppCalls c ++ collectAppCalls body
  | .cfBreak e | .cfContinue e | .cfBreakContinue e => collectAppCalls e
  | _ => []

/-- Detect the return tuple arity of a function by analyzing its call sites.
    Pattern: letBind "_tup" (.app f args) (letBind "a" (.proj (.var "_tup") 0) ...)
    Returns max number of projections seen on the result. -/
private partial def detectReturnArity (fname : String) : ImpExpr → Nat
  | .letBind n (.app f _) body =>
    if f == fname then
      -- Count how many projections of `n` follow
      let arity := countProjections n body
      max arity (detectReturnArity fname body)
    else detectReturnArity fname body
  | .letBind _ v body => max (detectReturnArity fname v) (detectReturnArity fname body)
  | .seq a b => max (detectReturnArity fname a) (detectReturnArity fname b)
  | .ifThenElse c t e =>
    max (detectReturnArity fname c) (max (detectReturnArity fname t) (detectReturnArity fname e))
  | .forFold _ _ _ body | .forFoldRev _ _ _ body => detectReturnArity fname body
  | .whileFold c body => max (detectReturnArity fname c) (detectReturnArity fname body)
  | .forFoldReturn _ _ _ body | .forFoldRevReturn _ _ _ body => detectReturnArity fname body
  | .whileFoldReturn c body => max (detectReturnArity fname c) (detectReturnArity fname body)
  | _ => 0
where
  /-- Count consecutive projections of variable `v` in a letBind chain. -/
  countProjections (v : String) : ImpExpr → Nat
    | .letBind _ (.proj (.var n) _) rest =>
      if n == v then 1 + countProjections v rest else 0
    | _ => 0

/-- Detect the types of each component in a tuple-returning dep.
    When `let (a, b) := f x`, trace how `a` and `b` are used to determine
    if each is Int or Array Int. Returns a list of bools (true = Int). -/
private partial def detectReturnComponentTypes (fname : String)
    (knownIntNames : List String) : ImpExpr → List (List Bool)
  | .letBind n (.app f _) body =>
    if f == fname then
      let components := collectProjBindings n body
      if components.isEmpty then
        detectReturnComponentTypes fname knownIntNames body
      else
        let isIntList := components.map fun (compName, _) =>
          isVarUsedAsIntSimple compName body || knownIntNames.contains compName
        [isIntList] ++ detectReturnComponentTypes fname knownIntNames body
    else
      detectReturnComponentTypes fname knownIntNames
        (.letBind n (.lit (.int 0)) body)  -- recurse into body only
  | .letBind _ v body =>
    detectReturnComponentTypes fname knownIntNames v ++
    detectReturnComponentTypes fname knownIntNames body
  | .seq a b =>
    detectReturnComponentTypes fname knownIntNames a ++
    detectReturnComponentTypes fname knownIntNames b
  | .ifThenElse c t e =>
    detectReturnComponentTypes fname knownIntNames c ++
    detectReturnComponentTypes fname knownIntNames t ++
    detectReturnComponentTypes fname knownIntNames e
  | .whileFold c body =>
    detectReturnComponentTypes fname knownIntNames c ++
    detectReturnComponentTypes fname knownIntNames body
  | .forFold _ _ _ body | .forFoldRev _ _ _ body =>
    detectReturnComponentTypes fname knownIntNames body
  | .whileFoldReturn c body =>
    detectReturnComponentTypes fname knownIntNames c ++
    detectReturnComponentTypes fname knownIntNames body
  | .forFoldReturn _ _ _ body | .forFoldRevReturn _ _ _ body =>
    detectReturnComponentTypes fname knownIntNames body
  | _ => []
where
  /-- Collect projection bindings: letBind "a" (proj (var n) 0) ... → [("a", 0), ...] -/
  collectProjBindings (v : String) : ImpExpr → List (String × Nat)
    | .letBind name (.proj (.var n) idx) rest =>
      if n == v then (name, idx) :: collectProjBindings v rest else []
    | _ => []
  /-- Simple check: is the variable used in any Int-context position? -/
  isVarUsedAsIntSimple (varName : String) : ImpExpr → Bool
    | .app f args =>
      let allArgsIntFns := ["add", "sub", "mul", "div", "rem", "neg",
        "Add", "Sub", "Mul", "Div", "Rem", "Neg",
        "lt", "le", "gt", "ge", "eq", "ne", "beq", "bne",
        "Lt", "Le", "Gt", "Ge", "Eq", "Ne",
        "shl", "shr", "Shl", "Shr",
        "bitand", "bitor", "bitxor", "bitnot",
        "BitAnd", "BitOr", "BitXor",
        "wrapping_add", "wrapping_sub", "wrapping_mul",
        "castVal", "cast", "min", "max"]
      let isVar (a : ImpExpr) := match a with
        | ImpExpr.var v => v == varName | _ => false
      let isIntArg := allArgsIntFns.any (f == ·) && args.any isVar
      let posSpecific :=
        (f == "index" || f == "array_update") && args.length > 1 &&
          (match args.toArray[1]? with | some a => isVar a | _ => false)
      (isIntArg || posSpecific) || args.any (isVarUsedAsIntSimple varName)
    | .ifThenElse c t e =>
      isVarUsedAsIntSimple varName c || isVarUsedAsIntSimple varName t ||
      isVarUsedAsIntSimple varName e
    | .letBind _ v body =>
      isVarUsedAsIntSimple varName v || isVarUsedAsIntSimple varName body
    | .seq a b => isVarUsedAsIntSimple varName a || isVarUsedAsIntSimple varName b
    | .whileFold c body =>
      isVarUsedAsIntSimple varName c || isVarUsedAsIntSimple varName body
    | .tuple es => es.any (isVarUsedAsIntSimple varName)
    | _ => false

/-- Check if an ImpExpr is known to have type Int (literal int, int operation, etc.). -/
private def isIntExprBase : ImpExpr → Bool
  | .lit (.int _) => true
  | .lit (.uintLit _ _) => true
  | .lit (.sintLit _ _) => true
  | .lit (.bool _) => true
  | .app f _ => match f with
    | "add" | "sub" | "mul" | "div" | "rem" | "neg"
    | "Add" | "Sub" | "Mul" | "Div" | "Rem" | "Neg"
    -- Indexing returns Int (element of Array Int)
    | "index"
    -- Comparison ops return Bool (treated as Int in untyped)
    | "lt" | "le" | "gt" | "ge" | "Lt" | "Le" | "Gt" | "Ge"
    | "eq" | "Eq" | "ne" | "Ne"
    -- Bitwise ops return Int
    | "shl" | "shr" | "Shl" | "Shr"
    | "bitand" | "bitor" | "bitxor" | "bitnot"
    | "BitAnd" | "BitOr" | "BitXor"
    -- Other Int-returning ops
    | "len" | "count_ones"
    | "wrapping_add" | "wrapping_sub" | "wrapping_mul"
    | "min" | "max"
    -- Cast ops return Int
    | "cast" | "castVal" | "from" => true
    | _ => false
  | _ => false

/-- Compute projection names that return Int from struct metadata. -/
private def intProjNamesFromMeta
    (structMeta : List (String × List (String × String × ImpType))) : List String :=
  structMeta.foldl (fun acc (sname, fields) =>
    acc ++ (fields.filterMap fun (fname, ftag, _) =>
      if ftag == "int" then some s!".{fname}" else none) ++
    (fields.filterMap fun (fname, ftag, _) =>
      if ftag == "int" then some s!"{sname}.{fname}" else none)) []

/-- Check if an expression returns Int, including struct projection awareness. -/
private def isIntExpr (intProjNames : List String := []) : ImpExpr → Bool
  | .app f args => intProjNames.contains f || isIntExprBase (.app f args)
  | e => isIntExprBase e

/-- Check if a free variable is used in Int-context positions
    (as an arg to arithmetic, comparison, repeat_, foldRange, etc.).
    Used to classify 0-arity deps as Int vs Array Int. -/
private partial def isVarUsedAsInt (varName : String) : ImpExpr → Bool
  | .app f args =>
    -- Use raw ImpExpr names (before runtimeName mapping)
    -- Functions where ALL arguments are Int
    let allArgsIntFns := ["add", "sub", "mul", "div", "rem", "neg",
      "Add", "Sub", "Mul", "Div", "Rem", "Neg",
      "lt", "le", "gt", "ge", "eq", "ne",
      "Lt", "Le", "Gt", "Ge", "Eq", "Ne",
      "shl", "shr", "Shl", "Shr",
      "bitand", "bitor", "bitxor", "bitnot",
      "BitAnd", "BitOr", "BitXor",
      "wrapping_add", "wrapping_sub", "wrapping_mul",
      "castVal", "cast", "min", "max"]
    -- Check if an arg matches varName (either as .var or as 0-arity .app)
    let argIsVarName (a : ImpExpr) : Bool := match a with
      | .var v => v == varName
      | .app n [] => n == varName  -- 0-arity call = constant
      | _ => false
    let allArgsInt := allArgsIntFns.any (f == ·) && args.any argIsVarName
    -- Helper: check if arg at position i is .var varName (or 0-arity .app)
    let argIsVar (i : Nat) := match args.toArray[i]? with
      | some a => argIsVarName a
      | _ => false
    -- Position-specific: only certain argument positions are Int
    -- index arr idx → position 1 (idx) is Int
    -- array_update arr idx val → position 1 (idx) is Int
    -- repeat_ val n → position 1 (n) is Int
    -- foldRange lo hi init body → lo (pos 0) and hi (pos 1) are Int
    -- array_lit: if varName is an element, it's used as Int
    -- (array_lit creates Array α; in the untyped pipeline, element-level deps are Int constants)
    let arrayLitInt := f == "array_lit" && args.any argIsVarName
    let posSpecific :=
      (f == "index" || f == "array_update" || f == "index_mut") &&
        args.length > 1 && argIsVar 1
      ||
      (f == "repeat" || f == "repeat_" || f == "from_elem") &&
        args.length > 1 && argIsVar 1
      ||
      (f == "foldRange" || f == "foldRangeRev") &&
        args.length > 0 && (argIsVar 0 || argIsVar 1)
    (allArgsInt || posSpecific || arrayLitInt) || args.any (isVarUsedAsInt varName)
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    (match lo with | .var v => v == varName | _ => false) ||
    (match hi with | .var v => v == varName | _ => false) ||
    isVarUsedAsInt varName lo || isVarUsedAsInt varName hi ||
    isVarUsedAsInt varName body
  | .letBind n (.var v) body =>
    -- If `let n := varName`, check if `n` is used as Int in the body
    if v == varName then isVarUsedAsInt n body
    else isVarUsedAsInt varName body
  | .letBind _ v body => isVarUsedAsInt varName v || isVarUsedAsInt varName body
  | .seq a b => isVarUsedAsInt varName a || isVarUsedAsInt varName b
  | .ifThenElse c t e =>
    isVarUsedAsInt varName c || isVarUsedAsInt varName t || isVarUsedAsInt varName e
  | .whileFold c body => isVarUsedAsInt varName c || isVarUsedAsInt varName body
  | .tuple es => es.any (isVarUsedAsInt varName)
  -- Match arms: if varName appears as a pattern, it's an enum variant (Int)
  | .match_ scrut arms =>
    isVarUsedAsInt varName scrut ||
    arms.any fun (pat, body) =>
      (match pat with | .varPat n => n == varName | _ => false) ||
      isVarUsedAsInt varName body
  | _ => false

/-- Find the most recent binding for a variable name in an expression tree.
    Returns the RHS of the last `letBind varName rhs body` encountered. -/
private partial def findVarBinding' (varName : String) : ImpExpr → Option ImpExpr
  | .letBind n v body =>
    if n == varName then some v
    else findVarBinding' varName body
  | .seq a b => findVarBinding' varName a |>.orElse fun _ => findVarBinding' varName b
  | .ifThenElse _ t e =>
    findVarBinding' varName t |>.orElse fun _ => findVarBinding' varName e
  | .whileFold _ body => findVarBinding' varName body
  | .forFold _ _ _ body | .forFoldRev _ _ _ body => findVarBinding' varName body
  | .forFoldReturn _ _ _ body | .forFoldRevReturn _ _ _ body => findVarBinding' varName body
  | .whileFoldReturn _ body => findVarBinding' varName body
  | .match_ _ arms => arms.findSome? fun (_, b) => findVarBinding' varName b
  | _ => none

/-- Extended isIntExpr that also recognizes .var references to known Int names.
    Optionally resolves local variable bindings via `findVarBinding'`. -/
private def isIntExprCtx (knownIntNames : List String)
    (intProjNames : List String := [])
    (ctx : Option ImpExpr := none) : ImpExpr → Bool
  | .var v =>
    knownIntNames.contains v ||
    -- Resolve local variable bindings through the context
    (match ctx with
     | some c =>
       -- Check if the variable is used as Int elsewhere in the context
       isVarUsedAsInt v c ||
       -- Also check the binding expression
       (match findVarBinding' v c with
       | some (.var w) => knownIntNames.contains w
       | some (.app f _) => knownIntNames.contains f || isIntExprBase (.app f [])
       | some binding => isIntExpr intProjNames binding
       | none => false)
     | none => false)
  | .app f args =>
    -- Check if function name is a known Int-returning name (dep or local def)
    -- But NOT for collection operations that may return arrays depending on args
    if knownIntNames.contains f then true
    else
      -- Exclude index with Range*/RangeTo/RangeFrom args (these are slice ops)
      match f, args with
      | "index", [_, .app "RangeTo" _] | "index", [_, .app "RangeFrom" _]
      | "index", [_, .app "Range" _] => false
      | _, _ => isIntExprBase (.app f args)
  | e => isIntExpr intProjNames e

/-- Check if an expression's terminal value (through let-chains and if-branches) is Int.
    This catches functions like `centered_mod_q` whose body is `let r := ...; if ... then Sub ... else cast ...`
    where the terminal values are Int-returning ops. -/
private partial def isTerminalInt (intProjNames : List String := []) : ImpExpr → Bool
  | .letBind _ _ body => isTerminalInt intProjNames body
  | .ifThenElse _ t e => isTerminalInt intProjNames t && isTerminalInt intProjNames e
  | e => isIntExpr intProjNames e

/-- Detect argument types for a function by analyzing its call sites.
    Returns a list of arg types (per position): true = Int, false = Array Int. -/
private partial def detectArgTypes (fname : String) (arity : Nat)
    (knownIntNames : List String := [])
    (intProjNames : List String := [])
    (fnCtx : Option ImpExpr := none) : ImpExpr → List (List Bool)
  | .app f args =>
    let sub := args.foldl (fun acc a => acc ++ detectArgTypes fname arity knownIntNames intProjNames fnCtx a) []
    if f == fname && args.length == arity then
      [args.map (isIntExprCtx knownIntNames intProjNames fnCtx)] ++ sub
    else sub
  | .letBind _ v body => detectArgTypes fname arity knownIntNames intProjNames fnCtx v ++ detectArgTypes fname arity knownIntNames intProjNames fnCtx body
  | .seq a b => detectArgTypes fname arity knownIntNames intProjNames fnCtx a ++ detectArgTypes fname arity knownIntNames intProjNames fnCtx b
  | .ifThenElse c t e =>
    detectArgTypes fname arity knownIntNames intProjNames fnCtx c ++ detectArgTypes fname arity knownIntNames intProjNames fnCtx t ++ detectArgTypes fname arity knownIntNames intProjNames fnCtx e
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    detectArgTypes fname arity knownIntNames intProjNames fnCtx lo ++ detectArgTypes fname arity knownIntNames intProjNames fnCtx hi ++ detectArgTypes fname arity knownIntNames intProjNames fnCtx body
  | .whileFold c body => detectArgTypes fname arity knownIntNames intProjNames fnCtx c ++ detectArgTypes fname arity knownIntNames intProjNames fnCtx body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    detectArgTypes fname arity knownIntNames intProjNames fnCtx lo ++ detectArgTypes fname arity knownIntNames intProjNames fnCtx hi ++ detectArgTypes fname arity knownIntNames intProjNames fnCtx body
  | .whileFoldReturn c body => detectArgTypes fname arity knownIntNames intProjNames fnCtx c ++ detectArgTypes fname arity knownIntNames intProjNames fnCtx body
  | .tuple es => es.foldl (fun acc e => acc ++ detectArgTypes fname arity knownIntNames intProjNames fnCtx e) []
  | .proj e _ => detectArgTypes fname arity knownIntNames intProjNames fnCtx e
  | .match_ scrut arms =>
    detectArgTypes fname arity knownIntNames intProjNames fnCtx scrut ++ arms.foldl (fun acc (_, b) => acc ++ detectArgTypes fname arity knownIntNames intProjNames fnCtx b) []
  | .cfBreak e | .cfContinue e | .cfBreakContinue e => detectArgTypes fname arity knownIntNames intProjNames fnCtx e
  | _ => []

/-- Find the binding expression for a variable name in a function body.
    Walks letBind nodes to find `let varName := expr` and returns `expr`. -/
private partial def findVarBinding (varName : String) : ImpExpr → Option ImpExpr
  | .letBind n v body =>
    if n == varName then some v
    else findVarBinding varName body
  | .seq a b => findVarBinding varName a |>.orElse fun _ => findVarBinding varName b
  | .ifThenElse _ t e =>
    findVarBinding varName t |>.orElse fun _ => findVarBinding varName e
  | .whileFold _ body => findVarBinding varName body
  | .forFold _ _ _ body | .forFoldRev _ _ _ body => findVarBinding varName body
  | .forFoldReturn _ _ _ body | .forFoldRevReturn _ _ _ body => findVarBinding varName body
  | .whileFoldReturn _ body => findVarBinding varName body
  | .match_ _ arms => arms.findSome? fun (_, b) => findVarBinding varName b
  | _ => none

/-- Infer the ImpType of an expression from known parameter types and common patterns.
    This resolves types through `index`, `repeat_`, struct constructors, etc.
    `fnBody` is the current function body, used to resolve local variable bindings.
    `defsMap` maps mutual def names to their bodies for cross-def resolution. -/
private partial def inferExprType (paramTypeMap : List (String × ImpType))
    (structMeta : List (String × List (String × String × ImpType)) := [])
    (fnBody : Option ImpExpr := none)
    (defsMap : List (String × ImpExpr) := [])
    (depth : Nat := 0) : ImpExpr → Option ImpType
  | .var v =>
    if depth > 5 then none  -- prevent infinite recursion
    else
    -- First check param types (unwrap references)
    match paramTypeMap.find? (·.1 == v) with
    | some (_, ty) => some (match ty with | .ref inner _ => inner | t => t)
    | none =>
      -- Try local binding in function body
      let fromLocal := match fnBody with
        | some body => findVarBinding v body
        | none => none
      match fromLocal with
      | some bindExpr =>
        inferExprType paramTypeMap structMeta fnBody defsMap (depth + 1) bindExpr
      | none =>
        -- Try cross-def resolution (0-arity mutual defs like ZERO_TOKEN)
        match defsMap.find? (·.1 == v) with
        | some (_, defExpr) =>
          inferExprType paramTypeMap structMeta none defsMap (depth + 1) defExpr
        | none => none
  | .lit (.int _) => some .int
  | .lit (.uintLit _ _) => some .int
  | .lit (.bool _) => some .bool
  | .tuple elems =>
    let elemTypes := elems.filterMap (inferExprType paramTypeMap structMeta fnBody defsMap (depth + 1))
    if elemTypes.length == elems.length then some (.tuple elemTypes) else none
  | .app "index" [arr, .app "RangeTo" _] | .app "index" [arr, .app "RangeFrom" _]
  | .app "index" [arr, .app "Range" _]
  | .app "index_mut" [arr, .app "RangeTo" _] | .app "index_mut" [arr, .app "RangeFrom" _]
  | .app "index_mut" [arr, .app "Range" _] =>
    -- Slice operation: returns the same array type (not element type)
    inferExprType paramTypeMap structMeta fnBody defsMap depth arr
  | .app "index" [arr, _] | .app "index_" [arr, _] =>
    match inferExprType paramTypeMap structMeta fnBody defsMap depth arr with
    | some (.array inner _) => some inner
    | some (.slice inner) => some inner
    | _ => none
  | .app "repeat_" [val, _] | .app "repeat" [val, _] | .app "from_elem" [val, _] =>
    match inferExprType paramTypeMap structMeta fnBody defsMap depth val with
    | some t => some (.array t 0)
    | _ => none
  | .app "with_capacity" _ => some (.array .unknown 0)
  | .app "array_update" [arr, _, _] =>
    inferExprType paramTypeMap structMeta fnBody defsMap depth arr
  | .app "push" [arr, _] =>
    inferExprType paramTypeMap structMeta fnBody defsMap depth arr
  | .app sname _ =>
    if structMeta.any (·.1 == sname) then some (.adt sname [])
    else if depth < 3 then
      -- Try resolving through defsMap: if called function's body is Int-valued
      match defsMap.find? (·.1 == sname) with
      | some (_, defBody) =>
        -- Strip params and check if body is Int-valued (through let-chains/branches)
        let rec stripParams : ImpExpr → ImpExpr
          | .letBind _ (.var _) b => stripParams b
          | e => e
        let stripped := stripParams defBody
        if isIntExprBase stripped || isTerminalInt [] stripped then some .int else none
      | none => none
    else none
  | _ => none

/-- Detect typed argument types for a dep by cross-referencing with fnTypes.
    For each call to `fname`, resolve arg types using `inferExprType` which handles
    nested arrays (index into Array (Array T)), struct constructors, etc.
    `fnBody` is the top-level function body for resolving local variable bindings.
    Returns list of (position → ImpType option) per call site. -/
private partial def detectTypedArgs (fname : String) (arity : Nat)
    (paramTypeMap : List (String × ImpType))
    (structMeta : List (String × List (String × String × ImpType)) := [])
    (fnBody : Option ImpExpr := none)
    (defsMap : List (String × ImpExpr) := [])
    : ImpExpr → List (List (Option ImpType))
  | .app f args =>
    let sub := args.foldl (fun acc a => acc ++ detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap a) []
    if f == fname && args.length == arity then
      let argTypes := args.map fun a => inferExprType paramTypeMap structMeta fnBody defsMap 0 a
      [argTypes] ++ sub
    else sub
  | .letBind _ v body =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap v ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap body
  | .seq a b =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap a ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap b
  | .ifThenElse c t e =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap c ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap t ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap e
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap lo ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap hi ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap body
  | .whileFold c body =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap c ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap lo ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap hi ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap body
  | .whileFoldReturn c body =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap c ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap body
  | .tuple es => es.foldl (fun acc e => acc ++ detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap e) []
  | .proj e _ => detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap e
  | .match_ scrut arms =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap scrut ++
    arms.foldl (fun acc (_, b) => acc ++ detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap b) []
  | .cfBreak e | .cfContinue e | .cfBreakContinue e =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap e
  | _ => []

/-- Detect if a function's return value is ever passed to a non-builtin function
    (i.e., another cross-crate dep). If so, it can't safely be typed as Int
    because deps default to Array Int arguments. -/
private partial def detectReturnUsedAsDep (fname : String) (depNames : List String) : ImpExpr → Bool
  | .app f args =>
    let inArgs := args.any (detectReturnUsedAsDep fname depNames)
    let directUse := depNames.contains f && f != fname &&
      args.any fun a => match a with | .app g _ => g == fname | .var v => v == fname | _ => false
    inArgs || directUse
  | .letBind n (.app f _) body =>
    if f == fname then
      -- Check if `n` is used as arg to a dep
      let usedInDep := depNames.any fun d => d != fname &&
        checkVarInDepCall n d body
      usedInDep || detectReturnUsedAsDep fname depNames body
    else detectReturnUsedAsDep fname depNames body
  | .letBind _ v body =>
    detectReturnUsedAsDep fname depNames v || detectReturnUsedAsDep fname depNames body
  | .seq a b =>
    detectReturnUsedAsDep fname depNames a || detectReturnUsedAsDep fname depNames b
  | .ifThenElse c t e =>
    detectReturnUsedAsDep fname depNames c ||
    detectReturnUsedAsDep fname depNames t ||
    detectReturnUsedAsDep fname depNames e
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    detectReturnUsedAsDep fname depNames lo ||
    detectReturnUsedAsDep fname depNames hi ||
    detectReturnUsedAsDep fname depNames body
  | .whileFold c body =>
    detectReturnUsedAsDep fname depNames c || detectReturnUsedAsDep fname depNames body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    detectReturnUsedAsDep fname depNames lo ||
    detectReturnUsedAsDep fname depNames hi ||
    detectReturnUsedAsDep fname depNames body
  | .whileFoldReturn c body =>
    detectReturnUsedAsDep fname depNames c || detectReturnUsedAsDep fname depNames body
  | .tuple es => es.any (detectReturnUsedAsDep fname depNames)
  | .proj e _ => detectReturnUsedAsDep fname depNames e
  | .match_ scrut arms =>
    detectReturnUsedAsDep fname depNames scrut ||
    arms.any fun (_, b) => detectReturnUsedAsDep fname depNames b
  | .cfBreak e | .cfContinue e | .cfBreakContinue e =>
    detectReturnUsedAsDep fname depNames e
  | _ => false
where
  checkVarInDepCall (v : String) (depName : String) : ImpExpr → Bool
    | .app f args => f == depName && args.any (fun a => match a with | .var n => n == v | _ => false)
      || args.any (checkVarInDepCall v depName)
    | .letBind _ val body =>
      checkVarInDepCall v depName val || checkVarInDepCall v depName body
    | .seq a b => checkVarInDepCall v depName a || checkVarInDepCall v depName b
    | .ifThenElse c t e =>
      checkVarInDepCall v depName c || checkVarInDepCall v depName t || checkVarInDepCall v depName e
    | _ => false

/-- Detect if a function's return value is used as an argument to struct constructors.
    If so, it should be Array Int (not Int), since struct fields are typed as Array Int. -/
private partial def detectReturnUsedAsStructArg (fname : String)
    (structNames : List String) : ImpExpr → Bool
  | .app f args =>
    let usedHere := structNames.contains f &&
      args.any fun a => match a with
        | ImpExpr.app g _ => g == fname
        | ImpExpr.var v => v == fname
        | _ => false
    usedHere || args.any (detectReturnUsedAsStructArg fname structNames)
  | .letBind n (.app f _) body =>
    if f == fname then
      -- Check if `n` is used as arg to a struct constructor
      let usedInStruct := structNames.any fun s =>
        checkVarInStructCall n s body
      usedInStruct || detectReturnUsedAsStructArg fname structNames body
    else detectReturnUsedAsStructArg fname structNames body
  | .letBind _ v body =>
    detectReturnUsedAsStructArg fname structNames v ||
    detectReturnUsedAsStructArg fname structNames body
  | .seq a b =>
    detectReturnUsedAsStructArg fname structNames a ||
    detectReturnUsedAsStructArg fname structNames b
  | .ifThenElse c t e =>
    detectReturnUsedAsStructArg fname structNames c ||
    detectReturnUsedAsStructArg fname structNames t ||
    detectReturnUsedAsStructArg fname structNames e
  | .whileFold c body =>
    detectReturnUsedAsStructArg fname structNames c ||
    detectReturnUsedAsStructArg fname structNames body
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    detectReturnUsedAsStructArg fname structNames lo ||
    detectReturnUsedAsStructArg fname structNames hi ||
    detectReturnUsedAsStructArg fname structNames body
  | .tuple es => es.any (detectReturnUsedAsStructArg fname structNames)
  | .cfBreak e | .cfContinue e | .cfBreakContinue e =>
    detectReturnUsedAsStructArg fname structNames e
  | _ => false
where
  checkVarInStructCall (v : String) (structName : String) : ImpExpr → Bool
    | .app f args => f == structName &&
        args.any (fun a => match a with | ImpExpr.var n => n == v | _ => false)
      || args.any (checkVarInStructCall v structName)
    | .letBind _ val body =>
      checkVarInStructCall v structName val || checkVarInStructCall v structName body
    | .seq a b => checkVarInStructCall v structName a || checkVarInStructCall v structName b
    | .ifThenElse c t e =>
      checkVarInStructCall v structName c || checkVarInStructCall v structName t ||
      checkVarInStructCall v structName e
    | _ => false

/-- Detect if a function's return value is ever used in Int context.
    Checks if the result of `fname` is passed as an Int-typed argument to
    known runtime functions (array_update value position, push element, etc.). -/
private partial def detectReturnIsInt (fname : String)
    (paramTypeMap : List (String × ImpType) := [])
    (structMeta : List (String × List (String × String × ImpType)) := [])
    (fnBody : Option ImpExpr := none)
    (defsMap : List (String × ImpExpr) := [])
    : ImpExpr → Bool
  | .app f args =>
    let inArgs := args.any (detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap)
    -- Check if fname's result is used directly as an Int-typed arg
    let directUse := match f with
      -- array_update arr idx val — val is Int only if arr has Int element type (flat)
      -- For nested arrays (Array (Array Int)), val is Array Int, not Int.
      | "array_update" => if args.length == 3 then
          let arrExpr := args.getD 0 (.lit (.int 0))
          let valExpr := args.getD 2 (.lit (.int 0))
          let isValFromFname := match valExpr with | .app g _ => g == fname | _ => false
          if isValFromFname then
            -- Check if the array has a known nested type
            let arrType := inferExprType paramTypeMap structMeta fnBody defsMap 0 arrExpr
            let _ := arrType  -- resolved via inferExprType with fnBody/defsMap
            match arrType with
            | some (.array inner _) | some (.slice inner) =>
              inner.isIntLike
            | _ => true
          else false
        else false
      | "push" => false
      -- Only ARITHMETIC ops that take Int→Int are evidence of Int return.
      -- Comparisons (eq, ne, lt, le, gt, ge) accept any type.
      -- Boolean ops (and, or, not) work on Bool.
      -- So only count add, sub, mul, div, rem, neg, shl, shr, bitand/or/xor,
      -- wrapping_add/sub/mul, min, max as Int-return evidence.
      | "add" | "sub" | "mul" | "div" | "rem" | "neg"
      | "Add" | "Sub" | "Mul" | "Div" | "Rem" | "Neg"
      | "shl" | "shr" | "Shl" | "Shr"
      | "bitand" | "bitor" | "bitxor" | "bitnot"
      | "BitAnd" | "BitOr" | "BitXor"
      | "wrapping_add" | "wrapping_sub" | "wrapping_mul"
      | "min" | "max" =>
        args.any fun a => match a with | .app g _ => g == fname | _ => false
      | _ => false
    inArgs || directUse
  | .letBind _ v body =>
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap v ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap body
  | .seq a b =>
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap a ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap b
  | .ifThenElse c t e =>
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap c ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap t ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap e
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap lo ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap hi ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap body
  | .whileFold c body =>
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap c ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap lo ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap hi ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap body
  | .whileFoldReturn c body =>
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap c ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap body
  | .tuple es => es.any (detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap)
  | .proj e _ => detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap e
  | .match_ scrut arms =>
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap scrut ||
    arms.any fun (_, b) => detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap b
  | .cfBreak e | .cfContinue e | .cfBreakContinue e =>
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap e
  | _ => false

/-- Detect if a function's return value is used as a Bool (if-condition or Bool operator arg).
    Checks if `fname(args...)` appears directly as the condition of `.ifThenElse`,
    or if a let-bound variable of `fname(args...)` is later used as a condition
    or as an argument to Bool operators (&&, ||, band, bor, Not, not). -/
private partial def detectReturnIsBool (fname : String) : ImpExpr → Bool
  | .ifThenElse c t e =>
    let condIsBool := match c with
      | .app f _ => f == fname
      | _ => false
    condIsBool || detectReturnIsBool fname c ||
      detectReturnIsBool fname t || detectReturnIsBool fname e
  | .letBind vn (.app f _) body =>
    if f == fname then
      -- Check if `vn` is used as an if-condition or Bool op arg in the body
      varUsedAsBool vn body || detectReturnIsBool fname body
    else detectReturnIsBool fname body
  | .letBind _ v body => detectReturnIsBool fname v || detectReturnIsBool fname body
  | .app f args =>
    -- Direct use: fname's result passed directly to a Bool op
    let directBool := isBoolOp f && args.any fun a => match a with
      | .app g _ => g == fname
      | _ => false
    directBool || args.any (detectReturnIsBool fname)
  | .seq a b => detectReturnIsBool fname a || detectReturnIsBool fname b
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    detectReturnIsBool fname lo || detectReturnIsBool fname hi || detectReturnIsBool fname body
  | .whileFold c body => detectReturnIsBool fname c || detectReturnIsBool fname body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    detectReturnIsBool fname lo || detectReturnIsBool fname hi || detectReturnIsBool fname body
  | .whileFoldReturn c body => detectReturnIsBool fname c || detectReturnIsBool fname body
  | .tuple es => es.any (detectReturnIsBool fname)
  | .proj e _ => detectReturnIsBool fname e
  | .match_ scrut arms =>
    detectReturnIsBool fname scrut || arms.any fun (_, b) => detectReturnIsBool fname b
  | .cfBreak e | .cfContinue e | .cfBreakContinue e => detectReturnIsBool fname e
  | _ => false
where
  isBoolOp : String → Bool
    | "&&" | "||" | "band" | "bor" | "Not" | "not" | "!" => true
    | _ => false
  /-- Check if a variable name is used as an if-condition or Bool operator argument. -/
  varUsedAsBool (vn : String) : ImpExpr → Bool
    | .ifThenElse (.var v) t e => v == vn || varUsedAsBool vn t || varUsedAsBool vn e
    | .ifThenElse c t e => varUsedAsBool vn c || varUsedAsBool vn t || varUsedAsBool vn e
    | .letBind _ v body => varUsedAsBool vn v || varUsedAsBool vn body
    | .seq a b => varUsedAsBool vn a || varUsedAsBool vn b
    | .app f args =>
      let argIsBool := isBoolOp f && args.any fun a => match a with
        | .var n => n == vn
        | _ => false
      argIsBool || args.any (varUsedAsBool vn)
    | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
      varUsedAsBool vn lo || varUsedAsBool vn hi || varUsedAsBool vn body
    | .whileFold c body => varUsedAsBool vn c || varUsedAsBool vn body
    | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
      varUsedAsBool vn lo || varUsedAsBool vn hi || varUsedAsBool vn body
    | .whileFoldReturn c body => varUsedAsBool vn c || varUsedAsBool vn body
    | .tuple es => es.any (varUsedAsBool vn)
    | .cfBreak e | .cfContinue e | .cfBreakContinue e => varUsedAsBool vn e
    | _ => false

/-- Struct metadata: name → list of (field_name, type_tag, impType).
    Type tags: "int" → Int, "array" → Array Int, or a struct name for nested structs.
    impType carries the full parsed Rust type for precision (nested arrays, tuples, etc.). -/
abbrev StructMeta' := List (String × List (String × String × ImpType))

/-- Detect if a dep's return value is used with struct projections or as a
    struct constructor argument. If so, returns the struct name (or the expected
    field type name for struct constructor arguments). -/
private partial def detectReturnStructType (depName : String)
    (structMeta : StructMeta') : ImpExpr → Option String
  | .letBind varName (.app f _) body =>
    if f == depName then
      -- Check if varName is used with any struct projection
      let projResult := structMeta.findSome? fun (sname, fields) =>
        let fieldNames := fields.map (·.1)
        let projUsed := fieldNames.any fun fname =>
          hasAppOnVar s!".{fname}" varName body ||
          hasAppOnVar s!"{sname}.{fname}" varName body
        if projUsed then some sname else none
      match projResult with
      | some s => some s
      | none =>
        -- Check if varName is used as an argument to a struct constructor
        let ctorResult := structMeta.findSome? fun (sname, fields) =>
          findVarAsStructCtorArg sname fields varName body
        match ctorResult with
        | some s => some s
        | none => detectReturnStructType depName structMeta body
    else detectReturnStructType depName structMeta body
  | .letBind _ v body =>
    (detectReturnStructType depName structMeta v).orElse fun _ =>
    detectReturnStructType depName structMeta body
  | .seq a b =>
    (detectReturnStructType depName structMeta a).orElse fun _ =>
    detectReturnStructType depName structMeta b
  | .ifThenElse c t e =>
    (detectReturnStructType depName structMeta c).orElse fun _ =>
    (detectReturnStructType depName structMeta t).orElse fun _ =>
    detectReturnStructType depName structMeta e
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    (detectReturnStructType depName structMeta lo).orElse fun _ =>
    (detectReturnStructType depName structMeta hi).orElse fun _ =>
    detectReturnStructType depName structMeta body
  | .whileFold c body =>
    (detectReturnStructType depName structMeta c).orElse fun _ =>
    detectReturnStructType depName structMeta body
  | _ => none
where
  /-- Check if `.app projName [.var varName]` appears in an expression. -/
  hasAppOnVar (projName : String) (varName : String) : ImpExpr → Bool
    | .app f [.var v] => (f == projName && v == varName) ||
        hasAppOnVar projName varName (.var v)
    | .app _ args => args.any (hasAppOnVar projName varName)
    | .letBind _ v body =>
      hasAppOnVar projName varName v || hasAppOnVar projName varName body
    | .seq a b => hasAppOnVar projName varName a || hasAppOnVar projName varName b
    | .ifThenElse c t e =>
      hasAppOnVar projName varName c || hasAppOnVar projName varName t ||
      hasAppOnVar projName varName e
    | .tuple es => es.any (hasAppOnVar projName varName)
    | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
      hasAppOnVar projName varName lo || hasAppOnVar projName varName hi ||
      hasAppOnVar projName varName body
    | .whileFold c body =>
      hasAppOnVar projName varName c || hasAppOnVar projName varName body
    | _ => false
  /-- Check if `.var varName` is used as an argument to struct constructor `sname`.
      If found, return the struct name of the field's type at that arg position
      (for Adt-typed fields). -/
  findVarAsStructCtorArg (sname : String) (fields : List (String × String × ImpType))
      (varName : String) : ImpExpr → Option String
    | .app f args =>
      if f == sname then
        -- Check if any argument is .var varName
        let indexed := (List.range args.length).zip args
        let result := indexed.findSome? fun (i, a) =>
          match a with
          | .var v =>
            if v == varName then
              -- Get the field type at this position
              match fields[i]? with
              | some (_, _, ImpType.adt adtName _) => some adtName
              | _ => none
            else none
          | _ => none
        match result with
        | some s => some s
        | none => args.findSome? (findVarAsStructCtorArg sname fields varName)
      else args.findSome? (findVarAsStructCtorArg sname fields varName)
    | .letBind _ v body =>
      (findVarAsStructCtorArg sname fields varName v).orElse fun _ =>
      findVarAsStructCtorArg sname fields varName body
    | .seq a b =>
      (findVarAsStructCtorArg sname fields varName a).orElse fun _ =>
      findVarAsStructCtorArg sname fields varName b
    | .ifThenElse c t e =>
      (findVarAsStructCtorArg sname fields varName c).orElse fun _ =>
      (findVarAsStructCtorArg sname fields varName t).orElse fun _ =>
      findVarAsStructCtorArg sname fields varName e
    | .tuple es => es.findSome? (findVarAsStructCtorArg sname fields varName)
    | _ => none

abbrev StructMeta := StructMeta'

/-- Recursively resolve a struct name to its Lean tuple type string.
    Handles nested structs: if struct A has a field of type struct B,
    resolves B's tuple type first. Requires acyclic struct definitions. -/
private partial def resolveStructType (structMeta : StructMeta) (name : String)
    : Option String :=
  match structMeta.find? (·.1 == name) with
  | some (_, fields) =>
    let lookup := resolveStructType structMeta
    let resolveField := fun (_fname : String) (tag : String) (impTy : ImpType) =>
      match impTy with
      | .unknown => if tag == "int" then "Int" else "Array Int"
      | ty => ty.toLeanTypeStr lookup
    if fields.length == 0 then some "Array Int"
    else if fields.length == 1 then
      let (fn, tag, ty) := fields.head!
      some (resolveField fn tag ty)
    else
      let fieldTypes := fields.map fun (fn, t, ty) =>
        let s := resolveField fn t ty
        if (s.splitOn " × ").length > 1 then s!"({s})" else s
      some (" × ".intercalate fieldTypes)
  | none => none

/-- Resolve a type tag to a Lean type string.
    When `impTy` is available (not `.unknown`), uses the full type info for precision.
    Otherwise falls back to heuristic: "int" → Int, everything else → Array Int. -/
private def typeTagToLean (_structs : StructMeta) (tag : String)
    (impTy : ImpType := .unknown)
    (structLookup : String → Option String := fun _ => none) : String :=
  match impTy with
  | .unknown => if tag == "int" then "Int" else "Array Int"
  | ty => ty.toLeanTypeStr structLookup

/-- Generate the tuple type for a struct given its fields.
    Composite field types (containing ×) are parenthesized to preserve associativity. -/
private def structTupleType (structs : StructMeta)
    (fields : List (String × String × ImpType))
    (structLookup : String → Option String := fun _ => none) : String :=
  if fields.length == 0 then "Array Int"
  else if fields.length == 1 then
    let (_, tag, ty) := fields.head!
    typeTagToLean structs tag ty structLookup
  else
    let fieldTypes := fields.map fun (_, t, ty) =>
      let s := typeTagToLean structs t ty structLookup
      -- Wrap composite types in parens to preserve tuple associativity
      if (s.splitOn " × ").length > 1 then s!"({s})" else s
    " × ".intercalate fieldTypes

/-- Generate the projection path for field index i out of N fields.
    0-indexed. Right-associated tuples: (A × B × C) = (A × (B × C)). -/
private def projPath (i n : Nat) : String :=
  if n <= 1 then ""
  else if i == 0 then ".1"
  else if n == 2 then ".2"
  else ".2" ++ projPath (i - 1) (n - 1)

/-- Check if a variable bound to a struct constructor call is ever passed
    to a non-projection function (i.e., used externally where Array Int is expected).
    This detects patterns like:
      let transcript := OekeTranscript a b c d
      pake_hash transcript shared   ← transcript passed to dep expecting Array Int -/
private partial def checkStructPassedExternally
    (structName : String) (fields : List (String × String × ImpType)) : ImpExpr → Bool
  | .letBind varName (.app ctor _) body =>
    if ctor == structName then
      -- Check if varName is used as arg to any non-projection function
      let projNames := fields.map fun (f, _) => s!".{f}"
      varUsedInNonProjection varName projNames body ||
        checkStructPassedExternally structName fields body
    else checkStructPassedExternally structName fields body
  | .letBind _ v body =>
    checkStructPassedExternally structName fields v ||
    checkStructPassedExternally structName fields body
  | .seq a b =>
    checkStructPassedExternally structName fields a ||
    checkStructPassedExternally structName fields b
  | .ifThenElse c t e =>
    checkStructPassedExternally structName fields c ||
    checkStructPassedExternally structName fields t ||
    checkStructPassedExternally structName fields e
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    checkStructPassedExternally structName fields lo ||
    checkStructPassedExternally structName fields hi ||
    checkStructPassedExternally structName fields body
  | .whileFold c body =>
    checkStructPassedExternally structName fields c ||
    checkStructPassedExternally structName fields body
  | .app _ args => args.any (checkStructPassedExternally structName fields)
  | .tuple es => es.any (checkStructPassedExternally structName fields)
  | .proj e _ => checkStructPassedExternally structName fields e
  | _ => false
where
  /-- Check if variable `v` appears as an argument to any function
      that is NOT a field projection of this struct. -/
  varUsedInNonProjection (v : String) (projNames : List String) : ImpExpr → Bool
    | .app f args =>
      let directUse := !projNames.contains f &&
        !isFieldProjection f &&
        args.any fun a => match a with | .var n => n == v | _ => false
      directUse || args.any (varUsedInNonProjection v projNames)
    | .letBind _ val body =>
      varUsedInNonProjection v projNames val ||
      varUsedInNonProjection v projNames body
    | .seq a b =>
      varUsedInNonProjection v projNames a ||
      varUsedInNonProjection v projNames b
    | .ifThenElse c t e =>
      varUsedInNonProjection v projNames c ||
      varUsedInNonProjection v projNames t ||
      varUsedInNonProjection v projNames e
    | .tuple es => es.any (varUsedInNonProjection v projNames)
    | .proj e _ => varUsedInNonProjection v projNames e
    | _ => false

/-- Compute which structs are pass-through (used as opaque values passed to deps).
    A struct is pass-through if:
    1. Its constructor is called and the result flows to non-projection deps, OR
    2. Its constructor is never called (projections become identity on Array Int).
    EXCEPTION: A struct is NEVER pass-through if its field projections are used
    in the code, because pass-through collapses the struct to `Array Int` and
    projections then have the wrong type. -/
private def computeStructPassthrough (structMeta : StructMeta)
    (defs : List (String × ImpExpr)) : List (String × Bool) :=
  let allCalls := defs.foldl (fun acc (_, e) => acc ++ collectAppCalls e) []
  let allAppNames := allCalls.map (·.1) |>.eraseDups
  -- Phase 1: initial pass-through computation
  let initial := structMeta.map fun (sname, fields) =>
    if fields.length <= 1 then (sname, false)
    else
      -- Check if any field projection is used in the code
      let projUsed := fields.any fun (fname, _, _) =>
        allAppNames.contains s!".{fname}" || allAppNames.contains s!"{sname}.{fname}"
      -- If projections are used, NEVER make pass-through (the struct needs tuple type)
      if projUsed then (sname, false)
      else
        let isUsed := allAppNames.contains sname
        if !isUsed then
          -- Constructor never called, no projections used → pass-through
          (sname, true)
        else
          let usedExternally := defs.any fun (_, e) =>
            checkStructPassedExternally sname fields e
          (sname, usedExternally)
  -- Phase 2: propagate — if struct A has a field of struct B type,
  -- and A is not pass-through, then B must also not be pass-through
  -- (its tuple type is needed for the nested field access).
  let rec propagate (pt : List (String × Bool)) (fuel : Nat) : List (String × Bool) :=
    match fuel with
    | 0 => pt
    | fuel + 1 =>
      let anyChanged := false
      let changed := pt.map fun (sname, isPt) =>
        if !isPt then (sname, false)  -- already not pass-through
        else
          -- Check if this struct is used as a field type of any non-pass-through struct
          let usedInNonPt := structMeta.any fun (otherName, otherFields) =>
            let otherIsPt := (pt.find? fun (n, _) => n == otherName).map (·.2) |>.getD true
            !otherIsPt && otherFields.any fun (_, tag, _) => tag == sname
          if usedInNonPt then (sname, false) else (sname, true)
      -- Check if anything changed (any pass-through became non-pass-through)
      let anyFlipped := changed.any fun (sname, isPt) =>
        let oldPt := (pt.find? fun (n, _) => n == sname).map (·.2) |>.getD true
        oldPt != isPt
      if anyFlipped then propagate changed fuel else pt
  propagate initial structMeta.length

/-- Build a struct lookup that maps pass-through structs to "Array Int"
    and resolves other structs to their tuple types. -/
private def mkStructLookup (structMeta : StructMeta)
    (passthrough : List (String × Bool)) : String → Option String :=
  fun name =>
    if passthrough.any fun (n, pt) => n == name && pt then some "Array Int"
    else resolveStructType structMeta name

/-- Generate auto-preamble: struct definitions, projections, and dependency class.
    `structMeta`: struct definitions from hax JSON (name → [(field_name, type_tag)])
    `defs`: the extracted ImpExpr function definitions
    `fnTypes`: per-function type info from hax JSON (for typed dep signatures) -/
def generatePreamble (defs : List (String × ImpExpr))
    (moduleName : String) (structMeta : StructMeta := [])
    (fnTypes : List (String × HaxAdapter.FnTypeInfo) := [])
    (callRetTypes : List (String × ImpType) := [])
    : String × List (String × String) :=
  let definedNames := defs.map (·.1)
  -- Collect all app calls across all definitions
  let allCalls := defs.foldl (fun acc (_, e) => acc ++ collectAppCalls e) []
  let allAppNames := allCalls.map (·.1) |>.eraseDups
  -- Known struct names from metadata
  let structNames := structMeta.map (·.1)
  -- Determine which struct constructors are "safe" for tuple representation.
  -- Compute pass-through info and build struct lookup
  let structIsPassthrough := computeStructPassthrough structMeta defs
  let structLookup := mkStructLookup structMeta structIsPassthrough
  -- Sort struct metadata: largest (most fields) first, so their projections get priority
  -- when there are field name conflicts across structs.
  let sortedStructMeta := structMeta.toArray.qsort (fun a b => a.2.length > b.2.length) |>.toList
  -- Generate struct constructor + projection definitions
  -- Track emitted projection names to avoid duplicates
  -- projConflicts: list of (unqualifiedName, qualifiedName) for conflicting projections
  -- These need to be rewritten in function bodies.
  let (structDefs, _, projConflicts) := sortedStructMeta.foldl (fun (acc, emittedProjs, conflicts) (sname, fields) =>
    if fields.isEmpty then (acc, emittedProjs, conflicts)
    else
      -- Check if this struct constructor is actually called in the code
      let isUsed := allAppNames.contains sname
      let isPassthrough := structIsPassthrough.any fun (n, pt) => n == sname && pt
      let tupleT := structTupleType structMeta fields structLookup
      -- Constructor definition (only if used in code)
      let ctorDefs := if isUsed then
        if isPassthrough then
          -- Pass-through: struct constructor is identity (returns first Array Int arg)
          let paramDecls := fields.map fun (fname, ftag, fty) =>
            let leanType := typeTagToLean structMeta ftag fty structLookup
            s!"({sanitizeName fname} : {leanType})"
          let paramStr := " ".intercalate paramDecls
          -- Return first Array Int field as the "representative" value
          let arrayField := (fields.find? fun (_, ftag, _) => ftag != "int").map (·.1)
          let retField := sanitizeName (arrayField.getD fields.head!.1)
          [s!"/-- Struct constructor (pass-through, auto-generated). -/\ndef {sanitizeName sname} {paramStr} : Array Int := {retField}"]
        else
          let paramDecls := fields.map fun (fname, ftag, fty) =>
            let leanType := typeTagToLean structMeta ftag fty structLookup
            s!"({sanitizeName fname} : {leanType})"
          let paramStr := " ".intercalate paramDecls
          let tupleStr := ", ".intercalate (fields.map fun (fname, _, _) => sanitizeName fname)
          let ctorDef := if fields.length == 1 then
              s!"def {sanitizeName sname} {paramStr} : {tupleT} := {sanitizeName fields.head!.1}"
            else
              s!"def {sanitizeName sname} {paramStr} : {tupleT} := ({tupleStr})"
          [s!"/-- Struct constructor + projections (auto-generated from Rust struct). -/\n{ctorDef}"]
      else []
      -- Projections: if struct is used with tuple type, project from tuple;
      -- if pass-through or unused, identity on Array Int
      -- Emit projections: check for both unqualified (.field) and qualified (Struct.field) names
      let (projDefs, emittedProjs') := (fields.zip (List.range fields.length)).foldl
        (fun (pdefs, ep) ((fname, ftag, fty), i) =>
          let projName := s!".{fname}"
          let qualName := s!"{sname}.{fname}"
          let unqualUsed := allAppNames.contains projName
          let qualUsed := allAppNames.contains qualName
          if unqualUsed || qualUsed then
            -- Determine which name to emit this projection under
            let emitName := if qualUsed then qualName else projName
            if !ep.contains projName then
              -- First struct to emit this projection (gets the chosen name)
              if !isPassthrough then
                let path := projPath i fields.length
                (pdefs ++ [s!"def «{emitName}» (x : {tupleT}) := x{path}"], ep ++ [projName])
              else
                (pdefs ++ [s!"def «{emitName}» (x : Array Int) := x"], ep ++ [projName])
            else
              -- Conflict: always emit with qualified name
              if !isPassthrough then
                let path := projPath i fields.length
                (pdefs ++ [s!"def «{qualName}» (x : {tupleT}) := x{path}"], ep)
              else
                (pdefs ++ [s!"def «{qualName}» (x : Array Int) := x"], ep)
          else (pdefs, ep))
        ([], emittedProjs)
      -- Collect conflicts: where unqualified is used but conflicts with a prior struct
      let newConflicts := (fields.zip (List.range fields.length)).foldl
        (fun cs ((fname, _, _), _) =>
          let projName := s!".{fname}"
          let qualName := s!"{sname}.{fname}"
          let unqualUsed := allAppNames.contains projName
          if unqualUsed && emittedProjs.contains projName then
            cs ++ [(projName, qualName)]
          else cs) ([] : List (String × String))
      (acc ++ ctorDefs ++ projDefs, emittedProjs', conflicts ++ newConflicts))
    ([], ([] : List String), ([] : List (String × String)))
  -- Collect free variables that appear as .var (not .app) — these are 0-arity deps
  -- like AES_SBOX, AEGIS_C0, etc. that aren't function calls
  let allFreeVars := defs.foldl (fun acc (fname, e) =>
    -- Function parameters are the top-level letBind names; collectFreeVars handles them
    -- We pass function name as bound since it refers to itself
    acc ++ collectFreeVars [fname] e) ([] : List String)
  let freeVarDeps := allFreeVars.eraseDups.filter fun v =>
    !definedNames.contains v &&
    !structNames.contains v && !isFieldProjection v &&
    -- Don't filter by isAlwaysBuiltin here: free vars (.var references) are NOT
    -- runtime function calls. Names like "Or", "And" can be enum variant constants
    -- even though they collide with runtime operator names. The !allAppNames check
    -- below ensures we don't double-count names that are also app calls.
    !allAppNames.contains v  -- not already collected as an app call
  -- Merge free vars as 0-arity calls
  let allCallsWithVars := allCalls ++ freeVarDeps.map (·, 0)
  let allNamesWithVars := (allAppNames ++ freeVarDeps).eraseDups
  -- Cross-crate dependencies: names that are called but not defined locally,
  -- not struct constructors, and not projections.
  -- Include runtime names that collide (e.g., `mul` used as a protocol dependency)
  -- For free-var-only deps (enum variant constants like Or, And), don't filter
  -- by isAlwaysBuiltin since they're values, not runtime function calls.
  let deps := allNamesWithVars.filter fun f =>
    !definedNames.contains f &&
    !structNames.contains f && !isFieldProjection f &&
    (!isAlwaysBuiltin f || freeVarDeps.contains f)
  -- Compute max arity for each dependency
  let depArities := deps.map fun d =>
    let arities := allCallsWithVars.filter (·.1 == d) |>.map (·.2)
    let maxArity := arities.foldl (fun acc a => max acc a) 0
    (d, maxArity)
  -- Build a combined map of all param types from fnTypes for typed arg detection
  let allParamTypes := fnTypes.foldl (fun acc (_, ti) => acc ++ ti.paramTypes) []
  -- Compute struct projection names that return Int
  let intProjNames := intProjNamesFromMeta structMeta
  -- Collect locally-defined names whose bodies are Int-valued (plain Int literals or simple
  -- arithmetic). This lets detectArgTypes resolve .var references to local constants.
  let knownIntNames := defs.filterMap fun (name, body) =>
    -- Strip top-level parameter bindings (letBind x (.var x) body)
    let rec stripParams : ImpExpr → ImpExpr
      | .letBind _ (.var _) b => stripParams b
      | e => e
    let stripped := stripParams body
    -- Check direct Int expression, or check terminal values of branches
    if isIntExpr intProjNames stripped || isTerminalInt intProjNames stripped
    then some name else none
  -- Generate deps class
  let depsStr := if depArities.isEmpty then ""
    else
      let depsClassName := s!"{moduleName}Deps"
      -- Detect return tuple arities and argument types by scanning call sites
      let allExprs := defs.map (·.2)
      -- Pre-pass: iteratively detect which deps return Int.
      -- Each round discovers new Int-returning deps and adds them to knownIntNames.
      -- This resolves circular dep chains (exp returns Int, group_op takes exp's result as Int).
      let depNamesList := depArities.map (·.1)
      -- Also detect deps returning Int from call-site return types
      let intReturnDepsFromCallRet := callRetTypes.filterMap fun (d, ty) =>
        if ty.isIntLike && depNamesList.contains d then some d else none
      -- Names that should NEVER be classified as Int-returning (collection operations)
      let collectionOps := ["iter", "map", "collect", "filter", "zip", "fold",
        "flat_map", "chain", "take", "skip", "enumerate", "rev", "sort",
        "into_iter", "next", "deref"]
      let rec iterateIntDeps (known : List String) (fuel : Nat) : List String :=
        match fuel with
        | 0 => known
        | fuel + 1 =>
          let newIntDeps := depArities.filterMap fun (d, _) =>
            if known.contains d || collectionOps.contains d then none
            else
              let retArity := allExprs.foldl (fun acc e => max acc (detectReturnArity d e)) 0
              -- Check usage as Int with current known set
              let retIsIntDirect := retArity < 2 &&
                allExprs.any (detectReturnIsInt d allParamTypes structMeta (some (ImpExpr.lit (.int 0))) defs.toArray.toList) &&
                !allExprs.any (detectReturnUsedAsDep d depNamesList) &&
                !allExprs.any (detectReturnUsedAsStructArg d structNames)
              -- Also check: if ALL args are known Int or other known-Int deps/constants
              let allArgsKnownInt := retArity < 2 && depArities.any fun (d', arity') =>
                d' == d && arity' > 0 &&
                  let argTypes := allExprs.foldl (fun acc e =>
                    acc ++ detectArgTypes d arity' known intProjNames (some e) e) ([] : List (List Bool))
                  argTypes.length > 0 && argTypes.all fun ct => ct.all id
              if retIsIntDirect || allArgsKnownInt then some d else none
          if newIntDeps.isEmpty then known
          else iterateIntDeps (known ++ newIntDeps) fuel
      let knownIntNames := iterateIntDeps
        (knownIntNames ++ intReturnDepsFromCallRet) 5
      let fields := depArities.map fun (d, arity) =>
        -- Check if any call site destructures the result as a tuple
        let retArity := allExprs.foldl (fun acc e =>
          max acc (detectReturnArity d e)) 0
        -- Check if return value is used in Int context
        -- BUT: if the result is also passed to another dep (which expects Array Int),
        -- don't mark as Int to avoid type conflicts.
        let retIsInt := retArity < 2 &&
          !collectionOps.contains d &&
          allExprs.any (detectReturnIsInt d allParamTypes structMeta) &&
          !allExprs.any (detectReturnUsedAsDep d depNamesList)
        -- Check if return value is used as a Bool (if-condition)
        let retIsBool := retArity < 2 && !retIsInt &&
          allExprs.any (detectReturnIsBool d)
        -- Check if return value is used with struct projections
        let retStructName := allExprs.findSome? (detectReturnStructType d structMeta)
        let retStructType := retStructName.bind structLookup
        -- First check: use call-site return type from hax JSON if available
        let callRetType := callRetTypes.find? (·.1 == d) |>.map (·.2)
        let retType := match callRetType with
          | some ty =>
            let s := ty.toLeanTypeStr structLookup
            -- Only use typed return if it resolves to a concrete type (not unknown/Unit)
            if s != "Unit" && s != "()" && !ty.isUnknown then s
            else match retStructType with
              | some st => st
              | none => if retIsBool then "Bool" else if retIsInt then "Int" else "Array Int"
          | none => match retStructType with
          | some st => st  -- Use the resolved struct tuple type
          | none =>
            if retArity >= 2 then
              -- Analyze each tuple component's type from usage context
              let compTypes := allExprs.foldl (fun acc e =>
                acc ++ detectReturnComponentTypes d knownIntNames e) []
              -- For each position, if ALL call sites agree it's Int, use Int
              let componentIsInt := (List.range retArity).map fun i =>
                compTypes.length > 0 &&
                compTypes.all fun ct => ct.getD i false
              " × ".intercalate (componentIsInt.map fun isInt =>
                if isInt then "Int" else "Array Int")
            else if retIsBool then "Bool"
            else if retIsInt then "Int"
            else "Array Int"
        if arity == 0 then
          -- For 0-arity free-variable deps, also check if used in Int contexts
          -- (e.g., as array size in repeat_, loop bound in foldRange)
          -- Also check if used with struct projections (needs struct tuple type)
          let finalRetType :=
            -- First check struct type from projections or constructor context
            match retStructType with
            | some st => st
            | none =>
              if retType == "Array Int" then
                -- Check direct struct projection usage: is dep var used as arg to projections?
                let structTypeFromVar := allExprs.findSome? fun e =>
                  structMeta.findSome? fun ((sname, fields) : String × List (String × String × ImpType)) =>
                    let projUsed : Bool := fields.any fun (fname, _, _) =>
                      checkProjOnVar d s!".{fname}" e ||
                      checkProjOnVar d s!"{sname}.{fname}" e
                    if projUsed == true then structLookup sname else none
                match structTypeFromVar with
                | some st => st
                | none =>
                  let usedAsInt := allExprs.any (isVarUsedAsInt d)
                  if usedAsInt then "Int" else retType
              else retType
          s!"  {sanitizeName d} : {finalRetType}"
        else
          -- Detect which arguments are Int vs Array Int (heuristic)
          let allArgTypes := allExprs.foldl (fun acc e =>
            acc ++ detectArgTypes d arity knownIntNames intProjNames (some e) e) []
          let argIsIntArr := (List.range arity).map fun i =>
            allArgTypes.length > 0 &&
            allArgTypes.all fun callArgs =>
              callArgs.getD i false
          -- Also detect typed args from fnTypes cross-referencing
          let typedArgResults := defs.foldl (fun acc (fnName, e) =>
            let paramMap := match fnTypes.find? (·.1 == fnName) with
              | some (_, ti) => ti.paramTypes
              | none => []
            acc ++ detectTypedArgs d arity paramMap structMeta (some e) defs e) ([] : List (List (Option ImpType)))
          -- For each position, find typed arg info (first known type wins)
          -- Skip Bool (ImpExpr uses Int for booleans) and Tuple (may be pass-through struct)
          let typedArgTypes := (List.range arity).map fun i =>
            typedArgResults.findSome? fun callArgs =>
              match callArgs.getD i none with
              | some .unknown | some .bool | some (.tuple _) => none
              | some ty => some ty
              | none => none
          -- Use single letter params for readability
          let letters := #["a", "b", "c", "d", "e", "f", "g", "h"]
          -- Heuristic: when a dep returns Int/Bool, unresolved args default to Int
          -- (scalar/group ops uniformly work on field elements)
          let defaultArgType := if retType == "Int" || retType == "Bool" then "Int" else "Array Int"
          let paramStr := (List.range arity).map (fun i =>
            let letter := if h : i < letters.size then letters[i] else s!"x{i}"
            -- Prefer typed arg info over heuristic
            let ty := match typedArgTypes.getD i none with
              | some impTy => impTy.toLeanTypeStr structLookup
              | none => if argIsIntArr.getD i false then "Int" else defaultArgType
            s!"({letter} : {ty})") |> " ".intercalate
          s!"  {sanitizeName d} {paramStr} : {retType}"
      let exportList := depArities.map (fun (d, _) => sanitizeName d) |> " ".intercalate
      s!"/-- External dependencies for {moduleName} extraction (auto-generated). -/\nclass {depsClassName} where\n{"\n".intercalate fields}\n\nexport {depsClassName} ({exportList})\n\nvariable [{depsClassName}]\n"
  -- Assemble preamble
  let parts := (if structDefs.isEmpty then [] else structDefs) ++
               (if depsStr.isEmpty then [] else [depsStr])
  let result := if parts.isEmpty then ""
    else "\n" ++ "\n\n".intercalate parts ++ "\n"
  (result, projConflicts)

/-- Post-process generated code: replace `Hax.{dep}` with bare `{dep}` for dependency names.
    This is needed because `runtimeName` maps names like `mul` to `Hax.mul`, but when
    `mul` is a cross-crate dependency (exported by the Deps class), we need the bare name. -/
private def fixDepReferences (code : String) (depNames : List String) : String :=
  depNames.foldl (fun acc dep =>
    -- Replace "Hax.{dep}" with "{dep}" only when followed by a word boundary
    -- (space, newline, paren, comma, etc. — NOT by a letter/digit/underscore/dot)
    -- This avoids replacing "Hax.S" inside "SSProve.Hax.Semantics"
    let haxName := s!"Hax.{dep}"
    let sanitized := sanitizeName dep
    -- Replace with common boundary suffixes
    [" ", "\n", ")", ",", "]", "}", ":", ";"].foldl (fun a suffix =>
      a.replace (haxName ++ suffix) (sanitized ++ suffix)) acc
    ) code

/-- Find field names that appear in multiple structs. -/
private def findAmbiguousFields (structMeta : StructMeta) : List String :=
  let allFields := structMeta.foldl (fun acc (_, fields) =>
    acc ++ fields.map (·.1)) []
  -- A field is ambiguous if it appears more than once
  let dupes := allFields.filter fun f =>
    Nat.blt 1 (allFields.filter (· == f)).length
  dupes.eraseDups

/-- Collect all projection names applied to a given variable in an expression. -/
private partial def collectProjectionsOnVar (varName : String) : ImpExpr → List String
  | .app f [.var v] =>
    if f.startsWith "." && v == varName then [f.drop 1] else []
  | .app _ args => args.foldl (fun acc a => acc ++ collectProjectionsOnVar varName a) []
  | .letBind _ v body =>
    collectProjectionsOnVar varName v ++ collectProjectionsOnVar varName body
  | .seq a b => collectProjectionsOnVar varName a ++ collectProjectionsOnVar varName b
  | .ifThenElse c t e =>
    collectProjectionsOnVar varName c ++ collectProjectionsOnVar varName t ++
    collectProjectionsOnVar varName e
  | .tuple es => es.foldl (fun acc e => acc ++ collectProjectionsOnVar varName e) []
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    collectProjectionsOnVar varName lo ++ collectProjectionsOnVar varName hi ++
    collectProjectionsOnVar varName body
  | .whileFold c body =>
    collectProjectionsOnVar varName c ++ collectProjectionsOnVar varName body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    collectProjectionsOnVar varName lo ++ collectProjectionsOnVar varName hi ++
    collectProjectionsOnVar varName body
  | .whileFoldReturn c body =>
    collectProjectionsOnVar varName c ++ collectProjectionsOnVar varName body
  | .cfBreak e | .cfContinue e | .cfBreakContinue e =>
    collectProjectionsOnVar varName e
  | .match_ scrut arms =>
    collectProjectionsOnVar varName scrut ++
    arms.foldl (fun acc (_, b) => acc ++ collectProjectionsOnVar varName b) []
  | _ => []

/-- Infer struct type of a variable from context:
    1. Check if `v` is bound to `StructName args` (constructor call)
    2. If not, look at all projections applied to `v` and find the struct whose
       fields best match. -/
private def inferStructType (structMeta : StructMeta) (varName : String)
    (ctx : ImpExpr) : Option String :=
  let structNames := structMeta.map (·.1)
  -- Method 1: Direct constructor binding
  let fromCtor := go structNames varName ctx
  if fromCtor.isSome then fromCtor
  else
    -- Method 2: Find struct whose fields best match projections on this variable
    let projs := (collectProjectionsOnVar varName ctx).eraseDups
    if projs.isEmpty then none
    else
      -- For each struct, count how many of its fields match the projections
      let candidates := structMeta.filter fun (_, fields) =>
        projs.any fun p => fields.any (·.1 == p)
      -- Pick the struct with the most matching fields (tiebreak by total fields)
      match candidates with
      | [] => none
      | [(sname, _)] => some sname
      | _ =>
        let scored := candidates.map fun (sname, fields) =>
          let matchCount := (projs.filter fun p => fields.any (·.1 == p)).length
          (sname, matchCount, fields.length)
        -- Sort by match count desc, then total fields asc (prefer smaller struct)
        let best := scored.foldl (fun acc (sname, mc, fl) =>
          match acc with
          | none => some (sname, mc, fl)
          | some (_, bestMc, bestFl) =>
            if mc > bestMc then some (sname, mc, fl)
            else if mc == bestMc && fl < bestFl then some (sname, mc, fl)
            else acc) none
        best.map (·.1)
where
  go (structNames : List String) (varName : String) : ImpExpr → Option String
    | .letBind n (.app ctor _) body =>
      if n == varName && structNames.contains ctor then some ctor
      else go structNames varName body
    | .letBind _ _ body => go structNames varName body
    | .seq a b =>
      (go structNames varName a).orElse fun _ => go structNames varName b
    | .ifThenElse _ t e =>
      (go structNames varName t).orElse fun _ => go structNames varName e
    | _ => none

/-- Qualify ambiguous projections in an ImpExpr: `.field` → `StructName.field`
    when the argument is known to be of a specific struct type. -/
private partial def qualifyProjections (structMeta : StructMeta)
    (ambiguous : List String) (ctx : ImpExpr) : ImpExpr → ImpExpr
  | .app f [arg] =>
    if f.startsWith "." then
      let fname := f.drop 1
      if ambiguous.contains fname then
        -- Try to infer the struct type of the argument
        let argVar := match arg with | .var v => some v | _ => none
        let structType := argVar.bind fun v => inferStructType structMeta v ctx
        match structType with
        | some sname =>
          -- Check if this struct actually has this field
          let hasField := structMeta.any fun (n, fields) =>
            n == sname && fields.any (·.1 == fname)
          if hasField then .app s!"{sname}.{fname}" [qualifyProjections structMeta ambiguous ctx arg]
          else .app f [qualifyProjections structMeta ambiguous ctx arg]
        | none => .app f [qualifyProjections structMeta ambiguous ctx arg]
      else .app f [qualifyProjections structMeta ambiguous ctx arg]
    else .app f (args := [qualifyProjections structMeta ambiguous ctx arg])
  | .app f args =>
    .app f (args.map (qualifyProjections structMeta ambiguous ctx))
  | .letBind n v body =>
    .letBind n (qualifyProjections structMeta ambiguous ctx v)
      (qualifyProjections structMeta ambiguous ctx body)
  | .seq a b =>
    .seq (qualifyProjections structMeta ambiguous ctx a)
      (qualifyProjections structMeta ambiguous ctx b)
  | .ifThenElse c t e =>
    .ifThenElse (qualifyProjections structMeta ambiguous ctx c)
      (qualifyProjections structMeta ambiguous ctx t)
      (qualifyProjections structMeta ambiguous ctx e)
  | .tuple es => .tuple (es.map (qualifyProjections structMeta ambiguous ctx))
  | .proj e i => .proj (qualifyProjections structMeta ambiguous ctx e) i
  | .match_ scrut arms =>
    .match_ (qualifyProjections structMeta ambiguous ctx scrut)
      (arms.map fun (p, b) => (p, qualifyProjections structMeta ambiguous ctx b))
  | .forFold v lo hi body =>
    .forFold v (qualifyProjections structMeta ambiguous ctx lo)
      (qualifyProjections structMeta ambiguous ctx hi)
      (qualifyProjections structMeta ambiguous ctx body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (qualifyProjections structMeta ambiguous ctx lo)
      (qualifyProjections structMeta ambiguous ctx hi)
      (qualifyProjections structMeta ambiguous ctx body)
  | .whileFold c body =>
    .whileFold (qualifyProjections structMeta ambiguous ctx c)
      (qualifyProjections structMeta ambiguous ctx body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (qualifyProjections structMeta ambiguous ctx lo)
      (qualifyProjections structMeta ambiguous ctx hi)
      (qualifyProjections structMeta ambiguous ctx body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (qualifyProjections structMeta ambiguous ctx lo)
      (qualifyProjections structMeta ambiguous ctx hi)
      (qualifyProjections structMeta ambiguous ctx body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (qualifyProjections structMeta ambiguous ctx c)
      (qualifyProjections structMeta ambiguous ctx body)
  | .cfBreak e => .cfBreak (qualifyProjections structMeta ambiguous ctx e)
  | .cfContinue e => .cfContinue (qualifyProjections structMeta ambiguous ctx e)
  | .cfBreakContinue e => .cfBreakContinue (qualifyProjections structMeta ambiguous ctx e)
  | e => e

/-- Rewrite all occurrences of `.app oldName args` to `.app newName args` in an ImpExpr. -/
private partial def rewriteAppName (oldName newName : String) : ImpExpr → ImpExpr
  | .app f args =>
    let f' := if f == oldName then newName else f
    .app f' (args.map (rewriteAppName oldName newName))
  | .letBind n v body =>
    .letBind n (rewriteAppName oldName newName v) (rewriteAppName oldName newName body)
  | .seq a b => .seq (rewriteAppName oldName newName a) (rewriteAppName oldName newName b)
  | .ifThenElse c t e =>
    .ifThenElse (rewriteAppName oldName newName c)
      (rewriteAppName oldName newName t) (rewriteAppName oldName newName e)
  | .whileFold c body =>
    .whileFold (rewriteAppName oldName newName c) (rewriteAppName oldName newName body)
  | .forFold v lo hi body =>
    .forFold v (rewriteAppName oldName newName lo)
      (rewriteAppName oldName newName hi) (rewriteAppName oldName newName body)
  | .tuple es => .tuple (es.map (rewriteAppName oldName newName))
  | .proj e i => .proj (rewriteAppName oldName newName e) i
  | .match_ scrut arms =>
    .match_ (rewriteAppName oldName newName scrut)
      (arms.map fun (p, b) => (p, rewriteAppName oldName newName b))
  | .cfBreak e => .cfBreak (rewriteAppName oldName newName e)
  | .cfContinue e => .cfContinue (rewriteAppName oldName newName e)
  | .cfBreakContinue e => .cfBreakContinue (rewriteAppName oldName newName e)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (rewriteAppName oldName newName lo)
      (rewriteAppName oldName newName hi) (rewriteAppName oldName newName body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (rewriteAppName oldName newName lo)
      (rewriteAppName oldName newName hi) (rewriteAppName oldName newName body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (rewriteAppName oldName newName lo)
      (rewriteAppName oldName newName hi) (rewriteAppName oldName newName body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (rewriteAppName oldName newName c) (rewriteAppName oldName newName body)
  | e => e

/-- Rewrite `.app "new" args` to `.app structName args` when `args.length` matches
    a struct's field count. This handles Rust patterns like `AuthShare::new(value, mac)`
    where hax strips the qualifying type name, leaving just `new`.
    When multiple structs match the arity, uses context (struct projections applied to
    the result) to disambiguate. Also replaces bare `.var "new"` refs that have
    a qualifying struct context. -/
private partial def rewriteNewToStructCtor (structMeta : StructMeta) : ImpExpr → ImpExpr
  | .app "new" args =>
    if args.isEmpty then .app "new" args  -- Vec::new() → keep as "new" → "#[]"
    else
      -- Find structs whose field count matches arg count
      let candidates := structMeta.filter fun (_, fields) => fields.length == args.length
      match candidates with
      | [(sname, _)] => .app sname (args.map (rewriteNewToStructCtor structMeta))
      | _ =>
        -- Multiple candidates: disambiguate by matching arg variable names to field names.
        -- E.g., `new value mac` with args [.var "value", .var "mac"] matches AuthShare
        -- which has fields [("value", ...), ("mac", ...)].
        let argNames := args.filterMap fun a => match a with | .var n => some n | _ => none
        let scored := candidates.map fun (sname, fields) =>
          let fieldNames := fields.map fun (f : String × String × ImpType) => f.1
          let matchCount := argNames.filter (fieldNames.contains ·) |>.length
          (sname, matchCount)
        let best := scored.foldl (fun acc (sn, mc) =>
          match acc with
          | none => if mc > 0 then some (sn, mc) else none
          | some (_, bestMc) => if mc > bestMc then some (sn, mc) else acc) none
        match best with
        | some (sname, _) => .app sname (args.map (rewriteNewToStructCtor structMeta))
        | none => .app "new" (args.map (rewriteNewToStructCtor structMeta))
  | .app f args => .app f (args.map (rewriteNewToStructCtor structMeta))
  | .letBind n v body =>
    .letBind n (rewriteNewToStructCtor structMeta v) (rewriteNewToStructCtor structMeta body)
  | .seq a b => .seq (rewriteNewToStructCtor structMeta a) (rewriteNewToStructCtor structMeta b)
  | .ifThenElse c t e =>
    .ifThenElse (rewriteNewToStructCtor structMeta c)
      (rewriteNewToStructCtor structMeta t) (rewriteNewToStructCtor structMeta e)
  | .tuple es => .tuple (es.map (rewriteNewToStructCtor structMeta))
  | .proj e i => .proj (rewriteNewToStructCtor structMeta e) i
  | .match_ scrut arms =>
    .match_ (rewriteNewToStructCtor structMeta scrut)
      (arms.map fun (p, b) => (p, rewriteNewToStructCtor structMeta b))
  | .forFold v lo hi body =>
    .forFold v (rewriteNewToStructCtor structMeta lo)
      (rewriteNewToStructCtor structMeta hi) (rewriteNewToStructCtor structMeta body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (rewriteNewToStructCtor structMeta lo)
      (rewriteNewToStructCtor structMeta hi) (rewriteNewToStructCtor structMeta body)
  | .whileFold c body =>
    .whileFold (rewriteNewToStructCtor structMeta c) (rewriteNewToStructCtor structMeta body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (rewriteNewToStructCtor structMeta lo)
      (rewriteNewToStructCtor structMeta hi) (rewriteNewToStructCtor structMeta body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (rewriteNewToStructCtor structMeta lo)
      (rewriteNewToStructCtor structMeta hi) (rewriteNewToStructCtor structMeta body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (rewriteNewToStructCtor structMeta c)
      (rewriteNewToStructCtor structMeta body)
  | .cfBreak e => .cfBreak (rewriteNewToStructCtor structMeta e)
  | .cfContinue e => .cfContinue (rewriteNewToStructCtor structMeta e)
  | .cfBreakContinue e => .cfBreakContinue (rewriteNewToStructCtor structMeta e)
  | e => e

/-- Check if a free variable name is used as an initial value for `from_elem` where
    the resulting array is later used with struct projections from `structMeta`.
    Returns the struct name if the variable is used as a struct array initializer. -/
private partial def detectStructArrayInit (varName : String) (structMeta : StructMeta)
    : ImpExpr → Option String
  | .letBind arrVar (.app "from_elem" [.var v, _]) body =>
    if v == varName then
      -- Check if arrVar is used with struct projections (indexed then projected)
      let structFromProj := structMeta.findSome? fun (sname, fields) =>
        -- Pattern: index arrVar i → bound to tmp → .field tmp
        let projUsed := detectArrayStructProjection arrVar sname fields body
        if projUsed then some sname else none
      -- Also check if arrVar is used as an argument to a struct constructor call
      let structFromCtor := structMeta.findSome? fun (sname, _) =>
        if detectArrayPassedToStructContext arrVar sname body then some sname else none
      (structFromProj.orElse fun _ => structFromCtor).orElse fun _ =>
        detectStructArrayInit varName structMeta body
    else detectStructArrayInit varName structMeta body
  | .letBind _ v body =>
    (detectStructArrayInit varName structMeta v).orElse fun _ =>
    detectStructArrayInit varName structMeta body
  | .seq a b =>
    (detectStructArrayInit varName structMeta a).orElse fun _ =>
    detectStructArrayInit varName structMeta b
  | _ => none
where
  /-- Check if elements of array `arrName` are later used with projections of struct `sname`. -/
  detectArrayStructProjection (arrName sname : String)
      (fields : List (String × String × ImpType)) : ImpExpr → Bool
    | .letBind tmpVar (.app "index" [.var arr, _]) body =>
      if arr == arrName then
        -- Check if tmpVar is used with any field projection of this struct
        fields.any fun (fname, _, _) =>
          exprContainsApp s!".{fname}" body ||
          exprContainsApp s!"{sname}.{fname}" body
      else detectArrayStructProjection arrName sname fields body
    | .letBind _ _ body => detectArrayStructProjection arrName sname fields body
    | .seq a b =>
      detectArrayStructProjection arrName sname fields a ||
      detectArrayStructProjection arrName sname fields b
    | .app _ args => args.any (detectArrayStructProjection arrName sname fields)
    | .ifThenElse c t e =>
      detectArrayStructProjection arrName sname fields c ||
      detectArrayStructProjection arrName sname fields t ||
      detectArrayStructProjection arrName sname fields e
    | _ => false
  /-- Check if array `arrName` is indexed and the result passed to a struct constructor. -/
  detectArrayPassedToStructContext (arrName sname : String) : ImpExpr → Bool
    | .app f args =>
      -- Check if sname constructor receives elements of arrName
      (f == sname && args.any fun a => match a with
        | .app "index" [.var arr, _] => arr == arrName
        | _ => false) ||
      args.any (detectArrayPassedToStructContext arrName sname)
    | .letBind _ v body =>
      detectArrayPassedToStructContext arrName sname v ||
      detectArrayPassedToStructContext arrName sname body
    | .seq a b =>
      detectArrayPassedToStructContext arrName sname a ||
      detectArrayPassedToStructContext arrName sname b
    | .ifThenElse c t e =>
      detectArrayPassedToStructContext arrName sname c ||
      detectArrayPassedToStructContext arrName sname t ||
      detectArrayPassedToStructContext arrName sname e
    | _ => false

/-- Rewrite `from_elem ZERO n` to `from_elem (ZERO, ZERO, ...) n` when the resulting
    array is used as a struct array. The zero value needs to be a tuple matching the
    struct's field types (all initialized to the same ZERO dep value).
    Also annotates the dep's type in the deps class by tracking which structs use which
    zero initializers. -/
private partial def rewriteStructFromElem (structMeta : StructMeta)
    (fnRetTypes : List (String × ImpType))
    (allDefs : List (String × ImpExpr)) : ImpExpr → ImpExpr
  | .letBind arrVar (.app "from_elem" [initVal, sz]) body =>
    -- Check function return type to see if this produces a Vec<Struct>
    let structName := fnRetTypes.findSome? fun (_, retTy) =>
      match retTy with
      | .adt name [.adt sname _] =>
        if (name == "Vec" || name.endsWith "::Vec") &&
           structMeta.any (·.1 == sname) then some sname else none
      | _ => none
    -- Also check if arrVar is used with struct projections in body
    let structFromUsage := structMeta.findSome? fun (sname, fields) =>
      let projUsed := fields.any fun (fname, _, _) =>
        checkArrayElemProjection arrVar sname fname body
      if projUsed then some sname else none
    -- Also check: if arrVar is indexed and results are passed to struct constructors
    let structFromCtor := structMeta.findSome? fun (sname, _) =>
      if checkArrayElemUsedAsStruct arrVar sname body then some sname else none
    -- Also check: if body contains a struct constructor call in an assignment context
    -- Pattern: let _assign := StructName args; _assign (from localMutation of array[0] = Struct::new(...))
    let structFromAssign := structMeta.findSome? fun (sname, _) =>
      if checkBodyContainsStructAssign sname body then some sname else none
    -- Also check: if arrVar is returned and the function calls generate_auth_share etc.
    -- that are known to return Vec<Struct>
    let structFromReturnCtx := structMeta.findSome? fun (sname, fields) =>
      -- Check if the arrVar is passed to push with a struct constructor value
      if checkPushWithStruct arrVar sname body then some sname
      -- Check if elements from this array flow into a struct constructor
      else if fields.length > 1 && checkArrayAssignedStruct arrVar sname body then some sname
      else none
    let resolvedStruct := (structName.orElse fun _ => structFromUsage).orElse
      (fun _ => (structFromCtor.orElse fun _ => (structFromAssign.orElse fun _ => structFromReturnCtx)))
    match resolvedStruct with
    | some sname =>
      match structMeta.find? (·.1 == sname) with
      | some (_, fields) =>
        if fields.length > 1 then
          -- Replace initVal with a tuple of initVal copies
          let tupleInit := ImpExpr.tuple (fields.map fun _ => initVal)
          .letBind arrVar (.app "from_elem" [tupleInit, sz])
            (rewriteStructFromElem structMeta fnRetTypes allDefs body)
        else
          .letBind arrVar (.app "from_elem" [initVal, sz])
            (rewriteStructFromElem structMeta fnRetTypes allDefs body)
      | none =>
        .letBind arrVar (.app "from_elem" [initVal, sz])
          (rewriteStructFromElem structMeta fnRetTypes allDefs body)
    | none =>
      .letBind arrVar (.app "from_elem" [initVal, sz])
        (rewriteStructFromElem structMeta fnRetTypes allDefs body)
  | .letBind n v body =>
    .letBind n (rewriteStructFromElem structMeta fnRetTypes allDefs v)
      (rewriteStructFromElem structMeta fnRetTypes allDefs body)
  | .seq a b =>
    .seq (rewriteStructFromElem structMeta fnRetTypes allDefs a)
      (rewriteStructFromElem structMeta fnRetTypes allDefs b)
  | .ifThenElse c t e =>
    .ifThenElse (rewriteStructFromElem structMeta fnRetTypes allDefs c)
      (rewriteStructFromElem structMeta fnRetTypes allDefs t)
      (rewriteStructFromElem structMeta fnRetTypes allDefs e)
  | .forFold v lo hi body =>
    .forFold v lo hi (rewriteStructFromElem structMeta fnRetTypes allDefs body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v lo hi (rewriteStructFromElem structMeta fnRetTypes allDefs body)
  | .whileFold c body =>
    .whileFold c (rewriteStructFromElem structMeta fnRetTypes allDefs body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v lo hi (rewriteStructFromElem structMeta fnRetTypes allDefs body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v lo hi (rewriteStructFromElem structMeta fnRetTypes allDefs body)
  | .whileFoldReturn c body =>
    .whileFoldReturn c (rewriteStructFromElem structMeta fnRetTypes allDefs body)
  | e => e
where
  /-- Check if elements of `arrVar` are indexed and then have `.fname` projection applied. -/
  checkArrayElemProjection (arrVar sname fname : String) : ImpExpr → Bool
    | .app f [.app "index" [.var arr, _]] =>
      (arr == arrVar && (f == s!".{fname}" || f == s!"{sname}.{fname}"))
    | .letBind tmp (.app "index" [.var arr, _]) body =>
      arr == arrVar && (
        exprContainsApp s!".{fname}" body ||
        exprContainsApp s!"{sname}.{fname}" body)
    | .app _ args => args.any (checkArrayElemProjection arrVar sname fname)
    | .letBind _ v body =>
      checkArrayElemProjection arrVar sname fname v ||
      checkArrayElemProjection arrVar sname fname body
    | .seq a b =>
      checkArrayElemProjection arrVar sname fname a ||
      checkArrayElemProjection arrVar sname fname b
    | .ifThenElse c t e =>
      checkArrayElemProjection arrVar sname fname c ||
      checkArrayElemProjection arrVar sname fname t ||
      checkArrayElemProjection arrVar sname fname e
    | .forFold _ _ _ body | .forFoldRev _ _ _ body => checkArrayElemProjection arrVar sname fname body
    | .whileFold _ body => checkArrayElemProjection arrVar sname fname body
    | _ => false
  /-- Check if elements of `arrVar` are indexed and passed to struct constructor `sname`. -/
  checkArrayElemUsedAsStruct (arrVar sname : String) : ImpExpr → Bool
    | .app f args =>
      (f == sname && args.any fun a => match a with
        | .app "index" [.var arr, _] => arr == arrVar | _ => false) ||
      args.any (checkArrayElemUsedAsStruct arrVar sname)
    | .letBind _ v body =>
      checkArrayElemUsedAsStruct arrVar sname v ||
      checkArrayElemUsedAsStruct arrVar sname body
    | .seq a b =>
      checkArrayElemUsedAsStruct arrVar sname a ||
      checkArrayElemUsedAsStruct arrVar sname b
    | .ifThenElse c t e =>
      checkArrayElemUsedAsStruct arrVar sname c ||
      checkArrayElemUsedAsStruct arrVar sname t ||
      checkArrayElemUsedAsStruct arrVar sname e
    | .forFold _ _ _ body | .forFoldRev _ _ _ body => checkArrayElemUsedAsStruct arrVar sname body
    | .whileFold _ body => checkArrayElemUsedAsStruct arrVar sname body
    | _ => false
  /-- Check if body contains a struct constructor call in an assignment pattern.
      Pattern: `letBind "_assign" (app sname args) (var "_assign")` inside if-then branches.
      This detects `shares[0] = AuthShare::new(value, mac)` after localMutation. -/
  checkBodyContainsStructAssign (sname : String) : ImpExpr → Bool
    | .letBind "_assign" (.app f _) (.var "_assign") => f == sname
    | .letBind _ v body =>
      checkBodyContainsStructAssign sname v || checkBodyContainsStructAssign sname body
    | .seq a b =>
      checkBodyContainsStructAssign sname a || checkBodyContainsStructAssign sname b
    | .ifThenElse _ t e =>
      checkBodyContainsStructAssign sname t || checkBodyContainsStructAssign sname e
    | _ => false
  /-- Check if `push arrVar (sname args)` appears in the body. -/
  checkPushWithStruct (arrVar sname : String) : ImpExpr → Bool
    | .app "push" [.var arr, .app f _] => arr == arrVar && f == sname
    | .app _ args => args.any (checkPushWithStruct arrVar sname)
    | .letBind _ v body =>
      checkPushWithStruct arrVar sname v || checkPushWithStruct arrVar sname body
    | .seq a b =>
      checkPushWithStruct arrVar sname a || checkPushWithStruct arrVar sname b
    | .ifThenElse c t e =>
      checkPushWithStruct arrVar sname c ||
      checkPushWithStruct arrVar sname t || checkPushWithStruct arrVar sname e
    | .forFold _ _ _ body | .forFoldRev _ _ _ body => checkPushWithStruct arrVar sname body
    | .whileFold _ body => checkPushWithStruct arrVar sname body
    | _ => false
  /-- Check if the array variable has struct-typed elements assigned to it.
      Pattern: `_assign := StructName ...` where `_assign` mutates `arrVar`'s elements. -/
  checkArrayAssignedStruct (arrVar sname : String) : ImpExpr → Bool
    | .letBind n (.app f _) (.var v) =>
      -- Mutation pattern: `let _assign := StructName args; _assign`
      n == v && f == sname && n.startsWith "_"
    | .letBind _ v body =>
      checkArrayAssignedStruct arrVar sname v ||
      checkArrayAssignedStruct arrVar sname body
    | .seq a b =>
      checkArrayAssignedStruct arrVar sname a ||
      checkArrayAssignedStruct arrVar sname b
    | .ifThenElse _ t e =>
      checkArrayAssignedStruct arrVar sname t ||
      checkArrayAssignedStruct arrVar sname e
    | _ => false

/-- Rewrite `.proj e i` to use correct nested projection paths when `e` is a tuple
    or struct constructor/dep call with known arity > 2.
    For right-associated tuples (A × B × C), `.proj e 1` should be `.proj (.proj e 1) 0`
    (rendering as `.2.1`), not `.proj e 1` (rendering as `.2`).
    `arityMap` maps names to their return arities:
    - struct names → struct field count
    - dep names → return tuple arity (from callRetTypes or heuristic) -/
private partial def fixProjectionPaths (arityMap : List (String × Nat)) : ImpExpr → ImpExpr
  | .letBind n (.proj e idx) body =>
    -- DON'T fix projections on variables — they are part of tuple destructuring
    -- patterns handled by `extractTupleDestr` in `toLean`.
    -- Only fix projections on direct app calls (e.g., `(derive_keys x).2`).
    match e with
    | .var _ =>
      -- Leave variable projections as-is (handled by destructuring)
      .letBind n (.proj e idx) (fixProjectionPaths arityMap body)
    | _ =>
      let fixedE := fixProjectionPaths arityMap e
      let arity := exprArity arityMap e
      let fixedProj := buildNestedProj fixedE idx arity
      .letBind n fixedProj (fixProjectionPaths arityMap body)
  | .proj e idx =>
    -- Only fix projections on non-variable expressions
    match e with
    | .var _ => .proj e idx
    | _ =>
      let fixedE := fixProjectionPaths arityMap e
      let arity := exprArity arityMap e
      buildNestedProj fixedE idx arity
  | .letBind n v body =>
    -- Propagate arity through let-bindings:
    -- If v is an app call with known arity, add n → arity to map for body
    let valArity := exprArity arityMap v
    let bodyMap := if valArity > 0 then (n, valArity) :: arityMap else arityMap
    .letBind n (fixProjectionPaths arityMap v) (fixProjectionPaths bodyMap body)
  | .app f args => .app f (args.map (fixProjectionPaths arityMap))
  | .seq a b => .seq (fixProjectionPaths arityMap a) (fixProjectionPaths arityMap b)
  | .ifThenElse c t e =>
    .ifThenElse (fixProjectionPaths arityMap c)
      (fixProjectionPaths arityMap t) (fixProjectionPaths arityMap e)
  | .tuple es => .tuple (es.map (fixProjectionPaths arityMap))
  | .match_ scrut arms =>
    .match_ (fixProjectionPaths arityMap scrut)
      (arms.map fun (p, b) => (p, fixProjectionPaths arityMap b))
  | .forFold v lo hi body =>
    .forFold v (fixProjectionPaths arityMap lo)
      (fixProjectionPaths arityMap hi) (fixProjectionPaths arityMap body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (fixProjectionPaths arityMap lo)
      (fixProjectionPaths arityMap hi) (fixProjectionPaths arityMap body)
  | .whileFold c body =>
    .whileFold (fixProjectionPaths arityMap c) (fixProjectionPaths arityMap body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (fixProjectionPaths arityMap lo)
      (fixProjectionPaths arityMap hi) (fixProjectionPaths arityMap body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (fixProjectionPaths arityMap lo)
      (fixProjectionPaths arityMap hi) (fixProjectionPaths arityMap body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (fixProjectionPaths arityMap c) (fixProjectionPaths arityMap body)
  | .cfBreak e => .cfBreak (fixProjectionPaths arityMap e)
  | .cfContinue e => .cfContinue (fixProjectionPaths arityMap e)
  | .cfBreakContinue e => .cfBreakContinue (fixProjectionPaths arityMap e)
  | e => e
where
  /-- Determine the arity (number of tuple elements) of an expression's return type. -/
  exprArity (am : List (String × Nat)) : ImpExpr → Nat
    | .app f _ => (am.find? (·.1 == f)).map (·.2) |>.getD 0
    | .var v => (am.find? (·.1 == v)).map (·.2) |>.getD 0
    | .tuple elems => elems.length
    | _ => 0
  /-- Build nested projection for right-associated tuple: index i out of arity n.
      idx=0 → .proj e 0 (.1)
      idx=1, n>2 → .proj (.proj e 1) 0 (.2.1)
      idx=1, n=2 → .proj e 1 (.2)
      idx=k, n>k+1 → .proj ... (keep nesting)
      idx=k, n=k+1 → .proj ... 1 (last element) -/
  buildNestedProj (e : ImpExpr) (idx arity : Nat) : ImpExpr :=
    if arity <= 2 || idx == 0 then .proj e idx
    else
      -- For idx > 0 and arity > 2: first take .2 (tail), then project from tail
      let tail := ImpExpr.proj e 1
      let tailArity := arity - 1
      let tailIdx := idx - 1
      buildNestedProj tail tailIdx tailArity

/-- Detect which deps need struct-aware typing. Scans all function bodies for patterns
    where a dep value is used to construct or fill struct arrays. Returns a list of
    (dep_name, struct_name) pairs indicating the dep should have the struct's tuple type
    instead of `Array Int`. -/
private def detectStructDeps (structMeta : StructMeta)
    (defs : List (String × ImpExpr))
    (fnTypes : List (String × HaxAdapter.FnTypeInfo)) : List (String × String) :=
  -- For each function, check if its return type is Vec<Struct>
  -- and if so, which deps are used as initial values
  defs.foldl (fun acc (fnName, _body) =>
    match fnTypes.find? (·.1 == fnName) with
    | some (_, ti) =>
      match ti.retType with
      | .adt name [.adt sname _] =>
        if (name == "Vec" || name.endsWith "::Vec") && structMeta.any (·.1 == sname) then
          -- This function returns Vec<Struct>
          -- Check which deps are used as from_elem initial values
          acc  -- handled by rewriteStructFromElem
        else acc
      | _ => acc
    | none => acc) []

def toLeanCertifiedFile (defs : List (String × ImpExpr))
    (moduleName : String := "Generated")
    (structMeta : StructMeta := [])
    (fnTypes : List (String × HaxAdapter.FnTypeInfo) := [])
    (callRetTypes : List (String × ImpType) := []) : String :=
  -- Deduplicate: hax JSON may contain the same constant/function defined in
  -- multiple Rust modules. Keep the first occurrence, drop later duplicates.
  let defs := defs.foldl (fun (acc : List (String × ImpExpr)) (n, e) =>
    if acc.any (·.1 == n) then acc else acc ++ [(n, e)]) []
  -- Pre-process: qualify ambiguous projection names
  let ambiguousFields := findAmbiguousFields structMeta
  let defs := if ambiguousFields.isEmpty then defs
    else defs.map fun (n, e) => (n, qualifyProjections structMeta ambiguousFields e e)
  -- Pre-process: rewrite `new args` to struct constructor calls
  let defs := if structMeta.isEmpty then defs
    else defs.map fun (n, e) => (n, rewriteNewToStructCtor structMeta e)
  -- Pre-process: rewrite `from_elem ZERO n` for struct arrays
  let defs := if structMeta.isEmpty then defs
    else defs.map fun (n, e) =>
      -- Get this function's return type to detect Vec<Struct> returns
      let fnRetType := fnTypes.find? (·.1 == n) |>.map (·.2.retType)
      let fnRetTypes := match fnRetType with
        | some ty => [(n, ty)]
        | none => []
      (n, rewriteStructFromElem structMeta fnRetTypes defs e)
  -- Pre-process: fix projection paths for tuples with arity > 2
  -- Build arity map from struct metadata, dep return types, and usage analysis
  let structArities := structMeta.map fun (sname, fields) => (sname, fields.length)
  let depRetArities := callRetTypes.filterMap fun (dname, retTy) =>
    match retTy with
    | .tuple elems => if elems.length > 2 then some (dname, elems.length) else none
    | _ => none
  -- Also detect return arities from usage (letBind destructions with projections)
  let allExprs := defs.map (·.2)
  let usageArities := defs.foldl (fun acc (_, e) =>
    let calls := collectAppCalls e
    let callNames := calls.map (·.1) |>.eraseDups
    acc ++ callNames.filterMap fun fname =>
      let arity := allExprs.foldl (fun a expr => max a (detectReturnArity fname expr)) 0
      if arity > 2 then some (fname, arity) else none) ([] : List (String × Nat))
  let arityMap := (structArities ++ depRetArities ++ usageArities).eraseDups
  let defs := if arityMap.isEmpty then defs
    else defs.map fun (n, e) => (n, fixProjectionPaths arityMap e)
  -- Build struct lookup function for type resolution (accounts for pass-through structs)
  let structLookup := mkStructLookup structMeta (computeStructPassthrough structMeta defs)
  let (preamble, projConflicts) := generatePreamble defs moduleName structMeta fnTypes callRetTypes
  -- Rewrite function body projection references for conflicts
  let defs := if projConflicts.isEmpty then defs
    else defs.map fun (n, e) =>
      let e' := projConflicts.foldl (fun expr (unqual, qual) =>
        rewriteAppName unqual qual expr) e
      (n, e')
  -- Compute dependency names for post-processing (must match generatePreamble)
  let definedNames := defs.map (·.1)
  let structNames := structMeta.map (·.1)
  let allCalls := defs.foldl (fun acc (_, e) => acc ++ collectAppCalls e) []
  let allAppNames := allCalls.map (·.1) |>.eraseDups
  let allFreeVars := defs.foldl (fun acc (fname, e) =>
    acc ++ collectFreeVars [fname] e) ([] : List String)
  let freeVarDeps := allFreeVars.eraseDups.filter fun v =>
    !definedNames.contains v &&
    !structNames.contains v && !isFieldProjection v &&
    !allAppNames.contains v  -- match generatePreamble: no isAlwaysBuiltin for free vars
  let allNamesWithVars := (allAppNames ++ freeVarDeps).eraseDups
  let depNames := allNamesWithVars.filter fun f =>
    !definedNames.contains f &&
    !structNames.contains f && !isFieldProjection f &&
    !isAlwaysBuiltin f
  -- Detect if any function has guard-recursion pattern (needs `partial`)
  let needsPartial := defs.any fun (n, e) =>
    -- Strip parameter bindings to get the function body
    let rec stripParams : ImpExpr → ImpExpr
      | .letBind _ (.var _) b => stripParams b
      | e => e
    hasGuardRecursion n (stripParams e)
  let header := s!"/-\n  Auto-generated by haxpipe --emit-certified (verified hax pipeline)\n  Surface code + ImpExpr literals for agreement proofs.\n-/\nimport SSProve.Hax.Runtime\nimport SSProve.Hax.AST\nimport SSProve.Hax.Semantics\n\nset_option linter.unusedVariables false\n\nnamespace {moduleName}\n\nopen SSProve.Hax\n{preamble}\nmutual\n\n"
  let body := "\n".intercalate (defs.map fun (n, e) =>
    let fnTi := fnTypes.find? (·.1 == n) |>.map (·.2)
    let surfaceDef := toLeanDef n e (fnTypeInfo := fnTi) (structLookup := structLookup)
    -- If any function needs partial, mark all as partial (mutual block requirement)
    let surfaceDef := if needsPartial then surfaceDef.replace "def " "partial def " else surfaceDef
    s!"{surfaceDef}")
  let impExprs := "\n".intercalate (defs.map fun (n, e) =>
    let impExprDef := toLeanImpExprDef n e
    s!"{impExprDef}")
  let footer := s!"\nend\n\n{impExprs}\nend {moduleName}\n"
  -- Post-process: fix dependency references that got Hax. prefix
  fixDepReferences (header ++ body ++ footer) depNames

end SSProve.Hax

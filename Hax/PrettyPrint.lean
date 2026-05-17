/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.AST
import Hax.ImpType
import Hax.HaxAdapter
import Hax.ImpType
import Hax.Canonicalize

/-!
# Lean 4 Pretty-Printer for ImpExpr (DEPRECATED — untyped path)

Emits Lean 4 source code from post-pipeline `ImpExpr`.

Assumes a runtime library providing `Hax.forFold`, `Hax.whileFold`, etc.
The output can be compiled by Lean 4 given appropriate imports.

**Not imported by the proof library** — only used by the executable.

## Deprecation notice (2026-05-14)

This module is the *untyped* emit path. Every production extraction
(100+ `*_haxpipe.lean` files in `SSProve-lean/CatCrypt/.../Extraction/`)
goes through `Hax.PrettyPrintT.toLeanCertifiedFileTyped` (the typed
path), which preserves hax JSON types and emits well-typed Lean. This
module is reached only by:

- `--emit-lean` (default mode) — surface-only emit
- `--emit-certified` *without* `--hax-format` — legacy expression
  parser path

Neither has a production consumer. Prefer `Hax.PrettyPrintT`. The
entry-point `toLeanCertifiedFile` is `@[deprecated]`; calling it
through `haxpipeT` also emits a runtime warning on stderr.

Removal target: once `tests/run_tests.sh` and `scripts/run_haxpipe.sh`
(SSProve-lean) are migrated or removed.
-/

namespace Hax

/-- Indent by `n` levels (2 spaces each). -/
private def indent (n : Nat) : String :=
  String.ofList (List.replicate (2 * n) ' ')

/-- Sanitize a name for Lean 4: wrap in French quotes if needed. -/
def sanitizeName (n : String) : String :=
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

/-- Handle width-annotated operation names (e.g. "wrapping_add#32").
    The HaxAdapter annotates width-sensitive Rust ops with `#bitwidth` when
    it can infer the type from the Impl discriminator. -/
private def widthAwareRuntime (f : String) : String :=
  if f.any (· == '#') then
    let parts := f.splitOn "#"
    match parts with
    | [op, w] => match op with
      | "wrapping_add" => s!"Hax.wrapping_add_w {w}"
      | "wrapping_sub" => s!"Hax.wrapping_sub_w {w}"
      | "wrapping_mul" => s!"Hax.wrapping_mul_w {w}"
      | "wrapping_neg" => s!"Hax.wrapping_neg_w {w}"
      | "rotate_right" => s!"Hax.rotate_right_w {w}"
      | "rotate_left"  => s!"Hax.rotate_left_w {w}"
      | "shr" | "Shr"  => s!"Hax.shr_w {w}"
      | "shl" | "Shl"  => s!"Hax.shl_w {w}"
      | "bitand" | "BitAnd" => s!"Hax.bitand_w {w}"
      | "bitor"  | "BitOr"  => s!"Hax.bitor_w {w}"
      | "bitxor" | "BitXor" => s!"Hax.bitxor_w {w}"
      | "bitnot" | "Not"    => s!"Hax.bitnot_w {w}"
      | "cast"               => s!"Hax.castVal_w {w}"
      | _ => s!"Hax.{op}"
    | _ => f
  else sanitizeName f

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
  -- iter/map/collect/flat_map are handled by special app cases, fallback to Hax.* for n-ary calls
  | "iter" => "Hax.iter"
  | "map" => "Hax.map_arr"
  | "collect" => "Hax.collect"
  | "flat_map" => "Hax.flat_map"
  | "zip" => "Hax.zip"
  | "into_vec" => "Hax.into_vec"
  | "next" => "Hax.next"
  | "enumerate" => "Hax.enumerate"
  | "with_capacity" => "Hax.with_capacity"
  | "from_elem" => "Hax.from_elem"
  | "truncate" => "Hax.truncate"
  | "is_empty" => "Hax.is_empty"
  | "deref" => "Hax.deref"
  | "clone" => "Hax.clone"
  | "to_vec" => "Hax.to_vec"
  | "_assign" => "Hax.assign"
  | "count_ones" => "Hax.count_ones"
  | "assert_failed" => "Hax.assert_failed"
  | "cast" => "Hax.castVal"
  -- Width-annotated variants (from HaxAdapter, e.g. wrapping_add#32)
  -- or everything else: sanitize and pass through
  | f => widthAwareRuntime f

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
private partial def patToLean : ImpPat → String
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
  -- General constructor pattern. The Plonky3-relevant cases are
  -- `Break` and `Continue` from `Core_models.Ops.Control_flow`
  -- (used by Rust's `?` operator); we emit fully-qualified names
  -- for these to bypass namespace-lookup against the enclosing
  -- extraction namespace. For other variants we still use the
  -- anonymous-constructor `.Name` form so Lean resolves against
  -- the scrutinee's expected type.
  | .ctorPat name args =>
      let head : String :=
        if name == "Break" then "ControlFlow.Break"
        else if name == "Continue" then "ControlFlow.Continue"
        else s!".{name}"
      if args.isEmpty then head
      else s!"{head} {" ".intercalate (args.map patToLean)}"

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

/-- Patch match expressions at the tail of a fold body where some arms return `()` (Unit)
    and others return non-unit values. Replaces `()` arms with the fold accumulator variable
    to ensure all arms have the same type.
    This handles patterns like `match ctr with | 0 => foldRange ... | _ => ()` inside folds. -/
private partial def patchMatchUnitArmsInBody (accVar : String) : ImpExpr → ImpExpr
  | .letBind n v body => .letBind n v (patchMatchUnitArmsInBody accVar body)
  | .seq a b => .seq a (patchMatchUnitArmsInBody accVar b)
  | .match_ scrut arms =>
    let hasUnit := arms.any fun (_, b) => b == .unitVal
    let hasNonUnit := arms.any fun (_, b) => b != .unitVal
    if hasUnit && hasNonUnit then
      .match_ scrut (arms.map fun (p, b) =>
        if b == .unitVal then (p, .var accVar) else (p, b))
    else .match_ scrut arms
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
private partial def extractCondMutationsAux (locals : List String) :
    ImpExpr → List (String × ImpExpr)
  | .seq (.seq a b) c => extractCondMutationsAux locals (.seq a (.seq b c))
  | .seq (.letBind n rhs (.var v)) rest =>
    -- Treat `let n := rhs; n` as a mutation pattern UNLESS `n` was
    -- previously introduced as a local in this same sub-tree (via a
    -- `letBind n init body` whose body contains us). Locals tracked
    -- via the `letBind n val body` arm below.
    if n == v && !locals.contains n then
      (n, rhs) :: extractCondMutationsAux locals rest
    else extractCondMutationsAux locals rest
  | .seq .unitVal rest => extractCondMutationsAux locals rest
  | .seq _ rest => extractCondMutationsAux locals rest
  | .letBind n rhs (.var v) =>
    if n == v && !locals.contains n then [(n, rhs)] else []
  -- Recurse into non-mutation letBind. Track fresh-init locals so that
  -- subsequent mutation-shaped `let n := X; n` patterns whose `n` is the
  -- inner-introduced local are NOT mistaken for outer accumulators.
  -- (This is the BLS fr_mul fix: inside the inner whileFold's then-branch,
  -- `letBind "temp" (repeat_ 0 7) <body>` introduces `temp` locally; later
  -- `letBind "temp" (array_update temp ti ...) (var "temp")` is a true
  -- mutation but ONLY of the inner-local `temp`, not an outer accumulator.)
  | .letBind n val body =>
    let isFreshLocal := !exprContainsVar n val && !locals.contains n
    let newLocals := if isFreshLocal then n :: locals else locals
    extractCondMutationsAux newLocals body
  | .unitVal => []
  | _ => []

/-- Top-level wrapper. -/
private partial def extractCondMutations (e : ImpExpr) : List (String × ImpExpr) :=
  extractCondMutationsAux [] e

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

/-- Check if an expression contains ControlFlow nodes (cfBreak/cfContinue/cfBreakContinue).
    Recurses into all sub-expressions including nested loop bodies. -/
private partial def hasControlFlowNodes : ImpExpr → Bool
  | .cfBreak _ | .cfContinue _ | .cfBreakContinue _ => true
  | .letBind _ v b => hasControlFlowNodes v || hasControlFlowNodes b
  | .seq e1 e2 => hasControlFlowNodes e1 || hasControlFlowNodes e2
  | .ifThenElse c t e => hasControlFlowNodes c || hasControlFlowNodes t || hasControlFlowNodes e
  | .match_ _ arms => arms.any fun (_, b) => hasControlFlowNodes b
  | .app _ args => args.any hasControlFlowNodes
  | .tuple elems => elems.any hasControlFlowNodes
  | _ => false

/-- Check if an expression has cfBreak/cfContinue at the surface level.
    Does NOT recurse into nested loop bodies (forFold/whileFold/forFoldReturn etc.),
    so inner-loop control flow doesn't leak to outer rendering decisions. -/
private partial def hasSurfaceControlFlow : ImpExpr → Bool
  | .cfBreak _ | .cfContinue _ | .cfBreakContinue _ => true
  | .letBind _ v b => hasSurfaceControlFlow v || hasSurfaceControlFlow b
  | .seq e1 e2 => hasSurfaceControlFlow e1 || hasSurfaceControlFlow e2
  | .ifThenElse _ t e => hasSurfaceControlFlow t || hasSurfaceControlFlow e
  | .match_ _ arms => arms.any fun (_, b) => hasSurfaceControlFlow b
  | .forFold _ _ _ _ | .forFoldRev _ _ _ _ => false  -- stop at loop boundaries
  | .whileFold _ _ => false
  | .forFoldReturn _ _ _ _ | .forFoldRevReturn _ _ _ _ => false
  | .whileFoldReturn _ _ => false
  | .app _ args => args.any hasSurfaceControlFlow
  | .tuple elems => elems.any hasSurfaceControlFlow
  | _ => false

/-- Wrap a tail-position forFold/forFoldRev whose body has surface
    ControlFlow (cfBreak/cfContinue) in a synthetic `_HAX_MERGE` marker.
    Used when the inner fold sits at a non-CF context (e.g. body of an
    outer `Hax.foldRange` lambda whose return type is the accumulator
    type). The marker is recognized by `toLean` and rendered as
    `(<rendered fold>).merge`, extracting the value from `ControlFlow`.

    Recurses through let-chains, seq-tails, and if/match arms to find
    the tail expression. Inner-loop bodies and non-tail positions are
    left untouched (their context is determined locally by the renderer). -/
private partial def wrapTailForFoldWithMerge : ImpExpr → ImpExpr
  | .letBind n v body => .letBind n v (wrapTailForFoldWithMerge body)
  | .seq a b => .seq a (wrapTailForFoldWithMerge b)
  | .ifThenElse c t e =>
    .ifThenElse c (wrapTailForFoldWithMerge t) (wrapTailForFoldWithMerge e)
  | .match_ scrut arms =>
    .match_ scrut (arms.map fun (p, b) => (p, wrapTailForFoldWithMerge b))
  | .forFold v lo hi body =>
    if hasSurfaceControlFlow body then
      .app "_HAX_MERGE" [.forFold v lo hi body]
    else .forFold v lo hi body
  | .forFoldRev v lo hi body =>
    if hasSurfaceControlFlow body then
      .app "_HAX_MERGE" [.forFoldRev v lo hi body]
    else .forFoldRev v lo hi body
  | e => e

/-- Extract accumulator variable names from a fold body.
    Looks for the localMutation pattern: `seq (letBind n rhs (var n)) rest`
    which came from `assign n rhs`. Returns unique names in order.
    Filters out `_assign`-prefixed names which are intermediate mutation
    temporaries from nested field/index assignments (not real accumulators). -/
private partial def extractAccumulatorsAux (locals : List String) : ImpExpr → List String
  | .seq (.seq a b) c => extractAccumulatorsAux locals (.seq a (.seq b c))
  | .seq (.letBind n val (.var v)) rest =>
    if n == v && !n.startsWith "_assign" && !locals.contains n then
      -- Discriminate between fresh init (`let n := init` where init is
      -- independent of n) and true mutation (`let n := f(n) ...`).
      -- A fresh init means `n` is loop-local, not an outer accumulator.
      if exprContainsVar n val then
        -- True mutation: n is an accumulator candidate.
        let restAccs := extractAccumulatorsAux locals rest
        if restAccs.contains n then restAccs else n :: restAccs
      else
        -- Fresh init: n is loop-local. Add to locals; don't promote.
        extractAccumulatorsAux (n :: locals) rest
    else extractAccumulatorsAux locals rest
  -- Look inside conditional mutations for hidden accumulators
  | .seq (.ifThenElse _ thn _) rest =>
    let thnAccs := extractCondMutations thn |>.map (·.1)
      |>.filter (fun n => !n.startsWith "_assign" && !locals.contains n)
    let restAccs := extractAccumulatorsAux locals rest
    let all := thnAccs ++ restAccs
    all.eraseDups
  -- Recurse into nested loops in seq position to find transitive accumulators
  | .seq (.forFold _ _ _ body) rest =>
    (extractAccumulatorsAux locals body ++ extractAccumulatorsAux locals rest).eraseDups
  | .seq (.forFoldRev _ _ _ body) rest =>
    (extractAccumulatorsAux locals body ++ extractAccumulatorsAux locals rest).eraseDups
  | .seq (.whileFold _ body) rest =>
    (extractAccumulatorsAux locals body ++ extractAccumulatorsAux locals rest).eraseDups
  | .seq _ rest => extractAccumulatorsAux locals rest
  | .letBind n val (.var v) =>
    if n == v && !n.startsWith "_assign" && !locals.contains n then [n] else []
  -- Non-mutation letBind: if `n` is freshly initialized (val doesn't reference n
  -- and n isn't already an outer accumulator), then n is loop-local. Add to locals
  -- before recursing so subsequent mutations don't promote it to an accumulator.
  | .letBind n val body =>
    let isFreshLocal := !exprContainsVar n val && !locals.contains n
    let newLocals := if isFreshLocal then n :: locals else locals
    extractAccumulatorsAux newLocals body
  | .ifThenElse _ thn els =>
    let thnAccs := extractCondMutations thn |>.map (·.1)
      |>.filter (fun n => !n.startsWith "_assign" && !locals.contains n)
    let elsAccs := if els == .unitVal then []
      else extractCondMutations els |>.map (·.1)
        |>.filter (fun n => !n.startsWith "_assign" && !locals.contains n)
    let elsDeep := if elsAccs.isEmpty && els != .unitVal then
        extractAccumulatorsAux locals els
      else elsAccs
    (thnAccs ++ elsDeep).eraseDups
  | .forFold _ _ _ body => extractAccumulatorsAux locals body
  | .forFoldRev _ _ _ body => extractAccumulatorsAux locals body
  | .whileFold _ body => extractAccumulatorsAux locals body
  | _ => []

/-- Top-level wrapper. -/
private partial def extractAccumulators (e : ImpExpr) : List String :=
  extractAccumulatorsAux [] e

/-- Build a destructure-and-return wrapper for an inner fold whose
    accumulator shape doesn't match the outer fold's. Emits
    `let <inner_destr> := <inner-fold>; <outer-tuple>` so that:
      * Inner accumulators NOT in the outer's list are bound but unused
        (named `_acc` to silence linters).
      * Outer accumulators NOT in the inner's list keep their current
        binding (untouched).
      * Outer accumulators present in inner are rebound by destructure.

    Uses a fresh `_innerTuple` name and `extractTupleDestr`-shaped
    `proj` chain so the renderer prints the standard
    `let (a, b, _c) := <fold>` Lean idiom. -/
private def buildDestructureAndTuple (fold : ImpExpr) (innerAccs outerAccs : List String) :
    ImpExpr :=
  let tmp := "_innerTuple"
  let outerTuple : ImpExpr :=
    if outerAccs.length == 1 then .var outerAccs.head!
    else .tuple (outerAccs.map .var)
  let mkLetChain (accs : List String) (body : ImpExpr) : ImpExpr :=
    -- Build chain right-to-left over accs paired with their indices.
    let indexed := accs.zipIdx
    indexed.foldr (init := body) fun (name, i) acc =>
      let bindName := if outerAccs.contains name then name else s!"_{name}"
      .letBind bindName (.proj (.var tmp) i) acc
  if innerAccs.length == 1 then
    let n := innerAccs.head!
    let bindName := if outerAccs.contains n then n else s!"_{n}"
    .letBind bindName fold outerTuple
  else
    .letBind tmp fold (mkLetChain innerAccs outerTuple)

/-- Wrap a tail-position forFold/forFoldRev whose accumulator shape
    differs from the enclosing outer fold's. Emits a destructure +
    outer-tuple-return. Used to fix `Application type mismatch` errors
    where an inner fold's result type (e.g. `(result, b, word)`) doesn't
    match the outer's expected accumulator type (e.g. `(result, b)`).

    Recurses through let-chains, seq-tails, and if/match arms. Inner
    folds NOT in tail position are left untouched. -/
private partial def wrapTailFoldForOuterAccs (outerAccs : List String) :
    ImpExpr → ImpExpr
  | .letBind n v body =>
    .letBind n v (wrapTailFoldForOuterAccs outerAccs body)
  | .seq a b => .seq a (wrapTailFoldForOuterAccs outerAccs b)
  | .ifThenElse c t e =>
    .ifThenElse c (wrapTailFoldForOuterAccs outerAccs t)
                   (wrapTailFoldForOuterAccs outerAccs e)
  | .match_ scrut arms =>
    .match_ scrut (arms.map fun (p, b) => (p, wrapTailFoldForOuterAccs outerAccs b))
  | .forFold v lo hi body =>
    let innerAccs := extractAccumulators body
    if innerAccs == outerAccs || outerAccs.length <= 1 ||
       hasSurfaceControlFlow body then
      .forFold v lo hi body
    else
      buildDestructureAndTuple (.forFold v lo hi body) innerAccs outerAccs
  | .forFoldRev v lo hi body =>
    let innerAccs := extractAccumulators body
    if innerAccs == outerAccs || outerAccs.length <= 1 ||
       hasSurfaceControlFlow body then
      .forFoldRev v lo hi body
    else
      buildDestructureAndTuple (.forFoldRev v lo hi body) innerAccs outerAccs
  | e => e

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
  -- Match at tail of fold body: transform each arm, replacing unitVal arms with accumulator return
  | .match_ scrut arms =>
    let accReturn := match accs with
      | [a] => ImpExpr.var a
      | _ => .tuple (accs.map .var)
    .match_ scrut (arms.map fun (p, b) =>
      if b == .unitVal then (p, accReturn)
      else (p, transformFoldBody accs b))
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

/-- Extract the initial value for an accumulator from a fold body.
    If the body starts with `let acc := <init>` where `<init>` does NOT reference
    `acc` (a fresh initialization, not a mutation), returns `some <init>`.
    This handles patterns like:
      `let w := ZERO_WORD; let w := array_update w 0 ...; w`
    where the first binding is a fresh init that should be the fold's initial value. -/
private partial def extractAccInit (accName : String) (allAccs : List String := [])
    : ImpExpr → Option ImpExpr
  | .seq (.seq a b) c => extractAccInit accName allAccs (.seq a (.seq b c))
  -- seq (letBind accName init (var accName)) rest
  -- This is a mutation pattern (let n := val; n), BUT if val does NOT reference
  -- accName OR any other accumulator, then it's a fresh init.
  -- (Mutating to the value of another accumulator is NOT a fresh init —
  --  e.g., `h = g` in SHA-256's compress rotation is true mutation, not init.)
  | .seq (.letBind n val (.var v)) rest =>
    let refsAnyAcc := allAccs.any fun a => exprContainsVar a val
    if n == accName && n == v then
      if refsAnyAcc then none  -- true mutation (references some accumulator)
      else some val  -- fresh init disguised as mutation
    else if n == accName then
      if refsAnyAcc then none
      else some val
    else extractAccInit accName allAccs rest
  -- seq (letBind n val body) rest — local binding, recurse into rest
  | .seq (.letBind _ _ _) rest => extractAccInit accName allAccs rest
  -- seq (non-letBind) rest — skip and recurse
  | .seq _ rest => extractAccInit accName allAccs rest
  -- Direct letBind accName init body — check if it's fresh (not self-referencing)
  | .letBind n val body =>
    if n == accName then
      let refsAnyAcc := allAccs.any fun a => exprContainsVar a val
      if refsAnyAcc then none
      else some val
    else extractAccInit accName allAccs body
  | _ => none

/-- Format accumulator initial value and lambda parameter for fold rendering. -/
private def accStrings (accs : List String) : String × String :=
  if accs.isEmpty then ("()", "_acc")
  else if accs.length == 1 then
    let name := sanitizeName accs.head!
    (name, name)
  else
    let names := ", ".intercalate (accs.map sanitizeName)
    (s!"({names})", s!"({names})")

/-- Compute custom init expressions for accumulators that need default initialization.
    Returns a list of (accName, initExpr) pairs for accumulators whose first binding
    in the fold body is a fresh init (not self-referencing).
    These need `let acc := init` emitted BEFORE the fold.
    Skips init expressions that reference variables only defined inside the fold body
    (local bindings like destructured results, loop-local temporaries). -/
private def accInitOverrides (accs : List String) (body : ImpExpr) :
    List (String × ImpExpr) :=
  -- Collect all locally-bound variable names inside the fold body
  let locallyBound := collectLetBindVars body
  accs.filterMap fun acc =>
    match extractAccInit acc accs body with
    | some initExpr =>
      -- Only emit override if the init expression doesn't reference any
      -- fold-body-local variable (which wouldn't exist in the outer scope)
      let usesLocal := locallyBound.any fun v =>
        v != acc && !accs.contains v && exprContainsVar v initExpr
      if usesLocal then none
      else some (acc, initExpr)
    | none => none

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
  | .cfBreak .unitVal => .cfBreak (accTuple accs)
  | .cfBreak v => .cfBreak v  -- preserve function-level early returns with actual values
  | .cfBreakContinue _ => .cfBreakContinue (accTuple accs)
  | .unitVal => .cfBreak (accTuple accs)
  | .seq (.cfBreak .unitVal) _ => .cfBreak (accTuple accs)
  | .seq (.cfBreak v) _ => .cfBreak v  -- preserve function-level early returns
  | .seq (.cfBreakContinue _) _ => .cfBreakContinue (accTuple accs)  -- preserve loop-break semantics
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
  -- Non-CF terminal expression: wrap in cfContinue so whileFold body has correct type
  | e =>
    if hasControlFlowNodes e then e
    else .seq e (.cfContinue (accTuple accs))

/-- Transform a whileFold body for surface rendering.
    - In continue branches: replace trailing `unitVal` with `cfContinue (accs)`
    - In break branches: replace `cfBreak unitVal` with `cfBreak (accs)` -/
private partial def transformWhileFoldBody (accs : List String) : ImpExpr → ImpExpr
  | .ifThenElse c thn els =>
    .ifThenElse c (transformWhileContinue accs thn) (transformWhileBreak accs els)
  | .letBind n v body => .letBind n v (transformWhileFoldBody accs body)
  | e => transformWhileContinue accs e

/-- Patch cfBreak unitVal → cfBreak (accTuple accs) in an expression.
    Used when the body already has CF nodes but the break value is ()
    instead of the accumulator tuple. -/
private partial def patchCfBreakUnit (accs : List String) : ImpExpr → ImpExpr
  | .cfBreak .unitVal => .cfBreak (accTuple accs)
  | .seq (.cfBreak .unitVal) rest => .seq (.cfBreak (accTuple accs)) rest
  | .letBind n v body => .letBind n v (patchCfBreakUnit accs body)
  | .seq e1 e2 => .seq (patchCfBreakUnit accs e1) (patchCfBreakUnit accs e2)
  | .ifThenElse c t e => .ifThenElse c (patchCfBreakUnit accs t) (patchCfBreakUnit accs e)
  | e => e

/-- Transform a forFold body for ControlFlow rendering.
    Wraps bare `unitVal` / accumulator returns in `cfContinue (accs)` so
    the body has type `ControlFlow β α` as expected by `Hax.forFold`.
    Preserves existing cfBreak/cfContinue nodes. -/
private partial def transformForFoldCfBody (accs : List String) : ImpExpr → ImpExpr
  | .seq (.seq a b) c => transformForFoldCfBody accs (.seq a (.seq b c))
  | .seq (.letBind n val (.var v)) rest =>
    if n == v then .letBind n val (transformForFoldCfBody accs rest)
    else .seq (.letBind n val (.var v)) (transformForFoldCfBody accs rest)
  | .seq .unitVal rest => transformForFoldCfBody accs rest
  -- Guard pattern in seq: seq (ifThenElse cond unitVal work) rest
  -- The unitVal branch means "skip" (cfContinue), the work branch does mutations,
  -- and rest continues the fold body. Transform: make the unitVal a cfContinue.
  | .seq (.ifThenElse c thn els) rest =>
    let thnHasCF := hasSurfaceControlFlow thn
    let elsHasCF := hasSurfaceControlFlow els
    -- Case 1: thn already has surface cfBreak (it IS the early exit), els is fall-through
    -- Combine els+rest as the continue path, patch thn's cfBreak unitVal → cfBreak (accs).
    if thnHasCF && !elsHasCF then
      let combined := if rest == .unitVal then els else .seq els rest
      .ifThenElse c (patchCfBreakUnit accs thn) (transformForFoldCfBody accs combined)
    -- Case 2: els already has surface cfBreak, thn is fall-through
    else if !thnHasCF && elsHasCF then
      let combined := if rest == .unitVal then thn else .seq thn rest
      .ifThenElse c (transformForFoldCfBody accs combined) (patchCfBreakUnit accs els)
    -- Case 3: neither has surface CF, thn is unitVal (guard: if cond then done else work)
    else if !thnHasCF && thn == .unitVal then
      -- In ControlFlow fold: done = cfBreak (exit loop), work continues
      let combined := if rest == .unitVal then els else .seq els rest
      let result := ImpExpr.ifThenElse c (.cfBreak (accTuple accs)) (transformForFoldCfBody accs combined)
      result
    -- Case 4: neither has CF, els is unitVal (inverted guard)
    else if !elsHasCF && els == .unitVal then
      let combined := if rest == .unitVal then thn else .seq thn rest
      .ifThenElse c (transformForFoldCfBody accs combined) (.cfBreak (accTuple accs))
    else
      .seq (.ifThenElse c thn els) (transformForFoldCfBody accs rest)
  | .seq e1 rest =>
    -- Dead code elimination: if e1 already returns ControlFlow, rest is unreachable
    if hasSurfaceControlFlow e1 then
      transformForFoldCfBody accs e1
    else
      .seq e1 (transformForFoldCfBody accs rest)
  | .letBind n val body => .letBind n val (transformForFoldCfBody accs body)
  | .ifThenElse c thn els =>
    let thnHasCF := hasSurfaceControlFlow thn
    let elsHasCF := hasSurfaceControlFlow els
    -- Always use full transform on both branches to handle nested if-else
    -- where sub-branches may have bare values needing cfContinue wrapping.
    -- transformForFoldCfBody preserves existing cfBreak/cfContinue nodes and
    -- patches cfBreak unitVal → cfBreak (accs) while wrapping bare terminals.
    .ifThenElse c (transformForFoldCfBody accs thn) (transformForFoldCfBody accs els)
  -- Patch cfBreak unitVal → cfBreak (accs) to carry accumulator through break
  | .cfBreak .unitVal => .cfBreak (accTuple accs)
  -- Existing cfBreak/cfContinue with non-unit values: preserve as-is
  | .cfBreak v => .cfBreak v
  | .cfContinue v => .cfContinue v
  | .cfBreakContinue v => .cfBreakContinue v
  | .unitVal => .cfContinue (accTuple accs)
  | .var n =>
    if accs.contains n then .cfContinue (accTuple accs)
    else .cfContinue (accTuple accs)
  | e => .cfContinue (accTuple accs)

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

/-- Collect all cfBreak values from an expression (for detecting return type). -/
private partial def extractAllCfBreakVals : ImpExpr → List ImpExpr
  | .cfBreak v => [v]
  | .letBind _ v b => extractAllCfBreakVals v ++ extractAllCfBreakVals b
  | .seq a b => extractAllCfBreakVals a ++ extractAllCfBreakVals b
  | .ifThenElse _ t e => extractAllCfBreakVals t ++ extractAllCfBreakVals e
  | .match_ _ arms => arms.foldl (fun acc (_, b) => acc ++ extractAllCfBreakVals b) []
  | _ => []

/-- Extract the cfBreak return value from an expression, looking through seq/unitVal wrappers.
    Returns the break value if the expression is essentially a cfBreak (early return),
    or none if it's not. -/
private partial def extractCfBreak : ImpExpr → Option ImpExpr
  | .cfBreak val => some val
  | .seq (.cfBreak val) .unitVal => some val
  | .cfContinue _ => none
  | .unitVal => none
  | .seq .unitVal rest => extractCfBreak rest
  | .letBind _ _ body => extractCfBreak body
  -- seq of mutation patterns (letBind n rhs (var n)) followed by more:
  -- recurse into the tail to find cfBreak at the end of a mutation chain
  | .seq (.letBind _ _ (.var _)) rest => extractCfBreak rest
  | .seq (.seq _ _) rest => extractCfBreak rest
  | _ => none

/-- Strip cfBreak from the tail of an expression, replacing it with the break value.
    This allows rendering the whole expression with proper let-bindings and the
    return value at the end (instead of cfBreak wrapper).
    Returns the original expression unchanged if no cfBreak is found. -/
private partial def stripCfBreak : ImpExpr → ImpExpr
  | .cfBreak val => val
  | .seq (.cfBreak val) .unitVal => val
  | .seq .unitVal rest => stripCfBreak rest
  | .letBind n v body => .letBind n v (stripCfBreak body)
  | .seq e1 e2 => .seq e1 (stripCfBreak e2)
  | e => e

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
partial def checkProjOnVar (varName projName : String) : ImpExpr → Bool
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
def hasGuardRecursion (fname : String) (e : ImpExpr) : Bool :=
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
    `lvl` is the current indentation level.
    `boolNames` is a list of function names known to return Bool (from TExpr types). -/
partial def toLean (e : ImpExpr) (lvl : Nat := 0) (boolNames : List String := []) : String :=
  let ind := indent lvl
  let ind1 := indent (lvl + 1)
  -- Type-annotation marker rendering.
  --
  -- The DECISION of which let-bindings to annotate is made by the
  -- *verified* pass `Hax.tAnnotateLetBindings`
  -- (`Hax/TPhase/AnnotateLets.lean`), which is proven denotation-
  -- preserving. That pass marks TExpr nodes with the `.ann` constructor.
  -- `Hax.PrettyPrintT.injectLetTypeAnnotations` then translates each
  -- `.ann` into an ImpExpr-level marker `::annot::<TyStr>` for this
  -- renderer to recognize.
  --
  -- The marker is an `.app` whose function name starts with `::annot::`;
  -- render as a Lean type ascription `(val : T)`.
  let annot : Option String := match e with
    | .app f [inner] =>
      if f.startsWith "::annot::" then
        some s!"({toLean inner 0 boolNames} : {f.drop "::annot::".length})"
      else if f.startsWith "::namedProj::" then
        -- Newtype `.0` projection marker, injected by PrettyPrintT from
        -- a `.namedProj T x` node. Render as the type-specific unwrap
        -- `«T.0» x` (a definitional identity emitted in the preamble).
        let tname := f.drop "::namedProj::".length
        some s!"«{tname}.0» {parensIf (toLean inner 0 boolNames) (!isAtom inner)}"
      else none
    | _ => none
  if let some s := annot then s else
  match e with
  -- Literals
  | .lit (.bool true) => "true"
  | .lit (.bool false) => "false"
  | .lit (.int n) => if n < 0 then s!"({n} : Int)" else s!"({n} : Int)"
  | .lit .unit => "()"
  | .lit (.uintLit w n) => s!"({n} : {w.toLeanType})"
  | .lit (.sintLit _ n) =>
    let numStr := if n < 0 then s!"({n})" else toString n
    s!"({numStr} : Int)"
  | .unitVal => "()"

  -- Variables
  | .var "new" => "#[]"  -- Vec::new() → empty array literal (polymorphic)
  | .var n => sanitizeName n

  -- Dead ControlFlow let-bindings: discarded `_` results from a cfBreak /
  -- cfContinue / cfBreakContinue are dropped (just render body).
  | .letBind n (.cfBreak _) body | .letBind n (.cfBreakContinue _) body =>
    if n.startsWith "_" then atLine body lvl
    else
      -- A non-discarded letBind whose RHS is a cfBreak doesn't have a
      -- sensible Lean form (cfBreak short-circuits the surrounding
      -- block; nothing flows out). Emit an `unreachable!` placeholder
      -- with the right unit type. (Was previously `(sorry : Unit)`.)
      let ind := indent lvl
      s!"{ind}let {sanitizeName n} := (sorry : Unit)\n{atLine body lvl}"
  -- `letBind n (cfContinue v) body` — bind `n := v` (the continue payload)
  -- and render the body. This handles `let fri_proof = match …
  -- { Some(p) => p, None => return None }` after the explicit-match
  -- desugar wraps the Some arm in `cfContinue p`.
  | .letBind n (.cfContinue v) body =>
    if n.startsWith "_" then atLine body lvl
    else
      let ind := indent lvl
      s!"{ind}let {sanitizeName n} := {toLean v 0}\n{atLine body lvl}"
  -- Let binding: detect tuple destructuring pattern
  -- letBind "_tup" rhs (letBind "a" (proj (var "_tup") 0) (letBind "b" (proj (var "_tup") 1) body))
  -- → let (a, b) := rhs
  | .letBind n val body =>
    -- Mutation-discard pattern: let _assign := val; _assign → let _ := val; ()
    -- Prevents non-Unit _assign values from leaking as the block return value.
    if n.startsWith "_assign" && body == .var n then
      s!"{ind}let _ := {toLean val 0}\n{ind}()"
    -- Conditional _assign with self-reference: let _assign := if ... then X else _assign
    -- The else branch references the previous _assign which may have a different type.
    -- Since _assign is always discarded, render as: let _ := if ... then (let _ := X; ()) else ()
    else if n.startsWith "_assign" && (match val with | .ifThenElse _ _ (.var elsV) => elsV.startsWith "_assign" | _ => false) then
      match val with
      | .ifThenElse c thn _ =>
        let ifLvl := max lvl 1
        let ifInd := indent ifLvl
        let ifInd1 := indent (ifLvl + 1)
        s!"{ind}let _ := \n{ifInd}if {condToLean c} then\n{ifInd1}let _ := {toLean thn 0}\n{ifInd1}()\n{ifInd}else\n{ifInd1}()\n{atLine body lvl}"
      | _ => s!"{ind}let _ := {toLean val 0}\n{atLine body lvl}"
    else
    -- Match-with-cfBreak pattern: let x := (match s with | p1 => v1 | p2 => cfBreak v2); body
    -- → if-else chain (for Option/Result patterns in untyped mode) or inlined match
    -- Inlines the continuation into non-cfBreak arms to avoid type mismatch.
    -- Peek through `::annot::<T>` markers — when the typed pipeline
    -- decides to annotate a let-binding's RHS, the marker hides the
    -- underlying match from this pattern check; peel it so the
    -- inline-into-arms transform can still fire.
    let unwrappedVal : ImpExpr :=
      match val with
      | .app f [inner] => if f.startsWith "::annot::" then inner else val
      | _ => val
    let matchCfBreak := match unwrappedVal with
      | .match_ scrut arms =>
        if arms.any fun (_, b) => hasCfBreak b then some (scrut, arms) else none
      | _ => none
    match matchCfBreak with
    | some (scrut, arms) =>
      -- Inline continuation into non-cfBreak arms. For the cfBreak arms,
      -- whether to keep the `Hax.cfBreak` wrapper depends on the
      -- surrounding context:
      --   - inside a loop body: keep it (the loop expects ControlFlow);
      --   - at function tail: unwrap to the raw early-return value (the
      --     function returns `Option T`, not `ControlFlow`).
      -- Heuristic: if the surrounding `body` (the rest of the block
      -- after this letBind) eventually emits a `cfContinue` — i.e.
      -- it's already wrapping its tail in ControlFlow constructors
      -- because it's inside a loop body — keep the cfBreak. Otherwise
      -- we're at a function tail and the cfBreak's wrapper would
      -- type-mismatch the function's `Option`-typed return.
      let surroundingIsLoop : Bool :=
        let rec hasCfContinue : ImpExpr → Bool
          | .cfContinue _ => true
          | .letBind _ v b => hasCfContinue v || hasCfContinue b
          | .seq a b => hasCfContinue a || hasCfContinue b
          | .ifThenElse _ t e => hasCfContinue t || hasCfContinue e
          | .match_ _ arms => arms.any (fun (_, b) => hasCfContinue b)
          | _ => false
        hasCfContinue body
      let armLvl := max lvl 1
        let armInd := indent armLvl
        let armStrs := arms.map fun (p, armBody) =>
          if hasCfBreak armBody then
            let rendered :=
              if surroundingIsLoop then
                toLean armBody (armLvl + 1)
              else
                -- Unwrap the cfBreak to its inner value for the
                -- function-tail case.
                match extractCfBreak armBody with
                | some v => toLean v (armLvl + 1)
                | none => toLean armBody (armLvl + 1)
            s!"{armInd}| {patToLean p} => {rendered}"
          else
            let inlined := ImpExpr.letBind n armBody body
            s!"{armInd}| {patToLean p} =>\n{atLine inlined (armLvl + 1)}"
        s!"{ind}match {toLean scrut 0} with\n{"\n".intercalate armStrs}"
    | none =>
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

  -- Synthetic marker: a tail-position forFold/forFoldRev returning
  -- `ControlFlow α α` that needs to be `.merge`d to extract the value.
  -- Inserted by `wrapTailForFoldWithMerge`; consumed here.
  -- `atLine` will prepend `indent lvl` since this is treated as a leaf
  -- (it's an `.app`); we therefore don't add `{ind}` ourselves.
  | .app "_HAX_MERGE" [inner] =>
    let innerStr := (toLean inner lvl).trimLeft
    s!"({innerStr}).merge"

  -- Function application
  -- Iterator map: map(iter_expr, func_expr) → (iter_expr).map (fun v => func_expr)
  -- The func_expr typically contains a free variable (the iterator element).
  | .app "map" [iterExpr, funcExpr] =>
    -- Detect the free variable: typically .app ".field" [.var name] or .app "Struct.field" [.var name]
    let param := match funcExpr with
      | .app _ [.var v] => v
      | _ => "_el"
    s!"({toLean iterExpr 0}).map (fun {sanitizeName param} => {toLean funcExpr 0})"
  -- Iterator flat_map: flat_map(iter_expr, func_expr) → (iter_expr).flatMap (fun v => func_expr)
  | .app "flat_map" [iterExpr, funcExpr] =>
    let param := match funcExpr with
      | .app _ [.var v] => v
      | _ => "_el"
    s!"Hax.concatMap ({toLean iterExpr 0}) (fun {sanitizeName param} => {toLean funcExpr 0})"
  -- Iterator collect: collect(arr) → arr (identity in untyped mode)
  | .app "collect" [arrExpr] => toLean arrExpr lvl
  -- Iterator iter: iter(arr) → arr (identity in untyped mode)
  | .app "iter" [arrExpr] => toLean arrExpr lvl
  | .app "array_lit" args =>
    -- Emit as Lean Array literal: #[a, b, c] (matches Array types in surface code)
    let argStrs := args.map fun a => toLean a 0
    s!"#[{", ".intercalate argStrs}]"
  | .app "Not" [x] | .app "not" [x] =>
    -- For Bool args, use logical negation; for Int args, use polymorphic Hax.Not
    -- (Hax.Not uses HaxNot typeclass: Bool → !, Int → bitwise complement)
    if isKnownBool x then s!"(!{parensIf (toLean x 0) (!isAtom x)})"
    else s!"(Hax.Not {parensIf (toLean x 0) (!isAtom x)})"
  -- panic/panic_fmt → unit (Rust panics become no-ops in the extraction)
  | .app "panic" _ | .app "panic_fmt" _ => "()"
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
      else atLine e (ifLvl + 1)
    -- When else-branch has ControlFlow but then is unitVal, then needs Hax.cfContinue ()
    let tStr := if t == .unitVal && hasControlFlowNodes e then
        s!"{ifInd1}Hax.cfContinue ()"
      else ""  -- empty means use default rendering below
    let condStr := condToLean c
    -- When then is unitVal but else has ControlFlow: use cfContinue for then-branch
    if tStr != "" then
      s!"{ifInd}if {condStr} then\n{tStr}\n{ifInd}else\n{eStr}"
    -- When else is unitVal and then is non-ControlFlow, non-unit:
    -- Wrap then-branch in `let _ := ...; ()` so both branches return Unit.
    -- This handles assert/panic patterns (if !cond then panic(...) else ())
    -- and avoids type mismatches between non-Unit then and Unit else.
    else if e == .unitVal && !hasControlFlowNodes t && t != .unitVal then
      s!"{ifInd}if {condStr} then\n{ifInd1}let _ := {toLean t (ifLvl + 1)}\n{ifInd1}()\n{ifInd}else\n{ifInd1}()"
    else
      s!"{ifInd}if {condStr} then\n{atLine t (ifLvl + 1)}\n{ifInd}else\n{eStr}"

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
        | [(_, body)] => atLine body (ifLvl + 1)
        | (p, body) :: rest =>
          match p with
          | .varPat n =>
            -- Parenthesize compound scrutinee to avoid multi-arg Hax.beq
            let scrutParen := if isAtom scrut then scrutStr else s!"({scrutStr})"
            s!"{ifInd}if Hax.beq {scrutParen} {sanitizeName n} then\n{atLine body (ifLvl + 1)}\n{ifInd}else\n{ifChain rest}"
          | _ => atLine body (ifLvl + 1) -- wildcard/fallback
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
    -- Render `Hax.cfBreak <e>` without a hardcoded type annotation on
    -- `none` / Bool literals. Earlier the renderer wrote
    -- `(none : Option (Array Int))` and `(true : Bool)` to "help" Lean,
    -- but the `Option (Array Int)` was wrong whenever the surrounding
    -- function returned `Option T` for any other `T` — this was a TCB
    -- heuristic baked to one particular crate. The correct annotation
    -- belongs in a verified TPhase that knows the surrounding return
    -- type; in its absence, leave the value bare and let Lean infer.
    let eStr := parensIf (toLean e 0) (!isAtom e)
    s!"Hax.cfBreak {eStr}"
  | .cfContinue e =>
    -- For `cfContinue ()` specifically, Lean cannot infer the implicit
    -- break-type `B` (no constraints flow into it), so emit it with
    -- `(B := Unit)` to break the metavariable cycle. The continue-type
    -- `C` is constrained by the unit literal.
    -- Match both `.unitVal` and `.tuple []` (the empty-accumulator case
    -- produces the latter via `accTuple []`).
    match e with
    | .unitVal => "Hax.cfContinue ()"
    | .tuple [] => "Hax.cfContinue ()"
    | _ => s!"Hax.cfContinue {parensIf (toLean e 0) (!isAtom e)}"
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
      -- Even with empty accs, wrap if-then-else branches that need ControlFlow
      let body' := transformWhileFoldBody [] body
      s!"{ind}Hax.whileFold () (fun _ => {toLean c 0}) fun _acc =>\n{atLine body' (lvl + 1)}"
  | .forFoldReturn v lo hi body =>
    let accs := extractAccumulators body
    let (initStr, paramStr) := accStrings accs
    -- First wrap bare values/accumulators in cfContinue (forFoldReturn body must return ControlFlow)
    let body' := transformForFoldCfBody accs body
    -- Then nest cfBreak for early function returns
    let body' := nestCfBreakForReturn body'
    s!"{ind}Hax.forFoldReturn {parensIf (toLean lo 0) (!isAtom lo)} {parensIf (toLean hi 0) (!isAtom hi)} {initStr} fun {sanitizeName v} {paramStr} =>\n{atLine body' (lvl + 1)}"
  | .forFoldRevReturn v lo hi body =>
    let accs := extractAccumulators body
    let (initStr, paramStr) := accStrings accs
    let body' := transformForFoldCfBody accs body
    let body' := nestCfBreakForReturn body'
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
      - Function applications known to return Bool (via `boolNames` from TExpr types) pass through.
      - `Not x` on a variable → `Hax.beq x (0 : Int)` (correct negation for Int).
      - `Not x` on a Bool expr → `!x`.
      - Bare variables → `Hax.bne x (0 : Int)` (forces Int, C-style truth). -/
  condToLean (c : ImpExpr) : String :=
    -- Type-directed Bool detection: check boolNames from TExpr types
    let isTypedBool (e : ImpExpr) : Bool := match e with
      | .app f _ => boolNames.contains f | _ => false
    match c with
    | .app "Not" [x] | .app "not" [x] =>
      if isKnownBool x || isTypedBool x then
        s!"!{parensIf (toLean x 0) (!isAtom x)}"
      else s!"Hax.beq {parensIf (toLean x 0) (!isAtom x)} 0"
    | .app _ _ =>
      if isKnownBool c || isTypedBool c then toLean c 0
      else s!"{parensIf (toLean c 0) (!isAtom c)} = true"
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
    if !hasSurfaceControlFlow body && !accs.isEmpty then
      -- Simple fold with accumulators, no ControlFlow
      let body' := simplifyFoldBody (transformFoldBody accs body)
      -- Inner forFold-with-CF in tail position would return ControlFlow; wrap with .merge
      let body' := wrapTailForFoldWithMerge body'
      -- Inner fold whose accumulator shape differs from outer's needs
      -- a destructure + outer-tuple-return wrapper.
      let body' := wrapTailFoldForOuterAccs accs body'
      s!"{ind}Hax.{simpleName} {loStr} {hiStr} {initStr} fun {sanitizeName v} {paramStr} =>\n{atLine body' (lvl + 1)}"
    else if accs.isEmpty && !hasSurfaceControlFlow body then
      -- Unit-accumulator fold (side-effect loop, no surface ControlFlow)
      -- Render as simple fold with `let _ := body; ()`
      let bodyStr := if isLeafExpr body then toLean body 0
                     else s!"\n{toLean body (lvl + 2)}"
      s!"{ind}Hax.{simpleName} {loStr} {hiStr} {initStr} fun {sanitizeName v} {paramStr} =>\n{ind1}let _ := {bodyStr}\n{ind1}()"
    else
      -- ControlFlow fold (has break/continue)
      -- Transform body: wrap bare () and accumulator returns in cfContinue
      let body' := transformForFoldCfBody accs body
      s!"{ind}Hax.{cfName} {loStr} {hiStr} {initStr} fun {sanitizeName v} {paramStr} =>\n{atLine body' (lvl + 1)}"
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
    -- Conditional _assign with self-reference in seq context
    | .letBind n (.ifThenElse c thn (.var elsV)) body, _ =>
      if n.startsWith "_assign" && elsV.startsWith "_assign" then
        let ifLvl := max lvl 1
        let ifInd := indent ifLvl
        let ifInd1 := indent (ifLvl + 1)
        s!"{ind}let _ := \n{ifInd}if {condToLean c} then\n{ifInd1}let _ := {toLean thn 0}\n{ifInd1}()\n{ifInd}else\n{ifInd1}()\n{seqToLean lvl body e2}"
      else
        s!"{ind}let {sanitizeName n} := {toLean (.ifThenElse c thn (.var elsV)) 0}\n{seqToLean lvl body e2}"
    -- Mutation-discard _assign in seq: seq (letBind "_assign" val (var "_assign")) rest
    -- Render as `let _ := val` to avoid type-leaking _assign bindings
    | .letBind n v (.var vn), _ =>
      if n.startsWith "_assign" && n == vn then
        s!"{ind}let _ := {toLean v 0}\n{seqToLean lvl (.var vn) e2}"
      else
        s!"{ind}let {sanitizeName n} := {toLean v 0}\n{seqToLean lvl (.var vn) e2}"
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
        -- Skip guard pattern if retVal is a cfBreak (double-nested forFoldReturn context).
        -- In that case, fall through to normal rendering to preserve ControlFlow nesting.
        match retVal with
        | .cfBreak _ =>
          let ifLvl := max lvl 1
          s!"{indent ifLvl}if {condToLean cond} then\n{atLine (.cfBreak retVal) (ifLvl + 1)}\n{indent ifLvl}else\n{atLine e2 (ifLvl + 1)}"
        | _ =>
          let ifLvl := max lvl 1
          let ifInd := indent ifLvl
          -- Use stripCfBreak to preserve let-bindings before the return value
          let thnStripped := stripCfBreak thn
          s!"{ifInd}if {condToLean cond} then\n{atLine thnStripped (ifLvl + 1)}\n{ifInd}else\n{atLine e2 (ifLvl + 1)}"
      | none, some retVal =>
        -- Inverted: if cond then continue else break → if !cond then val else rest
        -- Same double-nesting check as above
        match retVal with
        | .cfBreak _ =>
          let ifLvl := max lvl 1
          s!"{indent ifLvl}if !({condToLean cond}) then\n{atLine (.cfBreak retVal) (ifLvl + 1)}\n{indent ifLvl}else\n{atLine e2 (ifLvl + 1)}"
        | _ =>
          let ifLvl := max lvl 1
          let ifInd := indent ifLvl
          -- Use stripCfBreak to preserve let-bindings before the return value
          let elsStripped := stripCfBreak els
          s!"{ifInd}if !({condToLean cond}) then\n{atLine elsStripped (ifLvl + 1)}\n{ifInd}else\n{atLine e2 (ifLvl + 1)}"
      | _, _ =>
      -- Guard pattern in ControlFlow context: if cond then () else <work-with-CF>; rest
      -- The () needs to become Hax.cfContinue () so both branches have ControlFlow type
      if thn == .unitVal && (hasSurfaceControlFlow els || hasSurfaceControlFlow e2) then
        let ifLvl := max lvl 1
        let ifInd := indent ifLvl
        let ifInd1 := indent (ifLvl + 1)
        s!"{ifInd}if {condToLean cond} then\n{ifInd1}Hax.cfContinue ()\n{ifInd}else\n{atLine els (ifLvl + 1)}\n{seqToLean lvl .unitVal e2}"
      else if els == .unitVal && hasSurfaceControlFlow thn then
        -- thn has surface CF (e.g., cfBreak/cfContinue), wrap the els in cfContinue to match types
        let ifLvl := max lvl 1
        let ifInd := indent ifLvl
        let ifInd1 := indent (ifLvl + 1)
        s!"{ifInd}if {condToLean cond} then\n{atLine thn (ifLvl + 1)}\n{ifInd}else\n{ifInd1}Hax.cfContinue ()\n{seqToLean lvl .unitVal e2}"
      else if els == .unitVal then
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
            -- _assign variables are intermediate mutation artifacts; always use `let _ :=`
            if name.startsWith "_assign" then
              let ifLvl := max lvl 1
              let ifInd := indent ifLvl
              let ifInd1 := indent (ifLvl + 1)
              (inits, conds ++ [s!"{ind}let _ := \n{ifInd}if {condToLean cond} then\n{ifInd1}let _ := {toLean rhs 0}\n{ifInd1}()\n{ifInd}else\n{ifInd1}()"], seen)
            else if seen.contains name then
              -- Already seen this name — emit as conditional mutation
              (inits, conds ++ [s!"{ind}let {sanitizeName name} := if {condToLean cond} then {toLean rhs 0} else {sanitizeName name}"], seen)
            else
              -- First occurrence: check if this name has a later mutation (self-ref fix).
              -- BUT: only treat as "fresh init" if the rhs does NOT reference `name` itself.
              -- If `rhs` references `name` (e.g. `temp[0] = SBOX[temp[1]]`), then this is
              -- a real conditional mutation, not an init, and must be emitted conditionally.
              let hasDuplicate := (trueMuts.filter fun p => p.1 == name).length > 1
              let isSelfRef := exprContainsVar name rhs
              if hasDuplicate && !isSelfRef then
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
            if name.startsWith "_assign" then
              let ifLvl := max lvl 1
              let ifInd := indent ifLvl
              let ifInd1 := indent (ifLvl + 1)
              s!"{ind}let _ := \n{ifInd}if {condToLean cond} then\n{ifInd1}let _ := {toLean thnRhs 0}\n{ifInd1}()\n{ifInd}else\n{ifInd1}let _ := {toLean elsRhs 0}\n{ifInd1}()"
            else
              s!"{ind}let {sanitizeName name} := if {condToLean cond} then {toLean thnRhs 0} else {toLean elsRhs 0}"
          s!"{"\n".intercalate mutStr}\n{atLine e2 lvl}"
        else
          let valStr := if isLeafExpr e1 then toLean e1 0 else s!"\n{toLean e1 (lvl + 1)}"
          s!"{ind}let _ := {valStr}\n{atLine e2 lvl}"
    -- Skip dead ControlFlow expressions in seq (cfBreak/cfContinue/cfBreakContinue)
    | .cfBreak _, _ => atLine e2 lvl
    | .cfContinue _, _ => atLine e2 lvl
    | .cfBreakContinue _, _ => atLine e2 lvl
    -- Match in seq position: wrap each arm to return Unit so all arms have the same type.
    -- This handles patterns like `match x with | 0 => foldRange... | _ => ()` where some
    -- arms mutate accumulators (returning Array Int) and others are dead (returning Unit).
    | .match_ scrut arms, _ =>
      let hasUnitArm := arms.any fun (_, b) => b == .unitVal
      let hasNonUnitArm := arms.any fun (_, b) => b != .unitVal
      if hasUnitArm && hasNonUnitArm then
        -- Heterogeneous arms: wrap all in `let _ := body; ()` for uniform Unit type
        let armLvl := max lvl 1 + 1
        let armInd := indent armLvl
        let armStrs := arms.map fun (p, body) =>
          if body == .unitVal then s!"{armInd}| {patToLean p} => ()"
          else s!"{armInd}| {patToLean p} => let _ := {toLean body 0}\n{armInd}  ()"
        let matchInd := indent (max lvl 1)
        s!"{ind}let _ := \n{matchInd}match {toLean scrut 0} with\n{"\n".intercalate armStrs}\n{atLine e2 lvl}"
      else
        let valStr := if isLeafExpr e1 then toLean e1 0 else s!"\n{toLean e1 (lvl + 1)}"
        s!"{ind}let _ := {valStr}\n{atLine e2 lvl}"
    -- General case: skip assert blocks, eliminate dead code, discard e1's value otherwise
    | _, _ =>
      -- Skip assert_eq!/assert! blocks (Rust runtime assertions with unsynthesizable types)
      if isAssertBlock e1 then atLine e2 lvl
      -- Dead code elimination: if e1 fully returns ControlFlow (both branches of if-else
      -- have cfBreak/cfContinue), e2 is unreachable — skip it
      else if hasSurfaceControlFlow e1 then atLine e1 lvl
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
    -- Check if this fold uses ControlFlow (forFold instead of foldRange).
    -- If so, the result is `ControlFlow β α` and needs `.merge` to extract the value.
    let isCf := hasSurfaceControlFlow body
    -- Emit init overrides for accumulators that need default initialization
    let overrides := accInitOverrides accs body
    let initPrefix := if overrides.isEmpty then ""
      else overrides.map (fun (n, e) =>
        s!"{ind}let {sanitizeName n} := {toLean e 0}\n") |> String.join
    if accs.isEmpty then
      s!"{ind}let _ := {foldStr}\n{atLine tail lvl}"
    else if isCf then
      -- ControlFlow fold: result is ControlFlow, use .merge
      if accs.length == 1 then
        let acc := accs.head!
        match tail with
        | .var n => if n == acc then s!"{initPrefix}{ind}({foldStr}).merge"
                    else s!"{initPrefix}{ind}let _wf := {foldStr}\n{ind}let {sanitizeName acc} := _wf.merge\n{atLine tail lvl}"
        | _ => s!"{initPrefix}{ind}let _wf := {foldStr}\n{ind}let {sanitizeName acc} := _wf.merge\n{atLine tail lvl}"
      else
        let accStr := ", ".intercalate (accs.map sanitizeName)
        s!"{initPrefix}{ind}let _wf := {foldStr}\n{ind}let ({accStr}) := _wf.merge\n{atLine tail lvl}"
    else if accs.length == 1 then
      let acc := accs.head!
      -- If the tail just reads the accumulator, the fold IS the return value
      match tail with
      | .var n => if n == acc then s!"{initPrefix}{toLean foldExpr lvl}"
                  else s!"{initPrefix}{ind}let {sanitizeName acc} := {foldStr}\n{atLine tail lvl}"
      | _ => s!"{initPrefix}{ind}let {sanitizeName acc} := {foldStr}\n{atLine tail lvl}"
    else
      let accStr := ", ".intercalate (accs.map sanitizeName)
      s!"{initPrefix}{ind}let ({accStr}) := {foldStr}\n{atLine tail lvl}"
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
    -- Emit init overrides for accumulators that need default initialization
    let overrides := accInitOverrides accs body
    let initPrefix := if overrides.isEmpty then ""
      else overrides.map (fun (n, e) =>
        s!"{ind}let {sanitizeName n} := {toLean e 0}\n") |> String.join
    if accs.isEmpty then
      s!"{ind}let _ := {foldStr}\n{atLine tail lvl}"
    else if accs.length == 1 then
      let acc := accs.head!
      match tail with
      | .var n => if n == acc then s!"{initPrefix}{ind}({foldStr}).merge"
                  else s!"{initPrefix}{ind}let _wf := {foldStr}\n{ind}let {sanitizeName acc} := _wf.merge\n{atLine tail lvl}"
      | _ => s!"{initPrefix}{ind}let _wf := {foldStr}\n{ind}let {sanitizeName acc} := _wf.merge\n{atLine tail lvl}"
    else
      let accStr := ", ".intercalate (accs.map sanitizeName)
      s!"{initPrefix}{ind}let _wf := {foldStr}\n{ind}let ({accStr}) := _wf.merge\n{atLine tail lvl}"
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
      -- Emit init overrides for accumulators that need default initialization
      let overrides := accInitOverrides accs body
      let initPrefix := if overrides.isEmpty then ""
        else overrides.map (fun (n, e) =>
          s!"{ind}let {sanitizeName n} := {toLean e 0}\n") |> String.join
      -- Render the tail expression to detect its type for annotations
      let tailStr := (atLine tail (lvl + 1)).trimRight
      if accs.isEmpty then
        -- forFoldReturn returns ControlFlow β (ControlFlow γ Unit)
        -- We need to annotate to fix unresolvable γ
        s!"{initPrefix}{ind}let _fr := {foldStr}\n{ind}match (show ControlFlow _ (ControlFlow Unit Unit) from _fr) with\n{ind}| .Break _v => _v\n{ind}| .Continue _ =>\n{atLine tail (lvl + 1)}"
      else
        let accStr := ", ".intercalate (accs.map sanitizeName)
        let destr := if accs.length == 1 then sanitizeName accs.head! else s!"({accStr})"
        -- Render the tail unchanged. Earlier versions wrapped Bool tail
        -- literals in `Hax.boolToInt` whenever a heuristic guessed the
        -- function's return type was Int. That decision belongs in the
        -- typed pipeline (where the TExpr's annotated type is
        -- authoritative), not in the renderer. Keeping the renderer
        -- straight-line trivial removes TCB; any necessary type
        -- adjustment must be performed by a verified TPhase that
        -- normalises the AST so the trivial render produces well-typed
        -- Lean.
        let tailRendered := atLine tail (lvl + 1)
        -- Detect a nested-loop body that uses `cfBreak (cfBreak _)` to
        -- propagate an early-return up two levels. The inner match's
        -- `.Break _v` arm must then re-wrap `_v` as a cfBreak so the
        -- outer loop body's expected `ControlFlow B C` type is
        -- preserved.
        let hasNestedCfBreak : Bool :=
          let rec scan : ImpExpr → Bool
            | .cfBreak (.cfBreak _) => true
            | .cfBreak v => scan v
            | .letBind _ v b => scan v || scan b
            | .seq a b => scan a || scan b
            | .ifThenElse _ t e => scan t || scan e
            | .match_ _ arms => arms.any (fun (_, b) => scan b)
            | .whileFold _ b | .whileFoldReturn _ b => scan b
            | .forFold _ _ _ b | .forFoldRev _ _ _ b
            | .forFoldReturn _ _ _ b | .forFoldRevReturn _ _ _ b => scan b
            | _ => false
          scan body || scan tail
        let breakArm :=
          if hasNestedCfBreak then "Hax.cfBreak _v" else "_v"
        s!"{initPrefix}{ind}let _fr := {foldStr}\n{ind}match _fr with\n{ind}| .Break _v => {breakArm}\n{ind}| .Continue _cf =>\n{ind1}let {destr} := ControlFlow.merge _cf\n{tailRendered}"
    else
      seqFold lvl foldExpr body tail

/-- Collect all projection names applied to a given variable (simple version for param inference).
    Looks for `.app ".field" [.var varName]` and `.app "Struct.field" [.var varName]` patterns. -/
private partial def collectProjectionsOnVar' (varName : String) : ImpExpr → List String
  | .app f [.var v] =>
    if v == varName && (f.startsWith "." || f.contains '.') then
      -- Extract the field name from ".field" or "Struct.field"
      let fname := if f.startsWith "." then (f.drop 1).toString
        else match f.splitOn "." with | [_, n] => n | _ => ""
      if fname.isEmpty then [] else [fname]
    else []
  | .app _ args => args.foldl (fun acc a => acc ++ collectProjectionsOnVar' varName a) []
  | .letBind _ v body =>
    collectProjectionsOnVar' varName v ++ collectProjectionsOnVar' varName body
  | .seq a b => collectProjectionsOnVar' varName a ++ collectProjectionsOnVar' varName b
  | .ifThenElse c t e =>
    collectProjectionsOnVar' varName c ++ collectProjectionsOnVar' varName t ++
    collectProjectionsOnVar' varName e
  | .tuple es => es.foldl (fun acc e => acc ++ collectProjectionsOnVar' varName e) []
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    collectProjectionsOnVar' varName lo ++ collectProjectionsOnVar' varName hi ++
    collectProjectionsOnVar' varName body
  | .whileFold c body =>
    collectProjectionsOnVar' varName c ++ collectProjectionsOnVar' varName body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    collectProjectionsOnVar' varName lo ++ collectProjectionsOnVar' varName hi ++
    collectProjectionsOnVar' varName body
  | .whileFoldReturn c body =>
    collectProjectionsOnVar' varName c ++ collectProjectionsOnVar' varName body
  | .cfBreak e | .cfContinue e | .cfBreakContinue e =>
    collectProjectionsOnVar' varName e
  | .match_ scrut arms =>
    collectProjectionsOnVar' varName scrut ++
    arms.foldl (fun acc (_, b) => acc ++ collectProjectionsOnVar' varName b) []
  | _ => []

/-- Collect all function calls where a given variable is passed as an argument.
    Returns list of (calleeName, argIndex). -/
private partial def collectCallsOnVar (varName : String) : ImpExpr → List (String × Nat)
  | .app f args =>
    let thisCall := (args.zip (List.range args.length)).findSome? fun (a, i) =>
      if a == .var varName then some (f, i) else none
    let sub := args.foldl (fun acc a => acc ++ collectCallsOnVar varName a) []
    match thisCall with | some c => c :: sub | none => sub
  | .letBind _ v body => collectCallsOnVar varName v ++ collectCallsOnVar varName body
  | .seq a b => collectCallsOnVar varName a ++ collectCallsOnVar varName b
  | .ifThenElse c t e => collectCallsOnVar varName c ++ collectCallsOnVar varName t ++ collectCallsOnVar varName e
  | _ => []

private def inferParamStructType
    (structMeta : List (String × List (String × String × ImpType)))
    (structLookup : String → Option String)
    (paramName : String) (body : ImpExpr)
    (fnTypes : List (String × HaxAdapter.FnTypeInfo) := []) : Option String :=
  if structMeta.isEmpty then none
  else
    let projs := (collectProjectionsOnVar' paramName body).eraseDups
    if projs.isEmpty then
      -- No direct field access; check if param is passed to a function with struct-typed params
      let calleeStructType := collectCallsOnVar paramName body |>.findSome? fun (callee, argIdx) =>
        match fnTypes.find? (·.1 == callee) with
        | some (_, ti) =>
          if argIdx < ti.paramTypes.length then
            let (_, paramTy) := ti.paramTypes[argIdx]!
            -- Strip Ref wrapper
            let innerTy := match paramTy with | .ref inner _ => inner | t => t
            -- Check if it's a known struct ADT
            match innerTy with
            | .adt adtName _ =>
              let shortName := match adtName.splitOn "::" with | [] => adtName | segs => segs.getLast!
              match structMeta.find? (·.1 == shortName) with
              | some (sname, fields) =>
                if fields.length <= 1 then none  -- skip trivial structs
                else
                  let strs := fields.map fun (_, t, _) => if t == "int" then "Int" else "Array Int"
                  some (" × ".intercalate strs)
              | none => none
            | _ => none
          else none
        | none => none
      calleeStructType
    else
      let candidates := structMeta.filter fun (_, fields) =>
        projs.any fun proj => fields.any (·.1 == proj)
      -- Resolve struct type as tuple (never pass-through).
      -- When a parameter has field projections, it MUST be the tuple type.
      -- Use structLookup but override pass-through structs with tuple representation.
      let tupleResolve : String → Option String := fun name =>
        match structMeta.find? (·.1 == name) with
        | some (_, fields) =>
          if fields.length == 0 then some "Array Int"
          else if fields.length == 1 then
            let (_, tag, _) := fields.head!
            some (if tag == "int" then "Int" else "Array Int")
          else
            let strs := fields.map fun (_, t, _) =>
              let s := if t == "int" then "Int" else "Array Int"
              s
            some (" × ".intercalate strs)
        | none => none
      match candidates with
      | [] => none
      | [(sname, _)] => tupleResolve sname
      | _ =>
        let scored := candidates.map fun (sname, fields) =>
          let matchCount := (projs.filter fun proj => fields.any (·.1 == proj)).length
          (sname, matchCount, fields.length)
        let best := scored.foldl (fun acc (sname, mc, fl) =>
          match acc with
          | none => some (sname, mc, fl)
          | some (_, bestMc, bestFl) =>
            if mc > bestMc then some (sname, mc, fl)
            else if mc == bestMc && fl < bestFl then some (sname, mc, fl)
            else acc) none
        best.bind fun (sname, _, _) => tupleResolve sname

/-- Extract leading identity let-bindings (let x := x) as function parameters.
    These are emitted by HaxAdapter for Rust function parameters. -/
private def extractParams : ImpExpr → List String × ImpExpr
  | .letBind n (.var v) body =>
    if n == v then
      -- Include all parameters, including _-prefixed unused ones.
      -- Skipping _-prefixed params causes arity mismatches at call sites.
      let (ps, rest) := extractParams body
      (n :: ps, rest)
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
    When `fnTypeInfo` is provided, uses real types from hax JSON instead of heuristics.
    `structMeta` enables struct type inference from projection usage on params. -/
def toLeanDef (name : String) (e : ImpExpr) (annotateTypes : Bool := false)
    (fnTypeInfo : Option HaxAdapter.FnTypeInfo := none)
    (structLookup : String → Option String := fun _ => none)
    (structMeta : List (String × List (String × String × ImpType)) := [])
    (allFnTypes : List (String × HaxAdapter.FnTypeInfo) := []) : String :=
  let (params, body) := extractParams e
  let arrayParams := if annotateTypes && fnTypeInfo.isNone then
      (collectArrayParams params body).eraseDups
    else []
  let inferStructTypeForParam (p : String) : Option String :=
    inferParamStructType structMeta structLookup p body allFnTypes
  let paramStr := if params.isEmpty then ""
    else " " ++ " ".intercalate (params.map fun p =>
      let sn := sanitizeName p
      -- Use real type from fnTypeInfo when available.
      -- Skip Bool (ImpExpr world uses Int for booleans via Hax.bne x 0).
      -- Annotate Int, Array, Slice, Adt (via structLookup) to prevent
      -- wrong inference (e.g., u16 param inferred as Array Int).
      match fnTypeInfo >>= fun ti => ti.paramTypes.find? (·.1 == p) with
      | some (_, .unknown) | some (_, .bool) =>
        -- Check struct projection usage for unknown/Bool params
        match inferStructTypeForParam p with
        | some st => s!"({sn} : {st})"
        | none =>
          if annotateTypes && arrayParams.contains p then s!"({sn} : Array Int)"
          else sn
      | some (_, .tuple _) =>
        -- Tuple type from hax: use it directly via toLeanTypeStr
        match fnTypeInfo >>= fun ti => ti.paramTypes.find? (·.1 == p) with
        | some (_, ty) =>
          let tyStr := ty.toLeanTypeStr structLookup
          if (tyStr.splitOn " × ").length > 1 then s!"({sn} : {tyStr})"
          else sn
        | none => sn
      | some (_, ty) =>
        -- In untyped (certified) mode, collapse integer types to Int
        -- to avoid conflicts with untyped runtime ops (Hax.add, etc.)
        let tyStr := ty.toLeanTypeStr structLookup
        if ty.isIntLike then s!"({sn} : Int)"
        else if tyStr == "Int" then
          -- Type resolved to Int but might be a struct — check projection usage
          match inferStructTypeForParam p with
          | some st => s!"({sn} : {st})"
          | none => s!"({sn} : Int)"
        else if tyStr == "Array Int" then
          -- Pass-through struct or actual Array Int — check projection usage
          match inferStructTypeForParam p with
          | some st => s!"({sn} : {st})"
          | none => s!"({sn} : Array Int)"
        else if tyStr.startsWith "Array" && !(tyStr.splitOn " × ").length > 1 then s!"({sn} : {tyStr})"
        else if (tyStr.splitOn " × ").length > 1 then s!"({sn} : {tyStr})"  -- struct tuple type
        else sn  -- unknown/complex types: no annotation
      | none =>
        -- No type info from hax — check struct projection usage
        match inferStructTypeForParam p with
        | some st => s!"({sn} : {st})"
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
  let defs := defs.map fun (n, e) => (n, Hax.Canonicalize.canonicalize e)
  let header := s!"/-\n  Auto-generated by haxpipe (verified hax pipeline)\n-/\nimport Hax.Runtime\n\nnamespace {moduleName}\n\n"
  let body := "\n".intercalate (defs.map fun (n, e) => toLeanDef n e)
  let footer := s!"\nend {moduleName}\n"
  header ++ body ++ footer

/-! ## HaxBridge Template Generation

Generate CatCrypt HaxBridge boilerplate from extracted function names.

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
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.{ucModuleName}.Security
-- import CatCrypt.Crypto.{ucModuleName}.Extraction.{protocolName}_hax

/-!
# {protocolName} — Hax Bridge

Connects extracted implementation to the UC security proof.

## Architecture

Extracted pure functions plug directly into the Dependencies typeclass.
No intermediate PureCrypto record or RustM wrapping needed.
-/

set_option autoImplicit false

open Hax.Core CatCrypt.Prob CatCrypt.Crypto
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
  | .bool b => s!"ImpLit.bool {b}"
  | .int n => if n < 0 then s!"ImpLit.int ({n})" else s!"ImpLit.int {n}"
  | .unit => "ImpLit.unit"
  | .uintLit w n => s!"ImpLit.uintLit .{w.toSuffix} {n}"
  | .sintLit w n => s!"ImpLit.sintLit .{w.toSuffix} {n}"

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
  | .ctorPat name args =>
      s!".ctorPat \"{name}\" [{", ".intercalate (args.map patToConstructor)}]"

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
  s!"def {sanitizeName (name ++ "_impExpr")} : ImpExpr :=\n  {toLeanImpExpr e}\n"

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
  | "panic" | "literal" | "deref" | "clone" | "to_vec" | "copy_from_slice"
  | "extend_from_slice" | "truncate" | "sha256"
  | "with_capacity" | "into_vec" | "into_iter" | "next"
  | "from_elem" | "RangeTo" | "RangeFrom" | "Range" | "min" | "max"
  | "count_ones" | "assert_failed" | "index_mut" | "enumerate"
  | "is_empty" | "from" => true
  | _ => false

/-- Check if a name is ALWAYS a builtin runtime op and NEVER a cross-crate dep.
    This is the exclusion list from `generatePreamble`, factored out for reuse.
    Names like `mul` are NOT here because they can be cross-crate deps. -/
def isAlwaysBuiltin (f : String) : Bool :=
  match f with
  | "index" | "array_update" | "repeat" | "array_lit" | "push" | "len"
  | "copy_from_slice" | "extend_from_slice" | "truncate"
  | "with_capacity" | "into_vec" | "into_iter" | "iter" | "map" | "collect" | "flat_map" | "zip" | "next" | "new"
  | "from_elem" | "RangeTo" | "RangeFrom" | "Range"
  | "count_ones" | "assert_failed" | "index_mut" | "enumerate" | "is_empty"
  | "from" | "into" | "literal" | "deref" | "clone" | "to_vec" | "cast" | "castVal"
  | "castVal_w" | "bitxor_w" | "bitand_w" | "bitor_w" | "shr_w" | "shl_w"
  | "wrapping_add_w" | "wrapping_sub_w" | "wrapping_mul_w" | "from_val"
  | "assert_failed'"
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
  -- Width-annotated ops (wrapping_add#32, rotate_right#32, etc.)
  | f => f.any (· == '#')

/-- Check if a name looks like a struct field projection (starts with "." or is "Struct.field"). -/
def isFieldProjection (f : String) : Bool :=
  f.startsWith "." || f.contains '.'

/-- Collect free variables: `.var` names not bound by enclosing `letBind`.
    Returns (name, 0) pairs so they can be merged with `collectAppCalls` results. -/
partial def collectFreeVars (bound : List String := []) : ImpExpr → List String
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
partial def collectAppCalls : ImpExpr → List (String × Nat)
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
partial def detectReturnArity (fname : String) : ImpExpr → Nat
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
partial def isVarUsedAsInt (varName : String) : ImpExpr → Bool
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
    -- Also check struct projections (names like ".field" or "Struct.field")
    if knownIntNames.contains f || intProjNames.contains f then true
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
    (depth : Nat := 0)
    (callRetTypes : List (String × ImpType) := []) : ImpExpr → Option ImpType
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
        inferExprType paramTypeMap structMeta fnBody defsMap (depth + 1) callRetTypes bindExpr
      | none =>
        -- Try cross-def resolution (0-arity mutual defs like ZERO_TOKEN)
        match defsMap.find? (·.1 == v) with
        | some (_, defExpr) =>
          inferExprType paramTypeMap structMeta none defsMap (depth + 1) callRetTypes defExpr
        | none => none
  | .lit (.int _) => some .int
  | .lit (.uintLit _ _) => some .int
  | .lit (.bool _) => some .bool
  | .tuple elems =>
    let elemTypes := elems.filterMap (inferExprType paramTypeMap structMeta fnBody defsMap (depth + 1) callRetTypes)
    if elemTypes.length == elems.length then some (.tuple elemTypes) else none
  | .app "index" [arr, .app "RangeTo" _] | .app "index" [arr, .app "RangeFrom" _]
  | .app "index" [arr, .app "Range" _]
  | .app "index_mut" [arr, .app "RangeTo" _] | .app "index_mut" [arr, .app "RangeFrom" _]
  | .app "index_mut" [arr, .app "Range" _] =>
    -- Slice operation: returns the same array type (not element type)
    inferExprType paramTypeMap structMeta fnBody defsMap depth callRetTypes arr
  | .app "index" [arr, _] | .app "index_" [arr, _] =>
    match inferExprType paramTypeMap structMeta fnBody defsMap depth callRetTypes arr with
    | some (.array inner _) => some inner
    | some (.slice inner) => some inner
    | _ => none
  | .app "repeat_" [val, _] | .app "repeat" [val, _] | .app "from_elem" [val, _] =>
    match inferExprType paramTypeMap structMeta fnBody defsMap depth callRetTypes val with
    | some t => some (.array t 0)
    | _ => none
  | .app "with_capacity" _ => some (.array .unknown 0)
  | .app "array_update" [arr, _, _] =>
    inferExprType paramTypeMap structMeta fnBody defsMap depth callRetTypes arr
  | .app "push" [arr, _] =>
    inferExprType paramTypeMap structMeta fnBody defsMap depth callRetTypes arr
  | .app sname _ =>
    if structMeta.any (·.1 == sname) then some (.adt sname [])
    else
      -- Try call return types from hax JSON (dep return types)
      match callRetTypes.find? (·.1 == sname) with
      | some (_, retTy) => if retTy.isUnknown then none else some retTy
      | none =>
        if depth < 3 then
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
    (callRetTypes : List (String × ImpType) := [])
    : ImpExpr → List (List (Option ImpType))
  | .app f args =>
    let sub := args.foldl (fun acc a => acc ++ detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes a) []
    if f == fname && args.length == arity then
      let argTypes := args.map fun a => inferExprType paramTypeMap structMeta fnBody defsMap 0 callRetTypes a
      [argTypes] ++ sub
    else sub
  | .letBind _ v body =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes v ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes body
  | .seq a b =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes a ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes b
  | .ifThenElse c t e =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes c ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes t ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes e
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes lo ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes hi ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes body
  | .whileFold c body =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes c ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes lo ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes hi ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes body
  | .whileFoldReturn c body =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes c ++
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes body
  | .tuple es => es.foldl (fun acc e => acc ++ detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes e) []
  | .proj e _ => detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes e
  | .match_ scrut arms =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes scrut ++
    arms.foldl (fun acc (_, b) => acc ++ detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes b) []
  | .cfBreak e | .cfContinue e | .cfBreakContinue e =>
    detectTypedArgs fname arity paramTypeMap structMeta fnBody defsMap callRetTypes e
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
    (callRetTypes : List (String × ImpType) := [])
    : ImpExpr → Bool
  | .app f args =>
    let inArgs := args.any (detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes)
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
            let arrType := inferExprType paramTypeMap structMeta fnBody defsMap 0 callRetTypes arrExpr
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
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes v ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes body
  | .seq a b =>
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes a ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes b
  | .ifThenElse c t e =>
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes c ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes t ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes e
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes lo ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes hi ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes body
  | .whileFold c body =>
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes c ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes lo ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes hi ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes body
  | .whileFoldReturn c body =>
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes c ||
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes body
  | .tuple es => es.any (detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes)
  | .proj e _ => detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes e
  | .match_ scrut arms =>
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes scrut ||
    arms.any fun (_, b) => detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes b
  | .cfBreak e | .cfContinue e | .cfBreakContinue e =>
    detectReturnIsInt fname paramTypeMap structMeta fnBody defsMap callRetTypes e
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

/-- Detect if a dep's return value is used as a scrutinee of an Option/Result match
    (i.e., matched against somePat/nonePat/okPat/errPat). If so, it cannot be Int. -/
private partial def detectReturnIsOptionMatch (fname : String) : ImpExpr → Bool
  | .match_ scrut arms =>
    let scrutUsesF := match scrut with
      | .app f _ => f == fname
      | .var _ => false
      | _ => false
    let hasOptPats := arms.any fun (p, _) => match p with
      | .somePat _ | .nonePat | .okPat _ | .errPat _ => true | _ => false
    -- Also check: a let-bound result of fname is matched in Option context
    (scrutUsesF && hasOptPats) ||
    detectReturnIsOptionMatch fname scrut ||
    arms.any fun (_, b) => detectReturnIsOptionMatch fname b
  | .letBind vn (.app f _) body =>
    if f == fname then
      -- Check if vn is used as Option match scrutinee in the body
      varUsedAsOptionMatch vn body || detectReturnIsOptionMatch fname body
    else detectReturnIsOptionMatch fname body
  | .letBind _ v body =>
    detectReturnIsOptionMatch fname v || detectReturnIsOptionMatch fname body
  | .seq a b => detectReturnIsOptionMatch fname a || detectReturnIsOptionMatch fname b
  | .ifThenElse c t e =>
    detectReturnIsOptionMatch fname c || detectReturnIsOptionMatch fname t ||
    detectReturnIsOptionMatch fname e
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    detectReturnIsOptionMatch fname lo || detectReturnIsOptionMatch fname hi ||
    detectReturnIsOptionMatch fname body
  | .whileFold c body =>
    detectReturnIsOptionMatch fname c || detectReturnIsOptionMatch fname body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    detectReturnIsOptionMatch fname lo || detectReturnIsOptionMatch fname hi ||
    detectReturnIsOptionMatch fname body
  | .whileFoldReturn c body =>
    detectReturnIsOptionMatch fname c || detectReturnIsOptionMatch fname body
  | .cfBreak e | .cfContinue e | .cfBreakContinue e => detectReturnIsOptionMatch fname e
  | _ => false
where
  varUsedAsOptionMatch (vn : String) : ImpExpr → Bool
    | .match_ (.var v) arms =>
      let hasOptPats := arms.any fun (p, _) => match p with
        | .somePat _ | .nonePat | .okPat _ | .errPat _ => true | _ => false
      (v == vn && hasOptPats) || arms.any fun (_, b) => varUsedAsOptionMatch vn b
    | .letBind _ v body => varUsedAsOptionMatch vn v || varUsedAsOptionMatch vn body
    | .seq a b => varUsedAsOptionMatch vn a || varUsedAsOptionMatch vn b
    | .ifThenElse c t e =>
      varUsedAsOptionMatch vn c || varUsedAsOptionMatch vn t || varUsedAsOptionMatch vn e
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
      -- Use surface types (Int/Array Int) to match the surface code representation
      | ty => ty.toLeanTypeStrSurface lookup
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
def typeTagToLean (_structs : StructMeta) (tag : String)
    (impTy : ImpType := .unknown)
    (structLookup : String → Option String := fun _ => none) : String :=
  match impTy with
  | .unknown => if tag == "int" then "Int" else "Array Int"
  -- Use surface types (Int/Array Int) for struct fields, matching the
  -- surface code that operates on Array Int. This avoids type mismatches
  -- between struct constructors (which would use Array UInt8) and the
  -- surface code (which uses Hax.repeat_ producing Array Int).
  | ty => ty.toLeanTypeStrSurface structLookup

/-- Generate the tuple type for a struct given its fields.
    Composite field types (containing ×) are parenthesized to preserve associativity. -/
def structTupleType (structs : StructMeta)
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
def projPath (i n : Nat) : String :=
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
def computeStructPassthrough (structMeta : StructMeta)
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
def mkStructLookup (structMeta : StructMeta)
    (passthrough : List (String × Bool)) : String → Option String :=
  fun name =>
    if passthrough.any fun (n, pt) => n == name && pt then some "Array Int"
    else resolveStructType structMeta name

/-- Generate auto-preamble: struct definitions, projections, and dependency class.
    `structMeta`: struct definitions from hax JSON (name → [(field_name, type_tag)])
    `defs`: the extracted ImpExpr function definitions
    `fnTypes`: per-function type info from hax JSON (for typed dep signatures)
    `callSigs`: per-call-site full signatures from hax JSON (arg types + return type)
    `varRefTypes`: types of free variable references from hax JSON -/
def generatePreamble (defs : List (String × ImpExpr))
    (moduleName : String) (structMeta : StructMeta := [])
    (fnTypes : List (String × HaxAdapter.FnTypeInfo) := [])
    (callRetTypes : List (String × ImpType) := [])
    (callSigs : List (String × HaxAdapter.FnTypeInfo) := [])
    (varRefTypes : List (String × ImpType) := [])
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
      -- Constructor definition (generate if used in code OR if projections are used
      -- so that rewriteNewToStructCtor can rewrite `new []` calls)
      let projectionsUsed := fields.any fun (fname, _, _) =>
        allAppNames.contains s!".{fname}" || allAppNames.contains s!"{sname}.{fname}"
      -- Emit a type abbreviation `abbrev <sname>_T := <tupleT>` so per-field
      -- projection signatures don't repeat the full nested tuple type. Lean
      -- treats `abbrev` transparently, so this is purely cosmetic; values
      -- typed as `<sname>_T` are still tuples for any downstream consumer.
      -- Only useful for non-passthrough structs that we'll actually emit
      -- projections / ctor for; skip otherwise to keep noise out.
      let abbrevName := s!"{sanitizeName sname}_T"
      let hasAnyEmit := isUsed || projectionsUsed
      let abbrevDefs := if hasAnyEmit && !isPassthrough then
          [s!"/-- Tuple-encoded type for Rust struct `{sname}` (auto-generated). -/\nabbrev {abbrevName} := {tupleT}"]
        else []
      -- Use the abbrev when we have one; otherwise fall back to the raw tuple
      -- type string (passthrough cases use `Array Int` directly).
      let typeRef := if !isPassthrough && hasAnyEmit then abbrevName else tupleT
      let ctorDefs := if isUsed || projectionsUsed then
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
              s!"def {sanitizeName sname} {paramStr} : {typeRef} := {sanitizeName fields.head!.1}"
            else
              s!"def {sanitizeName sname} {paramStr} : {typeRef} := ({tupleStr})"
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
                (pdefs ++ [s!"def «{emitName}» (x : {typeRef}) := x{path}"], ep ++ [projName])
              else
                (pdefs ++ [s!"def «{emitName}» (x : Array Int) := x"], ep ++ [projName])
            else
              -- Conflict: always emit with qualified name
              if !isPassthrough then
                let path := projPath i fields.length
                (pdefs ++ [s!"def «{qualName}» (x : {typeRef}) := x{path}"], ep)
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
      (acc ++ abbrevDefs ++ ctorDefs ++ projDefs, emittedProjs', conflicts ++ newConflicts))
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
                !allExprs.any (detectReturnIsOptionMatch d) &&
                allExprs.any (detectReturnIsInt d allParamTypes structMeta (some (ImpExpr.lit (.int 0))) defs.toArray.toList callRetTypes) &&
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
        -- === TYPED PATH: Use call-site signatures from hax JSON when available ===
        let callSig := callSigs.find? (·.1 == d) |>.map (·.2)
        -- For 0-arity deps, also check varRefTypes
        let varRefType := varRefTypes.find? (·.1 == d) |>.map (·.2)
        -- Check if any call site destructures the result as a tuple
        let retArity := allExprs.foldl (fun acc e =>
          max acc (detectReturnArity d e)) 0
        -- Check if return value is used in Int context
        -- BUT: if the result is also passed to another dep (which expects Array Int),
        -- don't mark as Int to avoid type conflicts.
        -- Deps whose result is used as Option/Result match scrutinee cannot be Int
        let isOptionMatch := allExprs.any (detectReturnIsOptionMatch d)
        let retIsInt := retArity < 2 &&
          !collectionOps.contains d && !isOptionMatch &&
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
        -- Compute return type from typed info (callSig or callRetType), falling back to heuristic
        let retTypeFromSig := match callSig with
          | some sig =>
            if !sig.retType.isUnknown then
              let s := sig.retType.toLeanTypeStr structLookup
              if s != "Unit" && s != "()" then some s else none
            else none
          | none => none
        let retType := match retTypeFromSig with
          | some s => s
          | none =>
            match callRetType with
            | some ty =>
              let s := ty.toLeanTypeStr structLookup
              if s != "Unit" && s != "()" && !ty.isUnknown then s
              else match retStructType with
                | some st => st
                | none => if retIsBool then "Bool" else if retIsInt then "Int" else "Array Int"
            | none => match retStructType with
              | some st => st
              | none =>
                if retArity >= 2 then
                  let compTypes := allExprs.foldl (fun acc e =>
                    acc ++ detectReturnComponentTypes d knownIntNames e) []
                  let componentIsInt := (List.range retArity).map fun i =>
                    compTypes.length > 0 &&
                    compTypes.all fun ct => ct.getD i false
                  " × ".intercalate (componentIsInt.map fun isInt =>
                    if isInt then "Int" else "Array Int")
                else if retIsBool then "Bool"
                else if retIsInt then "Int"
                else "Array Int"
        -- Override: collection operations always return Array Int
        let retType := if collectionOps.contains d && retType == "Int" then "Array Int" else retType
        if arity == 0 then
          -- For 0-arity free-variable deps, use typed info when available
          let finalRetType :=
            -- First: check varRefTypes from hax JSON for this variable
            match varRefType with
            | some ty =>
              let s := ty.toLeanTypeStr structLookup
              if s != "Unit" && s != "()" && !ty.isUnknown then s
              else
                match retStructType with
                | some st => st
                | none =>
                  let usedAsInt := allExprs.any (isVarUsedAsInt d)
                  if usedAsInt then "Int" else "Array Int"
            | none =>
              match retStructType with
              | some st => st
              | none =>
                if retType == "Array Int" then
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
          -- === TYPED PATH for arguments: use callSig when available ===
          let letters := #["a", "b", "c", "d", "e", "f", "g", "h"]
          match callSig with
          | some sig =>
            -- We have typed arg info from hax JSON — use it directly
            let sigArgCount := sig.paramTypes.length
            let paramStr := (List.range arity).map (fun i =>
              let letter := if h : i < letters.size then letters[i] else s!"x{i}"
              let ty := if i < sigArgCount then
                let (_, impTy) := sig.paramTypes[i]!
                if impTy.isUnknown then "Array Int"
                else impTy.toLeanTypeStr structLookup
              else "Array Int"
              s!"({letter} : {ty})") |> " ".intercalate
            s!"  {sanitizeName d} {paramStr} : {retType}"
          | none =>
            -- Fall back to heuristic detection
            let allArgTypes := allExprs.foldl (fun acc e =>
              acc ++ detectArgTypes d arity knownIntNames intProjNames (some e) e) []
            let argIsIntArr := (List.range arity).map fun i =>
              allArgTypes.length > 0 &&
              allArgTypes.all fun callArgs =>
                callArgs.getD i false
            let typedArgResults := defs.foldl (fun acc (fnName, e) =>
              let paramMap := match fnTypes.find? (·.1 == fnName) with
                | some (_, ti) => ti.paramTypes
                | none => []
              acc ++ detectTypedArgs d arity paramMap structMeta (some e) defs callRetTypes e) ([] : List (List (Option ImpType)))
            let typedArgTypes := (List.range arity).map fun i =>
              typedArgResults.findSome? fun callArgs =>
                match callArgs.getD i none with
                | some .unknown | some .bool | some (.tuple _) => none
                | some ty => some ty
                | none => none
            let hasArrayArg := typedArgTypes.any fun opt =>
              match opt with
              | some (ImpType.array _ _) => true
              | some (ImpType.slice _) => true
              | some (ImpType.adt "Vec" _) => true
              | _ => false
            let defaultArgType := if retType == "Int" && !hasArrayArg then "Int" else "Array Int"
            let paramStr := (List.range arity).map (fun i =>
              let letter := if h : i < letters.size then letters[i] else s!"x{i}"
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

/-- Detect field name collisions across structs in the metadata.
    Returns a list of warning strings for fields that appear in multiple structs. -/
def detectFieldCollisions (structMeta : StructMeta) : List String :=
  -- Build a map: field name -> list of struct names that contain it
  let fieldToStructs := structMeta.foldl (fun acc (sname, fields) =>
    fields.foldl (fun acc2 (fname, _, _) =>
      let existing := acc2.find? (fun (f, _) => f == fname) |>.map (·.2) |>.getD []
      let acc2' := acc2.filter (fun (f, _) => f != fname)
      acc2' ++ [(fname, existing ++ [sname])]) acc) ([] : List (String × List String))
  -- Filter to fields with 2+ structs
  fieldToStructs.filterMap fun (fname, structs) =>
    if structs.length >= 2 then
      some s!"field name collision: '.{fname}' appears in structs {", ".intercalate structs} — rename to avoid projection ambiguity"
    else none

/-- Post-process generated code: replace `Hax.{dep}` with bare `{dep}` for dependency names.
    This is needed because `runtimeName` maps names like `mul` to `Hax.mul`, but when
    `mul` is a cross-crate dependency (exported by the Deps class), we need the bare name. -/
def fixDepReferences (code : String) (depNames : List String) : String :=
  depNames.foldl (fun acc dep =>
    -- Replace "Hax.{dep}" with "{dep}" only when followed by a word boundary
    -- (space, newline, paren, comma, etc. — NOT by a letter/digit/underscore/dot)
    -- This avoids replacing "Hax.S" inside "Hax.Semantics"
    let haxName := s!"Hax.{dep}"
    let sanitized := sanitizeName dep
    -- Replace with common boundary suffixes
    [" ", "\n", ")", ",", "]", "}", ":", ";"].foldl (fun a suffix =>
      a.replace (haxName ++ suffix) (sanitized ++ suffix)) acc
    ) code

/-- Find field names that appear in multiple structs. -/
def findAmbiguousFields (structMeta : StructMeta) : List String :=
  let allFields := structMeta.foldl (fun acc (_, fields) =>
    acc ++ fields.map (·.1)) []
  -- A field is ambiguous if it appears more than once
  let dupes := allFields.filter fun f =>
    Nat.blt 1 (allFields.filter (· == f)).length
  dupes.eraseDups

/-- Collect all projection names applied to a given variable in an expression. -/
private partial def collectProjectionsOnVar (varName : String) : ImpExpr → List String
  | .app f [.var v] =>
    if f.startsWith "." && v == varName then [(f.drop 1).toString] else []
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

/-- Infer the struct type of an arbitrary expression (not just a variable).
    Handles:
    - `.var v` → delegate to inferStructType
    - `.app "Hax.index" [arr, idx]` / `.app "index" [arr, idx]` → look at arr's element type
    - `.app ".field" [parent]` → look up field type in struct metadata
    This enables correct projection qualification for patterns like
    `.block_id (Hax.index (.stash state) i)` where `.stash` returns Array StashEntry. -/
private partial def inferExprStructType (structMeta : StructMeta) (ctx : ImpExpr)
    : ImpExpr → Option String
  | .var v => inferStructType structMeta v ctx
  -- Hax.index arr idx → element type of arr
  | .app f [arr, _] =>
    if f == "index" || f == "Hax.index" then
      inferArrayElementStructType structMeta ctx arr
    else none
  | .app f [inner] =>
    if f.startsWith "." || (f.splitOn ".").length > 1 then
      -- This is a struct projection. Infer the result struct type.
      let projField := if f.startsWith "." then f.drop 1
        else (f.splitOn ".").getLast!
      -- Find the struct that 'inner' belongs to, then look up the field type
      let innerStructType := inferExprStructType structMeta ctx inner
      match innerStructType with
      | some sname =>
        -- Find the field in this struct and check its type
        match structMeta.find? (·.1 == sname) with
        | some (_, fields) =>
          -- Find the matching field by name
          match fields.find? fun (fn, _, _) => fn == projField with
          | some (_, tag, _) =>
            -- The tag might be a struct name — check if it's in structMeta
            if structMeta.any (·.1 == tag) then some tag else none
          | none => none
        | none => none
      | none => none
    else none
  | _ => none
where
  /-- Infer the struct type of array elements. If the array comes from a struct
      field projection, look up the field's element type in struct metadata. -/
  inferArrayElementStructType (structMeta : StructMeta) (ctx : ImpExpr)
      : ImpExpr → Option String
    | .app f [inner] =>
      if f.startsWith "." || (f.splitOn ".").length > 1 then
        let projField := if f.startsWith "." then f.drop 1
          else (f.splitOn ".").getLast!
        -- Find the struct of the inner expression
        let innerStruct := inferExprStructType structMeta ctx inner
        match innerStruct with
        | some sname =>
          match structMeta.find? (·.1 == sname) with
          | some (_, fields) =>
            match fields.find? fun (fn, _, _) => fn == projField with
            | some (_, tag, fty) =>
              -- Check if the field type is Vec<Struct> or Array<Struct>
              -- Vec has 2 generic args: [elemType, allocator]
              let elemStruct := match fty with
                | .adt name args =>
                  if name == "Vec" || name.endsWith "::Vec" then
                    match args.head? with
                    | some (.adt inner _) =>
                      if structMeta.any (·.1 == inner) then some inner else none
                    | _ => none
                  else none
                | .array (.adt inner _) _ =>
                  if structMeta.any (·.1 == inner) then some inner else none
                | .slice (.adt inner _) =>
                  if structMeta.any (·.1 == inner) then some inner else none
                | _ => none
              match elemStruct with
              | some s => some s
              | none =>
                -- Fallback: check if tag is a known struct name (heuristic)
                if structMeta.any (·.1 == tag) then some tag else none
            | none => none
          | none => none
        | none => none
      else none
    | .var v =>
      -- Check if variable is bound to a struct constructor that returns arrays
      inferStructType structMeta v ctx |>.bind fun sname =>
        -- This variable is a struct — but we need its ELEMENT type
        none  -- variable-level struct type doesn't help with element type
    | _ => none

/-- Qualify ambiguous projections in an ImpExpr: `.field` → `StructName.field`
    when the argument is known to be of a specific struct type. -/
partial def qualifyProjections (structMeta : StructMeta)
    (ambiguous : List String) (ctx : ImpExpr) : ImpExpr → ImpExpr
  | .app f [arg] =>
    if f.startsWith "." then
      let fname := (f.drop 1).toString
      if ambiguous.contains fname then
        -- Try to infer the struct type: first from expression structure, then from variable
        let structType := inferExprStructType structMeta ctx arg
        let structType := match structType with
          | some s => some s
          | none =>
            let argVar := match arg with | .var v => some v | _ => none
            argVar.bind fun v => inferStructType structMeta v ctx
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
partial def rewriteAppName (oldName newName : String) : ImpExpr → ImpExpr
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
partial def rewriteNewToStructCtor (structMeta : StructMeta) : ImpExpr → ImpExpr
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
partial def rewriteStructFromElem (structMeta : StructMeta)
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
partial def fixProjectionPaths (arityMap : List (String × Nat)) : ImpExpr → ImpExpr
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

/-! ### Pass T-A: Initialize missing fold accumulators

When a fold accumulator tuple `(a, b)` references a variable `b` not bound in
the enclosing scope, inserts `let b := (0 : Int)` before the fold.
Merged from PrettyPrintT.lean. -/

/-- Collect all variable names bound by let-bindings at the top level. -/
private partial def collectBoundNamesT : ImpExpr → List String
  | .letBind n _ body => n :: collectBoundNamesT body
  | .seq a b => collectBoundNamesT a ++ collectBoundNamesT b
  | _ => []

/-- Extract accumulator variable names from a fold body by detecting mutation patterns. -/
private partial def extractAccumNamesFromBody : ImpExpr → List String
  | .seq (.seq a b) c => extractAccumNamesFromBody (.seq a (.seq b c))
  | .seq (.letBind n _ (.var v)) rest =>
    if n == v && !n.startsWith "_assign" then
      let restAccs := extractAccumNamesFromBody rest
      if restAccs.contains n then restAccs else n :: restAccs
    else extractAccumNamesFromBody rest
  | .seq (.ifThenElse _ thn _) rest =>
    let thnAccs := extractCondMutsT thn |>.filter (!·.startsWith "_assign")
    let restAccs := extractAccumNamesFromBody rest
    (thnAccs ++ restAccs).eraseDups
  | .seq _ rest => extractAccumNamesFromBody rest
  | .letBind n _ (.var v) =>
    if n == v && !n.startsWith "_assign" then [n] else []
  | .letBind _ _ body => extractAccumNamesFromBody body
  | .ifThenElse _ thn _ =>
    (extractCondMutsT thn).filter (!·.startsWith "_assign") |>.eraseDups
  | _ => []
where
  extractCondMutsT : ImpExpr → List String
    | .seq (.seq a b) c => extractCondMutsT (.seq a (.seq b c))
    | .seq (.letBind n _ (.var v)) rest =>
      if n == v then n :: extractCondMutsT rest else extractCondMutsT rest
    | .seq .unitVal rest => extractCondMutsT rest
    | .seq _ rest => extractCondMutsT rest
    | .letBind n _ (.var v) => if n == v then [n] else []
    | .letBind _ _ body => extractCondMutsT body
    | .unitVal => []
    | _ => []

/-- Walk an ImpExpr and insert `let v := (0 : Int)` before any fold whose
    accumulator references a variable not bound in the enclosing scope. -/
partial def initMissingFoldAccums (bound : List String := []) : ImpExpr → ImpExpr
  | .letBind n v body =>
    let v' := initMissingFoldAccums bound v
    let body' := initMissingFoldAccums (n :: bound) body
    .letBind n v' body'
  | .seq a b =>
    let a' := initMissingFoldAccums bound a
    let boundsFromA := collectBoundNamesT a
    .seq a' (initMissingFoldAccums (bound ++ boundsFromA) b)
  | .forFold v lo hi body =>
    let lo' := initMissingFoldAccums bound lo
    let hi' := initMissingFoldAccums bound hi
    let body' := initMissingFoldAccums (v :: bound) body
    let fold := ImpExpr.forFold v lo' hi' body'
    let accumNames := extractAccumNamesFromBody body'
    let freeAccums := accumNames.filter fun n => !bound.contains n
    freeAccums.foldr (fun fv expr => .letBind fv (.lit (.int 0)) expr) fold
  | .forFoldRev v lo hi body =>
    let lo' := initMissingFoldAccums bound lo
    let hi' := initMissingFoldAccums bound hi
    let body' := initMissingFoldAccums (v :: bound) body
    let fold := ImpExpr.forFoldRev v lo' hi' body'
    let accumNames := extractAccumNamesFromBody body'
    let freeAccums := accumNames.filter fun n => !bound.contains n
    freeAccums.foldr (fun fv expr => .letBind fv (.lit (.int 0)) expr) fold
  | .forFoldReturn v lo hi body =>
    let lo' := initMissingFoldAccums bound lo
    let hi' := initMissingFoldAccums bound hi
    let body' := initMissingFoldAccums (v :: bound) body
    let fold := ImpExpr.forFoldReturn v lo' hi' body'
    let accumNames := extractAccumNamesFromBody body'
    let freeAccums := accumNames.filter fun n => !bound.contains n
    freeAccums.foldr (fun fv expr => .letBind fv (.lit (.int 0)) expr) fold
  | .forFoldRevReturn v lo hi body =>
    let lo' := initMissingFoldAccums bound lo
    let hi' := initMissingFoldAccums bound hi
    let body' := initMissingFoldAccums (v :: bound) body
    let fold := ImpExpr.forFoldRevReturn v lo' hi' body'
    let accumNames := extractAccumNamesFromBody body'
    let freeAccums := accumNames.filter fun n => !bound.contains n
    freeAccums.foldr (fun fv expr => .letBind fv (.lit (.int 0)) expr) fold
  | .ifThenElse c t e =>
    .ifThenElse (initMissingFoldAccums bound c)
      (initMissingFoldAccums bound t) (initMissingFoldAccums bound e)
  | .match_ scrut arms =>
    .match_ (initMissingFoldAccums bound scrut)
      (arms.map fun (p, b) => (p, initMissingFoldAccums bound b))
  | .whileFold c body =>
    .whileFold (initMissingFoldAccums bound c) (initMissingFoldAccums bound body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (initMissingFoldAccums bound c) (initMissingFoldAccums bound body)
  | .tuple es => .tuple (es.map (initMissingFoldAccums bound))
  | .proj e i => .proj (initMissingFoldAccums bound e) i
  | .app f args => .app f (args.map (initMissingFoldAccums bound))
  | .cfBreak e => .cfBreak (initMissingFoldAccums bound e)
  | .cfContinue e => .cfContinue (initMissingFoldAccums bound e)
  | .cfBreakContinue e => .cfBreakContinue (initMissingFoldAccums bound e)
  | e => e

/-! ### Pass T-B: Reconcile function types with call-site types -/

/-- Unwrap ImpType.ref wrappers to get the inner type. -/
private def unwrapRefT : ImpType → ImpType
  | .ref inner _ => unwrapRefT inner
  | ty => ty

/-- Check if a type resolves to a struct tuple (not just Array Int or Int). -/
private def isStructTupleType (ty : ImpType) (structLookup : String → Option String) : Bool :=
  let ty := unwrapRefT ty
  match ty with
  | .adt name _ =>
    match structLookup name with
    | some s => (s.splitOn " × ").length > 1
    | none =>
      let shortName := match name.splitOn "::" with
        | [] => name
        | segs => segs.getLast!
      match structLookup shortName with
      | some s => (s.splitOn " × ").length > 1
      | none => false
  | .tuple elems => elems.length > 1
  | _ => false

/-- Reconcile fnTypes with call-site types. When a locally-defined function has struct-typed
    params but is called with Array Int args, replace the param types from call-site info. -/
def reconcileFnTypes
    (defs : List (String × ImpExpr))
    (fnTypes : List (String × HaxAdapter.FnTypeInfo))
    (structLookup : String → Option String)
    (callSigs : List (String × HaxAdapter.FnTypeInfo) := []) :
    List (String × HaxAdapter.FnTypeInfo) :=
  let definedNames := defs.map (·.1)
  let reconciled := fnTypes.map fun (fname, ti) =>
    if !definedNames.contains fname then (fname, ti)
    else
      let hasStructParams := ti.paramTypes.any fun (_, pty) =>
        isStructTupleType pty structLookup
      if !hasStructParams then (fname, ti)
      else
        match callSigs.find? (·.1 == fname) with
        | some (_, callTi) =>
          let callHasStruct := callTi.paramTypes.any fun (_, pty) =>
            isStructTupleType pty structLookup
          if callHasStruct then (fname, ti)
          else
            let indexed := (List.range ti.paramTypes.length).zip ti.paramTypes
            let newParamTypes := indexed.map fun (i, (pname, _)) =>
              match callTi.paramTypes[i]? with
              | some (_, callPty) => (pname, callPty)
              | none => (pname, ImpType.int)
            let newRetType := if callTi.retType.isUnknown then ti.retType else callTi.retType
            (fname, { paramTypes := newParamTypes, retType := newRetType })
        | none => (fname, ti)
  reconciled.foldl (fun (acc : List (String × HaxAdapter.FnTypeInfo)) (n, ti) =>
    if acc.any (·.1 == n) then acc else acc ++ [(n, ti)]) []

/-! ### Pass T-C: Type-aware projection qualification from usage -/

/-- Detect the struct constructor used with `Hax.push arr (StructName ...)` patterns. -/
private partial def detectArrayElementTypes : ImpExpr → List (String × String)
  | .app "push" [.var arr, .app ctor _] => [(arr, ctor)]
  | .letBind _ v body =>
    detectArrayElementTypes v ++ detectArrayElementTypes body
  | .seq a b => detectArrayElementTypes a ++ detectArrayElementTypes b
  | .ifThenElse c t e =>
    detectArrayElementTypes c ++ detectArrayElementTypes t ++ detectArrayElementTypes e
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    detectArrayElementTypes lo ++ detectArrayElementTypes hi ++ detectArrayElementTypes body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    detectArrayElementTypes lo ++ detectArrayElementTypes hi ++ detectArrayElementTypes body
  | .whileFold c body | .whileFoldReturn c body =>
    detectArrayElementTypes c ++ detectArrayElementTypes body
  | .match_ scrut arms =>
    detectArrayElementTypes scrut ++
    arms.foldl (fun acc (_, b) => acc ++ detectArrayElementTypes b) []
  | .app _ args => args.foldl (fun acc a => acc ++ detectArrayElementTypes a) []
  | .tuple es => es.foldl (fun acc e => acc ++ detectArrayElementTypes e) []
  | _ => []

/-- Detect the struct type from `let x := StructName args` patterns. -/
private partial def detectLetBindStructTypes : ImpExpr → List (String × String)
  | .letBind n (.app ctor _) body =>
    [(n, ctor)] ++ detectLetBindStructTypes body
  | .letBind _ v body =>
    detectLetBindStructTypes v ++ detectLetBindStructTypes body
  | .seq a b => detectLetBindStructTypes a ++ detectLetBindStructTypes b
  | .ifThenElse c t e =>
    detectLetBindStructTypes c ++ detectLetBindStructTypes t ++ detectLetBindStructTypes e
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    detectLetBindStructTypes lo ++ detectLetBindStructTypes hi ++ detectLetBindStructTypes body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    detectLetBindStructTypes lo ++ detectLetBindStructTypes hi ++ detectLetBindStructTypes body
  | .whileFold c body | .whileFoldReturn c body =>
    detectLetBindStructTypes c ++ detectLetBindStructTypes body
  | .match_ scrut arms =>
    detectLetBindStructTypes scrut ++
    arms.foldl (fun acc (_, b) => acc ++ detectLetBindStructTypes b) []
  | _ => []

/-- Rewrite ambiguous projections on array elements or variables whose struct type
    can be inferred from constructor usage patterns. -/
private partial def qualifyProjectionsFromUsageT
    (arrayElemTypes : List (String × String))
    (varStructTypes : List (String × String))
    (structMeta : StructMeta)
    (ambiguousFields : List String) : ImpExpr → ImpExpr
  | .app projName [.app idxFn [.var arr, idx]] =>
    if idxFn == "index" || idxFn == "Hax.index" then
      let fieldName := if projName.startsWith "." then (projName.drop 1).toString
        else if projName.contains '.' then
          match projName.splitOn "." with | _ :: f :: _ => f | _ => projName
        else projName
      if ambiguousFields.contains fieldName then
        match arrayElemTypes.find? (·.1 == arr) with
        | some (_, structName) =>
          let hasField := structMeta.any fun (sn, fields) =>
            sn == structName && fields.any (·.1 == fieldName)
          let newName := if hasField then s!"{structName}.{fieldName}" else projName
          .app newName [.app idxFn [.var arr,
            qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields idx]]
        | none =>
          .app projName [.app idxFn [.var arr,
            qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields idx]]
      else
        .app projName [.app idxFn [.var arr,
          qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields idx]]
    else
      .app projName [.app idxFn
        ((.var arr :: [idx]).map (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields))]
  | .app projName [.var v] =>
    let fieldName := if projName.startsWith "." then (projName.drop 1).toString
      else if projName.contains '.' then
        match projName.splitOn "." with | _ :: f :: _ => f | _ => projName
      else projName
    if ambiguousFields.contains fieldName then
      match varStructTypes.find? (·.1 == v) with
      | some (_, structName) =>
        let hasField := structMeta.any fun (sn, fields) =>
          sn == structName && fields.any (·.1 == fieldName)
        if hasField then .app s!"{structName}.{fieldName}" [.var v]
        else .app projName [.var v]
      | none => .app projName [.var v]
    else .app projName [.var v]
  | .app f args =>
    .app f (args.map (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields))
  | .letBind n v body =>
    .letBind n
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields v)
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields body)
  | .seq a b =>
    .seq (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields a)
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields b)
  | .ifThenElse c t e =>
    .ifThenElse
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields c)
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields t)
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields e)
  | .tuple es =>
    .tuple (es.map (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields))
  | .proj e i =>
    .proj (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields e) i
  | .match_ scrut arms =>
    .match_ (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields scrut)
      (arms.map fun (p, b) =>
        (p, qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields b))
  | .forFold v lo hi body =>
    .forFold v
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields lo)
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields hi)
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields lo)
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields hi)
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields lo)
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields hi)
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields lo)
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields hi)
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields body)
  | .whileFold c body =>
    .whileFold
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields c)
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields body)
  | .whileFoldReturn c body =>
    .whileFoldReturn
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields c)
      (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields body)
  | .cfBreak e =>
    .cfBreak (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields e)
  | .cfContinue e =>
    .cfContinue (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields e)
  | .cfBreakContinue e =>
    .cfBreakContinue (qualifyProjectionsFromUsageT arrayElemTypes varStructTypes structMeta ambiguousFields e)
  | e => e

/-- Propagate return element types through call chains. -/
private partial def propagateReturnElemTypes
    (funcRetElemTypes : List (String × String)) : ImpExpr → List (String × String)
  | .letBind varName (.app fname _) body =>
    let fromCall := match funcRetElemTypes.find? (·.1 == fname) with
      | some (_, sn) => [(varName, sn)]
      | none => []
    fromCall ++ propagateReturnElemTypes funcRetElemTypes body
  | .letBind _ v body =>
    propagateReturnElemTypes funcRetElemTypes v ++
    propagateReturnElemTypes funcRetElemTypes body
  | .seq a b =>
    propagateReturnElemTypes funcRetElemTypes a ++
    propagateReturnElemTypes funcRetElemTypes b
  | .ifThenElse c t e =>
    propagateReturnElemTypes funcRetElemTypes c ++
    propagateReturnElemTypes funcRetElemTypes t ++
    propagateReturnElemTypes funcRetElemTypes e
  | .forFold _ lo hi body | .forFoldRev _ lo hi body =>
    propagateReturnElemTypes funcRetElemTypes lo ++
    propagateReturnElemTypes funcRetElemTypes hi ++
    propagateReturnElemTypes funcRetElemTypes body
  | .forFoldReturn _ lo hi body | .forFoldRevReturn _ lo hi body =>
    propagateReturnElemTypes funcRetElemTypes lo ++
    propagateReturnElemTypes funcRetElemTypes hi ++
    propagateReturnElemTypes funcRetElemTypes body
  | .whileFold c body | .whileFoldReturn c body =>
    propagateReturnElemTypes funcRetElemTypes c ++
    propagateReturnElemTypes funcRetElemTypes body
  | .match_ scrut arms =>
    propagateReturnElemTypes funcRetElemTypes scrut ++
    arms.foldl (fun acc (_, b) => acc ++ propagateReturnElemTypes funcRetElemTypes b) []
  | _ => []

/-- Find field names that appear in multiple structs (ambiguous projections). -/
private def findAmbiguousFieldsT (structMeta : StructMeta) : List String :=
  let allFields := structMeta.foldl (fun acc (_, fields) =>
    acc ++ fields.map (·.1)) []
  let dupes := allFields.filter fun f =>
    Nat.blt 1 (allFields.filter (· == f)).length
  dupes.eraseDups

/-- Apply the three type-aware passes from PrettyPrintT as pre-processing steps. -/
def applyTypedPasses (defs : List (String × ImpExpr))
    (structMeta : StructMeta)
    (fnTypes : List (String × HaxAdapter.FnTypeInfo))
    (callSigs : List (String × HaxAdapter.FnTypeInfo)) :
    (List (String × ImpExpr)) × (List (String × HaxAdapter.FnTypeInfo)) :=
  -- Pass T-A: Fix missing fold accumulators
  let defs := defs.map fun (n, e) =>
    let rec getParams : ImpExpr → List String
      | .letBind pn (.var pv) body => if pn == pv then pn :: getParams body else []
      | _ => []
    let params := getParams e
    (n, initMissingFoldAccums params e)
  -- Pass T-B: Reconcile function types with call-site types
  let structIsPassthrough := computeStructPassthrough structMeta defs
  let structLookup := mkStructLookup structMeta structIsPassthrough
  let fnTypes := reconcileFnTypes defs fnTypes structLookup callSigs
  -- Pass T-C: Qualify projections from usage (array element types)
  let ambiguousFields := findAmbiguousFieldsT structMeta
  let defs := if ambiguousFields.isEmpty then defs
    else
      let structNames := structMeta.map (·.1)
      let arrayElemTypes := defs.foldl (fun acc (_, e) =>
        acc ++ detectArrayElementTypes e) []
      let varStructTypes := defs.foldl (fun acc (_, e) =>
        acc ++ detectLetBindStructTypes e) []
      let arrayElemTypes := arrayElemTypes.filter fun (_, sn) => structNames.contains sn
      let varStructTypes := varStructTypes.filter fun (_, sn) => structNames.contains sn
      let funcRetElemTypes := defs.filterMap fun (fname, e) =>
        let pushTypes := detectArrayElementTypes e
        let structPushes := pushTypes.filter fun (_, sn) => structNames.contains sn
        match structPushes.head? with
        | some (_, sn) => some (fname, sn)
        | none => none
      let crossFuncElemTypes := defs.foldl (fun acc (_, e) =>
        acc ++ propagateReturnElemTypes funcRetElemTypes e) []
      let paramStructTypes := defs.foldl (fun acc (fname, e) =>
        match fnTypes.find? (·.1 == fname) with
        | some (_, ti) =>
          let rec getParamsT : ImpExpr → List String
            | .letBind pn (.var pv) body => if pn == pv then pn :: getParamsT body else []
            | _ => []
          let paramNames := getParamsT e
          acc ++ paramNames.filterMap fun pname =>
            match ti.paramTypes.find? (·.1 == pname) with
            | some (_, pty) =>
              let upty := unwrapRefT pty
              match upty with
              | .adt adtName _ =>
                if structNames.contains adtName then some (pname, adtName) else none
              | _ => none
            | none => none
        | none => acc) ([] : List (String × String))
      let allArrayElemTypes := (arrayElemTypes ++ crossFuncElemTypes).eraseDups
      let allVarStructTypes := (varStructTypes ++ crossFuncElemTypes ++ paramStructTypes).eraseDups
      if allArrayElemTypes.isEmpty && allVarStructTypes.isEmpty && paramStructTypes.isEmpty then defs
      else defs.map fun (n, e) =>
        let fnParamTypes := match fnTypes.find? (·.1 == n) with
          | some (_, ti) =>
            let rec getParamsQ : ImpExpr → List String
              | .letBind pn (.var pv) body => if pn == pv then pn :: getParamsQ body else []
              | _ => []
            let paramNames := getParamsQ e
            paramNames.filterMap fun pname =>
              match ti.paramTypes.find? (·.1 == pname) with
              | some (_, pty) =>
                let upty := unwrapRefT pty
                match upty with
                | .adt adtName _ =>
                  if structNames.contains adtName then some (pname, adtName) else none
                | _ => none
              | none => none
          | none => []
        let localVarTypes := fnParamTypes ++ allVarStructTypes
        (n, qualifyProjectionsFromUsageT allArrayElemTypes localVarTypes structMeta ambiguousFields e)
  (defs, fnTypes)

/-- **DEPRECATED (2026-05-14).** The untyped emit path.

    All 100+ production extractions under `SSProve-lean/CatCrypt/.../*_haxpipe.lean`
    are generated by `haxpipeT --emit-certified --hax`, which routes through
    `toLeanCertifiedFileTyped` (PrettyPrintT.lean). This function only fires on
    `--emit-lean` or `--emit-certified` *without* `--hax-format`, neither of
    which has a production consumer.

    New code should use `toLeanCertifiedFileTyped`. This function is kept for
    backwards compatibility with the legacy expression-parser path and may be
    removed in a future release. -/
@[deprecated "Use toLeanCertifiedFileTyped (typed path, --emit-certified --hax). The untyped pipeline is retained only for the legacy expression-parser entry point." (since := "2026-05-14")]
def toLeanCertifiedFile (defs : List (String × ImpExpr))
    (moduleName : String := "Generated")
    (structMeta : StructMeta := [])
    (fnTypes : List (String × HaxAdapter.FnTypeInfo) := [])
    (callRetTypes : List (String × ImpType) := [])
    (callSigs : List (String × HaxAdapter.FnTypeInfo) := [])
    (varRefTypes : List (String × ImpType) := [])
    (withImpExprs : Bool := true) : String :=
  -- Apply canonicalization passes from `Hax.Canonicalize` to bring each
  -- post-pipeline ImpExpr into a form that `toLean` can render via a
  -- simpler syntax mapping. Idempotent — passing through this is a
  -- no-op if patterns are already canonical.
  let defs := defs.map fun (n, e) => (n, Hax.Canonicalize.canonicalize e)
  -- Deduplicate: hax JSON may contain the same constant/function defined in
  -- multiple Rust modules. Keep the first occurrence, drop later duplicates.
  let defs := defs.foldl (fun (acc : List (String × ImpExpr)) (n, e) =>
    if acc.any (·.1 == n) then acc else acc ++ [(n, e)]) []
  -- Apply typed passes (merged from PrettyPrintT)
  let (defs, fnTypes) := applyTypedPasses defs structMeta fnTypes callSigs
  -- Pre-process: qualify ambiguous projection names
  let ambiguousFields := findAmbiguousFields structMeta
  let defs := if ambiguousFields.isEmpty then defs
    else defs.map fun (n, e) => (n, qualifyProjections structMeta ambiguousFields e e)
  -- Pre-process: rewrite `new args` to struct constructor calls
  let defs := if structMeta.isEmpty then defs
    else defs.map fun (n, e) => (n, rewriteNewToStructCtor structMeta e)
  -- Pre-process: resolve remaining `new []` to struct constructors using type info.
  -- When `let v := new []; ... f(v) ...` and `f` has parameter type matching a struct,
  -- replace `new []` with the struct constructor using default values.
  let defs := if structMeta.isEmpty then defs
    else defs.map fun (defName, e) =>
      let rec findCallsWithVar (v : String) : ImpExpr → List (String × Nat)
        | .app f args =>
          let thisCall := if args.any (· == .var v) then
            (args.zip (List.range args.length)).findSome? fun (a, i) => if a == .var v then some (f, i) else none
          else none
          let sub := args.foldl (fun acc a => acc ++ findCallsWithVar v a) []
          match thisCall with
          | some c => c :: sub
          | none => sub
        | .letBind _ val body => findCallsWithVar v val ++ findCallsWithVar v body
        | .seq a b => findCallsWithVar v a ++ findCallsWithVar v b
        | .ifThenElse c t e => findCallsWithVar v c ++ findCallsWithVar v t ++ findCallsWithVar v e
        | _ => []
      let rec rewriteNewZeroArg : ImpExpr → ImpExpr
        | .letBind n (.app "new" []) body =>
          -- Find functions called with `n` as argument and the arg position
          let calls := findCallsWithVar n body
          -- Check if any call's parameter type is a struct
          let structMatch := calls.findSome? fun (fname, pos) =>
            let fnTi := fnTypes.find? (·.1 == fname) |>.map (·.2)
            match fnTi with
            | some ti =>
              if pos < ti.paramTypes.length then
                let paramTy := ti.paramTypes[pos]!.2
                match paramTy with
                | .adt sname _ => structMeta.find? fun (s, _) => s == sname
                | _ => none
              else none
            | none => none
          match structMatch with
          | some (sname, fields) =>
            let defaultArgs := fields.map fun (_, _, ty) =>
              match ty with
              | .array _ len => ImpExpr.app "repeat" [.lit (.int 0), .lit (.int len)]
              | _ => ImpExpr.lit (.int 0)
            .letBind n (.app sname defaultArgs) (rewriteNewZeroArg body)
          | none => .letBind n (.app "new" []) (rewriteNewZeroArg body)
        | .letBind n v body => .letBind n (rewriteNewZeroArg v) (rewriteNewZeroArg body)
        | .seq a b => .seq (rewriteNewZeroArg a) (rewriteNewZeroArg b)
        | .ifThenElse c t e => .ifThenElse (rewriteNewZeroArg c) (rewriteNewZeroArg t) (rewriteNewZeroArg e)
        | e => e
      (defName, rewriteNewZeroArg e)
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
  let (preamble, projConflicts) := generatePreamble defs moduleName structMeta fnTypes callRetTypes callSigs varRefTypes
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
  let headerComment := if withImpExprs then
    "/-\n  Auto-generated by haxpipe --emit-certified (verified hax pipeline)\n  Surface code + ImpExpr literals for agreement proofs.\n-/"
  else
    "/-\n  Auto-generated by haxpipe --emit-lean (verified hax pipeline)\n  Surface code only (no ImpExpr literals).\n-/"
  let imports := if withImpExprs then
    "import Hax.Runtime\nimport Hax.AST\nimport Hax.Semantics"
  else
    "import Hax.Runtime"
  -- Step 2: collect opaque ADT names from every type the emit will reference
  -- and emit `axiom <Name> : Type` declarations. This lets the emitter
  -- preserve cipher / block / newtype names in Deps signatures and let-binding
  -- annotations rather than collapsing them to `Int`.
  let collectFromFnTypeInfo (ti : HaxAdapter.FnTypeInfo) : List String :=
    ti.paramTypes.foldl (fun acc (_, t) => acc ++ t.collectOpaqueAdtNames structLookup) []
      ++ ti.retType.collectOpaqueAdtNames structLookup
  let opaqueFromFnTypes := fnTypes.foldl (fun acc (_, ti) =>
    acc ++ collectFromFnTypeInfo ti) ([] : List String)
  let opaqueFromCallSigs := callSigs.foldl (fun acc (_, ti) =>
    acc ++ collectFromFnTypeInfo ti) ([] : List String)
  let opaqueFromCallRet := callRetTypes.foldl (fun acc (_, t) =>
    acc ++ t.collectOpaqueAdtNames structLookup) ([] : List String)
  let opaqueFromVarRefs := varRefTypes.foldl (fun acc (_, t) =>
    acc ++ t.collectOpaqueAdtNames structLookup) ([] : List String)
  let allOpaque := (opaqueFromFnTypes ++ opaqueFromCallSigs ++
                    opaqueFromCallRet ++ opaqueFromVarRefs).eraseDups
  let axiomsBlock := if allOpaque.isEmpty then ""
    else "/-- Opaque types extracted from the hax JSON. Concrete instances\n    are provided by the protocol's bridge-adapter at the CatCrypt surface. -/\n"
      ++ "\n".intercalate (allOpaque.map fun n => s!"axiom {n} : Type") ++ "\n\n"
  let header := s!"{headerComment}\n{imports}\n\nset_option linter.unusedVariables false\n\nnamespace {moduleName}\n\nopen Hax\n\n{axiomsBlock}{preamble}\nmutual\n\n"
  let body := "\n".intercalate (defs.map fun (n, e) =>
    let fnTi := fnTypes.find? (·.1 == n) |>.map (·.2)
    let surfaceDef := toLeanDef n e (fnTypeInfo := fnTi) (structLookup := structLookup) (structMeta := structMeta) (allFnTypes := fnTypes)
    -- If any function needs partial, mark all as partial (mutual block requirement)
    let surfaceDef := if needsPartial then surfaceDef.replace "def " "partial def " else surfaceDef
    s!"{surfaceDef}")
  let impExprs := if withImpExprs then
    "\n".intercalate (defs.map fun (n, e) =>
      let impExprDef := toLeanImpExprDef n e
      -- If any function needs partial, mark impExpr defs too (mutual block requirement)
      let impExprDef := if needsPartial then impExprDef.replace "def " "partial def " else impExprDef
      s!"{impExprDef}")
  else ""
  let footer := if withImpExprs then
    s!"\n{impExprs}\nend\n\nend {moduleName}\n"
  else
    s!"\nend\n\nend {moduleName}\n"
  -- Post-process: fix dependency references that got Hax. prefix
  fixDepReferences (header ++ body ++ footer) depNames

end Hax

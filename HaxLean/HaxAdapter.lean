/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.AST
public import HaxLean.ImpType
public import HaxLean.TExpr
public import HaxLean.InlineClosures
public import HaxLean.JsonSize
public import Lean.Data.Json
public import HaxLean.FreeVars
import HaxLean.InclusiveRange

/-!
# Hax AST Adapter

Maps hax's JSON AST format (`Decorated<ExprKind>`) to our `ImpExpr`/`TExpr`.

## Hax JSON format

Hax uses Rust serde with externally tagged enums. An expression is:
```json
{
  "ty": <TyKind>,
  "span": <Span>,
  "contents": {"VariantName": {field1: ..., field2: ...}},
  "hir_id": null | [usize, usize],
  "attributes": [...]
}
```

We extract `contents` (the ExprKind) and `ty`, ignoring `span`, `hir_id`, `attributes`.

## Mapping overview

| Hax ExprKind          | Our ImpExpr              |
|-----------------------|--------------------------|
| `VarRef {id}`         | `.var id.name`           |
| `Literal {lit, neg}`  | `.lit ...`               |
| `If {cond,then,...}`  | `.ifThenElse`            |
| `Call {fun,args,...}`  | `.app f args`            |
| `Let {expr,pat}`      | `.letBind`               |
| `Block {stmts,expr}`  | nested `.seq`            |
| `Match {scrutinee,..}`| `.match_`                |
| `Tuple {fields}`      | `.tuple`                 |
| `Assign {lhs,rhs}`    | `.assign`                |
| `Borrow {arg,...}`     | `.borrow`                |
| `Deref {arg}`          | `.deref`                 |
| `Loop {body}`          | `.whileLoop`             |
| `Break {value,...}`    | `.break_`                |
| `Continue {..}`        | `.continue_`             |
| `Return {value}`       | `.earlyReturn`           |
| `Field {lhs,field}`   | `.proj lhs field_index`  |
| `TupleField {lhs,..}` | `.proj lhs field`        |
| `Binary {op,lhs,rhs}` | `.app op [lhs,rhs]`     |
| `Unary {op,arg}`       | `.app op [arg]`         |
| `Adt(..)`              | `.app ctor [fields]`    |
| `Closure {body,...}`   | body (simplified)        |
| others                 | `.app "unknown" []`     |
-/

public section

namespace Hax.HaxAdapter

open Lean (Json ToJson FromJson toJson fromJson?)

/-- Extract the first key from a JSON object by trying common keys. -/
def firstObjKey (j : Json) : Option String :=
  -- Try pretty-printing and extracting, or try known patterns
  let candidates := ["Add", "Sub", "Mul", "Div", "Rem", "Shl", "Shr",
    "BitAnd", "BitOr", "BitXor", "Eq", "Ne", "Lt", "Le", "Gt", "Ge",
    "Not", "Neg", "Offset"]
  candidates.findSome? fun k =>
    match j.getObjVal? k with
    | .ok _ => some k
    | _ => none

/-! ## Helper: extract name from hax identifiers -/

/-- The width part of an integer width tag: the bit width in decimal, and `size`
    for `usize`/`isize`, whose width is the platform word size. -/
def widthDigits : IntWidth → String
  | .w8 => "8" | .w16 => "16" | .w32 => "32" | .w64 => "64" | .w128 => "128"
  | .wsize => "size"

/-- The width tag of an integer type: `widthDigits` of its width for an unsigned
    type, the same prefixed with `i` for a signed type, and `none` for every
    other type. A width-sensitive operation `op` on an operand of the type is
    named `op#<tag>`. -/
def intTypeTag? : ImpType → Option String
  | .uint w => some (widthDigits w)
  | .sint w => some ("i" ++ widthDigits w)
  | _ => none

/-- The tag of a cast from `srcTy` to `dstTy`: `i<w>` for a signed target (any
    source), `<w>` for an unsigned target from an unsigned or non-integer source,
    and `u<w>` for an unsigned target from a signed source, where `<w>` is
    `widthDigits` of the target width. `none` for a non-integer target. -/
def castTag? (srcTy dstTy : ImpType) : Option String :=
  match dstTy, srcTy with
  | .sint w, _ => some ("i" ++ widthDigits w)
  | .uint w, .sint _ => some ("u" ++ widthDigits w)
  | .uint w, _ => some (widthDigits w)
  | _, _ => none

/-- The crates an export carries items for, and the short names of the functions
    and constants those items define.

    An item of a dependency crate appears in the export only as the `DefId` of a
    call or of a value reference. A `DefId` is named by the last segment of its
    path, so a dependency function whose short name is also defined in the
    export takes that same name: the call then reads as a reference to the
    emitted definition, and the dependency function reaches no field of the
    generated `Deps` class. `shadowsLocalFn` identifies that case and
    `extractDefIdName` qualifies the dependency name with its parent module. -/
structure LocalCrate where
  krates : List String := []
  fnNames : List String := []
  deriving Inhabited

/-- The krates whose items the runtime builtin table names, not the `Deps`
    class. A short name from one of these keeps its bare form, which is the key
    the builtin table reads. -/
def builtinKrates : List String := ["core", "std", "alloc", "<synthetic>"]

/-- The untagged call heads that the file printer renders as runtime functions
    rather than `Deps` fields (`builtinTable`, `runtimeName`) or that the
    semantics' builtin tables interpret (`defaultBuiltins`, `fullBuiltins`,
    `hax64Builtins`). -/
def builtinHeads : List String :=
  [ "index", "array_update", "slice_update", "repeat", "array_lit", "push", "len",
    "from_elem", "index_mut", "is_empty", "to_vec", "slice_reverse", "vec_remove",
    "copy_from_slice", "extend_from_slice", "truncate", "with_capacity", "into_vec",
    "into_iter", "iter", "map", "collect", "flat_map", "zip", "next", "new", "enumerate",
    "RangeTo", "RangeFrom", "Range", "range_incl_end",
    "count_ones", "assert_failed", "assert_failed'", "from", "into", "literal",
    "str_opaque", "deref", "deref_mut", "clone", "cast", "castVal", "castVal_w",
    "from_val", "panic", "sha256", "rotate_right", "rotate_left", "_assign",
    "Some", "None", "Ok", "Err",
    "add", "sub", "mul", "div", "rem", "neg", "wrapping_add", "wrapping_sub",
    "wrapping_mul", "Add", "Sub", "Mul", "Div", "Rem", "Neg",
    "wrapping_add_w", "wrapping_sub_w", "wrapping_mul_w",
    "bitand", "bitor", "bitxor", "bitnot", "bitxor_w", "bitand_w", "bitor_w", "shl_w",
    "shr_w", "BitAnd", "BitOr", "BitXor", "shl", "shr", "Shl", "Shr",
    "eq", "Eq", "ne", "Ne", "lt", "le", "gt", "ge", "Lt", "Le", "Gt", "Ge",
    "not", "Not", "and", "And", "or", "Or", "&&", "||", "min", "max",
    "expect", "is_err", "is_none", "is_ok", "is_some", "unwrap", "unwrap_or", "select" ]

/-- No builtin head contains `:`, so no head `q::h` is a builtin head. -/
theorem colon_not_mem_builtinHeads : ∀ s ∈ builtinHeads, ':' ∉ s.toList := by
  simp [builtinHeads]

/-- Whether a `DefId` in krate `krate` with short name `n` names an item of a
    dependency crate whose short name the export also defines. -/
def shadowsLocalFn (lc : LocalCrate) (krate n : String) : Bool :=
  !lc.krates.isEmpty && krate != "" && !lc.krates.contains krate
    && !builtinKrates.contains krate && lc.fnNames.contains n

/-- Extract the last meaningful name from a hax `DefId` path.
    DefId JSON: `{"krate": "...", "path": [{"data": {"TypeNs": "..."}, "disambiguator": 0}, ...]}` -/
partial def extractDefIdName (j : Json) (collisions : List String := [])
    (lc : LocalCrate := {}) : String :=
  -- hax DefId may be: {path: [...]} or {contents: {value: {path: [...]}}}
  -- Unwrap to find the object containing "path"
  let inner := match j.getObjVal? "contents" with
    | .ok c => match c.getObjVal? "value" with
      | .ok v => v
      | _ => c
    | _ => j
  match inner.getObjVal? "path" with
  | .ok (.arr segments) =>
    let names := segments.toList.filterMap fun seg =>
      match seg.getObjVal? "data" with
      | .ok (.str s) => some s  -- Simple string variant
      | .ok data =>
        -- Try {TypeNs: name} or {ValueNs: name} etc.
        match data.getObjVal? "TypeNs", data.getObjVal? "ValueNs" with
        | .ok (.str n), _ => some n
        | _, .ok (.str n) => some n
        | _, _ =>
          -- Try other Ns fields
          match data.getObjVal? "MacroNs", data.getObjVal? "LifetimeNs" with
          | .ok (.str n), _ => some n
          | _, .ok (.str n) => some n
          | _, _ => none
      | _ => none
    -- Check for Impl discriminator to infer integer width.
    -- The inherent-method impls of `core::num` are numbered in source order,
    -- `i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize` (0–11), so the
    -- unsigned widths sit at 6–11; measured on the exports: `u8::overflowing_add`
    -- is Impl 6, `u32::wrapping_add` Impl 8, `u64::to_be_bytes` Impl 9.
    -- Width-sensitive operations (wrapping_add, rotate_right, shr, shl, the
    -- byte conversions) are suffixed with the width tag of the type
    -- (`intTypeTag?`) so the runtime can truncate correctly. The signed impls
    -- 0–5 are read only in the `core` crate; the typed parser replaces the tag
    -- by the one of the call's operand type where that type is an integer.
    let isCore := (inner.getObjValAs? String "krate").toOption == some "core"
    let implWidth : Option String := do
      let segs := segments.toList
      let implSeg ← segs.find? fun seg =>
        match seg.getObjVal? "data" with
        | .ok (.str "Impl") => true
        | _ => false
      let disambiguator ← (implSeg.getObjValAs? Nat "disambiguator").toOption
      match disambiguator with
      | 0 => if isCore then some "i8" else none
      | 1 => if isCore then some "i16" else none
      | 2 => if isCore then some "i32" else none
      | 3 => if isCore then some "i64" else none
      | 4 => if isCore then some "i128" else none
      | 5 => if isCore then some "isize" else none
      | 6 => some "8"
      | 7 => some "16"
      | 8 => some "32"
      | 9 => some "64"
      | 10 => some "128"
      | 11 => some "size"
      | _ => none
    let widthSensitiveOps := ["wrapping_add", "wrapping_sub", "wrapping_mul", "wrapping_neg",
      "rotate_right", "rotate_left", "shr", "shl",
      "bitand", "bitor", "bitxor", "bitnot", "Not",
      -- Byte (de)serialization and overflowing arithmetic are inherent methods
      -- of each integer width. Without the suffix, `u32::to_be_bytes` on a
      -- digest word and `u64::to_be_bytes` on a length field collapse to one
      -- untyped Deps field that no single instance can implement: the SHA-256
      -- digest loop reads four bytes of it and the padding reads eight.
      "to_be_bytes", "to_le_bytes", "from_be_bytes", "from_le_bytes",
      "overflowing_add", "overflowing_sub",
      -- Associated integer consts (`u32::MAX`, `i64::MIN`, …): without
      -- the width suffix they collapse to a bare `MAX`/`MIN` shared
      -- across all integer types and leak into the Deps class as an
      -- ambiguous opaque field.
      "MAX", "MIN"]
    match names.getLast? with
    | some n =>
      -- Suffix width-sensitive ops with bit width (e.g. wrapping_add → wrapping_add#32)
      let base :=
        -- `1..=n` desugars to `RangeInclusive::new`; a bare `new` is
        -- indistinguishable from `Range::new`, and the loop reconstruction
        -- must add one to the upper bound for the inclusive form.
        if n == "new" && names.getD (names.length - 2) "" == "RangeInclusive" then
          "RangeInclusive::new"
        else if widthSensitiveOps.contains n then
          match implWidth with
          | some w => s!"{n}#{w}"
          | none => n
        else n
      -- Bug-2: when a short name collides across parent modules (e.g. edwards25519
      -- vs p256 `scalar_mult`), qualify it with the parent module segment so the
      -- two functions stay distinct. Otherwise one body wins and the other's call
      -- sites mis-type (3-tuple vs 4-tuple point). Applied identically at def and
      -- call sites (both route through here), keeping them consistent.
      --
      -- The same qualification separates a dependency-crate function from a
      -- local definition of the same short name (`shadowsLocalFn`): the two are
      -- distinct functions, and only the qualified one is absent from the
      -- emitted defs, which is what routes it into the `Deps` class.
      let qualified :=
        match names.reverse with
        | _ :: parent :: _ => s!"{parent}_{base}"
        | _ => base
      let krateName : String := (inner.getObjValAs? String "krate").toOption.getD ""
      -- A method declared by a trait (`kind: AssocFn` under a `Trait` parent),
      -- called on a type parameter, has no body in the export; when a local
      -- function has the same short name, the trait method is qualified with
      -- the trait's name so the call does not reach that function.
      let parentKind : Option String := do
        let p ← (inner.getObjVal? "parent").toOption
        let pc ← (p.getObjVal? "contents").toOption
        let pv ← (pc.getObjVal? "value").toOption
        (pv.getObjValAs? String "kind").toOption
      let traitMethodShadow :=
        (inner.getObjValAs? String "kind").toOption == some "AssocFn"
          && parentKind == some "Trait" && lc.fnNames.contains n
      if collisions.contains n || shadowsLocalFn lc krateName n || traitMethodShadow then
        qualified
      else base
    | none =>
      match inner.getObjValAs? String "krate" with
      | .ok k => k
      | _ => "unknown"
  | _ =>
    match inner.getObjValAs? String "krate" with
    | .ok k => k
    | _ => "unknown"

/-- The short name of the enum a variant `DefId` belongs to: the name
    `extractDefIdName` gives its parent, when the `DefId` has kind `Variant` and
    its parent kind `Enum`. `none` for any other `DefId`. -/
def variantEnumName (j : Json) : Option String := do
  let inner := match j.getObjVal? "contents" with
    | .ok c => match c.getObjVal? "value" with
      | .ok v => v
      | _ => c
    | _ => j
  guard ((inner.getObjValAs? String "kind").toOption == some "Variant")
  let p ← (inner.getObjVal? "parent").toOption
  let pv ← (p.getObjVal? "contents" >>= (·.getObjVal? "value")).toOption
  guard ((pv.getObjValAs? String "kind").toOption == some "Enum")
  pure (extractDefIdName pv)

/-- The krate of a hax `DefId`, or `""` when the node carries none. -/
def defIdKrate (defId : Json) : String :=
  let inner := match defId.getObjVal? "contents" with
    | .ok c => match c.getObjVal? "value" with | .ok v => v | _ => c
    | _ => defId
  (inner.getObjValAs? String "krate").toOption.getD ""

/-- The constructor head `E::V` of the variant `V` (short name `name`) of an enum
    `E` of a krate outside `builtinKrates`, for the variant `DefId` `variantDefId`.
    The printer renders it as the constructor `E.V` of the emitted inductive and
    keeps it out of the `Deps` class; it contains `::`, so it is no builtin head
    (`colon_not_mem_builtinHeads`). `none` for a variant of a `builtinKrates` enum
    (`Some`, `Ok`, …), for a `DefId` without a krate, and for a struct. -/
def crateVariantHead? (variantDefId : Json) (name : String) : Option String := do
  let enumName ← variantEnumName variantDefId
  let krate := defIdKrate variantDefId
  guard (krate != "" && !builtinKrates.contains krate)
  pure s!"{enumName}::{name}"

/-- Extract a name from a hax `LocalIdent`.
    LocalIdent JSON: `{"name": "x", "id": ...}` -/
def extractLocalIdentName (j : Json) : String :=
  match j.getObjValAs? String "name" with
  | .ok n => n
  | _ => "unknown"

/-- Extract the DefId name from an `item` JSON object.
    hax items have structure: `{id, value: {def_id: ...}}` or `{def_id: ...}`. -/
partial def extractItemDefIdName (item : Json) (fallback : String)
    (collisions : List String := []) (lc : LocalCrate := {}) : String :=
  let defIdJ := match item.getObjVal? "value" with
    | .ok v => match v.getObjVal? "def_id" with
      | .ok d => some d
      | _ => item.getObjVal? "def_id" |>.toOption
    | _ => item.getObjVal? "def_id" |>.toOption
  match defIdJ with
  | some defId => extractDefIdName defId collisions lc
  | none => fallback

/-- Fallback method-call disambiguation when no impl-self-type map is
    available (e.g. inside `extractCallName`'s standalone path).

    The principled disambiguator is `disambiguateMethodCallWithImplMap`
    (below), which uses hax's structural metadata. This fallback only
    fires when the DefId path contains an `Impl` discriminator
    segment (`{"data": "Impl"}`) — i.e. the call resolves through an
    inherent impl block — and picks the last non-`Impl` TypeNs segment
    as the receiver type prefix.

    **Free function calls** (e.g. `baby_bear::bb_mul`) have no `Impl`
    segment in their path; for those we return `baseName` unchanged so
    the call site matches the locally-emitted `def <baseName>` instead
    of being misclassified as an external dependency. Stdlib krates
    short-circuit identically.

    Historical note: an earlier version prefixed every non-stdlib path
    with its last TypeNs, which incorrectly added a module prefix to
    every free function call (e.g. `bb_mul` → `baby_bear_bb_mul`,
    `merkle_build_root` → `merkle_merkle_build_root`). All such calls
    leaked into the Deps class instead of resolving to local defs. -/
def disambiguateUserMethodName (j : Json) (baseName : String) : String :=
  -- Look at the DefId's path. Format may be: {contents: {value: {path}}}.
  let inner := match j.getObjVal? "contents" with
    | .ok c => match c.getObjVal? "value" with
      | .ok v => v
      | _ => c
    | _ => j
  let krate : String := (inner.getObjValAs? String "krate").toOption.getD ""
  let isStdlibKrate := krate == "core" || krate == "std" || krate == "alloc"
  if isStdlibKrate then baseName
  else
    -- This fallback fires when no impl-self-type map is available
    -- (callers of `extractCallName` outside `parseHaxTExpr`'s Call
    -- branch). When `disambiguateMethodCallWithImplMap` runs afterwards
    -- and finds an Impl ancestor, it produces the principled
    -- `<SelfType>_<method>` form — so we return `baseName` unchanged
    -- when an `Impl` segment is present and let the impl-map take over.
    -- When no Impl segment exists (free function in a module), we also
    -- return `baseName` unchanged so the call resolves to the local
    -- `def <method>` rather than a module-prefixed Deps entry.
    baseName

/-! ## Impl-self-type map (principled method-call disambiguation)

When hax extracts `crs.len()` for a user struct `Crs` with an inherent
`impl Crs { fn len(&self) -> usize { ... } }`, the resolved DefId path
ends `[Impl, ValueNs=len]` in the user's krate. There is no `TypeNs=Crs`
segment — `Impl` is a positional discriminator and the receiver type is
recorded separately in the Impl item's `self_ty` field.

To disambiguate `Crs::len` from `slice::len` (which has path
`[slice, Impl, ValueNs=len]` in the `core` krate), we pre-scan the
top-level JSON items, find every `kind: Impl { self_ty: Adt(...) }`
node, and record `Impl-DefId-id → SelfTypeName`. When a Call resolves
to a DefId whose parent is in this map, we know the receiver type and
emit `<SelfTypeName>_<methodName>`.

This is the principled version of the earlier name-allowlist heuristic
(`["len", "is_empty"]`): it uses hax's own structural metadata rather
than guessing from method names.
-/

/-- The representation of the elements of a field `impl` of `primeir_hax::Field`,
    read from its `MONT_BITS` constant: canonical (`canon`, the stored integer is
    the value) or Montgomery with radix `2 ^ k` (`mont k`, the stored integer is
    the value times `2 ^ k` modulo `p`). -/
inductive FieldImplRepr where
  /-- The stored integer is the value. -/
  | canon
  /-- The stored integer is the value times `2 ^ k` modulo the modulus. -/
  | mont (k : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Parse-time context threaded through the typed parse. `impls` maps an
    Impl-block DefId-interning-id to the short name of the self-type the impl is
    for (method-call disambiguation). `collisions` is the set of function short
    names that collide across ≥2 parent modules (e.g. `scalar_mult` under both
    `edwards25519` and `p256`); such names are qualified with their parent module
    at both def and call sites (Bug-2). The name `ImplSelfTypeMap` is retained for
    minimal churn. -/
structure ImplSelfTypeMap where
  impls : List (Nat × String) := []
  collisions : List String := []
  /-- Struct name → field names in declaration order, for lowering a write
      through a struct-field place (`self.buf = v`) to a functional
      `struct_update` of the root variable. Empty when the caller has no
      struct metadata; field writes then keep the `_assign` sink. -/
  structFields : StructFieldNames := []
  /-- The crate the export is taken from, with the short names of the functions
      it defines. A call into a dependency crate whose short name is one of them
      is qualified with its parent module (`shadowsLocalFn`). -/
  localCrate : LocalCrate := {}
  /-- The methods of the trait `impl` blocks the extracted crate defines, as
      `(impl interning id, method name, emitted name)`. A trait-method call
      whose `in_trait.impl` atom resolves to one of these `impl` blocks takes
      the emitted name, which is also the name the `impl`'s method body is
      emitted under. Built by `buildTraitImplMethodMap`. -/
  traitImplMethods : List (Nat × String × String) := []
  /-- The associated constants of the trait `impl` blocks the extracted crate
      defines, keyed like `traitImplMethods`. A constant read whose
      `in_trait.impl` atom resolves to one of these blocks takes the emitted
      name, under which the constant's value is emitted as a definition. Empty
      unless the trait-to-class emission asks for it
      (`parseHaxFileWithTExpr (traitImplConsts := true)`). -/
  traitImplConsts : List (Nat × String × String) := []
  /-- Whether a read of an associated constant through a trait bound of a
      type parameter (`localBoundAssocConst`) is a nullary call of the constant,
      `.app "ZERO" []`, rather than a variable. Set by the trait-to-class
      emission, where such a read names the class field. -/
  localBoundConstCalls : Bool := false
  /-- The crates whose trait methods are nominal: a call of a method declared
      by a trait of one of these crates, not resolved to a trait `impl` of the
      extracted crate, takes the head `krate::Trait::h`. A call of a method of
      another crate whose head is a builtin head may also take it
      (`ImplSelfTypeMap.qualifiesTraitCall`). -/
  nominalKrates : List String := []
  /-- The local `impl primeir_hax::Field for T` blocks whose self type `T` is
      a newtype over `u64` or over `[u64; n]`, as
      `(impl interning id, T, modulus, number of limbs)`, the number of limbs
      `1` for `u64` (`buildFieldImplMap`). A call of a method of
      `fieldTaggedMethods` resolved to one of them takes the head
      `fieldTagHeadRepr` of its modulus and representation, and a read of its
      `ZERO` or `ONE` is the literal of the representation of `0` or `1`
      (`fieldConstLit?`). -/
  fieldImpls : List (Nat × String × Nat × Nat) := []
  /-- The representation of each `impl` of `fieldImpls` whose representation is
      not canonical, keyed by its interning id (`buildFieldReprMap`); an `impl`
      without an entry is canonical (`fieldReprOf`). -/
  fieldReprs : List (Nat × FieldImplRepr) := []
  deriving Inhabited

/-- Map from newtype struct name (e.g. `"VectorCommitment"`) to its
    inner field type. Built once from the top-level JSON's Struct
    items, used by `tElideToNamedProj` to rewrite `.app ".0" [x]`
    calls into `.namedProj T x` markers when `x : T`. -/
abbrev NewtypeMap := List (String × ImpType)

/-! ## Struct-field assignment lowering

A Rust write through a struct-field place — `self.buf = v`, `self.buf[i] = v`,
`self.buf_len += 1` — has no mutable struct in the extraction; its meaning is a
functional update of the *root* variable. The lowering emits
`assign root (struct_update#S#i#n root newValue)`, an ordinary assignment the
mutation-threading passes and the renderer's accumulator extraction already
carry (the same shape an array-element write takes). The renderer expands the
`struct_update#S#i#n` head into the `Hax.struct_update_fst`/`_snd` composition
on the tuple encoding. -/

/-- Strip `deref` wrappers from a typed place expression. -/
def tStripDerefPlace : TExpr → TExpr
  | .mk (.deref e) _ => tStripDerefPlace e
  | e => e

/-- Strip `borrow` and `deref` wrappers from a typed place expression. -/
def tStripRefPlace : TExpr → TExpr
  | .mk (.deref e) _ => tStripRefPlace e
  | .mk (.borrow e) _ => tStripRefPlace e
  | e => e

/-- One level of `tIndexMutPlace`: `index_mut a i` read as `index a' i`, where
    `a'` is `a` without its `borrow`/`deref` wrappers, typed with the element
    type the call's `&mut` result points to. -/
def tIndexMutPlace1 : TExpr → TExpr
  | .mk (.app "index_mut" [a, i]) ty => .mk (.app "index" [tStripRefPlace a, i]) ty.pointee
  | e => e

/-- The element place of an overloaded `IndexMut::index_mut` call. For a `Vec`
    (or any other `IndexMut` implementor) hax gives the left-hand side `a[i]` of
    an assignment as `*index_mut(&mut a, i)`; with the outer `deref` stripped this
    is `index_mut (borrow a) i`, which this function reads as the place
    `index a i`, the `borrow`/`deref` wrappers of `a` removed, typed with the
    element type (the call's type is a `&mut` to it). A nested place `a[i][j]`
    is normalised at both levels. Every other expression is returned
    unchanged. -/
def tIndexMutPlace : TExpr → TExpr
  | .mk (.app "index_mut" [a, i]) ty =>
    .mk (.app "index" [tIndexMutPlace1 (tStripRefPlace a), i]) ty.pointee
  | e => e

/-- Whether `t` is the type `&mut Vec<_>`. -/
def isMutVecRef : ImpType → Bool
  | .ref (.adt n _) true => n == "Vec" || n.endsWith "::Vec"
  | _ => false

/-- A call argument with the `DerefMut::deref_mut` re-borrow of a `Vec` removed.
    hax gives a `&mut Vec<T>` place `v` passed where `&mut [T]` is expected as
    `&mut *deref_mut(&mut v)`; for `Vec` the call returns a reference to the
    same elements, so the argument is read as `&mut *(&mut v)`, whose root is
    `v`. The `borrow`/`deref` wrappers above the call are kept; a `deref_mut`
    whose argument is not typed `&mut Vec<_>`, and every other expression, is
    returned unchanged. -/
def tDerefMutArg : TExpr → TExpr
  | .mk (.borrow e) ty => .mk (.borrow (tDerefMutArg e)) ty
  | .mk (.deref e) ty => .mk (.deref (tDerefMutArg e)) ty
  | .mk (.app "deref_mut" [a]) ty =>
    if isMutVecRef a.ty then a else .mk (.app "deref_mut" [a]) ty
  | e => e

/-- Whether `t` is a mutable reference to a sequence: `&mut [T]`, `&mut [T; n]`
    or `&mut Vec<T>`. -/
def isMutSeqRef : ImpType → Bool
  | .ref (.slice _) true => true
  | .ref (.array _ _) true => true
  | t => isMutVecRef t

/-- The element type of a sequence type `[T]`, `[T; n]` or `Vec<T>`, seen through
    at most one reference; `.unknown` for any other type. -/
def seqElemTy : ImpType → ImpType
  | .slice t | .array t _ | .adt _ [t] => t
  | .ref (.slice t) _ | .ref (.array t _) _ | .ref (.adt _ [t]) _ => t
  | _ => .unknown

/-- The krate of the item a hax `fun` expression names, or `""` when it names
    no global item. -/
def callKrate (funJ : Json) : String :=
  let item := (funJ.getObjVal? "contents" >>= (·.getObjVal? "GlobalName")
    >>= (·.getObjVal? "item")).toOption
  let defId := item.bind fun it =>
    ((it.getObjVal? "value" >>= (·.getObjVal? "def_id")) <|> it.getObjVal? "def_id").toOption
  let inner := defId.map fun d => match d.getObjVal? "contents" with
    | .ok c => match c.getObjVal? "value" with | .ok v => v | _ => c
    | _ => d
  (inner.bind fun i => (i.getObjValAs? String "krate").toOption).getD ""

/-- The write-back form of the `core` slice method `a.swap(i, j)`. For `a` a
    `&mut [T]`, `&mut [T; n]` or `&mut Vec<T>` argument whose place is a variable
    `v`, it is the assignment

    `v := if i < len v && j < len v then
            array_update (array_update v i (index v j)) j (index v i)
          else v`,

    whose two reads are of the value of `v` before the call. When an index is out
    of range Rust panics, while the guarded form leaves `v` unchanged. The
    reads of `v` are through a `deref` typed with the referenced sequence type, so
    no operand of the rewritten form is a `&mut` argument. `none` when `a` is not
    such a place. -/
def tSliceSwap (a i j : TExpr) : Option TExprKind :=
  if !isMutSeqRef a.ty then none
  else
    match tStripRefPlace a with
    | v@(.mk (.var n) vTy) =>
      let seqTy := match vTy with | .ref t _ => t | t => t
      let sv : TExpr := match vTy with
        | .ref t _ => .mk (.deref v) t
        | _ => v
      let elTy := seqElemTy seqTy
      let usz : ImpType := .uint .wsize
      let lenV : TExpr := .mk (.app "len" [sv]) usz
      let inRange : TExpr := .mk (.app "&&"
        [.mk (.app "Lt" [i, lenV]) .bool, .mk (.app "Lt" [j, lenV]) .bool]) .bool
      let upd1 : TExpr := .mk (.app "array_update"
        [sv, i, .mk (.app "index" [sv, j]) elTy]) seqTy
      let upd2 : TExpr := .mk (.app "array_update"
        [upd1, j, .mk (.app "index" [sv, i]) elTy]) seqTy
      some (.assign n (.mk (.ifThenElse inRange upd2 sv) seqTy))
    | _ => none

/-- View a typed expression as a single-level struct-field place: the root
    variable, the field name, and the deref-stripped struct expression. `none`
    for the newtype projection `.0`, a nested field path, or a root that is not
    a plain variable. -/
def tFieldProjPlace : TExpr → Option (String × String × TExpr)
  | .mk (.app pf [sE]) _ =>
    if pf.startsWith "." && pf != ".0" then
      match tStripDerefPlace sE with
      | .mk (.var n) ty => some (n, (pf.drop 1).toString, .mk (.var n) ty)
      | _ => none
    else none
  | _ => none

/-- Lower an assignment through a struct-field place to an assignment of the
    place's root variable. `lhs'` is the deref-stripped place; `mkVal` builds
    the written value from the place's current-value read (identity for `=`,
    the compound operator's application for `op=`). Handled places, over a root
    variable `x` whose field `f` resolves through `sf` to position `i` of `n`:

      x.f      ↦ assign x (struct_update#S#i#n x (mkVal x.f))
      x.f[j]   ↦ assign x (struct_update#S#i#n x (array_update x.f j (mkVal x.f[j])))

    Every other place — an unresolved or ambiguous field name, a nested field
    path, a non-variable root — is `none`, and the caller keeps its previous
    lowering. -/
def tFieldPlaceAssign (sf : StructFieldNames) (lhs' : TExpr)
    (mkVal : TExpr → TExpr) : Option TExprKind :=
  match lhs' with
  | .mk (.app ind [fieldE, idx]) _ =>
    if ind == "index" || ind == "index_mut" then
      match tFieldProjPlace fieldE with
      | some (root, fname, sE) =>
        match resolveStructField sf fname with
        | some (sname, i, n) =>
          let read := TExpr.mk (.app "index" [fieldE, idx]) .unknown
          let newArr := TExpr.mk (.app "array_update" [fieldE, idx, mkVal read]) fieldE.ty
          some (.assign root (TExpr.mk (.app (structUpdateHead sname i n) [sE, newArr]) sE.ty))
        | none => none
      | none => none
    else none
  | _ =>
    match tFieldProjPlace lhs' with
    | some (root, fname, sE) =>
      match resolveStructField sf fname with
      | some (sname, i, n) =>
        some (.assign root (TExpr.mk (.app (structUpdateHead sname i n) [sE, mkVal lhs']) sE.ty))
      | none => none
    | none => none

/-- Lower an assignment through the place `a[j].g`, field `g` of element `j` of a
    sequence place `a` that is a variable or a single-level struct-field place
    `x.f`. With `e := index a j` and `g` at position `k` of the `m` fields of the
    element's struct `T` (`resolveFieldOfTy`), the new sequence is

      `array_update a j (struct_update#T#k#m e (mkVal e.g))`,

    stored by `v := …` for a variable `v` and through `tFieldPlaceAssign` for
    `x.f`. The element may be given as `*index_mut(&mut a, j)`, the form hax
    exports for an element of a `Vec`. `none` for every other place. -/
def tElemFieldPlaceAssign (sf : StructFieldNames) (lhs' : TExpr)
    (mkVal : TExpr → TExpr) : Option TExprKind :=
  match lhs' with
  | .mk (.app pg [elE]) gTy =>
    if !pg.startsWith "." || pg == ".0" then none
    else
      match tIndexMutPlace (tStripDerefPlace elE) with
      | .mk (.app "index" [arr, j]) _ =>
        let elTy := match elE.ty with | .ref t _ => t | t => t
        match resolveFieldOfTy sf elTy (pg.drop 1).toString with
        | some (sname, k, m) =>
          let elRead : TExpr := .mk (.app "index" [arr, j]) elTy
          let newEl : TExpr := .mk (.app (structUpdateHead sname k m)
            [elRead, mkVal (.mk (.app pg [elRead]) gTy)]) elTy
          let newArr : TExpr := .mk (.app "array_update" [arr, j, newEl]) arr.ty
          match tStripRefPlace arr with
          | .mk (.var n) _ => some (.assign n newArr)
          | arrP => tFieldPlaceAssign sf arrP (fun _ => newArr)
        | none => none
      | _ => none
  | _ => none

/-- The place `p` with every `index_mut(&mut a, i)` read as `index a i`, and
    the `deref` of such a call dropped (the call's target is the element place
    itself). `index` and field projections are normalised below the top; every
    other node is kept. -/
partial def tPlaceRead : TExpr → TExpr
  | .mk (.app "index_mut" [a, i]) ty =>
    .mk (.app "index" [tPlaceRead (tStripRefPlace a), i]) ty.pointee
  | .mk (.app "index" [a, i]) ty => .mk (.app "index" [tPlaceRead a, i]) ty
  | e@(.mk (.app pf [s]) ty) =>
    if pf.startsWith "." then .mk (.app pf [tPlaceRead s]) ty else e
  | .mk (.deref p) ty =>
    match p with
    | .mk (.app "index_mut" _) _ => tPlaceRead p
    | _ => .mk (.deref (tPlaceRead p)) ty
  | e => e

/-- The assignment storing `new` in the place `p`, for a place built from a
    variable by `deref`, `borrow`, `index`, `index_mut` and named struct-field
    projections, in any order and depth. Each step is a functional update of the
    enclosing value, read by `tPlaceRead`:

      `v := new`,
      `a[i] ← new` is `a ← array_update a i new`,
      `s.g ← new` is `s ← struct_update#T#k#m s new`,

    with `g` at position `k` of the `m` fields of `T`, resolved from the type of
    `s` (`resolveFieldOfTy`). `none` when a field does not resolve or the place
    has another node (a call result, the newtype projection `.0`, a tuple
    field). -/
partial def tPlaceAssign (sf : StructFieldNames) : TExpr → TExpr → Option TExprKind
  | .mk (.var n) _, new => some (.assign n new)
  | .mk (.deref p) _, new => tPlaceAssign sf p new
  | .mk (.borrow p) _, new => tPlaceAssign sf p new
  | .mk (.app "index_mut" [a, i]) ty, new =>
    tPlaceAssign sf (.mk (.app "index" [tStripRefPlace a, i]) ty) new
  | .mk (.app "index" [a, i]) _, new =>
    let a' := tPlaceRead a
    tPlaceAssign sf a (.mk (.app "array_update" [a', i, new]) a'.ty)
  | .mk (.app pf [s]) _, new =>
    if pf.startsWith "." && pf != ".0" then
      let s' := tPlaceRead s
      match resolveFieldOfTy sf s'.ty (pf.drop 1).toString with
      | some (sname, k, m) =>
        tPlaceAssign sf s (.mk (.app (structUpdateHead sname k m) [s', new]) s'.ty)
      | none => none
    else none
  | _, _ => none

/-- A one-line outline of a place, for a refusal message: variables by name,
    `*p`, `&p`, `p[_]`, `p.f`, and the head of any other node. -/
partial def placeOutline : TExpr → String
  | .mk (.var n) _ => n
  | .mk (.deref p) _ => s!"*({placeOutline p})"
  | .mk (.borrow p) _ => s!"&({placeOutline p})"
  | .mk (.app "index" [a, _]) _ => s!"{placeOutline a}[_]"
  | .mk (.app "index_mut" [a, _]) _ => s!"index_mut({placeOutline a}, _)"
  | .mk (.app f [s]) _ =>
    if f.startsWith "." then s!"{placeOutline s}{f}" else s!"{f}(…)"
  | .mk (.app f _) _ => s!"{f}(…)"
  | .mk (.proj p i) _ => s!"{placeOutline p}.{i}"
  | _ => "<expr>"

/-- The refusal of an assignment to the place `lhs` that the parse cannot lower
    to a threaded write: lowering it would lose the write. -/
def unsupportedPlaceError (lhs : TExpr) : String :=
  s!"unsupported assignment place (the write would be lost): {placeOutline lhs}"

/-- The value, before a call, of the sequence place a `&mut [T]`, `&mut [T; n]`
    or `&mut Vec<T>` argument `a` names. For a variable `v` it is `v`, read
    through a `deref` typed with the referenced type when `v` is itself a
    reference; for a struct-field place `x.f` it is the field projection. The
    result is typed with the sequence type. `none` for any other argument. -/
def tSeqPlaceRead (a : TExpr) : Option TExpr :=
  if !isMutSeqRef a.ty then none
  else
    match tStripRefPlace a with
    | v@(.mk (.var _) vTy) =>
      match vTy with
      | .ref t _ => some (.mk (.deref v) t)
      | _ => some v
    | p@(.mk (.app pf [_]) _) => if pf.startsWith "." then some p else none
    | _ => none

/-- The assignment that stores `new` in the place `a` names: `v := new` for a
    variable `v`, and the rebinding of `x` to `x` with field `f` set to `new` for
    a single-level struct-field place `x.f` (`tFieldPlaceAssign`). `none` for
    any other place. -/
def tSeqPlaceWrite (sf : StructFieldNames) (a new : TExpr) : Option TExprKind :=
  match tStripRefPlace a with
  | .mk (.var n) _ => some (.assign n new)
  | p => tFieldPlaceAssign sf p (fun _ => new)

/-- The write-back form of the `core` slice method `a.reverse()`: for `a` a
    `&mut [T]`, `&mut [T; n]` or `&mut Vec<T>` argument naming a variable or a
    struct-field place with current value `s` (`tSeqPlaceRead`), the assignment
    of `slice_reverse s` to that place (`tSeqPlaceWrite`). The builtin name
    `slice_reverse` is distinct from any crate function `reverse`. `none` for
    any other argument. -/
def tSliceReverse (sf : StructFieldNames) (a : TExpr) : Option TExprKind := do
  let s ← tSeqPlaceRead a
  tSeqPlaceWrite sf a (.mk (.app "slice_reverse" [s]) s.ty)

/-- The name bound to the pair `vec_remove s i` in the write-back form of
    `Vec::remove`. -/
def vecRemoveTmp : String := "_removed"

/-- The write-back form of `Vec::remove(a, i)`: for `a` a `&mut Vec<T>` argument
    naming a variable or a struct-field place with current value `s`, the
    expression

    `let _removed := vec_remove s i; (a := _removed.1); _removed.0`,

    whose value is the removed element and which rebinds the place to the vector
    without it. `vec_remove s i` is undefined when `i` is out of range, where
    Rust panics. `none` for any other argument. -/
def tVecRemove (sf : StructFieldNames) (a i : TExpr) : Option TExprKind := do
  guard (isMutVecRef a.ty)
  let s ← tSeqPlaceRead a
  let elTy := seqElemTy s.ty
  let pairTy : ImpType := .tuple [elTy, s.ty]
  let tmp : TExpr := .mk (.var vecRemoveTmp) pairTy
  let w ← tSeqPlaceWrite sf a (.mk (.proj tmp 1) s.ty)
  some (.letBind vecRemoveTmp (.mk (.app "vec_remove" [s, i]) pairTy)
    (.mk (.seq (.mk w .unit) (.mk (.proj tmp 0) elTy)) elTy))

/-- The last path segment of a hax `DefId`: the item's own short name.
    Each segment's `data` is either a bare string (`"Impl"`) or a one-key
    object tagged with the namespace it lives in (`{"ValueNs": "intt"}`), as
    `extractDefIdName` reads them. -/
def defIdLeafName (defId : Json) : Option String := do
  let contents ← (defId.getObjVal? "contents").toOption
  let v ← (contents.getObjVal? "value").toOption
  match v.getObjVal? "path" with
  | .ok (.arr segs) =>
    let names : List String := segs.toList.filterMap fun seg =>
      match seg.getObjVal? "data" with
      | .ok (.str s) => some s
      | .ok d =>
        ["TypeNs", "ValueNs", "MacroNs", "LifetimeNs"].findSome? fun ns =>
          match d.getObjVal? ns with
          | .ok (.str n) => some n
          | _ => none
      | _ => none
    names.getLast?
  | _ => none

/-- Extract the short name of a struct/enum from an `Adt` type JSON.
    Returns `none` if the JSON doesn't have the expected shape. -/
partial def extractAdtShortName (adtJ : Json) : Option String := do
  -- adtJ is the Adt's `value` (containing `def_id`, `generic_args`, etc.)
  let v ← (adtJ.getObjVal? "value").toOption
  let defId ← (v.getObjVal? "def_id").toOption
  let contents ← (defId.getObjVal? "contents").toOption
  let did_v ← (contents.getObjVal? "value").toOption
  let path ← (did_v.getObjVal? "path").toOption
  match path with
  | .arr segs =>
    -- Last TypeNs entry is the type name
    let names : List String := segs.toList.filterMap fun seg =>
      match seg.getObjVal? "data" with
      | .ok data =>
        match data.getObjVal? "TypeNs" with
        | .ok (.str n) => if n != "Impl" then some n else none
        | _ => none
      | _ => none
    names.getLast?
  | _ => none

/-- Build the map by walking top-level JSON items.

    For each `kind: Impl { of_trait: null, self_ty: Adt(...) }` (an
    inherent impl block), record the impl's interning id (from
    `owner_id.contents.id`) → self-type short name. Inherent impls are
    the ones whose methods can be called as `<receiver>.<method>()`
    and need disambiguation from stdlib methods of the same name. -/
partial def buildImplSelfTypeMap (j : Json) : List (Nat × String) :=
  match j with
  | .arr items =>
    items.toList.filterMap fun it =>
      match it.getObjVal? "kind" with
      | .ok kindJ =>
        match kindJ.getObjVal? "Impl" with
        | .ok impl =>
          -- Skip trait impls — `of_trait` is non-null only for trait
          -- impls. Inherent impls have `of_trait: null`.
          let isTraitImpl := match impl.getObjVal? "of_trait" with
            | .ok Json.null => false
            | .ok _ => true   -- any non-null value is a trait impl
            | _ => false
          if isTraitImpl then none
          else
            -- Get self_ty.value.Adt
            match impl.getObjVal? "self_ty" with
            | .ok selfTy =>
              match selfTy.getObjVal? "value" with
              | .ok stVal =>
                match stVal.getObjVal? "Adt" with
                | .ok adt =>
                  -- Impl items have `def_id: null`; the interning id
                  -- we want is in `owner_id.contents.id`.
                  match it.getObjVal? "owner_id" with
                  | .ok oid =>
                    match oid.getObjVal? "contents" with
                    | .ok c =>
                      match c.getObjValAs? Nat "id" with
                      | .ok implId =>
                        match extractAdtShortName adt with
                        | some name => some (implId, name)
                        | none => none
                      | _ => none
                    | _ => none
                  | _ => none
                | _ => none
              | _ => none
            | _ => none
        | _ => none
      | _ => none
  | _ => []

/-- Resolve the `parent` chain of a DefId to find the nearest Impl
    ancestor's interning-id. Returns `none` if no Impl ancestor is
    found in the chain. Uses `getObjVal? "Impl"` rather than pattern-
    matching on `Json.obj`'s internal RBNode representation. -/
partial def findImplAncestorId (defIdJ : Json) (depth : Nat := 8) : Option Nat :=
  if depth == 0 then none
  else
    match defIdJ.getObjVal? "contents" with
    | .ok c =>
      match c.getObjVal? "value" with
      | .ok v =>
        -- Check if THIS DefId points to an Impl. `kind` is either a
        -- string variant or an object `{Impl: {of_trait: ...}}`. We
        -- detect Impl by looking up the "Impl" key on the kind value.
        let isImpl := match v.getObjVal? "kind" with
          | .ok kindJ => (kindJ.getObjVal? "Impl").toOption.isSome
          | _ => false
        if isImpl then
          (c.getObjValAs? Nat "id").toOption
        else
          -- Recurse into parent
          match v.getObjVal? "parent" with
          | .ok parent =>
            match parent with
            | .null => none
            | parentJ =>
              match parentJ.getObjVal? "contents" with
              | .ok _ => findImplAncestorId parentJ (depth - 1)
              | _ => none
          | _ => none
      | _ => none
    | _ => none

/-- Look up an Impl-DefId-id in the map. -/
def lookupImplSelfType (id : Nat) (m : ImplSelfTypeMap) : Option String :=
  m.impls.find? (·.1 == id) |>.map (·.2)

/-- The `impl` block and method name a hax trait-method `Call` resolves to.

    The callee of such a call is a `GlobalName` whose `item.value.def_id` is
    the *trait's* `AssocFn`; the resolution is carried beside it, in
    `item.value.in_trait.impl`. A `Concrete` atom there names the `impl` block
    by its `DefId`, whose interning id is the one `buildImplSelfTypeMap` and
    `buildTraitImplMethodMap` key on. Any other atom (a parametric `LocalBound`,
    a projection) yields `none`, as does a call that is not through a trait. -/
def traitCallImplMethod (funJ : Json) : Option (Nat × String) := do
  let contents ← (funJ.getObjVal? "contents").toOption
  let gn ← (contents.getObjVal? "GlobalName").toOption
  let item ← (gn.getObjVal? "item").toOption
  let v ← (item.getObjVal? "value").toOption
  let inTrait ← (v.getObjVal? "in_trait").toOption
  let implJ ← (inTrait.getObjVal? "impl").toOption
  let concrete ← (implJ.getObjVal? "Concrete").toOption
  let cVal ← (concrete.getObjVal? "value").toOption
  let cDefId ← (cVal.getObjVal? "def_id").toOption
  let cContents ← (cDefId.getObjVal? "contents").toOption
  let implId ← (cContents.getObjValAs? Nat "id").toOption
  let calleeDefId ← (v.getObjVal? "def_id").toOption
  let method ← defIdLeafName calleeDefId
  some (implId, method)

/-- The emitted name of a trait-method call that resolves to an `impl` block
    the extracted crate defines and that defines the method itself. `none`
    for a call resolving to an `impl` outside the crate, and for a method the
    `impl` inherits as a trait default; such a call keeps its bare name and
    reaches the generated `Deps` class. -/
def resolveTraitImplCall (funJ : Json) (m : ImplSelfTypeMap) : Option String := do
  let (implId, method) ← traitCallImplMethod funJ
  let entry ← m.traitImplMethods.find? fun p => p.1 == implId && p.2.1 == method
  some entry.2.2

/-- The methods of `primeir_hax::Field` whose calls take a modulus-tagged head,
    with their arities. -/
def fieldTaggedMethods : List (String × Nat) :=
  [("add", 2), ("sub", 2), ("mul", 2), ("neg", 1), ("square", 1), ("double", 1)]

/-- The head `<method>#p<modulus>` of a field operation in the prime field of
    modulus `p`, the modulus in decimal: `mul#p2013265921`. -/
def fieldTagHead (method : String) (p : Nat) : String :=
  method ++ "#p" ++ toString p

/-- The head `<method>#p<modulus>#r<k>` of a field operation in the prime field
    of modulus `p` whose elements are stored in the Montgomery representation
    with radix `2 ^ k`, both numbers in decimal: the canonical head
    (`fieldTagHead`) followed by `#r` and `k`. -/
def fieldTagHeadMont (method : String) (p k : Nat) : String :=
  fieldTagHead method p ++ "#r" ++ toString k

/-- The head of a field operation at the modulus `p` in the representation `r`:
    `fieldTagHead` for `canon`, `fieldTagHeadMont` for `mont k`. -/
def fieldTagHeadRepr (method : String) (p : Nat) : FieldImplRepr → String
  | .canon => fieldTagHead method p
  | .mont k => fieldTagHeadMont method p k

/-- In the canonical representation the head is `fieldTagHead`. -/
theorem fieldTagHeadRepr_canon (method : String) (p : Nat) :
    fieldTagHeadRepr method p .canon = fieldTagHead method p := by
  simp only [fieldTagHeadRepr]

/-- The characters before the first `#`, and the characters after it when
    there is one. -/
def splitAtHash : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | '#' :: cs => ([], some cs)
  | c :: cs => (c :: (splitAtHash cs).1, (splitAtHash cs).2)

/-- A nonempty list of decimal digits. -/
def decDigitsOk (cs : List Char) : Bool := !cs.isEmpty && cs.all Char.isDigit

/-- The method, the modulus and the representation of the characters of a field
    head: the characters before the first `#`, then `p` and a nonempty list of
    decimal digits, then either nothing (`canon`) or `#r` and a nonempty list of
    decimal digits (`mont k`). `none` for characters of any other form. -/
def fieldTagReprChars? (cs : List Char) : Option (String × Nat × FieldImplRepr) :=
  match splitAtHash cs with
  | (pre, some ('p' :: r1)) =>
    match splitAtHash r1 with
    | (pd, none) =>
      if decDigitsOk pd then some (String.ofList pre, Nat.ofDigitChars 10 pd 0, .canon)
      else none
    | (pd, some ('r' :: kd)) =>
      if decDigitsOk pd && decDigitsOk kd then
        some (String.ofList pre, Nat.ofDigitChars 10 pd 0, .mont (Nat.ofDigitChars 10 kd 0))
      else none
    | _ => none
  | _ => none

/-- The method, the modulus and the representation of a field head
    (`fieldTagReprChars?`). -/
def fieldTagRepr? (f : String) : Option (String × Nat × FieldImplRepr) :=
  fieldTagReprChars? f.toList

theorem splitAtHash_append {xs : List Char} (h : '#' ∉ xs) (ys : List Char) :
    splitAtHash (xs ++ '#' :: ys) = (xs, some ys) := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ '#' := fun e => h (e ▸ List.mem_cons_self)
    have h' : '#' ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    rw [List.cons_append, splitAtHash.eq_3 c _ (by simpa using hc), ih h']

theorem splitAtHash_of_not_mem {xs : List Char} (h : '#' ∉ xs) :
    splitAtHash xs = (xs, none) := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ '#' := fun e => h (e ▸ List.mem_cons_self)
    have h' : '#' ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    rw [splitAtHash.eq_3 c _ (by simpa using hc), ih h']

theorem not_hash_mem_toDigits (n : Nat) : '#' ∉ Nat.toDigits 10 n := fun h => by
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  revert this
  decide

theorem decDigitsOk_toDigits (n : Nat) : decDigitsOk (Nat.toDigits 10 n) = true := by
  have hl := @Nat.length_toDigits_pos 10 n
  simp only [decDigitsOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true]
  exact ⟨List.ne_nil_of_length_pos hl,
    fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc⟩

/-- **The field heads round-trip**: `fieldTagRepr?` reads the method, the
    modulus and the representation back off the head `fieldTagHeadRepr` writes,
    for a method name without `#`. -/
theorem fieldTagRepr?_fieldTagHeadRepr {method : String} (hm : '#' ∉ method.toList)
    (p : Nat) (r : FieldImplRepr) :
    fieldTagRepr? (fieldTagHeadRepr method p r) = some (method, p, r) := by
  have hs : ∀ n : Nat, (toString n).toList = Nat.toDigits 10 n := fun _ => Nat.toList_repr
  cases r with
  | canon =>
    simp only [fieldTagRepr?, fieldTagHeadRepr, fieldTagHead, String.toList_append, hs]
    rw [List.append_assoc, show "#p".toList ++ Nat.toDigits 10 p
        = '#' :: ('p' :: Nat.toDigits 10 p) from rfl, fieldTagReprChars?,
      splitAtHash_append hm]
    simp only
    rw [splitAtHash_of_not_mem (not_hash_mem_toDigits p)]
    simp only [decDigitsOk_toDigits, if_true, String.ofList_toList, Nat.ofDigitChars_ten_toDigits]
  | mont k =>
    simp only [fieldTagRepr?, fieldTagHeadRepr, fieldTagHeadMont, fieldTagHead,
      String.toList_append, hs]
    rw [List.append_assoc, List.append_assoc, List.append_assoc,
      show "#p".toList ++ (Nat.toDigits 10 p ++ ("#r".toList ++ Nat.toDigits 10 k))
        = '#' :: ('p' :: (Nat.toDigits 10 p ++ '#' :: 'r' :: Nat.toDigits 10 k)) from rfl,
      fieldTagReprChars?, splitAtHash_append hm]
    simp only
    rw [splitAtHash_append (not_hash_mem_toDigits p)]
    simp only [decDigitsOk_toDigits, Bool.and_self, if_true, String.ofList_toList,
      Nat.ofDigitChars_ten_toDigits]

/-- No method of `fieldTaggedMethods` has `#` in its name. -/
theorem not_hash_of_lookup_fieldTaggedMethods {method : String} {arity : Nat}
    (h : fieldTaggedMethods.lookup method = some arity) : '#' ∉ method.toList := by
  have hmem : method ∈ fieldTaggedMethods.map (·.1) := by
    simp only [fieldTaggedMethods, List.lookup] at h
    simp only [fieldTaggedMethods, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false]
    repeat' split at h
    all_goals simp_all
  simp only [fieldTaggedMethods, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The representation of the `impl` with the interning id `implId`: its entry
    in `m.fieldReprs`, and `canon` when it has none. -/
def fieldReprOf (m : ImplSelfTypeMap) (implId : Nat) : FieldImplRepr :=
  (m.fieldReprs.lookup implId).getD .canon

/-- An `impl` of a map without representation entries is canonical. -/
theorem fieldReprOf_of_fieldReprs_nil {m : ImplSelfTypeMap} (h : m.fieldReprs = [])
    (implId : Nat) : fieldReprOf m implId = .canon := by
  simp [fieldReprOf, h]

/-- The modulus-tagged head (`fieldTagHeadRepr`, at the modulus and the
    representation of the `impl`) of a call with `nArgs` arguments of a method
    of `fieldTaggedMethods` that resolves to an `impl` of `m.fieldImpls`, when
    `nArgs` is the method's arity. `none` for any other call. -/
def fieldTaggedHead? (funJ : Json) (nArgs : Nat) (m : ImplSelfTypeMap) : Option String := do
  guard (!m.fieldImpls.isEmpty)
  let (implId, method) ← traitCallImplMethod funJ
  let arity ← fieldTaggedMethods.lookup method
  guard (arity == nArgs)
  let entry ← m.fieldImpls.find? (·.1 == implId)
  pure (fieldTagHeadRepr method entry.2.2.1 (fieldReprOf m implId))

/-- **The heads `fieldTaggedHead?` writes round-trip**: `fieldTagRepr?` reads
    from each the method, the modulus of its `impl` and the representation of
    that `impl`. -/
theorem fieldTagRepr?_of_fieldTaggedHead? {funJ : Json} {nArgs : Nat}
    {m : ImplSelfTypeMap} {h : String} (hh : fieldTaggedHead? funJ nArgs m = some h) :
    ∃ implId method entry, traitCallImplMethod funJ = some (implId, method) ∧
      m.fieldImpls.find? (·.1 == implId) = some entry ∧
      fieldTagRepr? h = some (method, entry.2.2.1, fieldReprOf m implId) := by
  unfold fieldTaggedHead? at hh
  cases hc : traitCallImplMethod funJ with
  | none => simp [hc] at hh
  | some x =>
    obtain ⟨implId, method⟩ := x
    cases ha : fieldTaggedMethods.lookup method with
    | none => simp [hc, ha] at hh
    | some arity =>
      cases he : m.fieldImpls.find? (·.1 == implId) with
      | none => simp [hc, ha, he] at hh
      | some entry =>
        simp only [hc, ha, he, Option.bind_eq_bind, Option.bind_some] at hh
        refine ⟨implId, method, entry, rfl, he, ?_⟩
        have hh' : fieldTagHeadRepr method entry.2.2.1 (fieldReprOf m implId) = h := by
          revert hh
          cases (!m.fieldImpls.isEmpty) <;> cases (arity == nArgs) <;> simp [guard, failure]
        rw [← hh']
        exact fieldTagRepr?_fieldTagHeadRepr (not_hash_of_lookup_fieldTaggedMethods ha) _ _

/-- The literal of a field element `v < 2^64` in `n` limbs: the integer
    literal `v` for one limb, and the array literal of the `n` little-endian
    `u64` limbs of `v` (`v`, then `0`s) otherwise. -/
def fieldLimbsLit (v : Int) (n : Nat) : TExprKind :=
  if n ≤ 1 then .lit (.int v)
  else .app "array_lit"
    ((List.range n).map fun i => .mk (.lit (.int (if i = 0 then v else 0))) (.uint .w64))

/-- The `n` little-endian base-`2^64` limbs of `v`. -/
def natLimbs : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, v => v % 2 ^ 64 :: natLimbs n (v / 2 ^ 64)

/-- The number little-endian base-`2^64` limbs denote. -/
def limbsValue (ls : List Nat) : Nat := ls.foldr (fun l acc => l + 2 ^ 64 * acc) 0

/-- The limbs of `v` denote `v` modulo `2^(64 n)`. -/
theorem limbsValue_natLimbs (n v : Nat) : limbsValue (natLimbs n v) = v % 2 ^ (64 * n) := by
  induction n generalizing v with
  | zero => simp [natLimbs, limbsValue, Nat.mod_one]
  | succ n ih =>
    have := ih (v / 2 ^ 64)
    simp only [limbsValue, natLimbs, List.foldr_cons] at this ⊢
    rw [this, Nat.mul_succ, Nat.add_comm (64 * n) 64, Nat.pow_add, Nat.mod_mul]

/-- Every limb is below `2^64`. -/
theorem natLimbs_lt (n v : Nat) : ∀ l ∈ natLimbs n v, l < 2 ^ 64 := by
  induction n generalizing v with
  | zero => simp [natLimbs]
  | succ n ih =>
    intro l hl
    simp only [natLimbs, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact Nat.mod_lt _ (by decide)
    · exact ih _ l hl

/-- The limbs of a number below `2^64`: the number, then `0`s. -/
theorem natLimbs_of_lt {v : Nat} (hv : v < 2 ^ 64) (n : Nat) :
    natLimbs (n + 1) v = (List.range (n + 1)).map (fun i => if i = 0 then v else 0) := by
  have hz : ∀ k, natLimbs k 0 = List.replicate k 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp [natLimbs, ih, List.replicate_succ]
  rw [natLimbs, Nat.mod_eq_of_lt hv, Nat.div_eq_of_lt hv, hz, List.range_succ_eq_map]
  simp only [List.map_cons, if_true, List.map_map]
  congr 1
  apply List.ext_getElem <;> simp

/-- The literal of a stored integer `v` in `n` limbs: the integer literal `v`
    for one limb, and the array literal of the `n` little-endian `u64` limbs of
    `v` (`natLimbs`) otherwise. -/
def fieldLimbsLitNat (v n : Nat) : TExprKind :=
  if n ≤ 1 then .lit (.int v)
  else .app "array_lit" ((natLimbs n v).map fun (l : Nat) => .mk (.lit (.int (l : Int))) (.uint .w64))

/-- Below `2^64` the two literals agree. -/
theorem fieldLimbsLit_eq_fieldLimbsLitNat {v : Nat} (hv : v < 2 ^ 64) (n : Nat) :
    fieldLimbsLit v n = fieldLimbsLitNat v n := by
  unfold fieldLimbsLit fieldLimbsLitNat
  split
  · rfl
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [natLimbs_of_lt hv, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply]
    split <;> rfl

/-- The integer the representation `r` stores for the value `v` at the modulus
    `p`: `v` for `canon`, `v * 2 ^ k mod p` for `mont k`. -/
def fieldReprVal (r : FieldImplRepr) (p v : Nat) : Nat :=
  match r with
  | .canon => v
  | .mont k => v * 2 ^ k % p

/-- The literal of the value `v` in the representation `r`, at the modulus `p`
    and in `n` limbs: `fieldLimbsLit v n` for `canon`, and the literal of the
    stored integer (`fieldReprVal`, `fieldLimbsLitNat`) for `mont k`. -/
def fieldConstLitRepr (r : FieldImplRepr) (p n v : Nat) : TExprKind :=
  match r with
  | .canon => fieldLimbsLit v n
  | .mont k => fieldLimbsLitNat (fieldReprVal (.mont k) p v) n

/-- In the canonical representation the literal of `v` is `fieldLimbsLit v n`. -/
theorem fieldConstLitRepr_canon (p n v : Nat) :
    fieldConstLitRepr .canon p n v = fieldLimbsLit v n := by
  simp only [fieldConstLitRepr]

/-- **The literal is the literal of the stored integer**: for a value below
    `2^64`, in every representation, `fieldConstLitRepr` is the literal of the
    limbs of the integer the representation stores. -/
theorem fieldConstLitRepr_eq (r : FieldImplRepr) (p n : Nat) {v : Nat} (hv : v < 2 ^ 64) :
    fieldConstLitRepr r p n v = fieldLimbsLitNat (fieldReprVal r p v) n := by
  cases r with
  | canon => exact fieldLimbsLit_eq_fieldLimbsLitNat hv n
  | mont k => rfl

/-- The literal of a read of the associated constant `ZERO` (`0`) or `ONE`
    (`1`) of an `impl` of `m.fieldImpls`, in the representation and the limbs
    of the `impl` (`fieldConstLitRepr`), from the `NamedConst` or `GlobalName`
    node of the read. `none` for any other read. -/
def fieldConstLit? (globalName : Json) (m : ImplSelfTypeMap) : Option TExprKind := do
  guard (!m.fieldImpls.isEmpty)
  let (implId, item) ← traitCallImplMethod
    (Json.mkObj [("contents", Json.mkObj [("GlobalName", globalName)])])
  let entry ← m.fieldImpls.find? (·.1 == implId)
  match item with
  | "ZERO" => some (fieldConstLitRepr (fieldReprOf m implId) entry.2.2.1 entry.2.2.2 0)
  | "ONE" => some (fieldConstLitRepr (fieldReprOf m implId) entry.2.2.1 entry.2.2.2 1)
  | _ => none

/-- **The constants `fieldConstLit?` reads**: a read yields a literal exactly
    when it resolves to an `impl` of `m.fieldImpls` and names `ZERO` or `ONE`,
    and the literal is then the literal of the limbs of the integer the
    representation of the `impl` stores for `0` or `1`. -/
theorem fieldConstLit?_eq_some_iff {globalName : Json} {m : ImplSelfTypeMap}
    {k : TExprKind} :
    fieldConstLit? globalName m = some k ↔
      ∃ implId item entry, traitCallImplMethod
          (Json.mkObj [("contents", Json.mkObj [("GlobalName", globalName)])]) =
          some (implId, item) ∧
        m.fieldImpls.find? (·.1 == implId) = some entry ∧
        ((item = "ZERO" ∧
            k = fieldLimbsLitNat (fieldReprVal (fieldReprOf m implId) entry.2.2.1 0)
              entry.2.2.2) ∨
          (item = "ONE" ∧
            k = fieldLimbsLitNat (fieldReprVal (fieldReprOf m implId) entry.2.2.1 1)
              entry.2.2.2)) := by
  unfold fieldConstLit?
  cases hc : traitCallImplMethod
      (Json.mkObj [("contents", Json.mkObj [("GlobalName", globalName)])]) with
  | none => simp
  | some x =>
    obtain ⟨implId, item⟩ := x
    cases he : m.fieldImpls.find? (·.1 == implId) with
    | none => simp [he]
    | some entry =>
      have hne : (!m.fieldImpls.isEmpty) = true := by
        cases hf : m.fieldImpls with
        | nil => simp [hf] at he
        | cons _ _ => rfl
      simp only [he, hne, guard, if_true, Option.bind_eq_bind, Option.bind_some,
        Option.some.injEq, Prod.mk.injEq, exists_and_left, pure]
      rw [fieldConstLitRepr_eq _ _ _ (by decide : (0 : Nat) < 2 ^ 64),
        fieldConstLitRepr_eq _ _ _ (by decide : (1 : Nat) < 2 ^ 64)]
      constructor
      · intro hk
        refine ⟨implId, item, ⟨rfl, rfl⟩, entry, he, ?_⟩
        split at hk
        · exact Or.inl ⟨rfl, (Option.some.inj hk).symm⟩
        · exact Or.inr ⟨rfl, (Option.some.inj hk).symm⟩
        · cases hk
      · rintro ⟨_, _, ⟨rfl, rfl⟩, x, hx, h⟩
        rw [he] at hx
        cases hx
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- The value of the callee's `DefId` of a call whose callee node `funJ` is a
    `GlobalName`; `none` for any other callee. -/
def calleeDefIdValue? (funJ : Json) : Option Json := do
  let contents ← (funJ.getObjVal? "contents").toOption
  let gn ← (contents.getObjVal? "GlobalName").toOption
  let item ← (gn.getObjVal? "item").toOption
  let v ← (item.getObjVal? "value").toOption
  let defId ← (v.getObjVal? "def_id").toOption
  let dc ← (defId.getObjVal? "contents").toOption
  (dc.getObjVal? "value").toOption

/-- Whether a call of a method of a trait of the crate `krate`, whose head is `h`
    without qualification, takes the qualified head: for a crate of
    `nominalKrates`; and, outside the trait-to-class emission
    (`localBoundConstCalls`), for a crate other than `primeir_hax` and outside
    `builtinKrates` when `h` is a builtin head (`builtinHeads`), which the
    printer and the semantics would read as the runtime function. -/
def ImplSelfTypeMap.qualifiesTraitCall (m : ImplSelfTypeMap) (krate h : String) : Bool :=
  m.nominalKrates.contains krate ||
    (!m.localBoundConstCalls && krate != "primeir_hax" && !builtinKrates.contains krate &&
      builtinHeads.contains h)

/-- The crate `krate` and the qualifier `krate::Trait` of a call whose callee is a
    method declared by the trait `Trait` of the crate `krate`: the callee's
    `DefId` has kind `AssocFn`, its parent has kind `Trait`, and `Trait` is the
    second-to-last segment of its path. `none` for any other call. -/
def traitMethodQualifier? (funJ : Json) : Option (String × String) := do
  let dv ← calleeDefIdValue? funJ
  let krate ← (dv.getObjValAs? String "krate").toOption
  guard ((dv.getObjValAs? String "kind").toOption == some "AssocFn")
  let p ← (dv.getObjVal? "parent").toOption
  let pv ← (p.getObjVal? "contents" >>= (·.getObjVal? "value")).toOption
  guard ((pv.getObjValAs? String "kind").toOption == some "Trait")
  let segs ← (dv.getObjValAs? (Array Json) "path").toOption
  guard (segs.size ≥ 2)
  let seg ← segs[segs.size - 2]?
  let trait ← (seg.getObjVal? "data" >>= (·.getObjValAs? String "TypeNs")).toOption
  pure (krate, s!"{krate}::{trait}")

/-- The qualifier `krate::Trait` of a call of a method of the trait `Trait` of a
    crate `krate` with `qual krate` (`traitMethodQualifier?`); `none` for any
    other call. -/
def nominalTraitQualifier? (funJ : Json) (qual : String → Bool) : Option String := do
  let (krate, q) ← traitMethodQualifier? funJ
  guard (qual krate)
  pure q

/-- The head `q::h` of a call with qualifier `q` (`nominalTraitQualifier?`)
    whose head is `h` when no crate is nominal. -/
def qualifyNominalHead (q h : String) : String := s!"{q}::{h}"

/-- A qualified head `q::h` is not a builtin head. -/
theorem qualifyNominalHead_not_mem_builtinHeads (q h : String) :
    qualifyNominalHead q h ∉ builtinHeads := by
  intro hm
  apply colon_not_mem_builtinHeads _ hm
  simp only [qualifyNominalHead, String.toList_append, List.mem_append]
  exact Or.inl (Or.inr (by simp [toString]))

/-- The head of a call with callee node `funJ` whose unqualified head is `h`:
    `krate::Trait::h` for a call of a method of a trait of `krate` with
    `m.qualifiesTraitCall krate h` (`nominalTraitQualifier?`) that is not
    resolved to a trait `impl` of the extracted crate (`resolved`), and `h`
    otherwise. -/
def traitCallHead (m : ImplSelfTypeMap) (funJ : Json) (resolved : Bool) (h : String) :
    String :=
  match nominalTraitQualifier? funJ (m.qualifiesTraitCall · h) with
  | some q => if resolved then h else qualifyNominalHead q h
  | none => h

/-- A call of a method of a trait of a crate of `builtinKrates` (`core::ops::Mul`,
    `core::cmp::PartialEq`, …) outside `nominalKrates` keeps its unqualified head,
    the key of the runtime builtin table. -/
theorem traitCallHead_builtinKrate (m : ImplSelfTypeMap) (funJ : Json) (resolved : Bool)
    (h k q : String) (hq : traitMethodQualifier? funJ = some (k, q))
    (hb : k ∈ builtinKrates) (hn : k ∉ m.nominalKrates) :
    traitCallHead m funJ resolved h = h := by
  simp [traitCallHead, nominalTraitQualifier?, hq, ImplSelfTypeMap.qualifiesTraitCall, hn, hb,
    guard, failure]

/-- Outside the trait-to-class emission, the head of a call of a method of a
    trait of a crate other than `primeir_hax` and outside `builtinKrates`, not
    resolved to a trait `impl` of the extracted crate, is not a builtin head:
    either `h`, when `h` is not a builtin head, or the qualified head. -/
theorem traitCallHead_not_mem_builtinHeads (m : ImplSelfTypeMap) (funJ : Json)
    (h k q : String) (hq : traitMethodQualifier? funJ = some (k, q))
    (hl : m.localBoundConstCalls = false) (hp : k ≠ "primeir_hax")
    (hb : k ∉ builtinKrates) :
    traitCallHead m funJ false h ∉ builtinHeads := by
  unfold traitCallHead nominalTraitQualifier?
  rw [hq]
  by_cases hc : m.qualifiesTraitCall k h
  · simp [hc, guard, qualifyNominalHead_not_mem_builtinHeads]
  · simp_all [ImplSelfTypeMap.qualifiesTraitCall, guard, failure]

/-- The head a call has when no crate is nominal, from its head under the
    nominal crates `krates`: `h` for `k::T::h` with `k` in `krates`, and the
    head itself otherwise. It inverts `qualifyNominalHead` on the qualifiers
    of `krates`. -/
def unqualifyNominalHead (krates : List String) (f : String) : String :=
  if krates.isEmpty then f
  else
    match f.splitOn "::" with
    | k :: _ :: rest@(_ :: _) => if krates.contains k then "::".intercalate rest else f
    | _ => f

/-- The head of the surface definitions and the `Deps` class for the head `f`
    under the nominal crates `krates`: `unqualifyNominalHead krates f`, except
    that a remaining head `k::T::h` with `h` a builtin head (the qualified head
    of `ImplSelfTypeMap.qualifiesTraitCall`) is the `Deps` name `T_h`. -/
def surfaceTraitHead (krates : List String) (f : String) : String :=
  let f' := unqualifyNominalHead krates f
  match f'.splitOn "::" with
  | [k, t, h] => if k != "" && builtinHeads.contains h then s!"{t}_{h}" else f'
  | _ => f'

/-- `surfaceTraitHead` applied to every app head of a typed expression. -/
partial def tUnqualifyNominalHeads (krates : List String) (e : TExpr) : TExpr :=
  match e with
  | .mk (.app f args) ty =>
    .mk (.app (surfaceTraitHead krates f) (args.map (tUnqualifyNominalHeads krates))) ty
  | e => tMapChildren (tUnqualifyNominalHeads krates) e

/-- The emitted name of a read of an associated constant (`Self::ONE`) that
    resolves to a trait `impl` block of the extracted crate, from the
    `NamedConst` or `GlobalName` node of the read (a node with an `item` whose
    value carries `in_trait`). `none` when `traitImplConsts` has no entry
    for it, which is always the case unless the trait-to-class emission built
    that table. -/
def resolveTraitImplConstRef (globalName : Json) (m : ImplSelfTypeMap) :
    Option String := do
  guard (!m.traitImplConsts.isEmpty)
  let (implId, item) ← traitCallImplMethod
    (Json.mkObj [("contents", Json.mkObj [("GlobalName", globalName)])])
  let entry ← m.traitImplConsts.find? fun p => p.1 == implId && p.2.1 == item
  some entry.2.2

/-- Whether the `NamedConst` or `GlobalName` node of a read names an associated
    constant (`def_id` of kind `AssocConst`) through a trait bound of a type
    parameter (an `in_trait.impl` atom of kind `LocalBound`), as `F::ZERO` in a
    function generic over `F: Field`. -/
def localBoundAssocConst (globalName : Json) : Bool :=
  let r : Option Unit := do
    let item ← (globalName.getObjVal? "item").toOption
    let v ← (item.getObjVal? "value").toOption
    let defId ← (v.getObjVal? "def_id").toOption
    let contents ← (defId.getObjVal? "contents").toOption
    let dv ← (contents.getObjVal? "value").toOption
    let kind ← (dv.getObjValAs? String "kind").toOption
    guard (kind == "AssocConst")
    let inTrait ← (v.getObjVal? "in_trait").toOption
    let implJ ← (inTrait.getObjVal? "impl").toOption
    let _ ← (implJ.getObjVal? "LocalBound").toOption
    pure ()
  r.isSome

/-- The trait and the self type of a read through a trait bound: the short
    name of the trait of the node's `in_trait` reference and its first generic
    argument, when that argument is a type variable of an export rewritten by
    `ClassEmit.keepTypeParams` (a type parameter `R`, or a projection on one
    spelled `(PolyRing.Coeff R)`). -/
def localBoundTraitSelf (globalName : Json) : Option (String × String) := do
  let item ← (globalName.getObjVal? "item").toOption
  let v ← (item.getObjVal? "value").toOption
  let inTrait ← (v.getObjVal? "in_trait").toOption
  let tr ← (inTrait.getObjVal? "trait").toOption
  let tv ← (tr.getObjVal? "value").toOption
  let tvv := (tv.getObjVal? "value").toOption.getD tv
  let defId ← (tvv.getObjVal? "def_id").toOption
  let tn ← defIdLeafName defId
  let args ← (tvv.getObjValAs? (Array Json) "generic_args").toOption
  let a0 ← args[0]?
  let ty ← (a0.getObjVal? "Type").toOption
  let tyv := (ty.getObjVal? "value").toOption.getD ty
  let s ← (tyv.getObjValAs? String "TypeVar").toOption
  pure (tn, s)

/-- The head `::clsitem::T::c::S` of a read of the item `c` of the class `T`
    at the type `S`. The renderer prints it as `(T.c (Self := S))`
    (`classItemRef?`); a head starting with `::` is never a `Deps` field. -/
def classItemHead (trait item selfTy : String) : String :=
  s!"::clsitem::{trait}::{item}::{selfTy}"

/-- The Lean term `(T.c (Self := S))` of a `classItemHead`, or `none` for any
    other head. -/
def classItemRef? (f : String) : Option String :=
  match f.splitOn "::" with
  | "" :: "clsitem" :: t :: c :: rest =>
    if rest.isEmpty then none
    else some s!"({t}.{c} (Self := {"::".intercalate rest}))"
  | _ => none

/-- The typed-expression kind of a read of a constant named `name` from its
    `NamedConst` or `GlobalName` node: the emitted name of a constant of a trait
    `impl` of the crate (`resolveTraitImplConstRef`); a nullary call of an
    associated constant read through a trait bound when
    `m.localBoundConstCalls` is set (`localBoundAssocConst`), qualified by its
    class and taken at the bound's type (`classItemHead`) when the bound's
    self type is a type variable, since a nullary class item does not
    determine its instance and two classes may declare an item of one name; a
    variable otherwise. A read of `ZERO` or `ONE` of a field `impl`
    (`fieldConstLit?`) is the literal of `0` or `1` in the limbs of the
    `impl`. -/
def constReadKind (globalName : Json) (m : ImplSelfTypeMap) (name : String) : TExprKind :=
  match fieldConstLit? globalName m with
  | some k => k
  | none =>
  match resolveTraitImplConstRef globalName m with
  | some n => .var n
  | none =>
    if m.localBoundConstCalls && localBoundAssocConst globalName then
      match localBoundTraitSelf globalName with
      | some (t, s) => .app (classItemHead t name s) []
      | none => .app name []
    else .var name

/-- The value of an integer limit (`u64::MAX`, `i32::MIN`, …) read by a
    `NamedConst` or `GlobalName` node of type `ty`: the node names an
    associated constant `MAX` or `MIN` of an inherent `impl` in the module
    `core::num`, and `ty` is a fixed-width integer type. The unsigned limits
    are `2 ^ w - 1` and `0`, the signed ones `2 ^ (w - 1) - 1` and
    `-2 ^ (w - 1)`, for the width `w` of `IntWidth.bits` (64 for `usize` and
    `isize`). `none` for any other node. -/
def coreIntLimit? (globalName : Json) (ty : ImpType) : Option Int := do
  let item ← (globalName.getObjVal? "item").toOption
  let defId ← ((item.getObjVal? "value" >>= (·.getObjVal? "def_id")) <|>
    item.getObjVal? "def_id").toOption
  let inner := match defId.getObjVal? "contents" with
    | .ok c => (c.getObjVal? "value").toOption.getD c
    | _ => defId
  guard ((inner.getObjValAs? String "krate").toOption == some "core")
  let segs ← (inner.getObjValAs? (Array Json) "path").toOption
  let seg0 ← segs[0]?
  guard ((seg0.getObjVal? "data" >>= (·.getObjValAs? String "TypeNs")).toOption == some "num")
  let segN ← segs.back?
  let leaf ← (segN.getObjVal? "data" >>= (·.getObjValAs? String "ValueNs")).toOption
  match leaf, ty with
  | "MAX", .uint w => some ((2 : Int) ^ w.bits - 1)
  | "MIN", .uint _ => some 0
  | "MAX", .sint w => some ((2 : Int) ^ (w.bits - 1) - 1)
  | "MIN", .sint w => some (-(2 : Int) ^ (w.bits - 1))
  | _, _ => none

/-- Disambiguate a method-call name using the impl map. Given the
    Call's `fun` JSON (a GlobalName) and the base method name, walk
    the function's DefId.parent chain to find an Impl ancestor. If
    that Impl's self-type is in the map, return `<TypeName>_<base>`. -/
def disambiguateMethodCallWithImplMap
    (funJ : Json) (baseName : String) (implMap : ImplSelfTypeMap) : String :=
  if implMap.impls.isEmpty then baseName
  else
    match funJ.getObjVal? "contents" with
    | .ok contents =>
      match contents.getObjVal? "GlobalName" with
      | .ok gn =>
        match gn.getObjVal? "item" with
        | .ok item =>
          -- Get the function's DefId
          let defIdJ := match item.getObjVal? "value" with
            | .ok v => (v.getObjVal? "def_id").toOption
            | _ => (item.getObjVal? "def_id").toOption
          match defIdJ with
          | some did =>
            -- Walk parent chain to find Impl ancestor
            match did.getObjVal? "contents" with
            | .ok c =>
              match c.getObjVal? "value" with
              | .ok v =>
                match v.getObjVal? "parent" with
                | .ok parent =>
                  match parent with
                  | .null => baseName
                  | parentJ =>
                    match findImplAncestorId parentJ with
                    | some implId =>
                      match lookupImplSelfType implId implMap with
                      | some tyName => s!"{tyName}_{baseName}"
                      | none => baseName
                    | none => baseName
                | _ => baseName
              | _ => baseName
            | _ => baseName
          | none => baseName
        | _ => baseName
      | _ => baseName
    | _ => baseName

/-- Extract a function name from a hax expression (for Call).
    If the callee is a GlobalName, extract its item's DefId name and
    disambiguate user methods.  Otherwise use a placeholder. -/
partial def extractCallName (j : Json) (collisions : List String := [])
    (lc : LocalCrate := {}) : String :=
  -- j is the `fun` expression (a Decorated<ExprKind>)
  match j.getObjVal? "contents" with
  | .ok contents =>
    match contents.getObjVal? "GlobalName" with
    | .ok gn =>
      match gn.getObjVal? "item" with
      | .ok item =>
        let baseName := extractItemDefIdName item "unknown_fn" collisions lc
        -- Locate the DefId for disambiguation (same lookup pattern as
        -- extractItemDefIdName).
        let defIdJ := match item.getObjVal? "value" with
          | .ok v => match v.getObjVal? "def_id" with
            | .ok d => some d
            | _ => item.getObjVal? "def_id" |>.toOption
          | _ => item.getObjVal? "def_id" |>.toOption
        match defIdJ with
        | some defId => disambiguateUserMethodName defId baseName
        | none => baseName
      | _ => "unknown_fn"
    | _ => "indirect_call"
  | _ => "unknown_fn"

/-! ## Type mapping -/

/-- Map hax's BinOp to a string name. -/
def binOpName (j : Json) : String :=
  match j with
  | .str s => s
  | _ =>
    -- BinOp is an enum: {"Add": null}, {"Sub": null}, etc.
    match firstObjKey j with
    | some k => k
    | none => "binop"

/-- Map hax's UnOp to a string name. -/
def unOpName (j : Json) : String :=
  match j with
  | .str s => s
  | _ =>
    match firstObjKey j with
    | some k => k
    | none => "unop"

/-- Extract the constant length from a hax `{Const: ...}` generic arg.
    Format: `{Const: {contents: {Literal: {Int: {Uint: ["256", "Usize"]}}}}}` -/
def extractConstLen (j : Json) : Option Nat :=
  let constJ := match j.getObjVal? "Const" with
    | .ok c => c
    | _ => j
  let contents := match constJ.getObjVal? "contents" with
    | .ok c => c
    | _ => constJ
  match contents.getObjVal? "Literal" with
  | .ok litJ =>
    match litJ.getObjVal? "Int" with
    | .ok intJ =>
      -- Try {Uint: ["256", "Usize"]} or {Int: ["256", "Isize"]}
      let tryVariant (key : String) : Option Nat :=
        match intJ.getObjVal? key with
        | .ok (.arr elems) =>
          match elems.toList.head? with
          | some (.str s) => s.toNat?
          | _ => none
        | _ => none
      (tryVariant "Uint").orElse fun _ => tryVariant "Int"
    | _ => none
  | _ => none

/-- Extract the last TypeNs name from a hax `def_id` path. -/
def extractAdtPathName (adtInner : Json) : Option String :=
  -- adtInner is the {def_id, generic_args, ...} inside {id, value: ...}
  let defIdJ := match adtInner.getObjVal? "def_id" with
    | .ok d => d
    | _ => adtInner
  -- Navigate: def_id.contents.value.path
  let inner := match defIdJ.getObjVal? "contents" with
    | .ok c => match c.getObjVal? "value" with
      | .ok v => v
      | _ => c
    | _ => defIdJ
  match inner.getObjVal? "path" with
  | .ok (.arr segments) =>
    let names := segments.toList.filterMap fun seg =>
      match seg.getObjVal? "data" with
      | .ok data =>
        match data.getObjVal? "TypeNs" with
        | .ok (.str n) => some n
        | _ => match data.getObjVal? "ValueNs" with
          | .ok (.str n) => some n
          | _ => none
      | _ => none
    names.getLast?
  | _ => none

/-- Extract generic_args from an Adt/Array/Tuple inner value. -/
def extractGenericArgs (adtInner : Json) : Array Json :=
  -- adtInner might be {id, value: {def_id, generic_args, ...}} or {def_id, generic_args, ...}
  let inner := match adtInner.getObjVal? "value" with
    | .ok v => v
    | _ => adtInner
  match inner.getObjValAs? (Array Json) "generic_args" with
  | .ok args => args
  | _ => #[]

/-- The trait and associated-item short names of a projection type `P::A`,
    from the value of its `Alias` node: the trait of the projection's
    `impl_expr` and the leaf name of its `assoc_item`. -/
def aliasProjTraitItem (alias : Json) : Option (String × String) := do
  let kind ← (alias.getObjVal? "kind").toOption
  let proj ← (kind.getObjVal? "Projection").toOption
  let ie ← (proj.getObjVal? "impl_expr").toOption
  let tr ← (ie.getObjVal? "trait").toOption
  let tv ← (tr.getObjVal? "value").toOption
  let tvv ← (tv.getObjVal? "value").toOption
  let traitName ← (tvv.getObjVal? "def_id").toOption >>= defIdLeafName
  let item ← (proj.getObjVal? "assoc_item").toOption
  let itemName ← (item.getObjVal? "def_id").toOption >>= defIdLeafName
  pure (traitName, itemName)

/-- The name of the opaque type that stands for a projection `P::A` of the
    trait `T`: `T_A`. Every occurrence of the projection, whatever the type
    parameter `P`, is read as the ADT of this name, which the emitter declares
    as `axiom T_A : Type`. -/
def assocOpaqueName (traitName itemName : String) : String :=
  s!"{traitName}_{itemName}"

/-- Map hax's TyKind to our ImpType.
    Hax types are wrapped as `{id: N, value: TyKind}`. A projection `P::A` of
    a trait `T` (an `Alias` node) is the opaque ADT `assocOpaqueName T A`. -/
partial def parseHaxType (j : Json) : ImpType :=
  -- Unwrap {id, value} wrapper from hax JSON (primary format)
  let tyKind := match j.getObjVal? "value" with
    | .ok v => v
    | _ => match j.getObjVal? "kind" with
      | .ok k => k
      | _ => j
  match tyKind with
  | .str "Bool" => .bool
  | .str "Char" => .int  -- approximate
  | .str "Str" => .str
  | .str "Never" => .unknown
  | .str "Error" => .unknown
  | _ =>
    if let .ok inner := tyKind.getObjVal? "Int" then
      -- Signed integer: {"Int": "I8"} or {"Int": {"I32": null}} etc.
      match inner with
      | .str "I8"    => .sint .w8
      | .str "I16"   => .sint .w16
      | .str "I32"   => .sint .w32
      | .str "I64"   => .sint .w64
      | .str "I128"  => .sint .w128
      | .str "Isize" => .sint .wsize
      | _ =>
        -- Try externally-tagged enum: {"I32": null}
        if inner.getObjVal? "I8" |>.isOk then .sint .w8
        else if inner.getObjVal? "I16" |>.isOk then .sint .w16
        else if inner.getObjVal? "I32" |>.isOk then .sint .w32
        else if inner.getObjVal? "I64" |>.isOk then .sint .w64
        else if inner.getObjVal? "I128" |>.isOk then .sint .w128
        else if inner.getObjVal? "Isize" |>.isOk then .sint .wsize
        else .int  -- fallback to arbitrary precision
    else if let .ok inner := tyKind.getObjVal? "Uint" then
      -- Unsigned integer: {"Uint": "U8"} or {"Uint": {"U32": null}} etc.
      match inner with
      | .str "U8"    => .uint .w8
      | .str "U16"   => .uint .w16
      | .str "U32"   => .uint .w32
      | .str "U64"   => .uint .w64
      | .str "U128"  => .uint .w128
      | .str "Usize" => .uint .wsize
      | _ =>
        if inner.getObjVal? "U8" |>.isOk then .uint .w8
        else if inner.getObjVal? "U16" |>.isOk then .uint .w16
        else if inner.getObjVal? "U32" |>.isOk then .uint .w32
        else if inner.getObjVal? "U64" |>.isOk then .uint .w64
        else if inner.getObjVal? "U128" |>.isOk then .uint .w128
        else if inner.getObjVal? "Usize" |>.isOk then .uint .wsize
        else .int  -- fallback
    else if let .ok _ := tyKind.getObjVal? "Float" then .unknown  -- no float in our ImpType
    else if let .ok tupleRef := tyKind.getObjVal? "Tuple" then
      -- Tuple: {id, value: {def_id: ...<tuple_N>..., generic_args: [{Type: t1}, ...]}}
      let genArgs := extractGenericArgs tupleRef
      let elemTypes := genArgs.toList.filterMap fun ga =>
        match ga.getObjVal? "Type" with
        | .ok tyJ => some (parseHaxType tyJ)
        | _ => none
      if elemTypes.isEmpty then .unit
      else .tuple elemTypes
    else if let .ok refData := tyKind.getObjVal? "Ref" then
      -- Ref encoding. hax emits `[Region, inner, Mutability]` (3-elt), with
      -- mutability as the boolean `true` for `&mut` and `false` for `&`; an
      -- older shape spells it `"Mut"`, and a 2-elt shape carries no
      -- mutability at all. Handle all three, falling back to the inner
      -- type's parse rather than `.unknown` so refs don't collapse the
      -- type-inference cascade — `Ref Array Int` should typecheck against
      -- `Array Int` thanks to the AutoDerefCoe at the consumer surface.
      match refData with
      | .arr #[_, inner, mut_] =>
        .ref (parseHaxType inner) (mut_ == .bool true || mut_ == .str "Mut")
      | .arr #[_, inner] =>
        .ref (parseHaxType inner) false
      | _ => .unknown
    else if let .ok sliceRef := tyKind.getObjVal? "Slice" then
      -- Slice: similar to Array but without const length
      let genArgs := extractGenericArgs sliceRef
      let elemType := genArgs.toList.findSome? fun ga =>
        match ga.getObjVal? "Type" with
        | .ok tyJ => some (parseHaxType tyJ)
        | _ => none
      match elemType with
      | some et => .slice et
      | none => .slice .unknown
    else if let .ok (.str n) := tyKind.getObjVal? "TypeVar" then
      -- A named type parameter kept as such. hax emits no `TypeVar` kind; it
      -- is written by `Hax.ClassEmit.keepTypeParams`, which rewrites every
      -- `Param` of an export for the trait-to-class emission.
      .typeVar n
    else if let .ok _paramData := tyKind.getObjVal? "Param" then
      -- Generic type parameter: in the untyped extraction model,
      -- crypto type params are almost always byte arrays.
      -- Map to slice (Array Int) as a safe default.
      .slice .int
    else if let .ok arrayRef := tyKind.getObjVal? "Array" then
      -- Array: {id, value: {def_id: ...<array>..., generic_args: [{Type: elemTy}, {Const: len}]}}
      let genArgs := extractGenericArgs arrayRef
      let elemType := genArgs.toList.findSome? fun ga =>
        match ga.getObjVal? "Type" with
        | .ok tyJ => some (parseHaxType tyJ)
        | _ => none
      let len := genArgs.toList.findSome? extractConstLen
      match elemType with
      | some et => .array et (len.getD 0)
      | none => .array .unknown (len.getD 0)
    else if let .ok adtRef := tyKind.getObjVal? "Adt" then
      -- Adt: {id, value: {def_id, generic_args, ...}}
      let adtInner := match adtRef.getObjVal? "value" with
        | .ok v => v
        | _ => adtRef
      let pathName := extractAdtPathName adtInner
      let genArgs := extractGenericArgs adtRef
      let typeArgs := genArgs.toList.filterMap fun ga =>
        match ga.getObjVal? "Type" with
        | .ok tyJ => some (parseHaxType tyJ)
        | _ => none
      match pathName with
      | some n => .adt n typeArgs
      | none => .adt "unknown" typeArgs
    else if let .ok _ := tyKind.getObjVal? "Arrow" then .unknown
    else if let .ok alias := tyKind.getObjVal? "Alias" then
      match aliasProjTraitItem alias with
      | some (t, a) => .adt (assocOpaqueName t a) []
      | none => .unknown
    else .unknown

/-- The hax type of an expression's `ty` field, `.unknown` when absent. -/
def extractExprType (j : Json) : ImpType :=
  match j.getObjVal? "ty" with
  | .ok tyJ => parseHaxType tyJ
  | _ => .unknown

/-- The width tag (`intTypeTag?`) of a hax expression's `ty` field: `some t` for an
    integer type, `none` otherwise. Used by the `Binary`, `AssignOp` and `Unary`
    parsers to annotate the arithmetic operators (`+`, `-`, `*`, `/`, `%`) and the
    width-sensitive operators (`>>`, `^`, `&`, `|`, `!`) with the width and
    signedness of their operand. -/
def extractExprWidth (j : Json) : Option String :=
  intTypeTag? (extractExprType j)

/-- The tag (`castTag?`) of a hax `Cast` node, from the `ty` of its source and the
    `ty` of the enclosing decorated node (the target type). -/
def extractCastTag (srcJ outerJ : Json) : Option String :=
  castTag? (extractExprType srcJ) (extractExprType outerJ)

/-- Suffix an operator name with the width tag of its operand when the tag is
    known: the checked arithmetic operators `Add`, `Sub`, `Mul`, `Div`, `Rem`,
    whose overflow and division by zero depend on the operand type, and the
    bitwise operators, shifts, wrapping operations and rotations. The method
    names `div`, `rem` take the tag of a signed operand only. An operator on an
    operand of unknown or non-integer type keeps its name. -/
def annotateOpWidth (op : String) (width : Option String) : String :=
  let widthSensitive := ["Add", "Sub", "Mul", "Div", "Rem",
                         "BitAnd", "BitOr", "BitXor", "Shl", "Shr", "Not",
                         "bitand", "bitor", "bitxor", "shl", "shr", "bitnot",
                         "wrapping_add", "wrapping_sub", "wrapping_mul", "wrapping_neg",
                         "rotate_right", "rotate_left"]
  let signSensitive := ["div", "rem"]
  if widthSensitive.contains op then
    match width with
    | some w => s!"{op}#{w}"
    | none => op
  else if signSensitive.contains op then
    match width with
    | some w => if w.startsWith "i" then s!"{op}#{w}" else op
    | none => op
  else op

/-! ## Pattern mapping -/

/-- Map hax's `Decorated<PatKind>` to our `ImpPat`. -/
partial def parseHaxPat (j : Json) : ImpPat :=
  -- j is Decorated<PatKind>: {contents: PatKind, ty: ..., span: ...}
  let patKind := match j.getObjVal? "contents" with
    | .ok c => c
    | _ => j
  match patKind with
  | .str "Wild" => .wildcard
  | .str "Missing" => .wildcard
  | .str "Never" => .wildcard
  | _ =>
    if let .ok bindData := patKind.getObjVal? "Binding" then
      match bindData.getObjVal? "var" with
      | .ok varJ => .varPat (extractLocalIdentName varJ)
      | _ => .wildcard
    else if let .ok derefData := patKind.getObjVal? "Deref" then
      -- Deref pattern: unwrap to inner subpattern
      match derefData.getObjVal? "subpattern" with
      | .ok subpat => parseHaxPat subpat
      | _ => .wildcard
    else if let .ok tupleData := patKind.getObjVal? "Tuple" then
      match tupleData.getObjValAs? (Array Json) "subpatterns" with
      | .ok pats => .tuplePat (pats.toList.map parseHaxPat)
      | _ => .wildcard
    else if let .ok constData := patKind.getObjVal? "Constant" then
      -- Constant pattern: try to extract the literal value
      match constData.getObjVal? "value" with
      | .ok valJ => parseConstantPat valJ
      | _ => .wildcard
    else if let .ok variantData := patKind.getObjVal? "Variant" then
      -- Variant pattern: use the variant info
      match variantData.getObjVal? "info" with
      | .ok info =>
        -- hax JSON: info.variant is a DefId (not a string "variant_name")
        let name := match info.getObjVal? "variant" with
          | .ok variantDefId => extractDefIdName variantDefId
          | _ => match info.getObjValAs? String "variant_name" with
            | .ok n => n
            | _ => "Variant"
        -- Get subpatterns
        let subpats := match variantData.getObjValAs? (Array Json) "subpatterns" with
          | .ok fps => fps.toList.filterMap fun fp =>
            match fp.getObjVal? "pattern" with
            | .ok p => some (parseHaxPat p)
            | _ => none
          | _ => []
        match name, subpats with
        | "Some", [p] => .somePat p
        | "None", [] => .nonePat
        | "Ok", [p] => .okPat p
        | "Err", [p] => .errPat p
        -- All other variants: emit a general constructor pattern.
        -- This includes `ControlFlow::Break` / `ControlFlow::Continue`
        -- (which carry one arg each), user-defined enum variants, etc.
        -- The renderer prints these as `.Name args` so Lean resolves
        -- the constructor against the scrutinee's expected type.
        | _, _ => .ctorPat name subpats
      | _ => .wildcard
    else if let .ok orData := patKind.getObjVal? "Or" then
      -- Or pattern: take the first alternative (simplified)
      match orData.getObjValAs? (Array Json) "pats" with
      | .ok pats => match pats.toList.head? with
        | some p => parseHaxPat p
        | none => .wildcard
      | _ => .wildcard
    else if let .ok ascData := patKind.getObjVal? "AscribeUserType" then
      match ascData.getObjVal? "subpattern" with
      | .ok p => parseHaxPat p
      | _ => .wildcard
    else .wildcard
where
  parseConstantPat (j : Json) : ImpPat :=
    -- ConstantExpr might contain a literal
    match j.getObjVal? "contents" with
    | .ok (.str "Unit") => .litPat .unit
    | .ok contents =>
      if let .ok litData := contents.getObjVal? "Literal" then
        parseLitPat litData
      else .wildcard
    | _ => .wildcard
  parseLitPat (j : Json) : ImpPat :=
    if let .ok b := j.getObjValAs? Bool "Bool" then .litPat (.bool b)
    else if let .ok intData := j.getObjVal? "Int" then
      match intData with
      -- Format: "Int": [n, suffix]
      | .arr #[n, _] =>
        match n.getStr? with
        | .ok s => match s.toInt? with
          | some n => .litPat (.int n)
          | none => .wildcard
        | _ => .wildcard
      -- Format: "Int": {"Uint": [n, suffix]} or "Int": {"Int": [n, suffix]}
      | _ =>
        let tryUint := intData.getObjVal? "Uint"
        let tryInt := intData.getObjVal? "Int"
        match tryUint.toOption.orElse fun _ => tryInt.toOption with
        | some (.arr #[n, _]) =>
          match n.getStr? with
          | .ok s => match s.toInt? with
            | some n => .litPat (.int n)
            | none => .wildcard
          | _ => .wildcard
        | _ => .wildcard
    else .wildcard

/-! ## Expression mapping -/

/-- Parse a hax literal. -/
def parseLiteral (data : Json) : ImpExpr :=
  -- Literal { lit: Spanned<LitKind>, neg: bool }
  let neg := match data.getObjValAs? Bool "neg" with
    | .ok true => true
    | _ => false
  let litKind := match data.getObjVal? "lit" with
    | .ok spanned => match spanned.getObjVal? "node" with
      | .ok n => n
      | _ => spanned
    | _ => data
  if let .ok b := litKind.getObjValAs? Bool "Bool" then .lit (.bool b)
  else if let .ok intData := litKind.getObjVal? "Int" then
    -- Format 1: "Int": [n_string, suffix]
    -- Format 2: "Int": {"Uint": [n_string, suffix]} or {"Int": [n_string, suffix]}
    let nArr := match intData with
      | .arr a => some a
      | _ =>
        let tryUint := intData.getObjVal? "Uint"
        let tryInt := intData.getObjVal? "Int"
        match (tryUint.toOption.orElse fun _ => tryInt.toOption) with
        | some (.arr a) => some a
        | _ => none
    match nArr with
    | some #[nJ, suffJ] =>
      let n := match nJ.getStr? with
        | .ok s => s.toInt?.getD 0
        | _ => match nJ.getNat? with
          | .ok n => n
          | _ => 0
      let val := if neg then -n else n
      -- Parse suffix to determine width: "U8", "U16", {"Unsigned":"U8"}, etc.
      let suffix := match suffJ with
        | .str "Unsuffixed" => ""
        | .str s => s
        | _ =>
          -- Try {"Unsigned": "U8"} format (lit expressions)
          match suffJ.getObjVal? "Unsigned" with
          | .ok (.str s) => "U" ++ s.replace "U" ""
          | _ => match suffJ.getObjVal? "Signed" with
            | .ok (.str s) => "I" ++ s.replace "I" ""
            | _ => match suffJ.getObjVal? "Uint" with
              | .ok (.str s) => s
              | _ => match suffJ.getObjVal? "Int" with
                | .ok (.str s) => "I" ++ s
                | _ => ""
      let nval := val.toNat
      match suffix with
      | "U8"  => .lit (.uintLit .w8 nval)
      | "U16" => .lit (.uintLit .w16 nval)
      | "U32" => .lit (.uintLit .w32 nval)
      | "U64" => .lit (.uintLit .w64 nval)
      | "U128" => .lit (.uintLit .w128 nval)
      | "Usize" => .lit (.uintLit .wsize nval)
      | _ => .lit (.int val)
    | some #[nJ] =>
      let n := match nJ.getStr? with
        | .ok s => s.toInt?.getD 0
        | _ => match nJ.getNat? with
          | .ok n => n
          | _ => 0
      .lit (.int (if neg then -n else n))
    | _ => .lit (.int 0)
  else if let .ok bsData := litKind.getObjVal? "ByteStr" then
    -- ByteStr: [[byte0, byte1, ...], "Cooked"]
    match bsData with
    | .arr #[.arr bytes, _] =>
      let byteExprs : List ImpExpr := (bytes.toList.filterMap fun b =>
        match b.getNat? with
        | .ok n => some (ImpExpr.lit (.int n))
        | _ => none)
      .app "array_lit" byteExprs
    | _ => .app "array_lit" []
  else if let .ok _strData := litKind.getObjVal? "Str" then
    -- Str: intentional opaque placeholder, see typed branch comment.
    .app "str_opaque" []
  else .app "literal" []  -- char, float, etc.

/-- The bindings that destructure the tuple held by the variable `parent` by the
    subpatterns `pats`, the first at component `i`. A variable is bound to its
    projection (a name starting with `_` to `_`); a nested tuple pattern binds its
    projection to the temporary `parent_i` and is destructured from it in turn;
    any other subpattern binds its projection to `_`. -/
def tupleDestructBinds (parent : String) : List ImpPat → Nat → List (String × ImpExpr)
  | [], _ => []
  | .varPat n :: ps, i =>
    (if n.startsWith "_" then "_" else n, .proj (.var parent) i) ::
      tupleDestructBinds parent ps (i + 1)
  | .tuplePat qs :: ps, i =>
    let t := parent ++ "_" ++ toString i
    ((t, .proj (.var parent) i) :: tupleDestructBinds t qs 0) ++
      tupleDestructBinds parent ps (i + 1)
  | _ :: ps, i => ("_", .proj (.var parent) i) :: tupleDestructBinds parent ps (i + 1)

/-- The type of component `i` of a tuple type; `.unknown` for any other type. -/
def tupleComponentTy (ty : ImpType) (i : Nat) : ImpType :=
  match ty with
  | .tuple ts => ts.getD i .unknown
  | _ => .unknown

/-- Typed `tupleDestructBinds`: `parentTy` is the type of `parent`; a temporary has
    the type of its component, a projection has type `.unknown`. -/
def tTupleDestructBinds (parent : String) (parentTy : ImpType) :
    List ImpPat → Nat → List (String × TExpr)
  | [], _ => []
  | .varPat n :: ps, i =>
    (if n.startsWith "_" then "_" else n,
      TExpr.mk (.proj (TExpr.mk (.var parent) parentTy) i) .unknown) ::
      tTupleDestructBinds parent parentTy ps (i + 1)
  | .tuplePat qs :: ps, i =>
    let t := parent ++ "_" ++ toString i
    ((t, TExpr.mk (.proj (TExpr.mk (.var parent) parentTy) i) .unknown) ::
        tTupleDestructBinds t (tupleComponentTy parentTy i) qs 0) ++
      tTupleDestructBinds parent parentTy ps (i + 1)
  | _ :: ps, i =>
    ("_", TExpr.mk (.proj (TExpr.mk (.var parent) parentTy) i) .unknown) ::
      tTupleDestructBinds parent parentTy ps (i + 1)

/-- The field subpatterns of a hax struct pattern: for a `Variant` pattern whose
    `info.kind` is `Struct`, each entry of `subpatterns` as the field name (named by
    `extractDefIdName`, as the `Field` projection names it) and the subpattern JSON;
    `none` for any other pattern. -/
def structPatFields? (j : Json) : Option (List (String × Json)) := do
  let patKind := match j.getObjVal? "contents" with
    | .ok c => c
    | _ => j
  let vd ← (patKind.getObjVal? "Variant").toOption
  let info ← (vd.getObjVal? "info").toOption
  let kindJ ← (info.getObjVal? "kind").toOption
  let _ ← (kindJ.getObjVal? "Struct").toOption
  let fps ← (vd.getObjValAs? (Array Json) "subpatterns").toOption
  fps.toList.mapM fun fp => do
    let fj ← (fp.getObjVal? "field").toOption
    let pj ← (fp.getObjVal? "pattern").toOption
    return (extractDefIdName fj, pj)

/-- The bindings that destructure the struct held by the variable `parent` by the
    field subpatterns `fields` (from `structPatFields?`). A variable is bound to the
    field projection `.app ".f" [.var parent]` (a name starting with `_` to `_`); a
    wildcard binds nothing; a nested tuple or struct pattern binds the projection to
    the temporary `parent_f` and is destructured from it in turn; any other
    subpattern binds the projection to `_`. -/
partial def structDestructBinds (parent : String) (fields : List (String × Json)) :
    List (String × ImpExpr) :=
  fields.flatMap fun (f, pj) =>
    let proj : ImpExpr := .app ("." ++ f) [.var parent]
    let t := parent ++ "_" ++ f
    match parseHaxPat pj with
    | .varPat n => [(if n.startsWith "_" then "_" else n, proj)]
    | .wildcard => []
    | .tuplePat qs => (t, proj) :: tupleDestructBinds t qs 0
    | _ => match structPatFields? pj with
      | some fs => (t, proj) :: structDestructBinds t fs
      | none => [("_", proj)]

/-- Typed `structDestructBinds`: `parentTy` is the type of `parent`; a projection
    has the type `ty` of its subpattern node. -/
partial def tStructDestructBinds (parent : String) (parentTy : ImpType)
    (fields : List (String × Json)) : List (String × TExpr) :=
  fields.flatMap fun (f, pj) =>
    let fTy := extractExprType pj
    let proj := TExpr.mk (.app ("." ++ f) [TExpr.mk (.var parent) parentTy]) fTy
    let t := parent ++ "_" ++ f
    match parseHaxPat pj with
    | .varPat n => [(if n.startsWith "_" then "_" else n, proj)]
    | .wildcard => []
    | .tuplePat qs => (t, proj) :: tTupleDestructBinds t fTy qs 0
    | _ => match structPatFields? pj with
      | some fs => (t, proj) :: tStructDestructBinds t fTy fs
      | none => [("_", proj)]

/-- Replace the deepest unitVal in a letBind chain with a continuation.
    letBind a v1 (letBind b v2 unitVal) → letBind a v1 (letBind b v2 cont) -/
def replaceDeepestUnit (e : ImpExpr) (cont : ImpExpr) : ImpExpr :=
  match e with
  | .letBind n v .unitVal => .letBind n v cont
  | .letBind n v body => .letBind n v (replaceDeepestUnit body cont)
  | _ => .seq e cont

/-- Convert a list of statement expressions into nested seq/letBind. -/
def stmtsToSeq (stmts : List ImpExpr) (tail : ImpExpr) : ImpExpr :=
  match stmts with
  | [] => tail
  | [s] => replaceDeepestUnit s tail
  | s :: rest => replaceDeepestUnit s (stmtsToSeq rest tail)

/-- The parameter names of a hax `Closure` payload, in order: `some names` when every
    parameter with a pattern binds a variable or is a wildcard (named `_`) and at least one
    does, `none` otherwise. A parameter whose `pat` is `null` or missing is the implicit
    environment slot and names nothing. -/
def closureParams? (cdata : Json) : Option (List String) :=
  match cdata.getObjValAs? (Array Json) "params" with
  | .ok paramsArr =>
    let step (acc : Option (List String)) (p : Json) : Option (List String) :=
      acc.bind fun ns =>
        match p.getObjVal? "pat" with
        | .ok .null => some ns
        | .ok patJ => match parseHaxPat patJ with
          | .varPat nm => some (ns ++ [nm])
          | .wildcard => some (ns ++ ["_"])
          | _ => none
        | .error _ => some ns
    match paramsArr.toList.foldl step (some []) with
    | some [] => none
    | r => r
  | .error _ => none

/-! ### Rust's `?` operator

hax exports `c?` as `match Try::branch(c) { ControlFlow::Break(r) =>
return FromResidual::from_residual(r), ControlFlow::Continue(p) => b }`. The
adapter reads it as a `match` on `c` whose failure arm returns from the
function: on an `Option`, `match c | some p => b | none => return None`; on a
`Result`, `match c | ok p => b | err r => return Err(r')`, where `r'` is `r`
when the function returns the error type of `c` and `from(r)` otherwise. A
`match` with an early-return arm in an argument position is bound by a `let`
in front of the application. -/

/-- The operand of a `?`: an `Option`, or a `Result` whose error the function
    returns through `from` (`convert = true`) or unchanged. -/
inductive TryOperand where
  | option
  | result (convert : Bool)
  deriving Inhabited, BEq, Repr

/-- A type without its outer references. -/
def tyWithoutRefs : ImpType → ImpType
  | .ref t _ => tyWithoutRefs t
  | t => t

/-- The error type of a `Result` type, under any number of references. -/
def resultErrTy? (t : ImpType) : Option ImpType :=
  match tyWithoutRefs t with
  | .result _ e => some e
  | .adt "Result" [_, e] => some e
  | _ => none

/-- The operand of a `?` whose `Try::branch` call has the type `cfTy` and whose
    failure arm returns a value of the type `retTy`: `option` when the residual
    type of the `ControlFlow` is an `Option`, `result` when it is a `Result`,
    converting the error unless `retTy` is a `Result` with the same error
    type. -/
def tryOperandOf? (cfTy retTy : ImpType) : Option TryOperand :=
  let residual? : Option ImpType := match tyWithoutRefs cfTy with
    | .controlFlow r _ => some r
    | .adt "ControlFlow" (r :: _) => some r
    | _ => none
  match residual?.map tyWithoutRefs with
  | some (.option _) | some (.adt "Option" _) => some .option
  | some r@(.result _ _) | some r@(.adt "Result" _) =>
    match resultErrTy? r, resultErrTy? retTy with
    | some e, some f => some (.result !(e == f))
    | _, _ => some (.result true)
  | _ => none

/-- The type of the value of the first `Return` node of a hax JSON tree, in
    depth-first order. -/
partial def returnValueTy? (j : Json) : Option ImpType :=
  match j.getObjVal? "Return" with
  | .ok r =>
    match r.getObjVal? "value" with
    | .ok v =>
      match v.getObjVal? "ty" with
      | .ok t => some (parseHaxType t)
      | .error _ => none
    | .error _ => none
  | .error _ =>
    match j with
    | .obj kvs => kvs.toList.findSome? fun (_, v) => returnValueTy? v
    | .arr items => items.toList.findSome? returnValueTy?
    | _ => none

/-- The `match` on `c` that reads `c?`, from the arms of the exported `match` on
    `Try::branch(c)`: a `Break(r)` arm returning `from_residual(r)` and a
    `Continue(p)` arm with the body `b`. For an `Option` it is
    `match c | some p => b | none => return None`; for a `Result` it is
    `match c | ok p => b | err r => return Err(r')`, with `r' = from(r)` when the
    error converts and `r' = r` otherwise. `none` when the arms have another
    form. -/
def tryMatch? (k : TryOperand) (c : ImpExpr) (arms : List (ImpPat × ImpExpr)) :
    Option ImpExpr := do
  guard (arms.length == 2)
  let r ← arms.findSome? fun (p, b) =>
    match p, b with
    | .ctorPat "Break" [.varPat r], .earlyReturn (.app "from_residual" [.var r']) =>
      if r == r' then some r else none
    | _, _ => none
  let (q, b) ← arms.findSome? fun (p, b) =>
    match p with
    | .ctorPat "Continue" [q] => some (q, b)
    | _ => none
  match k with
  | .option =>
    pure (.match_ c [(.somePat q, b), (.nonePat, .earlyReturn (.app "None" []))])
  | .result convert =>
    let err : ImpExpr := if convert then .app "from" [.var r] else .var r
    pure (.match_ c [(.okPat q, b), (.errPat (.varPat r), .earlyReturn (.app "Err" [err]))])

/-- The prefix of the names that bind a term moved in front of an application. -/
def tryBindPrefix : String := "_try_"

/-- Whether a term is a `match` with an arm that returns from the function. -/
def isEarlyExitMatch : ImpExpr → Bool
  | .match_ _ arms => arms.any fun (_, b) => (b matches .earlyReturn _)
  | _ => false

/-- The leading `let`s of a term whose names have the prefix `tryBindPrefix`,
    and the term under them. -/
def peelTryLets : ImpExpr → List (String × ImpExpr) × ImpExpr
  | .letBind n v b =>
    if n.startsWith tryBindPrefix then
      let (bs, e) := peelTryLets b
      ((n, v) :: bs, e)
    else ([], .letBind n v b)
  | e => ([], e)

/-- The term `e` under the `let`s `bs`, the first one outermost. -/
def wrapTryLets (bs : List (String × ImpExpr)) (e : ImpExpr) : ImpExpr :=
  bs.foldr (fun (n, v) acc => .letBind n v acc) e

/-- `base` when it is not in `avoid`, otherwise `base_k` for the least `k ≥ 1`
    with `base_k` not in `avoid`. -/
def freshTryName (avoid : List String) (base : String) : String :=
  if !avoid.contains base then base else go (avoid.length + 1) 1
where
  /-- The first of `base_k`, `base_(k+1)`, … not in `avoid`, within `fuel` steps. -/
  go : Nat → Nat → String
    | 0, k => s!"{base}_{k}"
    | fuel + 1, k =>
      let n := s!"{base}_{k}"
      if avoid.contains n then go fuel (k + 1) else n

/-- Whether a term is a literal, a variable or the unit value. -/
def isAtomicArg : ImpExpr → Bool
  | .lit _ | .var _ | .unitVal => true
  | _ => false

/-- The application `f args` with its early-exit arguments in front of it. The
    `let`s that `peelTryLets` finds at the head of an argument move in front of
    the application; an argument that `isEarlyExitMatch` is bound by a `let` in
    front of it and read by name. Every argument before the last such argument
    that is not atomic (`isAtomicArg`), or is a variable with the prefix
    `tryBindPrefix`, is bound in front as well, so that the arguments keep their
    left-to-right order of evaluation. A new name is `_try_<v>` for a `match` on
    the variable `v` and `_try_arg<i>` for argument `i` otherwise, made distinct
    from the free variables of the application and the names moved in front
    (`freshTryName`). -/
def floatEarlyExitArgs (f : String) (args : List ImpExpr) : ImpExpr :=
  let peeled := args.map peelTryLets
  let lifted := peeled.zipIdx.filter fun ((bs, a), _) => !bs.isEmpty || isEarlyExitMatch a
  match lifted.getLast? with
  | none => .app f args
  | some (_, last) =>
    let avoid0 := freeVars (.app f args) ++ peeled.flatMap fun (bs, _) => bs.map (·.1)
    let step (acc : List (String × ImpExpr) × List ImpExpr × List String)
        (x : (List (String × ImpExpr) × ImpExpr) × Nat) :
        List (String × ImpExpr) × List ImpExpr × List String :=
      let (binds, out, avoid) := acc
      let ((bs, a), i) := x
      if i > last then (binds, out ++ [a], avoid)
      else
        let binds := binds ++ bs
        let prefixedVar := match a with
          | .var v => v.startsWith tryBindPrefix
          | _ => false
        if isEarlyExitMatch a || (i < last && (!isAtomicArg a || prefixedVar)) then
          let base := match a with
            | .match_ (.var v) _ => s!"{tryBindPrefix}{v}"
            | _ => s!"{tryBindPrefix}arg{i}"
          let n := freshTryName avoid base
          (binds ++ [(n, a)], out ++ [.var n], n :: avoid)
        else (binds, out ++ [a], avoid)
    let (binds, out, _) := peeled.zipIdx.foldl step ([], [], avoid0)
    wrapTryLets binds (.app f out)

/-- The `match` of `scrut` with `arms`, the `let`s at the head of `scrut` with
    the prefix `tryBindPrefix` moved in front of it when no arm reads their
    names. -/
def matchLiftingTryLets (scrut : ImpExpr) (arms : List (ImpPat × ImpExpr)) : ImpExpr :=
  let (bs, s) := peelTryLets scrut
  let armVars := arms.flatMap fun (_, b) => freeVars b
  if bs.isEmpty || bs.any (fun (n, _) => armVars.contains n) then .match_ scrut arms
  else wrapTryLets bs (.match_ s arms)

/-- The `match` the adapter reads from an exported `match` on `scrut` with the
    arms `arms`, `armsJ` being the JSON of the arms and `scrutTy` the type of
    `scrut`: a `?` on `c` (`scrut = branch(c)`) is `tryMatch?`, and the `let`s
    with the prefix `tryBindPrefix` at the head of `scrut` move in front of the
    `match` (`matchLiftingTryLets`). -/
def readMatch (scrut : ImpExpr) (scrutTy : ImpType) (armsJ : List Json)
    (arms : List (ImpPat × ImpExpr)) : ImpExpr :=
  let (bs, s) := peelTryLets scrut
  let armVars := arms.flatMap fun (_, b) => freeVars b
  let tryForm? : Option ImpExpr := match s with
    | .app "branch" [c] =>
      (tryOperandOf? scrutTy ((returnValueTy? (.arr armsJ.toArray)).getD .unknown)).bind
        fun k => tryMatch? k c arms
    | _ => none
  match tryForm? with
  | some m =>
    if bs.any (fun (n, _) => armVars.contains n) then .match_ scrut arms
    else wrapTryLets bs m
  | none => matchLiftingTryLets scrut arms

/-! The same for `TExpr`. -/

/-- `tryMatch?` on `TExpr`. The `None` and `Err(r')` values have the type of
    `from_residual(r)`; `r` has the error type of its residual type and `from(r)`
    the error type the function returns. -/
def tTryMatch? (k : TryOperand) (c : TExpr) (arms : List (ImpPat × TExpr)) :
    Option TExprKind := do
  guard (arms.length == 2)
  let (r, rTy, fTy, bTy) ← arms.findSome? fun (p, b) =>
    match p, b with
    | .ctorPat "Break" [.varPat r],
        .mk (.earlyReturn (.mk (.app "from_residual" [.mk (.var r') rTy]) fTy)) bTy =>
      if r == r' then some (r, rTy, fTy, bTy) else none
    | _, _ => none
  let (q, b) ← arms.findSome? fun (p, b) =>
    match p with
    | .ctorPat "Continue" [q] => some (q, b)
    | _ => none
  match k with
  | .option =>
    pure (.match_ c [(.somePat q, b),
      (.nonePat, .mk (.earlyReturn (.mk (.app "None" []) fTy)) bTy)])
  | .result convert =>
    let e : TExpr := .mk (.var r) ((resultErrTy? rTy).getD .unknown)
    let err : TExpr :=
      if convert then .mk (.app "from" [e]) ((resultErrTy? fTy).getD .unknown) else e
    pure (.match_ c [(.okPat q, b),
      (.errPat (.varPat r), .mk (.earlyReturn (.mk (.app "Err" [err]) fTy)) bTy)])

/-- `isEarlyExitMatch` on `TExpr`. -/
def tIsEarlyExitMatch : TExpr → Bool
  | .mk (.match_ _ arms) _ => arms.any fun (_, b) => (b.kind matches .earlyReturn _)
  | _ => false

/-- `peelTryLets` on `TExpr`. -/
def tPeelTryLets : TExpr → List (String × TExpr) × TExpr
  | .mk (.letBind n v b) ty =>
    if n.startsWith tryBindPrefix then
      let (bs, e) := tPeelTryLets b
      ((n, v) :: bs, e)
    else ([], .mk (.letBind n v b) ty)
  | e => ([], e)

/-- `wrapTryLets` on `TExpr`: each `let` has the type of `e`. -/
def tWrapTryLets (bs : List (String × TExpr)) (e : TExpr) : TExpr :=
  bs.foldr (fun (n, v) acc => .mk (.letBind n v acc) e.ty) e

/-- `floatEarlyExitArgs` on `TExpr`, for an application of type `ty`. -/
def tFloatEarlyExitArgs (f : String) (args : List TExpr) (ty : ImpType) : TExpr :=
  let peeled := args.map tPeelTryLets
  let lifted := peeled.zipIdx.filter fun ((bs, a), _) => !bs.isEmpty || tIsEarlyExitMatch a
  match lifted.getLast? with
  | none => .mk (.app f args) ty
  | some (_, last) =>
    let avoid0 := freeVars (TExpr.mk (.app f args) ty).erase ++
      peeled.flatMap fun (bs, _) => bs.map (·.1)
    let step (acc : List (String × TExpr) × List TExpr × List String)
        (x : (List (String × TExpr) × TExpr) × Nat) :
        List (String × TExpr) × List TExpr × List String :=
      let (binds, out, avoid) := acc
      let ((bs, a), i) := x
      if i > last then (binds, out ++ [a], avoid)
      else
        let binds := binds ++ bs
        let prefixedVar := match a.kind with
          | .var v => v.startsWith tryBindPrefix
          | _ => false
        if tIsEarlyExitMatch a || (i < last && (!isAtomicArg a.erase || prefixedVar)) then
          let base := match a.kind with
            | .match_ (.mk (.var v) _) _ => s!"{tryBindPrefix}{v}"
            | _ => s!"{tryBindPrefix}arg{i}"
          let n := freshTryName avoid base
          (binds ++ [(n, a)], out ++ [.mk (.var n) a.ty], n :: avoid)
        else (binds, out ++ [a], avoid)
    let (binds, out, _) := peeled.zipIdx.foldl step ([], [], avoid0)
    tWrapTryLets binds (.mk (.app f out) ty)

/-- The term `mk xs` of type `ty` built from the operands `xs`, with the
    early-exit operands bound in front of it in their order of evaluation, as
    `tFloatEarlyExitArgs` binds the arguments of an application: the operands of
    an operator, a constructor, a projection, a borrow or a condition. -/
def tFloatEarlyExitOperands (xs : List TExpr) (ty : ImpType)
    (mk : List TExpr → TExprKind) : TExpr :=
  let (bs, e) := tPeelTryLets (tFloatEarlyExitArgs "" xs ty)
  match e.kind with
  | .app _ out => tWrapTryLets bs (.mk (mk out) ty)
  | _ => .mk (mk xs) ty

/-- Whether a term holds an early exit in evaluation position: it is an early-exit
    `match` (`tIsEarlyExitMatch`) or has `let`s with the prefix `tryBindPrefix` at
    its head. -/
def tHasEarlyExit (e : TExpr) : Bool :=
  tIsEarlyExitMatch e || !(tPeelTryLets e).1.isEmpty

/-- `readMatch` on `TExpr`, for a `match` of type `ty`: the operand of a `?` is
    read from the type of `branch(c)` and the type of `from_residual(r)`. -/
def tReadMatch (scrut : TExpr) (arms : List (ImpPat × TExpr)) (ty : ImpType) : TExpr :=
  let (bs, s) := tPeelTryLets scrut
  let armVars := arms.flatMap fun (_, b) => freeVars b.erase
  let retTy : ImpType := (arms.findSome? fun (_, b) =>
    match b with
    | .mk (.earlyReturn (.mk (.app "from_residual" _) fTy)) _ => some fTy
    | _ => none).getD .unknown
  let tryForm? : Option TExprKind := match s.kind with
    | .app "branch" [c] => (tryOperandOf? s.ty retTy).bind fun k => tTryMatch? k c arms
    | _ => none
  let m : TExpr := .mk (tryForm?.getD (.match_ s arms)) ty
  if bs.isEmpty then .mk (tryForm?.getD (.match_ scrut arms)) ty
  else if bs.any (fun (n, _) => armVars.contains n) then .mk (.match_ scrut arms) ty
  else tWrapTryLets bs m

open Hax.JsonSize

/-! ### `parseHaxExpr` and friends (mutually recursive on JSON sub-tree). -/

mutual

/-- Map hax's `Decorated<ExprKind>` JSON to our `ImpExpr`.
    Strips metadata (span, hir_id, attributes), keeping only the expression and type. -/
def parseHaxExpr (j : Json) : Except String ImpExpr := do
  match h_c : j.getObjVal? "contents" with
  | .ok contents => parseExprKind j contents
  | .error e => throw e
termination_by jsonSize j
decreasing_by exact getObjVal?_decreases h_c

/-- Parse a hax ExprKind (externally tagged enum).
    `outerJ` is the full Decorated expression (for extracting `ty`).
    `j` is the `contents` (ExprKind). -/
def parseExprKind (outerJ j : Json) : Except String ImpExpr := do
  -- Unit variants come as plain strings
  match j.getStr? with
  | .ok "Todo" => return .app "hax_unsupported_Todo" []  -- will cause Lean compile error
  | _ => pure ()

  -- Struct variants: {"VariantName": {fields...}}
  match h_VarRef : j.getObjVal? "VarRef" with
  | .ok data =>
    let name := match data.getObjVal? "id" with
      | .ok id => extractLocalIdentName id
      | _ => "unknown_var"
    return .var name
  | .error _ =>
  -- UpvarRef: a closure-captured variable. Structure:
  -- `{"UpvarRef": {"var_hir_id": {"name": "x", "id": ...}}}`.
  -- The OCaml `cargo hax into lean` backend treats this identically
  -- to `VarRef` — the captured variable is lexically in scope at the
  -- closure body's emission point, so a plain `.var name` reference
  -- resolves correctly (see Libcrux_specs_hax aes128_gcm_encrypt:
  -- `(fun block => Libcrux_specs_hax.Aes.aes128_encrypt k block)`
  -- where `k` is the captured `let k := *key`).
  match h_UpvarRef : j.getObjVal? "UpvarRef" with
  | .ok data =>
    let name := match data.getObjVal? "var_hir_id" with
      | .ok h => extractLocalIdentName h
      | _ => "unknown_upvar"
    return .var name
  | .error _ =>
  match h_GlobalName : j.getObjVal? "GlobalName" with
  | .ok data =>
    let name := match data.getObjVal? "item" with
      | .ok item => extractItemDefIdName item "global"
      | _ => "global"
    return .var name
  | .error _ =>
  match h_Literal : j.getObjVal? "Literal" with
  | .ok data => return parseLiteral data
  | .error _ =>
  match h_If : j.getObjVal? "If" with
  | .ok data =>
    match h_If_cond : data.getObjVal? "cond" with
    | .ok condJ =>
      let cond ← parseHaxExpr condJ
      match h_If_then : data.getObjVal? "then" with
      | .ok thnJ =>
        let thn ← parseHaxExpr thnJ
        let els ← match h_If_else : data.getObjVal? "else_opt" with
          | .ok (.null) => pure .unitVal
          | .ok elsJ => parseHaxExpr elsJ
          | _ => pure .unitVal
        return .ifThenElse cond thn els
      | .error e => throw e
    | .error e => throw e
  | .error _ =>
  match h_Call : j.getObjVal? "Call" with
  | .ok data =>
    let funName := match data.getObjVal? "fun" with
      | .ok fj => extractCallName fj
      | _ => "unknown_fn"
    match h_Call_args : data.getObjValAs? (Array Json) "args" with
    | .ok argsJ =>
      let args ← argsJ.toList.attach.mapM (fun ⟨a, ha⟩ => parseHaxExpr a)
      return floatEarlyExitArgs funName args
    | .error e => throw e
  | .error _ =>
  match h_Let : j.getObjVal? "Let" with
  | .ok data =>
    match h_Let_expr : data.getObjVal? "expr" with
    | .ok rhsJ =>
      let rhs ← parseHaxExpr rhsJ
      let pat := match data.getObjVal? "pat" with
        | .ok p => parseHaxPat p
        | _ => .wildcard
      -- Handle tuple destructuring: let (a, b) = rhs → let _tup := rhs; let a := _tup.1; let b := _tup.2
      match pat with
      | .tuplePat pats =>
        let tmpName := "_tup"
        let bindings := tupleDestructBinds tmpName pats 0
        let inner := bindings.foldr (fun (n, proj) acc => .letBind n proj acc) .unitVal
        return .letBind tmpName rhs inner
      | .varPat n =>
        return .letBind n rhs .unitVal
      | _ =>
        -- Struct destructuring: let S { x, .. } = rhs → let _st := rhs; let x := _st.x
        match data.getObjVal? "pat" |>.toOption |>.bind structPatFields? with
        | some fields =>
          let bindings := structDestructBinds "_st" fields
          let inner := bindings.foldr (fun (n, proj) acc => .letBind n proj acc) .unitVal
          return .letBind "_st" rhs inner
        | none =>
          return .letBind "_let" rhs .unitVal
    | .error e => throw e
  | .error _ =>
  match h_Block : j.getObjVal? "Block" with
  | .ok data =>
    -- Block: {stmts: [...], expr: Option<Expr>, ...}
    -- #[serde(flatten)] means Block fields are inlined into the ExprKind
    let stmts ← match h_Block_stmts : data.getObjValAs? (Array Json) "stmts" with
      | .ok ss => ss.toList.attach.mapM (fun ⟨s, hs⟩ => parseStmt s)
      | _ => pure []
    let tail ← match h_Block_expr : data.getObjVal? "expr" with
      | .ok (.null) => pure .unitVal
      | .ok e => parseHaxExpr e
      | _ => pure .unitVal
    return stmtsToSeq stmts tail
  | .error _ =>
  match h_Match : j.getObjVal? "Match" with
  | .ok data =>
    match h_Match_scrut : data.getObjVal? "scrutinee" with
    | .ok scrutJ =>
      let scrut ← parseHaxExpr scrutJ
      match h_Match_arms : data.getObjValAs? (Array Json) "arms" with
      | .ok armsJ =>
        let arms ← armsJ.toList.attach.mapM (fun ⟨a, ha⟩ => parseArm a)
        let scrutTy := match scrutJ.getObjVal? "ty" with
          | .ok t => parseHaxType t
          | .error _ => .unknown
        return readMatch scrut scrutTy armsJ.toList arms
      | .error e => throw e
    | .error e => throw e
  | .error _ =>
  match h_Tuple : j.getObjVal? "Tuple" with
  | .ok data =>
    match h_Tuple_fields : data.getObjValAs? (Array Json) "fields" with
    | .ok fieldsJ =>
      let fields ← fieldsJ.toList.attach.mapM (fun ⟨f, hf⟩ => parseHaxExpr f)
      if fields.isEmpty then return .unitVal
      return .tuple fields
    | .error e => throw e
  | .error _ =>
  match h_Array : j.getObjVal? "Array" with
  | .ok data =>
    match h_Array_fields : data.getObjValAs? (Array Json) "fields" with
    | .ok fieldsJ =>
      let fields ← fieldsJ.toList.attach.mapM (fun ⟨f, hf⟩ => parseHaxExpr f)
      return .app "array_lit" fields
    | .error e => throw e
  | .error _ =>
  match h_Assign : j.getObjVal? "Assign" with
  | .ok data =>
    match h_Assign_lhs : data.getObjVal? "lhs" with
    | .ok lhsJ =>
      let lhs ← parseHaxExpr lhsJ
      match h_Assign_rhs : data.getObjVal? "rhs" with
      | .ok rhsJ =>
        let rhs ← parseHaxExpr rhsJ
        -- Strip deref wrappers from LHS (references erased by dropReferences)
        let rec stripD : ImpExpr → ImpExpr
          | .deref e => stripD e
          | e => e
        let lhs' : ImpExpr := stripD lhs
        let getVarName : ImpExpr → String
          | .var n => n
          | .deref (.var n) => n
          | _ => "_assign"
        -- `index` and `index_mut` are both element-access on the LHS of an
        -- assignment (the latter from a `&mut`-indexed target, e.g. `arr[i] = v`
        -- where `arr` is `&mut`). Normalise both to the same writeback form.
        let isIndex (f : String) : Bool := f == "index" || f == "index_mut"
        match lhs' with
        | .var n => return .assign n rhs
        -- Nested array element assignment: arr[i][j] = v
        -- → assign arr (array_update arr i (array_update (index arr i) j v))
        | .app outer [.app inner [outerArr, outerIdx], innerIdx] =>
          if isIndex outer && isIndex inner then
            let outerName := getVarName (stripD outerArr)
            let innerUpdate := ImpExpr.app "array_update"
              [.app "index" [outerArr, outerIdx], innerIdx, rhs]
            return .assign outerName (.app "array_update" [outerArr, outerIdx, innerUpdate])
          else return .assign "_assign" rhs
        -- Array element assignment: arr[i] = v → assign arr (array_update arr i v)
        | .app f [arr, idx] =>
          if isIndex f then
            let arrName := getVarName (stripD arr)
            return .assign arrName (.app "array_update" [arr, idx, rhs])
          else return .assign "_assign" rhs
        | _ => return .assign "_assign" rhs
      | .error e => throw e
    | .error e => throw e
  | .error _ =>
  match h_AssignOp : j.getObjVal? "AssignOp" with
  | .ok data =>
    let rawOp := match data.getObjVal? "op" with
      | .ok opJ => binOpName opJ
      | _ => "op"
    -- Strip "Assign" suffix to get base op (BitXorAssign → BitXor)
    let op := if rawOp.endsWith "Assign" then (rawOp.dropEnd 6).toString else rawOp
    match h_AO_lhs : data.getObjVal? "lhs" with
    | .ok lhsJ =>
      let lhs ← parseHaxExpr lhsJ
      match h_AO_rhs : data.getObjVal? "rhs" with
      | .ok rhsJ =>
        let rhs ← parseHaxExpr rhsJ
        -- Strip deref wrappers from LHS
        let rec stripD2 : ImpExpr → ImpExpr
          | .deref e => stripD2 e
          | e => e
        let lhs' : ImpExpr := stripD2 lhs
        -- `index` / `index_mut` both denote element access; a `&mut`-indexed
        -- compound-assign target (`arr[i] op= v`) arrives as `index_mut`.
        let isIndexOp (f : String) : Bool := f == "index" || f == "index_mut"
        match lhs' with
        | .var n => return .assign n (.app op [lhs, rhs])
        | .app f [arr, idx] =>
          if isIndexOp f then
            -- arr[i] op= v → assign arr (array_update arr idx (op(arr[i], v)))
            -- The element-read inside `op` uses plain `index` (the rendered
            -- `index_mut` would otherwise force a monomorphic element type).
            let arrName := match stripD2 arr with
              | .var n => n | .deref (.var n) => n | _ => "_assign"
            let elemRead := ImpExpr.app "index" [arr, idx]
            return .assign arrName (.app "array_update" [arr, idx, .app op [elemRead, rhs]])
          else return .assign "_assign" (.app op [lhs, rhs])
        | _ => return .assign "_assign" (.app op [lhs, rhs])
      | .error e => throw e
    | .error e => throw e
  | .error _ =>
  match h_Borrow : j.getObjVal? "Borrow" with
  | .ok data =>
    match h_Borrow_arg : data.getObjVal? "arg" with
    | .ok argJ =>
      let arg ← parseHaxExpr argJ
      return .borrow arg
    | .error e => throw e
  | .error _ =>
  match h_Deref : j.getObjVal? "Deref" with
  | .ok data =>
    match h_Deref_arg : data.getObjVal? "arg" with
    | .ok argJ =>
      let arg ← parseHaxExpr argJ
      return .deref arg
    | .error e => throw e
  | .error _ =>
  match h_Loop : j.getObjVal? "Loop" with
  | .ok data =>
    match h_Loop_body : data.getObjVal? "body" with
    | .ok bodyJ =>
      let body ← parseHaxExpr bodyJ
      -- hax Loop is a general loop (while true), not a for-range
      return .whileLoop (.lit (.bool true)) body
    | .error e => throw e
  | .error _ =>
  match h_Break : j.getObjVal? "Break" with
  | .ok data =>
    let value ← match h_Break_v : data.getObjVal? "value" with
      | .ok (.null) => pure none
      | .ok v => return .break_ (some (← parseHaxExpr v))
      | _ => pure none
    return .break_ value
  | .error _ =>
  match h_Continue : j.getObjVal? "Continue" with
  | .ok _data => return .continue_
  | .error _ =>
  match h_Return : j.getObjVal? "Return" with
  | .ok data =>
    let value ← match h_Return_v : data.getObjVal? "value" with
      | .ok (.null) => pure .unitVal
      | .ok v => parseHaxExpr v
      | _ => pure .unitVal
    return .earlyReturn value
  | .error _ =>
  match h_Binary : j.getObjVal? "Binary" with
  | .ok data =>
    let op := match data.getObjVal? "op" with
      | .ok opJ => binOpName opJ
      | _ => "binop"
    match h_Bin_lhs : data.getObjVal? "lhs" with
    | .ok lhsJ =>
      let lhs ← parseHaxExpr lhsJ
      match h_Bin_rhs : data.getObjVal? "rhs" with
      | .ok rhsJ =>
        let rhs ← parseHaxExpr rhsJ
        -- Annotate width-sensitive ops with the bit width of the lhs operand
        let opAnnotated := annotateOpWidth op (extractExprWidth lhsJ)
        return .app opAnnotated [lhs, rhs]
      | .error e => throw e
    | .error e => throw e
  | .error _ =>
  match h_Logical : j.getObjVal? "LogicalOp" with
  | .ok data =>
    let op := match data.getObjVal? "op" with
      | .ok (.str "And") => "&&"
      | .ok (.str "Or") => "||"
      | _ => "logical_op"
    match h_LO_lhs : data.getObjVal? "lhs" with
    | .ok lhsJ =>
      let lhs ← parseHaxExpr lhsJ
      match h_LO_rhs : data.getObjVal? "rhs" with
      | .ok rhsJ =>
        let rhs ← parseHaxExpr rhsJ
        return .app op [lhs, rhs]
      | .error e => throw e
    | .error e => throw e
  | .error _ =>
  match h_Unary : j.getObjVal? "Unary" with
  | .ok data =>
    let op := match data.getObjVal? "op" with
      | .ok opJ => unOpName opJ
      | _ => "unop"
    match h_Un_arg : data.getObjVal? "arg" with
    | .ok argJ =>
      let arg ← parseHaxExpr argJ
      let opAnnotated := annotateOpWidth op (extractExprWidth argJ)
      return .app opAnnotated [arg]
    | .error e => throw e
  | .error _ =>
  match h_Field : j.getObjVal? "Field" with
  | .ok data =>
    match h_Field_lhs : data.getObjVal? "lhs" with
    | .ok lhsJ =>
      let lhs ← parseHaxExpr lhsJ
      let fieldName := match data.getObjVal? "field" with
        | .ok fj => extractDefIdName fj
        | _ => "field"
      return .app ("." ++ fieldName) [lhs]
    | .error e => throw e
  | .error _ =>
  match h_TF : j.getObjVal? "TupleField" with
  | .ok data =>
    match h_TF_lhs : data.getObjVal? "lhs" with
    | .ok lhsJ =>
      let lhs ← parseHaxExpr lhsJ
      let idx := match data.getObjValAs? Nat "field" with
        | .ok n => n
        | _ => 0
      return .proj lhs idx
    | .error e => throw e
  | .error _ =>
  match h_Index : j.getObjVal? "Index" with
  | .ok data =>
    match h_Idx_lhs : data.getObjVal? "lhs" with
    | .ok lhsJ =>
      let lhs ← parseHaxExpr lhsJ
      match h_Idx_idx : data.getObjVal? "index" with
      | .ok indexJ =>
        let index ← parseHaxExpr indexJ
        return .app "index" [lhs, index]
      | .error e => throw e
    | .error e => throw e
  | .error _ =>
  match h_Cast : j.getObjVal? "Cast" with
  | .ok data =>
    -- Cast: annotate with the cast tag of the source type and the outer
    -- expression's ty (the target type), e.g. `x as u8` → app "cast#8" [x],
    -- `x as i32` → app "cast#i32" [x], `(x : i64) as u64` → app "cast#u64" [x].
    match h_Cast_src : data.getObjVal? "source" with
    | .ok srcJ =>
      let source ← parseHaxExpr srcJ
      let targetWidth := extractCastTag srcJ outerJ
      match targetWidth with
      | some w => return .app s!"cast#{w}" [source]
      | none => return .app "cast" [source]
    | .error e => throw e
  | .error _ =>
  match h_Use : j.getObjVal? "Use" with
  | .ok data =>
    match h_Use_src : data.getObjVal? "source" with
    | .ok srcJ => parseHaxExpr srcJ
    | .error e => throw e
  | .error _ =>
  match h_NTA : j.getObjVal? "NeverToAny" with
  | .ok data =>
    match h_NTA_src : data.getObjVal? "source" with
    | .ok srcJ => parseHaxExpr srcJ
    | .error e => throw e
  | .error _ =>
  match h_Box : j.getObjVal? "Box" with
  | .ok data =>
    match h_Box_v : data.getObjVal? "value" with
    | .ok vJ => parseHaxExpr vJ
    | .error e => throw e
  | .error _ =>
  match h_Adt : j.getObjVal? "Adt" with
  | .ok data => parseAdtExpr data
  | .error _ =>
  match h_Closure : j.getObjVal? "Closure" with
  | .ok data =>
    -- A closure with named parameters is a `.lam`; the capture list is not kept.
    match h_Cl_body : data.getObjVal? "body" with
    | .ok bodyJ =>
      let body ← parseHaxExpr bodyJ
      match closureParams? data with
      | some names => pure (.lam names body)
      | none => pure body
    | .error e => throw e
  | .error _ =>
  match h_Repeat : j.getObjVal? "Repeat" with
  | .ok data =>
    match h_Rpt_v : data.getObjVal? "value" with
    | .ok vJ =>
      let value ← parseHaxExpr vJ
      let count ← match h_Rpt_c : data.getObjVal? "count" with
        | .ok countJ => parseHaxExpr countJ
        | _ => pure (.lit (.int 0))
      return .app "repeat" [value, count]
    | .error e => throw e
  | .error _ =>
  match h_PTA : j.getObjVal? "PlaceTypeAscription" with
  | .ok data =>
    match h_PTA_src : data.getObjVal? "source" with
    | .ok srcJ => parseHaxExpr srcJ
    | .error e => throw e
  | .error _ =>
  match h_VTA : j.getObjVal? "ValueTypeAscription" with
  | .ok data =>
    match h_VTA_src : data.getObjVal? "source" with
    | .ok srcJ => parseHaxExpr srcJ
    | .error e => throw e
  | .error _ =>
  match h_PC : j.getObjVal? "PointerCoercion" with
  | .ok data =>
    match h_PC_src : data.getObjVal? "source" with
    | .ok srcJ => parseHaxExpr srcJ
    | .error e => throw e
  | .error _ =>
  match h_CB : j.getObjVal? "ConstBlock" with
  | .ok _data => return .app "const_block" []
  | .error _ =>
  match h_NC : j.getObjVal? "NamedConst" with
  | .ok data =>
    let name := match data.getObjVal? "item" with
      | .ok item => extractItemDefIdName item "const"
      | _ => "const"
    return .var name
  | .error _ =>
  match h_CP : j.getObjVal? "ConstParam" with
  | .ok _data => return .var "const_param"
  | .error _ =>
  match h_CR : j.getObjVal? "ConstRef" with
  | .ok data =>
    let name := match data.getObjVal? "id" with
      | .ok id => match id.getObjValAs? String "name" with
        | .ok n => n
        | _ => "const_ref"
      | _ => "const_ref"
    return .var name
  | .error _ =>
  match h_SR : j.getObjVal? "StaticRef" with
  | .ok data =>
    let name := match data.getObjVal? "def_id" with
      | .ok defId => extractDefIdName defId
      | _ => "static"
    return .var name
  | .error _ =>
  match h_Yield : j.getObjVal? "Yield" with
  | .ok data =>
    match h_Yield_v : data.getObjVal? "value" with
    | .ok vJ =>
      let value ← parseHaxExpr vJ
      return .app "yield" [value]
    | .error e => throw e
  | .error _ =>
  match h_Todo : j.getObjVal? "Todo" with
  | .ok s =>
    let msg := match s with
      | .str m => m
      | _ => "todo"
    return .app ("todo:" ++ msg) []
  | .error _ =>
    throw s!"unknown hax ExprKind: {j.pretty}"
termination_by jsonSize j
decreasing_by
  all_goals first
    | exact getObjVal?_chain_decreases ‹_› ‹_›
    | exact getObjVal?_decreases ‹_›
    | (have ha := Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›
       exact Nat.lt_trans
         (getObjValAs?_arr_mem_decreases ‹_› ha)
         (getObjVal?_decreases ‹_›))

/-- Parse a hax Stmt (from Block). -/
def parseStmt (j : Json) : Except String ImpExpr := do
  match h_kind : j.getObjVal? "kind" with
  | .ok kind =>
    match h_Expr : kind.getObjVal? "Expr" with
    | .ok data =>
      match h_E_e : data.getObjVal? "expr" with
      | .ok e => parseHaxExpr e
      | _ => return .unitVal
    | .error _ =>
    match h_Let : kind.getObjVal? "Let" with
    | .ok data =>
      let pat := match data.getObjVal? "pattern" with
        | .ok p => parseHaxPat p
        | _ => .wildcard
      let init ← match h_init : data.getObjVal? "initializer" with
        | .ok (.null) => pure .unitVal
        | .ok e => parseHaxExpr e
        | _ => pure .unitVal
      -- The `let`s that `floatEarlyExitArgs` put at the head of the initializer
      -- go in front of the statement.
      let (tryBinds, init) := peelTryLets init
      -- Handle tuple destructuring: let (a, b) = rhs → let _tup := rhs; let a := _tup.1; let b := _tup.2
      -- Uses nested letBind so stmtsToSeq can connect the tail properly.
      let stmt : ImpExpr := match pat with
        | .tuplePat pats =>
          let tmpName := "_tup"
          let bindings := tupleDestructBinds tmpName pats 0
          let inner := bindings.foldr (fun (n, proj) acc => .letBind n proj acc) .unitVal
          .letBind tmpName init inner
        | .varPat n =>
          .letBind n init .unitVal  -- body filled in by stmtsToSeq
        | _ =>
          -- Struct destructuring: let S { x, .. } = init → let _st := init; let x := _st.x
          match data.getObjVal? "pattern" |>.toOption |>.bind structPatFields? with
          | some fields =>
            let bindings := structDestructBinds "_st" fields
            let inner := bindings.foldr (fun (n, proj) acc => .letBind n proj acc) .unitVal
            .letBind "_st" init inner
          | none =>
            .letBind "_let" init .unitVal
      return wrapTryLets tryBinds stmt
    | .error _ => return .unitVal
  | .error _ => return .unitVal
termination_by jsonSize j
decreasing_by
  all_goals first
    | (-- 3-level chain: j → kind → data → e (via h_kind, h_Let, h_init)
       exact Nat.lt_trans (getObjVal?_decreases h_init)
              (Nat.lt_trans (getObjVal?_decreases h_Let)
                            (getObjVal?_decreases h_kind)))
    | (-- 2-level chain
       exact Nat.lt_trans (getObjVal?_decreases h_E_e)
                          (Nat.lt_trans (getObjVal?_decreases h_Expr)
                                        (getObjVal?_decreases h_kind)))

/-- Parse a hax Arm (from Match). -/
def parseArm (j : Json) : Except String (ImpPat × ImpExpr) := do
  let pat := match j.getObjVal? "pattern" with
    | .ok p => parseHaxPat p
    | _ => .wildcard
  let body ← match h_body : j.getObjVal? "body" with
    | .ok b => parseHaxExpr b
    | _ => pure .unitVal
  return (pat, body)
termination_by jsonSize j
decreasing_by exact getObjVal?_decreases ‹_›

/-- Parse a hax AdtExpr (struct/enum construction). -/
def parseAdtExpr (j : Json) : Except String ImpExpr := do
  -- hax JSON: info.variant is a DefId, info.type_namespace is a DefId
  let name := match j.getObjVal? "info" with
    | .ok info => match info.getObjVal? "variant" with
      | .ok variantDefId => extractDefIdName variantDefId
      | _ => match info.getObjVal? "type_namespace" with
        | .ok nsDefId => extractDefIdName nsDefId
        | _ => match info.getObjValAs? String "variant_name" with
          | .ok n => n
          | _ => "Adt"
    | _ => "Adt"
  let fields ← match h_flds : j.getObjValAs? (Array Json) "fields" with
    | .ok fs => fs.toList.attach.mapM fun ⟨fj, hf⟩ =>
      match h_v : fj.getObjVal? "value" with
      | .ok v => parseHaxExpr v
      | _ => pure .unitVal
    | _ => pure []
  return .app name fields
termination_by jsonSize j
decreasing_by
  all_goals first
    | (have ha := Array.mem_toList_iff.mp ‹_ ∈ Array.toList _›
       exact Nat.lt_trans
         (getObjVal?_decreases ‹_›)
         (getObjValAs?_arr_mem_decreases ‹_› ha))
    | exact getObjVal?_decreases ‹_›

end -- mutual

/-! ## For-Loop Reconstruction

Hax desugars `for i in lo..hi { body }` into an iterator pattern:
```
match into_iter(Range { start: lo, end: hi }) {
  iter => loop {
    match next(&mut iter) {
      None => break,
      Some(i) => body
    }
  }
}
```

We reconstruct this back to `forLoop` / `forLoopRev` by pattern-matching
on the parsed `ImpExpr`. This mirrors the OCaml hax engine's
`phase_reconstruct_for_loops.ml`.

### Reversed ranges

`for i in (lo..hi).rev()` appears as `into_iter(rev(Range { ... }))`.
We detect `rev` in the call chain and emit `forLoopRev`. -/

/-- Check if a function name is `into_iter` (possibly qualified). -/
def isIntoIter (f : String) : Bool :=
  f == "into_iter" || f.endsWith "into_iter" ||
  f.endsWith "IntoIterator::into_iter"

/-- Check if a function name is `Iterator::next` (possibly qualified). -/
def isIterNext (f : String) : Bool :=
  f == "next" || f.endsWith "next" ||
  f.endsWith "Iterator::next" || f.endsWith "Iterator__next"

/-- Check if a function name is `rev` (possibly qualified). -/
def isRev (f : String) : Bool :=
  f == "rev" || f.endsWith "rev" || f.endsWith "Iterator::rev"

/-- Try to extract Range bounds from a constructor call.
    Hax represents `Range { start, end }` as `app "Range" [lo, hi]`
    or as `app "Range::new" [lo, hi]` or as `tuple [lo, hi]` wrapping. -/
def tryExtractRange (e : ImpExpr) : Option (ImpExpr × ImpExpr × Bool) :=
  match e with
  | .app f [lo, hi] =>
    -- The third component says whether the upper bound is inclusive
    -- (`RangeInclusive`, from `lo..=hi`).
    if f.startsWith "RangeInclusive" then some (lo, hi, true)
    else if f == "Range" || f.endsWith "Range" || f == "new" || f == "Range::new"
    then some (lo, hi, false)
    else none
  | .tuple [lo, hi] => some (lo, hi, false)  -- Range as tuple
  | _ => none

/-- Strip the "Assign" suffix from a compound op name to get the base op.
    Returns `none` if not a compound assign op. -/
def stripAssignSuffix (f : String) : Option String :=
  let pairs := [
    ("AddAssign", "Add"), ("SubAssign", "Sub"), ("MulAssign", "Mul"),
    ("DivAssign", "Div"), ("RemAssign", "Rem"),
    ("BitXorAssign", "BitXor"), ("BitOrAssign", "BitOr"), ("BitAndAssign", "BitAnd"),
    ("ShlAssign", "Shl"), ("ShrAssign", "Shr")]
  pairs.findSome? fun (cmpd, base) => if f == cmpd then some base else none

/-- Strip deref wrappers (references are erased by dropReferences phase). -/
def stripDeref : ImpExpr → ImpExpr
  | .deref e => stripDeref e
  | e => e

/-- Extract the variable name from an lvalue expression. -/
def extractLValueName : ImpExpr → String
  | .var n => n
  | .deref (.var n) => n
  | .deref (.deref (.var n)) => n
  | .app "index" (.var n :: _) => n
  | .app "index" (.deref (.var n) :: _) => n
  | .app "index" (.deref (.deref (.var n)) :: _) => n
  | _ => "_assign"

/-- Information about a recognized iterator expression. -/
inductive IterInfo where
  | range (lo hi : ImpExpr) (reversed inclusive : Bool)
  | collection (coll : ImpExpr)
  /-- An iterator over the positions of one or two collections: `c.iter_mut()`
      (`elems = [(c, true)]`), `it.enumerate()` over a collection
      (`withIndex = true`) and `a.zip(b)` (`elems = [(a, _), (b, _)]`). Each
      entry is a collection and whether its elements are mutable places
      (`iter_mut`). -/
  | positions (elems : List (ImpExpr × Bool)) (withIndex : Bool)

/-- Whether a function name is `iter_mut` (possibly qualified). -/
def isIterMut (f : String) : Bool := f == "iter_mut" || f.endsWith "::iter_mut"

/-- Whether a function name is `enumerate` (possibly qualified). -/
def isEnumerate (f : String) : Bool := f == "enumerate" || f.endsWith "::enumerate"

/-- Whether a function name is `zip` (possibly qualified). -/
def isZip (f : String) : Bool := f == "zip" || f.endsWith "::zip"

/-- The collection an iterator expression walks and whether its elements are
    mutable places: `c` for `c.iter()`, `c.iter_mut()` (mutable) and
    `c.into_iter()`, and the expression itself otherwise. -/
def iterCollection : ImpExpr → ImpExpr × Bool
  | e@(.app g [c]) =>
    if isIterMut g then (c, true)
    else if g == "iter" || g.endsWith "::iter" || isIntoIter g then (c, false)
    else (e, false)
  | e => (e, false)

/-- The `positions` iterator of `c.iter_mut()`, `it.enumerate()` and `a.zip(b)`
    under `into_iter`, and `none` for every other argument of `into_iter`. The
    walked iterators are collections: `enumerate` or `zip` over a nested
    `enumerate`, `zip`, `rev` or stepped iterator is `none`. -/
def tryExtractPositions (arg : ImpExpr) : Option IterInfo :=
  let plain (e : ImpExpr) : Bool := match e with
    | .app g _ => !(isEnumerate g || isZip g || isRev g || g == "step_by"
        || g.endsWith "::step_by")
    | _ => true
  match arg with
  | .app g [inner] =>
    if isIterMut g then some (.positions [(inner, true)] false)
    else if isEnumerate g then
      let (c, m) := iterCollection inner
      if plain c then some (.positions [(c, m)] true) else none
    else none
  | .app g [x, y] =>
    if isZip g then
      let (a, ma) := iterCollection x
      let (b, mb) := iterCollection y
      if plain a && plain b then some (.positions [(a, ma), (b, mb)] false) else none
    else none
  | _ => none

/-- Try to extract iterator info from the scrutinee of the outer match.
    Recognizes: `into_iter(Range(lo, hi))` and `into_iter(rev(Range(lo, hi)))`. -/
def tryExtractIterator (e : ImpExpr) : Option IterInfo :=
  match e with
  | .app f [arg] =>
    if isIntoIter f then
      -- Direct range: into_iter(Range(lo, hi))
      match tryExtractRange arg with
      | some (lo, hi, incl) => some (.range lo hi false incl)
      | none =>
      match tryExtractPositions arg with
      | some info => some info
      | none =>
        -- Reversed range: into_iter(rev(Range(lo, hi)))
        match arg with
        | .app g [inner] =>
          if isRev g then
            match tryExtractRange inner with
            | some (lo, hi, incl) => some (.range lo hi true incl)
            | none => none
          -- iter(collection) wrapped in into_iter
          else if g == "iter" || g.endsWith "iter" then
            some (.collection inner)
          else
            -- Bare collection: into_iter(collection)
            some (.collection arg)
        | _ =>
          -- Bare collection (variable or other expr): into_iter(collection)
          some (.collection arg)
    else if isRev f then
      -- rev(into_iter(Range(lo, hi)))
      match e with
      | .app _ [.app g [inner]] =>
        if isIntoIter g then
          match tryExtractRange inner with
          | some (lo, hi, incl) => some (.range lo hi true incl)
          | none => none
        else none
      | _ => none
    else none
  | _ => none

/-- Try to extract the element pattern and body from the inner match on `next()`.
    Pattern: `match next(&mut iter) { None => break, Some(p) => body }`, with `p`
    a variable, `_` or a tuple pattern (`Some((i, x))` of `enumerate` and
    `zip`); a `&b` pattern arrives as `b` (`parseHaxPat` unwraps `Deref`). A
    bare binding arm `v => body` gives the pattern `v`. -/
def tryExtractNextMatchPat (innerBody : ImpExpr) (iterVar : String) :
    Option (ImpPat × ImpExpr) :=
  -- The inner body may be wrapped in seq, letBind, or be a direct match
  match innerBody with
  | .match_ scrut arms =>
    -- Check scrutinee calls next on the iterator
    let isNext := match scrut with
      | .app f _ => isIterNext f
      | _ => false
    if !isNext then none
    else
      -- Look for None → break, Some(p) → body pattern
      -- The arms may be in either order
      let findSome := arms.findSome? fun (pat, body) =>
        match pat with
        | .somePat (.varPat v) => some (.varPat v, body)
        | .somePat .wildcard => some (.varPat "_iter_unused", body)
        | .somePat (.tuplePat ps) => some (.tuplePat ps, body)
        | .varPat v =>
          -- Sometimes hax uses a binding pattern for Some
          -- Check if there's a destructure in the body
          some (.varPat v, body)
        | _ => none
      let hasBreak := arms.any fun (pat, body) =>
        match pat with
        | .nonePat | .wildcard => match body with
          | .break_ _ => true
          | _ => false
        | _ => false
      match findSome, hasBreak with
      | some r, true => some r
      | _, _ => none
  -- Wrapped in letBind: let _ = match ... ; rest
  | .letBind _ inner rest =>
    match tryExtractNextMatchPat inner iterVar with
    | some r => some r
    | none => tryExtractNextMatchPat rest iterVar
  | .seq e1 e2 =>
    match tryExtractNextMatchPat e1 iterVar with
    | some r => some r
    | none => tryExtractNextMatchPat e2 iterVar
  | _ => none

/-- Try to extract the loop variable and body from the inner match on `next()`:
    `tryExtractNextMatchPat` when the element pattern is a variable. -/
def tryExtractNextMatch (innerBody : ImpExpr) (iterVar : String) :
    Option (String × ImpExpr) :=
  match tryExtractNextMatchPat innerBody iterVar with
  | some (.varPat v, body) => some (v, body)
  | _ => none

/-- The variable an element pattern of a `positions` loop binds: `some (some v)`
    for `v`, `some none` for `_`, and `none` for any other pattern. -/
def elemPatVar : ImpPat → Option (Option String)
  | .varPat v => some (if v == "_iter_unused" then none else some v)
  | .wildcard => some none
  | _ => none

/-- The per-element patterns of a `positions` iterator: the counter pattern
    (`enumerate` only) and one pattern per collection, each a variable or `_`.
    `none` when the pattern has another shape. -/
def positionsPats (elems : List (ImpExpr × Bool)) (withIndex : Bool) (p : ImpPat) :
    Option (Option (Option String) × List (Option String)) :=
  match withIndex, elems, p with
  | true, [_], .tuplePat [pi, pe] => do
    let i ← elemPatVar pi
    let e ← elemPatVar pe
    pure (some i, [e])
  | false, [_], pe => do
    let e ← elemPatVar pe
    pure (none, [e])
  | false, [_, _], .tuplePat [pa, pb] => do
    let a ← elemPatVar pa
    let b ← elemPatVar pb
    pure (none, [a, b])
  | _, _, _ => none

/-- The write-back `a := array_update a idx x` of the element variable `x` of an
    `iter_mut` loop to position `idx` of the collection variable `a`. -/
def iterMutStore (x a idx : String) : ImpExpr :=
  .assign a (.app "array_update" [.var a, .var idx, .var x])

/-- The body `e` of an `iter_mut` loop with every write of the element variable
    `x` followed by its write-back `a := array_update a idx x` to position `idx`
    of the collection variable `a`. A write is an `assign x _` or a compound
    assignment call `XAssign` whose target is `x`. The walk stops below a
    binder that rebinds `x` (a `let`, a loop counter, a closure parameter). -/
partial def iterMutWriteBack (x a idx : String) : ImpExpr → ImpExpr
  | .assign n rhs =>
    let rhs' := iterMutWriteBack x a idx rhs
    if n == x then .seq (.assign n rhs') (iterMutStore x a idx)
    else .assign n rhs'
  | .app f [t, v] =>
    let e' := ImpExpr.app f [iterMutWriteBack x a idx t, iterMutWriteBack x a idx v]
    if (stripAssignSuffix f).isSome && extractLValueName t == x then
      .seq e' (iterMutStore x a idx)
    else e'
  | .app f args => .app f (args.map (iterMutWriteBack x a idx))
  | .letBind n v b =>
    .letBind n (iterMutWriteBack x a idx v) (if n == x then b else iterMutWriteBack x a idx b)
  | .lam ps b => if ps.contains x then .lam ps b else .lam ps (iterMutWriteBack x a idx b)
  | .tuple es => .tuple (es.map (iterMutWriteBack x a idx))
  | .proj e i => .proj (iterMutWriteBack x a idx e) i
  | .ifThenElse c t e =>
    .ifThenElse (iterMutWriteBack x a idx c) (iterMutWriteBack x a idx t)
      (iterMutWriteBack x a idx e)
  | .match_ s arms =>
    .match_ (iterMutWriteBack x a idx s) (arms.map fun (p, e) => (p, iterMutWriteBack x a idx e))
  | .seq e1 e2 => .seq (iterMutWriteBack x a idx e1) (iterMutWriteBack x a idx e2)
  | .borrow e => .borrow (iterMutWriteBack x a idx e)
  | .deref e => .deref (iterMutWriteBack x a idx e)
  | .forLoop v lo hi b => .forLoop v (iterMutWriteBack x a idx lo) (iterMutWriteBack x a idx hi)
      (if v == x then b else iterMutWriteBack x a idx b)
  | .forLoopRev v lo hi b => .forLoopRev v (iterMutWriteBack x a idx lo)
      (iterMutWriteBack x a idx hi) (if v == x then b else iterMutWriteBack x a idx b)
  | .whileLoop c b => .whileLoop (iterMutWriteBack x a idx c) (iterMutWriteBack x a idx b)
  | .break_ (some e) => .break_ (some (iterMutWriteBack x a idx e))
  | .earlyReturn e => .earlyReturn (iterMutWriteBack x a idx e)
  | .questionMark e => .questionMark (iterMutWriteBack x a idx e)
  | .typeAscription e ty => .typeAscription (iterMutWriteBack x a idx e) ty
  | e => e

/-- The collection variable of an `iter_mut` place: `a` for `a`, `&mut a` and
    `*a`, and `none` for any other place. -/
def iterMutRoot : ImpExpr → Option String
  | .var n => some n
  | .borrow e => iterMutRoot e
  | .deref e => iterMutRoot e
  | _ => none

/-- The counted loop of a `positions` iterator over `elems` with body `body`
    and element pattern `p`: the loop runs its counter over `0..len` (`min` of
    the two lengths for `zip`, as `Iterator::zip` stops at the shorter one),
    binds the `enumerate` counter pattern to the counter, and each element
    variable to `index c counter`. The counter is the `enumerate` variable when
    there is one, `_ci_x` for an `iter_mut` element `x` and `_ci` otherwise. An
    `iter_mut` element whose collection is a variable `a` is written back to
    position `counter` of `a` after each write (`iterMutWriteBack`). `none` when
    the pattern does not fit, or an `iter_mut` collection is not a variable. -/
def positionsLoop (elems : List (ImpExpr × Bool)) (withIndex : Bool) (p : ImpPat)
    (body : ImpExpr) : Option ImpExpr := do
  let (ip, eps) ← positionsPats elems withIndex p
  let pairs := elems.zip eps
  let mutVar := pairs.findSome? fun ((_, m), v) => if m then v else none
  let idx := match ip with
    | some (some i) => i
    | _ => match mutVar with
      | some x => "_ci_" ++ x
      | none => "_ci"
  -- Mutable elements need a variable collection root.
  let mutRoots ← pairs.filterMapM fun ((c, m), v) =>
    if m then
      match v with
      | some x => (iterMutRoot c).map fun a => some (x, a)
      | none => some none
    else some none
  let body' := mutRoots.foldl (fun b (x, a) => iterMutWriteBack x a idx b) body
  let bound := pairs.foldr (fun ((c, _), v) b =>
    match v with
    | some x => .letBind x (.app "index" [c, .var idx]) b
    | none => b) body'
  let hi := match elems with
    | [(a, _), (b, _)] => ImpExpr.app "min" [.app "len" [a], .app "len" [b]]
    | (a, _) :: _ => .app "len" [a]
    | [] => .lit (.int 0)
  pure (.forLoop idx (.lit (.int 0)) hi bound)

/-- Reconstruct for-loops from desugared iterator patterns in a single expression.
    Recursively traverses the expression, looking for the characteristic
    `match(into_iter(Range(...))) { iter => loop { match(next(iter)) { ... } } }`
    pattern produced by Rust's for-loop desugaring. -/
partial def reconstructForLoops : ImpExpr → ImpExpr
  | .match_ scrut arms =>
    match tryExtractIterator scrut, arms with
    | some (.range lo hi reversed inclusive),
      [(.varPat _iterVar, .whileLoop (.lit (.bool true)) innerBody)] =>
      -- Found the pattern! Extract the loop var from the inner next() match
      let lo' := reconstructForLoops lo
      -- `forLoop` iterates `[lo, hi)`; an inclusive range ends one past `hi`
      -- (`inclusiveUpper`, an integer literal on a literal `hi`).
      let hi' :=
        let h := reconstructForLoops hi
        if inclusive then inclusiveUpper h else h
      match tryExtractNextMatch innerBody _iterVar with
      | some (loopVar, body) =>
        let body' := reconstructForLoops body
        if reversed then .forLoopRev loopVar lo' hi' body'
        else .forLoop loopVar lo' hi' body'
      | none =>
        -- Inner match didn't match — fall through to regular match
        .match_ (reconstructForLoops scrut) (arms.map fun (p, e) => (p, reconstructForLoops e))
    | some (.collection coll),
      [(.varPat _iterVar, .whileLoop (.lit (.bool true)) innerBody)] =>
      -- Collection iteration: for elem in collection
      -- → forLoop "_i" 0 (len collection) (let elem := index collection _i; body)
      let coll' := reconstructForLoops coll
      match tryExtractNextMatch innerBody _iterVar with
      | some (loopVar, body) =>
        let body' := reconstructForLoops body
        let idxVar := "_ci"
        let loopBody := .letBind loopVar (.app "index" [coll', .var idxVar]) body'
        .forLoop idxVar (.lit (.int 0)) (.app "len" [coll']) loopBody
      | none =>
        .match_ (reconstructForLoops scrut) (arms.map fun (p, e) => (p, reconstructForLoops e))
    | some (.positions elems withIndex),
      [(.varPat _iterVar, .whileLoop (.lit (.bool true)) innerBody)] =>
      -- `iter_mut`, `enumerate` and `zip`: a counted loop over the positions
      let elems' := elems.map fun (c, m) => (reconstructForLoops c, m)
      let loop := tryExtractNextMatchPat innerBody _iterVar >>= fun (p, body) =>
        positionsLoop elems' withIndex p (reconstructForLoops body)
      match loop with
      | some l => l
      | none =>
        .match_ (reconstructForLoops scrut) (arms.map fun (p, e) => (p, reconstructForLoops e))
    | _, _ =>
      .match_ (reconstructForLoops scrut) (arms.map fun (p, e) => (p, reconstructForLoops e))
  -- Recursive descent into all other constructors
  | .lit v => .lit v
  | .var n => .var n
  | .letBind n v b => .letBind n (reconstructForLoops v) (reconstructForLoops b)
  | .lam ps b => .lam ps (reconstructForLoops b)
  | .app f args => .app f (args.map reconstructForLoops)
  | .tuple es => .tuple (es.map reconstructForLoops)
  | .proj e i => .proj (reconstructForLoops e) i
  | .ifThenElse c t e => .ifThenElse (reconstructForLoops c) (reconstructForLoops t) (reconstructForLoops e)
  | .unitVal => .unitVal
  | .seq e1 e2 => .seq (reconstructForLoops e1) (reconstructForLoops e2)
  | .borrow e => .borrow (reconstructForLoops e)
  | .deref e => .deref (reconstructForLoops e)
  | .assign n rhs => .assign n (reconstructForLoops rhs)
  | .forLoop v lo hi body => .forLoop v (reconstructForLoops lo) (reconstructForLoops hi) (reconstructForLoops body)
  | .forLoopRev v lo hi body => .forLoopRev v (reconstructForLoops lo) (reconstructForLoops hi) (reconstructForLoops body)
  | .whileLoop c body => .whileLoop (reconstructForLoops c) (reconstructForLoops body)
  | .break_ (some e) => .break_ (some (reconstructForLoops e))
  | .break_ none => .break_ none
  | .continue_ => .continue_
  | .earlyReturn e => .earlyReturn (reconstructForLoops e)
  | .questionMark e => .questionMark (reconstructForLoops e)
  | .forFold v lo hi body => .forFold v (reconstructForLoops lo) (reconstructForLoops hi) (reconstructForLoops body)
  | .forFoldRev v lo hi body => .forFoldRev v (reconstructForLoops lo) (reconstructForLoops hi) (reconstructForLoops body)
  | .whileFold c body => .whileFold (reconstructForLoops c) (reconstructForLoops body)
  | .forFoldReturn v lo hi body => .forFoldReturn v (reconstructForLoops lo) (reconstructForLoops hi) (reconstructForLoops body)
  | .forFoldRevReturn v lo hi body => .forFoldRevReturn v (reconstructForLoops lo) (reconstructForLoops hi) (reconstructForLoops body)
  | .whileFoldReturn c body => .whileFoldReturn (reconstructForLoops c) (reconstructForLoops body)
  | .cfBreak e => .cfBreak (reconstructForLoops e)
  | .cfContinue e => .cfContinue (reconstructForLoops e)
  | .cfBreakContinue e => .cfBreakContinue (reconstructForLoops e)
  | .typeAscription e ty => .typeAscription (reconstructForLoops e) ty

/-! ## Compound Assignment Normalization

Hax sometimes emits compound assignments (`state[3] ^= k0`) as `Call` expressions
to trait methods like `BitXorAssign::bitxor_assign`, producing `app "BitXorAssign" [lhs, rhs]`.
These should be `assign` nodes for the pipeline's LocalMutation phase to process correctly.

We normalize:
- `app "XAssign" [var x, rhs]` → `assign x (app "X" [var x, rhs])`
- `app "XAssign" [index(arr, i), rhs]` → `assign arr (app "array_update" [var arr, i, app "X" [index(arr, i), rhs]])`
-/

/-- Normalize compound assignment ops in an expression.
    Converts `app "XAssign" [target, val]` into proper `assign` nodes
    that the pipeline's LocalMutation phase can process. -/
partial def normalizeAssignOps : ImpExpr → ImpExpr
  | .app f [target, val] =>
    match stripAssignSuffix f with
    | some baseOp =>
      let target' := normalizeAssignOps target
      let val' := normalizeAssignOps val
      let name := extractLValueName target'
      match stripDeref target' with
      | .app "index" [arr, idx] =>
        -- Array element mutation: arr = array_update(arr, idx, X(arr[idx], val))
        .assign name (.app "array_update" [arr, idx, .app baseOp [target', val']])
      | _ =>
        -- Simple variable mutation: x = X(x, val)
        .assign name (.app baseOp [target', val'])
    | none => .app f [normalizeAssignOps target, normalizeAssignOps val]
  | .app f args => .app f (args.map normalizeAssignOps)
  | .lit v => .lit v
  | .var n => .var n
  | .unitVal => .unitVal
  | .letBind n v b => .letBind n (normalizeAssignOps v) (normalizeAssignOps b)
  | .lam ps b => .lam ps (normalizeAssignOps b)
  | .tuple es => .tuple (es.map normalizeAssignOps)
  | .proj e i => .proj (normalizeAssignOps e) i
  | .ifThenElse c t e =>
    .ifThenElse (normalizeAssignOps c) (normalizeAssignOps t) (normalizeAssignOps e)
  | .match_ s arms =>
    .match_ (normalizeAssignOps s) (arms.map fun (p, b) => (p, normalizeAssignOps b))
  | .seq e1 e2 => .seq (normalizeAssignOps e1) (normalizeAssignOps e2)
  | .borrow e => .borrow (normalizeAssignOps e)
  | .deref e => .deref (normalizeAssignOps e)
  | .assign n rhs => .assign n (normalizeAssignOps rhs)
  | .forLoop v lo hi body =>
    .forLoop v (normalizeAssignOps lo) (normalizeAssignOps hi) (normalizeAssignOps body)
  | .forLoopRev v lo hi body =>
    .forLoopRev v (normalizeAssignOps lo) (normalizeAssignOps hi) (normalizeAssignOps body)
  | .whileLoop c body => .whileLoop (normalizeAssignOps c) (normalizeAssignOps body)
  | .break_ (some e) => .break_ (some (normalizeAssignOps e))
  | .break_ none => .break_ none
  | .continue_ => .continue_
  | .earlyReturn e => .earlyReturn (normalizeAssignOps e)
  | .questionMark e => .questionMark (normalizeAssignOps e)
  | .forFold v lo hi body =>
    .forFold v (normalizeAssignOps lo) (normalizeAssignOps hi) (normalizeAssignOps body)
  | .forFoldRev v lo hi body =>
    .forFoldRev v (normalizeAssignOps lo) (normalizeAssignOps hi) (normalizeAssignOps body)
  | .whileFold c body => .whileFold (normalizeAssignOps c) (normalizeAssignOps body)
  | .forFoldReturn v lo hi body =>
    .forFoldReturn v (normalizeAssignOps lo) (normalizeAssignOps hi) (normalizeAssignOps body)
  | .forFoldRevReturn v lo hi body =>
    .forFoldRevReturn v (normalizeAssignOps lo) (normalizeAssignOps hi) (normalizeAssignOps body)
  | .whileFoldReturn c body =>
    .whileFoldReturn (normalizeAssignOps c) (normalizeAssignOps body)
  | .cfBreak e => .cfBreak (normalizeAssignOps e)
  | .cfContinue e => .cfContinue (normalizeAssignOps e)
  | .cfBreakContinue e => .cfBreakContinue (normalizeAssignOps e)
  | .typeAscription e ty => .typeAscription (normalizeAssignOps e) ty

/-- The THIR expression of an item body (the `body` of a `Fn` definition or
    of a `Const` item). In a hax 0.4 export an item body is the object
    `{"expr": e, "params": ps}` and this returns `e`; in a hax 0.3 export the
    item body is the expression itself, an object with a `contents` key, and
    this returns it unchanged. Any other value is returned unchanged. -/
@[expose] def thirBodyExpr (j : Json) : Json :=
  match j.getObjVal? "contents" with
  | .ok _ => j
  | .error _ =>
    match j.getObjVal? "expr", j.getObjVal? "params" with
    | .ok e, .ok _ => e
    | _, _ => j

/-- `thirBodyExpr` is the identity on an item body of the hax 0.3 shape. -/
@[simp] theorem thirBodyExpr_of_contents {j c : Json}
    (h : j.getObjVal? "contents" = .ok c) : thirBodyExpr j = j := by
  simp [thirBodyExpr, h]

/-- `thirBodyExpr` returns the `expr` field of an item body of the hax 0.4 shape. -/
theorem thirBodyExpr_of_expr_params {j e ps : Json} {m : String}
    (hc : j.getObjVal? "contents" = .error m) (he : j.getObjVal? "expr" = .ok e)
    (hp : j.getObjVal? "params" = .ok ps) : thirBodyExpr j = e := by
  simp [thirBodyExpr, hc, he, hp]

/-! ## Full hax export file parsing

The `hax_frontend_export.json` produced by `cargo hax json` is a top-level **array** of
items. Each item has `{def_id, owner_id, span, vis_span, kind, attributes, visibility}`.
The `kind` field is an externally-tagged enum:

- `"Fn"`: `{ident: [name, span], generics, def: {header, params, ret, body}}`
  where `body` is an item body (see `thirBodyExpr`) whose expression
  `parseHaxExpr` handles.
- `"Const"`: `[ident_pair, generics, ty, body]` where `body` is an item body.
- `"TyAlias"`, `"Mod"`, `"Use"`, `"ExternCrate"`: skipped.

A `Mod` item carries the items of its module as a sub-item list (`kind.Mod =
[name_data, sub_items]`, or an object with an `items` field), and the export
also lists each of those items at the top level, so a module's contents occur
once per enclosing module plus once at the top level. `flattenModItems` turns
an export into the list of its distinct items with every `Mod` sub-item list
emptied.
-/

/-- The sub-item list of a `Mod` item, in either the array form
    `[name_data, sub_items]` or the object form with an `items` field, and
    `#[]` for any other item. -/
def modSubItems (item : Json) : Array Json :=
  match item.getObjVal? "kind" with
  | .ok kind =>
    match kind.getObjVal? "Mod" with
    | .ok (.arr modData) =>
      match (modData[1]? : Option Json) with
      | some (.arr sub) => sub
      | _ => #[]
    | .ok modData =>
      match modData.getObjValAs? (Array Json) "items" with
      | .ok sub => sub
      | _ => #[]
    | _ => #[]
  | _ => #[]

/-- `item` with the sub-item list of its `Mod` kind replaced by `[]`; every
    other item is returned unchanged. -/
def clearModSubItems (item : Json) : Json :=
  match item.getObjVal? "kind" with
  | .ok kind =>
    match kind.getObjVal? "Mod" with
    | .ok (.arr modData) =>
      match (modData[1]? : Option Json) with
      | some (.arr _) =>
        item.setObjVal! "kind" (kind.setObjVal! "Mod" (.arr (modData.set! 1 (.arr #[]))))
      | _ => item
    | .ok modData =>
      match modData.getObjValAs? (Array Json) "items" with
      | .ok _ =>
        item.setObjVal! "kind" (kind.setObjVal! "Mod" (modData.setObjVal! "items" (.arr #[])))
      | _ => item
    | _ => item
  | _ => item

/-- The identity of an export item: its `def_id`, or its `owner_id` and `span`
    when the `def_id` is `null` (an `impl` or `use` item). -/
def haxItemKey (item : Json) : String :=
  match item.getObjVal? "def_id" with
  | .ok .null | .error _ =>
    "S" ++ (Json.arr #[(item.getObjVal? "owner_id").toOption.getD .null,
                       (item.getObjVal? "span").toOption.getD .null]).compress
  | .ok d => "D" ++ d.compress

/-- The pre-order walk behind `flattenModItems`: each item of `items` whose key
    is not in `seen` is appended with its `Mod` sub-item list emptied, followed
    by the walk of that sub-item list. -/
partial def flattenModItemsAux (items : Array Json)
    (acc : Array Json × Std.HashSet String) : Array Json × Std.HashSet String :=
  items.foldl (init := acc) fun (out, seen) item =>
    let k := haxItemKey item
    if seen.contains k then (out, seen)
    else flattenModItemsAux (modSubItems item) (out.push (clearModSubItems item), seen.insert k)

/-- The item array of a hax export. A hax 0.4 export is the object
    `{"Legacy": items}` (the `Items` enum of the frontend) and this returns
    `items`; a `{"FullDef": _}` export is refused with an error; any other value,
    in particular the bare item array of a hax 0.3 export, is returned unchanged. -/
@[expose] def haxExportArray (j : Json) : Except String Json :=
  match j.getObjVal? "Legacy" with
  | .ok items => .ok items
  | .error _ =>
    match j.getObjVal? "FullDef" with
    | .ok _ => .error "hax export in the FullDef form is not supported; export with the legacy item form"
    | .error _ => .ok j
/-- The items of an export in pre-order (an item, then the items of its `Mod`
    sub-item list), each item once by `haxItemKey` at its first occurrence, with
    every `Mod` sub-item list emptied. A value other than an array is returned
    unchanged. -/
def flattenModItems (j : Json) : Json :=
  match j with
  | .arr items => .arr (flattenModItemsAux items (#[], {})).1
  | _ => j

/-- Every item of a hax export, at the top level or under a `Mod`. -/
partial def exportItems (j : Json) : List Json :=
  match j with
  | .arr items => items.toList.flatMap fun it =>
    let sub : List Json :=
      match (it.getObjVal? "kind" >>= (·.getObjVal? "Mod")) with
      | .ok (.arr modData) =>
        match modData.toList[1]? with
        | some s => exportItems s
        | none => []
      | .ok modData =>
        match modData.getObjValAs? (Array Json) "items" with
        | .ok s => exportItems (.arr s)
        | _ => []
      | _ => []
    it :: sub
  | _ => []

/-! ## Associated types of trait `impl` blocks

A projection type `P::A` (an `Alias` node) of a trait whose `impl` blocks in
the export give the associated type `A` exactly one type is read at that type:
in struct fields (`parseStructDefsFromJson`), and in every type of the item
signatures, call sites and expressions read by the export-level parsers
(`resolveAssocTypes`). Any other projection of a trait `T` is read by
`parseHaxType` as the opaque type `T_A` (`assocOpaqueName`). -/

/-- The associated types defined by the trait `impl` blocks of an export, as
    `(trait, associated type, type)`: the short names of the `impl`'s trait and
    of each of its `Type` items, and the item's `ty`, without duplicates. -/
def implAssocTypes (j : Json) : List (String × String × Json) :=
  ((exportItems j).flatMap fun it => (do
    let kind ← (it.getObjVal? "kind").toOption
    let impl ← (kind.getObjVal? "Impl").toOption
    let tr ← (impl.getObjVal? "of_trait").toOption
    let tv ← (tr.getObjVal? "value").toOption
    let traitName ← (tv.getObjVal? "def_id").toOption >>= defIdLeafName
    let implItems ← (impl.getObjValAs? (Array Json) "items").toOption
    pure (implItems.toList.filterMap fun (ii : Json) => do
      let ik ← (ii.getObjVal? "kind").toOption
      let tyItem ← (ik.getObjVal? "Type").toOption
      let ty ← (tyItem.getObjVal? "ty").toOption
      let name ← match ii.getObjVal? "ident" with
        | .ok (.arr identPair) => match identPair.toList with
          | (.str n) :: _ => some n
          | _ => none
        | _ => none
      pure (traitName, name, ty))).getD []).eraseDups

/-- The type of a projection `P::A` (a type node whose value is an `Alias`) of a
    trait whose `impl` blocks in `assoc` (`implAssocTypes`) give `A` exactly one
    type; `none` for any other type node. -/
def resolveAssocType? (assoc : List (String × String × Json)) (tyJ : Json) :
    Option Json := do
  let v ← (tyJ.getObjVal? "value").toOption
  let alias ← (v.getObjVal? "Alias").toOption
  let (t, a) ← aliasProjTraitItem alias
  match (assoc.filter fun (t', a', _) => t' == t && a' == a).map (·.2.2) with
  | [ty] => some ty
  | _ => none

/-- The type of a struct field: the type `resolveAssocType?` gives a
    projection, any other type unchanged. -/
def resolveAssocFieldType (assoc : List (String × String × Json)) (tyJ : Json) : Json :=
  (resolveAssocType? assoc tyJ).getD tyJ

/-- An export with every type node that `resolveAssocType?` resolves, at any
    depth, replaced by its resolution under the export's associated types
    (`implAssocTypes`). An export whose trait `impl` blocks define no
    associated type is returned unchanged. The replacement types are not
    rewritten further. -/
partial def resolveAssocTypes (j : Json) : Json :=
  let assoc := implAssocTypes j
  if assoc.isEmpty then j else go assoc j
where
  /-- The rewrite of `resolveAssocTypes` under the associated types `assoc`. -/
  go (assoc : List (String × String × Json)) (j : Json) : Json :=
    match j with
    | .arr xs => .arr (xs.map (go assoc))
    | .obj t =>
      match resolveAssocType? assoc j with
      | some ty => ty
      | none => Json.mkObj (t.toList.map fun (k, v) => (k, go assoc v))
    | _ => j

/-- Extract the function name from a hax `Fn` item's `ident` field.
    Format: `[name_string, span_object]`. -/
def extractFnName (ident : Json) : String :=
  match ident with
  | .arr elems => match elems.toList.head? with
    | some (.str n) => n
    | _ => "unknown_fn"
  | _ => "unknown_fn"

/-- Extract parameter names from a hax function definition's `params` array.
    Each param has `{pat: Decorated<PatKind>, ty: ...}`.
    Returns the list of parameter names (from Binding patterns). -/
def extractParamNames (params : Array Json) : List String :=
  params.toList.filterMap fun p =>
    match p.getObjVal? "pat" with
    | .ok patJ =>
      let contents := match patJ.getObjVal? "contents" with
        | .ok c => c
        | _ => patJ
      match contents.getObjVal? "Binding" with
      | .ok bindData =>
        match bindData.getObjVal? "var" with
        | .ok varJ => match varJ.getObjValAs? String "name" with
          | .ok n => some n
          | _ => none
        | _ => none
      | _ => none
    | _ => none

/-- Per-function type information extracted from hax JSON.
    Re-exported from ImpType for convenience. -/
abbrev FnTypeInfo := Hax.FnTypeInfo

/-- Extract parameter names and types from a hax function definition's `params` array.
    Each param has `{pat: Decorated<PatKind>, ty: {id, value: TyKind}}`. -/
def extractParamTypes (params : Array Json) : List (String × ImpType) :=
  params.toList.filterMap fun p =>
    let name := match p.getObjVal? "pat" with
      | .ok patJ =>
        let contents := match patJ.getObjVal? "contents" with
          | .ok c => c
          | _ => patJ
        match contents.getObjVal? "Binding" with
        | .ok bindData =>
          match bindData.getObjVal? "var" with
          | .ok varJ => varJ.getObjValAs? String "name" |>.toOption
          | _ => none
        | _ => none
      | _ => none
    let ty := match p.getObjVal? "ty" with
      | .ok tyJ => parseHaxType tyJ
      | _ => .unknown
    name.map (·, ty)

/-- The parameter list of a hax function definition `defLike` (the `def`
    object of a `Fn` item, or the `Fn` payload of an `impl` method): its
    `params` field, and when that field is absent the `params` of its item
    body (`ThirBody.params` of a hax 0.4 export). `none` when neither is
    present. -/
def fnDefParams? (defLike : Json) : Option (Array Json) :=
  match defLike.getObjValAs? (Array Json) "params" with
  | .ok ps => some ps
  | .error _ =>
    match defLike.getObjVal? "body" with
    | .ok b => (b.getObjValAs? (Array Json) "params").toOption
    | .error _ => none

/-- The declared parameters of a hax function definition, one `(name, type)`
    pair per parameter in order. The name is the variable a `Binding` pattern
    binds, and `arg{i}` for the parameter at position `i` whose pattern binds
    no single variable; the type is `parseHaxType` of its `ty` field. -/
def declaredParamSig (params : Array Json) : List (String × ImpType) :=
  (params.toList.zip (List.range params.size)).map fun (p, i) =>
    let name := match extractParamNames #[p] with
      | [n] => n
      | _ => s!"arg{i}"
    let ty := match p.getObjVal? "ty" with
      | .ok tyJ => parseHaxType tyJ
      | _ => .unknown
    (name, ty)

/-- The identity of a hax `DefId` as a string: its crate followed by the
    compressed JSON of its `path` (each segment with its disambiguator). The
    `DefId` is read through a `{contents: {value: _}}` wrapper when one is
    present. `none` when the crate or the path is missing. -/
def defIdKey? (defId : Json) : Option String :=
  let inner := match defId.getObjVal? "contents" with
    | .ok c => match c.getObjVal? "value" with | .ok v => v | _ => c
    | _ => defId
  match inner.getObjValAs? String "krate", inner.getObjVal? "path" with
  | .ok k, .ok p => some s!"{k}::{p.compress}"
  | _, _ => none

/-- The declared parameters (`declaredParamSig`) of every `Fn` item of a hax
    export with a `def` field, keyed by `defIdKey?` of the item's `def_id`,
    recursing into the sub-item lists of `Mod` items. -/
partial def localFnParamSigs (items : List Json) : List (String × List (String × ImpType)) :=
  items.flatMap fun (item : Json) =>
    match item.getObjVal? "kind" with
    | .ok kind =>
      match kind.getObjVal? "Fn" with
      | .ok fnData =>
        let key := (item.getObjVal? "def_id").toOption.bind defIdKey?
        let params := (fnData.getObjVal? "def").toOption.bind fnDefParams?
        match key, params with
        | some k, some ps => [(k, declaredParamSig ps)]
        | _, _ => []
      | .error _ =>
        match kind.getObjVal? "Mod" with
        | .ok (Json.arr modData) =>
          match modData.toList[1]? with
          | some (Json.arr subItems) => localFnParamSigs subItems.toList
          | _ => []
        | _ => []
    | .error _ => []

/-- Wrap a function body in parameter bindings.
    Emits `letBind "param" (var "param") body` for each parameter,
    which the pipeline processes as identity bindings.
    The `extractFnDefs` in Main.lean then extracts these as function parameters. -/
def wrapParams (params : List String) (body : ImpExpr) : ImpExpr :=
  params.foldr (fun p acc => .letBind p (.var p) acc) body

/-- Parse a single top-level item from `hax_frontend_export.json`.
    Returns `some (name, body)` for `Fn` and `Const` items, `none` for others. -/
partial def parseHaxItem (j : Json) : Except String (Option (String × ImpExpr)) := do
  let kind ← j.getObjVal? "kind"
  -- Fn: {ident: [name, span], generics: {...}, def: {header, params, ret, body}}
  if let .ok fnData := kind.getObjVal? "Fn" then
    let name := match fnData.getObjVal? "ident" with
      | .ok ident => extractFnName ident
      | _ => "unknown_fn"
    -- Extract parameter names
    let paramNames := match fnData.getObjVal? "def" with
      | .ok def_ => match fnDefParams? def_ with
        | some params => extractParamNames params
        | none => []
      | _ => []
    let body ← match fnData.getObjVal? "def" with
      | .ok def_ => parseHaxExpr (thirBodyExpr (← def_.getObjVal? "body"))
      | _ => throw s!"Fn item '{name}' missing def.body"
    let processed := normalizeAssignOps (reconstructForLoops body)
    -- Wrap body in identity let-bindings for parameters so the pretty printer
    -- can detect them and emit proper function signatures.
    let wrapped := if paramNames.isEmpty then processed else wrapParams paramNames processed
    return some (name, wrapped)
  -- Const: top-level `pub const` has 4 elements [ident, generics, ty, body];
  -- impl-item associated consts have 2 elements [ty, value-info] — skip those
  -- (they're picked up at the Deps-typeclass bridge layer, not the surface).
  else if let .ok (.arr constData) := kind.getObjVal? "Const" then
    if constData.toList.length < 4 then
      return none
    let name := match constData.toList with
      | (.arr ident) :: _ => extractFnName (.arr ident)
      | _ => "unknown_const"
    let body ← match constData.toList[3]? with
      | some bodyJ => parseHaxExpr (thirBodyExpr bodyJ)
      | none => throw s!"Const item '{name}' missing body"
    return some (name, normalizeAssignOps (reconstructForLoops body))
  -- Skip: Mod, Use, ExternCrate, TyAlias
  else return none

/-- Parse a single top-level item with type information.
    Returns `some (name, body, fnTypeInfo)` for `Fn` items, `none` for others. -/
partial def parseHaxItemWithTypes (j : Json) :
    Except String (Option (String × ImpExpr × FnTypeInfo)) := do
  let kind ← j.getObjVal? "kind"
  if let .ok fnData := kind.getObjVal? "Fn" then
    let name := match fnData.getObjVal? "ident" with
      | .ok ident => extractFnName ident
      | _ => "unknown_fn"
    let def_ := match fnData.getObjVal? "def" with
      | .ok d => some d
      | _ => none
    let paramNames := match def_ >>= fnDefParams? with
      | some params => extractParamNames params
      | none => []
    let paramTypes := match def_ >>= fnDefParams? with
      | some params => extractParamTypes params
      | none => []
    let retType := match def_ with
      | some d => match d.getObjVal? "ret" with
        | .ok retJ => parseHaxType retJ
        | _ => .unknown
      | none => .unknown
    let body ← match def_ with
      | some d => parseHaxExpr (thirBodyExpr (← d.getObjVal? "body"))
      | none => throw s!"Fn item '{name}' missing def.body"
    let processed := normalizeAssignOps (reconstructForLoops body)
    let wrapped := if paramNames.isEmpty then processed else wrapParams paramNames processed
    return some (name, wrapped, ⟨paramTypes, retType⟩)
  else if let .ok (.arr constData) := kind.getObjVal? "Const" then
    if constData.toList.length < 4 then
      return none
    let name := match constData.toList with
      | (.arr ident) :: _ => extractFnName (.arr ident)
      | _ => "unknown_const"
    let body ← match constData.toList[3]? with
      | some bodyJ => parseHaxExpr (thirBodyExpr bodyJ)
      | none => throw s!"Const item '{name}' missing body"
    return some (name, normalizeAssignOps (reconstructForLoops body), ⟨[], .unknown⟩)
  else return none

/-- Parse a full hax export with per-function type information.
    Returns both the combined ImpExpr and a list of (name, FnTypeInfo).
    Recurses into Mod items to find nested functions/constants. Projection
    types are read at the types `resolveAssocTypes` gives them. -/
partial def parseHaxFileWithTypes (j : Json) :
    Except String (ImpExpr × List (String × FnTypeInfo)) := do
  let rec parseItemsWithTypes (items : List Json) :
      Except String (List (String × ImpExpr × FnTypeInfo)) := do
    let mut result : List (String × ImpExpr × FnTypeInfo) := []
    for item in items do
      -- Try parsing as Fn/Const
      match ← parseHaxItemWithTypes item with
      | some r => result := result ++ [r]
      | none =>
        -- Recurse into Mod items
        let kind := (item.getObjVal? "kind").toOption
        match kind with
        | some kindJ =>
          -- Try Mod: kind.Mod = [name_data, [sub_items]]
          match kindJ.getObjVal? "Mod" with
          | .ok (.arr modData) =>
            match modData.toList[1]? with
            | some subJ =>
              match subJ with
              | .arr subItems =>
                let sub ← parseItemsWithTypes subItems.toList
                result := result ++ sub
              | _ => pure ()
            | _ => pure ()
          | .ok modData =>
            -- Mod might also be an object with items field
            match modData.getObjValAs? (Array Json) "items" with
            | .ok subItems =>
              let sub ← parseItemsWithTypes subItems.toList
              result := result ++ sub
            | _ => pure ()
          | _ =>
            -- Impl blocks are skipped: a method there may carry no body.
            pure ()
        | none => pure ()
    return result
  match resolveAssocTypes j with
  | .arr items =>
    let parsed ← parseItemsWithTypes items.toList
    match parsed with
    | [] => throw "no functions or constants found in hax export"
    | _ =>
      let expr := parsed.foldr (fun (name, body, _) acc => .letBind name body acc) .unitVal
      let fnTypes := parsed.map fun (name, _, ti) => (name, ti)
      return (expr, fnTypes)
  | _ =>
    return (normalizeAssignOps (reconstructForLoops (← parseHaxExpr j)), [])

/-- Collect return types for all function calls from the hax JSON expression tree.
    Walks the raw JSON (before ImpExpr conversion) and extracts `ty` from each Call node.
    Returns a map: functionName → ImpType (return type). -/
partial def collectCallReturnTypes (j : Json) : List (String × ImpType) :=
  match j with
  | .obj _ =>
    -- Check if this node has a Call in contents
    let callTypes := match j.getObjVal? "contents" with
      | .ok contents =>
        match contents.getObjVal? "Call" with
        | .ok callData =>
          let funName := extractCallName (match callData.getObjVal? "fun" with
            | .ok f => f | _ => .null)
          let retType := match j.getObjVal? "ty" with
            | .ok tyJ => parseHaxType tyJ
            | _ => .unknown
          if funName != "unknown_fn" && funName != "indirect_call" && !retType.isUnknown then
            [(funName, retType)]
          else []
        | _ => []
      | _ => []
    -- Recurse into all object values
    let childTypes := j.getObj?.toOption.map (fun obj =>
      obj.toList.flatMap fun (_, v) => collectCallReturnTypes v) |>.getD []
    callTypes ++ childTypes
  | .arr items => items.toList.flatMap collectCallReturnTypes
  | _ => []

/-- The `defIdKey?` of the callee of a hax `Call`, read from its `fun`
    expression when that is a `GlobalName` (the same `def_id` lookup as
    `extractCallName`). -/
def calleeDefIdKey? (funJ : Json) : Option String := do
  let contents ← (funJ.getObjVal? "contents").toOption
  let gn ← (contents.getObjVal? "GlobalName").toOption
  let item ← (gn.getObjVal? "item").toOption
  let defId ← match item.getObjVal? "value" with
    | .ok v => match v.getObjVal? "def_id" with
      | .ok d => some d
      | _ => item.getObjVal? "def_id" |>.toOption
    | _ => item.getObjVal? "def_id" |>.toOption
  defIdKey? defId

/-- The parameters of the signature of a call with argument types `argTypes`
    to a callee with declared parameters `decl` (`declaredParamSig`). With
    one declared parameter per argument, parameter `i` is named after the
    declared parameter and has the argument type, or the declared type when
    the argument type is unknown. Otherwise parameter `i` is named `arg{i}`
    and has the argument type. -/
def callParamSig (decl : Option (List (String × ImpType))) (argTypes : List ImpType) :
    List (String × ImpType) :=
  match decl with
  | some ds =>
    if ds.length == argTypes.length then
      (ds.zip argTypes).map fun ((n, dty), aty) => (n, if aty.isUnknown then dty else aty)
    else (argTypes.zip (List.range argTypes.length)).map fun (t, i) => (s!"arg{i}", t)
  | none => (argTypes.zip (List.range argTypes.length)).map fun (t, i) => (s!"arg{i}", t)

/-- Collect full type signatures (argument types + return type) for function calls
    from the hax JSON expression tree. For each Call node, extracts the `ty` of each
    argument and the `ty` of the call itself (return type); the parameters are
    `callParamSig` of the callee's entry in `decls` (keyed by `defIdKey?`, from
    `localFnParamSigs`) and the argument types.
    Returns: functionName → FnTypeInfo. -/
partial def collectCallSignatures (j : Json)
    (decls : List (String × List (String × ImpType)) := []) : List (String × FnTypeInfo) :=
  match j with
  | .obj _ =>
    let callSigs := match j.getObjVal? "contents" with
      | .ok contents =>
        match contents.getObjVal? "Call" with
        | .ok callData =>
          let funJ := match callData.getObjVal? "fun" with
            | .ok f => f | _ => .null
          let funName := extractCallName funJ
          let retType := match j.getObjVal? "ty" with
            | .ok tyJ => parseHaxType tyJ
            | _ => .unknown
          let argTys : List ImpType := match callData.getObjValAs? (Array Json) "args" with
            | .ok args => args.toList.map fun arg =>
                match arg.getObjVal? "ty" with
                | .ok tyJ => parseHaxType tyJ
                | _ => .unknown
            | _ => []
          let decl := (calleeDefIdKey? funJ).bind fun k => (decls.find? (·.1 == k)).map (·.2)
          if funName != "unknown_fn" && funName != "indirect_call" then
            [(funName, ⟨callParamSig decl argTys, retType⟩)]
          else []
        | _ => []
      | _ => []
    let childSigs := j.getObj?.toOption.map (fun obj =>
      obj.toList.flatMap fun (_, v) => collectCallSignatures v decls) |>.getD []
    callSigs ++ childSigs
  | .arr items => items.toList.flatMap (collectCallSignatures · decls)
  | _ => []

/-- Extract call signatures from a single hax JSON item (Fn), with callee
    parameters from `decls` (`collectCallSignatures`). -/
partial def extractCallSigsItem (item : Json)
    (decls : List (String × List (String × ImpType)) := []) : List (String × FnTypeInfo) :=
  match item.getObjVal? "kind" with
  | .ok kind =>
    match kind.getObjVal? "Fn" with
    | .ok fnData =>
      match fnData.getObjVal? "def" with
      | .ok d => match d.getObjVal? "body" with
        | .ok body => collectCallSignatures (thirBodyExpr body) decls
        | _ => []
      | _ => []
    | _ =>
      -- Also check Const items
      match kind.getObjVal? "Const" with
      | .ok (.arr constData) =>
        match constData.toList[3]? with
        | some bodyJ => collectCallSignatures (thirBodyExpr bodyJ) decls
        | none => []
      | _ => []
  | _ => []

/-- Extract call signatures from a full hax export JSON, with the parameters
    of a call to a `Fn` item of the export named and typed after its declared
    parameters (`localFnParamSigs`, `callParamSig`).
    Returns deduplicated map: functionName → FnTypeInfo.
    When multiple call sites exist, keeps the one with the most non-unknown arg types.
    Projection types are read at the types `resolveAssocTypes` gives them. -/
partial def extractCallSignaturesFromFile (j : Json) : List (String × FnTypeInfo) :=
  let j := resolveAssocTypes j
  let decls := match j with
    | Json.arr items => localFnParamSigs items.toList
    | _ => []
  let raw : List (String × FnTypeInfo) := match j with
    | Json.arr items => items.toList.flatMap fun item =>
      extractCallSigsItem item decls ++
      -- Also recurse into Mod items
      (match item.getObjVal? "kind" with
       | .ok kind =>
         match kind.getObjVal? "Mod" with
         | .ok (Json.arr modData) =>
           match modData.toList[1]? with
           | some (Json.arr subItems) => subItems.toList.flatMap (extractCallSigsItem · decls)
           | _ => []
         | _ => []
       | _ => ([] : List (String × FnTypeInfo)))
    | _ => []
  -- Deduplicate: for each function name, pick the best type info
  -- (most non-unknown param types, then non-unknown return type)
  raw.foldl (fun (acc : List (String × FnTypeInfo)) ((name, ti) : String × FnTypeInfo) =>
    match acc.find? (·.1 == name) with
    | some (_, existTi) =>
      let existKnown := existTi.paramTypes.filter (fun (_, t) => !t.isUnknown) |>.length
      let existScore := existKnown + (if existTi.retType.isUnknown then 0 else 1)
      let newKnown := ti.paramTypes.filter (fun (_, t) => !t.isUnknown) |>.length
      let newScore := newKnown + (if ti.retType.isUnknown then 0 else 1)
      if newScore > existScore then
        acc.map fun (n, t) => if n == name then (n, ti) else (n, t)
      else acc
    | none => acc ++ [(name, ti)]) []

/-- Collect types of free variable references from hax JSON expression tree.
    For standalone variable references (VarRef) that are not function call targets,
    extracts `ty` to determine whether a free var dep should be Int, Array Int, etc.
    Returns: variableName → ImpType. -/
partial def collectVarRefTypes (j : Json) : List (String × ImpType) :=
  match j with
  | .obj _ =>
    let varTypes := match j.getObjVal? "contents" with
      | .ok contents =>
        -- Handle GlobalVar references
        let globalVarTypes := match contents.getObjVal? "GlobalVar" with
          | .ok varData =>
            let varName := match varData.getObjVal? "id" with
              | .ok id => match id.getObjValAs? String "name" with
                | .ok n => n
                | _ => "unknown"
              | _ => "unknown"
            let ty := match j.getObjVal? "ty" with
              | .ok tyJ => parseHaxType tyJ
              | _ => .unknown
            if varName != "unknown" && !ty.isUnknown then [(varName, ty)] else []
          | _ => ([] : List (String × ImpType))
        -- Handle StaticRef references (static constants like AEGIS_C0)
        let staticRefTypes := match contents.getObjVal? "StaticRef" with
          | .ok data =>
            let varName := match data.getObjVal? "def_id" with
              | .ok defId => extractDefIdName defId
              | _ => "unknown"
            let ty := match j.getObjVal? "ty" with
              | .ok tyJ => parseHaxType tyJ
              | _ => .unknown
            if varName != "unknown" && varName != "static" && !ty.isUnknown
            then [(varName, ty)] else []
          | _ => ([] : List (String × ImpType))
        globalVarTypes ++ staticRefTypes
      | _ => ([] : List (String × ImpType))
    let childTypes := j.getObj?.toOption.map (fun obj =>
      obj.toList.flatMap fun (_, v) => collectVarRefTypes v) |>.getD []
    varTypes ++ childTypes
  | .arr items => items.toList.flatMap collectVarRefTypes
  | _ => []

/-- Extract var ref types from a single hax JSON item. -/
partial def extractVarRefTypesItem (item : Json) : List (String × ImpType) :=
  match item.getObjVal? "kind" with
  | .ok kind =>
    match kind.getObjVal? "Fn" with
    | .ok fnData =>
      match fnData.getObjVal? "def" with
      | .ok d => match d.getObjVal? "body" with
        | .ok body => collectVarRefTypes (thirBodyExpr body)
        | _ => []
      | _ => []
    | _ =>
      match kind.getObjVal? "Const" with
      | .ok (.arr constData) =>
        match constData.toList[3]? with
        | some bodyJ => collectVarRefTypes (thirBodyExpr bodyJ)
        | none => []
      | _ => []
  | _ => []

/-- Extract variable reference types from a full hax export JSON.
    Returns deduplicated map: variableName → ImpType. Projection types are
    read at the types `resolveAssocTypes` gives them. -/
partial def extractVarRefTypesFromFile (j : Json) : List (String × ImpType) :=
  let raw : List (String × ImpType) := match resolveAssocTypes j with
    | Json.arr items => items.toList.flatMap fun item =>
      extractVarRefTypesItem item ++
      (match item.getObjVal? "kind" with
       | .ok kind =>
         match kind.getObjVal? "Mod" with
         | .ok (Json.arr modData) =>
           match modData.toList[1]? with
           | some (Json.arr subItems) => subItems.toList.flatMap extractVarRefTypesItem
           | _ => []
         | _ => []
       | _ => ([] : List (String × ImpType)))
    | _ => []
  raw.foldl (fun (acc : List (String × ImpType)) ((name, ty) : String × ImpType) =>
    if acc.any (·.1 == name) then acc else acc ++ [(name, ty)]) []

/-- Extract call return types from a single hax JSON item (Fn). -/
partial def extractCallRetTypesItem (item : Json) : List (String × ImpType) :=
  match item.getObjVal? "kind" with
  | .ok kind =>
    match kind.getObjVal? "Fn" with
    | .ok fnData =>
      match fnData.getObjVal? "def" with
      | .ok d => match d.getObjVal? "body" with
        | .ok body => collectCallReturnTypes (thirBodyExpr body)
        | _ => []
      | _ => []
    | _ => []
  | _ => []

/-- Extract call return types from a full hax export JSON.
    Returns deduplicated map: functionName → ImpType. Projection types are
    read at the types `resolveAssocTypes` gives them. -/
partial def extractCallReturnTypesFromFile (j : Json) : List (String × ImpType) :=
  let raw := match resolveAssocTypes j with
    | .arr items => items.toList.flatMap extractCallRetTypesItem
    | _ => []
  -- Deduplicate: keep first occurrence per function name
  raw.foldl (fun acc (name, ty) =>
    if acc.any (·.1 == name) then acc else acc ++ [(name, ty)]) []

/-- Validate that an ImpExpr contains no unsupported/dangerous patterns
    that could produce vacuous proofs. Returns a list of warnings. -/
partial def validateExtraction (e : ImpExpr) (path : String := "") : List String :=
  match e with
  | .app f args =>
    let selfWarns :=
      if f.startsWith "hax_unsupported_" then
        [s!"{path}: unsupported hax construct '{f}' — extraction is incomplete"]
      else if f == "literal" then
        [s!"{path}: unsupported literal type — extraction is incomplete"]
      else if f.startsWith "todo:" then
        [s!"{path}: hax Todo '{f}' — Rust code was not translated"]
      else []
    selfWarns ++ args.flatMap (fun a => validateExtraction a path)
  | .letBind n v b =>
    validateExtraction v (path ++ "/" ++ n) ++ validateExtraction b path
  | .seq e1 e2 => validateExtraction e1 path ++ validateExtraction e2 path
  | .ifThenElse c t el =>
    validateExtraction c path ++ validateExtraction t path ++ validateExtraction el path
  | .match_ s arms =>
    validateExtraction s path ++
      arms.flatMap (fun (_, b) => validateExtraction b path)
  | .tuple es => es.flatMap (fun e => validateExtraction e path)
  | .proj e _ => validateExtraction e path
  | .forLoop _ lo hi b | .forLoopRev _ lo hi b
  | .forFold _ lo hi b | .forFoldRev _ lo hi b
  | .forFoldReturn _ lo hi b | .forFoldRevReturn _ lo hi b =>
    validateExtraction lo path ++ validateExtraction hi path ++
      validateExtraction b path
  | .whileLoop c b | .whileFold c b | .whileFoldReturn c b =>
    validateExtraction c path ++ validateExtraction b path
  | .borrow e | .deref e | .assign _ e | .break_ (some e)
  | .earlyReturn e | .questionMark e
  | .cfBreak e | .cfContinue e | .cfBreakContinue e =>
    validateExtraction e path
  | _ => []

/-- Parse a full `hax_frontend_export.json` (top-level array of items).
    Combines all `Fn` and `Const` items into nested `letBind`s. -/
partial def parseHaxFile (j : Json) : Except String ImpExpr := do
  match j with
  | .arr items =>
    let parsed ← items.toList.filterMapM parseHaxItem
    match parsed with
    | [] => throw "no functions or constants found in hax export"
    | _ => return parsed.foldr (fun (name, body) acc => .letBind name body acc) .unitVal
  | _ =>
    -- Single Decorated<ExprKind> — use the existing single-expression parser
    return normalizeAssignOps (reconstructForLoops (← parseHaxExpr j))

/-- Parse and validate a hax export. Returns the ImpExpr and any warnings.
    Warnings indicate incomplete translation (Todo, unsupported literals, etc.)
    that could make downstream proofs vacuous. -/
partial def parseHaxFileValidated (j : Json) : Except String (ImpExpr × List String) := do
  let expr ← parseHaxFile j
  let warnings := validateExtraction expr
  return (expr, warnings)

/-- Extract the type from a hax Decorated JSON node's `ty` field. -/
def extractNodeType (j : Json) : ImpType :=
  match j.getObjVal? "ty" with
  | .ok tyJ => parseHaxType tyJ
  | _ => .unknown

/-- The `def_id` of the `item` of a hax `GlobalName` node `gn`, read from
    `item.value.def_id` or `item.def_id`. -/
def globalNameDefId? (gn : Json) : Option Json := do
  let item ← (gn.getObjVal? "item").toOption
  match item.getObjVal? "value" with
  | .ok v => match v.getObjVal? "def_id" with
    | .ok d => some d
    | _ => (item.getObjVal? "def_id").toOption
  | _ => (item.getObjVal? "def_id").toOption

/-- The parameter types and the result type of the hax function type `ty`: the
    `inputs` and `output` of its signature, under `Arrow` or under the `fn_sig` of
    `FnDef`. `none` for any other type. -/
def fnTypeSig? (ty : Json) : Option (Array Json × Option Json) := do
  let kind := match ty.getObjVal? "value" with
    | .ok v => v
    | _ => (ty.getObjVal? "kind").toOption.getD ty
  let sig ← (kind.getObjVal? "Arrow").toOption <|>
    ((kind.getObjVal? "FnDef").toOption >>= fun d => (d.getObjVal? "fn_sig").toOption)
  let fs := (sig.getObjVal? "value").toOption.getD sig
  let inputs ← (fs.getObjValAs? (Array Json) "inputs").toOption
  pure (inputs, (fs.getObjVal? "output").toOption)

/-- The value of the constructor head `head` of a variant used as a function, at
    the hax function type `ty`: the eta-expansion `fun _ctor0 … => head _ctor0 …`
    over the parameters of `ty` (`fnTypeSig?`). `none` when `ty` is no function
    type. -/
def variantCtorValue? (head : String) (ty : Json) : Option TExprKind := do
  let (inputs, output) ← fnTypeSig? ty
  let params := (List.range inputs.size).map (s!"_ctor{·}")
  let args := (params.zip inputs.toList).map fun (p, t) => TExpr.mk (.var p) (parseHaxType t)
  let retTy := (output.map parseHaxType).getD .unknown
  pure (.lam params (TExpr.mk (.app head args) retTy))

/-- Bug-1 (let-bound local closures): if `exprJ` is a `Closure` with an inline
    `body` and ≥1 cleanly-named param, return its ordered param names and the body
    JSON, for sentinel marking. The IR has no lambda, so a let-bound closure is
    marked `letBind f (app "__clo__:p…" [body]) …` and inlined at its `Fn::call`
    sites by `tInlineClosures` (pre-pipeline). The first hax closure param is the
    implicit environment slot (null pat) and is dropped by `parseHaxPat`. Returns
    `none` for closures passed directly to a HOF/loop (no inline `body`, or no
    named params) — those keep the existing param-dropping behavior. -/
def closureSentinelArg? (exprJ : Json) : Option (List String × Json) :=
  let kind := match exprJ.getObjVal? "contents" with | .ok c => c | _ => exprJ
  match kind.getObjVal? "Closure" with
  | .ok cdata =>
    match cdata.getObjVal? "body", cdata.getObjValAs? (Array Json) "params" with
    | .ok bodyJ, .ok paramsArr =>
      -- A tuple-pattern parameter is bound by `tClosureBinders` in the
      -- `Closure` arm of `parseHaxTExpr`.
      let tuplePat := paramsArr.toList.any fun p =>
        match p.getObjVal? "pat" with
        | .ok patJ => (parseHaxPat patJ matches .tuplePat _)
        | _ => false
      if tuplePat then none else
      let names := paramsArr.toList.filterMap (fun p =>
        match p.getObjVal? "pat" with
        | .ok patJ => match parseHaxPat patJ with
          | .varPat nm => if nm.startsWith "_" then none else some nm
          | _ => none
        | _ => none)
      if names.isEmpty then none else some (names, bodyJ)
    | _, _ => none
  | _ => none

/-- Whether a closure parameter pattern binds variables only: a variable, a
    wildcard, or a tuple of such patterns. -/
def closureParamPatBinds : ImpPat → Bool
  | .varPat _ | .wildcard => true
  | .tuplePat ps => ps.attach.all fun ⟨p, _⟩ => closureParamPatBinds p
  | _ => false

/-- The binders of a hax `Closure` payload for `parseHaxTExpr`: the parameter
    names in order and the `let`s in front of the body that destructure the tuple
    parameters. A variable parameter is its name, a wildcard is `_`, a parameter
    whose `pat` is `null` or missing is the implicit environment slot and names
    nothing, and a tuple parameter (`closureParamPatBinds`) at position `k` is
    named `_clo<k>` and destructured by `tTupleDestructBinds`. A parameter with any
    other pattern is refused. -/
def tClosureBinders (cdata : Json) : Except String (List String × List (String × TExpr)) := do
  let params := (cdata.getObjValAs? (Array Json) "params").toOption.getD #[]
  let mut names : List String := []
  let mut binds : List (String × TExpr) := []
  for p in params.toList do
    match p.getObjVal? "pat" with
    | .ok .null => pure ()
    | .ok patJ =>
      match parseHaxPat patJ with
      | .varPat nm => names := names ++ [nm]
      | .wildcard => names := names ++ ["_"]
      | pat@(.tuplePat ps) =>
        unless closureParamPatBinds pat do
          throw "unsupported construct: a closure parameter pattern other than variables and tuples of variables"
        let n := s!"_clo{names.length}"
        names := names ++ [n]
        binds := binds ++ tTupleDestructBinds n (extractNodeType patJ) ps 0
      | _ =>
        throw "unsupported construct: a closure parameter pattern other than variables and tuples of variables"
    | .error _ => pure ()
  return (names, binds)

/-- Parse a hax `Decorated<ExprKind>` JSON directly into a `TExpr`,
    preserving the type annotation from every JSON node's `ty` field.
    This is the principled typed extraction: every subexpression carries
    its Rust type, eliminating the need for heuristic type recovery.

    `implMap` is the user-inherent-impl lookup table built by
    `buildImplSelfTypeMap`. Used to disambiguate method calls into
    `<TypeName>_<method>` based on the resolved DefId's Impl ancestor's
    self-type. Defaults to `[]` (no disambiguation). -/
partial def parseHaxTExpr (j : Json) (implMap : ImplSelfTypeMap := {}) : Except String TExpr := do
  let ty := extractNodeType j
  let contents ← j.getObjVal? "contents"
  let kind ← parseTExprKind contents j
  return TExpr.mk kind ty
where
  /-- Parse a hax ExprKind into a TExprKind, recursing into sub-expressions
      with full type preservation. `parentJ` is the enclosing Decorated node
      (used to access `ty` for the current node). -/
  parseTExprKind (j _parentJ : Json) : Except String TExprKind := do
    -- Unit variants
    match j with
    | .str "Todo" => return .app "hax_unsupported_Todo" []
    | _ => pure ()

    if let .ok data := j.getObjVal? "VarRef" then
      let name := match data.getObjVal? "id" with
        | .ok id => extractLocalIdentName id
        | _ => "unknown_var"
      return .var name

    -- UpvarRef: closure-captured variable. See the matching case in
    -- `parseExprKind` (around line 879) for why this is just a `.var name`.
    else if let .ok data := j.getObjVal? "UpvarRef" then
      let name := match data.getObjVal? "var_hir_id" with
        | .ok h => extractLocalIdentName h
        | _ => "unknown_upvar"
      return .var name

    else if let .ok data := j.getObjVal? "GlobalName" then
      let name := match data.getObjVal? "item" with
        | .ok item => extractItemDefIdName item "global" [] implMap.localCrate
        | _ => "global"
      -- A variant of an enum of the crate used as a function value is the
      -- eta-expansion of its head `E::V` (`variantCtorValue?`), the head of its
      -- construction (`crateVariantHead?`); without a function type it is refused.
      if let some head := (globalNameDefId? data).bind
          (fun vd => crateVariantHead? vd (extractDefIdName vd)) then
        match (_parentJ.getObjVal? "ty").toOption.bind (variantCtorValue? head) with
        | some k => return k
        | none => throw s!"unsupported construct: the enum variant `{head}` used as a function value without a function type; write the closure `|x| {head}(x)`"
      -- An integer limit of `core` is its value (`coreIntLimit?`).
      match coreIntLimit? data (extractNodeType _parentJ) with
      | some n => return .lit (.int n)
      | none => return constReadKind data implMap name

    else if let .ok data := j.getObjVal? "Literal" then
      -- ByteStr and Str can't be represented as ImpLit; handle before parseTLiteral
      let litKind := match data.getObjVal? "lit" with
        | .ok spanned => match spanned.getObjVal? "node" with
          | .ok n => n
          | _ => spanned
        | _ => data
      if let .ok bsData := litKind.getObjVal? "ByteStr" then
        -- ByteStr: [[byte0, byte1, ...], "Cooked"] → array_lit [bytes]
        match bsData with
        | .arr #[.arr bytes, _] =>
          let byteExprs : List TExpr := bytes.toList.filterMap fun b =>
            match b.getNat? with
            | .ok n => some (TExpr.mk (.lit (.int n)) (.uint .w8))
            | _ => none
          return .app "array_lit" byteExprs
        | _ => return .app "array_lit" []
      else if let .ok _strData := litKind.getObjVal? "Str" then
        -- Str: string literal → intentional opaque placeholder. Use a
        -- distinct app head (`str_opaque`) so `validateExtraction`
        -- doesn't flag it as an "unsupported literal" — string content
        -- in extracted Rust is almost always a debug label (e.g.
        -- `TransitionConstraint { name: "next.a = cur.b", … }`) that we
        -- deliberately don't carry through to Lean. Renders to the same
        -- `Hax.literal` constant as the generic unsupported placeholder.
        return .app "str_opaque" []
      else if let .ok byteVal := litKind.getObjValAs? Nat "Byte" then
        -- Byte: single byte b'X' → integer literal (byte value)
        return .lit (.int byteVal)
      else return .lit (parseTLiteral data)

    else if let .ok data := j.getObjVal? "If" then
      let cond ← parseHaxTExpr (← data.getObjVal? "cond") implMap
      let thn ← parseHaxTExpr (← data.getObjVal? "then") implMap
      let els ← match data.getObjVal? "else_opt" with
        | .ok (.null) => pure (TExpr.mk .unitVal .unit)
        | .ok elsJ => parseHaxTExpr elsJ implMap
        | _ => pure (TExpr.mk .unitVal .unit)
      -- A `?` in the condition is bound in front of the `if`.
      return (tFloatEarlyExitOperands [cond] (extractNodeType _parentJ) fun
        | [c] => .ifThenElse c thn els
        | _ => .ifThenElse cond thn els).kind

    else if let .ok data := j.getObjVal? "Call" then
      let funJ ← data.getObjVal? "fun"
      let funName := extractCallName funJ implMap.collisions implMap.localCrate
      -- Strip panicking calls. `assert!`, `assert_eq!`, `panic!`,
      -- `unreachable!` etc. expand through hax into calls to
      -- `core::panicking::*` helpers (`assert_failed`, `panic`,
      -- `panic_fmt`, `unreachable_display`, …). These are runtime
      -- crash points with no verification value — extracting them
      -- faithfully would force the verifier to model panicking
      -- semantics. Replace with `.unitVal` so the surrounding
      -- `let _ := <assert>; rest` reduces (via rule A of
      -- `tFlattenLetFoldReturn`) to just `rest`. The `AssertKind::Eq`
      -- variant tag that precedes `assert_failed` also resolves to a
      -- bare last-segment name (e.g. `Eq` → conflicts with binary
      -- ops); replacing the call discards the whole `let kind := …; …`
      -- shape before it can be rendered.
      let panickingFns := ["assert_failed", "panic", "panic_fmt",
        "begin_panic", "panic_explicit", "panic_display",
        "unreachable_display", "panic_nounwind", "panic_nounwind_fmt",
        "panic_str", "panic_bounds_check"]
      if panickingFns.contains funName then
        return .unitVal
      let argsJ ← data.getObjValAs? (Array Json) "args"
      let args ← argsJ.toList.attach.mapM (fun ⟨a, _h⟩ => parseHaxTExpr a implMap)
      -- A call of a method of `primeir_hax::Field` resolved to a field `impl`
      -- of the crate takes its modulus-tagged head (`fieldTaggedHead?`).
      if let some h := fieldTaggedHead? funJ args.length implMap then
        return .app h args
      -- A `Vec` passed through a `deref_mut` re-borrow is the `Vec` place
      -- itself (`tDerefMutArg`), so a write-back through the argument reaches
      -- its root variable.
      let args := args.map tDerefMutArg
      -- The `core` slice method `a.swap(i, j)` writes through its receiver; it
      -- becomes the rebinding of the receiver's variable (`tSliceSwap`).
      if funName == "swap" && callKrate funJ == "core" then
        if let [a, i, k] := args then
          if let some e := tSliceSwap a i k then
            return e
      -- `a.reverse()` (`core`) rebinds the receiver's place to the reversed
      -- sequence (`tSliceReverse`); `Vec::remove(a, i)` (`alloc`) is the
      -- removed element and rebinds the receiver's place to the vector without
      -- it (`tVecRemove`).
      if funName == "reverse" && callKrate funJ == "core" then
        if let [a] := args then
          if let some e := tSliceReverse implMap.structFields a then
            return e
      if funName == "remove" && callKrate funJ == "alloc" then
        if let [a, i] := args then
          if let some e := tVecRemove implMap.structFields a i then
            return e
      -- `a.as_slice()` on an array (`core`) is its argument: arrays and slices
      -- have one carrier, `Array`, in the emitted signatures
      -- (`ImpType.toLeanTypeStrSurface`).
      if funName == "as_slice" && callKrate funJ == "core" then
        if let [a] := args then
          match a.ty with
          | .array _ _ | .ref (.array _ _) _ => return a.kind
          | _ => pure ()
      -- Principled method-call disambiguation via the impl-self-type map.
      --
      -- When the Rust source has `crs.len()` and hax resolves it via
      -- the user's `impl Crs { fn len(&self) -> usize { ... } }`, the
      -- function's DefId has parent = the inherent Impl block. The map
      -- (built once per JSON, indexed by Impl-DefId-id) tells us the
      -- self-type. We then emit `<SelfTypeName>_<methodName>` so the
      -- typed pipeline routes the call to a Deps method.
      --
      -- This works for ANY user-defined method (not a hardcoded
      -- allowlist). If the call resolves outside any tracked Impl
      -- (e.g., to `core::slice::Impl::len`), the lookup returns
      -- `none` and we use the bare name.
      let funName' := disambiguateMethodCallWithImplMap funJ funName implMap
      -- A trait-method call resolved to a trait `impl` of the extracted crate
      -- takes that `impl` method's emitted name, so the call reaches the
      -- method's body instead of the generated `Deps` class. A call through a
      -- trait whose `impl` is outside the crate is left alone.
      let resolvedImpl := resolveTraitImplCall funJ implMap
      let funName' := resolvedImpl.getD funName'
      -- A width-tagged inherent integer method (`wrapping_add#32`) carries the
      -- tag of its integer type: the result type where that is an integer
      -- (`wrapping_*`, `rotate_*`, `from_*_bytes`), else the first argument's
      -- (`to_*_bytes`, `overflowing_*`).
      let funName'' := match funName'.splitOn "#" with
        | [op, _] =>
          match intTypeTag? (extractNodeType _parentJ) <|>
              (args.head?.bind fun a => intTypeTag? a.ty) with
          | some t => s!"{op}#{t}"
          | none => funName'
        | _ => funName'
      -- A call of a trait method of a nominal crate keeps its trait in the
      -- head (`primeir_hax::Field::mul`), which separates it from the integer
      -- builtin of the same short name. A call resolved to a trait `impl` of
      -- the extracted crate names a definition and keeps that name.
      let funName'' := traitCallHead implMap funJ resolvedImpl.isSome funName''
      return (tFloatEarlyExitArgs funName'' args (extractNodeType _parentJ)).kind

    else if let .ok data := j.getObjVal? "Let" then
      let exprJ ← data.getObjVal? "expr"
      let pat := match data.getObjVal? "pat" with
        | .ok p => parseHaxPat p
        | _ => .wildcard
      -- A `let`-bound local closure becomes a first-class `.lam` value; its
      -- `Fn::call` sites are lowered to direct applications by `tLowerClosureCalls`.
      if let .varPat n := pat then
        if let some (names, bodyJ) := closureSentinelArg? exprJ then
          let body ← parseHaxTExpr bodyJ implMap
          -- `.unknown` (not `body.ty`): a closure's type is `params → body.ty`,
          -- not `body.ty`; leave it for Lean to infer so the let-binding isn't
          -- mis-ascribed with the return type.
          let lam := TExpr.mk (.lam names body) .unknown
          return .letBind n lam (TExpr.mk .unitVal .unit)
      let rhs ← parseHaxTExpr exprJ implMap
      match pat with
      | .tuplePat pats =>
        let tmpName := "_tup"
        let bindings := tTupleDestructBinds tmpName rhs.ty pats 0
        let inner := bindings.foldr (fun (n, proj) acc =>
          TExpr.mk (.letBind n proj acc) .unknown) (TExpr.mk .unitVal .unit)
        return .letBind tmpName rhs inner
      | .varPat n =>
        return .letBind n rhs (TExpr.mk .unitVal .unit)
      | _ =>
        match data.getObjVal? "pat" |>.toOption |>.bind structPatFields? with
        | some fields =>
          let bindings := tStructDestructBinds "_st" rhs.ty fields
          let inner := bindings.foldr (fun (n, proj) acc =>
            TExpr.mk (.letBind n proj acc) .unknown) (TExpr.mk .unitVal .unit)
          return .letBind "_st" rhs inner
        | none =>
          return .letBind "_let" rhs (TExpr.mk .unitVal .unit)

    else if let .ok data := j.getObjVal? "Block" then
      -- Strip assertion-shape Blocks. `assert!`/`assert_eq!` expands
      -- into a Block whose `expr` is a `Call` to `assert_failed` (with
      -- the AssertKind tag bound in preceding `Let` stmts). After the
      -- panicking-call strip in the Call branch the assert_failed
      -- becomes `.unitVal`, but the surrounding `let kind := …` and
      -- argument-construction stmts remain as dead bindings whose
      -- renderer output collides with the surrounding context. Collapse
      -- the entire Block to `.unitVal` when its `expr` resolves to a
      -- known panicking function — the stmts only existed to compute
      -- panic arguments and have no observable effect once the call
      -- itself is gone.
      let panickingFns := ["assert_failed", "panic", "panic_fmt",
        "begin_panic", "panic_explicit", "panic_display",
        "unreachable_display", "panic_nounwind", "panic_nounwind_fmt",
        "panic_str", "panic_bounds_check"]
      let exprIsPanic := match data.getObjVal? "expr" with
        | .ok exprJ =>
          match exprJ.getObjVal? "contents" with
          | .ok contents =>
            match contents.getObjVal? "Call" with
            | .ok callData =>
              match callData.getObjVal? "fun" with
              | .ok funJ => panickingFns.contains (extractCallName funJ)
              | _ => false
            | _ => false
          | _ => false
        | _ => false
      if exprIsPanic then
        return .unitVal
      let stmts ← match data.getObjValAs? (Array Json) "stmts" with
        | .ok ss => ss.toList.attach.mapM (fun ⟨s, _h⟩ => parseTStmt s)
        | _ => pure []
      let tail ← match data.getObjVal? "expr" with
        | .ok (.null) => pure (TExpr.mk .unitVal .unit)
        | .ok e => parseHaxTExpr e implMap
        | _ => pure (TExpr.mk .unitVal .unit)
      return (tStmtsToSeq stmts tail).kind

    else if let .ok data := j.getObjVal? "Match" then
      let scrut ← parseHaxTExpr (← data.getObjVal? "scrutinee") implMap
      let armsJ ← data.getObjValAs? (Array Json) "arms"
      let arms ← armsJ.toList.attach.mapM (fun ⟨a, _h⟩ => parseTArm a)
      return (tReadMatch scrut arms (extractNodeType _parentJ)).kind

    else if let .ok data := j.getObjVal? "Tuple" then
      let fieldsJ ← data.getObjValAs? (Array Json) "fields"
      let fields ← fieldsJ.toList.attach.mapM (fun ⟨f, _h⟩ => parseHaxTExpr f implMap)
      if fields.isEmpty then return .unitVal
      return (tFloatEarlyExitOperands fields (extractNodeType _parentJ) .tuple).kind

    else if let .ok data := j.getObjVal? "Array" then
      let fieldsJ ← data.getObjValAs? (Array Json) "fields"
      let fields ← fieldsJ.toList.attach.mapM (fun ⟨f, _h⟩ => parseHaxTExpr f implMap)
      return (tFloatEarlyExitArgs "array_lit" fields (extractNodeType _parentJ)).kind

    else if let .ok data := j.getObjVal? "Assign" then
      let lhsJ ← data.getObjVal? "lhs"
      let lhs ← parseHaxTExpr lhsJ implMap
      let rhs ← parseHaxTExpr (← data.getObjVal? "rhs") implMap
      let rec stripD : TExpr → TExpr
        | .mk (.deref e) _ => stripD e
        | e => e
      let lhs' := tIndexMutPlace (stripD lhs)
      let getVarName : TExpr → String
        | .mk (.var n) _ => n
        | .mk (.deref (.mk (.var n) _)) _ => n
        | _ => "_assign"
      -- A place the specific arms do not lower goes to the general place
      -- lowering `tPlaceAssign`; a place it does not lower either is refused,
      -- so that no write is dropped.
      let general : Except String TExprKind :=
        match tPlaceAssign implMap.structFields lhs' rhs with
        | some k => pure k
        | none => throw (unsupportedPlaceError lhs')
      match lhs'.kind with
      | .var n => return .assign n rhs
      -- Nested: arr[i][j] = v → assign arr (array_update arr i (array_update (index arr i) j v))
      | .app "index" [.mk (.app "index" [outerArr, outerIdx]) _, innerIdx] =>
        let outerName := getVarName (stripD outerArr)
        if outerName == "_assign" then general
        else
        let innerUpdate := TExpr.mk (.app "array_update"
          [TExpr.mk (.app "index" [outerArr, outerIdx]) rhs.ty, innerIdx, rhs]) rhs.ty
        return .assign outerName (TExpr.mk (.app "array_update" [outerArr, outerIdx, innerUpdate]) outerArr.ty)
      | .app "index" [arr, idx] =>
        let arrName := getVarName (stripD arr)
        if arrName == "_assign" then
          -- Element of a struct-field place: self.buf[i] = v.
          match tFieldPlaceAssign implMap.structFields lhs' (fun _ => rhs) with
          | some k => return k
          | none => general
        else
          return .assign arrName (TExpr.mk (.app "array_update" [arr, idx, rhs]) rhs.ty)
      | _ =>
        -- Struct-field place `self.buf = v`, or a field of a sequence element
        -- `self.v[i].g = v`.
        match tFieldPlaceAssign implMap.structFields lhs' (fun _ => rhs) with
        | some k => return k
        | none =>
          match tElemFieldPlaceAssign implMap.structFields lhs' (fun _ => rhs) with
          | some k => return k
          | none => general

    else if let .ok data := j.getObjVal? "AssignOp" then
      let rawOp := match data.getObjVal? "op" with
        | .ok opJ => binOpName opJ
        | _ => "op"
      let baseOp := if rawOp.endsWith "Assign" then (rawOp.dropEnd 6).toString else rawOp
      let lhsJ ← data.getObjVal? "lhs"
      -- `x op= y` is `x = x op y`: the operator carries the tag of `x`, as in `Binary`.
      let op := annotateOpWidth baseOp (extractExprWidth lhsJ)
      let lhs ← parseHaxTExpr lhsJ implMap
      let rhs ← parseHaxTExpr (← data.getObjVal? "rhs") implMap
      let rec stripD2 : TExpr → TExpr
        | .mk (.deref e) _ => stripD2 e
        | e => e
      let lhs' := tIndexMutPlace (stripD2 lhs)
      -- As in `Assign`: the general place lowering, then refusal.
      let general : Except String TExprKind :=
        match tPlaceAssign implMap.structFields lhs'
            (TExpr.mk (.app op [tPlaceRead lhs', rhs]) lhs.ty) with
        | some k => pure k
        | none => throw (unsupportedPlaceError lhs')
      match lhs'.kind with
      | .var n => return .assign n (TExpr.mk (.app op [lhs, rhs]) lhs.ty)
      | .app "index" [arr, idx] =>
        let arrName := match (stripD2 arr).kind with
          | .var n => n | _ => "_assign"
        if arrName == "_assign" then
          -- Element of a struct-field place: self.buf[i] op= v.
          match tFieldPlaceAssign implMap.structFields lhs'
              (fun read => TExpr.mk (.app op [read, rhs]) lhs.ty) with
          | some k => return k
          | none => general
        else
          -- The element read is the place `lhs'`, never an `index_mut` call.
          return .assign arrName (TExpr.mk (.app "array_update" [arr, idx, TExpr.mk (.app op [lhs', rhs]) lhs.ty]) arr.ty)
      | _ =>
        -- Struct-field place `self.buf_len op= v`, or a field of a sequence
        -- element `self.v[i].g op= v`; any other place goes to `general`.
        let mkVal := fun read => TExpr.mk (.app op [read, rhs]) lhs.ty
        match tFieldPlaceAssign implMap.structFields lhs' mkVal with
        | some k => return k
        | none =>
          match tElemFieldPlaceAssign implMap.structFields lhs' mkVal with
          | some k => return k
          | none => general

    else if let .ok data := j.getObjVal? "Borrow" then
      let arg ← parseHaxTExpr (← data.getObjVal? "arg") implMap
      return (tFloatEarlyExitOperands [arg] (extractNodeType _parentJ) fun
        | [a] => .borrow a
        | _ => .borrow arg).kind

    else if let .ok _ := j.getObjVal? "RawBorrow" then
      throw "unsupported construct: a raw borrow (`&raw const`, `&raw mut`, as in `core::ptr::eq`)"

    else if let .ok data := j.getObjVal? "Deref" then
      let arg ← parseHaxTExpr (← data.getObjVal? "arg") implMap
      return (tFloatEarlyExitOperands [arg] (extractNodeType _parentJ) fun
        | [a] => .deref a
        | _ => .deref arg).kind

    else if let .ok data := j.getObjVal? "Loop" then
      let body ← parseHaxTExpr (← data.getObjVal? "body") implMap
      return .whileLoop (TExpr.mk (.lit (.bool true)) .bool) body

    else if let .ok data := j.getObjVal? "Break" then
      let value ← match data.getObjVal? "value" with
        | .ok (.null) => pure none
        | .ok v => return .break_ (some (← parseHaxTExpr v implMap))
        | _ => pure none
      return .break_ value

    else if let .ok _data := j.getObjVal? "Continue" then
      return .continue_

    else if let .ok data := j.getObjVal? "Return" then
      let value ← match data.getObjVal? "value" with
        | .ok (.null) => pure (TExpr.mk .unitVal .unit)
        | .ok v => parseHaxTExpr v implMap
        | _ => pure (TExpr.mk .unitVal .unit)
      return .earlyReturn value

    else if let .ok data := j.getObjVal? "Binary" then
      let op := match data.getObjVal? "op" with
        | .ok opJ => binOpName opJ
        | _ => "binop"
      let lhsJ ← data.getObjVal? "lhs"
      let lhs ← parseHaxTExpr lhsJ implMap
      let rhs ← parseHaxTExpr (← data.getObjVal? "rhs") implMap
      let opAnnotated := annotateOpWidth op (extractExprWidth lhsJ)
      -- A `?` in an operand is bound in front of the operation.
      return (tFloatEarlyExitArgs opAnnotated [lhs, rhs] (extractNodeType _parentJ)).kind

    else if let .ok data := j.getObjVal? "LogicalOp" then
      let op := match data.getObjVal? "op" with
        | .ok (.str "And") => "&&"
        | .ok (.str "Or") => "||"
        | _ => "logical_op"
      let lhs ← parseHaxTExpr (← data.getObjVal? "lhs") implMap
      let rhs ← parseHaxTExpr (← data.getObjVal? "rhs") implMap
      -- The right operand is evaluated only on the left operand's value, so a `?`
      -- in it cannot be bound in front; a `?` in the left operand is.
      if tHasEarlyExit rhs then
        throw s!"unsupported construct: `?` in the right operand of `{op}`"
      return (tFloatEarlyExitArgs op [lhs, rhs] (extractNodeType _parentJ)).kind

    else if let .ok data := j.getObjVal? "Unary" then
      let op := match data.getObjVal? "op" with
        | .ok opJ => unOpName opJ
        | _ => "unop"
      let argJ ← data.getObjVal? "arg"
      let arg ← parseHaxTExpr argJ implMap
      let opAnnotated := annotateOpWidth op (extractExprWidth argJ)
      return (tFloatEarlyExitArgs opAnnotated [arg] (extractNodeType _parentJ)).kind

    else if let .ok data := j.getObjVal? "Field" then
      let lhs ← parseHaxTExpr (← data.getObjVal? "lhs") implMap
      let fieldName := match data.getObjVal? "field" with
        | .ok fj => extractDefIdName fj
        | _ => "field"
      return (tFloatEarlyExitArgs ("." ++ fieldName) [lhs] (extractNodeType _parentJ)).kind

    else if let .ok data := j.getObjVal? "TupleField" then
      let lhs ← parseHaxTExpr (← data.getObjVal? "lhs") implMap
      let idx := match data.getObjValAs? Nat "field" with
        | .ok n => n
        | _ => 0
      return (tFloatEarlyExitOperands [lhs] (extractNodeType _parentJ) fun
        | [a] => .proj a idx
        | _ => .proj lhs idx).kind

    else if let .ok data := j.getObjVal? "Index" then
      let lhs ← parseHaxTExpr (← data.getObjVal? "lhs") implMap
      let index ← parseHaxTExpr (← data.getObjVal? "index") implMap
      return (tFloatEarlyExitArgs "index" [lhs, index] (extractNodeType _parentJ)).kind

    else if let .ok data := j.getObjVal? "Cast" then
      let source ← parseHaxTExpr (← data.getObjVal? "source") implMap
      -- A `bool as uN` cast (e.g. `carry as u8` from `overflowing_add`) is a
      -- value injection `if b then 1 else 0`, NOT a width truncation. The
      -- source's `ty` is `.bool` here (hax types the destructured carry var
      -- directly), so `cast#w`/`castVal_w` would be ill-typed. Emit
      -- `Hax.boolToInt` instead.
      match source.ty with
      | .bool => return .app "boolToInt" [source]
      | _ =>
        -- The outer decorated node has the target type.
        let targetWidth := castTag? source.ty (extractExprType _parentJ)
        match targetWidth with
        | some w => return .app s!"cast#{w}" [source]
        | none => return .app "cast" [source]

    else if let .ok data := j.getObjVal? "Use" then
      return (← parseHaxTExpr (← data.getObjVal? "source") implMap).kind

    else if let .ok data := j.getObjVal? "NeverToAny" then
      -- `NeverToAny` is the `!` → any-type coercion. Two distinct uses:
      --
      --   * **Panicking** (`assert!`, `panic!`, `unreachable!`): the
      --     wrapped source has no observable value. Strip the whole
      --     subtree to `.unitVal` so the renderer doesn't try to emit
      --     `AssertKind` tags or `panic_fmt` marshalling code.
      --
      --   * **Early return** (`return None;` inside `if`): the wrapped
      --     source is a `Return` whose payload IS observable as a
      --     function-tail value. Must recurse normally so the
      --     `cfBreak` propagates through `tWrapMatchArmsCF`.
      --
      -- Discriminator: scan the source's JSON for a panicking-call
      -- function name. If found, strip. Otherwise recurse.
      let srcJ ← data.getObjVal? "source"
      let panickingFns := ["assert_failed", "panic", "panic_fmt",
        "begin_panic", "panic_explicit", "panic_display",
        "unreachable_display", "panic_nounwind", "panic_nounwind_fmt",
        "panic_str", "panic_bounds_check"]
      let rec containsPanic : Json → Bool
        | .obj kvs => kvs.toList.any fun (_, v) =>
          match v with
          | .str s => panickingFns.contains s
          | _ => containsPanic v
        | .arr items => items.toList.any containsPanic
        | _ => false
      if containsPanic srcJ then
        return .unitVal
      else
        return (← parseHaxTExpr srcJ implMap).kind

    else if let .ok data := j.getObjVal? "Box" then
      return (← parseHaxTExpr (← data.getObjVal? "value") implMap).kind

    else if let .ok data := j.getObjVal? "Adt" then
      parseTAdtExpr data

    else if let .ok data := j.getObjVal? "Closure" then
      let body ← parseHaxTExpr (← data.getObjVal? "body") implMap
      match closureParams? data with
      | some names => return .lam names body
      | none =>
        let (names, binds) ← tClosureBinders data
        if names.isEmpty then return body.kind
        return .lam names (binds.foldr (fun (n, proj) acc =>
          TExpr.mk (.letBind n proj acc) body.ty) body)

    else if let .ok data := j.getObjVal? "Repeat" then
      let value ← parseHaxTExpr (← data.getObjVal? "value") implMap
      let count ← match data.getObjVal? "count" with
        | .ok countJ => parseHaxTExpr countJ implMap
        | _ => pure (TExpr.mk (.lit (.int 0)) .int)
      return .app "repeat" [value, count]

    else if let .ok data := j.getObjVal? "PlaceTypeAscription" then
      return (← parseHaxTExpr (← data.getObjVal? "source") implMap).kind

    else if let .ok data := j.getObjVal? "ValueTypeAscription" then
      return (← parseHaxTExpr (← data.getObjVal? "source") implMap).kind

    else if let .ok data := j.getObjVal? "PointerCoercion" then
      return (← parseHaxTExpr (← data.getObjVal? "source") implMap).kind

    else if let .ok _data := j.getObjVal? "ConstBlock" then
      return .app "const_block" []

    else if let .ok data := j.getObjVal? "NamedConst" then
      let name := match data.getObjVal? "item" with
        | .ok item => extractItemDefIdName item "const" [] implMap.localCrate
        | _ => "const"
      match coreIntLimit? data (extractNodeType _parentJ) with
      | some n => return .lit (.int n)
      | none => return constReadKind data implMap name

    else if let .ok _data := j.getObjVal? "ConstParam" then
      return .var "const_param"

    else if let .ok data := j.getObjVal? "ConstRef" then
      let name := match data.getObjVal? "id" with
        | .ok id => match id.getObjValAs? String "name" with
          | .ok n => n
          | _ => "const_ref"
        | _ => "const_ref"
      return .var name

    else if let .ok data := j.getObjVal? "StaticRef" then
      let name := match data.getObjVal? "def_id" with
        | .ok defId => extractDefIdName defId [] implMap.localCrate
        | _ => "static"
      return .var name

    else if let .ok data := j.getObjVal? "Yield" then
      let value ← parseHaxTExpr (← data.getObjVal? "value") implMap
      return .app "yield" [value]

    else if let .ok s := j.getObjVal? "Todo" then
      let msg := match s with
        | .str m => m
        | _ => "todo"
      return .app ("todo:" ++ msg) []

    else
      throw s!"unknown hax ExprKind: {j.pretty}"

  /-- Parse a hax literal into ImpLit. -/
  parseTLiteral (data : Json) : ImpLit :=
    let neg := match data.getObjValAs? Bool "neg" with
      | .ok true => true
      | _ => false
    let litKind := match data.getObjVal? "lit" with
      | .ok spanned => match spanned.getObjVal? "node" with
        | .ok n => n
        | _ => spanned
      | _ => data
    if let .ok b := litKind.getObjValAs? Bool "Bool" then .bool b
    else if let .ok intData := litKind.getObjVal? "Int" then
      let nArr := match intData with
        | .arr a => some a
        | _ =>
          let tryUint := intData.getObjVal? "Uint"
          let tryInt := intData.getObjVal? "Int"
          match (tryUint.toOption.orElse fun _ => tryInt.toOption) with
          | some (.arr a) => some a
          | _ => none
      match nArr with
      | some #[nJ, _] =>
        let n := match nJ.getStr? with
          | .ok s => s.toInt?.getD 0
          | _ => match nJ.getNat? with
            | .ok n => n
            | _ => 0
        .int (if neg then -n else n)
      | _ => .int 0
    else if let .ok _bsData := litKind.getObjVal? "ByteStr" then
      -- ByteStr handled at call site; this is a fallback
      .unit
    else .unit  -- char, float, Str, etc.

  /-- Parse a hax Stmt into TExpr. -/
  parseTStmt (j : Json) : Except String TExpr := do
    let kind ← j.getObjVal? "kind"
    if let .ok data := kind.getObjVal? "Expr" then
      match data.getObjVal? "expr" with
      | .ok e => parseHaxTExpr e implMap
      | _ => return TExpr.mk .unitVal .unit
    else if let .ok data := kind.getObjVal? "Let" then
      let pat := match data.getObjVal? "pattern" with
        | .ok p => parseHaxPat p
        | _ => .wildcard
      -- Bug-1: a `let`-bound local closure is marked with a sentinel so the
      -- pre-pipeline `tInlineClosures` pass can inline it at its `Fn::call` sites.
      if let .varPat n := pat then
        if let .ok initJ := data.getObjVal? "initializer" then
          if let some (names, bodyJ) := closureSentinelArg? initJ then
            let body ← parseHaxTExpr bodyJ implMap
            let lam := TExpr.mk (.lam names body) .unknown
            return TExpr.mk (.letBind n lam (TExpr.mk .unitVal .unit)) .unknown
      let init ← match data.getObjVal? "initializer" with
        | .ok (.null) => pure (TExpr.mk .unitVal .unit)
        | .ok e => parseHaxTExpr e implMap
        | _ => pure (TExpr.mk .unitVal .unit)
      -- The `let`s that `tFloatEarlyExitArgs` put at the head of the
      -- initializer go in front of the statement.
      let (tryBinds, init) := tPeelTryLets init
      let stmt : TExpr := match pat with
        | .tuplePat pats =>
          let tmpName := "_tup"
          let bindings := tTupleDestructBinds tmpName init.ty pats 0
          let inner := bindings.foldr (fun (n, proj) acc =>
            TExpr.mk (.letBind n proj acc) .unknown) (TExpr.mk .unitVal .unit)
          TExpr.mk (.letBind tmpName init inner) .unknown
        | .varPat n =>
          TExpr.mk (.letBind n init (TExpr.mk .unitVal .unit)) .unknown
        | _ =>
          match data.getObjVal? "pattern" |>.toOption |>.bind structPatFields? with
          | some fields =>
            let bindings := tStructDestructBinds "_st" init.ty fields
            let inner := bindings.foldr (fun (n, proj) acc =>
              TExpr.mk (.letBind n proj acc) .unknown) (TExpr.mk .unitVal .unit)
            TExpr.mk (.letBind "_st" init inner) .unknown
          | none =>
            TExpr.mk (.letBind "_let" init (TExpr.mk .unitVal .unit)) .unknown
      return tWrapTryLets tryBinds stmt
    else
      return TExpr.mk .unitVal .unit

  /-- Replace the deepest unitVal in a TExpr letBind chain with a continuation. -/
  tReplaceDeepestUnit (e : TExpr) (cont : TExpr) : TExpr :=
    match e.kind with
    | .letBind n v (.mk .unitVal _) => TExpr.mk (.letBind n v cont) e.ty
    | .letBind n v body => TExpr.mk (.letBind n v (tReplaceDeepestUnit body cont)) e.ty
    | _ => TExpr.mk (.seq e cont) cont.ty

  /-- Convert a list of TExpr statements into nested seq/letBind. -/
  tStmtsToSeq (stmts : List TExpr) (tail : TExpr) : TExpr :=
    match stmts with
    | [] => tail
    | [s] => tReplaceDeepestUnit s tail
    | s :: rest => tReplaceDeepestUnit s (tStmtsToSeq rest tail)

  /-- Parse a hax Arm into (ImpPat, TExpr). -/
  parseTArm (j : Json) : Except String (ImpPat × TExpr) := do
    let pat := match j.getObjVal? "pattern" with
      | .ok p => parseHaxPat p
      | _ => .wildcard
    let body ← match j.getObjVal? "body" with
      | .ok b => parseHaxTExpr b implMap
      | _ => pure (TExpr.mk .unitVal .unit)
    return (pat, body)

  /-- Parse a hax AdtExpr into TExprKind. -/
  parseTAdtExpr (j : Json) : Except String TExprKind := do
    -- The head is the variant DefId's short name. For a struct construction
    -- the variant DefId is the struct's own DefId, so the head is the bare
    -- struct constructor def (`Sha256`); a core constructor keeps its bare
    -- name, which `runtimeName` maps (`RangeTo` ↦ `Hax.RangeTo`). The
    -- `type_namespace` DefId resolves to the enclosing module, not the type
    -- name, so it is used only as a fallback when no variant DefId is present.
    let name := match j.getObjVal? "info" with
      | .ok info => match info.getObjVal? "variant" with
        | .ok variantDefId => extractDefIdName variantDefId
        | _ => match info.getObjVal? "type_namespace" with
          | .ok nsDefId => extractDefIdName nsDefId
          | _ => match info.getObjValAs? String "variant_name" with
            | .ok n => n
            | _ => "Adt"
      | _ => "Adt"
    let fieldsJ : List Json := match j.getObjValAs? (Array Json) "fields" with
      | .ok fs => fs.toList
      | _ => []
    let given ← fieldsJ.mapM fun fj =>
      match fj.getObjVal? "value" with
      | .ok v => parseHaxTExpr v implMap
      | _ => pure (TExpr.mk .unitVal .unit)
    -- A functional record update `S { f: v, ..base }` lists only the written
    -- fields; its `base` is `{Base: {base, field_types}}` (hax 0.4) or
    -- `{base, field_types}` (hax 0.3). Each field of `S`, in declaration
    -- order, is the written value or the projection `.f` of the base, typed by
    -- `field_types`; a base other than a variable is bound once by a `let`.
    let fru : Option Json := do
      let b ← (j.getObjVal? "base").toOption
      match b.getObjVal? "Base" with
      | .ok inner => some inner
      | _ => if (b.getObjVal? "base").toOption.isSome then some b else none
    let (fields, fruBase) ← match fru, implMap.structFields.lookup name with
      | some fruJ, some declared =>
        let baseE ← parseHaxTExpr (← fruJ.getObjVal? "base") implMap
        let fieldTys : List ImpType := match fruJ.getObjValAs? (Array Json) "field_types" with
          | .ok ts => ts.toList.map parseHaxType
          | _ => []
        let named : List (Option String × TExpr) := (fieldsJ.zip given).map fun (fj, e) =>
          ((fj.getObjVal? "field").toOption.map (extractDefIdName ·), e)
        let (baseRef, bind) := match baseE.kind with
          | .var _ => (baseE, none)
          | _ => (TExpr.mk (.var "_fru_base") baseE.ty, some baseE)
        let full := (declared.zip (List.range declared.length)).map fun (f, k) =>
          match named.find? (·.1 == some f) with
          | some (_, e) => e
          | none => TExpr.mk (.app ("." ++ f) [baseRef]) (fieldTys.getD k .unknown)
        pure (full, bind)
      | _, _ => pure (given, none)
    -- An enum variant named like a struct of the crate (the typestate form
    -- `enum E { V(V) }`) is written `E::V`, which renders as the constructor
    -- `E.V`; the bare name would resolve to the struct.
    let variantDefId := (j.getObjVal? "info" >>= (·.getObjVal? "variant")).toOption
    -- A variant of an enum of the crate is `E::V` (`crateVariantHead?`), so that it
    -- reaches neither a builtin head (`And` ↦ `Hax.band`) nor the `Deps` class.
    -- A struct of the crate whose name is a builtin head is refused.
    if let some vd := variantDefId then
      if (variantEnumName vd).isNone && builtinHeads.contains name
          && !builtinKrates.contains (defIdKrate vd) && defIdKrate vd != "" then
        throw s!"unsupported construct: the crate struct `{name}` has the name of a builtin head; rename the struct"
    let head := match variantDefId.bind (crateVariantHead? · name) with
      | some h => h
      | none =>
      match variantDefId.map variantEnumName with
      | some (some enumName) =>
        let shortOf : ImpType → Option String
          | .adt n _ => (n.splitOn "::").getLast?
          | _ => none
        if (implMap.structFields.lookup name).isSome
            || fields.any (fun f => shortOf f.ty == some name) then
          s!"{enumName}::{name}"
        else name
      | _ => name
    match fruBase with
    | some b => return .letBind "_fru_base" b (TExpr.mk (.app head fields) b.ty)
    | none => return (tFloatEarlyExitArgs head fields .unknown).kind

/-- `iterMutWriteBack` on a typed body: every write of the element variable `x`
    is followed by `store`, the write-back of `x` to its collection. -/
partial def tIterMutWriteBack (x : String) (store : TExpr) (e : TExpr) : TExpr :=
  let go := tIterMutWriteBack x store
  match e with
  | .mk (.assign n rhs) ty =>
    if n == x then .mk (.seq (.mk (.assign n (go rhs)) ty) store) ty
    else .mk (.assign n (go rhs)) ty
  | .mk (.app f [t, v]) ty =>
    let e' : TExpr := .mk (.app f [go t, go v]) ty
    if (stripAssignSuffix f).isSome && extractLValueName t.erase == x then
      .mk (.seq e' store) .unit
    else e'
  | .mk (.letBind n v b) ty => .mk (.letBind n (go v) (if n == x then b else go b)) ty
  | .mk (.lam ps b) ty => if ps.contains x then e else .mk (.lam ps (go b)) ty
  | .mk (.forLoop v lo hi b) ty =>
    .mk (.forLoop v (go lo) (go hi) (if v == x then b else go b)) ty
  | .mk (.forLoopRev v lo hi b) ty =>
    .mk (.forLoopRev v (go lo) (go hi) (if v == x then b else go b)) ty
  | e => tMapChildren go e

/-- `positionsLoop` on typed collections and body. The counter and the
    `enumerate` variable are typed `usize`, each element variable with the
    element type of its collection, and the write-back of an `iter_mut` element
    with the collection's type. -/
def tPositionsLoop (elems : List (TExpr × Bool)) (withIndex : Bool) (p : ImpPat)
    (body : TExpr) : Option TExpr := do
  let (ip, eps) ← positionsPats (elems.map fun (c, m) => (c.erase, m)) withIndex p
  let pairs := elems.zip eps
  let mutVar := pairs.findSome? fun ((_, m), v) => if m then v else none
  let idx := match ip with
    | some (some i) => i
    | _ => match mutVar with
      | some x => "_ci_" ++ x
      | none => "_ci"
  let usz : ImpType := .uint .wsize
  let idxE : TExpr := .mk (.var idx) usz
  let seqTy (c : TExpr) : ImpType := match c.ty with | .ref t _ => t | t => t
  let mutStores ← pairs.filterMapM fun ((c, m), v) =>
    if m then
      match v with
      | some x => (iterMutRoot c.erase).map fun a =>
        let aTy := seqTy c
        some (x, (TExpr.mk (.assign a (.mk (.app "array_update"
          [.mk (.var a) aTy, idxE, .mk (.var x) (seqElemTy aTy)]) aTy)) .unit : TExpr))
      | none => some none
    else some none
  let body' := mutStores.foldl (fun b (x, st) => tIterMutWriteBack x st b) body
  let bound := pairs.foldr (fun ((c, _), v) b =>
    match v with
    | some x => .mk (.letBind x (.mk (.app "index" [c, idxE]) (seqElemTy (seqTy c))) b) b.ty
    | none => b) body'
  let lenOf (c : TExpr) : TExpr := .mk (.app "len" [c]) usz
  let hi : TExpr := match elems with
    | [(a, _), (b, _)] => .mk (.app "min" [lenOf a, lenOf b]) usz
    | (a, _) :: _ => lenOf a
    | [] => .mk (.lit (.int 0)) usz
  pure (.mk (.forLoop idx (.mk (.lit (.int 0)) usz) hi bound) .unit)

/-- Whether an iterator scrutinee ranges over a `RangeInclusive`. hax lowers
    `lo..=hi` to a value whose only inclusive marker is its type, so the typed
    tree is where the bound can be told apart from `lo..hi`; the argument of
    `into_iter`, possibly under `rev`, is inspected. -/
partial def scrutIsInclusiveRange : TExpr → Bool
  | .mk (.app _ [arg]) _ =>
    match arg with
    | .mk _ (.adt n _) => n.endsWith "RangeInclusive" || scrutIsInclusiveRange arg
    | .mk (.app _ [_]) _ => scrutIsInclusiveRange arg
    | _ => false
  | _ => false

/-- Reconstruct for-loops in a TExpr, preserving type annotations.
    Walks the TExpr tree directly, using untyped helpers (`tryExtractIterator`,
    `tryExtractNextMatch`) only on erased sub-expressions for pattern recognition.
    Structurally new nodes (produced by for-loop reconstruction) get `.unknown` type;
    all other nodes preserve their original `ty`. -/
partial def reconstructForLoopsTExpr : TExpr → TExpr
  | .mk (.match_ scrut arms) ty =>
    match tryExtractIterator scrut.erase, arms with
    | some (.range _lo _hi reversed inclusive),
      [(.varPat _iterVar, .mk (.whileLoop (.mk (.lit (.bool true)) _) innerBody) _)] =>
      -- Found the iterator pattern! Extract loop var and body from the inner next() match
      match tryExtractNextMatch innerBody.erase _iterVar with
      | some (loopVar, _bodyImp) =>
        -- We need to find the actual TExpr body from the arms.
        -- The body is inside the inner match on next(). Walk the TExpr to find it.
        let body' := extractNextMatchBodyT innerBody _iterVar
        match body' with
        | some bodyTE =>
          let bodyRec := reconstructForLoopsTExpr bodyTE
          -- lo and hi come from the scrut pattern; extract from erased and lift
          match tryExtractIterator scrut.erase with
          | some (.range loImp hiImp _reversed _inclusive) =>
            let loTE := reconstructForLoopsTExpr (findSubTExprForImp scrut loImp)
            let hiTE := reconstructForLoopsTExpr (findSubTExprForImp scrut hiImp)
            -- `forLoop` iterates `[lo, hi)`; an inclusive range ends one past `hi`
            -- (`inclusiveUpperT`, an integer literal on a literal `hi`).
            let hiTE := if inclusive || scrutIsInclusiveRange scrut
              then inclusiveUpperT hiTE
              else hiTE
            if reversed then .mk (.forLoopRev loopVar loTE hiTE bodyRec) ty
            else .mk (.forLoop loopVar loTE hiTE bodyRec) ty
          | _ => -- shouldn't happen, but fall through
            .mk (.match_ (reconstructForLoopsTExpr scrut)
              (arms.map fun (p, e) => (p, reconstructForLoopsTExpr e))) ty
        | none =>
          .mk (.match_ (reconstructForLoopsTExpr scrut)
            (arms.map fun (p, e) => (p, reconstructForLoopsTExpr e))) ty
      | none =>
        .mk (.match_ (reconstructForLoopsTExpr scrut)
          (arms.map fun (p, e) => (p, reconstructForLoopsTExpr e))) ty
    | some (.collection _collImp),
      [(.varPat _iterVar, .mk (.whileLoop (.mk (.lit (.bool true)) _) innerBody) _)] =>
      -- Collection iteration pattern
      match tryExtractNextMatch innerBody.erase _iterVar with
      | some (loopVar, _bodyImp) =>
        match extractNextMatchBodyT innerBody _iterVar with
        | some bodyTE =>
          let bodyRec := reconstructForLoopsTExpr bodyTE
          -- The collection is the argument inside into_iter in scrut
          let collTE := extractCollectionTExpr scrut
          let idxVar := "_ci"
          let loopBody := TExpr.mk (.letBind loopVar
            (TExpr.mk (.app "index" [collTE, TExpr.mk (.var idxVar) .unknown]) .unknown)
            bodyRec) .unknown
          .mk (.forLoop idxVar
            (TExpr.mk (.lit (.int 0)) .unknown)
            (TExpr.mk (.app "len" [collTE]) .unknown)
            loopBody) ty
        | none =>
          .mk (.match_ (reconstructForLoopsTExpr scrut)
            (arms.map fun (p, e) => (p, reconstructForLoopsTExpr e))) ty
      | none =>
        .mk (.match_ (reconstructForLoopsTExpr scrut)
          (arms.map fun (p, e) => (p, reconstructForLoopsTExpr e))) ty
    | some (.positions elems withIndex),
      [(.varPat _iterVar, .mk (.whileLoop (.mk (.lit (.bool true)) _) innerBody) _)] =>
      -- `iter_mut`, `enumerate` and `zip`: the loop `positionsLoop` builds,
      -- with the typed collections and body
      let elemsT := elems.map fun (c, m) =>
        (reconstructForLoopsTExpr (findSubTExprForImp scrut c), m)
      let loop := tryExtractNextMatchPat innerBody.erase _iterVar >>= fun (p, _) =>
        extractNextMatchBodyT innerBody _iterVar >>= fun bodyTE =>
        tPositionsLoop elemsT withIndex p (reconstructForLoopsTExpr bodyTE)
      match loop with
      | some l => .mk l.kind ty
      | none =>
        .mk (.match_ (reconstructForLoopsTExpr scrut)
          (arms.map fun (p, e) => (p, reconstructForLoopsTExpr e))) ty
    | _, _ =>
      .mk (.match_ (reconstructForLoopsTExpr scrut)
        (arms.map fun (p, e) => (p, reconstructForLoopsTExpr e))) ty
  -- Recursive descent into all other constructors, preserving ty
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n v b) ty =>
    .mk (.letBind n (reconstructForLoopsTExpr v) (reconstructForLoopsTExpr b)) ty
  | .mk (.lam ps b) ty => .mk (.lam ps (reconstructForLoopsTExpr b)) ty
  | .mk (.app f args) ty =>
    .mk (.app f (args.map reconstructForLoopsTExpr)) ty
  | .mk (.tuple es) ty =>
    .mk (.tuple (es.map reconstructForLoopsTExpr)) ty
  | .mk (.proj e i) ty =>
    .mk (.proj (reconstructForLoopsTExpr e) i) ty
  | .mk (.ifThenElse c t e) ty =>
    .mk (.ifThenElse (reconstructForLoopsTExpr c) (reconstructForLoopsTExpr t) (reconstructForLoopsTExpr e)) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq e1 e2) ty =>
    .mk (.seq (reconstructForLoopsTExpr e1) (reconstructForLoopsTExpr e2)) ty
  | .mk (.borrow e) ty =>
    .mk (.borrow (reconstructForLoopsTExpr e)) ty
  | .mk (.deref e) ty =>
    .mk (.deref (reconstructForLoopsTExpr e)) ty
  | .mk (.assign n rhs) ty =>
    .mk (.assign n (reconstructForLoopsTExpr rhs)) ty
  | .mk (.forLoop v lo hi body) ty =>
    .mk (.forLoop v (reconstructForLoopsTExpr lo) (reconstructForLoopsTExpr hi) (reconstructForLoopsTExpr body)) ty
  | .mk (.forLoopRev v lo hi body) ty =>
    .mk (.forLoopRev v (reconstructForLoopsTExpr lo) (reconstructForLoopsTExpr hi) (reconstructForLoopsTExpr body)) ty
  | .mk (.whileLoop c body) ty =>
    .mk (.whileLoop (reconstructForLoopsTExpr c) (reconstructForLoopsTExpr body)) ty
  | .mk (.break_ (some e)) ty =>
    .mk (.break_ (some (reconstructForLoopsTExpr e))) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty =>
    .mk (.earlyReturn (reconstructForLoopsTExpr e)) ty
  | .mk (.questionMark e) ty =>
    .mk (.questionMark (reconstructForLoopsTExpr e)) ty
  | .mk (.forFold v lo hi body) ty =>
    .mk (.forFold v (reconstructForLoopsTExpr lo) (reconstructForLoopsTExpr hi) (reconstructForLoopsTExpr body)) ty
  | .mk (.forFoldRev v lo hi body) ty =>
    .mk (.forFoldRev v (reconstructForLoopsTExpr lo) (reconstructForLoopsTExpr hi) (reconstructForLoopsTExpr body)) ty
  | .mk (.whileFold c body) ty =>
    .mk (.whileFold (reconstructForLoopsTExpr c) (reconstructForLoopsTExpr body)) ty
  | .mk (.forFoldReturn v lo hi body) ty =>
    .mk (.forFoldReturn v (reconstructForLoopsTExpr lo) (reconstructForLoopsTExpr hi) (reconstructForLoopsTExpr body)) ty
  | .mk (.forFoldRevReturn v lo hi body) ty =>
    .mk (.forFoldRevReturn v (reconstructForLoopsTExpr lo) (reconstructForLoopsTExpr hi) (reconstructForLoopsTExpr body)) ty
  | .mk (.whileFoldReturn c body) ty =>
    .mk (.whileFoldReturn (reconstructForLoopsTExpr c) (reconstructForLoopsTExpr body)) ty
  | .mk (.cfBreak e) ty =>
    .mk (.cfBreak (reconstructForLoopsTExpr e)) ty
  | .mk (.cfContinue e) ty =>
    .mk (.cfContinue (reconstructForLoopsTExpr e)) ty
  | .mk (.cfBreakContinue e) ty =>
    .mk (.cfBreakContinue (reconstructForLoopsTExpr e)) ty
  | .mk (.ann e) ty =>
    .mk (.ann (reconstructForLoopsTExpr e)) ty
  | .mk (.namedProj n e) ty =>
    .mk (.namedProj n (reconstructForLoopsTExpr e)) ty
where
  /-- Walk the TExpr tree to find the body of the `next()` match inside a while-loop body.
      Mirrors `tryExtractNextMatch` but returns the typed body TExpr. -/
  extractNextMatchBodyT (innerBody : TExpr) (iterVar : String) : Option TExpr :=
    match innerBody with
    | .mk (.match_ scrut arms) _ =>
      let isNext := match scrut.erase with
        | .app f _ => isIterNext f
        | _ => false
      if !isNext then none
      else
        let findSome := arms.findSome? fun (pat, body) =>
          match pat with
          | .somePat (.varPat _) => some body
          | .somePat .wildcard => some body
          | .somePat (.tuplePat _) => some body
          | .varPat _ => some body
          | _ => none
        let hasBreak := arms.any fun (pat, body) =>
          match pat with
          | .nonePat | .wildcard => match body.kind with
            | .break_ _ => true
            | _ => false
          | _ => false
        match findSome, hasBreak with
        | some body, true => some body
        | _, _ => none
    | .mk (.letBind _ inner rest) _ =>
      match extractNextMatchBodyT inner iterVar with
      | some r => some r
      | none => extractNextMatchBodyT rest iterVar
    | .mk (.seq e1 e2) _ =>
      match extractNextMatchBodyT e1 iterVar with
      | some r => some r
      | none => extractNextMatchBodyT e2 iterVar
    | _ => none
  /-- Find the sub-TExpr whose erasure matches the given ImpExpr.
      Used to recover typed lo/hi from the scrutinee.
      Falls back to lifting the ImpExpr with `.unknown` types if not found. -/
  findSubTExprForImp (te : TExpr) (target : ImpExpr) : TExpr :=
    if te.erase == target then te
    else match te with
    | .mk (.app _ args) _ =>
      match args.find? (fun a => a.erase == target) with
      | some found => found
      | none =>
        -- Search deeper
        match args.findSome? (fun a => findSubTExprDeep a target) with
        | some found => found
        | none => TExpr.ofImpExpr target
    | _ => TExpr.ofImpExpr target
  /-- Deep search for a sub-TExpr matching the target ImpExpr. -/
  findSubTExprDeep (te : TExpr) (target : ImpExpr) : Option TExpr :=
    if te.erase == target then some te
    else match te with
    | .mk (.app _ args) _ =>
      args.findSome? (fun a => findSubTExprDeep a target)
    | .mk (.letBind _ v b) _ =>
      findSubTExprDeep v target |>.orElse (fun _ => findSubTExprDeep b target)
    | .mk (.seq e1 e2) _ =>
      findSubTExprDeep e1 target |>.orElse (fun _ => findSubTExprDeep e2 target)
    | .mk (.tuple es) _ =>
      es.findSome? (fun a => findSubTExprDeep a target)
    | _ => none
  /-- Extract the collection TExpr from inside into_iter(...) in the scrutinee. -/
  extractCollectionTExpr (scrut : TExpr) : TExpr :=
    match scrut with
    | .mk (.app f [arg]) _ =>
      if isIntoIter f then arg
      else scrut
    | _ => scrut

/-- Normalize compound assignment ops in a TExpr, preserving type annotations.
    Converts `app "XAssign" [target, val]` into proper `assign` nodes.
    Structurally new nodes get `.unknown` type; recursive cases preserve `ty`. -/
partial def normalizeAssignOpsTExpr : TExpr → TExpr
  | .mk (.app f [target, val]) ty =>
    match stripAssignSuffix f with
    | some baseOp =>
      let target' := normalizeAssignOpsTExpr target
      let val' := normalizeAssignOpsTExpr val
      let name := extractLValueName target'.erase
      match stripDeref target'.erase with
      | .app "index" [arr, idx] =>
        -- Array element mutation: arr = array_update(arr, idx, X(arr[idx], val))
        .mk (.assign name (TExpr.mk (.app "array_update"
          [TExpr.ofImpExpr arr, TExpr.ofImpExpr idx,
           TExpr.mk (.app baseOp [target', val']) .unknown]) .unknown)) ty
      | _ =>
        -- Simple variable mutation: x = X(x, val)
        .mk (.assign name (TExpr.mk (.app baseOp [target', val']) .unknown)) ty
    | none => .mk (.app f [normalizeAssignOpsTExpr target, normalizeAssignOpsTExpr val]) ty
  | .mk (.app f args) ty =>
    .mk (.app f (args.map normalizeAssignOpsTExpr)) ty
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.letBind n v b) ty =>
    .mk (.letBind n (normalizeAssignOpsTExpr v) (normalizeAssignOpsTExpr b)) ty
  | .mk (.lam ps b) ty => .mk (.lam ps (normalizeAssignOpsTExpr b)) ty
  | .mk (.tuple es) ty =>
    .mk (.tuple (es.map normalizeAssignOpsTExpr)) ty
  | .mk (.proj e i) ty =>
    .mk (.proj (normalizeAssignOpsTExpr e) i) ty
  | .mk (.ifThenElse c t e) ty =>
    .mk (.ifThenElse (normalizeAssignOpsTExpr c) (normalizeAssignOpsTExpr t) (normalizeAssignOpsTExpr e)) ty
  | .mk (.match_ s arms) ty =>
    .mk (.match_ (normalizeAssignOpsTExpr s) (arms.map fun (p, b) => (p, normalizeAssignOpsTExpr b))) ty
  | .mk (.seq e1 e2) ty =>
    .mk (.seq (normalizeAssignOpsTExpr e1) (normalizeAssignOpsTExpr e2)) ty
  | .mk (.borrow e) ty =>
    .mk (.borrow (normalizeAssignOpsTExpr e)) ty
  | .mk (.deref e) ty =>
    .mk (.deref (normalizeAssignOpsTExpr e)) ty
  | .mk (.assign n rhs) ty =>
    .mk (.assign n (normalizeAssignOpsTExpr rhs)) ty
  | .mk (.forLoop v lo hi body) ty =>
    .mk (.forLoop v (normalizeAssignOpsTExpr lo) (normalizeAssignOpsTExpr hi) (normalizeAssignOpsTExpr body)) ty
  | .mk (.forLoopRev v lo hi body) ty =>
    .mk (.forLoopRev v (normalizeAssignOpsTExpr lo) (normalizeAssignOpsTExpr hi) (normalizeAssignOpsTExpr body)) ty
  | .mk (.whileLoop c body) ty =>
    .mk (.whileLoop (normalizeAssignOpsTExpr c) (normalizeAssignOpsTExpr body)) ty
  | .mk (.break_ (some e)) ty =>
    .mk (.break_ (some (normalizeAssignOpsTExpr e))) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty =>
    .mk (.earlyReturn (normalizeAssignOpsTExpr e)) ty
  | .mk (.questionMark e) ty =>
    .mk (.questionMark (normalizeAssignOpsTExpr e)) ty
  | .mk (.forFold v lo hi body) ty =>
    .mk (.forFold v (normalizeAssignOpsTExpr lo) (normalizeAssignOpsTExpr hi) (normalizeAssignOpsTExpr body)) ty
  | .mk (.forFoldRev v lo hi body) ty =>
    .mk (.forFoldRev v (normalizeAssignOpsTExpr lo) (normalizeAssignOpsTExpr hi) (normalizeAssignOpsTExpr body)) ty
  | .mk (.whileFold c body) ty =>
    .mk (.whileFold (normalizeAssignOpsTExpr c) (normalizeAssignOpsTExpr body)) ty
  | .mk (.forFoldReturn v lo hi body) ty =>
    .mk (.forFoldReturn v (normalizeAssignOpsTExpr lo) (normalizeAssignOpsTExpr hi) (normalizeAssignOpsTExpr body)) ty
  | .mk (.forFoldRevReturn v lo hi body) ty =>
    .mk (.forFoldRevReturn v (normalizeAssignOpsTExpr lo) (normalizeAssignOpsTExpr hi) (normalizeAssignOpsTExpr body)) ty
  | .mk (.whileFoldReturn c body) ty =>
    .mk (.whileFoldReturn (normalizeAssignOpsTExpr c) (normalizeAssignOpsTExpr body)) ty
  | .mk (.cfBreak e) ty =>
    .mk (.cfBreak (normalizeAssignOpsTExpr e)) ty
  | .mk (.cfContinue e) ty =>
    .mk (.cfContinue (normalizeAssignOpsTExpr e)) ty
  | .mk (.cfBreakContinue e) ty =>
    .mk (.cfBreakContinue (normalizeAssignOpsTExpr e)) ty
  | .mk (.ann e) ty =>
    .mk (.ann (normalizeAssignOpsTExpr e)) ty
  | .mk (.namedProj n e) ty =>
    .mk (.namedProj n (normalizeAssignOpsTExpr e)) ty

/-- The names of the local variables a hax expression reads: the `VarRef` and
    `UpvarRef` nodes, at any depth. -/
partial def haxLocalRefNames : Json → List String
  | .obj kvs => kvs.toList.flatMap fun (k, v) =>
    let here : List String := match k, v with
      | "VarRef", d => match d.getObjVal? "id" with
        | .ok id => [extractLocalIdentName id]
        | _ => []
      | "UpvarRef", d => match d.getObjVal? "var_hir_id" with
        | .ok h => [extractLocalIdentName h]
        | _ => []
      | _, _ => []
    here ++ haxLocalRefNames v
  | .arr xs => xs.toList.flatMap haxLocalRefNames
  | _ => []

/-- The variables a pattern binds. -/
def patLocalBinders : ImpPat → List String
  | .varPat n => [n]
  | .tuplePat ps | .ctorPat _ ps => ps.attach.flatMap fun ⟨p, _⟩ => patLocalBinders p
  | .somePat p | .okPat p | .errPat p => patLocalBinders p
  | _ => []

/-- The variables among `locals` that a parsed body reads or assigns outside the
    scope of every binder of them, `bound` being the names in scope: the names
    bound by `let`, `fun`, a `match` arm's pattern or a loop. -/
partial def tUnboundLocals (locals bound : List String) : TExpr → List String
  | .mk k _ =>
    let go := tUnboundLocals locals
    let free (n : String) : List String :=
      if locals.contains n && !bound.contains n then [n] else []
    match k with
    | .var n => free n
    | .assign n rhs => free n ++ go bound rhs
    | .letBind n v b => go bound v ++ go (n :: bound) b
    | .lam ps b => go (ps ++ bound) b
    | .app _ args | .tuple args => args.flatMap (go bound)
    | .match_ s arms =>
      go bound s ++ arms.flatMap fun (p, b) => go (patLocalBinders p ++ bound) b
    | .forLoop v lo hi b | .forLoopRev v lo hi b | .forFold v lo hi b
    | .forFoldRev v lo hi b | .forFoldReturn v lo hi b | .forFoldRevReturn v lo hi b =>
      go bound lo ++ go bound hi ++ go (v :: bound) b
    | .ifThenElse c t e => go bound c ++ go bound t ++ go bound e
    | .seq a b | .whileLoop a b | .whileFold a b | .whileFoldReturn a b =>
      go bound a ++ go bound b
    | .proj e _ | .borrow e | .deref e | .earlyReturn e | .questionMark e | .ann e | .namedProj _ e
    | .cfBreak e | .cfContinue e | .cfBreakContinue e | .break_ (some e) => go bound e
    | _ => []

/-- A body without its leading rebindings `let p := p` of a parameter `p` in `ps`,
    the form of Rust's `let mut p = p;`: such a `let` binds `p` to the value it
    has. -/
def tDropParamRebinds (ps : List String) : TExpr → TExpr
  | .mk (.letBind n (.mk (.var v) vt) b) t =>
    if n == v && ps.contains n then tDropParamRebinds ps b
    else .mk (.letBind n (.mk (.var v) vt) b) t
  | e => e

/-- Parse a single hax Fn item into a typed TExpr with full type information.
    Returns `some (name, rawTExpr, processedTExpr, fnTypeInfo)` for Fn items.
    `rawTExpr` preserves types from hax JSON (for type extraction).
    `processedTExpr` has for-loop reconstruction and assign normalization applied
    (types may be lost due to ImpExpr roundtrip, used for pipeline/rendering). -/
partial def parseHaxItemTExpr (j : Json) (implMap : ImplSelfTypeMap := {}) :
    Except String (Option (String × TExpr × TExpr × FnTypeInfo)) := do
  let kind ← j.getObjVal? "kind"
  if let .ok fnData := kind.getObjVal? "Fn" then
    -- Top-level Fn items have `ident` under `kind.Fn`; impl methods
    -- have it on the item itself. Try both.
    let baseName := match fnData.getObjVal? "ident" with
      | .ok ident => extractFnName ident
      | _ => match j.getObjVal? "ident" with
        | .ok ident => extractFnName ident
        | _ => "unknown_fn"
    -- Bug-2: if this function's short name collides across modules, qualify the
    -- DEF name from the item's def_id path (same rule as call sites). Non-colliding
    -- names keep the bare `extractFnName` form (zero churn for them).
    let name := if implMap.collisions.contains baseName then
        match j.getObjVal? "def_id" with
        | .ok defId => extractDefIdName defId implMap.collisions
        | _ => baseName
      else baseName
    -- Top-level Fn items wrap params/body/ret in a `def` field; impl
    -- methods inline them directly under `kind.Fn`. Use `def` when
    -- present, otherwise the Fn data itself.
    let defLike : Json := match fnData.getObjVal? "def" with
      | .ok d => d
      | _ => fnData
    let paramNames := match fnDefParams? defLike with
      | some params => extractParamNames params
      | none => []
    let paramTypes := match fnDefParams? defLike with
      | some params => extractParamTypes params
      | none => []
    let retType := match defLike.getObjVal? "ret" with
      | .ok retJ => parseHaxType retJ
      | _ => .unknown
    let bodyJ := thirBodyExpr (← defLike.getObjVal? "body")
    let body ← parseHaxTExpr bodyJ implMap
    -- A local variable read outside every binder of it is a binder the parse has
    -- not translated; it is refused, so that it never becomes a `Deps` field.
    let unbound := (tUnboundLocals (haxLocalRefNames bodyJ) paramNames body).eraseDups
    unless unbound.isEmpty do
      throw s!"unsupported construct in `{name}`: the local variables {unbound} are read outside the translation of their binders"
    -- `let mut p = p;` on a parameter `p` rebinds `p` to its value; the leading
    -- such `let`s are dropped, so that they are not read as further parameters.
    let body := tDropParamRebinds paramNames body
    -- Save the raw TExpr (with full types from hax JSON) for type extraction
    let rawWrapped := if paramNames.isEmpty then body
      else paramNames.foldr (fun p acc =>
        let paramTy := match paramTypes.find? (·.1 == p) with
          | some (_, ty) => ty | none => .unknown
        TExpr.mk (.letBind p (TExpr.mk (.var p) paramTy) acc) body.ty) body
    -- Apply for-loop reconstruction and assign normalization (via erase/lift roundtrip)
    -- This loses types but produces correct ImpExpr structure for the pipeline
    let processed := normalizeAssignOpsTExpr (reconstructForLoopsTExpr body)
    let procWrapped := if paramNames.isEmpty then processed
      else paramNames.foldr (fun p acc =>
        let paramTy := match paramTypes.find? (·.1 == p) with
          | some (_, ty) => ty | none => .unknown
        TExpr.mk (.letBind p (TExpr.mk (.var p) paramTy) acc) processed.ty) processed
    return some (name, rawWrapped, procWrapped, ⟨paramTypes, retType⟩)
  else if let .ok (.arr constData) := kind.getObjVal? "Const" then
    -- Top-level `pub const X: T = body` has 4 elements:
    --   [ident, generics, ty, body]
    -- Impl-item associated consts (Rust `const X: T = body` inside an
    -- `impl` block) have a different 2-element shape:
    --   [ty, value-info]
    -- We only handle the top-level form here; impl-item Consts are
    -- skipped (the protocol-side `Deps` typeclass picks them up at
    -- the bridge layer instead).
    if constData.toList.length < 4 then
      return none
    let name := match constData.toList with
      | (.arr ident) :: _ => extractFnName (.arr ident)
      | _ => "unknown_const"
    let body ← match constData.toList[3]? with
      | some bodyJ => parseHaxTExpr (thirBodyExpr bodyJ) implMap
      | none => throw s!"Const item '{name}' missing body"
    let processed := normalizeAssignOpsTExpr (reconstructForLoopsTExpr body)
    return some (name, body, processed, ⟨[], .unknown⟩)
  else return none

/-- The ordered segment names of a hax DefId path (mirrors `extractDefIdName`'s
    `names`). The last is the item name; the second-to-last is its parent module. -/
partial def defIdPathNames (defId : Json) : List String :=
  let inner := match defId.getObjVal? "contents" with
    | .ok c => match c.getObjVal? "value" with | .ok v => v | _ => c
    | _ => defId
  match inner.getObjVal? "path" with
  | .ok (.arr segments) => segments.toList.filterMap fun seg =>
      match seg.getObjVal? "data" with
      | .ok (.str s) => some s
      | .ok data =>
        match data.getObjVal? "TypeNs", data.getObjVal? "ValueNs" with
        | .ok (.str n), _ => some n
        | _, .ok (.str n) => some n
        | _, _ => none
      | _ => none
  | _ => []

/-- Collect `(fnShortName, parentModule)` for every `Fn` item, recursing into
    `Mod` sub-items, for Bug-2 collision detection. -/
partial def collectFnNameParents (items : List Json) : List (String × String) :=
  items.foldl (init := []) fun acc item =>
    match item.getObjVal? "kind" with
    | .ok kind =>
      if (kind.getObjVal? "Fn").toOption.isSome then
        match item.getObjVal? "def_id" with
        | .ok defId =>
          match (defIdPathNames defId).reverse with
          | name :: parent :: _ => (name, parent) :: acc
          | _ => acc
        | _ => acc
      else
        match kind.getObjVal? "Mod" with
        | .ok (Json.arr modData) =>
          match modData.toList[1]? with
          | some (Json.arr subItems) => collectFnNameParents subItems.toList ++ acc
          | _ => acc
        | _ => acc
    | _ => acc

/-- `(krate, shortName)` for every item `parseItemsTExpr` turns into a definition
    under its bare name: an `Fn` item and a top-level `Const` item (the
    four-element form), at the top level or under a `Mod`. An inherent-impl
    method is named `<SelfType>_<method>` and a trait impl is skipped, so
    neither is recursed into. -/
partial def collectItemKrateNames (items : List Json) : List (String × String) :=
  items.foldl (init := []) fun acc item =>
    match item.getObjVal? "kind" with
    | .ok kind =>
      let isTopLevelConst := match kind.getObjVal? "Const" with
        | .ok (Json.arr constData) => constData.size ≥ 4
        | _ => false
      if (kind.getObjVal? "Fn").toOption.isSome || isTopLevelConst then
        match item.getObjVal? "def_id" with
        | .ok defId =>
          match (defIdPathNames defId).getLast? with
          | some name => (defIdKrate defId, name) :: acc
          | none => acc
        | _ => acc
      else
        match kind.getObjVal? "Mod" with
        | .ok (Json.arr modData) =>
          match modData.toList[1]? with
          | some (Json.arr subItems) => collectItemKrateNames subItems.toList ++ acc
          | _ => acc
        | _ => acc
    | _ => acc

/-- The crates the export carries items for and the short names those items
    define, read off the top-level item list. -/
partial def localCrateOfExport (root : Json) : LocalCrate :=
  let items := match root with | .arr xs => xs.toList | _ => []
  let pairs := collectItemKrateNames items
  { krates := (pairs.map (·.1)).eraseDups.filter (· != ""),
    fnNames := (pairs.map (·.2)).eraseDups }

/-- Function short names that collide across ≥2 distinct parent modules. Such
    names are module-qualified at both def and call sites (Bug-2). -/
partial def fnNameCollisions (root : Json) : List String :=
  let items := match root with | .arr xs => xs.toList | _ => []
  let pairs := collectFnNameParents items
  let names := (pairs.map (·.1)).eraseDups
  names.filter fun nm =>
    ((pairs.filter (·.1 == nm)).map (·.2)).eraseDups.length > 1

/-- Whether the `impl` item `implItem` is a method whose first parameter is
    `self`. Its parameters sit under `kind.Fn`, or under `kind.Fn.def`. -/
def implFnTakesSelf (implItem : Json) : Bool :=
  let params : Option (Array Json) := do
    let k ← (implItem.getObjVal? "kind").toOption
    let fnData ← (k.getObjVal? "Fn").toOption
    let defLike := (fnData.getObjVal? "def").toOption.getD fnData
    (defLike.getObjValAs? (Array Json) "params").toOption
  match params with
  | some ps => (extractParamNames ps).head? == some "self"
  | none => false

/-- The methods every trait `impl` block of the extracted crate defines, as
    `(impl interning id, trait short name, self-type short name, method name)`,
    recursing into `Mod` sub-items. Two kinds of `impl` are excluded and keep
    opaque methods: one whose `owner_id` is not local, which belongs to a
    dependency crate, and one of a trait of `core`, `alloc` or `std`. The
    second is what `#[derive(Debug)]`, `#[derive(Clone)]` and their siblings
    produce: the body is compiler-generated rather than written, it is not
    part of any specification, and for `Debug` it calls the `core::fmt`
    builder through `&mut`, which the write-back gate refuses.

    `itemKind` selects the `impl` items collected: `"Fn"` (the methods, the
    default) or `"Const"` (the associated constants). With `selfOnly`, only
    the methods whose first parameter is `self` (`implFnTakesSelf`). -/
partial def collectLocalTraitImplMethods (j : Json) (itemKind : String := "Fn")
    (selfOnly : Bool := false) :
    List (Nat × String × String × String) :=
  let ofImpl (it : Json) (impl : Json) : List (Nat × String × String × String) :=
    let traitName : Option String := do
      let tr ← (impl.getObjVal? "of_trait").toOption
      let tv ← (tr.getObjVal? "value").toOption
      let defId ← (tv.getObjVal? "def_id").toOption
      guard (!builtinKrates.contains (defIdKrate defId))
      defIdLeafName defId
    let ownerVal : Option Json := do
      let oid ← (it.getObjVal? "owner_id").toOption
      let c ← (oid.getObjVal? "contents").toOption
      (c.getObjVal? "value").toOption
    let implId : Option Nat := do
      let oid ← (it.getObjVal? "owner_id").toOption
      let c ← (oid.getObjVal? "contents").toOption
      (c.getObjValAs? Nat "id").toOption
    let isLocal : Bool := match ownerVal with
      | some v => (v.getObjValAs? Bool "is_local").toOption == some true
      | none => false
    let selfName : Option String := do
      let selfTy ← (impl.getObjVal? "self_ty").toOption
      let stVal ← (selfTy.getObjVal? "value").toOption
      let adt ← (stVal.getObjVal? "Adt").toOption
      extractAdtShortName adt
    match isLocal, implId, traitName with
    | true, some iid, some tn =>
      let sn := selfName.getD tn
      match impl.getObjValAs? (Array Json) "items" with
      | .ok implItems =>
        implItems.toList.filterMap fun implItem =>
          match implItem.getObjVal? "kind" with
          | .ok k =>
            if (k.getObjVal? itemKind).toOption.isSome
                && (!selfOnly || implFnTakesSelf implItem) then
              match implItem.getObjVal? "ident" with
              | .ok ident => some (iid, tn, sn, extractFnName ident)
              | _ => none
            else none
          | _ => none
      | _ => []
    | _, _, _ => []
  let ofItem (it : Json) : List (Nat × String × String × String) :=
    match it.getObjVal? "kind" with
    | .ok kindJ =>
      match kindJ.getObjVal? "Mod" with
      | .ok (.arr modData) =>
        match modData.toList[1]? with
        | some sub => collectLocalTraitImplMethods sub itemKind selfOnly
        | none => []
      | .ok modData =>
        match modData.getObjValAs? (Array Json) "items" with
        | .ok subItems => collectLocalTraitImplMethods (.arr subItems) itemKind selfOnly
        | _ => []
      | _ =>
        match kindJ.getObjVal? "Impl" with
        | .ok impl =>
          match impl.getObjVal? "of_trait" with
          | .ok Json.null => []
          | .ok _ => ofImpl it impl
          | _ => []
        | _ => []
    | _ => []
  match j with
  | .arr items => items.toList.foldl (init := []) fun acc it => acc ++ ofItem it
  | _ => []

/-- The `(trait, method)` short names of the `GlobalName` item `j` when it
    names a trait method through an `impl` atom other than `Concrete` (a
    `LocalBound` of a type parameter, a projection). Such a call does not
    resolve to an `impl` of the crate (`traitCallImplMethod`) and keeps the
    name `extractDefIdName` gives the trait method. -/
def boundTraitMethodCall? (gn : Json) : Option (String × String) := do
  let item ← (gn.getObjVal? "item").toOption
  let v ← (item.getObjVal? "value").toOption
  let inTrait ← (v.getObjVal? "in_trait").toOption
  let implJ ← (inTrait.getObjVal? "impl").toOption
  guard (implJ.getObjVal? "Concrete").toOption.isNone
  let calleeDefId ← (v.getObjVal? "def_id").toOption
  match (defIdPathNames calleeDefId).reverse with
  | method :: trait :: _ => some (trait, method)
  | _ => none

/-- The keys of a hax expression node that hold no expression: types, source
    positions and `DefId`s. `traitMethodsCalledThroughBound` does not descend
    into them. -/
def nonExprKeys : List String :=
  ["ty", "span", "def_id", "hir_id", "attributes", "generic_args", "impl_exprs",
   "parent", "fn_span", "typ", "info", "field_types"]

/-- The `(trait, method)` short names of every trait method the export calls
    through an `impl` atom other than `Concrete` (`boundTraitMethodCall?`),
    without duplicates. -/
partial def traitMethodsCalledThroughBound (j : Json) : List (String × String) :=
  (go j #[]).toList.eraseDups
where
  /-- Accumulate the bound trait-method calls of `j` into `acc`. -/
  go (j : Json) (acc : Array (String × String)) : Array (String × String) :=
    match j with
    | .arr xs => xs.foldl (fun a x => go x a) acc
    | .obj kvs =>
      let acc := match (j.getObjVal? "GlobalName").toOption.bind boundTraitMethodCall? with
        | some p => acc.push p
        | none => acc
      kvs.foldl (fun a k v => if nonExprKeys.contains k then a else go v a) acc
    | _ => acc

/-- The traits of the crate with a method `m` that the export calls through a
    trait bound (`traitMethodsCalledThroughBound`), that a local `impl` defines
    with a `self` receiver, and whose short name a local function also has.
    `extractDefIdName` names such a call `<Trait>_<m>`, the field of the
    generated `Deps` class, and its receiver is a value of a type parameter,
    which the `impl`'s `self` type does not match. -/
def boundShadowedTraits (j : Json) : List String :=
  let selfMethods := collectLocalTraitImplMethods j (selfOnly := true)
  let lc := localCrateOfExport j
  ((traitMethodsCalledThroughBound j).filter fun (t, m) =>
    lc.fnNames.contains m && selfMethods.any fun p => p.2.1 == t && p.2.2.2 == m).map (·.1)

/-- The emitted name of every trait-`impl` method of the extracted crate, keyed
    by the `impl`'s interning id and the method name.

    The name is `<Trait>_<method>`, which identifies the trait and the method
    the call site named. The self type disambiguates them,
    `<Trait>_<SelfTy>_<method>`, when the crate has more than one `impl` of that
    trait, and for a trait of `boundShadowedTraits`, whose `<Trait>_<method>`
    names the `Deps` field of a call through a trait bound. A dot is not
    usable as the separator: `PrettyPrint.isFieldProjection` classifies any app
    head containing one as a struct-field projection. -/
def buildTraitImplMethodMap (j : Json) : List (Nat × String × String) :=
  let raw := collectLocalTraitImplMethods j
  let shadowed := boundShadowedTraits j
  raw.map fun (implId, traitName, selfName, method) =>
    let implsOfTrait := ((raw.filter (·.2.1 == traitName)).map (·.1)).eraseDups
    let qual := if implsOfTrait.length > 1 || shadowed.contains traitName then
      s!"{traitName}_{selfName}" else traitName
    (implId, method, s!"{qual}_{method}")

/-- The emitted name of every associated constant of a trait `impl` of the
    extracted crate, keyed by the `impl`'s interning id and the constant name.
    The naming rule is `buildTraitImplMethodMap`'s, with the `impl` blocks of a
    trait counted over methods and constants together, so a constant and a
    method of one `impl` carry the same qualifier. -/
def buildTraitImplConstMap (j : Json) : List (Nat × String × String) :=
  let consts := collectLocalTraitImplMethods j "Const"
  let all := collectLocalTraitImplMethods j ++ consts
  let shadowed := boundShadowedTraits j
  consts.map fun (implId, traitName, selfName, item) =>
    let implsOfTrait := ((all.filter (·.2.1 == traitName)).map (·.1)).eraseDups
    let qual := if implsOfTrait.length > 1 || shadowed.contains traitName then
      s!"{traitName}_{selfName}" else traitName
    (implId, item, s!"{qual}_{item}")

/-- The definition of an associated constant of a trait `impl` block, from the
    `impl` item. Such an item has the two-element form `Const: [ty, body]`,
    with `body` an item body (`thirBodyExpr`). `none` for any other item. -/
partial def parseImplConstTExpr (implItem : Json) (implMap : ImplSelfTypeMap) :
    Except String (Option (TExpr × TExpr × FnTypeInfo)) := do
  let kind ← implItem.getObjVal? "kind"
  match kind.getObjVal? "Const" with
  | .ok (.arr #[tyJ, bodyJ]) =>
    if bodyJ.isNull then return none
    let body ← parseHaxTExpr (thirBodyExpr bodyJ) implMap
    let processed := normalizeAssignOpsTExpr (reconstructForLoopsTExpr body)
    return some (body, processed, ⟨[], parseHaxType tyJ⟩)
  | _ => return none

/-- Parse the inner ImpType of a newtype, a tuple struct with exactly one field.
    Hax represents `struct T(Inner)` as `kind: Struct(..., {Tuple: [[field0_data]]})`.
    Returns `none` for any other struct, including a tuple struct with zero or
    several fields, which `parseStructDefs` reads as a struct with positional
    fields. -/
def parseTupleStructInner (structData : Array Json) : Option ImpType :=
  let variantData := structData.toList[2]?
  match variantData with
  | some vd =>
    match vd.getObjVal? "Tuple" with
    | .ok (Json.arr tupleData) =>
      match tupleData.toList with
      | (Json.arr fields) :: _ =>
        match fields.toList with
        | [fj] =>
          match fj.getObjVal? "ty" with
          | .ok tyJ => some (parseHaxType tyJ)
          | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-- Walk top-level JSON items (including nested Mod items) and collect
    every `struct T(Inner)` newtype (single-positional-field tuple
    struct). Returns `(T.name, Inner)` pairs. Newtypes are distinct from
    named-field structs (which `parseStructDefsFromJson` handles). -/
partial def buildNewtypeMap (j : Json) : NewtypeMap :=
  let parseItems (items : List Json) : NewtypeMap :=
    items.foldl (init := []) fun acc item =>
      match item.getObjVal? "kind" with
      | .ok kindJ =>
        -- Tuple struct: kind.Struct = [name, generics, {Tuple: ...}]
        let here : NewtypeMap :=
          match kindJ.getObjVal? "Struct" with
          | .ok (.arr sd) =>
            let name := match sd.toList with
              | (Json.arr nameSpan) :: _ =>
                match nameSpan.toList with
                | (Json.str n) :: _ => n
                | _ => ""
              | _ => ""
            if name.isEmpty then []
            else match parseTupleStructInner sd with
              | some inner => [(name, inner)]
              | none => []
          | _ => []
        -- Recurse into Mod items: kind.Mod = [name_data, [sub_items]]
        let modNewtypes : NewtypeMap :=
          match kindJ.getObjVal? "Mod" with
          | .ok (.arr modData) =>
            match modData.toList[1]? with
            | some (Json.arr subItems) => buildNewtypeMap (Json.arr subItems)
            | _ => []
          | _ => []
        acc ++ here ++ modNewtypes
      | _ => acc
  match j with
  | .arr items =>
    let raw := parseItems items.toList
    raw.foldl (fun acc (n, t) =>
      if acc.any (·.1 == n) then acc else acc ++ [(n, t)]) []
  | _ => []

/-! ## Modulus-tagged field operations

A call of a method of `primeir_hax::Field` that resolves to an `impl` of the
crate whose self type is a newtype over `u64` (a modulus below `2^64`) or over
`[u64; n]` (a modulus `p ≥ 2^64`, `n` the least number of words with
`p ≤ 2^(64 n)`) takes the head `<method>#p<modulus>` (`fieldTagHead`) when the
`impl` stores elements canonically, and `<method>#p<modulus>#r<k>`
(`fieldTagHeadMont`) when its `MONT_BITS` constant is `k > 0`, the Montgomery
representation with radix `2 ^ k` (`fieldImplRepr?`); the newtype is erased to
its inner type in the whole export (`tEraseFieldNewtypes`), so the operands and
the result of such a call are `u64` values, or arrays of `n` little-endian `u64`
limbs, holding the stored integers. -/

/-- The top-level constants of a hax export (the four-element `Const` form
    `[ident, generics, ty, body]`), as `(name, body)`. -/
def exportConstBodies (j : Json) : List (String × Json) :=
  (exportItems j).filterMap fun it => do
    let kind ← (it.getObjVal? "kind").toOption
    match kind.getObjVal? "Const" with
    | .ok (.arr cd) =>
      match cd.toList with
      | [ident, _, _, body] => some (extractFnName ident, thirBodyExpr body)
      | _ => none
    | _ => none

/-- The `u64` limbs a constant expression denotes: an integer literal, an array
    literal of integer literals, a borrow or dereference of one, or a read of a
    constant of `consts` (matched on the last `::` segment of its name), with at
    most `fuel` nested reads. -/
partial def constLimbs (consts : List (String × Json)) (fuel : Nat) (e : TExpr) :
    Option (List Nat) :=
  match e.kind with
  | .lit (.int n) => if 0 ≤ n then some [n.toNat] else none
  | .lit (.uintLit _ n) => some [n]
  | .borrow e | .deref e | .ann e => constLimbs consts fuel e
  | .app "array_lit" es => do
    let ls ← es.mapM (constLimbs consts fuel)
    ls.mapM fun l => match l with
      | [x] => some x
      | _ => none
  | .var n | .app n [] =>
    match fuel with
    | 0 => none
    | fuel + 1 => do
      let body ← consts.lookup (((n.splitOn "::").getLast?).getD n)
      let te ← (parseHaxTExpr body {}).toOption
      constLimbs consts fuel te
  | _ => none

/-- Whether a trait `impl` block implements the trait `Field` of the crate
    `primeir_hax` (its `of_trait` reference). -/
def isPrimeirFieldImpl (impl : Json) : Bool :=
  let r : Option Unit := do
    let tr ← (impl.getObjVal? "of_trait").toOption
    let tv ← (tr.getObjVal? "value").toOption
    let defId ← (tv.getObjVal? "def_id").toOption
    guard (defIdKrate defId == "primeir_hax")
    guard (defIdLeafName defId == some "Field")
  r.isSome

/-- The number of limbs of an element of the prime field of modulus `p` whose
    self type has the inner type `inner`: `1` when `inner` is `u64` and
    `p < 2^64`; `n` when `inner` is `[u64; n]`, `p ≥ 2^64` and `n` is the least
    number of `64`-bit words with `p ≤ 2^(64 n)`. `none` otherwise. -/
def fieldReprLimbs? (inner : ImpType) (p : Nat) : Option Nat :=
  match inner with
  | .uint .w64 => if p < 2 ^ 64 then some 1 else none
  | .array (.uint .w64) n =>
    if 2 ^ 64 ≤ p ∧ 2 ^ (64 * (n - 1)) < p ∧ p ≤ 2 ^ (64 * n) then some n else none
  | _ => none

/-- The inner type of a field newtype with `n` limbs: `u64` for one limb,
    `[u64; n]` otherwise. -/
def fieldReprTy (n : Nat) : ImpType :=
  if n ≤ 1 then .uint .w64 else .array (.uint .w64) n

/-- The last `::` segment of a name. -/
def lastPathSegment (n : String) : String := ((n.splitOn "::").getLast?).getD n

/-- The entry `(impl interning id, T, modulus, number of limbs)` of an item of a
    hax export that is a local `impl primeir_hax::Field for T` whose self type
    `T` is a newtype in `newtypes` over `u64` or over `[u64; n]`, with the
    top-level constants `consts` of the export. The modulus is the value of the
    `impl`'s `MODULUS_LE` constant read as little-endian base-`2^64` limbs
    (`constLimbs`); `none` for an `impl` whose `MODULUS_LE` does not evaluate to
    limbs below `2^64` denoting a number at least `2`, or whose inner type is
    not the representation of that modulus (`fieldReprLimbs?`), and for any
    other item. -/
def fieldImplEntry? (consts : List (String × Json)) (newtypes : NewtypeMap) (it : Json) :
    Option (Nat × String × Nat × Nat) := do
    let kind ← (it.getObjVal? "kind").toOption
    let impl ← (kind.getObjVal? "Impl").toOption
    guard (isPrimeirFieldImpl impl)
    let oid ← (it.getObjVal? "owner_id").toOption
    let c ← (oid.getObjVal? "contents").toOption
    guard ((c.getObjVal? "value" >>= (·.getObjValAs? Bool "is_local")).toOption == some true)
    let implId ← (c.getObjValAs? Nat "id").toOption
    let selfTy ← (impl.getObjVal? "self_ty").toOption
    let stVal ← (selfTy.getObjVal? "value").toOption
    let adt ← (stVal.getObjVal? "Adt").toOption
    let sn ← extractAdtShortName adt
    let inner ← newtypes.lookup sn
    let implItems ← (impl.getObjValAs? (Array Json) "items").toOption
    let modItem ← implItems.find? fun ii =>
      (ii.getObjVal? "ident").toOption.map extractFnName == some "MODULUS_LE"
    let k ← (modItem.getObjVal? "kind").toOption
    let bodyJ ← match k.getObjVal? "Const" with
      | .ok (.arr #[_, b]) => some (thirBodyExpr b)
      | _ => none
    let te ← (parseHaxTExpr bodyJ {}).toOption
    let limbs ← constLimbs consts 8 te
    guard (limbs.all (· < 2 ^ 64))
    let p := limbs.foldr (fun l acc => l + 2 ^ 64 * acc) 0
    guard (2 ≤ p)
    let n ← fieldReprLimbs? inner p
    pure (implId, sn, p, n)

/-- The items of a trait `impl` item of a hax export, and `#[]` for any other
    item. -/
def fieldImplItems (it : Json) : Array Json :=
  ((do
    let kind ← (it.getObjVal? "kind").toOption
    let impl ← (kind.getObjVal? "Impl").toOption
    (impl.getObjValAs? (Array Json) "items").toOption : Option (Array Json))).getD #[]

/-- The item named `name` of the items of an `impl`. -/
def implItemNamed? (implItems : Array Json) (name : String) : Option Json :=
  implItems.find? fun ii => (ii.getObjVal? "ident").toOption.map extractFnName == some name

/-- The `u64` limbs of the body of an associated constant item of an `impl`
    whose self type is the newtype `sn`, with the top-level constants `consts`:
    a construction `sn(x)` is read as `x` (`constLimbs`). -/
def implConstLimbs? (consts : List (String × Json)) (sn : String) (item : Json) :
    Option (List Nat) := do
  let k ← (item.getObjVal? "kind").toOption
  let bodyJ ← match k.getObjVal? "Const" with
    | .ok (.arr #[_, b]) => some (thirBodyExpr b)
    | _ => none
  let te ← (parseHaxTExpr bodyJ {}).toOption
  let te := match te.kind with
    | .app f [x] => if lastPathSegment f == sn then x else te
    | _ => te
  constLimbs consts 8 te

/-- The representation of a field `impl` with the items `implItems` and the self
    type `sn`, from its `MONT_BITS` constant: `canon` when the `impl` does not
    define it (the trait default `0`) or defines it as `0`, `mont k` when it
    defines it as `k > 0`. `none` when the constant does not evaluate to one
    number. -/
def fieldImplRepr? (consts : List (String × Json)) (sn : String) (implItems : Array Json) :
    Option FieldImplRepr :=
  match implItemNamed? implItems "MONT_BITS" with
  | none => some .canon
  | some it =>
    match implConstLimbs? consts sn it with
    | some [0] => some .canon
    | some [k] => some (.mont k)
    | _ => none

/-- Whether the limbs `one` of the constant `ONE` of a field `impl` of modulus
    `p` are the representation `r` of `1`: always for `canon`; for `mont k`,
    the limbs are given, are below `2^64` and denote `2 ^ k mod p`
    (`fieldReprVal`). -/
def fieldOneOk (r : FieldImplRepr) (p : Nat) (one : Option (List Nat)) : Bool :=
  match r with
  | .canon => true
  | .mont k =>
    match one with
    | some ls => ls.all (· < 2 ^ 64) && limbsValue ls == fieldReprVal (.mont k) p 1
    | none => false

/-- **The Montgomery check**: in the representation `mont k`, `fieldOneOk`
    holds exactly when the limbs of `ONE` are below `2^64` and denote the
    integer the representation stores for `1`. -/
theorem fieldOneOk_mont_iff (k p : Nat) (ls : List Nat) :
    fieldOneOk (.mont k) p (some ls) = true ↔
      (∀ l ∈ ls, l < 2 ^ 64) ∧ limbsValue ls = fieldReprVal (.mont k) p 1 := by
  simp [fieldOneOk]

/-- The entry of an item of a hax export that is a field `impl`
    (`fieldImplEntry?`) together with its representation (`fieldImplRepr?`).
    `none` for an `impl` whose `MONT_BITS` does not evaluate to one number, and
    for a Montgomery `impl` whose `ONE` is not the representation of `1`
    (`fieldOneOk`). -/
def fieldImplReprEntry? (consts : List (String × Json)) (newtypes : NewtypeMap) (it : Json) :
    Option ((Nat × String × Nat × Nat) × FieldImplRepr) := do
  let e ← fieldImplEntry? consts newtypes it
  let items := fieldImplItems it
  let r ← fieldImplRepr? consts e.2.1 items
  guard (fieldOneOk r e.2.2.1 ((implItemNamed? items "ONE").bind (implConstLimbs? consts e.2.1)))
  pure (e, r)

/-- **An `impl` without `MONT_BITS` is read as before**: its entry is the
    entry `fieldImplEntry?` gives, in the canonical representation. -/
theorem fieldImplReprEntry?_of_canon {consts : List (String × Json)} {newtypes : NewtypeMap}
    {it : Json} (h : implItemNamed? (fieldImplItems it) "MONT_BITS" = none) :
    fieldImplReprEntry? consts newtypes it =
      (fieldImplEntry? consts newtypes it).map (·, .canon) := by
  unfold fieldImplReprEntry?
  cases fieldImplEntry? consts newtypes it with
  | none => rfl
  | some e => simp [fieldImplRepr?, h, fieldOneOk, guard]

/-- The local `impl primeir_hax::Field for T` blocks of a hax export whose self
    type `T` is a newtype in `newtypes` over `u64` or over `[u64; n]`, as
    `(impl interning id, T, modulus, number of limbs)` (`fieldImplReprEntry?`). -/
def buildFieldImplMap (j : Json) (newtypes : NewtypeMap) :
    List (Nat × String × Nat × Nat) :=
  let consts := exportConstBodies j
  (exportItems j).filterMap fun it => (fieldImplReprEntry? consts newtypes it).map (·.1)

/-- The representations of the `impl`s of `buildFieldImplMap` that are not
    canonical, keyed by their interning ids. -/
def buildFieldReprMap (j : Json) (newtypes : NewtypeMap) : List (Nat × FieldImplRepr) :=
  let consts := exportConstBodies j
  (exportItems j).filterMap fun it => do
    let (e, r) ← fieldImplReprEntry? consts newtypes it
    match r with
    | .canon => none
    | .mont k => some (e.1, .mont k)

/-- **The canonical path is unchanged**: on an export none of whose items
    defines `MONT_BITS`, `buildFieldImplMap` lists the entries `fieldImplEntry?`
    gives and `buildFieldReprMap` is empty. -/
theorem buildFieldImplMap_of_canon {j : Json} {newtypes : NewtypeMap}
    (h : ∀ it ∈ exportItems j, implItemNamed? (fieldImplItems it) "MONT_BITS" = none) :
    buildFieldImplMap j newtypes =
        (exportItems j).filterMap (fieldImplEntry? (exportConstBodies j) newtypes) ∧
      buildFieldReprMap j newtypes = [] := by
  have hx : ∀ it ∈ exportItems j, fieldImplReprEntry? (exportConstBodies j) newtypes it =
      (fieldImplEntry? (exportConstBodies j) newtypes it).map (·, .canon) :=
    fun it hit => fieldImplReprEntry?_of_canon (h it hit)
  constructor
  · unfold buildFieldImplMap
    clear h
    generalize exportItems j = l at hx ⊢
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.filterMap_cons]
      rw [hx a List.mem_cons_self, ih fun it hit => hx it (List.mem_cons_of_mem _ hit)]
      cases fieldImplEntry? (exportConstBodies j) newtypes a <;> rfl
  · unfold buildFieldReprMap
    rw [List.filterMap_eq_nil_iff]
    intro it hit
    rw [hx it hit]
    cases fieldImplEntry? (exportConstBodies j) newtypes it <;> rfl

/-- `ty` with every type of `names` (field newtypes, each with its inner type)
    replaced by its inner type. -/
partial def eraseFieldNewtypeTy (names : List (String × ImpType)) : ImpType → ImpType
  | .adt n args =>
    match (if args.isEmpty then names.lookup (lastPathSegment n) else none) with
    | some inner => inner
    | none => .adt n (args.map (eraseFieldNewtypeTy names))
  | .tuple es => .tuple (es.map (eraseFieldNewtypeTy names))
  | .option t => .option (eraseFieldNewtypeTy names t)
  | .result a b => .result (eraseFieldNewtypeTy names a) (eraseFieldNewtypeTy names b)
  | .controlFlow a b =>
    .controlFlow (eraseFieldNewtypeTy names a) (eraseFieldNewtypeTy names b)
  | .fn ps r => .fn (ps.map (eraseFieldNewtypeTy names)) (eraseFieldNewtypeTy names r)
  | .ref t m => .ref (eraseFieldNewtypeTy names t) m
  | .slice t => .slice (eraseFieldNewtypeTy names t)
  | .array t n => .array (eraseFieldNewtypeTy names t) n
  | t => t

/-- Whether `ty` is a type of `names`, or a reference to one. -/
def isFieldNewtypeTy (names : List (String × ImpType)) : ImpType → Bool
  | .adt n [] => names.any (·.1 == lastPathSegment n)
  | .ref t _ => isFieldNewtypeTy names t
  | _ => false

/-- A typed expression with the field newtypes `names` erased: a construction
    `T(x)` with `x` of the inner type of `T` is `x`, a projection `x.0` of an
    `x : T` is `x`, and every type of `names` in a node's type is its inner
    type (`eraseFieldNewtypeTy`). -/
partial def tEraseFieldNewtypes (names : List (String × ImpType)) (e : TExpr) : TExpr :=
  let go := tEraseFieldNewtypes names
  let rest : Unit → TExpr := fun _ =>
    match tMapChildren go e with
    | .mk k ty => .mk k (eraseFieldNewtypeTy names ty)
  match e with
  | .mk (.app f [x]) ty =>
    if (names.lookup (lastPathSegment f)).any (· == x.ty) && isFieldNewtypeTy names ty
    then go x
    else if f == ".0" && isFieldNewtypeTy names x.ty then go x
    else rest ()
  | .mk (.proj x 0) _ => if isFieldNewtypeTy names x.ty then go x else rest ()
  | _ => rest ()

/-- Parse a full hax export file into typed TExprs.
    Returns (combined ImpExpr, fnTypes, raw typed defs (with hax types preserved),
    processed typed defs (for pipeline/rendering)).

    `resolveTraitImpls := false` empties the trait-`impl` method map, so every
    method of every trait `impl` the crate defines keeps its bare name, reaches
    the generated `Deps` class and contributes no definition of its own. It is
    the uniform reading of an export whose `impl`s cannot be resolved
    consistently: a method body emitted at the concrete self type calls the
    trait methods and reads the associated constants of a further `impl`, which
    stays opaque, while the crate's generic functions call those same names at a
    type parameter — and the `Deps` class carries one field, hence one type, per
    name. `Hax.traitImplDepTypeConflicts` identifies such an export.

    `traitImplConsts := true` also resolves the associated constants of the
    crate's trait `impl`s (`buildTraitImplConstMap`): each becomes a
    definition, and a read of it through a `Concrete` atom takes its name. The
    trait-to-class emission sets it; its instances name those definitions. It
    also makes a read of an associated constant through a trait bound of a type
    parameter a nullary call, `.app "ZERO" []` (`constReadKind`).

    A call of a method declared by a trait, not resolved to a trait `impl` of
    the crate, takes the qualified head `krate::Trait::h` (`traitCallHead`)
    when `krate` is in `nominalKrates`, and, outside `traitImplConsts`, when
    `krate` is neither `primeir_hax` nor in `builtinKrates` and the unqualified
    head is a builtin head (`ImplSelfTypeMap.qualifiesTraitCall`).

    A call of a method of `primeir_hax::Field` resolved to an `impl` of
    `buildFieldImplMap` takes its modulus-tagged head (`fieldTaggedHead?`),
    and the self types of those `impl`s are erased to their inner types, `u64`
    or `[u64; n]`, in every definition and signature (`tEraseFieldNewtypes`),
    whatever the other flags.

    Projection types are read at the types `resolveAssocTypes` gives them. -/
partial def parseHaxFileWithTExpr (j : Json) (structFields : StructFieldNames := [])
    (resolveTraitImpls : Bool := true) (traitImplConsts : Bool := false)
    (nominalKrates : List String := []) :
    Except String (ImpExpr × List (String × FnTypeInfo)
                   × List (String × TExpr) × List (String × TExpr)) := do
  let j := resolveAssocTypes j
  -- Build the impl-self-type map once from the full JSON. This lets the
  -- recursive parse disambiguate user-defined methods (e.g. `Crs::len`)
  -- from stdlib ones (`slice::len`) at every Call node. `structFields`
  -- (struct name → field names, from the caller's struct metadata) lets the
  -- assignment arms lower struct-field writes to `struct_update` assignments.
  let implMap : ImplSelfTypeMap :=
    { impls := buildImplSelfTypeMap j, collisions := fnNameCollisions j,
      structFields := structFields, localCrate := localCrateOfExport j,
      traitImplMethods := if resolveTraitImpls then buildTraitImplMethodMap j else []
      traitImplConsts := if traitImplConsts then buildTraitImplConstMap j else []
      localBoundConstCalls := traitImplConsts, nominalKrates := nominalKrates
      fieldImpls := buildFieldImplMap j (buildNewtypeMap j)
      fieldReprs := buildFieldReprMap j (buildNewtypeMap j) }
  let fieldNewtypes := (implMap.fieldImpls.map fun e => (e.2.1, fieldReprTy e.2.2.2)).eraseDups
  let rec parseItemsTExpr (items : List Json) :
      Except String (List (String × TExpr × TExpr × FnTypeInfo)) := do
    let mut result : List (String × TExpr × TExpr × FnTypeInfo) := []
    for item in items do
      match ← parseHaxItemTExpr item implMap with
      | some r => result := result ++ [r]
      | none =>
        let kind := (item.getObjVal? "kind").toOption
        match kind with
        | some kindJ =>
          match kindJ.getObjVal? "Mod" with
          | .ok (.arr modData) =>
            match modData.toList[1]? with
            | some subJ =>
              match subJ with
              | .arr subItems =>
                let sub ← parseItemsTExpr subItems.toList
                result := result ++ sub
              | _ => pure ()
            | _ => pure ()
          | .ok modData =>
            match modData.getObjValAs? (Array Json) "items" with
            | .ok subItems =>
              let sub ← parseItemsTExpr subItems.toList
              result := result ++ sub
            | _ => pure ()
          | _ =>
            -- Recurse into impl blocks. An inherent impl's method becomes a
            -- top-level def `<SelfType>_<method>`, matching the name
            -- produced by `disambiguateMethodCallWithImplMap` at call
            -- sites. A trait impl's method becomes a top-level def under the
            -- name `buildTraitImplMethodMap` assigns it, matching the name
            -- `resolveTraitImplCall` gives its call sites.
            match kindJ.getObjVal? "Impl" with
            | .ok impl =>
              let isTraitImpl := match impl.getObjVal? "of_trait" with
                | .ok Json.null => false
                | .ok _ => true
                | _ => false
              if !isTraitImpl then
                -- Resolve the self-type short name. Mirrors
                -- `buildImplSelfTypeMap` (line 281) and uses
                -- `extractAdtShortName` to walk `self_ty.value.Adt`.
                let selfName : Option String := do
                  let selfTy ← (impl.getObjVal? "self_ty").toOption
                  let stVal ← (selfTy.getObjVal? "value").toOption
                  let adt ← (stVal.getObjVal? "Adt").toOption
                  extractAdtShortName adt
                match selfName, impl.getObjValAs? (Array Json) "items" with
                | some sn, .ok implItems =>
                  for implItem in implItems do
                    match ← parseHaxItemTExpr implItem implMap with
                    | some (mName, raw, proc, ti) =>
                      result := result ++ [(s!"{sn}_{mName}", raw, proc, ti)]
                    | none => pure ()
                | _, _ => pure ()
              else
                let implId : Option Nat := do
                  let oid ← (item.getObjVal? "owner_id").toOption
                  let c ← (oid.getObjVal? "contents").toOption
                  (c.getObjValAs? Nat "id").toOption
                match implId, impl.getObjValAs? (Array Json) "items" with
                | some iid, .ok implItems =>
                  for implItem in implItems do
                    match ← parseHaxItemTExpr implItem implMap with
                    | some (mName, raw, proc, ti) =>
                      match implMap.traitImplMethods.find? fun p =>
                          p.1 == iid && p.2.1 == mName with
                      | some entry => result := result ++ [(entry.2.2, raw, proc, ti)]
                      | none => pure ()
                    | none =>
                      let cName := match implItem.getObjVal? "ident" with
                        | .ok ident => extractFnName ident
                        | _ => ""
                      match implMap.traitImplConsts.find? fun p =>
                          p.1 == iid && p.2.1 == cName with
                      | some entry =>
                        match ← parseImplConstTExpr implItem implMap with
                        | some (raw, proc, ti) =>
                          result := result ++ [(entry.2.2, raw, proc, ti)]
                        | none => pure ()
                      | none => pure ()
                | _, _ => pure ()
            | _ => pure ()
        | none => pure ()
    return result
  match j with
  | .arr items =>
    let parsed ← parseItemsTExpr items.toList
    let parsed :=
      if fieldNewtypes.isEmpty then parsed
      else
        let eraseTy := eraseFieldNewtypeTy fieldNewtypes
        parsed.map fun (name, raw, proc, ti) =>
          (name, tEraseFieldNewtypes fieldNewtypes raw, tEraseFieldNewtypes fieldNewtypes proc,
            ⟨ti.paramTypes.map fun (p, t) => (p, eraseTy t), eraseTy ti.retType⟩)
    match parsed with
    | [] => throw "no functions or constants found in hax export"
    | _ =>
      let expr := parsed.foldr (fun (name, _, procTe, _) acc =>
        .letBind name procTe.erase acc) .unitVal
      let fnTypes := parsed.map fun (name, _, _, ti) => (name, ti)
      let rawTexprs := parsed.map fun (name, rawTe, _, _) => (name, rawTe)
      let procTexprs := parsed.map fun (name, _, procTe, _) => (name, procTe)
      return (expr, fnTypes, rawTexprs, procTexprs)
  | _ =>
    let te ← parseHaxTExpr j implMap
    let processed := normalizeAssignOpsTExpr (reconstructForLoopsTExpr te)
    return (processed.erase, [], [("expr", te)], [("expr", processed)])

/-! ## Struct Definition Extraction

Parse struct definitions from `hax_frontend_export.json` to generate
correct preambles (struct constructors, projections, dependency classes). -/

/-- A field in a Rust struct. -/
structure FieldInfo where
  name : String
  /-- "int" for integer scalars, "array" for Array/Vec types,
      or a struct name for nested struct types. -/
  typeTag : String
  /-- Full parsed type (when available from hax JSON). -/
  impType : ImpType := .unknown
  deriving Inhabited

/-- A Rust struct definition with its fields in order. -/
structure StructInfo where
  name : String
  fields : List FieldInfo
  deriving Inhabited

/-- Classify a hax type JSON value into "int", "array", or a struct name. -/
def classifyFieldType (tyVal : Json) : String :=
  -- Uint types: {"Uint": "U8"}, {"Uint": "U16"}, etc.
  if tyVal.getObjVal? "Uint" |>.isOk then "int"
  -- Int types: {"Int": "I8"}, etc.
  else if tyVal.getObjVal? "Int" |>.isOk then "int"
  -- Usize
  else if tyVal.getObjVal? "Usize" |>.isOk then "int"
  -- Bool
  else if tyVal.getObjVal? "Bool" |>.isOk then "int"
  -- Param: generic type parameter (e.g., `E` in `struct Foo<E> { field: E }`)
  -- In crypto crates, generic params are almost always byte arrays.
  -- Classify as "array" (safe default; will get `Array Int` type).
  else if tyVal.getObjVal? "Param" |>.isOk then "array"
  -- A type parameter kept by `Hax.ClassEmit.keepTypeParams`, classified as
  -- the `Param` it rewrites.
  else if tyVal.getObjVal? "TypeVar" |>.isOk then "array"
  -- Array: {"Array": {id: ..., value: ...}}
  else if tyVal.getObjVal? "Array" |>.isOk then "array"
  -- Slice
  else if tyVal.getObjVal? "Slice" |>.isOk then "array"
  -- Vec (common in hax)
  else if ((toString tyVal).splitOn "Vec").length > 1 then "array"
  -- Adt referencing another struct
  else if let .ok adtJ := tyVal.getObjVal? "Adt" then
    -- Try to extract the struct name from the def_id path
    -- Navigate: Adt{id,value} → value.def_id.contents.value.path
    let structName := do
      let v ← adtJ.getObjVal? "value"
      let did ← v.getObjVal? "def_id"
      let c ← did.getObjVal? "contents"
      let vi ← c.getObjVal? "value"
      let path ← vi.getObjValAs? (Array Json) "path"
      let name := path.foldl (fun (acc : String) (p : Json) =>
        match p.getObjVal? "data" with
        | .ok d => match d.getObjVal? "TypeNs" with
          | .ok (.str n) => n
          | _ => acc
        | _ => acc) ""
      if name.isEmpty then .error "empty" else .ok name
    match structName with
    | .ok n => n
    | .error _ => "array"
  else "array"  -- default to array for unknown types

/-- Parse struct definitions from a hax JSON export array.
    Returns a list of `StructInfo` for all struct items. A field typed by an
    associated type is read at the type `resolveAssocFieldType assoc` gives. -/
partial def parseStructDefs (items : List Json)
    (assoc : List (String × String × Json) := []) : List StructInfo :=
  let parseOneStruct (structData : Array Json) : Option StructInfo :=
    let name := match structData.toList with
      | (Json.arr nameSpan) :: _ => match nameSpan.toList with
        | (Json.str n) :: _ => n
        | _ => ""
      | _ => ""
    if name.isEmpty then none
    else
      -- A field definition; `ident` is the field name, which hax writes as
      -- the position (`"0"`, `"1"`, …) for a tuple struct.
      let parseField (fj : Json) : Option FieldInfo :=
        let ident := match fj.getObjVal? "ident" with
          | Except.ok (Json.arr identPair) => match identPair.toList with
            | (Json.str n) :: _ => n
            | _ => ""
          | _ => ""
        if ident.isEmpty then none
        else
          let ty := (fj.getObjVal? "ty").toOption.map (resolveAssocFieldType assoc)
          let typeTag := match ty with
            | some tyJ =>
              let tyVal := (tyJ.getObjVal? "value").toOption
              match tyVal with
              | some v => classifyFieldType v
              | none => "array"
            | none => "array"
          let impTy := match ty with
            | some tyJ => parseHaxType tyJ
            | none => ImpType.unknown
          some { name := ident, typeTag := typeTag, impType := impTy : FieldInfo }
      let variantData := structData.toList[2]?
      match variantData with
      | some vd =>
        let structFields := vd.getObjVal? "Struct" |>.toOption
        match structFields with
        | some sf =>
          let fieldsJ := sf.getObjValAs? (Array Json) "fields" |>.toOption
          match fieldsJ with
          | some fields =>
            some { name := name, fields := fields.toList.filterMap parseField : StructInfo }
          | none => none
        | none =>
          -- A unit struct (`struct X;`, variant data `Unit`) is a struct with
          -- no fields. A tuple struct (`Tuple` variant data) is a struct with
          -- positional fields `0`, `1`, … unless it has exactly one field:
          -- `struct T(Inner)` is a newtype, which `buildNewtypeMap` collects.
          if (vd.getObjVal? "Unit").toOption.isSome then
            some { name := name, fields := [] : StructInfo }
          else match vd.getObjVal? "Tuple" with
            | .ok (Json.arr tupleData) => match tupleData.toList with
              | (Json.arr fields) :: _ =>
                if fields.size == 1 then none
                else some { name := name, fields := fields.toList.filterMap parseField : StructInfo }
              | _ => none
            | _ => none
      | none => none
  items.foldl (fun acc item =>
    let kind := (item.getObjVal? "kind").toOption
    match kind with
    | some kindJ =>
      -- Recurse into Mod items: kind.Mod = [name_data, [sub_items]]
      let modStructs := match kindJ.getObjVal? "Mod" with
        | Except.ok (Json.arr modData) =>
          match modData.toList[1]? with
          | some (Json.arr subItems) => parseStructDefs subItems.toList assoc
          | _ => []
        | _ => []
      let thisStruct := match kindJ.getObjVal? "Struct" with
        | Except.ok (Json.arr sd) => parseOneStruct sd
        | _ => none
      acc ++ modStructs ++ thisStruct.toList
    | none => acc) []

/-- Parse struct defs from a top-level hax JSON (array of items), with the
    associated types of the export's trait `impl` blocks (`implAssocTypes`). -/
def parseStructDefsFromJson (j : Json) : List StructInfo :=
  let raw := match j with
    | .arr items => parseStructDefs items.toList (implAssocTypes j)
    | _ => []
  -- Deduplicate by struct name (keep first occurrence)
  raw.foldl (fun acc si =>
    if acc.any (·.name == si.name) then acc else acc ++ [si]) []

/-- A Rust `pub type X = T` alias.  `name` is the alias name; `body` is the
    underlying `ImpType` (e.g. `Vector UInt8 32` for `pub type Scalar = [u8; 32]`).
    Generics are not yet supported (most crypto-protocol aliases are monomorphic). -/
structure TypeAliasInfo where
  name : String
  body : ImpType
  deriving Inhabited

/-- Parse `TyAlias` items from a hax JSON export array. -/
partial def parseTypeAliasDefs (items : List Json) : List TypeAliasInfo :=
  let parseOneAlias (aliasData : Array Json) : Option TypeAliasInfo :=
    let name := match aliasData.toList with
      | (Json.arr nameSpan) :: _ => match nameSpan.toList with
        | (Json.str n) :: _ => n
        | _ => ""
      | _ => ""
    if name.isEmpty then none
    else
      let body := match aliasData.toList[2]? with
        | some bodyJ => parseHaxType bodyJ
        | none => ImpType.unknown
      some { name := name, body := body : TypeAliasInfo }
  items.foldl (fun acc item =>
    let kind := (item.getObjVal? "kind").toOption
    match kind with
    | some kindJ =>
      let modAliases := match kindJ.getObjVal? "Mod" with
        | Except.ok (Json.arr modData) =>
          match modData.toList[1]? with
          | some (Json.arr subItems) => parseTypeAliasDefs subItems.toList
          | _ => []
        | _ => []
      let thisAlias := match kindJ.getObjVal? "TyAlias" with
        | Except.ok (Json.arr ad) => parseOneAlias ad
        | _ => none
      acc ++ modAliases ++ thisAlias.toList
    | none => acc) []

/-- Parse `TyAlias` defs from a top-level hax JSON (array of items),
    deduplicating by alias name. -/
def parseTypeAliasDefsFromJson (j : Json) : List TypeAliasInfo :=
  let raw := match j with
    | .arr items => parseTypeAliasDefs items.toList
    | _ => []
  raw.foldl (fun acc a =>
    if acc.any (·.name == a.name) then acc else acc ++ [a]) []

/-- One variant of a Rust enum. `payload` is the list of positional
    field types; `[]` means a unit variant. Tuple variants
    (`Foo(A, B)`) and struct variants (`Foo { x: A, y: B }`) are
    flattened to their positional shape; field names are dropped
    (downstream we always pattern-match positionally). -/
structure EnumVariantInfo where
  name : String
  payload : List ImpType := []
  deriving Inhabited

/-- A Rust enum definition: name + variants. -/
structure EnumInfo where
  name : String
  variants : List EnumVariantInfo
  deriving Inhabited

/-- Parse the positional payload types of one enum variant from its
    hax JSON. Returns `[]` for unit variants. Handles two shapes:

      `data: {"Tuple": [[field, ...], ...]}`    — tuple variant
      `data: {"Struct": {"fields": [...]}}`     — struct variant

    For both, we extract each field's `ty` via `parseHaxType`. The
    field name is dropped — we emit a positional constructor.
    Unit variants have no `data` field (or `data` absent / null). -/
def parseEnumVariantPayload (variantJ : Json) : List ImpType :=
  let dataJ := match variantJ.getObjVal? "data" with
    | .ok v => v
    | _ => Json.null
  -- Tuple variant
  let fromTuple : List ImpType :=
    match dataJ.getObjVal? "Tuple" with
    | .ok (Json.arr tupArr) =>
      match tupArr.toList with
      | (Json.arr fields) :: _ =>
        fields.toList.filterMap fun fj =>
          match fj.getObjVal? "ty" with
          | .ok tyJ => some (parseHaxType tyJ)
          | _ => none
      | _ => []
    | _ => []
  if !fromTuple.isEmpty then fromTuple else
  -- Struct variant
  match dataJ.getObjVal? "Struct" with
  | .ok structJ =>
    match structJ.getObjValAs? (Array Json) "fields" with
    | .ok fields =>
      fields.toList.filterMap fun fj =>
        match fj.getObjVal? "ty" with
        | .ok tyJ => some (parseHaxType tyJ)
        | _ => none
    | _ => []
  | _ => []

/-- Parse Rust enum definitions from a hax JSON export array.
    Hax encodes `kind.Enum` as `[[name, name_span], generics, variants_array]`
    where each variant is `{ident: [variant_name, span], data: ..., ...}`. -/
partial def parseEnumDefs (items : List Json) : List EnumInfo :=
  let parseOneEnum (enumData : Array Json) : Option EnumInfo :=
    -- enumData = [name_with_span, generics, variants]
    let name := match enumData.toList with
      | (Json.arr nameSpan) :: _ => match nameSpan.toList with
        | (Json.str n) :: _ => n
        | _ => ""
      | _ => ""
    if name.isEmpty then none
    else
      let variantsJ := enumData.toList[2]?
      match variantsJ with
      | some (Json.arr variantList) =>
        let variants := variantList.toList.filterMap fun vj =>
          match vj.getObjVal? "ident" with
          | Except.ok (Json.arr identPair) => match identPair.toList with
            | (Json.str n) :: _ =>
              some ({ name := n, payload := parseEnumVariantPayload vj } : EnumVariantInfo)
            | _ => none
          | _ => none
        some { name := name, variants := variants }
      | _ => none
  items.foldl (fun acc item =>
    let kind := (item.getObjVal? "kind").toOption
    match kind with
    | some kindJ =>
      -- Recurse into Mod items: kind.Mod = [name_data, [sub_items]]
      let modEnums := match kindJ.getObjVal? "Mod" with
        | Except.ok (Json.arr modData) =>
          match modData.toList[1]? with
          | some (Json.arr subItems) => parseEnumDefs subItems.toList
          | _ => []
        | _ => []
      let thisEnum := match kindJ.getObjVal? "Enum" with
        | Except.ok (Json.arr ed) => parseOneEnum ed
        | _ => none
      acc ++ modEnums ++ thisEnum.toList
    | none => acc) []

/-- Parse enum defs from a top-level hax JSON (array of items). -/
def parseEnumDefsFromJson (j : Json) : List EnumInfo :=
  let raw := match j with
    | .arr items => parseEnumDefs items.toList
    | _ => []
  -- Deduplicate by enum name (keep first occurrence)
  raw.foldl (fun acc ei =>
    if acc.any (·.name == ei.name) then acc else acc ++ [ei]) []

end Hax.HaxAdapter

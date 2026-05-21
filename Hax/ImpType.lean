/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-!
# Simplified Rust Type Representation

`ImpType` models a post-monomorphization subset of Rust's type system.
Types are fully instantiated (no polymorphism) and come directly from
the hax frontend — no type inference is needed.

This is used by `TExpr` to annotate every subexpression with its type,
mirroring hax's `Decorated<ExprKind>` pattern.
-/

namespace Hax

/-- Fixed-width integer width, matching Rust's integer types. -/
inductive IntWidth where
  | w8 | w16 | w32 | w64 | w128 | wsize
  deriving Inhabited, BEq, Repr, DecidableEq

namespace IntWidth

/-- Number of bits for this width. `wsize` is 64 bits (64-bit platforms). -/
def bits : IntWidth → Nat
  | .w8 => 8 | .w16 => 16 | .w32 => 32 | .w64 => 64 | .w128 => 128 | .wsize => 64

/-- The modulus `2^bits` for unsigned wrapping arithmetic. -/
def modulus (w : IntWidth) : Nat := 2 ^ w.bits

/-- Display name for code generation. -/
def toSuffix : IntWidth → String
  | .w8 => "u8" | .w16 => "u16" | .w32 => "u32" | .w64 => "u64"
  | .w128 => "u128" | .wsize => "usize"

/-- Lean 4 type name for this width. -/
def toLeanType : IntWidth → String
  | .w8 => "UInt8" | .w16 => "UInt16" | .w32 => "UInt32" | .w64 => "UInt64"
  | .w128 => "UInt128" | .wsize => "USize"

/-- Suffix for signed code generation. -/
def toSignedSuffix : IntWidth → String
  | .w8 => "i8" | .w16 => "i16" | .w32 => "i32" | .w64 => "i64"
  | .w128 => "i128" | .wsize => "isize"

/-- Lean 4 type name for signed integers (all map to Int for now). -/
def toSignedLeanType : IntWidth → String
  | _ => "Int"

end IntWidth

/-- Simplified Rust type representation (post-monomorphization). -/
inductive ImpType where
  | bool
  | int                                      -- arbitrary-precision (backward compat)
  | uint (w : IntWidth)                      -- unsigned fixed-width
  | sint (w : IntWidth)                      -- signed fixed-width
  | unit
  | str
  | tuple (elems : List ImpType)
  | option (inner : ImpType)
  | result (ok err : ImpType)
  | controlFlow (brk cont : ImpType)
  | adt (name : String) (args : List ImpType)
  | fn (params : List ImpType) (ret : ImpType)
  | ref (inner : ImpType) (isMut : Bool)
  | slice (inner : ImpType)
  | array (inner : ImpType) (len : Nat)
  | typeVar (name : String)
  | unknown
  deriving Inhabited

namespace ImpType

/-- Structural equality for `ImpType`. Manual because nested `List ImpType`
    prevents `deriving BEq`. -/
def beq : ImpType → ImpType → Bool
  | .bool, .bool => true
  | .int, .int => true
  | .uint w₁, .uint w₂ => w₁ == w₂
  | .sint w₁, .sint w₂ => w₁ == w₂
  | .unit, .unit => true
  | .str, .str => true
  | .tuple e₁, .tuple e₂ => beqList e₁ e₂
  | .option a, .option b => beq a b
  | .result a₁ b₁, .result a₂ b₂ => beq a₁ a₂ && beq b₁ b₂
  | .controlFlow a₁ b₁, .controlFlow a₂ b₂ => beq a₁ a₂ && beq b₁ b₂
  | .adt n₁ a₁, .adt n₂ a₂ => n₁ == n₂ && beqList a₁ a₂
  | .fn p₁ r₁, .fn p₂ r₂ => beqList p₁ p₂ && beq r₁ r₂
  | .ref a₁ b₁, .ref a₂ b₂ => beq a₁ a₂ && b₁ == b₂
  | .slice a, .slice b => beq a b
  | .array a₁ n₁, .array a₂ n₂ => beq a₁ a₂ && n₁ == n₂
  | .typeVar n₁, .typeVar n₂ => n₁ == n₂
  | .unknown, .unknown => true
  | _, _ => false
where
  beqList : List ImpType → List ImpType → Bool
    | [], [] => true
    | a :: r₁, b :: r₂ => beq a b && beqList r₁ r₂
    | _, _ => false

instance : BEq ImpType := ⟨beq⟩

end ImpType

namespace ImpType

/-- Extract the integer width if this is a fixed-width integer type. -/
def intWidth? : ImpType → Option IntWidth
  | .uint w => some w
  | .sint w => some w
  | _ => none

/-- Is this a fixed-width unsigned integer type? -/
def isUint : ImpType → Bool
  | .uint _ => true
  | _ => false

/-- Is this a signed integer type? -/
def isSigned : ImpType → Bool
  | .sint _ => true
  | _ => false

/-- Is this the unknown type (unresolved or unsupported)? -/
def isUnknown : ImpType → Bool
  | .unknown => true
  | _ => false

/-- Is this an integer-like type (int, uint, or sint)? -/
def isIntLike : ImpType → Bool
  | .int => true
  | .uint _ => true
  | .sint _ => true
  | _ => false

/-- Rust standard-library types that should NOT be preserved as opaque
    axioms. These are iterator adapters, format helpers, ranges, etc. —
    handled by the Lean runtime's polymorphic combinators (`Hax.into_iter`,
    `Hax.next`, etc.) and have no protocol meaning. They collapse to
    `Int` (the untyped runtime placeholder) in surface emission. -/
def isStdlibCollapseName (n : String) : Bool :=
  match n with
  -- Iterator adapters (core::iter::*)
  | "Iter" | "IterMut" | "IntoIter" | "Zip" | "Chain" | "Map"
  | "FilterMap" | "Filter" | "FlatMap" | "Flatten" | "Take" | "TakeWhile"
  | "Skip" | "SkipWhile" | "Enumerate" | "Rev" | "Cycle" | "Fuse"
  | "Inspect" | "Empty" | "Once" | "OnceWith" | "Repeat" | "RepeatWith"
  | "Successors" | "FromFn" | "StepBy" | "Peekable" | "Scan"
  -- Ranges (core::ops::*)
  | "Range" | "RangeInclusive" | "RangeFrom" | "RangeTo"
  | "RangeToInclusive" | "RangeFull"
  -- Formatting (core::fmt::*)
  | "Arguments" | "Formatter"
  -- Allocator (std::alloc) — hax surfaces `Vec<u8>`'s allocator param
  | "Global"
  -- typenum stdlib types (Rust type-level numerics). NOTE: GenericArray
  -- is treated specially as an array wrapper, not collapsed here.
  | "UInt" | "UTerm" | "B0" | "B1"
  -- AssertKind appears from core::macros::Eq (assert_eq machinery)
  | "AssertKind"
  -- Other common Rust stdlib types we don't carry semantics for
  | "Cow" | "Borrow" | "Drain" => true
  | _ => false

/-- Sanitize a Rust path/identifier into a valid Lean identifier.
    Strips path prefix (keeps last `::` segment), then maps non-alphanum
    chars to `_`. Used to preserve opaque ADT names through the emit
    instead of collapsing them to `Int`. -/
def sanitizeAdtShortName (name : String) : String :=
  let short := match name.splitOn "::" with
    | [] => name
    | segs => segs.getLast!
  -- Strip generic args if present: `MyType<u8, u32>` → `MyType`
  let bareIdent := (short.splitOn "<").head!
  -- Replace any non-alphanum/non-underscore char with underscore
  let chars := bareIdent.toList.map fun c =>
    if c.isAlphanum || c == '_' then c else '_'
  let s := String.mk chars
  -- Lean identifiers must start with a letter or underscore
  if s.isEmpty || (s.front.isDigit) then "T_" ++ s else s

/-- Walk a type and return the set of "opaque" ADT short names — names that
    are not in `structLookup` and not a recognized wrapper (Vec/Box/Option/
    Result). These are the names that would otherwise collapse to `Int`
    in the surface stringifier; they need `axiom <Name> : Type` declarations
    emitted at the top of the certified file so Lean has a target type. -/
partial def collectOpaqueAdtNames (structLookup : String → Option String := fun _ => none) :
    ImpType → List String
  | .adt name args =>
    let argNames := args.foldl (fun acc a => acc ++ a.collectOpaqueAdtNames structLookup) []
    if structLookup name |>.isSome then argNames
    else if name == "Vec" || name.endsWith "::Vec"
        || name == "Box" || name.endsWith "::Box"
        || name == "Option" || name.endsWith "::Option"
        || name == "Result" || name.endsWith "::Result" then argNames
    else
      let short := sanitizeAdtShortName name
      if structLookup short |>.isSome then argNames
      -- Stdlib iterator/range/format types collapse to Int — no axiom.
      else if isStdlibCollapseName short then argNames
      else short :: argNames
  | .tuple es => es.foldl (fun acc a => acc ++ a.collectOpaqueAdtNames structLookup) []
  | .option inner => inner.collectOpaqueAdtNames structLookup
  | .result a b => a.collectOpaqueAdtNames structLookup ++ b.collectOpaqueAdtNames structLookup
  | .controlFlow a b => a.collectOpaqueAdtNames structLookup ++ b.collectOpaqueAdtNames structLookup
  | .ref inner _ => inner.collectOpaqueAdtNames structLookup
  | .slice inner => inner.collectOpaqueAdtNames structLookup
  | .array inner _ => inner.collectOpaqueAdtNames structLookup
  | _ => []

/-- Convert an ImpType to a Lean 4 type string for code generation.
    `structLookup` resolves ADT names to their Lean tuple type strings. -/
partial def toLeanTypeStr (ty : ImpType) (structLookup : String → Option String := fun _ => none) : String :=
  match ty with
  | .bool => "Bool"
  | .int => "Int"
  | .uint w => w.toLeanType
  | .sint w => w.toSignedLeanType
  | .unit => "Unit"
  | .str => "String"
  | .tuple elems =>
    if elems.isEmpty then "Unit"
    else
      let strs := elems.map fun e =>
        let s := e.toLeanTypeStr structLookup
        if (s.splitOn " × ").length > 1 then s!"({s})" else s
      " × ".intercalate strs
  | .option inner => s!"Option ({inner.toLeanTypeStr structLookup})"
  | .result ok err =>
    s!"Except ({err.toLeanTypeStr structLookup}) ({ok.toLeanTypeStr structLookup})"
  | .controlFlow brk cont =>
    s!"ControlFlow ({brk.toLeanTypeStr structLookup}) ({cont.toLeanTypeStr structLookup})"
  | .adt name args =>
    -- Check struct lookup first
    match structLookup name with
    | some s => s
    | none =>
      -- Vec/Array → Array inner (Vec has 2 generic args: elem type + allocator)
      if name == "Vec" || name.endsWith "::Vec" then
        match args with
        | inner :: _ => s!"Array ({inner.toLeanTypeStr structLookup})"
        | _ => "Array Int"
      -- GenericArray<T, N> from the `generic-array` crate is semantically
      -- an array of T (length encoded in N via typenum). Collapse like Vec.
      else if name == "GenericArray" || name.endsWith "::GenericArray" then
        match args with
        | inner :: _ => s!"Array ({inner.toLeanTypeStr structLookup})"
        | _ => "Array Int"
      else if name == "Box" || name.endsWith "::Box" then
        match args with
        | inner :: _ => inner.toLeanTypeStr structLookup
        | _ => "Int"
      else if name == "Option" || name.endsWith "::Option" then
        match args with
        | inner :: _ => s!"Option ({inner.toLeanTypeStr structLookup})"
        | _ => "Option Int"
      else if name == "Result" || name.endsWith "::Result" then
        match args with
        | ok :: err :: _ =>
          s!"Except ({err.toLeanTypeStr structLookup}) ({ok.toLeanTypeStr structLookup})"
        | ok :: _ => s!"Except Int ({ok.toLeanTypeStr structLookup})"
        | _ => "Except Int Int"
      else
        -- Try matching the sanitized last segment of the Rust path against
        -- structLookup. e.g., "softspoken_hax::types::WordVec" → try "WordVec".
        let shortName := sanitizeAdtShortName name
        match structLookup shortName with
        | some s => s
        | none =>
          -- Stdlib iterator/range/format types collapse to Int (no axiom).
          if isStdlibCollapseName shortName then "Int"
          else
            -- Preserve opaque ADT name. Mirrors the surface-stringifier change;
            -- the emitter declares `axiom <ShortName> : Type` for any name that
            -- reaches this branch.
            shortName
  | .fn _ _ => "Int"  -- function types collapse to Int in untyped mode
  | .ref inner _ => inner.toLeanTypeStr structLookup
  | .slice inner => s!"Array ({inner.toLeanTypeStr structLookup})"
  | .array inner len => s!"Vector {inner.toLeanTypeStr structLookup} {len}"
  | .typeVar _ => "Int"
  | .unknown => "Int"

/-- Convert an ImpType to a surface Lean type string, collapsing all
    integer-like types to `Int` and array/vector types to `Array (Int)`.
    This produces types compatible with the untyped Runtime (Hax.add etc.
    are polymorphic over `Int`). Structural types (Bool, Option, tuples)
    are preserved. -/
partial def toLeanTypeStrSurface (ty : ImpType)
    (structLookup : String → Option String := fun _ => none) : String :=
  match ty with
  | .bool => "Bool"
  | .int | .uint _ | .sint _ | .typeVar _ | .unknown | .fn _ _ => "Int"
  | .unit => "Unit"
  | .str => "String"
  | .tuple elems =>
    if elems.isEmpty then "Unit"
    else
      let strs := elems.map fun e =>
        let s := e.toLeanTypeStrSurface structLookup
        if (s.splitOn " × ").length > 1 then s!"({s})" else s
      " × ".intercalate strs
  | .option inner => s!"Option ({inner.toLeanTypeStrSurface structLookup})"
  | .result ok err =>
    s!"Except ({err.toLeanTypeStrSurface structLookup}) ({ok.toLeanTypeStrSurface structLookup})"
  | .controlFlow brk cont =>
    s!"ControlFlow ({brk.toLeanTypeStrSurface structLookup}) ({cont.toLeanTypeStrSurface structLookup})"
  | .adt name args =>
    match structLookup name with
    | some s => s
    | none =>
      if name == "Vec" || name.endsWith "::Vec" then
        match args with
        | inner :: _ => s!"Array ({inner.toLeanTypeStrSurface structLookup})"
        | _ => "Array (Int)"
      -- GenericArray<T, N> from `generic-array` crate → Array T (length
      -- encoded via typenum N).
      else if name == "GenericArray" || name.endsWith "::GenericArray" then
        match args with
        | inner :: _ => s!"Array ({inner.toLeanTypeStrSurface structLookup})"
        | _ => "Array (Int)"
      else if name == "Box" || name.endsWith "::Box" then
        match args with
        | inner :: _ => inner.toLeanTypeStrSurface structLookup
        | _ => "Int"
      else if name == "Option" || name.endsWith "::Option" then
        match args with
        | inner :: _ => s!"Option ({inner.toLeanTypeStrSurface structLookup})"
        | _ => "Option Int"
      else if name == "Result" || name.endsWith "::Result" then
        match args with
        | ok :: err :: _ =>
          s!"Except ({err.toLeanTypeStrSurface structLookup}) ({ok.toLeanTypeStrSurface structLookup})"
        | ok :: _ => s!"Except Int ({ok.toLeanTypeStrSurface structLookup})"
        | _ => "Except Int Int"
      else
        let shortName := sanitizeAdtShortName name
        match structLookup shortName with
        | some s => s
        | none =>
          -- Stdlib iterator/range/format types collapse to Int (no axiom).
          if isStdlibCollapseName shortName then "Int"
          else
            -- Preserve opaque ADT name instead of collapsing to `Int`.
            -- The emitter declares `axiom <ShortName> : Type` at the top of
            -- the certified file via `collectOpaqueAdtNames`, so Lean sees
            -- this name as a valid (uninhabited) type. Consumers provide
            -- concrete instances via the bridge-adapter pattern.
            shortName
  | .ref inner _ => inner.toLeanTypeStrSurface structLookup
  | .slice inner => s!"Array ({inner.toLeanTypeStrSurface structLookup})"
  | .array inner _ => s!"Array ({inner.toLeanTypeStrSurface structLookup})"

/-- Precise type rendering that preserves fixed-size byte arrays as
    `Vector UInt8 N`.  Used by item-level emitters that want type-rich
    output (e.g. `pub type` alias bodies, typed deps class signatures).
    Other primitive types still collapse to `Int` for compatibility
    with the untyped Runtime. -/
partial def toLeanTypeStrPrecise (ty : ImpType)
    (structLookup : String → Option String := fun _ => none) : String :=
  match ty with
  | .array inner len =>
    match inner with
    | .uint .w8 => s!"Vector UInt8 {len}"
    | _ => s!"Array ({inner.toLeanTypeStrSurface structLookup})"
  | _ => ty.toLeanTypeStrSurface structLookup

end ImpType

/-- Type information for a Rust function (parameter names+types, return type).
    Defined here so both HaxAdapter and PrettyPrint can use it. -/
structure FnTypeInfo where
  paramTypes : List (String × ImpType)
  retType : ImpType
  deriving Inhabited

end Hax

/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/

/-!
# Simplified Rust Type Representation

`ImpType` models a post-monomorphization subset of Rust's type system.
Types are fully instantiated (no polymorphism) and come directly from
the hax frontend — no type inference is needed.

This is used by `TExpr` to annotate every subexpression with its type,
mirroring hax's `Decorated<ExprKind>` pattern.
-/

namespace SSProve.Hax

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

/-- Convert an ImpType to a Lean 4 type string for code generation.
    `structLookup` resolves ADT names to their Lean tuple type strings. -/
partial def toLeanTypeStr (ty : ImpType) (structLookup : String → Option String := fun _ => none) : String :=
  match ty with
  | .bool => "Bool"
  | .int => "Int"
  | .uint _ => "Int"  -- In untyped extraction mode, all integers map to Int
  | .sint _ => "Int"
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
      else if name == "Box" || name.endsWith "::Box" then
        match args with
        | inner :: _ => inner.toLeanTypeStr structLookup
        | _ => "Int"
      else "Int"  -- unknown ADT
  | .fn _ _ => "Int"  -- function types collapse to Int in untyped mode
  | .ref inner _ => inner.toLeanTypeStr structLookup
  | .slice inner => s!"Array ({inner.toLeanTypeStr structLookup})"
  | .array inner _ => s!"Array ({inner.toLeanTypeStr structLookup})"
  | .typeVar _ => "Int"
  | .unknown => "Int"

end ImpType

/-- Type information for a Rust function (parameter names+types, return type).
    Defined here so both HaxAdapter and PrettyPrint can use it. -/
structure FnTypeInfo where
  paramTypes : List (String × ImpType)
  retType : ImpType
  deriving Inhabited

end SSProve.Hax

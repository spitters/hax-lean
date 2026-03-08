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

/-- Simplified Rust type representation (post-monomorphization). -/
inductive ImpType where
  | bool
  | int
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

end SSProve.Hax

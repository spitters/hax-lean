/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import HaxLean.AST

/-!
# Values and Environments

Untyped runtime values and variable environments for the imperative
expression semantics. Using a tagged union avoids formalizing the Rust
type system while still being expressive enough for correctness proofs.
-/

namespace Hax

/-- Runtime values — untyped tagged union.

    Width-aware integer values (`uint`, `sint`) carry their bit width,
    enabling exact Rust wrapping semantics. The legacy `int` constructor
    is preserved for backward compatibility with existing untyped proofs.
    Array values support fixed-size arrays and slices. -/
inductive Value where
  | bool (b : Bool)
  | int (n : Int)
  | uint (w : IntWidth) (v : Nat)            -- unsigned fixed-width (v < w.modulus)
  | sint (w : IntWidth) (v : Int)            -- signed fixed-width
  | unit
  | tuple (vs : List Value)
  | array (vs : List Value)                  -- array/slice
  | option (v : Option Value)
  | result (ok : Bool) (payload : Value)     -- true = Ok, false = Err
  | controlFlow (isBreak : Bool) (payload : Value)  -- true = Break, false = Continue
  deriving Inhabited, BEq, Repr

namespace Value

/-- Coerce a literal to a value. -/
def ofLit : ImpLit → Value
  | .bool b => .bool b
  | .int n => .int n
  | .unit => .unit
  | .uintLit w n => .uint w (n % w.modulus)
  | .sintLit w n => .sint w n

/-- Try to extract a Bool. -/
def toBool : Value → Option Bool
  | .bool b => some b
  | _ => none

/-- Try to extract an Int (works for both typed and untyped integers). -/
def toInt : Value → Option Int
  | .int n => some n
  | .uint _ v => some (v : Int)
  | .sint _ v => some v
  | _ => none

/-- Try to extract an unsigned integer with its width. -/
def toUint : Value → Option (IntWidth × Nat)
  | .uint w v => some (w, v)
  | .int n => if 0 ≤ n then some (.w64, n.toNat) else none
  | _ => none

/-- Try to extract tuple elements. -/
def toTuple : Value → Option (List Value)
  | .tuple vs => some vs
  | _ => none

/-- Try to extract array elements. -/
def toArray : Value → Option (List Value)
  | .array vs => some vs
  | .tuple vs => some vs  -- backward compat: tuples can act as arrays
  | _ => none

/-- Project the i-th component of a tuple or array. -/
def projIdx (v : Value) (i : Nat) : Option Value :=
  match v with
  | .tuple vs => vs[i]?
  | .array vs => vs[i]?
  | _ => none

/-- Array/slice length. -/
def arrayLen : Value → Option Nat
  | .array vs => some vs.length
  | .tuple vs => some vs.length
  | _ => none

end Value

/-- Variable environment: maps variable names to values.

    Using a total function with `Option` keeps the type simple and avoids
    needing Finmap. `none` means the variable is not in scope. -/
abbrev Env := String → Option Value

namespace Env

/-- The empty environment. -/
def empty : Env := fun _ => none

instance : Inhabited Env := ⟨empty⟩

/-- Extend the environment with a single binding. -/
def extend (env : Env) (name : String) (v : Value) : Env :=
  fun x => if x == name then some v else env x

/-- Restrict the environment to only the given variable names. -/
def restrict (env : Env) (names : List String) : Env :=
  fun x => if names.contains x then env x else none

/-- Remove a variable from the environment. -/
def remove (env : Env) (name : String) : Env :=
  fun x => if x == name then none else env x

@[simp]
theorem extend_same (env : Env) (name : String) (v : Value) :
    (env.extend name v) name = some v := by
  simp [extend]

@[simp]
theorem extend_other (env : Env) (name : String) (v : Value)
    (x : String) (h : x ≠ name) :
    (env.extend name v) x = env x := by
  simp only [extend, beq_iff_eq]
  exact if_neg h

end Env

/-- Bind a pattern match result to the environment.
    Returns `none` if the pattern doesn't match the value. -/
def matchPat : ImpPat → Value → Env → Option Env
  | .wildcard, _, env => some env
  | .litPat l, v', env => if Value.ofLit l == v' then some env else none
  | .varPat name, v', env => some (env.extend name v')
  | .tuplePat pats, .tuple vs, env =>
    if pats.length != vs.length then none
    else matchPatList pats vs env
  | .tuplePat pats, .array vs, env =>
    if pats.length != vs.length then none
    else matchPatList pats vs env
  | .somePat p', .option (some v'), env => matchPat p' v' env
  | .nonePat, .option none, env => some env
  | .okPat p', .result true v', env => matchPat p' v' env
  | .errPat p', .result false v', env => matchPat p' v' env
  | _, _, _ => none
where
  /-- Match a list of patterns against a list of values, threading the env. -/
  matchPatList : List ImpPat → List Value → Env → Option Env
    | [], [], env => some env
    | p :: ps, v :: vs, env => do
      let env' ← matchPat p v env
      matchPatList ps vs env'
    | _, _, _ => none

end Hax

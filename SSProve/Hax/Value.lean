/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.AST

/-!
# Values and Environments

Untyped runtime values and variable environments for the imperative
expression semantics. Using a tagged union avoids formalizing the Rust
type system while still being expressive enough for correctness proofs.
-/

namespace SSProve.Hax

/-- Runtime values — untyped tagged union. -/
inductive Value where
  | bool (b : Bool)
  | int (n : Int)
  | unit
  | tuple (vs : List Value)
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

/-- Try to extract a Bool. -/
def toBool : Value → Option Bool
  | .bool b => some b
  | _ => none

/-- Try to extract an Int. -/
def toInt : Value → Option Int
  | .int n => some n
  | _ => none

/-- Try to extract tuple elements. -/
def toTuple : Value → Option (List Value)
  | .tuple vs => some vs
  | _ => none

/-- Project the i-th component of a tuple. -/
def projIdx (v : Value) (i : Nat) : Option Value :=
  match v with
  | .tuple vs => vs[i]?
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

end SSProve.Hax

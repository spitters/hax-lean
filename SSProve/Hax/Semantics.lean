/-
Copyright (c) 2025 SSProve-Lean4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSProve-Lean4 Contributors
-/
import SSProve.Hax.AST
import SSProve.Hax.Value

/-!
# Fuel-Bounded Big-Step Semantics

Denotational semantics for `ImpExpr` using `StateM Env Outcome`.
A fuel parameter ensures termination for loops; correctness theorems
are parametric in the fuel.

## Main definitions

* `Outcome` — result of evaluating an expression
* `denote` — fuel-bounded big-step denotation

## Design

We use `StateM Env Outcome` matching the `interpDet : StateM Heap α`
pattern from `Deep/DeterministicInterp.lean`. The `Outcome` type tracks
non-local control flow (early return, break, continue) explicitly.

Loop helpers (`denoteForLoop`, `denoteWhile`) are in a mutual block with
`denote`. List evaluation (`denoteArgs`) and match dispatch
(`denoteMatchArms`) are also mutual.

Termination uses a lexicographic measure `(fuel, sizeOf expr)`:
- Most `denote` cases decrease `sizeOf` with `fuel` fixed.
- Loop helpers decrease `fuel` when iterating, and their calls to
  `denote body` decrease `sizeOf` relative to the helper's measure.
-/

namespace SSProve.Hax

/-- Outcome of evaluating an expression. -/
inductive Outcome where
  | val (v : Value)
  | earlyRet (v : Value)
  | broke (v : Value)
  | continued
  | err (msg : String)
  deriving Inhabited, BEq, Repr

namespace Outcome

def isVal : Outcome → Bool
  | .val _ => true
  | _ => false

def toVal : Outcome → Option Value
  | .val v => some v
  | _ => none

end Outcome

/-- A built-in function table. -/
abbrev Builtins := String → List Value → Option Value

/-- Default builtins: arithmetic, comparisons, etc. -/
def defaultBuiltins : Builtins
  | "add", [.int a, .int b] => some (.int (a + b))
  | "sub", [.int a, .int b] => some (.int (a - b))
  | "mul", [.int a, .int b] => some (.int (a * b))
  | "neg", [.int a] => some (.int (-a))
  | "eq", [a, b] => some (.bool (a == b))
  | "ne", [a, b] => some (.bool (!(a == b)))
  | "lt", [.int a, .int b] => some (.bool (a < b))
  | "le", [.int a, .int b] => some (.bool (a ≤ b))
  | "gt", [.int a, .int b] => some (.bool (a > b))
  | "ge", [.int a, .int b] => some (.bool (a ≥ b))
  | "not", [.bool b] => some (.bool !b)
  | "and", [.bool a, .bool b] => some (.bool (a && b))
  | "or", [.bool a, .bool b] => some (.bool (a || b))
  | "Some", [v] => some (.option (some v))
  | "None", [] => some (.option none)
  | "Ok", [v] => some (.result true v)
  | "Err", [v] => some (.result false v)
  | _, _ => none

theorem ImpExpr.sizeOf_pos (e : ImpExpr) : 0 < sizeOf e := by
  cases e <;> (dsimp [sizeOf, SizeOf.sizeOf, ImpExpr._sizeOf_1]; omega)

mutual

/-- Big-step denotational semantics with fuel for termination.

    The `fuel` parameter bounds loop iterations. Non-loop constructs
    do not consume fuel. `bi` provides builtin function implementations. -/
def denote (bi : Builtins) (fuel : Nat) : ImpExpr → StateM Env Outcome
  | .lit v => pure (.val (Value.ofLit v))
  | .var name => do
    let env ← get
    match env name with
    | some v => pure (.val v)
    | none => pure (.err s!"undefined variable: {name}")
  | .letBind name val body => do
    let rv ← denote bi fuel val
    match rv with
    | .val v => do modify (Env.extend · name v); denote bi fuel body
    | other => pure other
  | .app f args => do
    let mvals ← denoteArgs bi fuel args
    match mvals with
    | some vals =>
      match bi f vals with
      | some v => pure (.val v)
      | none => pure (.err s!"unknown function or bad args: {f}")
    | none => pure (.err "non-value in function arguments")
  | .tuple elems => do
    let mvals ← denoteArgs bi fuel elems
    match mvals with
    | some vals => pure (.val (.tuple vals))
    | none => pure (.err "non-value in tuple elements")
  | .proj e i => do
    let r ← denote bi fuel e
    match r with
    | .val v =>
      match v.projIdx i with
      | some vi => pure (.val vi)
      | none => pure (.err s!"projection index {i} out of range")
    | other => pure other
  | .ifThenElse cond thn els => do
    let rc ← denote bi fuel cond
    match rc with
    | .val (.bool true) => denote bi fuel thn
    | .val (.bool false) => denote bi fuel els
    | .val _ => pure (.err "if condition not a bool")
    | other => pure other
  | .match_ scrut arms => do
    let rs ← denote bi fuel scrut
    match rs with
    | .val v => denoteMatchArms bi fuel v arms
    | other => pure other
  | .unitVal => pure (.val .unit)
  | .seq e1 e2 => do
    let r1 ← denote bi fuel e1
    match r1 with
    | .val _ => denote bi fuel e2
    | other => pure other
  | .borrow e => denote bi fuel e
  | .deref e => denote bi fuel e
  | .assign name rhs => do
    let r ← denote bi fuel rhs
    match r with
    | .val v => do modify (Env.extend · name v); pure (.val .unit)
    | other => pure other
  | .forLoop var lo hi body => do
    let rlo ← denote bi fuel lo
    let rhi ← denote bi fuel hi
    match rlo, rhi with
    | .val (.int lo_val), .val (.int hi_val) =>
      denoteForLoop bi fuel var lo_val hi_val body
    | .val _, .val _ => pure (.err "for loop bounds must be integers")
    | other, _ => pure other
  | .whileLoop cond body =>
    denoteWhile bi fuel cond body
  | .break_ (some e) => do
    let r ← denote bi fuel e
    match r with
    | .val v => pure (.broke v)
    | other => pure other
  | .break_ none => pure (.broke .unit)
  | .continue_ => pure .continued
  | .earlyReturn e => do
    let r ← denote bi fuel e
    match r with
    | .val v => pure (.earlyRet v)
    | other => pure other
  | .questionMark e => do
    let r ← denote bi fuel e
    match r with
    | .val (.result true v) => pure (.val v)
    | .val (.result false v) => pure (.earlyRet (.result false v))
    | .val _ => pure (.err "? operator on non-Result")
    | other => pure other
  -- Phase 3/4 output constructors: should not appear in pre-pipeline expressions
  | .forFold _ _ _ _ => pure (.err "forFold in pre-pipeline expression")
  | .whileFold _ _ => pure (.err "whileFold in pre-pipeline expression")
  | .forFoldReturn _ _ _ _ => pure (.err "forFoldReturn in pre-pipeline expression")
  | .whileFoldReturn _ _ => pure (.err "whileFoldReturn in pre-pipeline expression")
  | .cfBreak _ => pure (.err "cfBreak in pre-pipeline expression")
  | .cfContinue _ => pure (.err "cfContinue in pre-pipeline expression")
  | .cfBreakContinue _ => pure (.err "cfBreakContinue in pre-pipeline expression")
  termination_by e => (fuel, sizeOf e)
  decreasing_by
    all_goals simp_wf
    all_goals (first | omega |
      (try (have := ImpExpr.sizeOf_pos lo);
       try (have := ImpExpr.sizeOf_pos hi);
       try (have := ImpExpr.sizeOf_pos body);
       try (have := ImpExpr.sizeOf_pos cond);
       omega))

/-- Evaluate a list of expressions, collecting normal values. -/
def denoteArgs (bi : Builtins) (fuel : Nat) :
    List ImpExpr → StateM Env (Option (List Value))
  | [] => pure (some [])
  | e :: es => do
    let r ← denote bi fuel e
    match r with
    | .val v => do
      let rest ← denoteArgs bi fuel es
      pure (rest.map (v :: ·))
    | _ => pure none
  termination_by l => (fuel, sizeOf l)

/-- Try match arms in order against a value. -/
def denoteMatchArms (bi : Builtins) (fuel : Nat)
    (v : Value) : List (ImpPat × ImpExpr) → StateM Env Outcome
  | [] => pure (.err "no matching pattern")
  | (pat, body) :: rest => do
    let env ← get
    match matchPat pat v env with
    | some env' => do set env'; denote bi fuel body
    | none => denoteMatchArms bi fuel v rest
  termination_by arms => (fuel, sizeOf arms)

/-- For loop helper: iterate body over [lo, hi). -/
def denoteForLoop (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) : StateM Env Outcome :=
  if lo ≥ hi then pure (.val .unit)
  else if fuel = 0 then pure (.err "out of fuel")
  else do
    modify (Env.extend · var (.int lo))
    let rb ← denote bi fuel body
    match rb with
    | .val _ | .continued =>
      denoteForLoop bi (fuel - 1) var (lo + 1) hi body
    | .broke v => pure (.val v)
    | other => pure other
  termination_by (fuel, sizeOf body + 1)

/-- While loop helper. -/
def denoteWhile (bi : Builtins) (fuel : Nat)
    (cond body : ImpExpr) : StateM Env Outcome :=
  if fuel = 0 then pure (.err "out of fuel")
  else do
    let rc ← denote bi fuel cond
    match rc with
    | .val (.bool true) => do
      let rb ← denote bi fuel body
      match rb with
      | .val _ | .continued =>
        denoteWhile bi (fuel - 1) cond body
      | .broke v => pure (.val v)
      | other => pure other
    | .val (.bool false) => pure (.val .unit)
    | .val _ => pure (.err "while condition not a bool")
    | other => pure other
  termination_by (fuel, sizeOf cond + sizeOf body)
  decreasing_by
    all_goals simp_wf
    all_goals (first | omega |
      (try (have := ImpExpr.sizeOf_pos cond);
       try (have := ImpExpr.sizeOf_pos body);
       omega))

end

/-- Congruence: mapping over args preserves `denoteArgs` when `denote` is preserved. -/
theorem denoteArgs_map_congr (bi : Builtins) (fuel : Nat)
    (f : ImpExpr → ImpExpr) (es : List ImpExpr)
    (hf : ∀ e, e ∈ es → denote bi fuel (f e) = denote bi fuel e) :
    denoteArgs bi fuel (es.map f) = denoteArgs bi fuel es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons]
    unfold denoteArgs
    rw [hf e (.head _)]
    congr 1; funext r; split
    · congr 1; exact ih (fun e' he' => hf e' (.tail _ he'))
    · rfl

/-- Congruence: mapping over match arms preserves `denoteMatchArms`. -/
theorem denoteMatchArms_map_congr (bi : Builtins) (fuel : Nat)
    (f : ImpExpr → ImpExpr) (v : Value)
    (arms : List (ImpPat × ImpExpr))
    (hf : ∀ pa, pa ∈ arms → denote bi fuel (f pa.2) = denote bi fuel pa.2) :
    denoteMatchArms bi fuel v (arms.map (fun (p, e) => (p, f e))) =
    denoteMatchArms bi fuel v arms := by
  induction arms with
  | nil => rfl
  | cons pa arms ih =>
    obtain ⟨pat, body⟩ := pa
    simp only [List.map_cons]
    unfold denoteMatchArms
    congr 1; funext env
    split
    · congr 1; funext _; exact hf (pat, body) (.head _)
    · show denoteMatchArms bi fuel v (arms.map (fun (p, e) => (p, f e)))
          = denoteMatchArms bi fuel v arms
      exact ih (fun pa' hpa' => hf pa' (.tail _ hpa'))

/-- Congruence: replacing `body` in `denoteForLoop` when `denote` is preserved for all fuel. -/
theorem denoteForLoop_congr (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi : Int) (body body' : ImpExpr)
    (hbody : ∀ fuel, denote bi fuel body' = denote bi fuel body) :
    denoteForLoop bi fuel var lo hi body' = denoteForLoop bi fuel var lo hi body := by
  induction fuel generalizing lo with
  | zero =>
    unfold denoteForLoop
    split
    · rfl
    · split
      · rfl
      · next h => exact absurd rfl h
  | succ n ih =>
    unfold denoteForLoop
    split
    · rfl
    · split
      · next h => exact absurd h (Nat.succ_ne_zero n)
      · congr 1; funext _
        rw [hbody (n + 1)]
        congr 1; funext rb
        split
        all_goals first | (simp only [Nat.add_sub_cancel]; exact ih (lo + 1)) | rfl

/-- Congruence: replacing `cond` and `body` in `denoteWhile` when `denote` is preserved for all fuel. -/
theorem denoteWhile_congr (bi : Builtins) (fuel : Nat)
    (cond cond' body body' : ImpExpr)
    (hcond : ∀ fuel, denote bi fuel cond' = denote bi fuel cond)
    (hbody : ∀ fuel, denote bi fuel body' = denote bi fuel body) :
    denoteWhile bi fuel cond' body' = denoteWhile bi fuel cond body := by
  induction fuel with
  | zero =>
    unfold denoteWhile
    split
    · rfl
    · next h => exact absurd rfl h
  | succ n ih =>
    unfold denoteWhile
    split
    · next h => exact absurd h (Nat.succ_ne_zero n)
    · congr 1; funext _
      rw [hcond (n + 1)]
      congr 1; funext rc
      split
      · congr 1; funext _
        rw [hbody (n + 1)]
        congr 1; funext rb
        split
        all_goals first | (simp only [Nat.add_sub_cancel]; exact ih) | rfl
      · rfl
      · rfl
      · rfl

/-- Convenience: denote with default builtins. -/
def denoteDefault (fuel : Nat) (e : ImpExpr) : StateM Env Outcome :=
  denote defaultBuiltins fuel e

end SSProve.Hax

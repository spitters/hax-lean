/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Hax.AST
import Hax.Value
import Hax.Semantics

/-!
# ControlFlow-Aware Semantics

A variant of `denote` that interprets `app "for_fold"`, `app "while_fold"`,
`app "ControlFlow.Break"`, and `app "ControlFlow.Continue"` as special forms.

ControlFlow values (`Value.controlFlow`) propagate through all expression
constructs, mimicking how `broke`/`continued`/`earlyRet` propagate through
the `other => pure other` branches in the original `denote`.

## Main definitions

* `denote'` — ControlFlow-aware evaluator
* `Outcome.encodeCF4` — maps `earlyRet v` to `val (controlFlow true v)`
* `Builtins.NoControlFlow` — builtins never produce controlFlow values
* `Builtins.HasErr` — builtins include Err constructor
* `LoopScoped` — break/continue only appear inside loops
-/

namespace Hax

/-! ## Outcome encoding -/

namespace Outcome

/-- Encode early exit outcomes as values (phase 4 simulation). -/
def encodeCF4 : Outcome → Outcome
  | .earlyRet v => .val (.controlFlow true v)
  | o => o

@[simp] theorem encodeCF4_val (v : Value) : encodeCF4 (.val v) = .val v := rfl
@[simp] theorem encodeCF4_err (msg : String) : encodeCF4 (.err msg) = .err msg := rfl
@[simp] theorem encodeCF4_broke (v : Value) : encodeCF4 (.broke v) = .broke v := rfl
@[simp] theorem encodeCF4_continued : encodeCF4 .continued = .continued := rfl
@[simp] theorem encodeCF4_earlyRet (v : Value) :
    encodeCF4 (.earlyRet v) = .val (.controlFlow true v) := rfl

/-- Encode loop control flow outcomes as values (phase 3 simulation). -/
def encodeCF3 : Outcome → Outcome
  | .broke v => .val (.controlFlow true v)
  | .continued => .val (.controlFlow false .unit)
  | o => o

@[simp] theorem encodeCF3_val (v : Value) : encodeCF3 (.val v) = .val v := rfl
@[simp] theorem encodeCF3_err (msg : String) : encodeCF3 (.err msg) = .err msg := rfl
@[simp] theorem encodeCF3_broke (v : Value) :
    encodeCF3 (.broke v) = .val (.controlFlow true v) := rfl
@[simp] theorem encodeCF3_continued :
    encodeCF3 .continued = .val (.controlFlow false .unit) := rfl
@[simp] theorem encodeCF3_earlyRet (v : Value) : encodeCF3 (.earlyRet v) = .earlyRet v := rfl

/-- Combined encoding for the full pipeline (Phases 3 + 4).
    Maps all control flow outcomes to `val` encodings:
    - `val v` → `val v` (unchanged)
    - `err msg` → `err msg` (unchanged)
    - `earlyRet v` → `val (controlFlow true v)` (early return → CF break)
    - `broke v` → `val (controlFlow true v)` (loop break → CF break)
    - `continued` → `val (controlFlow false unit)` (continue → CF continue)

    Note: `earlyRet` and `broke` have the same encoding. For well-scoped
    programs (`LoopScoped`), `broke`/`continued` never appear at the top
    level — they're resolved by the enclosing loop. -/
def encodeCF : Outcome → Outcome
  | .val v => .val v
  | .err msg => .err msg
  | .earlyRet v => .val (.controlFlow true v)
  | .broke v => .val (.controlFlow true v)
  | .continued => .val (.controlFlow false .unit)

@[simp] theorem encodeCF_val (v : Value) : encodeCF (.val v) = .val v := rfl
@[simp] theorem encodeCF_err (msg : String) : encodeCF (.err msg) = .err msg := rfl
@[simp] theorem encodeCF_earlyRet (v : Value) :
    encodeCF (.earlyRet v) = .val (.controlFlow true v) := rfl
@[simp] theorem encodeCF_broke (v : Value) :
    encodeCF (.broke v) = .val (.controlFlow true v) := rfl
@[simp] theorem encodeCF_continued :
    encodeCF .continued = .val (.controlFlow false .unit) := rfl

/-- Composition: encodeCF4 ∘ encodeCF3 = encodeCF -/
@[simp] theorem encodeCF4_encodeCF3 (o : Outcome) :
    encodeCF4 (encodeCF3 o) = encodeCF o := by
  cases o <;> rfl

/-- Nested Phase 3 encoding for loop bodies with earlyReturn.
    Like `encodeCF3` but double-wraps `broke` to distinguish from `earlyRet`:
    - `broke v` → `val (controlFlow true (controlFlow false v))` (loop break)
    - `earlyRet v` → `earlyRet v` (preserved for Phase 4)
    - `continued` → `val (controlFlow false unit)` (same as encodeCF3) -/
def encodeCF3nested : Outcome → Outcome
  | .val v => .val v
  | .err msg => .err msg
  | .earlyRet v => .earlyRet v
  | .broke v => .val (.controlFlow true (.controlFlow false v))
  | .continued => .val (.controlFlow false .unit)

@[simp] theorem encodeCF3nested_val (v : Value) : encodeCF3nested (.val v) = .val v := rfl
@[simp] theorem encodeCF3nested_err (msg : String) : encodeCF3nested (.err msg) = .err msg := rfl
@[simp] theorem encodeCF3nested_earlyRet (v : Value) :
    encodeCF3nested (.earlyRet v) = .earlyRet v := rfl
@[simp] theorem encodeCF3nested_broke (v : Value) :
    encodeCF3nested (.broke v) = .val (.controlFlow true (.controlFlow false v)) := rfl
@[simp] theorem encodeCF3nested_continued :
    encodeCF3nested .continued = .val (.controlFlow false .unit) := rfl

/-- Parameterized Phase 3 encoding: `false` → `encodeCF3`, `true` → `encodeCF3nested`.
    Defined so that `encodeCF3gen false` reduces to `encodeCF3` definitionally. -/
def encodeCF3gen : Bool → Outcome → Outcome
  | false => encodeCF3
  | true => encodeCF3nested

theorem encodeCF3gen_false_eq : encodeCF3gen false = encodeCF3 := rfl
theorem encodeCF3gen_true_eq : encodeCF3gen true = encodeCF3nested := rfl

@[simp] theorem encodeCF3gen_val (n : Bool) (v : Value) :
    encodeCF3gen n (.val v) = .val v := by cases n <;> rfl
@[simp] theorem encodeCF3gen_err (n : Bool) (msg : String) :
    encodeCF3gen n (.err msg) = .err msg := by cases n <;> rfl
@[simp] theorem encodeCF3gen_earlyRet (n : Bool) (v : Value) :
    encodeCF3gen n (.earlyRet v) = .earlyRet v := by cases n <;> rfl
@[simp] theorem encodeCF3gen_continued (n : Bool) :
    encodeCF3gen n .continued = .val (.controlFlow false .unit) := by cases n <;> rfl
@[simp] theorem encodeCF3gen_broke_false (v : Value) :
    encodeCF3gen false (.broke v) = .val (.controlFlow true v) := rfl
@[simp] theorem encodeCF3gen_broke_true (v : Value) :
    encodeCF3gen true (.broke v) = .val (.controlFlow true (.controlFlow false v)) := rfl

/-- Nested encoding for Phase 3+4 inside loops with earlyReturn.
    Distinguishes broke (→ double-wrapped) from earlyRet (→ single-wrapped). -/
def encodeCFnested : Outcome → Outcome
  | .val v => .val v
  | .err msg => .err msg
  | .earlyRet v => .val (.controlFlow true v)
  | .broke v => .val (.controlFlow true (.controlFlow false v))
  | .continued => .val (.controlFlow false .unit)

@[simp] theorem encodeCFnested_val (v : Value) : encodeCFnested (.val v) = .val v := rfl
@[simp] theorem encodeCFnested_err (msg : String) : encodeCFnested (.err msg) = .err msg := rfl
@[simp] theorem encodeCFnested_earlyRet (v : Value) :
    encodeCFnested (.earlyRet v) = .val (.controlFlow true v) := rfl
@[simp] theorem encodeCFnested_broke (v : Value) :
    encodeCFnested (.broke v) = .val (.controlFlow true (.controlFlow false v)) := rfl
@[simp] theorem encodeCFnested_continued :
    encodeCFnested .continued = .val (.controlFlow false .unit) := rfl

end Outcome

/-! ## Builtins predicates -/

namespace Builtins

/-- Builtins that never produce controlFlow values. -/
def NoControlFlow (bi : Builtins) : Prop :=
  ∀ f args v, bi f args = some v → ∀ isBreak w, v ≠ .controlFlow isBreak w

/-- Builtins that include the Err constructor. -/
def HasErr (bi : Builtins) : Prop :=
  ∀ v, bi "Err" [v] = some (.result false v)

theorem defaultBuiltins_noControlFlow : NoControlFlow defaultBuiltins := by
  intro f args v h isBreak w heq
  subst heq; revert h; unfold defaultBuiltins
  split <;> (intro h; cases h)

theorem defaultBuiltins_hasErr : HasErr defaultBuiltins := by
  intro v; rfl

end Builtins

/-- Extend builtins with ControlFlow.Break and ControlFlow.Continue. -/
def cfBuiltins (bi : Builtins) : Builtins := fun f args =>
  match f, args with
  | "ControlFlow.Break", [v] => some (.controlFlow true v)
  | "ControlFlow.Continue", [v] => some (.controlFlow false v)
  | _, _ => bi f args

/-! ## LoopScoped predicate -/

/-- An expression where `break_` and `continue_` only appear inside
    `forLoop` or `whileLoop` bodies. This holds for all well-typed
    Rust programs (the compiler enforces it). -/
inductive LoopScoped : ImpExpr → Prop where
  | lit {v} : LoopScoped (.lit v)
  | var {n} : LoopScoped (.var n)
  | letBind {n val body} : LoopScoped val → LoopScoped body →
      LoopScoped (.letBind n val body)
  | app {f args} : (∀ a, a ∈ args → LoopScoped a) →
      LoopScoped (.app f args)
  | tuple {elems} : (∀ a, a ∈ elems → LoopScoped a) →
      LoopScoped (.tuple elems)
  | proj {e i} : LoopScoped e → LoopScoped (.proj e i)
  | ifThenElse {c t e} : LoopScoped c → LoopScoped t → LoopScoped e →
      LoopScoped (.ifThenElse c t e)
  | match_ {scrut arms} : LoopScoped scrut →
      (∀ pa, pa ∈ arms → LoopScoped pa.2) →
      LoopScoped (.match_ scrut arms)
  | unitVal : LoopScoped .unitVal
  | seq {e1 e2} : LoopScoped e1 → LoopScoped e2 →
      LoopScoped (.seq e1 e2)
  | borrow {e} : LoopScoped e → LoopScoped (.borrow e)
  | deref {e} : LoopScoped e → LoopScoped (.deref e)
  | assign {n rhs} : LoopScoped rhs → LoopScoped (.assign n rhs)
  | forLoop {v lo hi body} : LoopScoped lo → LoopScoped hi →
      LoopScoped (.forLoop v lo hi body)
  | forLoopRev {v lo hi body} : LoopScoped lo → LoopScoped hi →
      LoopScoped (.forLoopRev v lo hi body)
  | whileLoop {c body} : LoopScoped (.whileLoop c body)
  | earlyReturn {e} : LoopScoped e → LoopScoped (.earlyReturn e)
  | questionMark {e} : LoopScoped e → LoopScoped (.questionMark e)
  | forFold {v lo hi body} : LoopScoped lo → LoopScoped hi →
      LoopScoped (.forFold v lo hi body)
  | forFoldRev {v lo hi body} : LoopScoped lo → LoopScoped hi →
      LoopScoped (.forFoldRev v lo hi body)
  | whileFold {c body} : LoopScoped (.whileFold c body)
  | forFoldReturn {v lo hi body} : LoopScoped lo → LoopScoped hi →
      LoopScoped (.forFoldReturn v lo hi body)
  | forFoldRevReturn {v lo hi body} : LoopScoped lo → LoopScoped hi →
      LoopScoped (.forFoldRevReturn v lo hi body)
  | whileFoldReturn {c body} : LoopScoped (.whileFoldReturn c body)
  | cfBreak {e} : LoopScoped e → LoopScoped (.cfBreak e)
  | cfContinue {e} : LoopScoped e → LoopScoped (.cfContinue e)
  | cfBreakContinue {e} : LoopScoped e → LoopScoped (.cfBreakContinue e)

/-! ## ControlFlow-aware evaluator

The key insight: `denote'` extends `denote` in three ways:
1. The builtins are extended with ControlFlow.Break/Continue via `cfBuiltins`
2. ControlFlow values propagate through val-matching positions
3. `app "for_fold"` and `app "while_fold"` are interpreted as loops
   using `denoteForLoop'` and `denoteWhile'` respectively -/

private theorem string_sizeOf_pos (s : String) : 0 < sizeOf s := by
  have : sizeOf s ≥ 1 := by
    rcases s with ⟨cs, h⟩; simp only [sizeOf, String._sizeOf_1]; omega
  omega

mutual

/-- ControlFlow-aware big-step semantics. -/
def denote' (bi : Builtins) (fuel : Nat) : ImpExpr → StateM Env Outcome
  | .lit v => pure (.val (Value.ofLit v))
  | .var name => do
    let env ← get
    match env name with
    | some v => pure (.val v)
    | none => pure (.err s!"undefined variable: {name}")
  | .letBind name val body => do
    let rv ← denote' bi fuel val
    match rv with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v => do modify (Env.extend · name v); denote' bi fuel body
    | other => pure other
  | .lam _ _ =>
    -- The reference semantics is first-order; a closure value is not modeled
    -- (mirrors `denote`'s `.lam` case). `.lam` is a syntactic carrier for
    -- extraction; the verified guarantee is type erasure, not this denotation.
    pure (.err "closures are not evaluated by the reference semantics")
  | .app f args => denoteApp' bi fuel f args
  | .tuple elems => do
    let mvals ← denoteArgs' bi fuel elems
    match mvals with
    | some vals => pure (.val (.tuple vals))
    | none => pure (.err "non-value in tuple elements")
  | .proj e i => do
    let r ← denote' bi fuel e
    match r with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v =>
      match v.projIdx i with
      | some vi => pure (.val vi)
      | none => pure (.err s!"projection index {i} out of range")
    | other => pure other
  | .ifThenElse cond thn els => do
    let rc ← denote' bi fuel cond
    match rc with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val (.bool true) => denote' bi fuel thn
    | .val (.bool false) => denote' bi fuel els
    | .val _ => pure (.err "if condition not a bool")
    | other => pure other
  | .match_ scrut arms => do
    let rs ← denote' bi fuel scrut
    match rs with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v => denoteMatchArms' bi fuel v arms
    | other => pure other
  | .unitVal => pure (.val .unit)
  | .seq e1 e2 => do
    let r1 ← denote' bi fuel e1
    match r1 with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val _ => denote' bi fuel e2
    | other => pure other
  | .borrow e => denote' bi fuel e
  | .deref e => denote' bi fuel e
  | .assign name rhs => do
    let r ← denote' bi fuel rhs
    match r with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v => do modify (Env.extend · name v); pure (.val .unit)
    | other => pure other
  | .forLoop var lo hi body => do
    let rlo ← denote' bi fuel lo
    let rhi ← denote' bi fuel hi
    match rlo, rhi with
    | .val (.int lo_val), .val (.int hi_val) =>
      denoteForLoopOrig' bi fuel var lo_val hi_val body
    | .val _, .val _ => pure (.err "for loop bounds must be integers")
    | other, _ => pure other
  | .forLoopRev var lo hi body => do
    let rlo ← denote' bi fuel lo
    let rhi ← denote' bi fuel hi
    match rlo, rhi with
    | .val (.int lo_val), .val (.int hi_val) =>
      denoteForLoopRevOrig' bi fuel var lo_val hi_val body
    | .val _, .val _ => pure (.err "for loop bounds must be integers")
    | other, _ => pure other
  | .whileLoop cond body =>
    denoteWhileOrig' bi fuel cond body
  | .break_ (some e) => do
    let r ← denote' bi fuel e
    match r with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v => pure (.broke v)
    | other => pure other
  | .break_ none => pure (.broke .unit)
  | .continue_ => pure .continued
  | .earlyReturn e => do
    let r ← denote' bi fuel e
    match r with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v => pure (.earlyRet v)
    | other => pure other
  | .questionMark e => do
    let r ← denote' bi fuel e
    match r with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val (.result true v) => pure (.val v)
    | .val (.result false v) => pure (.earlyRet (.result false v))
    | .val _ => pure (.err "? operator on non-Result")
    | other => pure other
  -- Dedicated constructors for Phase 3/4 output
  | .forFold var lo hi body => do
    let rlo ← denote' bi fuel lo
    let rhi ← denote' bi fuel hi
    match rlo, rhi with
    | .val (.int lo_val), .val (.int hi_val) =>
      denoteForLoop' bi fuel var lo_val hi_val body
    | .val (.controlFlow _ _), _ => pure rlo
    | _, .val (.controlFlow _ _) => pure rlo
    | .val _, .val _ => pure (.err "for loop bounds must be integers")
    | other, _ => pure other
  | .forFoldRev var lo hi body => do
    let rlo ← denote' bi fuel lo
    let rhi ← denote' bi fuel hi
    match rlo, rhi with
    | .val (.int lo_val), .val (.int hi_val) =>
      denoteForLoopRev' bi fuel var lo_val hi_val body
    | .val (.controlFlow _ _), _ => pure rlo
    | _, .val (.controlFlow _ _) => pure rlo
    | .val _, .val _ => pure (.err "for loop bounds must be integers")
    | other, _ => pure other
  | .whileFold cond body =>
    denoteWhile' bi fuel cond body
  | .forFoldReturn var lo hi body => do
    let rlo ← denote' bi fuel lo
    let rhi ← denote' bi fuel hi
    match rlo, rhi with
    | .val (.int lo_val), .val (.int hi_val) =>
      denoteForLoop'Return bi fuel var lo_val hi_val body
    | .val (.controlFlow _ _), _ => pure rlo
    | _, .val (.controlFlow _ _) => pure rlo
    | .val _, .val _ => pure (.err "for loop bounds must be integers")
    | other, _ => pure other
  | .forFoldRevReturn var lo hi body => do
    let rlo ← denote' bi fuel lo
    let rhi ← denote' bi fuel hi
    match rlo, rhi with
    | .val (.int lo_val), .val (.int hi_val) =>
      denoteForLoopRev'Return bi fuel var lo_val hi_val body
    | .val (.controlFlow _ _), _ => pure rlo
    | _, .val (.controlFlow _ _) => pure rlo
    | .val _, .val _ => pure (.err "for loop bounds must be integers")
    | other, _ => pure other
  | .whileFoldReturn cond body =>
    denoteWhile'Return bi fuel cond body
  | .cfBreak e => do
    let r ← denote' bi fuel e
    match r with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v => pure (.val (.controlFlow true v))
    | other => pure other
  | .cfContinue e => do
    let r ← denote' bi fuel e
    match r with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v => pure (.val (.controlFlow false v))
    | other => pure other
  | .cfBreakContinue e => do
    let r ← denote' bi fuel e
    match r with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v => pure (.val (.controlFlow true (.controlFlow false v)))
    | other => pure other
  | .typeAscription e _ => denote' bi fuel e
  termination_by e => (fuel, sizeOf e)
  decreasing_by
    all_goals simp_wf
    all_goals (first | omega |
      (try (have := ImpExpr.sizeOf_pos lo);
       try (have := ImpExpr.sizeOf_pos hi);
       try (have := ImpExpr.sizeOf_pos body);
       try (have := ImpExpr.sizeOf_pos cond);
       try (have := string_sizeOf_pos f);
       simp +arith [sizeOf, SizeOf.sizeOf, ImpExpr._sizeOf_1] at *;
       omega))

/-- App dispatch: now only handles regular (non-reserved) function calls.
    Reserved names are handled by dedicated AST constructors. -/
def denoteApp' (bi : Builtins) (fuel : Nat) (f : String) (args : List ImpExpr) :
    StateM Env Outcome := do
  let mvals ← denoteArgs' bi fuel args
  match mvals with
  | some vals =>
    match bi f vals with
    | some v => pure (.val v)
    | none => pure (.err s!"unknown function or bad args: {f}")
  | none => pure (.err "non-value in function arguments")
  termination_by (fuel, 1 + sizeOf args)

/-- Evaluate a list of expressions, collecting normal non-controlFlow values.
    Returns `none` if any argument evaluates to non-val or controlFlow. -/
def denoteArgs' (bi : Builtins) (fuel : Nat) :
    List ImpExpr → StateM Env (Option (List Value))
  | [] => pure (some [])
  | e :: es => do
    let r ← denote' bi fuel e
    match r with
    | .val (.controlFlow _ _) => pure none
    | .val v => do
      let rest ← denoteArgs' bi fuel es
      pure (rest.map (v :: ·))
    | _ => pure none
  termination_by l => (fuel, sizeOf l)

/-- Try match arms in order against a value. -/
def denoteMatchArms' (bi : Builtins) (fuel : Nat)
    (v : Value) : List (ImpPat × ImpExpr) → StateM Env Outcome
  | [] => pure (.err "no matching pattern")
  | (pat, body) :: rest => do
    let env ← get
    match matchPat pat v env with
    | some env' => do set env'; denote' bi fuel body
    | none => denoteMatchArms' bi fuel v rest
  termination_by arms => (fuel, sizeOf arms)

/-- For loop over [lo, hi) with ControlFlow-based break/continue detection.
    Used by `denote'` to evaluate `app "for_fold" [var, lo, hi, body]` expressions
    produced by `functionalizeLoops`. -/
def denoteForLoop' (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) : StateM Env Outcome :=
  if lo ≥ hi then pure (.val .unit)
  else if fuel = 0 then pure (.err "out of fuel")
  else do
    modify (Env.extend · var (.int lo))
    let rb ← denote' bi fuel body
    match rb with
    | .val (.controlFlow true v) => pure (.val v)       -- break
    | .val (.controlFlow false _) =>                     -- continue
      denoteForLoop' bi (fuel - 1) var (lo + 1) hi body
    | .val _ => denoteForLoop' bi (fuel - 1) var (lo + 1) hi body  -- normal
    | other => pure other                                -- earlyRet/err/broke/continued
  termination_by (fuel, sizeOf body + 1)

/-- While loop with ControlFlow-based break/continue detection.
    Used by `denote'` to evaluate `app "while_fold" [cond, body]` expressions
    produced by `functionalizeLoops`. -/
def denoteWhile' (bi : Builtins) (fuel : Nat)
    (cond body : ImpExpr) : StateM Env Outcome :=
  if fuel = 0 then pure (.err "out of fuel")
  else do
    let rc ← denote' bi fuel cond
    match rc with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val (.bool true) => do
      let rb ← denote' bi fuel body
      match rb with
      | .val (.controlFlow true v) => pure (.val v)      -- break
      | .val (.controlFlow false _) =>                    -- continue
        denoteWhile' bi (fuel - 1) cond body
      | .val _ => denoteWhile' bi (fuel - 1) cond body   -- normal
      | other => pure other
    | .val (.bool false) => pure (.val .unit)
    | .val _ => pure (.err "while condition not a bool")
    | other => pure other
  termination_by (fuel, sizeOf cond + sizeOf body)
  decreasing_by
    all_goals simp_wf
    all_goals (first | omega |
      (have := ImpExpr.sizeOf_pos cond;
       have := ImpExpr.sizeOf_pos body;
       omega))

/-- For loop helper for the original `forLoop` constructor.
    Same as `denoteForLoop` but using `denote'` internally. -/
def denoteForLoopOrig' (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) : StateM Env Outcome :=
  if lo ≥ hi then pure (.val .unit)
  else if fuel = 0 then pure (.err "out of fuel")
  else do
    modify (Env.extend · var (.int lo))
    let rb ← denote' bi fuel body
    match rb with
    | .val _ | .continued =>
      denoteForLoopOrig' bi (fuel - 1) var (lo + 1) hi body
    | .broke v => pure (.val v)
    | other => pure other
  termination_by (fuel, sizeOf body + 1)

/-- While loop helper for the original `whileLoop` constructor.
    Same as `denoteWhile` but using `denote'` internally. -/
def denoteWhileOrig' (bi : Builtins) (fuel : Nat)
    (cond body : ImpExpr) : StateM Env Outcome :=
  if fuel = 0 then pure (.err "out of fuel")
  else do
    let rc ← denote' bi fuel cond
    match rc with
    | .val (.bool true) => do
      let rb ← denote' bi fuel body
      match rb with
      | .val _ | .continued =>
        denoteWhileOrig' bi (fuel - 1) cond body
      | .broke v => pure (.val v)
      | other => pure other
    | .val (.bool false) => pure (.val .unit)
    | .val _ => pure (.err "while condition not a bool")
    | other => pure other
  termination_by (fuel, sizeOf cond + sizeOf body)
  decreasing_by
    all_goals simp_wf
    all_goals (first | omega |
      (have := ImpExpr.sizeOf_pos cond;
       have := ImpExpr.sizeOf_pos body;
       omega))

/-- For loop with nested ControlFlow: distinguishes loop break from early return.
    Used by `denote'` to evaluate `app "for_fold_return" [var, lo, hi, body]`.

    Body results:
    - `val (controlFlow true (controlFlow false v))` → loop break, return `val v`
    - `val (controlFlow true v)` (non-Continue) → early return, propagate
    - `val (controlFlow false _)` → continue iterating
    - `val _` (non-CF) → normal, continue iterating -/
def denoteForLoop'Return (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) : StateM Env Outcome :=
  if lo ≥ hi then pure (.val .unit)
  else if fuel = 0 then pure (.err "out of fuel")
  else do
    modify (Env.extend · var (.int lo))
    let rb ← denote' bi fuel body
    match rb with
    | .val (.controlFlow true (.controlFlow false v)) =>  -- Break(Continue(v)) = loop break
      pure (.val v)
    | .val (.controlFlow true v) =>                       -- Break(v) = early return
      pure (.val (.controlFlow true v))
    | .val (.controlFlow false _) =>                      -- Continue = continue
      denoteForLoop'Return bi (fuel - 1) var (lo + 1) hi body
    | .val _ =>                                           -- normal value
      denoteForLoop'Return bi (fuel - 1) var (lo + 1) hi body
    | other => pure other                                 -- err/earlyRet/broke/continued
  termination_by (fuel, sizeOf body + 1)

/-- While loop with nested ControlFlow: distinguishes loop break from early return.
    Used by `denote'` to evaluate `app "while_fold_return" [cond, body]`. -/
def denoteWhile'Return (bi : Builtins) (fuel : Nat)
    (cond body : ImpExpr) : StateM Env Outcome :=
  if fuel = 0 then pure (.err "out of fuel")
  else do
    let rc ← denote' bi fuel cond
    match rc with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val (.bool true) => do
      let rb ← denote' bi fuel body
      match rb with
      | .val (.controlFlow true (.controlFlow false v)) =>  -- loop break
        pure (.val v)
      | .val (.controlFlow true v) =>                       -- early return
        pure (.val (.controlFlow true v))
      | .val (.controlFlow false _) =>                      -- continue
        denoteWhile'Return bi (fuel - 1) cond body
      | .val _ =>                                           -- normal
        denoteWhile'Return bi (fuel - 1) cond body
      | other => pure other
    | .val (.bool false) => pure (.val .unit)
    | .val _ => pure (.err "while condition not a bool")
    | other => pure other
  termination_by (fuel, sizeOf cond + sizeOf body)
  decreasing_by
    all_goals simp_wf
    all_goals (first | omega |
      (have := ImpExpr.sizeOf_pos cond;
       have := ImpExpr.sizeOf_pos body;
       omega))

/-- Reverse for loop helper for the original `forLoopRev` constructor.
    Same as `denoteForLoopOrig'` but iterates hi-1 down to lo. -/
def denoteForLoopRevOrig' (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) : StateM Env Outcome :=
  if lo ≥ hi then pure (.val .unit)
  else if fuel = 0 then pure (.err "out of fuel")
  else do
    modify (Env.extend · var (.int (hi - 1)))
    let rb ← denote' bi fuel body
    match rb with
    | .val _ | .continued =>
      denoteForLoopRevOrig' bi (fuel - 1) var lo (hi - 1) body
    | .broke v => pure (.val v)
    | other => pure other
  termination_by (fuel, sizeOf body + 1)

/-- Reverse for loop over [lo, hi) with ControlFlow-based break/continue detection.
    Same as `denoteForLoop'` but iterates hi-1 down to lo. -/
def denoteForLoopRev' (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) : StateM Env Outcome :=
  if lo ≥ hi then pure (.val .unit)
  else if fuel = 0 then pure (.err "out of fuel")
  else do
    modify (Env.extend · var (.int (hi - 1)))
    let rb ← denote' bi fuel body
    match rb with
    | .val (.controlFlow true v) => pure (.val v)       -- break
    | .val (.controlFlow false _) =>                     -- continue
      denoteForLoopRev' bi (fuel - 1) var lo (hi - 1) body
    | .val _ => denoteForLoopRev' bi (fuel - 1) var lo (hi - 1) body  -- normal
    | other => pure other                                -- earlyRet/err/broke/continued
  termination_by (fuel, sizeOf body + 1)

/-- Reverse for loop with nested ControlFlow: distinguishes loop break from early return.
    Same as `denoteForLoop'Return` but iterates hi-1 down to lo. -/
def denoteForLoopRev'Return (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) : StateM Env Outcome :=
  if lo ≥ hi then pure (.val .unit)
  else if fuel = 0 then pure (.err "out of fuel")
  else do
    modify (Env.extend · var (.int (hi - 1)))
    let rb ← denote' bi fuel body
    match rb with
    | .val (.controlFlow true (.controlFlow false v)) =>  -- Break(Continue(v)) = loop break
      pure (.val v)
    | .val (.controlFlow true v) =>                       -- Break(v) = early return
      pure (.val (.controlFlow true v))
    | .val (.controlFlow false _) =>                      -- Continue = continue
      denoteForLoopRev'Return bi (fuel - 1) var lo (hi - 1) body
    | .val _ =>                                           -- normal value
      denoteForLoopRev'Return bi (fuel - 1) var lo (hi - 1) body
    | other => pure other                                 -- err/earlyRet/broke/continued
  termination_by (fuel, sizeOf body + 1)

end

/-! ## ControlFlow-free invariant -/

/-- A value is a top-level controlFlow wrapper. -/
def Value.isControlFlow : Value → Bool
  | .controlFlow _ _ => true
  | _ => false

@[simp] theorem Value.isControlFlow_controlFlow (b : Bool) (v : Value) :
    (Value.controlFlow b v).isControlFlow = true := rfl
@[simp] theorem Value.isControlFlow_bool (b : Bool) :
    (Value.bool b).isControlFlow = false := rfl
@[simp] theorem Value.isControlFlow_int (n : Int) :
    (Value.int n).isControlFlow = false := rfl
@[simp] theorem Value.isControlFlow_unit :
    Value.unit.isControlFlow = false := rfl
@[simp] theorem Value.isControlFlow_tuple (vs : List Value) :
    (Value.tuple vs).isControlFlow = false := rfl
@[simp] theorem Value.isControlFlow_option (v : Option Value) :
    (Value.option v).isControlFlow = false := rfl
@[simp] theorem Value.isControlFlow_result (ok : Bool) (v : Value) :
    (Value.result ok v).isControlFlow = false := rfl

@[simp] theorem Value.isControlFlow_uint (w : IntWidth) (n : Nat) :
    (Value.uint w n).isControlFlow = false := rfl
@[simp] theorem Value.isControlFlow_sint (w : IntWidth) (n : Int) :
    (Value.sint w n).isControlFlow = false := rfl
@[simp] theorem Value.isControlFlow_array (vs : List Value) :
    (Value.array vs).isControlFlow = false := rfl

theorem Value.ofLit_not_isControlFlow (l : ImpLit) :
    (Value.ofLit l).isControlFlow = false := by
  cases l <;> simp [Value.ofLit, isControlFlow]

/-- A value contains no controlFlow wrappers at any depth. -/
def Value.deepNoControlFlow : Value → Bool
  | .bool _ => true
  | .int _ => true
  | .uint _ _ => true
  | .sint _ _ => true
  | .unit => true
  | .tuple vs => deepNoControlFlowList vs
  | .array vs => deepNoControlFlowList vs
  | .option none => true
  | .option (some v) => v.deepNoControlFlow
  | .result _ v => v.deepNoControlFlow
  | .controlFlow _ _ => false
where
  deepNoControlFlowList : List Value → Bool
    | [] => true
    | v :: vs => v.deepNoControlFlow && deepNoControlFlowList vs

@[simp] theorem Value.deepNoControlFlow_list_nil :
    Value.deepNoControlFlow.deepNoControlFlowList [] = true := rfl

@[simp] theorem Value.deepNoControlFlow_list_cons (v : Value) (vs : List Value) :
    Value.deepNoControlFlow.deepNoControlFlowList (v :: vs) =
      (v.deepNoControlFlow && Value.deepNoControlFlow.deepNoControlFlowList vs) := rfl

theorem Value.deepNoControlFlow_implies_isControlFlow_false {v : Value}
    (h : v.deepNoControlFlow = true) : v.isControlFlow = false := by
  cases v <;> simp_all [isControlFlow, deepNoControlFlow]

theorem Value.ofLit_deepNoControlFlow (l : ImpLit) :
    (Value.ofLit l).deepNoControlFlow = true := by
  cases l <;> simp [Value.ofLit, Value.deepNoControlFlow, IntWidth.modulus]

theorem Value.deepNoControlFlow_tuple_mem {vs : List Value}
    (h : (Value.tuple vs).deepNoControlFlow = true) {v : Value} (hv : v ∈ vs) :
    v.deepNoControlFlow = true := by
  simp [deepNoControlFlow] at h
  induction vs with
  | nil => cases hv
  | cons w ws ih =>
    simp [deepNoControlFlow.deepNoControlFlowList, Bool.and_eq_true] at h
    cases hv with
    | head => exact h.1
    | tail _ hv => exact ih h.2 hv

theorem Value.deepNoControlFlow_array_mem {vs : List Value}
    (h : (Value.array vs).deepNoControlFlow = true) {v : Value} (hv : v ∈ vs) :
    v.deepNoControlFlow = true := by
  simp [deepNoControlFlow] at h
  induction vs with
  | nil => cases hv
  | cons w ws ih =>
    simp [deepNoControlFlow.deepNoControlFlowList, Bool.and_eq_true] at h
    cases hv with
    | head => exact h.1
    | tail _ hv => exact ih h.2 hv

theorem Value.deepNoControlFlow_projIdx {v : Value} {i : Nat} {vi : Value}
    (hv : v.deepNoControlFlow = true) (hp : v.projIdx i = some vi) :
    vi.deepNoControlFlow = true := by
  cases v with
  | tuple vs =>
    simp [projIdx] at hp
    exact deepNoControlFlow_tuple_mem hv (List.mem_of_getElem? hp)
  | array vs =>
    simp [projIdx] at hp
    exact deepNoControlFlow_array_mem hv (List.mem_of_getElem? hp)
  | _ => simp [projIdx] at hp

/-- An environment contains no controlFlow values at any depth. -/
def Env.NoControlFlow (env : Env) : Prop :=
  ∀ n v, env n = some v → v.deepNoControlFlow = true

theorem Env.NoControlFlow.empty : Env.NoControlFlow Env.empty := by
  intro n v h; simp [Env.empty] at h

theorem Env.NoControlFlow.extend {env : Env} (henv : env.NoControlFlow)
    {name : String} {v : Value} (hv : v.deepNoControlFlow = true) :
    (Env.extend env name v).NoControlFlow := by
  intro n w hw
  simp only [Env.extend, beq_iff_eq] at hw
  split at hw
  · exact Option.some.inj hw ▸ hv
  · exact henv n w hw

theorem Env.NoControlFlow.isControlFlow_false {env : Env} (henv : env.NoControlFlow)
    {n : String} {v : Value} (h : env n = some v) : v.isControlFlow = false :=
  Value.deepNoControlFlow_implies_isControlFlow_false (henv n v h)

/-- Builtins that preserve deepNoControlFlow: if all inputs are deep-no-CF,
    so is the output. -/
def Builtins.DeepNoControlFlow (bi : Builtins) : Prop :=
  ∀ f args v, bi f args = some v →
    (∀ a ∈ args, a.deepNoControlFlow = true) → v.deepNoControlFlow = true

theorem Builtins.defaultBuiltins_deepNoControlFlow : DeepNoControlFlow defaultBuiltins := by
  intro f args v h hargs
  revert h; unfold defaultBuiltins
  split <;> intro h <;> cases h <;>
    first | simp [Value.deepNoControlFlow] | skip
  all_goals exact hargs _ (List.Mem.head _)

end Hax

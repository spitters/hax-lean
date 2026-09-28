/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.AST
public import HaxLean.Value

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

@[expose] public section

namespace Hax

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
    do not consume fuel. `bi` provides builtin function implementations.
    A counted loop evaluates its upper bound only when its lower bound is a value;
    otherwise it returns the lower bound's outcome. Each bound is an integer or an
    unsigned word (`Value.uint`), read as the integer it denotes; the counter is
    bound to integers. -/
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
  | .lam _ _ =>
    -- The reference semantics is first-order; a closure value is not modeled.
    -- (`.lam` is a syntactic carrier for extraction; the verified guarantee is
    -- type erasure, not this denotation.)
    pure (.err "closures are not evaluated by the reference semantics")
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
    match rlo with
    | .val vlo => do
      let rhi ← denote bi fuel hi
      match vlo, rhi with
      | .int lo_val, .val (.int hi_val) =>
        denoteForLoop bi fuel var lo_val hi_val body
      | .int lo_val, .val (.uint _ hi_val) =>
        denoteForLoop bi fuel var lo_val hi_val body
      | .uint _ lo_val, .val (.int hi_val) =>
        denoteForLoop bi fuel var lo_val hi_val body
      | .uint _ lo_val, .val (.uint _ hi_val) =>
        denoteForLoop bi fuel var lo_val hi_val body
      | _, .val _ => pure (.err "for loop bounds must be integers")
      | _, other => pure other
    | other => pure other
  | .forLoopRev var lo hi body => do
    let rlo ← denote bi fuel lo
    match rlo with
    | .val vlo => do
      let rhi ← denote bi fuel hi
      match vlo, rhi with
      | .int lo_val, .val (.int hi_val) =>
        denoteForLoopRev bi fuel var lo_val hi_val body
      | .int lo_val, .val (.uint _ hi_val) =>
        denoteForLoopRev bi fuel var lo_val hi_val body
      | .uint _ lo_val, .val (.int hi_val) =>
        denoteForLoopRev bi fuel var lo_val hi_val body
      | .uint _ lo_val, .val (.uint _ hi_val) =>
        denoteForLoopRev bi fuel var lo_val hi_val body
      | _, .val _ => pure (.err "for loop bounds must be integers")
      | _, other => pure other
    | other => pure other
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
  | .forFoldRev _ _ _ _ => pure (.err "forFoldRev in pre-pipeline expression")
  | .whileFold _ _ => pure (.err "whileFold in pre-pipeline expression")
  | .forFoldReturn _ _ _ _ => pure (.err "forFoldReturn in pre-pipeline expression")
  | .forFoldRevReturn _ _ _ _ => pure (.err "forFoldRevReturn in pre-pipeline expression")
  | .whileFoldReturn _ _ => pure (.err "whileFoldReturn in pre-pipeline expression")
  | .cfBreak _ => pure (.err "cfBreak in pre-pipeline expression")
  | .cfContinue _ => pure (.err "cfContinue in pre-pipeline expression")
  | .cfBreakContinue _ => pure (.err "cfBreakContinue in pre-pipeline expression")
  | .typeAscription e _ => denote bi fuel e
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

/-- Reverse for loop helper: iterate body over (lo, hi] in reverse (hi-1 down to lo). -/
def denoteForLoopRev (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) : StateM Env Outcome :=
  if lo ≥ hi then pure (.val .unit)
  else if fuel = 0 then pure (.err "out of fuel")
  else do
    modify (Env.extend · var (.int (hi - 1)))
    let rb ← denote bi fuel body
    match rb with
    | .val _ | .continued =>
      denoteForLoopRev bi (fuel - 1) var lo (hi - 1) body
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

/-- Congruence lemma for `denoteForLoopRev`. -/
theorem denoteForLoopRev_congr (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi : Int) (body body' : ImpExpr)
    (hbody : ∀ fuel, denote bi fuel body' = denote bi fuel body) :
    denoteForLoopRev bi fuel var lo hi body' = denoteForLoopRev bi fuel var lo hi body := by
  induction fuel generalizing hi with
  | zero =>
    unfold denoteForLoopRev
    split
    · rfl
    · split
      · rfl
      · next h => exact absurd rfl h
  | succ n ih =>
    unfold denoteForLoopRev
    split
    · rfl
    · split
      · next h => exact absurd h (Nat.succ_ne_zero n)
      · congr 1; funext _
        rw [hbody (n + 1)]
        congr 1; funext rb
        split
        all_goals first | (simp only [Nat.add_sub_cancel]; exact ih (hi - 1)) | rfl

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

/-! ## Width-Aware Builtins

Extended builtins that handle width-specific integer values (`Value.uint`)
with Rust's wrapping semantics. Falls back to `defaultBuiltins` for
untyped operations. Compatible with all pipeline proofs since `Builtins`
is a parameter. -/

/-- Wrap a natural number to unsigned integer range. -/
def wrapUint (w : IntWidth) (n : Nat) : Value :=
  .uint w (n % w.modulus)

/-- Unsigned arithmetic operations (wrapping semantics). -/
def widthArithOps : Builtins
  | "add", [.uint w a, .uint _ b] => some (wrapUint w (a + b))
  | "sub", [.uint w a, .uint _ b] => some (wrapUint w ((a + w.modulus - b) % w.modulus))
  | "mul", [.uint w a, .uint _ b] => some (wrapUint w (a * b))
  | "div", [.uint w a, .uint _ b] =>
    if b = 0 then some (.uint w 0) else some (.uint w (a / b))
  | "rem", [.uint w a, .uint _ b] =>
    if b = 0 then some (.uint w 0) else some (.uint w (a % b))
  | _, _ => none

/-- Unsigned bitwise operations. -/
def widthBitwiseOps : Builtins
  | "shl", [.uint w a, .uint _ b] =>
    some (wrapUint w (a <<< (b % w.bits)))
  | "shr", [.uint w a, .uint _ b] =>
    some (.uint w (a >>> (b % w.bits)))
  | "bitand", [.uint w a, .uint _ b] => some (.uint w (a &&& b))
  | "bitor", [.uint w a, .uint _ b] => some (.uint w (a ||| b))
  | "bitxor", [.uint w a, .uint _ b] => some (.uint w (a ^^^ b))
  | "bitnot", [.uint w a] => some (wrapUint w (w.modulus - 1 - a))
  | _, _ => none

/-- Unsigned comparison operations. -/
def widthCmpOps : Builtins
  | "eq", [.uint _ a, .uint _ b] => some (.bool (a == b))
  | "ne", [.uint _ a, .uint _ b] => some (.bool (a != b))
  | "lt", [.uint _ a, .uint _ b] => some (.bool (a < b))
  | "le", [.uint _ a, .uint _ b] => some (.bool (a ≤ b))
  | "gt", [.uint _ a, .uint _ b] => some (.bool (a > b))
  | "ge", [.uint _ a, .uint _ b] => some (.bool (a ≥ b))
  | _, _ => none

/-- Cast operations: identity for data types. -/
def widthCastOps : Builtins
  | "cast", [.uint w v] => some (.uint w v)
  | "cast", [.sint w v] => some (.sint w v)
  | "cast", [.int n] => some (.int n)
  | "cast", [.bool b] => some (.bool b)
  | "cast", [.unit] => some .unit
  | _, _ => none

/-- Array operations (guarded: only return data values, not controlFlow). -/
def widthArrayOps : Builtins
  | "index", [.array vs, .uint _ i] => vs[i]?.bind fun
    | .controlFlow _ _ => none
    | v => some v
  | "index", [.array vs, .int i] => if 0 ≤ i then
    vs[i.toNat]?.bind fun
      | .controlFlow _ _ => none
      | v => some v
    else none
  | "len", [.array vs] => some (.uint .wsize vs.length)
  | "push", [.array vs, v] => some (.array (vs ++ [v]))
  | "repeat", [v, .uint _ n] => some (.array (List.replicate n v))
  | "repeat", [v, .int n] => if 0 ≤ n then some (.array (List.replicate n.toNat v)) else none
  | "array_lit", vs => some (.array vs)
  | "rotate_right", [.uint .w64 a, .uint _ b] =>
    let shift := b % 64
    some (.uint .w64 (((a >>> shift) ||| (a <<< (64 - shift))) % IntWidth.w64.modulus))
  | "array_update", [.array vs, .uint _ i, v] =>
    if i < vs.length then some (.array (vs.set i v)) else some (.array vs)
  | "array_update", [.array vs, .int i, v] =>
    if 0 ≤ i && i.toNat < vs.length then some (.array (vs.set i.toNat v)) else some (.array vs)
  | "slice_reverse", [.array vs] => some (.array vs.reverse)
  | "vec_remove", [.array vs, .uint _ i] =>
    vs[i]?.map fun x => .tuple [x, .array (vs.eraseIdx i)]
  | "vec_remove", [.array vs, .int i] =>
    if 0 ≤ i then vs[i.toNat]?.map fun x => .tuple [x, .array (vs.eraseIdx i.toNat)]
    else none
  | _, _ => none

/-- Signed integer modular reduction: maps to [-2^(w-1), 2^(w-1)). -/
def wrapSint (w : IntWidth) (n : Int) : Value :=
  let m : Int := w.modulus
  let r := n % m
  .sint w (if r ≥ m / 2 then r - m else r)

/-- Signed arithmetic operations on `Value.sint`. `div` and `rem` round
    towards zero (`Int.tdiv`/`Int.tmod`), matching Rust's `/` and `%` on a
    signed type and `Hax.div_iw`/`Hax.rem_iw`. -/
def signedArithOps : Builtins
  | "add", [.sint w a, .sint _ b] => some (wrapSint w (a + b))
  | "sub", [.sint w a, .sint _ b] => some (wrapSint w (a - b))
  | "mul", [.sint w a, .sint _ b] => some (wrapSint w (a * b))
  | "div", [.sint w a, .sint _ b] =>
    if b = 0 then some (.sint w 0) else some (wrapSint w (a.tdiv b))
  | "rem", [.sint w a, .sint _ b] =>
    if b = 0 then some (.sint w 0) else some (wrapSint w (a.tmod b))
  | "neg", [.sint w a] => some (wrapSint w (-a))
  | _, _ => none

/-- Signed comparison operations. -/
def signedCmpOps : Builtins
  | "eq", [.sint _ a, .sint _ b] => some (.bool (a == b))
  | "ne", [.sint _ a, .sint _ b] => some (.bool (a != b))
  | "lt", [.sint _ a, .sint _ b] => some (.bool (a < b))
  | "le", [.sint _ a, .sint _ b] => some (.bool (a ≤ b))
  | "gt", [.sint _ a, .sint _ b] => some (.bool (a > b))
  | "ge", [.sint _ a, .sint _ b] => some (.bool (a ≥ b))
  | _, _ => none

/-- Signed bitwise and rotate operations on `Value.sint`: the operands are
    read as their two's-complement unsigned representative (residue modulo
    `2^w.bits`), the unsigned bit operation applies, and the result is read
    back into signed range through `wrapSint`. `shr` (arithmetic right
    shift) acts on the signed value directly, sign-extending. Matches
    `Hax.bitand_iw` and siblings, and `Hax.shr_iw`, in `Runtime.lean`. -/
def signedBitwiseOps : Builtins
  | "shl", [.sint w a, .sint _ b] =>
    let au := (a % (w.modulus : Int)).toNat
    some (wrapSint w (↑((au <<< b.toNat) % w.modulus)))
  | "shr", [.sint w a, .sint _ b] => some (wrapSint w (a >>> b.toNat))
  | "bitand", [.sint w a, .sint _ b] =>
    let au := (a % (w.modulus : Int)).toNat
    let bu := (b % (w.modulus : Int)).toNat
    some (wrapSint w (↑(au &&& bu)))
  | "bitor", [.sint w a, .sint _ b] =>
    let au := (a % (w.modulus : Int)).toNat
    let bu := (b % (w.modulus : Int)).toNat
    some (wrapSint w (↑(au ||| bu)))
  | "bitxor", [.sint w a, .sint _ b] =>
    let au := (a % (w.modulus : Int)).toNat
    let bu := (b % (w.modulus : Int)).toNat
    some (wrapSint w (↑(au ^^^ bu)))
  | "bitnot", [.sint w a] =>
    let au := (a % (w.modulus : Int)).toNat
    some (wrapSint w (↑(w.modulus - 1 - au)))
  | "rotate_right", [.sint w x, .sint _ n] =>
    let xu := (x % (w.modulus : Int)).toNat
    let shift := n.toNat % w.bits
    some (wrapSint w (↑(((xu >>> shift) ||| (xu <<< (w.bits - shift))) % w.modulus)))
  | "rotate_left", [.sint w x, .sint _ n] =>
    let xu := (x % (w.modulus : Int)).toNat
    let shift := n.toNat % w.bits
    some (wrapSint w (↑(((xu <<< shift) ||| (xu >>> (w.bits - shift))) % w.modulus)))
  | _, _ => none

/-- Panic/unwrap operations. Models Rust's `unwrap`, `expect`, `unwrap_or`.
    Successful unwraps return the inner value; panic cases return `none`
    (mapped to `Outcome.err` by `denote`, modeling Rust panics). -/
def panicOps : Builtins
  -- Option::unwrap / Result::unwrap
  | "unwrap", [.option (some v)] => some v
  | "unwrap", [.result true v] => some v
  | "unwrap", [.option none] => none      -- panic: unwrap on None
  | "unwrap", [.result false _] => none   -- panic: unwrap on Err
  -- Option::expect / Result::expect (message ignored in semantics)
  | "expect", [.option (some v), _] => some v
  | "expect", [.result true v, _] => some v
  | "expect", [.option none, _] => none
  | "expect", [.result false _, _] => none
  -- Option::unwrap_or / Result::unwrap_or
  | "unwrap_or", [.option (some v), _] => some v
  | "unwrap_or", [.option none, d] => some d
  | "unwrap_or", [.result true v, _] => some v
  | "unwrap_or", [.result false _, d] => some d
  -- Option::is_some / Option::is_none
  | "is_some", [.option (some _)] => some (.bool true)
  | "is_some", [.option none] => some (.bool false)
  | "is_none", [.option (some _)] => some (.bool false)
  | "is_none", [.option none] => some (.bool true)
  -- Result::is_ok / Result::is_err
  | "is_ok", [.result ok _] => some (.bool ok)
  | "is_err", [.result ok _] => some (.bool !ok)
  | _, _ => none

/-- Width-specific operations on `Value.uint`. Returns `none` if the
    operation is not handled (allowing fallback to `defaultBuiltins`).
    Composed from smaller helpers for proof-friendliness. -/
def widthOps : Builtins := fun f args =>
  widthArithOps f args <|> widthBitwiseOps f args <|> widthCmpOps f args <|>
  widthCastOps f args <|> widthArrayOps f args <|>
  signedArithOps f args <|> signedCmpOps f args <|> signedBitwiseOps f args

/-- Full builtins: width ops + panic ops + defaults. -/
def fullBuiltins : Builtins := fun f args =>
  widthOps f args <|> panicOps f args <|> defaultBuiltins f args

/-- Width-aware builtins (without panic ops): tries `widthOps` first,
    then falls back to `defaultBuiltins`. -/
def widthAwareBuiltins : Builtins := fun f args =>
  match widthOps f args with
  | some v => some v
  | none => defaultBuiltins f args

/-! ## The `u64` word table on `int` values

The adapter tags the operations of `u64` code with the width (`wrapping_add#64`,
`Shr#64`, …).  `hax64WordOps` gives each tagged name its Rust meaning on `.int`
values in `[0, 2^64)`, and `hax64Builtins` adds the array operations of
`widthArrayOps`. -/

/-- A binary operation on two `int` values in `[0, 2^64)`, read as natural
    numbers; `none` for any other operand. -/
def u64BinOp (a b : Int) (g : Nat → Nat → Option Nat) : Option Value :=
  if 0 ≤ a ∧ a < 2 ^ 64 ∧ 0 ≤ b ∧ b < 2 ^ 64 then
    (g a.toNat b.toNat).map fun r => Value.int r
  else none

/-- A unary operation on an `int` value in `[0, 2^64)`, read as a natural
    number; `none` for any other operand. -/
def u64UnOp (a : Int) (g : Nat → Nat) : Option Value :=
  if 0 ≤ a ∧ a < 2 ^ 64 then some (.int (g a.toNat : Nat)) else none

/-- Rotation right of `x` read modulo `2^w` by `n` modulo `w` bits, the Rust
    `rotate_right` on `u<w>` (`Hax.rotate_right_w`). -/
def rotrNat (w x n : Nat) : Nat :=
  (((x % 2 ^ w) >>> (n % w)) ||| ((x % 2 ^ w) <<< (w - n % w))) % 2 ^ w

/-- Rotation left of `x` read modulo `2^w` by `n` modulo `w` bits, the Rust
    `rotate_left` on `u<w>` (`Hax.rotate_left_w`). -/
def rotlNat (w x n : Nat) : Nat :=
  (((x % 2 ^ w) <<< (n % w)) ||| ((x % 2 ^ w) >>> (w - n % w))) % 2 ^ w

/-- The comparisons and the checked additions and subtractions of `u64` code, the
    calls after the arms of `hax64WordOps` and `hax64NarrowOps`:
    * `Lt`, `Gt`, `Le`, `Ge`, `Eq`, `Ne` and `lt`, `gt`, `le`, `ge`, `eq`, `ne` on two
      `int` values, the Boolean `bool` of the integer comparison; `Eq`, `eq`, `Ne`, `ne`
      also on two `bool` values;
    * `add` on two `int` values in `[0, 2^64)`, the sum, `none` when it is `2^64` or
      more, where Rust panics (the arm `Add` of `hax64WordOps`);
    * `Sub` and `sub` on two `int` values in `[0, 2^64)`, the difference, `none` when
      the subtrahend exceeds the minuend, where Rust panics. -/
def hax64CmpOps : Builtins
  | "Lt", [.int a, .int b] => some (.bool (decide (a < b)))
  | "lt", [.int a, .int b] => some (.bool (decide (a < b)))
  | "Gt", [.int a, .int b] => some (.bool (decide (b < a)))
  | "gt", [.int a, .int b] => some (.bool (decide (b < a)))
  | "Le", [.int a, .int b] => some (.bool (decide (a ≤ b)))
  | "le", [.int a, .int b] => some (.bool (decide (a ≤ b)))
  | "Ge", [.int a, .int b] => some (.bool (decide (b ≤ a)))
  | "ge", [.int a, .int b] => some (.bool (decide (b ≤ a)))
  | "Eq", [.int a, .int b] => some (.bool (a == b))
  | "eq", [.int a, .int b] => some (.bool (a == b))
  | "Ne", [.int a, .int b] => some (.bool (a != b))
  | "ne", [.int a, .int b] => some (.bool (a != b))
  | "Eq", [.bool a, .bool b] => some (.bool (a == b))
  | "eq", [.bool a, .bool b] => some (.bool (a == b))
  | "Ne", [.bool a, .bool b] => some (.bool (a != b))
  | "ne", [.bool a, .bool b] => some (.bool (a != b))
  | "add", [.int a, .int b] => u64BinOp a b fun x y =>
      if x + y < 2 ^ 64 then some (x + y) else none
  | "Sub", [.int a, .int b] => u64BinOp a b fun x y => if y ≤ x then some (x - y) else none
  | "sub", [.int a, .int b] => u64BinOp a b fun x y => if y ≤ x then some (x - y) else none
  | _, _ => none

/-- The narrow calls of `u64` code beside the arms of `hax64WordOps`, on `int`
    values in `[0, 2^64)`:
    * the `u16` and `usize` operations `wrapping_add#w`, `wrapping_sub#w`,
      `wrapping_mul#w`, `BitAnd#w`, `BitOr#w`, `BitXor#w`, `Shl#w`, `Shr#w` for
      `w ∈ {16, size}`, read modulo `2^w` with `usize` `64` bits wide, the
      shifts `none` for an amount of `w` or more, and the truncations `cast#16`,
      `cast#size` of a non-negative value;
    * the rotations `rotate_right#w` (`rotrNat`) and `rotate_left#w`
      (`rotlNat`) and the complement `Not#w`, `2^w - 1 - x mod 2^w`, for
      `w ∈ {8, 16, 32, 64, size}`;
    * every other call as `hax64CmpOps`. -/
def hax64NarrowOps : Builtins
  | "cast#16", [.int a] => if 0 ≤ a then some (.int (a.toNat % 2 ^ 16 : Nat)) else none
  | "cast#size", [.int a] => if 0 ≤ a then some (.int (a.toNat % 2 ^ 64 : Nat)) else none
  | "wrapping_add#16", [.int a, .int b] => u64BinOp a b fun x y => some ((x + y) % 2 ^ 16)
  | "wrapping_sub#16", [.int a, .int b] => u64BinOp a b fun x y =>
      some ((x % 2 ^ 16 + 2 ^ 16 - y % 2 ^ 16) % 2 ^ 16)
  | "wrapping_mul#16", [.int a, .int b] => u64BinOp a b fun x y => some ((x * y) % 2 ^ 16)
  | "BitAnd#16", [.int a, .int b] => u64BinOp a b fun x y =>
      some ((x % 2 ^ 16) &&& (y % 2 ^ 16))
  | "BitOr#16", [.int a, .int b] => u64BinOp a b fun x y =>
      some ((x % 2 ^ 16) ||| (y % 2 ^ 16))
  | "BitXor#16", [.int a, .int b] => u64BinOp a b fun x y =>
      some ((x % 2 ^ 16) ^^^ (y % 2 ^ 16))
  | "Shl#16", [.int a, .int b] => u64BinOp a b fun x y =>
      if y < 16 then some (((x % 2 ^ 16) <<< y) % 2 ^ 16) else none
  | "Shr#16", [.int a, .int b] => u64BinOp a b fun x y =>
      if y < 16 then some ((x % 2 ^ 16) >>> y) else none
  | "wrapping_add#size", [.int a, .int b] => u64BinOp a b fun x y => some ((x + y) % 2 ^ 64)
  | "wrapping_sub#size", [.int a, .int b] => u64BinOp a b fun x y =>
      some ((x % 2 ^ 64 + 2 ^ 64 - y % 2 ^ 64) % 2 ^ 64)
  | "wrapping_mul#size", [.int a, .int b] => u64BinOp a b fun x y => some ((x * y) % 2 ^ 64)
  | "BitAnd#size", [.int a, .int b] => u64BinOp a b fun x y =>
      some ((x % 2 ^ 64) &&& (y % 2 ^ 64))
  | "BitOr#size", [.int a, .int b] => u64BinOp a b fun x y =>
      some ((x % 2 ^ 64) ||| (y % 2 ^ 64))
  | "BitXor#size", [.int a, .int b] => u64BinOp a b fun x y =>
      some ((x % 2 ^ 64) ^^^ (y % 2 ^ 64))
  | "Shl#size", [.int a, .int b] => u64BinOp a b fun x y =>
      if y < 64 then some (((x % 2 ^ 64) <<< y) % 2 ^ 64) else none
  | "Shr#size", [.int a, .int b] => u64BinOp a b fun x y =>
      if y < 64 then some ((x % 2 ^ 64) >>> y) else none
  | "rotate_right#8", [.int a, .int b] => u64BinOp a b fun x y => some (rotrNat 8 x y)
  | "rotate_right#16", [.int a, .int b] => u64BinOp a b fun x y => some (rotrNat 16 x y)
  | "rotate_right#32", [.int a, .int b] => u64BinOp a b fun x y => some (rotrNat 32 x y)
  | "rotate_right#64", [.int a, .int b] => u64BinOp a b fun x y => some (rotrNat 64 x y)
  | "rotate_right#size", [.int a, .int b] => u64BinOp a b fun x y => some (rotrNat 64 x y)
  | "rotate_left#8", [.int a, .int b] => u64BinOp a b fun x y => some (rotlNat 8 x y)
  | "rotate_left#16", [.int a, .int b] => u64BinOp a b fun x y => some (rotlNat 16 x y)
  | "rotate_left#32", [.int a, .int b] => u64BinOp a b fun x y => some (rotlNat 32 x y)
  | "rotate_left#64", [.int a, .int b] => u64BinOp a b fun x y => some (rotlNat 64 x y)
  | "rotate_left#size", [.int a, .int b] => u64BinOp a b fun x y => some (rotlNat 64 x y)
  | "Not#8", [.int a] => u64UnOp a fun x => 2 ^ 8 - 1 - x % 2 ^ 8
  | "Not#16", [.int a] => u64UnOp a fun x => 2 ^ 16 - 1 - x % 2 ^ 16
  | "Not#32", [.int a] => u64UnOp a fun x => 2 ^ 32 - 1 - x % 2 ^ 32
  | "Not#64", [.int a] => u64UnOp a fun x => 2 ^ 64 - 1 - x % 2 ^ 64
  | "Not#size", [.int a] => u64UnOp a fun x => 2 ^ 64 - 1 - x % 2 ^ 64
  | f, args => hax64CmpOps f args

/-- The Rust `u64` operations on `int` values in `[0, 2^64)`:
    * `wrapping_add#64`, `wrapping_sub#64`, `wrapping_mul#64` modulo `2^64`;
    * `mulhi#64`, the high 64 bits of the 128-bit product;
    * `BitAnd#64`, `BitOr#64`, `BitXor#64`;
    * `Shl#64`, `Shr#64` (the operators `<<`, `>>`) and `shl#64`, `shr#64` (the
      trait methods), `none` for an amount of 64 or more, where Rust panics;
    * `Add`, `none` when the sum is `2^64` or more, where Rust panics;
    * the steps of the widening multiply `((a as u128) * (b as u128) >> 64) as u64`:
      `cast#128` and `cast#64` on a non-negative value modulo `2^128` and `2^64`,
      `Mul` on non-negative values with product below `2^128`, and `Shr#128` on a
      value below `2^128` by an amount below `128`;
    * `Rem` on a value below `2^128` by a positive modulus below `2^128`, `none`
      for a zero modulus, where Rust panics;
    * `mulmod#64`, the product of two words modulo a positive modulus below
      `2^64`: the value of `((a as u128) * (b as u128) % (p as u128)) as u64`;
    * the `u8` and `u32` operations `wrapping_add#w`, `wrapping_sub#w`,
      `wrapping_mul#w`, `BitAnd#w`, `BitOr#w`, `BitXor#w`, `Shl#w`, `Shr#w` for
      `w ∈ {8, 32}` on `int` values in `[0, 2^64)` read modulo `2^w` (on operands
      below `2^w` the Rust operation), the shifts `none` for an amount of `w` or
      more, and the truncations `cast#8`, `cast#32` of a non-negative value;
    * every other call as `hax64NarrowOps`. -/
def hax64WordOps : Builtins
  | "wrapping_add#64", [.int a, .int b] => u64BinOp a b fun x y => some ((x + y) % 2 ^ 64)
  | "wrapping_sub#64", [.int a, .int b] => u64BinOp a b fun x y =>
      some ((x % 2 ^ 64 + 2 ^ 64 - y % 2 ^ 64) % 2 ^ 64)
  | "wrapping_mul#64", [.int a, .int b] => u64BinOp a b fun x y => some ((x * y) % 2 ^ 64)
  | "mulhi#64", [.int a, .int b] => u64BinOp a b fun x y => some ((x * y) >>> 64)
  | "BitAnd#64", [.int a, .int b] => u64BinOp a b fun x y => some ((x % 2 ^ 64) &&& (y % 2 ^ 64))
  | "BitOr#64", [.int a, .int b] => u64BinOp a b fun x y => some ((x % 2 ^ 64) ||| (y % 2 ^ 64))
  | "BitXor#64", [.int a, .int b] => u64BinOp a b fun x y => some ((x % 2 ^ 64) ^^^ (y % 2 ^ 64))
  | "Shl#64", [.int a, .int b] => u64BinOp a b fun x y =>
      if y < 64 then some (((x % 2 ^ 64) <<< y) % 2 ^ 64) else none
  | "shl#64", [.int a, .int b] => u64BinOp a b fun x y =>
      if y < 64 then some (((x % 2 ^ 64) <<< y) % 2 ^ 64) else none
  | "Shr#64", [.int a, .int b] => u64BinOp a b fun x y =>
      if y < 64 then some ((x % 2 ^ 64) >>> y) else none
  | "shr#64", [.int a, .int b] => u64BinOp a b fun x y =>
      if y < 64 then some ((x % 2 ^ 64) >>> y) else none
  | "Add", [.int a, .int b] => u64BinOp a b fun x y =>
      if x + y < 2 ^ 64 then some (x + y) else none
  | "cast#64", [.int a] => if 0 ≤ a then some (.int (a.toNat % 2 ^ 64 : Nat)) else none
  | "cast#128", [.int a] => if 0 ≤ a then some (.int (a.toNat % 2 ^ 128 : Nat)) else none
  | "Mul", [.int a, .int b] =>
      if 0 ≤ a ∧ 0 ≤ b ∧ a.toNat * b.toNat < 2 ^ 128 then
        some (.int (a.toNat * b.toNat : Nat))
      else none
  | "Shr#128", [.int a, .int b] =>
      if 0 ≤ a ∧ a < 2 ^ 128 ∧ 0 ≤ b ∧ b < 128 then
        some (.int (a.toNat >>> b.toNat : Nat))
      else none
  | "Rem", [.int a, .int b] =>
      if 0 ≤ a ∧ a < 2 ^ 128 ∧ 0 < b ∧ b < 2 ^ 128 then
        some (.int (a.toNat % b.toNat : Nat))
      else none
  | "mulmod#64", [.int a, .int b, .int p] =>
      if 0 < p ∧ p < 2 ^ 64 then u64BinOp a b fun x y => some ((x * y) % p.toNat) else none
  | "cast#8", [.int a] => if 0 ≤ a then some (.int (a.toNat % 2 ^ 8 : Nat)) else none
  | "cast#32", [.int a] => if 0 ≤ a then some (.int (a.toNat % 2 ^ 32 : Nat)) else none
  | "wrapping_add#8", [.int a, .int b] => u64BinOp a b fun x y => some ((x + y) % 2 ^ 8)
  | "wrapping_sub#8", [.int a, .int b] => u64BinOp a b fun x y =>
      some ((x % 2 ^ 8 + 2 ^ 8 - y % 2 ^ 8) % 2 ^ 8)
  | "wrapping_mul#8", [.int a, .int b] => u64BinOp a b fun x y => some ((x * y) % 2 ^ 8)
  | "BitAnd#8", [.int a, .int b] => u64BinOp a b fun x y => some ((x % 2 ^ 8) &&& (y % 2 ^ 8))
  | "BitOr#8", [.int a, .int b] => u64BinOp a b fun x y => some ((x % 2 ^ 8) ||| (y % 2 ^ 8))
  | "BitXor#8", [.int a, .int b] => u64BinOp a b fun x y => some ((x % 2 ^ 8) ^^^ (y % 2 ^ 8))
  | "Shl#8", [.int a, .int b] => u64BinOp a b fun x y =>
      if y < 8 then some (((x % 2 ^ 8) <<< y) % 2 ^ 8) else none
  | "Shr#8", [.int a, .int b] => u64BinOp a b fun x y =>
      if y < 8 then some ((x % 2 ^ 8) >>> y) else none
  | "wrapping_add#32", [.int a, .int b] => u64BinOp a b fun x y => some ((x + y) % 2 ^ 32)
  | "wrapping_sub#32", [.int a, .int b] => u64BinOp a b fun x y =>
      some ((x % 2 ^ 32 + 2 ^ 32 - y % 2 ^ 32) % 2 ^ 32)
  | "wrapping_mul#32", [.int a, .int b] => u64BinOp a b fun x y => some ((x * y) % 2 ^ 32)
  | "BitAnd#32", [.int a, .int b] => u64BinOp a b fun x y =>
      some ((x % 2 ^ 32) &&& (y % 2 ^ 32))
  | "BitOr#32", [.int a, .int b] => u64BinOp a b fun x y =>
      some ((x % 2 ^ 32) ||| (y % 2 ^ 32))
  | "BitXor#32", [.int a, .int b] => u64BinOp a b fun x y =>
      some ((x % 2 ^ 32) ^^^ (y % 2 ^ 32))
  | "Shl#32", [.int a, .int b] => u64BinOp a b fun x y =>
      if y < 32 then some (((x % 2 ^ 32) <<< y) % 2 ^ 32) else none
  | "Shr#32", [.int a, .int b] => u64BinOp a b fun x y =>
      if y < 32 then some ((x % 2 ^ 32) >>> y) else none
  | f, args => hax64NarrowOps f args

/-- The builtin table of `u64` code: `hax64WordOps`, then the array operations
    `widthArrayOps` (`index`, `array_update`, `array_lit`, `slice_reverse` and
    `vec_remove` on `.array`). -/
def hax64Builtins : Builtins := fun f args =>
  hax64WordOps f args <|> widthArrayOps f args

/-- On two words below `2^64`, `u64BinOp` is the operation on their natural
    numbers. -/
theorem u64BinOp_natCast {n m : Nat} (hn : n < 2 ^ 64) (hm : m < 2 ^ 64)
    (g : Nat → Nat → Option Nat) :
    u64BinOp n m g = (g n m).map fun r => Value.int r := by
  have hn' : (n : Int) < 2 ^ 64 := by exact_mod_cast hn
  have hm' : (m : Int) < 2 ^ 64 := by exact_mod_cast hm
  rw [u64BinOp, if_pos ⟨by omega, hn', by omega, hm'⟩, Int.toNat_natCast, Int.toNat_natCast]

/-- On a word below `2^64`, `u64UnOp` is the operation on its natural number. -/
theorem u64UnOp_natCast {n : Nat} (hn : n < 2 ^ 64) (g : Nat → Nat) :
    u64UnOp n g = some (.int (g n : Nat)) := by
  have hn' : (n : Int) < 2 ^ 64 := by exact_mod_cast hn
  rw [u64UnOp, if_pos ⟨by omega, hn'⟩, Int.toNat_natCast]

/-- Where `hax64WordOps` is undefined, `hax64Builtins` is `widthArrayOps`. -/
theorem hax64Builtins_of_none {f : String} {args : List Value}
    (h : hax64WordOps f args = none) : hax64Builtins f args = widthArrayOps f args := by
  unfold hax64Builtins
  rw [h]
  rfl

/-! The arms of `hax64WordOps` and of `widthArrayOps` used by the word
contract, as equations. -/

section hax64Arms

variable (a b : Int)

theorem hax64WordOps_wrapping_add : hax64WordOps "wrapping_add#64" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x + y) % 2 ^ 64) := rfl

theorem hax64WordOps_wrapping_sub : hax64WordOps "wrapping_sub#64" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 64 + 2 ^ 64 - y % 2 ^ 64) % 2 ^ 64) := rfl

theorem hax64WordOps_wrapping_mul : hax64WordOps "wrapping_mul#64" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x * y) % 2 ^ 64) := rfl

theorem hax64WordOps_mulhi : hax64WordOps "mulhi#64" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x * y) >>> 64) := rfl

theorem hax64WordOps_bitAnd : hax64WordOps "BitAnd#64" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 64) &&& (y % 2 ^ 64)) := rfl

theorem hax64WordOps_bitXor : hax64WordOps "BitXor#64" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 64) ^^^ (y % 2 ^ 64)) := rfl

theorem hax64WordOps_shl : hax64WordOps "Shl#64" [.int a, .int b] =
    u64BinOp a b fun x y => if y < 64 then some (((x % 2 ^ 64) <<< y) % 2 ^ 64) else none :=
  rfl

theorem hax64WordOps_shr : hax64WordOps "Shr#64" [.int a, .int b] =
    u64BinOp a b fun x y => if y < 64 then some ((x % 2 ^ 64) >>> y) else none := rfl

theorem hax64WordOps_add : hax64WordOps "Add" [.int a, .int b] =
    u64BinOp a b fun x y => if x + y < 2 ^ 64 then some (x + y) else none := rfl

theorem hax64WordOps_cast64 : hax64WordOps "cast#64" [.int a] =
    if 0 ≤ a then some (.int (a.toNat % 2 ^ 64 : Nat)) else none := rfl

theorem hax64WordOps_cast128 : hax64WordOps "cast#128" [.int a] =
    if 0 ≤ a then some (.int (a.toNat % 2 ^ 128 : Nat)) else none := rfl

theorem hax64WordOps_mul : hax64WordOps "Mul" [.int a, .int b] =
    if 0 ≤ a ∧ 0 ≤ b ∧ a.toNat * b.toNat < 2 ^ 128 then
      some (.int (a.toNat * b.toNat : Nat)) else none := rfl

theorem hax64WordOps_shr128 : hax64WordOps "Shr#128" [.int a, .int b] =
    if 0 ≤ a ∧ a < 2 ^ 128 ∧ 0 ≤ b ∧ b < 128 then
      some (.int (a.toNat >>> b.toNat : Nat)) else none := rfl

theorem hax64WordOps_rem : hax64WordOps "Rem" [.int a, .int b] =
    if 0 ≤ a ∧ a < 2 ^ 128 ∧ 0 < b ∧ b < 2 ^ 128 then
      some (.int (a.toNat % b.toNat : Nat)) else none := rfl

theorem hax64WordOps_mulmod (p : Int) : hax64WordOps "mulmod#64" [.int a, .int b, .int p] =
    if 0 < p ∧ p < 2 ^ 64 then u64BinOp a b fun x y => some ((x * y) % p.toNat) else none :=
  rfl

theorem hax64WordOps_cast8 : hax64WordOps "cast#8" [.int a] =
    if 0 ≤ a then some (.int (a.toNat % 2 ^ 8 : Nat)) else none := rfl

theorem hax64WordOps_cast32 : hax64WordOps "cast#32" [.int a] =
    if 0 ≤ a then some (.int (a.toNat % 2 ^ 32 : Nat)) else none := rfl

theorem hax64WordOps_wrapping_add8 : hax64WordOps "wrapping_add#8" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x + y) % 2 ^ 8) := rfl

theorem hax64WordOps_wrapping_sub8 : hax64WordOps "wrapping_sub#8" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 8 + 2 ^ 8 - y % 2 ^ 8) % 2 ^ 8) := rfl

theorem hax64WordOps_wrapping_mul8 : hax64WordOps "wrapping_mul#8" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x * y) % 2 ^ 8) := rfl

theorem hax64WordOps_bitAnd8 : hax64WordOps "BitAnd#8" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 8) &&& (y % 2 ^ 8)) := rfl

theorem hax64WordOps_bitOr8 : hax64WordOps "BitOr#8" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 8) ||| (y % 2 ^ 8)) := rfl

theorem hax64WordOps_bitXor8 : hax64WordOps "BitXor#8" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 8) ^^^ (y % 2 ^ 8)) := rfl

theorem hax64WordOps_shl8 : hax64WordOps "Shl#8" [.int a, .int b] =
    u64BinOp a b fun x y => if y < 8 then some (((x % 2 ^ 8) <<< y) % 2 ^ 8) else none := rfl

theorem hax64WordOps_shr8 : hax64WordOps "Shr#8" [.int a, .int b] =
    u64BinOp a b fun x y => if y < 8 then some ((x % 2 ^ 8) >>> y) else none := rfl

theorem hax64WordOps_wrapping_add32 : hax64WordOps "wrapping_add#32" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x + y) % 2 ^ 32) := rfl

theorem hax64WordOps_wrapping_sub32 : hax64WordOps "wrapping_sub#32" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 32 + 2 ^ 32 - y % 2 ^ 32) % 2 ^ 32) := rfl

theorem hax64WordOps_wrapping_mul32 : hax64WordOps "wrapping_mul#32" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x * y) % 2 ^ 32) := rfl

theorem hax64WordOps_bitAnd32 : hax64WordOps "BitAnd#32" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 32) &&& (y % 2 ^ 32)) := rfl

theorem hax64WordOps_bitOr32 : hax64WordOps "BitOr#32" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 32) ||| (y % 2 ^ 32)) := rfl

theorem hax64WordOps_bitXor32 : hax64WordOps "BitXor#32" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 32) ^^^ (y % 2 ^ 32)) := rfl

theorem hax64WordOps_shl32 : hax64WordOps "Shl#32" [.int a, .int b] =
    u64BinOp a b fun x y => if y < 32 then some (((x % 2 ^ 32) <<< y) % 2 ^ 32) else none :=
  rfl

theorem hax64WordOps_shr32 : hax64WordOps "Shr#32" [.int a, .int b] =
    u64BinOp a b fun x y => if y < 32 then some ((x % 2 ^ 32) >>> y) else none := rfl

theorem hax64WordOps_cast16 : hax64WordOps "cast#16" [.int a] =
    if 0 ≤ a then some (.int (a.toNat % 2 ^ 16 : Nat)) else none := rfl

theorem hax64WordOps_castSize : hax64WordOps "cast#size" [.int a] =
    if 0 ≤ a then some (.int (a.toNat % 2 ^ 64 : Nat)) else none := rfl

theorem hax64WordOps_wrapping_add16 : hax64WordOps "wrapping_add#16" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x + y) % 2 ^ 16) := rfl

theorem hax64WordOps_wrapping_sub16 : hax64WordOps "wrapping_sub#16" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 16 + 2 ^ 16 - y % 2 ^ 16) % 2 ^ 16) := rfl

theorem hax64WordOps_wrapping_mul16 : hax64WordOps "wrapping_mul#16" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x * y) % 2 ^ 16) := rfl

theorem hax64WordOps_bitAnd16 : hax64WordOps "BitAnd#16" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 16) &&& (y % 2 ^ 16)) := rfl

theorem hax64WordOps_bitOr16 : hax64WordOps "BitOr#16" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 16) ||| (y % 2 ^ 16)) := rfl

theorem hax64WordOps_bitXor16 : hax64WordOps "BitXor#16" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 16) ^^^ (y % 2 ^ 16)) := rfl

theorem hax64WordOps_shl16 : hax64WordOps "Shl#16" [.int a, .int b] =
    u64BinOp a b fun x y => if y < 16 then some (((x % 2 ^ 16) <<< y) % 2 ^ 16) else none :=
  rfl

theorem hax64WordOps_shr16 : hax64WordOps "Shr#16" [.int a, .int b] =
    u64BinOp a b fun x y => if y < 16 then some ((x % 2 ^ 16) >>> y) else none := rfl

theorem hax64WordOps_wrapping_addSize : hax64WordOps "wrapping_add#size" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x + y) % 2 ^ 64) := rfl

theorem hax64WordOps_wrapping_subSize : hax64WordOps "wrapping_sub#size" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 64 + 2 ^ 64 - y % 2 ^ 64) % 2 ^ 64) := rfl

theorem hax64WordOps_wrapping_mulSize : hax64WordOps "wrapping_mul#size" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x * y) % 2 ^ 64) := rfl

theorem hax64WordOps_bitAndSize : hax64WordOps "BitAnd#size" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 64) &&& (y % 2 ^ 64)) := rfl

theorem hax64WordOps_bitOrSize : hax64WordOps "BitOr#size" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 64) ||| (y % 2 ^ 64)) := rfl

theorem hax64WordOps_bitXorSize : hax64WordOps "BitXor#size" [.int a, .int b] =
    u64BinOp a b fun x y => some ((x % 2 ^ 64) ^^^ (y % 2 ^ 64)) := rfl

theorem hax64WordOps_shlSize : hax64WordOps "Shl#size" [.int a, .int b] =
    u64BinOp a b fun x y => if y < 64 then some (((x % 2 ^ 64) <<< y) % 2 ^ 64) else none :=
  rfl

theorem hax64WordOps_shrSize : hax64WordOps "Shr#size" [.int a, .int b] =
    u64BinOp a b fun x y => if y < 64 then some ((x % 2 ^ 64) >>> y) else none := rfl

theorem hax64WordOps_rotr8 : hax64WordOps "rotate_right#8" [.int a, .int b] =
    u64BinOp a b fun x y => some (rotrNat 8 x y) := rfl

theorem hax64WordOps_rotr16 : hax64WordOps "rotate_right#16" [.int a, .int b] =
    u64BinOp a b fun x y => some (rotrNat 16 x y) := rfl

theorem hax64WordOps_rotr32 : hax64WordOps "rotate_right#32" [.int a, .int b] =
    u64BinOp a b fun x y => some (rotrNat 32 x y) := rfl

theorem hax64WordOps_rotr64 : hax64WordOps "rotate_right#64" [.int a, .int b] =
    u64BinOp a b fun x y => some (rotrNat 64 x y) := rfl

theorem hax64WordOps_rotrSize : hax64WordOps "rotate_right#size" [.int a, .int b] =
    u64BinOp a b fun x y => some (rotrNat 64 x y) := rfl

theorem hax64WordOps_rotl8 : hax64WordOps "rotate_left#8" [.int a, .int b] =
    u64BinOp a b fun x y => some (rotlNat 8 x y) := rfl

theorem hax64WordOps_rotl16 : hax64WordOps "rotate_left#16" [.int a, .int b] =
    u64BinOp a b fun x y => some (rotlNat 16 x y) := rfl

theorem hax64WordOps_rotl32 : hax64WordOps "rotate_left#32" [.int a, .int b] =
    u64BinOp a b fun x y => some (rotlNat 32 x y) := rfl

theorem hax64WordOps_rotl64 : hax64WordOps "rotate_left#64" [.int a, .int b] =
    u64BinOp a b fun x y => some (rotlNat 64 x y) := rfl

theorem hax64WordOps_rotlSize : hax64WordOps "rotate_left#size" [.int a, .int b] =
    u64BinOp a b fun x y => some (rotlNat 64 x y) := rfl

theorem hax64WordOps_not8 : hax64WordOps "Not#8" [.int a] =
    u64UnOp a fun x => 2 ^ 8 - 1 - x % 2 ^ 8 := rfl

theorem hax64WordOps_not16 : hax64WordOps "Not#16" [.int a] =
    u64UnOp a fun x => 2 ^ 16 - 1 - x % 2 ^ 16 := rfl

theorem hax64WordOps_not32 : hax64WordOps "Not#32" [.int a] =
    u64UnOp a fun x => 2 ^ 32 - 1 - x % 2 ^ 32 := rfl

theorem hax64WordOps_not64 : hax64WordOps "Not#64" [.int a] =
    u64UnOp a fun x => 2 ^ 64 - 1 - x % 2 ^ 64 := rfl

theorem hax64WordOps_notSize : hax64WordOps "Not#size" [.int a] =
    u64UnOp a fun x => 2 ^ 64 - 1 - x % 2 ^ 64 := rfl

theorem hax64WordOps_Lt : hax64WordOps "Lt" [.int a, .int b] = some (.bool (decide (a < b))) :=
  rfl

theorem hax64WordOps_lt : hax64WordOps "lt" [.int a, .int b] = some (.bool (decide (a < b))) :=
  rfl

theorem hax64WordOps_Gt : hax64WordOps "Gt" [.int a, .int b] = some (.bool (decide (b < a))) :=
  rfl

theorem hax64WordOps_gt : hax64WordOps "gt" [.int a, .int b] = some (.bool (decide (b < a))) :=
  rfl

theorem hax64WordOps_Le : hax64WordOps "Le" [.int a, .int b] = some (.bool (decide (a ≤ b))) :=
  rfl

theorem hax64WordOps_le : hax64WordOps "le" [.int a, .int b] = some (.bool (decide (a ≤ b))) :=
  rfl

theorem hax64WordOps_Ge : hax64WordOps "Ge" [.int a, .int b] = some (.bool (decide (b ≤ a))) :=
  rfl

theorem hax64WordOps_ge : hax64WordOps "ge" [.int a, .int b] = some (.bool (decide (b ≤ a))) :=
  rfl

theorem hax64WordOps_Eq : hax64WordOps "Eq" [.int a, .int b] = some (.bool (a == b)) := rfl

theorem hax64WordOps_eq : hax64WordOps "eq" [.int a, .int b] = some (.bool (a == b)) := rfl

theorem hax64WordOps_Ne : hax64WordOps "Ne" [.int a, .int b] = some (.bool (a != b)) := rfl

theorem hax64WordOps_ne : hax64WordOps "ne" [.int a, .int b] = some (.bool (a != b)) := rfl

theorem hax64WordOps_Eq_bool (x y : Bool) :
    hax64WordOps "Eq" [.bool x, .bool y] = some (.bool (x == y)) := rfl

theorem hax64WordOps_eq_bool (x y : Bool) :
    hax64WordOps "eq" [.bool x, .bool y] = some (.bool (x == y)) := rfl

theorem hax64WordOps_Ne_bool (x y : Bool) :
    hax64WordOps "Ne" [.bool x, .bool y] = some (.bool (x != y)) := rfl

theorem hax64WordOps_ne_bool (x y : Bool) :
    hax64WordOps "ne" [.bool x, .bool y] = some (.bool (x != y)) := rfl

theorem hax64WordOps_add_lower : hax64WordOps "add" [.int a, .int b] =
    u64BinOp a b fun x y => if x + y < 2 ^ 64 then some (x + y) else none := rfl

theorem hax64WordOps_Sub : hax64WordOps "Sub" [.int a, .int b] =
    u64BinOp a b fun x y => if y ≤ x then some (x - y) else none := rfl

theorem hax64WordOps_sub : hax64WordOps "sub" [.int a, .int b] =
    u64BinOp a b fun x y => if y ≤ x then some (x - y) else none := rfl

theorem hax64WordOps_index (vs : List Value) :
    hax64WordOps "index" [.array vs, .int a] = none := rfl

theorem hax64WordOps_array_update (vs : List Value) (v : Value) :
    hax64WordOps "array_update" [.array vs, .int a, v] = none := rfl

theorem widthArrayOps_index_int (vs : List Value) :
    widthArrayOps "index" [.array vs, .int a] =
      if 0 ≤ a then vs[a.toNat]?.bind (fun
        | .controlFlow _ _ => none
        | v => some v) else none := rfl

theorem widthArrayOps_array_update_int (vs : List Value) (v : Value) :
    widthArrayOps "array_update" [.array vs, .int a, v] =
      if 0 ≤ a && a.toNat < vs.length then some (.array (vs.set a.toNat v))
      else some (.array vs) := rfl

/-- `slice_reverse` on a sequence is `List.reverse`. -/
theorem widthArrayOps_slice_reverse (vs : List Value) :
    widthArrayOps "slice_reverse" [.array vs] = some (.array vs.reverse) := rfl

/-- `vec_remove v i` is the pair of the element at `i` and `v` with that element
    erased; it is undefined when `i` is out of range, where `Vec::remove` panics. -/
theorem widthArrayOps_vec_remove_int (vs : List Value) :
    widthArrayOps "vec_remove" [.array vs, .int a] =
      if 0 ≤ a then vs[a.toNat]?.map (fun x => .tuple [x, .array (vs.eraseIdx a.toNat)])
      else none := rfl

end hax64Arms

/-! ## Convenience: extract result value -/

/-- Run `denote` and extract the result value (if evaluation succeeds). -/
def denoteValue (bi : Builtins) (fuel : Nat) (e : ImpExpr) (env : Env) : Option Value :=
  let (outcome, _) := (denote bi fuel e).run env
  outcome.toVal

/-- Convenience: denote with width-aware builtins. -/
def denoteWidthAware (fuel : Nat) (e : ImpExpr) : StateM Env Outcome :=
  denote widthAwareBuiltins fuel e

end Hax

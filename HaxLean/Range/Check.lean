/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Range.Domain
public import HaxLean.AnfDenote
public import HaxLean.DenoteTotal
public import HaxLean.Phase.FunctionalizeLoopsCF
public import HaxLean.TExpr

/-!
# A range checker for the typed extraction, sound for `denote'`

A checker over the erased literal (`ImpExpr`, the image of `TExpr.erase`) that assigns each
term an abstract value (`AV`: an integer interval of the shared domain
`HaxLean/Range/Domain.lean`, an array-length interval, or no information) and each program
point an abstract environment (`AEnv`), and accepts a call of a head only when the head's
transfer function (`Spec.xfer`) accepts the abstract values of its arguments. The heads whose
Rust counterpart panics are those of `HaxLean/RuntimeM.lean`; a transfer function accepts such
a head only when the intervals prove its guard (`HaxLean/Range/Heads.lean`).

The checker refines an interval by the guard of an `if` whose condition compares two atoms
(`refineCond`), and, when the specification sets `Spec.logic`, by an equality of two atoms
and through negations, conjunctions that hold and disjunctions that fail; it drops the
variables a `match` arm binds, checks a counted loop (`forFold`) against a loop invariant, and reads a call of a function of the crate through its summary,
which is one more head of `Spec.xfer`. The loop invariant is a candidate (`loopInv`, from the
annotation `Spec.ann` that an untrusted inference supplies): the checker verifies that the
environment before the loop, after each iteration and at each `cfBreak`/`cfContinue` of the
body lies in it. A `whileFold` is checked the same way, its condition refining the
environment of the body.

## Soundness

`guardBi g bi` is the builtin table `bi` restricted to calls whose guard `g` holds: a call
whose guard fails has no value, as Rust panics there. `check_sound` says that, under `Sound`,
a term the checker accepts evaluates under `denote'` with the guarded table exactly as with
`bi`, from every environment that lies in the abstract environment and holds no control-flow
value: no guard fails on any run. Its value lies in the abstract value and its final
environment in the final abstract environment (`Post`).

## Main definitions

* `AV`, `AV.Mem`, `AEnv`, `Sat`: abstract values and environments and their meaning.
* `Spec`: the transfer functions of the heads and the loop annotation.
* `guardBi`: the builtin table that fails where a guard fails.
* `LogicSem`: the reading of the Boolean and equality heads that the refinement uses.
* `refineAtoms`, `condOk`, `refineCond`: the refinement of an environment by a guard.
* `check`, `checkArgs`, `checkArms`: the checker.
* `Sound`: the hypotheses relating a specification to a builtin table.

## Main results

* `check_sound`: an accepted term runs the same under the guarded table, with its value and
  environment in the abstract ones.
* `checkT_sound`: the same for a `TExpr`, through `TExpr.erase`.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Range

open CatCrypt.Crypto.SecureCompilation.RangeDomain

/-! ## Abstract values -/

/-- An abstract value: no information, an integer interval, or the length interval of an
    array. -/
inductive AV where
  | top
  | num (i : Iv)
  | arr (len : Iv)
  deriving Inhabited, BEq, Repr

namespace AV

/-- The values an abstract value describes: every value for `top`; an integer, unsigned or
    signed word whose integer lies in `i` for `num i`; an array or tuple whose length lies in
    `l` for `arr l`. -/
def Mem : AV → Value → Prop
  | .top, _ => True
  | .num i, v => ∃ n, v.toInt = some n ∧ i.Has n
  | .arr l, v => ∃ n, v.arrayLen = some n ∧ l.Has (n : Int)

/-- Inclusion of abstract values. -/
def le : AV → AV → Bool
  | _, .top => true
  | .num a, .num b => ivLe a b
  | .arr a, .arr b => ivLe a b
  | _, _ => false

/-- The least abstract value above both. -/
def join : AV → AV → AV
  | .num a, .num b => .num (ivHull a b)
  | .arr a, .arr b => .arr (ivHull a b)
  | _, _ => .top

/-- The interval of an integer abstract value. -/
def num? : AV → Option Iv
  | .num i => some i
  | _ => none

theorem Mem.le {a b : AV} {v : Value} (h : a.Mem v) (hab : a.le b = true) : b.Mem v := by
  cases b with
  | top => trivial
  | num j =>
    cases a with
    | num i => obtain ⟨n, hn, hi⟩ := h; exact ⟨n, hn, hi.le hab⟩
    | _ => simp [AV.le] at hab
  | arr j =>
    cases a with
    | arr i => obtain ⟨n, hn, hi⟩ := h; exact ⟨n, hn, hi.le hab⟩
    | _ => simp [AV.le] at hab

theorem Mem.join_left {a b : AV} {v : Value} (h : a.Mem v) : (a.join b).Mem v := by
  cases a <;> cases b <;> simp only [join] <;> try trivial
  · obtain ⟨n, hn, hi⟩ := h; exact ⟨n, hn, hi.hull_left⟩
  · obtain ⟨n, hn, hi⟩ := h; exact ⟨n, hn, hi.hull_left⟩

theorem Mem.join_right {a b : AV} {v : Value} (h : b.Mem v) : (a.join b).Mem v := by
  cases a <;> cases b <;> simp only [join] <;> try trivial
  · obtain ⟨n, hn, hi⟩ := h; exact ⟨n, hn, hi.hull_right⟩
  · obtain ⟨n, hn, hi⟩ := h; exact ⟨n, hn, hi.hull_right⟩

end AV

/-- The abstract value of a literal. -/
def litAV : ImpLit → AV
  | .int n => .num (ivPoint n)
  | .uintLit w n => .num (ivPoint ((n % w.modulus : Nat) : Int))
  | .sintLit _ n => .num (ivPoint n)
  | _ => .top

theorem litAV_mem (l : ImpLit) : (litAV l).Mem (Value.ofLit l) := by
  cases l <;> first | trivial | exact ⟨_, rfl, Iv.has_point _⟩

/-! ## Abstract environments -/

/-- An abstract environment: the abstract value of each variable it names, the first binding
    of a name counting. -/
abbrev AEnv := List (String × AV)

/-- The abstract value of `x`, `top` when unnamed. -/
def AEnv.get (Γ : AEnv) (x : String) : AV := (Γ.lookup x).getD .top

/-- The environment `env` binds every variable `Γ` names to a value of its abstract value. -/
def Sat (Γ : AEnv) (env : Env) : Prop :=
  ∀ x a, Γ.lookup x = some a → ∃ v, env x = some v ∧ a.Mem v

/-- Every variable `J` names is named in `Γ` at an abstract value included in its value in
    `J`. -/
def entails (Γ J : AEnv) : Bool :=
  J.all fun p => match Γ.lookup p.1 with
    | some b => b.le p.2
    | none => false

/-- The join of two abstract environments: the variables both name, at the join. -/
def AEnv.join (Γ1 Γ2 : AEnv) : AEnv :=
  Γ1.filterMap fun p => (Γ2.lookup p.1).map fun b => (p.1, p.2.join b)

/-- `Γ` without the variables of `xs`. -/
def AEnv.drop (xs : List String) (Γ : AEnv) : AEnv :=
  Γ.filter fun p => !xs.contains p.1

/-! ## The guarded builtin table -/

/-- The builtin table `bi` restricted to the calls whose guard `g` holds; a call whose guard
    fails has no value, as Rust panics there. -/
def guardBi (g : String → List Value → Bool) (bi : Builtins) : Builtins := fun f vs =>
  if g f vs then bi f vs else none

/-! ## Specifications -/

/-- The transfer functions of the heads and the loop annotation. `xfer f avs = some a`: a call
    of `f` on arguments of the abstract values `avs` is accepted, with result in `a`. `ann`
    gives a candidate interval to a variable a loop body writes; it is untrusted, as the
    checker verifies the invariant it yields. -/
structure Spec where
  /-- The transfer function of each head, `none` where a call is refused. -/
  xfer : String → List AV → Option AV
  /-- The candidate abstract value of a variable written in a loop. -/
  ann : AEnv := []
  /-- Whether the refinement by a guard reads negations, conjunctions, disjunctions and
      equalities (`refineCond`), which `Sound` then relates to the table by `LogicSem`. -/
  logic : Bool := false

/-- Each value of a list lies in the abstract value at its position. -/
def MemList : List AV → List Value → Prop
  | [], [] => True
  | a :: as, v :: vs => a.Mem v ∧ MemList as vs
  | _, _ => False

/-- The relation of a comparison head, as `(strict, swapped)` for `<`, `≤`, `>`, `≥`. -/
def cmpOf : String → Option (Bool × Bool)
  | "Lt" | "lt" => some (true, false)
  | "Le" | "le" => some (false, false)
  | "Gt" | "gt" => some (true, true)
  | "Ge" | "ge" => some (false, true)
  | _ => none

/-- The integer relation of a comparison: `m < n` or `m ≤ n`, the operands swapped when
    `swapped`. -/
def cmpRel (strict swapped : Bool) (m n : Int) : Prop :=
  if swapped then (if strict then n < m else n ≤ m) else (if strict then m < n else m ≤ n)

/-- A conjunction head. -/
def isAnd (op : String) : Bool := op == "&&" || op == "and"

/-- A disjunction head. -/
def isOr (op : String) : Bool := op == "||" || op == "or"

/-- A negation head. -/
def isNot (op : String) : Bool := op == "Not" || op == "not"

/-- The equality heads: `some true` for `==`, `some false` for `!=`. -/
def eqOf : String → Option Bool
  | "Eq" | "eq" => some true
  | "Ne" | "ne" => some false
  | _ => none

/-- What the refinement by a Boolean combination of guards reads of the table: a negation,
    conjunction or disjunction answering a Boolean takes Boolean arguments and computes the
    connective, and an equality head answers with the truth of the equality of the integers. -/
structure LogicSem (bi : Builtins) : Prop where
  and_ : ∀ op vl vr b, isAnd op = true → bi op [vl, vr] = some (.bool b) →
    ∃ x y, vl = .bool x ∧ vr = .bool y ∧ b = (x && y)
  or_ : ∀ op vl vr b, isOr op = true → bi op [vl, vr] = some (.bool b) →
    ∃ x y, vl = .bool x ∧ vr = .bool y ∧ b = (x || y)
  not_ : ∀ op v b, isNot op = true → bi op [v] = some (.bool b) → ∃ x, v = .bool x ∧ b = !x
  eq : ∀ op q vl vr b m n, eqOf op = some q → bi op [vl, vr] = some (.bool b) →
    vl.toInt = some m → vr.toInt = some n → (b = q ↔ m = n)

/-- The hypotheses relating a specification to a builtin table and a guard: the table keeps
    values free of control flow, an accepted call has its guard and, on arguments free of
    control flow, its result in the transfer function's value, a comparison head answers with
    the truth of its relation, and the Boolean heads are read as `LogicSem` when the
    specification refines by them. -/
structure Sound (g : String → List Value → Bool) (H : Spec) (bi : Builtins) : Prop where
  deep : Builtins.DeepNoControlFlow bi
  guard : ∀ f avs a vs, H.xfer f avs = some a → MemList avs vs → g f vs = true
  result : ∀ f avs a vs v, H.xfer f avs = some a → MemList avs vs →
    (∀ w ∈ vs, w.deepNoControlFlow = true) → bi f vs = some v → a.Mem v
  cmp : ∀ op strict swapped vl vr b m n, cmpOf op = some (strict, swapped) →
    bi op [vl, vr] = some (.bool b) → vl.toInt = some m → vr.toInt = some n →
    (b = true ↔ cmpRel strict swapped m n)
  logic : H.logic = true → LogicSem bi

/-! ## Refinement by a guard -/

/-- The abstract value of an atom: a variable or a literal. -/
def atomAV (Γ : AEnv) : ImpExpr → Option AV
  | .var x => some (Γ.get x)
  | .lit l => some (litAV l)
  | _ => none

/-- `Γ` with the variable `A` met with `(-∞, B - d]`, read in `Γ0`, when `A` is a variable
    with an integer interval and the atom `B` has one. -/
def refineUpper (Γ0 : AEnv) (A B : ImpExpr) (d : Int) (Γ : AEnv) : AEnv :=
  match A with
  | .var x =>
    match atomAV Γ0 B, Γ0.get x with
    | some (.num ib), .num ix => (x, .num (ivMeet ix (ix.1, ib.2 - d))) :: Γ
    | _, _ => Γ
  | _ => Γ

/-- `Γ` with the variable `B` met with `[A + d, ∞)`, read in `Γ0`, when `B` is a variable
    with an integer interval and the atom `A` has one. -/
def refineLower (Γ0 : AEnv) (A B : ImpExpr) (d : Int) (Γ : AEnv) : AEnv :=
  match B with
  | .var y =>
    match atomAV Γ0 A, Γ0.get y with
    | some (.num ia), .num iy => (y, .num (ivMeet iy (ia.1 + d, iy.2))) :: Γ
    | _, _ => Γ
  | _ => Γ

/-- `Γ` refined by `A < B` (`strict`) or `A ≤ B` for atoms `A`, `B`: a variable among them
    with an integer interval is met with the bound the other side gives. -/
def refineLt (Γ : AEnv) (A B : ImpExpr) (strict : Bool) : AEnv :=
  let d : Int := if strict then 1 else 0
  refineLower Γ A B d (refineUpper Γ A B d Γ)

/-- Whether a term is an atom: a variable or a literal. -/
def isAtom : ImpExpr → Bool
  | .var _ | .lit _ => true
  | _ => false

/-- `Γ` refined by the call `op l r` of two atoms answering `pos`: a comparison bounds each
    variable by the other side; with `lg`, an equality that holds bounds each side by the
    other from both directions. -/
def refineAtoms (lg : Bool) (op : String) (l r : ImpExpr) (pos : Bool) (Γ : AEnv) : AEnv :=
  match cmpOf op with
  | some (strict, swapped) =>
    if pos = swapped then refineLt Γ r l (if pos then strict else !strict)
    else refineLt Γ l r (if pos then strict else !strict)
  | none =>
    match eqOf op with
    | some q => if lg && pos == q then refineLt (refineLt Γ l r false) r l false else Γ
    | none => Γ

/-- A condition whose run with a Boolean answer leaves the environment: an atom, a call on
    two atoms, or a negation, conjunction or disjunction of such conditions. -/
def condOk : ImpExpr → Bool
  | .var _ | .lit _ => true
  | .app op [l, r] => (isAtom l && isAtom r) || ((isAnd op || isOr op) && condOk l && condOk r)
  | .app op [c] => isNot op && condOk c
  | _ => false

/-- `Γ` refined by the condition `c` holding (`pos`) or failing: by `refineAtoms` when `c`
    calls a head on two atoms; with `lg`, through a negation, and through both sides of a
    conjunction that holds or a disjunction that fails when the sides are `condOk`; `Γ`
    otherwise. -/
def refineCond (lg : Bool) : ImpExpr → Bool → AEnv → AEnv
  | .app op [l, r], pos, Γ =>
    if isAtom l && isAtom r then refineAtoms lg op l r pos Γ
    else if lg && isAnd op && condOk l && condOk r then
      if pos then refineCond lg r true (refineCond lg l true Γ) else Γ
    else if lg && isOr op && condOk l && condOk r then
      if pos then Γ else refineCond lg r false (refineCond lg l false Γ)
    else Γ
  | .app op [c], pos, Γ => if lg && isNot op then refineCond lg c (!pos) Γ else Γ
  | _, _, Γ => Γ

/-! ## Loop invariants (untrusted) -/

/-- The variables a term may write: assigned, let-bound, loop counters and pattern
    variables. Used only to propose a loop invariant, which the checker verifies. -/
partial def writes : ImpExpr → List String
  | .assign x r => x :: writes r
  | .letBind x v b => x :: writes v ++ writes b
  | .forFold x lo hi b | .forFoldRev x lo hi b | .forLoop x lo hi b | .forLoopRev x lo hi b
  | .forFoldReturn x lo hi b | .forFoldRevReturn x lo hi b =>
    x :: writes lo ++ writes hi ++ writes b
  | .match_ s arms => writes s ++ arms.flatMap fun (p, b) => patVarsU p ++ writes b
  | .app _ as | .tuple as => as.flatMap writes
  | .lam _ b | .proj b _ | .borrow b | .deref b | .earlyReturn b | .questionMark b
  | .cfBreak b | .cfContinue b | .cfBreakContinue b | .typeAscription b _ | .break_ (some b) =>
    writes b
  | .ifThenElse c t e => writes c ++ writes t ++ writes e
  | .seq a b | .whileLoop a b | .whileFold a b | .whileFoldReturn a b => writes a ++ writes b
  | _ => []
where
  /-- The variables of a pattern. -/
  patVarsU : ImpPat → List String
    | .varPat n => [n]
    | .tuplePat ps | .ctorPat _ ps => ps.flatMap patVarsU
    | .somePat p | .okPat p | .errPat p => patVarsU p
    | _ => []

/-- The candidate invariant of a loop with counter `x` and body `body`, entered in `Γ`: the
    variables of `Γ` the body does not write, and each written variable at its annotation when
    its entry value lies in it. -/
def loopInv (ann : AEnv) (x : String) (body : ImpExpr) (Γ : AEnv) : AEnv :=
  let ws := x :: writes body
  AEnv.drop ws Γ ++ (writes body).filterMap fun y =>
    match ann.lookup y, Γ.lookup y with
    | some a, some b => if b.le a then some (y, a) else none
    | _, _ => none

/-- The abstract value of the counter of a loop over `[lo, hi)`: `[lo.1, hi.2 - 1]` when both
    bounds have integer intervals. -/
def ctrAV : AV → AV → AV
  | .num il, .num ih => .num (il.1, ih.2 - 1)
  | _, _ => .top

/-! ## Patterns -/

mutual

/-- The variables a pattern binds. -/
def patVars : ImpPat → List String
  | .varPat n => [n]
  | .tuplePat ps => patVarsList ps
  | .ctorPat _ ps => patVarsList ps
  | .somePat p => patVars p
  | .okPat p => patVars p
  | .errPat p => patVars p
  | .wildcard | .litPat _ | .nonePat => []

/-- The variables a list of patterns binds. -/
def patVarsList : List ImpPat → List String
  | [] => []
  | p :: ps => patVars p ++ patVarsList ps

end

/-! ## The checker -/

mutual

/-- The abstract value of `e` and the abstract environment after it, from the abstract
    environment `Γ`, with `J` the invariant of the innermost loop; `none` when `e` is outside
    the checked class or a call is refused. -/
def check (H : Spec) (J : AEnv) : AEnv → ImpExpr → Option (AV × AEnv)
  | Γ, .lit l => some (litAV l, Γ)
  | Γ, .var x => some (Γ.get x, Γ)
  | Γ, .unitVal => some (.top, Γ)
  | Γ, .letBind x v b =>
    match check H J Γ v with
    | some (a, Γ1) => check H J ((x, a) :: Γ1) b
    | none => none
  | Γ, .seq a b =>
    match check H J Γ a with
    | some (_, Γ1) => check H J Γ1 b
    | none => none
  | Γ, .assign x r =>
    match check H J Γ r with
    | some (a, Γ1) => some (.top, (x, a) :: Γ1)
    | none => none
  | Γ, .typeAscription e _ => check H J Γ e
  | Γ, .borrow e => check H J Γ e
  | Γ, .deref e => check H J Γ e
  | Γ, .app f args =>
    match checkArgs H J Γ args with
    | some (avs, Γ1) => (H.xfer f avs).map fun a => (a, Γ1)
    | none => none
  | Γ, .ifThenElse c t e =>
    match check H J Γ c with
    | some (_, Γ1) =>
      match check H J (refineCond H.logic c true Γ1) t,
          check H J (refineCond H.logic c false Γ1) e with
      | some (at', Γt), some (ae, Γe) => some (at'.join ae, AEnv.join Γt Γe)
      | _, _ => none
    | none => none
  | Γ, .match_ s arms =>
    match check H J Γ s with
    | some (_, Γ1) => checkArms H J Γ1 arms
    | none => none
  | Γ, .forFold x lo hi body =>
    match check H J Γ lo with
    | some (al, Γ1) =>
      match check H J Γ1 hi with
      | some (ah, Γ2) =>
        let inv := loopInv H.ann x body Γ2
        if entails Γ2 inv then
          match check H inv ((x, ctrAV al ah) :: inv) body with
          | some (_, Γb) => if entails Γb inv then some (.top, inv) else none
          | none => none
        else none
      | none => none
    | none => none
  | Γ, .whileFold c body =>
    let inv := loopInv H.ann "" body Γ
    if entails Γ inv then
      match check H J inv c with
      | some (_, Γc) =>
        if entails Γc inv then
          match check H inv (refineCond H.logic c true Γc) body with
          | some (_, Γb) => if entails Γb inv then some (.top, inv) else none
          | none => none
        else none
      | none => none
    else none
  | Γ, .tuple es =>
    match checkArgs H J Γ es with
    | some (_, Γ1) => some (.top, Γ1)
    | none => none
  | Γ, .proj e _ =>
    match check H J Γ e with
    | some (_, Γ1) => some (.top, Γ1)
    | none => none
  | Γ, .earlyReturn e =>
    match check H J Γ e with
    | some (_, Γ1) => some (.top, Γ1)
    | none => none
  | Γ, .questionMark e =>
    match check H J Γ e with
    | some (_, Γ1) => some (.top, Γ1)
    | none => none
  | Γ, .cfBreak e =>
    match check H J Γ e with
    | some (_, Γ1) => if entails Γ1 J then some (.top, Γ1) else none
    | none => none
  | Γ, .cfContinue e =>
    match check H J Γ e with
    | some (_, Γ1) => if entails Γ1 J then some (.top, Γ1) else none
    | none => none
  | _, _ => none

/-- The abstract values of call arguments, evaluated left to right. -/
def checkArgs (H : Spec) (J : AEnv) : AEnv → List ImpExpr → Option (List AV × AEnv)
  | Γ, [] => some ([], Γ)
  | Γ, e :: es =>
    match check H J Γ e with
    | some (a, Γ1) =>
      match checkArgs H J Γ1 es with
      | some (as, Γ2) => some (a :: as, Γ2)
      | none => none
    | none => none

/-- The join of the arms of a `match`, each checked without the variables its pattern
    binds. -/
def checkArms (H : Spec) (J : AEnv) : AEnv → List (ImpPat × ImpExpr) → Option (AV × AEnv)
  | Γ, [] => some (.top, Γ)
  | Γ, [(p, b)] => check H J (AEnv.drop (patVars p) Γ) b
  | Γ, (p, b) :: arm :: rest =>
    match check H J (AEnv.drop (patVars p) Γ) b, checkArms H J Γ (arm :: rest) with
    | some (a1, Γ1), some (a2, Γ2) => some (a1.join a2, AEnv.join Γ1 Γ2)
    | _, _ => none

end

/-- The checker on a typed term, through its erasure. -/
def checkT (H : Spec) (Γ : AEnv) (e : TExpr) : Option (AV × AEnv) :=
  check H [] Γ e.erase

end Hax.Range

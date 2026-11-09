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
public import HaxLean.Phase.InlineLocalClosures
public import HaxLean.TExpr

/-!
# A range checker for the typed extraction, sound for `denote'`

A checker over the erased literal (`ImpExpr`, the image of `TExpr.erase`) that assigns each
term an abstract value (`AV`: an integer interval of the shared domain
`HaxLean/Range/Domain.lean`, an array-length interval, an index with relational facts, or no
information) and each program point an abstract environment (`AEnv`), and accepts a call of a
head only when the head's transfer function (`Spec.xfer`) accepts the abstract values of its
arguments, or when its relational transfer function (`Spec.xrel`) accepts them together with
the facts the environment gives between its arguments. The heads whose Rust counterpart
panics are those of `HaxLean/RuntimeM.lean`; a transfer function accepts such a head only when
the intervals or the facts prove its guard (`HaxLean/Range/Heads.lean`).

A relational fact `(s, c)` of an index variable `x` (`AV.idx`) says `x + c < len s`; with
`c = -1` it says `x ≤ len s`. The environment carries the facts of each variable beside its
interval. A fact is set by a guard `x < len s` or `x ≤ len s` (`refineLen`) and on the counter
of a counted loop over `[lo, len s)` whose body binds no `s` (`ctrAVLen`); it is kept through
joins that both sides have (`AV.join`), and dropped when its array variable is bound
(`AEnv.kill`, `AEnv.drop`).

The checker refines an interval by the guard of an `if` whose condition compares two atoms
(`refineCond`), and, when the specification sets `Spec.logic`, by an equality of two atoms
and through negations, conjunctions that hold and disjunctions that fail; it drops the
variables a `match` arm binds, checks a counted loop (`forFold`) against a loop invariant,
and reads a call of a function of the crate through its summary, which is one more head of
`Spec.xfer`. The loop invariant is a candidate (`loopInv`, from the annotation `Spec.ann`
that an untrusted inference supplies): the checker verifies that the environment before the
loop, after each iteration and at each `cfBreak`/`cfContinue` of the body lies in it. A
`whileFold` is checked the same way, its condition refining the environment of the body.

## Soundness

`guardBi g bi` is the builtin table `bi` restricted to calls whose guard `g` holds: a call
whose guard fails has no value, as Rust panics there. `check_sound` says that, under `Sound`,
a term the checker accepts evaluates under `denote'` with the guarded table exactly as with
`bi`, from every environment that lies in the abstract environment and holds no control-flow
value: no guard fails on any run. Its value lies in the abstract value and its final
environment in the final abstract environment (`Post`).

## Main definitions

* `AV`, `AV.Mem`, `AV.RelIn`, `AEnv`, `Sat`: abstract values and environments and their
  meaning.
* `Spec`: the transfer functions of the heads and the loop annotation.
* `guardBi`: the builtin table that fails where a guard fails.
* `LogicSem`: the reading of the Boolean and equality heads that the refinement uses.
* `refineAtoms`, `refineLen`, `condOk`, `refineCond`: the refinement of an environment by a
  guard.
* `argRels`: the facts between the arguments of a call.
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

/-- An abstract value: no information, an integer interval, the length interval of an array,
    or an index: an integer at least `lo`, at most `hi` when given, with the facts `rs`, each
    `(s, c)` meaning that the integer plus `c` lies below the length of the array `s`. -/
inductive AV where
  | top
  | num (i : Iv)
  | arr (len : Iv)
  | idx (lo : Int) (hi : Option Int) (rs : List (String × Int))
  deriving Inhabited, BEq, Repr

/-- An optional upper bound below another, `none` being no bound. -/
def hiLe : Option Int → Option Int → Bool
  | _, none => true
  | some a, some b => decide (a ≤ b)
  | none, some _ => false

/-- The larger of two optional upper bounds. -/
def hiJoin : Option Int → Option Int → Option Int
  | some a, some b => some (max a b)
  | _, _ => none

/-- The smaller of an optional upper bound and a bound. -/
def hiMin : Option Int → Int → Int
  | some a, b => min a b
  | none, b => b

/-- Every fact of `rb` follows from a fact of `ra` on the same array. -/
def relsLe (rb ra : List (String × Int)) : Bool :=
  rb.all fun p => ra.any fun q => q.1 == p.1 && decide (p.2 ≤ q.2)

/-- The facts on the arrays of `ra` that `rb` also has, at the weaker offset. -/
def relsJoin (ra rb : List (String × Int)) : List (String × Int) :=
  ra.filterMap fun p => (rb.lookup p.1).map fun c => (p.1, min p.2 c)

namespace AV

/-- The values an abstract value describes: every value for `top`; an integer, unsigned or
    signed word whose integer lies in `i` for `num i`; an array or tuple whose length lies in
    `l` for `arr l`; an integer, unsigned or signed word whose integer lies between the bounds
    for `idx`, whose facts `RelIn` reads. -/
def Mem : AV → Value → Prop
  | .top, _ => True
  | .num i, v => ∃ n, v.toInt = some n ∧ i.Has n
  | .arr l, v => ∃ n, v.arrayLen = some n ∧ l.Has (n : Int)
  | .idx lo hi _, v => ∃ n, v.toInt = some n ∧ lo ≤ n ∧ ∀ h, hi = some h → n ≤ h

/-- The facts of an abstract value: those of an index, none otherwise. -/
def rels : AV → List (String × Int)
  | .idx _ _ rs => rs
  | _ => []

/-- The fact `(s, c)` holds of the integer `k` in `env`: `s` is an array of length above
    `k + c`. -/
def LenGt (env : Env) (k : Int) (p : String × Int) : Prop :=
  ∃ w n, env p.1 = some w ∧ w.arrayLen = some n ∧ k + p.2 < (n : Int)

/-- The facts of `a` hold of the value `v` in `env`. -/
def RelIn (env : Env) (a : AV) (v : Value) : Prop :=
  ∀ p ∈ a.rels, ∃ k, v.toInt = some k ∧ LenGt env k p

/-- Inclusion of abstract values. -/
def le : AV → AV → Bool
  | _, .top => true
  | .num a, .num b => ivLe a b
  | .arr a, .arr b => ivLe a b
  | .idx a ha ra, .idx b hb rb => decide (b ≤ a) && hiLe ha hb && relsLe rb ra
  | .idx a (some h) _, .num b => ivLe (a, h) b
  | .num a, .idx b hb [] => decide (b ≤ a.1) && hiLe (some a.2) hb
  | _, _ => false

/-- An abstract value above both. -/
def join : AV → AV → AV
  | .num a, .num b => .num (ivHull a b)
  | .arr a, .arr b => .arr (ivHull a b)
  | .idx a ha ra, .idx b hb rb => .idx (min a b) (hiJoin ha hb) (relsJoin ra rb)
  | .idx a (some h) _, .num b => .num (ivHull (a, h) b)
  | .num a, .idx b (some h) _ => .num (ivHull a (b, h))
  | _, _ => .top

/-- The abstract value without its facts: an index with both bounds as an interval. -/
def strip : AV → AV
  | .idx lo (some h) _ => .num (lo, h)
  | .idx lo none _ => .idx lo none []
  | a => a

/-- The abstract value without the facts on the arrays of `xs`. -/
def forget (xs : List String) : AV → AV
  | .idx lo hi rs => .idx lo hi (rs.filter fun p => !xs.contains p.1)
  | a => a

/-- The abstract value with the fact `p`, for an integer abstract value; unchanged
    otherwise. -/
def addRel (p : String × Int) : AV → AV
  | .num i => .idx i.1 (some i.2) [p]
  | .idx lo hi rs => .idx lo hi (p :: rs)
  | a => a

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
    | idx lo hi rs =>
      cases hi with
      | some h' =>
        obtain ⟨n, hn, h1, h2⟩ := h
        exact ⟨n, hn, Iv.Has.le ⟨h1, h2 h' rfl⟩ hab⟩
      | none => simp [AV.le] at hab
    | _ => simp [AV.le] at hab
  | arr j =>
    cases a with
    | arr i => obtain ⟨n, hn, hi⟩ := h; exact ⟨n, hn, hi.le hab⟩
    | _ => simp [AV.le] at hab
  | idx lo hi rs =>
    cases a with
    | num i =>
      cases rs with
      | nil =>
        obtain ⟨n, hn, h1, h2⟩ := h
        simp only [AV.le, Bool.and_eq_true, decide_eq_true_eq] at hab
        refine ⟨n, hn, by omega, fun h' hh => ?_⟩
        subst hh
        simp only [hiLe, decide_eq_true_eq] at hab
        omega
      | cons _ _ => simp [AV.le] at hab
    | idx lo' hi' rs' =>
      obtain ⟨n, hn, h1, h2⟩ := h
      simp only [AV.le, Bool.and_eq_true, decide_eq_true_eq] at hab
      refine ⟨n, hn, by omega, fun h' hh => ?_⟩
      subst hh
      cases hi' with
      | none => simp [hiLe] at hab
      | some a' =>
        have := h2 a' rfl
        simp only [hiLe, decide_eq_true_eq] at hab
        omega
    | _ => simp [AV.le] at hab

theorem Mem.join_left {a b : AV} {v : Value} (h : a.Mem v) : (a.join b).Mem v := by
  cases a <;> cases b <;> simp only [join] <;> try trivial
  · obtain ⟨n, hn, hi⟩ := h; exact ⟨n, hn, hi.hull_left⟩
  · rename_i i lo hi rs
    cases hi with
    | some h' => obtain ⟨n, hn, hi⟩ := h; exact ⟨n, hn, hi.hull_left⟩
    | none => trivial
  · obtain ⟨n, hn, hi⟩ := h; exact ⟨n, hn, hi.hull_left⟩
  · rename_i lo hi rs i
    cases hi with
    | some h' =>
      obtain ⟨n, hn, h1, h2⟩ := h
      exact ⟨n, hn, Iv.Has.hull_left ⟨h1, h2 h' rfl⟩⟩
    | none => trivial
  · rename_i lo hi rs lo' hi' rs'
    obtain ⟨n, hn, h1, h2⟩ := h
    refine ⟨n, hn, by omega, fun h' hh => ?_⟩
    cases hi <;> cases hi' <;> simp only [hiJoin, reduceCtorEq, Option.some.injEq] at hh
    subst hh
    have := h2 _ rfl
    omega

theorem Mem.join_right {a b : AV} {v : Value} (h : b.Mem v) : (a.join b).Mem v := by
  cases a <;> cases b <;> simp only [join] <;> try trivial
  · obtain ⟨n, hn, hi⟩ := h; exact ⟨n, hn, hi.hull_right⟩
  · rename_i i lo hi rs
    cases hi with
    | some h' =>
      obtain ⟨n, hn, h1, h2⟩ := h
      exact ⟨n, hn, Iv.Has.hull_right ⟨h1, h2 h' rfl⟩⟩
    | none => trivial
  · obtain ⟨n, hn, hi⟩ := h; exact ⟨n, hn, hi.hull_right⟩
  · rename_i lo hi rs i
    cases hi with
    | some h' => obtain ⟨n, hn, hi⟩ := h; exact ⟨n, hn, hi.hull_right⟩
    | none => trivial
  · rename_i lo hi rs lo' hi' rs'
    obtain ⟨n, hn, h1, h2⟩ := h
    refine ⟨n, hn, by omega, fun h' hh => ?_⟩
    cases hi <;> cases hi' <;> simp only [hiJoin, reduceCtorEq, Option.some.injEq] at hh
    subst hh
    have := h2 _ rfl
    omega

theorem Mem.strip {a : AV} {v : Value} (h : a.Mem v) : a.strip.Mem v := by
  cases a with
  | idx lo hi rs =>
    cases hi with
    | some h' => obtain ⟨n, hn, h1, h2⟩ := h; exact ⟨n, hn, h1, h2 h' rfl⟩
    | none => exact h
  | _ => exact h

theorem rels_strip (a : AV) : a.strip.rels = [] := by
  cases a with
  | idx lo hi rs => cases hi <;> rfl
  | _ => rfl

theorem RelIn.strip (env : Env) (a : AV) (v : Value) : a.strip.RelIn env v := by
  intro p hp
  rw [rels_strip] at hp
  cases hp

theorem LenGt.weaken {env : Env} {k : Int} {p q : String × Int} (h : LenGt env k q)
    (h1 : q.1 = p.1) (h2 : p.2 ≤ q.2) : LenGt env k p := by
  obtain ⟨w, n, hw, hn, hk⟩ := h
  exact ⟨w, n, h1 ▸ hw, hn, by omega⟩

theorem RelIn.le {a b : AV} {env : Env} {v : Value} (h : a.RelIn env v)
    (hab : a.le b = true) : b.RelIn env v := by
  intro p hp
  cases b with
  | idx lo hi rs =>
    cases a with
    | idx lo' hi' rs' =>
      simp only [AV.le, Bool.and_eq_true] at hab
      simp only [rels] at hp
      obtain ⟨q, hq, hq1, hq2⟩ : ∃ q ∈ rs', q.1 = p.1 ∧ p.2 ≤ q.2 := by
        have := List.all_eq_true.1 hab.2 p hp
        simpa [List.any_eq_true] using this
      obtain ⟨k, hk, hl⟩ := h q hq
      exact ⟨k, hk, hl.weaken hq1 hq2⟩
    | num i =>
      cases rs with
      | nil => cases hp
      | cons _ _ => simp [AV.le] at hab
    | _ => simp [AV.le] at hab
  | _ => cases hp

/-- A key that `lookup` finds is paired in the list with the value it returns. -/
theorem mem_of_lookup_eq {l : List (String × Int)} {s : String} {c : Int}
    (h : l.lookup s = some c) : (s, c) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons q l ih =>
    by_cases hq : s = q.1
    · subst hq
      simp only [List.lookup, BEq.rfl, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · have hb : (s == q.1) = false := by simpa using hq
      simp only [List.lookup, hb] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem RelIn.join_left {a b : AV} {env : Env} {v : Value} (h : a.RelIn env v) :
    (a.join b).RelIn env v := by
  intro p hp
  match a, b with
  | .idx lo hi rs, .idx lo' hi' rs' =>
    simp only [join, rels, relsJoin, List.mem_filterMap, Option.map_eq_some_iff] at hp
    obtain ⟨q, hq, c, -, rfl⟩ := hp
    obtain ⟨k, hk, hl⟩ := h q hq
    exact ⟨k, hk, hl.weaken rfl (Int.min_le_left _ _)⟩
  | .top, _ | .arr _, .top | .arr _, .num _ | .arr _, .arr _ | .arr _, .idx _ _ _
  | .num _, .top | .num _, .arr _ | .num _, .num _
  | .num _, .idx _ none _ | .num _, .idx _ (some _) _ | .idx _ _ _, .top
  | .idx _ _ _, .arr _ | .idx _ none _, .num _ | .idx _ (some _) _, .num _ =>
    simp [join, rels] at hp

theorem RelIn.join_right {a b : AV} {env : Env} {v : Value} (h : b.RelIn env v) :
    (a.join b).RelIn env v := by
  intro p hp
  match a, b with
  | .idx lo hi rs, .idx lo' hi' rs' =>
    simp only [join, rels, relsJoin, List.mem_filterMap, Option.map_eq_some_iff] at hp
    obtain ⟨q, -, c, hc, rfl⟩ := hp
    obtain ⟨k, hk, hl⟩ := h (q.1, c) (mem_of_lookup_eq hc)
    exact ⟨k, hk, hl.weaken rfl (Int.min_le_right _ _)⟩
  | .top, _ | .arr _, .top | .arr _, .num _ | .arr _, .arr _ | .arr _, .idx _ _ _
  | .num _, .top | .num _, .arr _ | .num _, .num _
  | .num _, .idx _ none _ | .num _, .idx _ (some _) _ | .idx _ _ _, .top
  | .idx _ _ _, .arr _ | .idx _ none _, .num _ | .idx _ (some _) _, .num _ =>
    simp [join, rels] at hp

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

/-- The environment `env` binds every variable `Γ` names to a value of its abstract value, of
    whose facts hold in `env`. -/
def Sat (Γ : AEnv) (env : Env) : Prop :=
  ∀ x a, Γ.lookup x = some a → ∃ v, env x = some v ∧ a.Mem v ∧ a.RelIn env v

/-- Every variable `J` names is named in `Γ` at an abstract value included in its value in
    `J`. -/
def entails (Γ J : AEnv) : Bool :=
  J.all fun p => match Γ.lookup p.1 with
    | some b => b.le p.2
    | none => false

/-- The join of two abstract environments: the variables both name, at the join. -/
def AEnv.join (Γ1 Γ2 : AEnv) : AEnv :=
  Γ1.filterMap fun p => (Γ2.lookup p.1).map fun b => (p.1, p.2.join b)

/-- `Γ` without the variables of `xs` and without the facts on the arrays of `xs`. -/
def AEnv.drop (xs : List String) (Γ : AEnv) : AEnv :=
  (Γ.filter fun p => !xs.contains p.1).map fun p => (p.1, p.2.forget xs)

/-- `Γ` without the facts on the array `x`, for a binding of `x`. -/
def AEnv.kill (x : String) (Γ : AEnv) : AEnv :=
  Γ.map fun p => (p.1, p.2.forget [x])

/-! ## The guarded builtin table -/

/-- The builtin table `bi` restricted to the calls whose guard `g` holds; a call whose guard
    fails has no value, as Rust panics there. -/
def guardBi (g : String → List Value → Bool) (bi : Builtins) : Builtins := fun f vs =>
  if g f vs then bi f vs else none

/-! ## Specifications -/

/-- The transfer functions of the heads and the loop annotation. `xfer f avs = some a`: a call
    of `f` on arguments of the abstract values `avs` is accepted, with result in `a`.
    `xrel f avs rs = some a`: a call of `f` on such arguments that also satisfy the facts `rs`
    (`RelArgs`) is accepted, with result in `a`. `ann` gives a candidate abstract value to a
    variable a loop body writes; it is untrusted, as the checker verifies the invariant it
    yields. -/
structure Spec where
  /-- The transfer function of each head, `none` where a call is refused. -/
  xfer : String → List AV → Option AV
  /-- The transfer function of each head on arguments with facts between them. -/
  xrel : String → List AV → List (Nat × Nat × Int) → Option AV := fun _ _ _ => none
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

/-- The facts `rs` between the values `vs`: for `(i, j, c)`, the integer at position `i` plus
    `c` lies below the length of the array at position `j`. -/
def RelArgs (rs : List (Nat × Nat × Int)) (vs : List Value) : Prop :=
  ∀ r ∈ rs, ∃ k n, (vs[r.1]?).bind Value.toInt = some k ∧
    (vs[r.2.1]?).bind Value.arrayLen = some n ∧ k + r.2.2 < (n : Int)

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
    control flow, its result in the transfer function's value (for `xrel`, on arguments that
    satisfy the facts), a comparison head answers with the truth of its relation, `len`
    answers with the length of an array, and the Boolean heads are read as `LogicSem` when the
    specification refines by them. -/
structure Sound (g : String → List Value → Bool) (H : Spec) (bi : Builtins) : Prop where
  deep : Builtins.DeepNoControlFlow bi
  guard : ∀ f avs a vs, H.xfer f avs = some a → MemList avs vs → g f vs = true
  result : ∀ f avs a vs v, H.xfer f avs = some a → MemList avs vs →
    (∀ w ∈ vs, w.deepNoControlFlow = true) → bi f vs = some v → a.Mem v
  relGuard : ∀ f avs rs a vs, H.xrel f avs rs = some a → MemList avs vs → RelArgs rs vs →
    g f vs = true
  relResult : ∀ f avs rs a vs v, H.xrel f avs rs = some a → MemList avs vs → RelArgs rs vs →
    (∀ w ∈ vs, w.deepNoControlFlow = true) → bi f vs = some v → a.Mem v
  cmp : ∀ op strict swapped vl vr b m n, cmpOf op = some (strict, swapped) →
    bi op [vl, vr] = some (.bool b) → vl.toInt = some m → vr.toInt = some n →
    (b = true ↔ cmpRel strict swapped m n)
  len : ∀ arr v, bi "len" [arr] = some v → ∃ n, arr.arrayLen = some n ∧ v.toInt = some n
  logic : H.logic = true → LogicSem bi

/-! ## Refinement by a guard -/

/-- The abstract value of an atom: a variable or a literal. -/
def atomAV (Γ : AEnv) : ImpExpr → Option AV
  | .var x => some (Γ.get x).strip
  | .lit l => some (litAV l)
  | _ => none

/-- `Γ` with the variable `A` met with `(-∞, B - d]`, read in `Γ0`, when `A` is a variable
    with an integer interval or an index and the atom `B` has an interval. -/
def refineUpper (Γ0 : AEnv) (A B : ImpExpr) (d : Int) (Γ : AEnv) : AEnv :=
  match A with
  | .var x =>
    match atomAV Γ0 B, Γ0.get x with
    | some (.num ib), .num ix => (x, .num (ivMeet ix (ix.1, ib.2 - d))) :: Γ
    | some (.num ib), .idx lo hi rs => (x, .idx lo (some (hiMin hi (ib.2 - d))) rs) :: Γ
    | _, _ => Γ
  | _ => Γ

/-- `Γ` with the variable `B` met with `[A + d, ∞)`, read in `Γ0`, when `B` is a variable
    with an integer interval or an index and the atom `A` has an interval. -/
def refineLower (Γ0 : AEnv) (A B : ImpExpr) (d : Int) (Γ : AEnv) : AEnv :=
  match B with
  | .var y =>
    match atomAV Γ0 A, Γ0.get y with
    | some (.num ia), .num iy => (y, .num (ivMeet iy (ia.1 + d, iy.2))) :: Γ
    | some (.num ia), .idx lo hi rs => (y, .idx (max lo (ia.1 + d)) hi rs) :: Γ
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

/-- The variable a term reads in place: a variable under borrows, dereferences and type
    ascriptions. -/
def argVar : ImpExpr → Option String
  | .var x => some x
  | .borrow e => argVar e
  | .deref e => argVar e
  | .typeAscription e _ => argVar e
  | _ => none

/-- The array whose length a term reads: `s` for `len` of a read of `s`. -/
def lenVar : ImpExpr → Option String
  | .app "len" [e] => argVar e
  | _ => none

/-- An operand of a comparison the refinement reads: an atom or the length of an array. -/
def isCmpArg (e : ImpExpr) : Bool := isAtom e || (lenVar e).isSome

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

/-- `Γ` with the fact `A < len s` (`strict`) or `A ≤ len s` added to the variable `A`, when
    `B` is the length of the array `s`. -/
def addLen (Γ : AEnv) (A B : ImpExpr) (strict : Bool) : AEnv :=
  match A, lenVar B with
  | .var x, some s => (x, (Γ.get x).addRel (s, if strict then 0 else -1)) :: Γ
  | _, _ => Γ

/-- `Γ` refined by the comparison `op l r` answering `pos`, of an atom and the length of an
    array: the variable below the length gets the fact. -/
def refineLen (op : String) (l r : ImpExpr) (pos : Bool) (Γ : AEnv) : AEnv :=
  match cmpOf op with
  | some (strict, swapped) =>
    if pos = swapped then addLen Γ r l (if pos then strict else !strict)
    else addLen Γ l r (if pos then strict else !strict)
  | none => Γ

/-- A condition whose run with a Boolean answer leaves the environment: a call on two atoms
    or lengths of arrays, or a negation, conjunction or disjunction of such conditions. -/
def condOk : ImpExpr → Bool
  | .var _ | .lit _ => true
  | .app op [l, r] =>
    (isCmpArg l && isCmpArg r) || ((isAnd op || isOr op) && condOk l && condOk r)
  | .app op [c] => isNot op && condOk c
  | _ => false

/-- `Γ` refined by the condition `c` holding (`pos`) or failing: by `refineAtoms` when `c`
    calls a head on two atoms, by `refineLen` when on an atom and the length of an array;
    with `lg`, through a negation, and through both sides of a conjunction that holds or a
    disjunction that fails when the sides are `condOk`; `Γ` otherwise. -/
def refineCond (lg : Bool) : ImpExpr → Bool → AEnv → AEnv
  | .app op [l, r], pos, Γ =>
    if isAtom l && isAtom r then refineAtoms lg op l r pos Γ
    else if isCmpArg l && isCmpArg r then refineLen op l r pos Γ
    else if lg && isAnd op && condOk l && condOk r then
      if pos then refineCond lg r true (refineCond lg l true Γ) else Γ
    else if lg && isOr op && condOk l && condOk r then
      if pos then Γ else refineCond lg r false (refineCond lg l false Γ)
    else Γ
  | .app op [c], pos, Γ => if lg && isNot op then refineCond lg c (!pos) Γ else Γ
  | _, _, Γ => Γ

/-! ## Facts between the arguments of a call -/

/-- An argument read in place: a literal or a variable under borrows, dereferences and type
    ascriptions. -/
def pureArg (e : ImpExpr) : Bool := isAtom e || (argVar e).isSome

/-- The facts between the arguments of a call that `Γ` gives, when every argument is read in
    place: `(i, j, c)` when argument `i` reads a variable with the fact `(s, c)` and argument
    `j` reads `s`. -/
def argRels (Γ : AEnv) (args : List ImpExpr) : List (Nat × Nat × Int) :=
  if args.all pureArg then
    let vs := args.map argVar
    (List.range vs.length).flatMap fun i =>
      match vs[i]?.join with
      | some x => (Γ.get x).rels.flatMap fun p =>
          (List.range vs.length).filterMap fun j =>
            if vs[j]?.join = some p.1 then some (i, j, p.2) else none
      | none => []
  else []

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

/-- The abstract value of the counter `x` of a loop over `[lo, hi)` with body `body`: when
    `hi` is the length of an array `s` other than `x` that the body binds nowhere, an index
    from `lo.1` with the fact `x < len s`; `ctrAV` otherwise. -/
def ctrAVLen (x : String) (hi body : ImpExpr) (al ah : AV) : AV :=
  match lenVar hi, al with
  | some s, .num il =>
    if s != x && InlineLocalClosures.frameOk (fun _ => true) (fun n => n != s) (fun _ => true)
        body then
      .idx il.1 ((ah.num?).map fun ih => ih.2 - 1) [(s, 0)]
    else ctrAV al ah
  | _, _ => ctrAV al ah

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
  | Γ, .var x => some ((Γ.get x).strip, Γ)
  | Γ, .unitVal => some (.top, Γ)
  | Γ, .letBind x v b =>
    match check H J Γ v with
    | some (a, Γ1) => check H J ((x, a.strip) :: AEnv.kill x Γ1) b
    | none => none
  | Γ, .seq a b =>
    match check H J Γ a with
    | some (_, Γ1) => check H J Γ1 b
    | none => none
  | Γ, .assign x r =>
    match check H J Γ r with
    | some (a, Γ1) => some (.top, (x, a.strip) :: AEnv.kill x Γ1)
    | none => none
  | Γ, .typeAscription e _ => check H J Γ e
  | Γ, .borrow e => check H J Γ e
  | Γ, .deref e => check H J Γ e
  | Γ, .app f args =>
    match checkArgs H J Γ args with
    | some (avs, Γ1) =>
      match H.xfer f avs with
      | some a => some (a, Γ1)
      | none => (H.xrel f avs (argRels Γ args)).map fun a => (a, Γ1)
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
          match check H inv ((x, ctrAVLen x hi body al ah) :: AEnv.kill x inv) body with
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

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.TExpr
public import HaxLean.Semantics

/-!
# Counted loops over an inclusive range

A Rust loop `for v in lo..=hi` runs its body for `v = lo, lo + 1, ..., hi`,
once with `v = hi` when `hi` is the maximum of its type, and not at all when
`hi < lo`. The adapter lowers it to the counted loop `forLoop v lo hi' body`,
which iterates the integer interval `[lo, hi')`; `hi'` is `inclusiveUpper hi`.

## Main definitions

* `inclusiveUpper` — the exclusive bound `hi + 1`: an integer literal when `hi`
  is an integer literal, else the application `range_incl_end hi`.
* `inclusiveUpperT` — the same bound on typed expressions.
* `RangeInclEnd` — a builtin table whose `range_incl_end` is the integer
  `k + 1` on every value denoting the integer `k`.
* `denoteForInclusive` — the reference iteration over `lo..=hi`: it compares
  `lo` with `hi` and never computes `hi + 1`.

## Main statements

* `inclusiveUpperT_erase` — `inclusiveUpperT` erases to `inclusiveUpper`.
* `fullBuiltins_rangeInclEnd`, `widthAwareBuiltins_rangeInclEnd`,
  `hax64Builtins_rangeInclEnd` — the three tables satisfy `RangeInclEnd`.
* `denoteForLoop_succ_eq_denoteForInclusive` — the counted loop over
  `[lo, hi + 1)` is the reference iteration over `lo..=hi`.
* `denote_forLoop_inclusiveUpper_lit` — on a literal upper bound (of any
  width, including the maximum of the type), the lowered loop denotes the
  reference iteration, for every builtin table.
* `denote_forLoop_inclusiveUpper_end` — on any other upper bound, the lowered
  loop denotes the reference iteration whenever the builtin table's
  `range_incl_end` is the bound's integer plus `1`.
* `denote_forLoop_inclusiveUpper_toInt` — on any other upper bound whose value
  is an unsigned, signed or unbounded integer, under a table satisfying
  `RangeInclEnd`, the lowered loop denotes the reference iteration, including
  at the maximum of the type.
* `denoteForInclusive_of_lt` — `lo..=hi` with `hi < lo` runs the body zero times.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax

/-- The exclusive upper bound of the counted loop that iterates `lo..=hi`.
    On a literal `hi` denoting an integer `k` (unsuffixed, unsigned or signed)
    it is the integer literal `k + 1`; the addition happens in `Int`, so the
    maximum of a word type gives its modulus. On any other `hi` it is the
    application `range_incl_end hi`, whose value in `widthArrayOps` is the
    integer `hi + 1`. -/
def inclusiveUpper (hi : ImpExpr) : ImpExpr :=
  match hi with
  | .lit l =>
    match (Value.ofLit l).toInt with
    | some k => .lit (.int (k + 1))
    | none => .app "range_incl_end" [hi]
  | _ => .app "range_incl_end" [hi]

/-- `inclusiveUpper` on typed expressions: the bound is decided on the erased
    expression, and the nodes it builds carry the type `.unknown`. -/
def inclusiveUpperT (hi : TExpr) : TExpr :=
  match hi.erase with
  | .lit l =>
    match (Value.ofLit l).toInt with
    | some k => .mk (.lit (.int (k + 1))) .unknown
    | none => .mk (.app "range_incl_end" [hi]) .unknown
  | _ => .mk (.app "range_incl_end" [hi]) .unknown

theorem inclusiveUpperT_erase (hi : TExpr) :
    (inclusiveUpperT hi).erase = inclusiveUpper hi.erase := by
  unfold inclusiveUpperT inclusiveUpper
  split
  · next l h =>
    rw [h]
    split <;> simp [TExpr.erase, h]
  · simp [TExpr.erase]

/-- The builtin table `bi` computes the exclusive end of an inclusive range
    exactly: `range_incl_end` on a value denoting the integer `k` is the
    integer `k + 1`. -/
def RangeInclEnd (bi : Builtins) : Prop :=
  ∀ (v : Value) (k : Int), v.toInt = some k → bi "range_incl_end" [v] = some (.int (k + 1))

theorem widthArrayOps_rangeInclEnd : RangeInclEnd widthArrayOps := by
  intro v k h
  cases v <;> simp only [Value.toInt, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem fullBuiltins_rangeInclEnd : RangeInclEnd fullBuiltins := by
  intro v k h
  cases v <;> simp only [Value.toInt, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem widthAwareBuiltins_rangeInclEnd : RangeInclEnd widthAwareBuiltins := by
  intro v k h
  cases v <;> simp only [Value.toInt, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

theorem hax64Builtins_rangeInclEnd : RangeInclEnd hax64Builtins := by
  intro v k h
  cases v <;> simp only [Value.toInt, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> rfl

/-- The reference iteration of a body over `lo..=hi`, as Rust's
    `RangeInclusive` iterator runs it: when `hi < lo` it runs nothing; otherwise
    it binds `var` to `lo` and runs the body, and it stops after the iteration
    with `lo = hi`. A `break` ends the loop with its value; each iteration after
    the first consumes one unit of fuel. -/
def denoteForInclusive (bi : Builtins) (var : String) (lo hi : Int)
    (body : ImpExpr) : Nat → StateM Env Outcome
  | 0 => if hi < lo then pure (.val .unit) else pure (.err "out of fuel")
  | fuel + 1 =>
    if hi < lo then pure (.val .unit)
    else do
      modify (Env.extend · var (.int lo))
      let rb ← denote bi (fuel + 1) body
      match rb with
      | .val _ | .continued =>
        if lo = hi then pure (.val .unit)
        else denoteForInclusive bi var (lo + 1) hi body fuel
      | .broke v => pure (.val v)
      | other => pure other

theorem denoteForInclusive_of_lt (bi : Builtins) (var : String) (lo hi : Int)
    (body : ImpExpr) (fuel : Nat) (h : hi < lo) :
    denoteForInclusive bi var lo hi body fuel = pure (.val .unit) := by
  cases fuel <;> simp [denoteForInclusive, h]

theorem denoteForLoop_succ_eq_denoteForInclusive (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) :
    denoteForLoop bi fuel var lo (hi + 1) body =
      denoteForInclusive bi var lo hi body fuel := by
  induction fuel generalizing lo with
  | zero =>
    rw [denoteForLoop]
    by_cases h : hi < lo
    · simp [denoteForInclusive, h, show lo ≥ hi + 1 by omega]
    · simp [denoteForInclusive, h, show ¬ lo ≥ hi + 1 by omega]
  | succ n ih =>
    rw [denoteForLoop]
    by_cases h : hi < lo
    · simp [denoteForInclusive, h, show lo ≥ hi + 1 by omega]
    · simp only [denoteForInclusive, h, show ¬ lo ≥ hi + 1 by omega, ite_false,
        Nat.add_one_ne_zero, Nat.add_sub_cancel]
      congr 1
      funext u
      congr 1
      funext rb
      cases rb with
      | val v =>
        by_cases he : lo = hi
        · subst he
          rw [denoteForLoop]
          simp
        · simp [he, ih]
      | continued =>
        by_cases he : lo = hi
        · subst he
          rw [denoteForLoop]
          simp
        · simp [he, ih]
      | _ => rfl

theorem denote_forLoop_inclusiveUpper_lit (bi : Builtins) (fuel : Nat)
    (var : String) (lo body : ImpExpr) (l : ImpLit) (k a : Int) (vlo : Value)
    (s s' : Env) (hk : (Value.ofLit l).toInt = some k)
    (hlo : (denote bi fuel lo).run s = (.val vlo, s'))
    (ha : vlo = .int a ∨ ∃ (w : IntWidth) (n : Nat), vlo = .uint w n ∧ a = n) :
    (denote bi fuel (.forLoop var lo (inclusiveUpper (.lit l)) body)).run s =
      (denoteForInclusive bi var a k body fuel).run s' := by
  simp only [inclusiveUpper, hk]
  rw [denote]
  simp only [StateT.run, bind, StateT.bind] at hlo ⊢
  rw [show denote bi fuel lo s = (Outcome.val vlo, s') from hlo]
  simp only [denote, pure, Value.ofLit]
  rcases ha with rfl | ⟨w, n, rfl, rfl⟩ <;>
    rw [← denoteForLoop_succ_eq_denoteForInclusive] <;> rfl

theorem denote_forLoop_inclusiveUpper_end (bi : Builtins) (fuel : Nat)
    (var : String) (lo hi body : ImpExpr) (k a : Int) (vlo vhi : Value)
    (s s' s'' : Env) (hnl : ∀ l, hi ≠ .lit l)
    (hlo : (denote bi fuel lo).run s = (.val vlo, s'))
    (ha : vlo = .int a ∨ ∃ (w : IntWidth) (n : Nat), vlo = .uint w n ∧ a = n)
    (hhi : (denote bi fuel hi).run s' = (.val vhi, s''))
    (hend : bi "range_incl_end" [vhi] = some (.int (k + 1))) :
    (denote bi fuel (.forLoop var lo (inclusiveUpper hi) body)).run s =
      (denoteForInclusive bi var a k body fuel).run s'' := by
  have hup : inclusiveUpper hi = .app "range_incl_end" [hi] := by
    unfold inclusiveUpper
    split
    · next l => exact absurd rfl (hnl l)
    · rfl
  rw [hup, denote]
  simp only [StateT.run, bind, StateT.bind] at hlo hhi ⊢
  rw [show denote bi fuel lo s = (Outcome.val vlo, s') from hlo]
  simp only [denote, denoteArgs, bind, StateT.bind, pure]
  rw [show denote bi fuel hi s' = (Outcome.val vhi, s'') from hhi]
  rw [← denoteForLoop_succ_eq_denoteForInclusive]
  simp only [StateT.bind, StateT.pure, pure, bind, Option.map_some, hend]
  rcases ha with rfl | ⟨w, n, rfl, rfl⟩ <;> rfl

/-- **A widthed upper bound of `lo..=hi` iterates Rust's count.** On an upper
    bound that is not a literal and denotes an unsigned, signed or unbounded
    integer `k`, under a table satisfying `RangeInclEnd` (`fullBuiltins`,
    `widthAwareBuiltins`, `hax64Builtins`), the lowered loop denotes the
    reference iteration over `lo..=k`; at `k` the maximum of its type it runs
    the body once with the counter at `k`, and at `k < lo` it runs it zero
    times (`denoteForInclusive_of_lt`). -/
theorem denote_forLoop_inclusiveUpper_toInt (bi : Builtins) (hbi : RangeInclEnd bi)
    (fuel : Nat) (var : String) (lo hi body : ImpExpr) (k a : Int) (vlo vhi : Value)
    (s s' s'' : Env) (hnl : ∀ l, hi ≠ .lit l)
    (hlo : (denote bi fuel lo).run s = (.val vlo, s'))
    (ha : vlo = .int a ∨ ∃ (w : IntWidth) (n : Nat), vlo = .uint w n ∧ a = n)
    (hhi : (denote bi fuel hi).run s' = (.val vhi, s''))
    (hk : vhi.toInt = some k) :
    (denote bi fuel (.forLoop var lo (inclusiveUpper hi) body)).run s =
      (denoteForInclusive bi var a k body fuel).run s'' :=
  denote_forLoop_inclusiveUpper_end bi fuel var lo hi body k a vlo vhi s s' s'' hnl hlo ha hhi
    (hbi vhi k hk)

end Hax

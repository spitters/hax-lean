/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# Runtime Library for Generated Lean 4 Code

Defines `ControlFlow`, `Hax.forFold`, `Hax.whileFold`, their `Return`
variants, and the builtin operations that the surface code printed by
`haxpipeT --emit-certified` refers to. Every certified extraction imports this
module (through `CatCrypt.Hax.Runtime`, which re-exports it).

## Design

The `ControlFlow` type mirrors Rust's `core::ops::ControlFlow<B, C>`.
Fold operations thread an accumulator through a closure that returns
`ControlFlow`: `Continue acc'` continues iteration with the new accumulator,
`Break v` exits the loop with value `v`.

The range folds recurse structurally on the trip count `(hi - lo).toNat`.
`whileFold` and `whileFoldReturn` are total: their value is the result of the
loop at the least number of trips after which it stops, and a fixed value when
no number of trips stops it; `whileFoldFuel` is the fuel-bounded run they are
characterised by. Their compiled code is the loop itself (`whileFoldImpl`,
`whileFoldReturnImpl`).

### Correspondence with the AST

| AST constructor        | Runtime function       |
|------------------------|------------------------|
| `forFold v lo hi body` | `Hax.forFold`          |
| `whileFold c body`     | `Hax.whileFold`        |
| `forFoldReturn`        | `Hax.forFoldReturn`    |
| `whileFoldReturn`      | `Hax.whileFoldReturn`  |
| `cfBreak e`            | `ControlFlow.Break`    |
| `cfContinue e`         | `ControlFlow.Continue` |
| `cfBreakContinue e`    | `ControlFlow.Break (ControlFlow.Continue e)` |
-/

@[expose] public section

/-- Rust's `ControlFlow<B, C>`: either stop with `Break b` or continue
    with `Continue c`. -/
inductive ControlFlow (B C : Type) where
  | Break (b : B)
  | Continue (c : C)
  deriving BEq, Repr

/-- `ControlFlow` is inhabited whenever the continue type is.
    (Uses `Continue default` rather than requiring `Inhabited B`.) -/
instance {B C : Type} [Inhabited C] : Inhabited (ControlFlow B C) :=
  ⟨.Continue default⟩

namespace ControlFlow

variable {B C : Type}

/-- Extract the break value if present. -/
def breakVal? : ControlFlow B C → Option B
  | .Break b => some b
  | .Continue _ => none

/-- Extract the continue value if present. -/
def continueVal? : ControlFlow B C → Option C
  | .Break _ => none
  | .Continue c => some c

/-- Is this a `Break`? -/
def isBreak : ControlFlow B C → Bool
  | .Break _ => true
  | .Continue _ => false

/-- Extract the value from either variant when both carry the same type. -/
def merge {α : Type} : ControlFlow α α → α
  | .Break v => v
  | .Continue v => v

end ControlFlow

namespace Hax

/-- Total fold over `[lo, hi)` — structurally recursive on `(hi - lo).toNat`. -/
def foldRange {α : Type} (lo hi : Int) (init : α) (f : Int → α → α) : α :=
  go (hi - lo).toNat lo init
where
  go : Nat → Int → α → α
    | 0, _, acc => acc
    | n + 1, i, acc => go n (i + 1) (f i acc)

/-- Total reverse fold over `(lo, hi]`. -/
def foldRangeRev {α : Type} (lo hi : Int) (init : α) (f : Int → α → α) : α :=
  go (hi - lo).toNat (hi - 1) init
where
  go : Nat → Int → α → α
    | 0, _, acc => acc
    | n + 1, i, acc => go n (i - 1) (f i acc)

/-- Relational congruence for `foldRange`: a relation `R` between two accumulator
    types that holds on the initial accumulators and is preserved by the two step
    functions at every index carries over to the two fold results over the same
    index range. Stated here, before `foldRange` is sealed `@[irreducible]`, so
    the equational unfolding is available. -/
theorem foldRange_rel {α β : Type} {R : α → β → Prop} {lo hi : Int}
    {fa : Int → α → α} {fb : Int → β → β} {ia : α} {ib : β}
    (h0 : R ia ib) (hstep : ∀ i a b, R a b → R (fa i a) (fb i b)) :
    R (foldRange lo hi ia fa) (foldRange lo hi ib fb) := by
  simp only [foldRange]
  suffices H : ∀ (n : Nat) (lo : Int) (a : α) (b : β), R a b →
      R (foldRange.go fa n lo a) (foldRange.go fb n lo b) from H _ _ _ _ h0
  intro n
  induction n with
  | zero => intro lo a b hab; exact hab
  | succ n ih =>
    intro lo a b hab
    simp only [foldRange.go]
    exact ih (lo + 1) (fa lo a) (fb lo b) (hstep lo a b hab)

-- Performance: keep whnf from unfolding iteration combinators inside
-- the giant `mutual` blocks emitted by haxpipeT. Without this, elaborating
-- a single foldRange-heavy def (e.g. FAEST's `compute_witness`) can blow
-- past 6.4M heartbeats. The bodies are
-- never relied on for definitional equality outside `Hax/Runtime.lean`.
attribute [irreducible] foldRange foldRangeRev

/-- Total fold over `[lo, hi)` with ControlFlow accumulator. -/
def forFold {α β : Type} (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow β α) : ControlFlow β α :=
  go (hi - lo).toNat lo init
where
  go : Nat → Int → α → ControlFlow β α
    | 0, _, acc => .Continue acc
    | n + 1, i, acc =>
      match f i acc with
      | .Break v => .Break v
      | .Continue acc' => go n (i + 1) acc'

/-- Total reverse fold over `(lo, hi]` with ControlFlow accumulator. -/
def forFoldRev {α β : Type} (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow β α) : ControlFlow β α :=
  go (hi - lo).toNat (hi - 1) init
where
  go : Nat → Int → α → ControlFlow β α
    | 0, _, acc => .Continue acc
    | n + 1, i, acc =>
      match f i acc with
      | .Break v => .Break v
      | .Continue acc' => go n (i - 1) acc'

/-- Total for-fold with early return support (nested ControlFlow). -/
def forFoldReturn {α β γ : Type} (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow (ControlFlow β γ) α) :
    ControlFlow β (ControlFlow γ α) :=
  go (hi - lo).toNat lo init
where
  go : Nat → Int → α → ControlFlow β (ControlFlow γ α)
    | 0, _, acc => .Continue (.Continue acc)
    | n + 1, i, acc =>
      match f i acc with
      | .Break (.Continue v) => .Continue (.Break v)  -- loop break
      | .Break (.Break v) => .Break v                  -- early return
      | .Continue acc' => go n (i + 1) acc'

/-- Total reverse for-fold with early return support. -/
def forFoldRevReturn {α β γ : Type} (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow (ControlFlow β γ) α) :
    ControlFlow β (ControlFlow γ α) :=
  go (hi - lo).toNat (hi - 1) init
where
  go : Nat → Int → α → ControlFlow β (ControlFlow γ α)
    | 0, _, acc => .Continue (.Continue acc)
    | n + 1, i, acc =>
      match f (i) acc with
      | .Break (.Continue v) => .Continue (.Break v)  -- loop break
      | .Break (.Break v) => .Break v                  -- early return
      | .Continue acc' => go n (i - 1) acc'

/-! ### One-trip unfolding of the range folds -/

/-- `forFold` on `[lo, hi)`: the accumulator when the range is empty, otherwise
    one step at `lo` followed by the fold over `[lo + 1, hi)`. -/
theorem forFold_eq {α β : Type} (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow β α) :
    forFold lo hi init f =
      if lo ≥ hi then .Continue init
      else
        match f lo init with
        | .Break v => .Break v
        | .Continue acc => forFold (lo + 1) hi acc f := by
  unfold forFold
  split
  · rw [show (hi - lo).toNat = 0 by omega]; rfl
  · rw [show (hi - lo).toNat = (hi - (lo + 1)).toNat + 1 by omega]; rfl

/-- `forFoldRev` on `(lo, hi]`: the accumulator when the range is empty,
    otherwise one step at `hi - 1` followed by the fold over `(lo, hi - 1]`. -/
theorem forFoldRev_eq {α β : Type} (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow β α) :
    forFoldRev lo hi init f =
      if lo ≥ hi then .Continue init
      else
        match f (hi - 1) init with
        | .Break v => .Break v
        | .Continue acc => forFoldRev lo (hi - 1) acc f := by
  unfold forFoldRev
  split
  · rw [show (hi - lo).toNat = 0 by omega]; rfl
  · rw [show (hi - lo).toNat = (hi - 1 - lo).toNat + 1 by omega]; rfl

/-- `forFoldReturn` on `[lo, hi)`: normal completion when the range is empty,
    otherwise one classified step at `lo` followed by the fold over
    `[lo + 1, hi)`. -/
theorem forFoldReturn_eq {α β γ : Type} (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow (ControlFlow β γ) α) :
    forFoldReturn lo hi init f =
      if lo ≥ hi then .Continue (.Continue init)
      else
        match f lo init with
        | .Break (.Continue v) => .Continue (.Break v)
        | .Break (.Break v) => .Break v
        | .Continue acc => forFoldReturn (lo + 1) hi acc f := by
  unfold forFoldReturn
  split
  · rw [show (hi - lo).toNat = 0 by omega]; rfl
  · rw [show (hi - lo).toNat = (hi - (lo + 1)).toNat + 1 by omega]; rfl

/-- `forFoldRevReturn` on `(lo, hi]`: normal completion when the range is
    empty, otherwise one classified step at `hi - 1` followed by the fold over
    `(lo, hi - 1]`. -/
theorem forFoldRevReturn_eq {α β γ : Type} (lo hi : Int) (init : α)
    (f : Int → α → ControlFlow (ControlFlow β γ) α) :
    forFoldRevReturn lo hi init f =
      if lo ≥ hi then .Continue (.Continue init)
      else
        match f (hi - 1) init with
        | .Break (.Continue v) => .Continue (.Break v)
        | .Break (.Break v) => .Break v
        | .Continue acc => forFoldRevReturn lo (hi - 1) acc f := by
  unfold forFoldRevReturn
  split
  · rw [show (hi - lo).toNat = 0 by omega]; rfl
  · rw [show (hi - lo).toNat = (hi - 1 - lo).toNat + 1 by omega]; rfl

/-! ### While-folds

A while-fold tests `cond` on the accumulator; on `false` it stops with
`Continue acc`, on `true` it runs the body, stopping on `Break` and repeating on
`Continue acc'`. `whileFoldFuel cond f n acc` runs at most `n` condition tests.
It is `some r` exactly when the loop stops within them, with result `r`, and a
larger budget returns the same `r` (`whileFoldFuel_mono`). `whileFold` is that
`r` for any stopping budget, hence for the least one, and `Continue init` when
no budget stops the loop. -/

/-- The run of a while-fold from `acc` bounded by `n` condition tests: `some r`
    when the loop stops within them with result `r`, `none` otherwise. -/
def whileFoldFuel {α β : Type} (cond : α → Bool) (f : α → ControlFlow β α) :
    Nat → α → Option (ControlFlow β α)
  | 0, _ => none
  | n + 1, acc =>
    if cond acc then
      match f acc with
      | .Break v => some (.Break v)
      | .Continue acc' => whileFoldFuel cond f n acc'
    else some (.Continue acc)

/-- A bounded run that stops keeps its result under a larger bound. -/
theorem whileFoldFuel_mono {α β : Type} {cond : α → Bool} {f : α → ControlFlow β α}
    {n m : Nat} {acc : α} {r : ControlFlow β α}
    (h : whileFoldFuel cond f n acc = some r) (hnm : n ≤ m) :
    whileFoldFuel cond f m acc = some r := by
  induction n generalizing m acc with
  | zero => simp [whileFoldFuel] at h
  | succ n ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [whileFoldFuel] at h ⊢
    split at h
    · rw [if_pos ‹_›]
      split at h
      · exact h
      · exact ih h (by omega)
    · rw [if_neg ‹_›]; exact h

/-- Two bounded runs of the same while-fold that both stop agree. -/
theorem whileFoldFuel_agree {α β : Type} {cond : α → Bool} {f : α → ControlFlow β α}
    {n m : Nat} {acc : α} {r s : ControlFlow β α}
    (hr : whileFoldFuel cond f n acc = some r) (hs : whileFoldFuel cond f m acc = some s) :
    r = s := by
  have h1 := whileFoldFuel_mono hr (Nat.le_max_left n m)
  have h2 := whileFoldFuel_mono hs (Nat.le_max_right n m)
  rw [h1] at h2; exact Option.some.inj h2

/-- The while-fold from `init` stops: some bounded run of it stops. -/
def WhileFoldStops {α β : Type} (init : α) (cond : α → Bool)
    (f : α → ControlFlow β α) : Prop :=
  ∃ n, (whileFoldFuel cond f n init).isSome

/-- The compiled code of `whileFold`: the loop itself, which returns the result
    of a stopping run and does not return otherwise. -/
partial def whileFoldImpl {α β : Type}
    (init : α) (cond : α → Bool) (f : α → ControlFlow β α) :
    ControlFlow β α :=
  if cond init then
    match f init with
    | .Break v => .Break v
    | .Continue acc => whileFoldImpl acc cond f
  else .Continue init

/-- While-fold with accumulator. Iterates while the condition returns `true`.
    The result of the loop at the least number of trips after which it stops
    (condition `false` or `Break`), and `Continue init` when it does not stop.
    Evaluation runs `whileFoldImpl`, which agrees with this value on every run
    that stops. -/
@[implemented_by whileFoldImpl]
def whileFold {α β : Type}
    (init : α) (cond : α → Bool) (f : α → ControlFlow β α) :
    ControlFlow β α :=
  open Classical in
  if h : WhileFoldStops init cond f then
    (whileFoldFuel cond f (Classical.choose h) init).get (Classical.choose_spec h)
  else .Continue init

/-- Closed form: a bounded run that stops gives the value of `whileFold`. -/
theorem whileFold_eq_of_fuel {α β : Type} {init : α} {cond : α → Bool}
    {f : α → ControlFlow β α} {n : Nat} {r : ControlFlow β α}
    (h : whileFoldFuel cond f n init = some r) : whileFold init cond f = r := by
  have hs : WhileFoldStops init cond f := ⟨n, by simp [h]⟩
  unfold whileFold
  rw [dif_pos hs]
  exact whileFoldFuel_agree (Option.eq_some_of_isSome (Classical.choose_spec hs)) h

/-- `whileFold` on a loop that does not stop is `Continue init`. -/
theorem whileFold_of_not_stops {α β : Type} {init : α} {cond : α → Bool}
    {f : α → ControlFlow β α} (h : ¬ WhileFoldStops init cond f) :
    whileFold init cond f = .Continue init := by
  unfold whileFold
  rw [dif_neg h]

/-- One-trip unfolding of a stopping `whileFold`. -/
theorem whileFold_eq {α β : Type} {init : α} {cond : α → Bool}
    {f : α → ControlFlow β α} (h : WhileFoldStops init cond f) :
    whileFold init cond f =
      if cond init then
        match f init with
        | .Break v => .Break v
        | .Continue acc => whileFold acc cond f
      else .Continue init := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hn
  rw [whileFold_eq_of_fuel hr]
  cases n with
  | zero => simp [whileFoldFuel] at hr
  | succ n =>
    simp only [whileFoldFuel] at hr
    split at hr
    · rw [if_pos ‹_›]
      split at hr
      · exact (Option.some.inj hr).symm
      · exact (whileFold_eq_of_fuel hr).symm
    · rw [if_neg ‹_›]; exact (Option.some.inj hr).symm

/-- The run of a while-fold with early return from `acc`, bounded by `n`
    condition tests: `some r` when the loop stops within them with result `r`,
    `none` otherwise. -/
def whileFoldReturnFuel {α β γ : Type} (cond : α → Bool)
    (f : α → ControlFlow (ControlFlow β γ) α) :
    Nat → α → Option (ControlFlow β (ControlFlow γ α))
  | 0, _ => none
  | n + 1, acc =>
    if cond acc then
      match f acc with
      | .Break (.Continue v) => some (.Continue (.Break v))
      | .Break (.Break v) => some (.Break v)
      | .Continue acc' => whileFoldReturnFuel cond f n acc'
    else some (.Continue (.Continue acc))

/-- A bounded run that stops keeps its result under a larger bound. -/
theorem whileFoldReturnFuel_mono {α β γ : Type} {cond : α → Bool}
    {f : α → ControlFlow (ControlFlow β γ) α}
    {n m : Nat} {acc : α} {r : ControlFlow β (ControlFlow γ α)}
    (h : whileFoldReturnFuel cond f n acc = some r) (hnm : n ≤ m) :
    whileFoldReturnFuel cond f m acc = some r := by
  induction n generalizing m acc with
  | zero => simp [whileFoldReturnFuel] at h
  | succ n ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [whileFoldReturnFuel] at h ⊢
    split at h
    · rw [if_pos ‹_›]
      split at h
      · exact h
      · exact h
      · exact ih h (by omega)
    · rw [if_neg ‹_›]; exact h

/-- Two bounded runs of the same while-fold with early return that both stop
    agree. -/
theorem whileFoldReturnFuel_agree {α β γ : Type} {cond : α → Bool}
    {f : α → ControlFlow (ControlFlow β γ) α}
    {n m : Nat} {acc : α} {r s : ControlFlow β (ControlFlow γ α)}
    (hr : whileFoldReturnFuel cond f n acc = some r)
    (hs : whileFoldReturnFuel cond f m acc = some s) : r = s := by
  have h1 := whileFoldReturnFuel_mono hr (Nat.le_max_left n m)
  have h2 := whileFoldReturnFuel_mono hs (Nat.le_max_right n m)
  rw [h1] at h2; exact Option.some.inj h2

/-- The while-fold with early return from `init` stops: some bounded run of it
    stops. -/
def WhileFoldReturnStops {α β γ : Type} (init : α) (cond : α → Bool)
    (f : α → ControlFlow (ControlFlow β γ) α) : Prop :=
  ∃ n, (whileFoldReturnFuel cond f n init).isSome

/-- The compiled code of `whileFoldReturn`: the loop itself, which returns the
    result of a stopping run and does not return otherwise. -/
partial def whileFoldReturnImpl {α β γ : Type}
    (init : α) (cond : α → Bool)
    (f : α → ControlFlow (ControlFlow β γ) α) :
    ControlFlow β (ControlFlow γ α) :=
  if cond init then
    match f init with
    | .Break (.Continue v) => .Continue (.Break v)
    | .Break (.Break v) => .Break v
    | .Continue acc => whileFoldReturnImpl acc cond f
  else .Continue (.Continue init)

/-- While-fold with early return support (nested ControlFlow). The result of
    the loop at the least number of trips after which it stops (condition
    `false`, loop break, or early return), and `Continue (Continue init)` when
    it does not stop. Evaluation runs `whileFoldReturnImpl`, which agrees with
    this value on every run that stops. -/
@[implemented_by whileFoldReturnImpl]
def whileFoldReturn {α β γ : Type}
    (init : α) (cond : α → Bool)
    (f : α → ControlFlow (ControlFlow β γ) α) :
    ControlFlow β (ControlFlow γ α) :=
  open Classical in
  if h : WhileFoldReturnStops init cond f then
    (whileFoldReturnFuel cond f (Classical.choose h) init).get (Classical.choose_spec h)
  else .Continue (.Continue init)

/-- Closed form: a bounded run that stops gives the value of `whileFoldReturn`. -/
theorem whileFoldReturn_eq_of_fuel {α β γ : Type} {init : α} {cond : α → Bool}
    {f : α → ControlFlow (ControlFlow β γ) α} {n : Nat}
    {r : ControlFlow β (ControlFlow γ α)}
    (h : whileFoldReturnFuel cond f n init = some r) :
    whileFoldReturn init cond f = r := by
  have hs : WhileFoldReturnStops init cond f := ⟨n, by simp [h]⟩
  unfold whileFoldReturn
  rw [dif_pos hs]
  exact whileFoldReturnFuel_agree (Option.eq_some_of_isSome (Classical.choose_spec hs)) h

/-- `whileFoldReturn` on a loop that does not stop is `Continue (Continue init)`. -/
theorem whileFoldReturn_of_not_stops {α β γ : Type} {init : α} {cond : α → Bool}
    {f : α → ControlFlow (ControlFlow β γ) α} (h : ¬ WhileFoldReturnStops init cond f) :
    whileFoldReturn init cond f = .Continue (.Continue init) := by
  unfold whileFoldReturn
  rw [dif_neg h]

/-- One-trip unfolding of a stopping `whileFoldReturn`. -/
theorem whileFoldReturn_eq {α β γ : Type} {init : α} {cond : α → Bool}
    {f : α → ControlFlow (ControlFlow β γ) α} (h : WhileFoldReturnStops init cond f) :
    whileFoldReturn init cond f =
      if cond init then
        match f init with
        | .Break (.Continue v) => .Continue (.Break v)
        | .Break (.Break v) => .Break v
        | .Continue acc => whileFoldReturn acc cond f
      else .Continue (.Continue init) := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hn
  rw [whileFoldReturn_eq_of_fuel hr]
  cases n with
  | zero => simp [whileFoldReturnFuel] at hr
  | succ n =>
    simp only [whileFoldReturnFuel] at hr
    split at hr
    · rw [if_pos ‹_›]
      split at hr
      · exact (Option.some.inj hr).symm
      · exact (Option.some.inj hr).symm
      · exact (whileFoldReturn_eq_of_fuel hr).symm
    · rw [if_neg ‹_›]; exact (Option.some.inj hr).symm

/-- Helper for code generation: wraps `ControlFlow.Break` with explicit type params. -/
@[inline] def cfBreak {B C : Type} (v : B) : ControlFlow B C := ControlFlow.Break v

/-- Helper for code generation: wraps `ControlFlow.Continue` with explicit type params. -/
@[inline] def cfContinue {B C : Type} (v : C) : ControlFlow B C := ControlFlow.Continue v

/-- Extract the final value from a non-early-returning fold result. -/
def unwrapContinue {B C : Type} [Inhabited C] : ControlFlow B C → C
  | .Continue c => c
  | .Break _ => panic! "unexpected Break in unwrapContinue"

/-! ## Builtin operations for generated code

These definitions are referenced by generated Lean 4 code via `Hax.add`, `Hax.Sub`, etc.
Capitalized variants match hax's Rust operator names. -/

-- OfNat instances for Bool and Array Int (needed for cross-type comparisons
-- in extracted code where `bne x 0` has x : Bool or x : Array Int).
instance : OfNat Bool 0 where ofNat := false
instance (n : Nat) : OfNat Bool (n + 1) where ofNat := true
instance : OfNat (Array Int) 0 where ofNat := #[]

-- Element-wise instances for Array Int (needed when Rust trait arithmetic
-- operates on ADT types like FieldElement that are extracted as Array Int).
instance : Add (Array Int) where add a b := Array.zipWith (· + ·) a b
instance : Sub (Array Int) where sub a b := Array.zipWith (· - ·) a b
instance : Mul (Array Int) where mul a b := Array.zipWith (· * ·) a b
instance : Div (Array Int) where div a b := Array.zipWith (· / ·) a b
instance : Mod (Array Int) where mod a b := Array.zipWith (· % ·) a b
instance : Neg (Array Int) where neg a := a.map (- ·)

-- Arithmetic (polymorphic: works for Int, Array Int, etc.)
@[inline] def add {α : Type} [Add α] (a b : α) : α := a + b
@[inline] def sub {α : Type} [Sub α] (a b : α) : α := a - b
@[inline] def mul {α : Type} [Mul α] (a b : α) : α := a * b
@[inline] def div {α : Type} [Div α] (a b : α) : α := a / b
@[inline] def rem {α : Type} [Mod α] (a b : α) : α := a % b
@[inline] def neg {α : Type} [Neg α] (a : α) : α := -a

-- Comparison (polymorphic: works for Int, Array Int, Array (Array Int), etc.)
@[inline] def beq {α : Type} [BEq α] (a b : α) : Bool := a == b
@[inline] def bne {α : Type} [BEq α] (a b : α) : Bool := !(a == b)
-- Aliases of `beq` / `bne`
abbrev beq_ := @beq
abbrev bne_ := @bne
@[inline] def lt {α : Type} [LT α] [DecidableRel (α := α) (· < ·)] (a b : α) : Bool := a < b
@[inline] def le {α : Type} [LE α] [DecidableRel (α := α) (· ≤ ·)] (a b : α) : Bool := a ≤ b
@[inline] def gt {α : Type} [LT α] [DecidableRel (α := α) (· < ·)] (a b : α) : Bool := b < a
@[inline] def ge {α : Type} [LE α] [DecidableRel (α := α) (· ≤ ·)] (a b : α) : Bool := b ≤ a

-- Boolean
@[inline] def bnot (b : Bool) : Bool := !b
@[inline] def band (a b : Bool) : Bool := a && b
@[inline] def bor (a b : Bool) : Bool := a || b

-- Bitwise on `Int`, operating on the magnitude (`toNat`)
@[inline] def shl (a b : Int) : Int := ↑(a.toNat <<< b.toNat)
@[inline] def shr (a b : Int) : Int := ↑(a.toNat >>> b.toNat)
@[inline] def bitand (a b : Int) : Int := ↑(a.toNat &&& b.toNat)
@[inline] def bitor (a b : Int) : Int := ↑(a.toNat ||| b.toNat)
@[inline] def bitxor (a b : Int) : Int := ↑(a.toNat ^^^ b.toNat)
@[inline] def bitnot (a : Int) : Int := -(a + 1)

/-! ### Width-aware operations for typed extraction

These operate on `Int` (matching the typed pipeline's representation) but
truncate results to `w` bits, modeling Rust's fixed-width semantics.
haxpipeT emits these when it knows the Rust type width from the TExpr. -/

/-- Truncate `n` to `w` bits (mod 2^w). -/
@[inline] def mod2w (w : Nat) (n : Int) : Int := ↑(n.toNat % (2 ^ w))

/-- Width-aware wrapping add: `(a + b) mod 2^w`. -/
@[inline] def wrapping_add_w (w : Nat) (a b : Int) : Int := mod2w w (a + b)

/-- Width-aware wrapping sub: `(a - b + 2^w) mod 2^w`. -/
@[inline] def wrapping_sub_w (w : Nat) (a b : Int) : Int := mod2w w (a - b + ↑(2 ^ w))

/-- Width-aware wrapping mul: `(a * b) mod 2^w`. -/
@[inline] def wrapping_mul_w (w : Nat) (a b : Int) : Int := mod2w w (a * b)

/-- Width-aware wrapping neg: `(2^w - a) mod 2^w`. -/
@[inline] def wrapping_neg_w (w : Nat) (a : Int) : Int := mod2w w (↑(2 ^ w) - a)

/-- Width-aware right shift: `(a mod 2^w) >>> b`. -/
@[inline] def shr_w (w : Nat) (a b : Int) : Int := ↑((a.toNat % (2 ^ w)) >>> b.toNat)

/-- Width-aware left shift: `((a mod 2^w) <<< b) mod 2^w`. -/
@[inline] def shl_w (w : Nat) (a b : Int) : Int := mod2w w ↑(a.toNat <<< b.toNat)

/-- Width-aware bitwise AND: `(a mod 2^w) &&& (b mod 2^w)`. -/
@[inline] def bitand_w (w : Nat) (a b : Int) : Int := ↑((a.toNat % (2 ^ w)) &&& (b.toNat % (2 ^ w)))

/-- Width-aware bitwise OR. -/
@[inline] def bitor_w (w : Nat) (a b : Int) : Int := ↑((a.toNat % (2 ^ w)) ||| (b.toNat % (2 ^ w)))

/-- Width-aware bitwise XOR. -/
@[inline] def bitxor_w (w : Nat) (a b : Int) : Int := ↑((a.toNat % (2 ^ w)) ^^^ (b.toNat % (2 ^ w)))

/-- Width-aware bitwise NOT: flip `w` bits. -/
@[inline] def bitnot_w (w : Nat) (a : Int) : Int := ↑((2 ^ w - 1) - (a.toNat % (2 ^ w)))

/-- Width-aware rotate right by `n` bits within `w`-bit word. -/
@[inline] def rotate_right_w (w : Nat) (x n : Int) : Int :=
  let xn := x.toNat % (2 ^ w)
  let shift := n.toNat % w
  mod2w w ↑((xn >>> shift) ||| (xn <<< (w - shift)))

/-- Width-aware rotate left by `n` bits within `w`-bit word. -/
@[inline] def rotate_left_w (w : Nat) (x n : Int) : Int :=
  let xn := x.toNat % (2 ^ w)
  let shift := n.toNat % w
  mod2w w ↑((xn <<< shift) ||| (xn >>> (w - shift)))

/-- Width-aware cast: truncate to `dstWidth` bits. -/
@[inline] def castVal_w (dstWidth : Nat) (a : Int) : Int := mod2w dstWidth a

-- Indexing — out-of-bounds returns a[0] or a dummy value (never reached in extracted code)
@[inline] def index {α : Type} [Inhabited α] (a : Array α) (i : Int) : α :=
  if h : i.toNat < a.size then a[i.toNat]
  else if h2 : 0 < a.size then a[0]
  else default

-- Capitalized aliases (hax's Rust operator names)
-- These are polymorphic so they work with both Int and fixed-width UInt types.
-- Lean's type inference resolves to the correct width-specific operation.
@[inline] def Add {α : Type} [HAdd α α α] (a b : α) : α := a + b
@[inline] def Sub {α : Type} [HSub α α α] (a b : α) : α := a - b
@[inline] def Mul {α : Type} [HMul α α α] (a b : α) : α := a * b
@[inline] def Div {α : Type} [HDiv α α α] (a b : α) : α := a / b
@[inline] def Rem {α : Type} [HMod α α α] (a b : α) : α := a % b
@[inline] def Neg {α : Type} [_root_.Neg α] (a : α) : α := -a
abbrev Eq := @beq
abbrev Ne := @bne
@[inline] def Lt {α : Type} [_root_.LT α] [DecidableRel (α := α) (· < ·)] (a b : α) : Bool :=
  decide (a < b)
@[inline] def Le {α : Type} [_root_.LE α] [DecidableRel (α := α) (· ≤ ·)] (a b : α) : Bool :=
  decide (a ≤ b)
@[inline] def Gt {α : Type} [_root_.LT α] [DecidableRel (α := α) (· < ·)] (a b : α) : Bool :=
  decide (b < a)
@[inline] def Ge {α : Type} [_root_.LE α] [DecidableRel (α := α) (· ≤ ·)] (a b : α) : Bool :=
  decide (b ≤ a)
/-- Polymorphic NOT: boolean negation for Bool, bitwise complement for UInt. -/
class HaxNot (α : Type) where
  not : α → α
instance : HaxNot Bool where not := fun b => !b
instance : HaxNot Int where not := fun a => -(a + 1)  -- two's complement; width-specific NOT uses bitnot_w
instance : HaxNot UInt8 where not := fun a => ~~~a
instance : HaxNot UInt16 where not := fun a => ~~~a
instance : HaxNot UInt32 where not := fun a => ~~~a
instance : HaxNot UInt64 where not := fun a => ~~~a
@[inline] def Not {α : Type} [HaxNot α] (a : α) : α := HaxNot.not a
abbrev And := @band
abbrev Or := @bor
@[inline] def Shl {α β γ : Type} [HShiftLeft α β γ] (a : α) (b : β) : γ := a <<< b
@[inline] def Shr {α β γ : Type} [HShiftRight α β γ] (a : α) (b : β) : γ := a >>> b
@[inline] def BitAnd {α : Type} [HAnd α α α] (a b : α) : α := a &&& b
@[inline] def BitOr {α : Type} [HOr α α α] (a b : α) : α := a ||| b
@[inline] def BitXor {α : Type} [HXor α α α] (a b : α) : α := a ^^^ b

/-- Polymorphic condition: coerce any type to Bool for `if` conditions.
    Bool passes through; Int uses C-style truth (nonzero = true). -/
class HaxCond (α : Type) where
  toBool : α → Bool
instance : HaxCond Bool where toBool := id
instance : HaxCond Int where toBool := fun n => n != 0
@[inline] def cond {α : Type} [HaxCond α] (a : α) : Bool := HaxCond.toBool a

/-- Generic cast (identity in untyped mode).
    Named `castVal` to avoid conflict with Lean's kernel `cast`.
    For width-specific casts, use `cast_u8_u64` etc. -/
@[inline] def castVal (a : Int) : Int := a  -- identity; width-specific casts use castVal_w

/-- Bool → Int cast: `true → 1`, `false → 0`.
    Used for Rust's `b as u64` when `b : Bool`. -/
@[inline] def boolToInt (b : Bool) : Int := if b then 1 else 0

/-! ## Width-Aware Operations

These use Lean's built-in fixed-width integer types (`UInt8`, `UInt16`, `UInt32`,
`UInt64`), which are `BitVec n` under the hood. This ensures exact agreement
with Rust's wrapping semantics for unsigned integers.

The naming convention is `op_uN` where `op` is the operation and `N` is the
bit width (e.g., `shl_u32`, `bitxor_u64`). -/

-- UInt8 operations
@[inline] def add_u8  (a b : UInt8)  : UInt8  := a + b
@[inline] def sub_u8  (a b : UInt8)  : UInt8  := a - b
@[inline] def mul_u8  (a b : UInt8)  : UInt8  := a * b
@[inline] def div_u8  (a b : UInt8)  : UInt8  := a / b
@[inline] def rem_u8  (a b : UInt8)  : UInt8  := a % b
@[inline] def shl_u8  (a b : UInt8)  : UInt8  := a <<< b
@[inline] def shr_u8  (a b : UInt8)  : UInt8  := a >>> b
@[inline] def bitand_u8  (a b : UInt8) : UInt8 := a &&& b
@[inline] def bitor_u8   (a b : UInt8) : UInt8 := a ||| b
@[inline] def bitxor_u8  (a b : UInt8) : UInt8 := a ^^^ b
@[inline] def bitnot_u8  (a : UInt8)   : UInt8 := ~~~a
@[inline] def eq_u8  (a b : UInt8)  : Bool := a == b
@[inline] def ne_u8  (a b : UInt8)  : Bool := a != b
@[inline] def lt_u8  (a b : UInt8)  : Bool := a < b
@[inline] def le_u8  (a b : UInt8)  : Bool := a ≤ b
@[inline] def gt_u8  (a b : UInt8)  : Bool := a > b
@[inline] def ge_u8  (a b : UInt8)  : Bool := a ≥ b

-- UInt16 operations
@[inline] def add_u16 (a b : UInt16) : UInt16 := a + b
@[inline] def sub_u16 (a b : UInt16) : UInt16 := a - b
@[inline] def mul_u16 (a b : UInt16) : UInt16 := a * b
@[inline] def div_u16 (a b : UInt16) : UInt16 := a / b
@[inline] def rem_u16 (a b : UInt16) : UInt16 := a % b
@[inline] def shl_u16 (a b : UInt16) : UInt16 := a <<< b
@[inline] def shr_u16 (a b : UInt16) : UInt16 := a >>> b
@[inline] def bitand_u16 (a b : UInt16) : UInt16 := a &&& b
@[inline] def bitor_u16  (a b : UInt16) : UInt16 := a ||| b
@[inline] def bitxor_u16 (a b : UInt16) : UInt16 := a ^^^ b
@[inline] def bitnot_u16 (a : UInt16)   : UInt16 := ~~~a
@[inline] def eq_u16 (a b : UInt16) : Bool := a == b
@[inline] def ne_u16 (a b : UInt16) : Bool := a != b
@[inline] def lt_u16 (a b : UInt16) : Bool := a < b
@[inline] def le_u16 (a b : UInt16) : Bool := a ≤ b
@[inline] def gt_u16 (a b : UInt16) : Bool := a > b
@[inline] def ge_u16 (a b : UInt16) : Bool := a ≥ b

-- UInt32 operations
@[inline] def add_u32 (a b : UInt32) : UInt32 := a + b
@[inline] def sub_u32 (a b : UInt32) : UInt32 := a - b
@[inline] def mul_u32 (a b : UInt32) : UInt32 := a * b
@[inline] def div_u32 (a b : UInt32) : UInt32 := a / b
@[inline] def rem_u32 (a b : UInt32) : UInt32 := a % b
@[inline] def shl_u32 (a b : UInt32) : UInt32 := a <<< b
@[inline] def shr_u32 (a b : UInt32) : UInt32 := a >>> b
@[inline] def bitand_u32 (a b : UInt32) : UInt32 := a &&& b
@[inline] def bitor_u32  (a b : UInt32) : UInt32 := a ||| b
@[inline] def bitxor_u32 (a b : UInt32) : UInt32 := a ^^^ b
@[inline] def bitnot_u32 (a : UInt32)   : UInt32 := ~~~a
@[inline] def eq_u32 (a b : UInt32) : Bool := a == b
@[inline] def ne_u32 (a b : UInt32) : Bool := a != b
@[inline] def lt_u32 (a b : UInt32) : Bool := a < b
@[inline] def le_u32 (a b : UInt32) : Bool := a ≤ b
@[inline] def gt_u32 (a b : UInt32) : Bool := a > b
@[inline] def ge_u32 (a b : UInt32) : Bool := a ≥ b

-- UInt64 operations
@[inline] def add_u64 (a b : UInt64) : UInt64 := a + b
@[inline] def sub_u64 (a b : UInt64) : UInt64 := a - b
@[inline] def mul_u64 (a b : UInt64) : UInt64 := a * b
@[inline] def div_u64 (a b : UInt64) : UInt64 := a / b
@[inline] def rem_u64 (a b : UInt64) : UInt64 := a % b
@[inline] def shl_u64 (a b : UInt64) : UInt64 := a <<< b
@[inline] def shr_u64 (a b : UInt64) : UInt64 := a >>> b
@[inline] def bitand_u64 (a b : UInt64) : UInt64 := a &&& b
@[inline] def bitor_u64  (a b : UInt64) : UInt64 := a ||| b
@[inline] def bitxor_u64 (a b : UInt64) : UInt64 := a ^^^ b
@[inline] def bitnot_u64 (a : UInt64)   : UInt64 := ~~~a
@[inline] def eq_u64 (a b : UInt64) : Bool := a == b
@[inline] def ne_u64 (a b : UInt64) : Bool := a != b
@[inline] def lt_u64 (a b : UInt64) : Bool := a < b
@[inline] def le_u64 (a b : UInt64) : Bool := a ≤ b
@[inline] def gt_u64 (a b : UInt64) : Bool := a > b
@[inline] def ge_u64 (a b : UInt64) : Bool := a ≥ b

/-! ### Cast operations

Widening casts preserve the value; narrowing casts truncate (mod 2^target_bits),
matching Rust's `as` semantics for unsigned integers. -/

-- Widening: u8 → larger
@[inline] def cast_u8_u16  (x : UInt8) : UInt16 := x.toUInt16
@[inline] def cast_u8_u32  (x : UInt8) : UInt32 := x.toUInt32
@[inline] def cast_u8_u64  (x : UInt8) : UInt64 := x.toUInt64

-- Widening: u16 → larger
@[inline] def cast_u16_u32 (x : UInt16) : UInt32 := x.toUInt32
@[inline] def cast_u16_u64 (x : UInt16) : UInt64 := x.toUInt64

-- Widening: u32 → u64
@[inline] def cast_u32_u64 (x : UInt32) : UInt64 := x.toUInt64

-- Narrowing: u64 → smaller (truncates)
@[inline] def cast_u64_u32 (x : UInt64) : UInt32 := x.toUInt32
@[inline] def cast_u64_u16 (x : UInt64) : UInt16 := x.toUInt16
@[inline] def cast_u64_u8  (x : UInt64) : UInt8  := x.toUInt8

-- Narrowing: u32 → smaller
@[inline] def cast_u32_u16 (x : UInt32) : UInt16 := x.toUInt16
@[inline] def cast_u32_u8  (x : UInt32) : UInt8  := x.toUInt8

-- Narrowing: u16 → u8
@[inline] def cast_u16_u8  (x : UInt16) : UInt8  := x.toUInt8

/-! ### Signed Integer Operations

Rust signed integers use two's complement wrapping. They are represented as `Int`
with explicit modular reduction (so the wrapping is explicit rather than relying
on a fixed-width type). `bmod_signed w n` reduces `n` to `[-2^(w-1), 2^(w-1))`. -/

/-- Signed modular reduction: maps integer to [-2^(w-1), 2^(w-1)). -/
@[inline] def bmod_signed (bits : Nat) (n : Int) : Int :=
  let m := 2 ^ bits
  let r := n % m
  if r ≥ m / 2 then r - m else r

-- Signed 8-bit operations
@[inline] def add_i8  (a b : Int) : Int := bmod_signed 8 (a + b)
@[inline] def sub_i8  (a b : Int) : Int := bmod_signed 8 (a - b)
@[inline] def mul_i8  (a b : Int) : Int := bmod_signed 8 (a * b)
@[inline] def div_i8  (a b : Int) : Int := if b = 0 then 0 else bmod_signed 8 (a / b)
@[inline] def rem_i8  (a b : Int) : Int := if b = 0 then 0 else bmod_signed 8 (a % b)
@[inline] def neg_i8  (a : Int) : Int := bmod_signed 8 (-a)
@[inline] def eq_i8   (a b : Int) : Bool := a == b
@[inline] def ne_i8   (a b : Int) : Bool := a != b
@[inline] def lt_i8   (a b : Int) : Bool := a < b
@[inline] def le_i8   (a b : Int) : Bool := a ≤ b
@[inline] def gt_i8   (a b : Int) : Bool := a > b
@[inline] def ge_i8   (a b : Int) : Bool := a ≥ b

-- Signed 16-bit operations
@[inline] def add_i16 (a b : Int) : Int := bmod_signed 16 (a + b)
@[inline] def sub_i16 (a b : Int) : Int := bmod_signed 16 (a - b)
@[inline] def mul_i16 (a b : Int) : Int := bmod_signed 16 (a * b)
@[inline] def div_i16 (a b : Int) : Int := if b = 0 then 0 else bmod_signed 16 (a / b)
@[inline] def rem_i16 (a b : Int) : Int := if b = 0 then 0 else bmod_signed 16 (a % b)
@[inline] def neg_i16 (a : Int) : Int := bmod_signed 16 (-a)
@[inline] def eq_i16  (a b : Int) : Bool := a == b
@[inline] def ne_i16  (a b : Int) : Bool := a != b
@[inline] def lt_i16  (a b : Int) : Bool := a < b
@[inline] def le_i16  (a b : Int) : Bool := a ≤ b
@[inline] def gt_i16  (a b : Int) : Bool := a > b
@[inline] def ge_i16  (a b : Int) : Bool := a ≥ b

-- Signed 32-bit operations
@[inline] def add_i32 (a b : Int) : Int := bmod_signed 32 (a + b)
@[inline] def sub_i32 (a b : Int) : Int := bmod_signed 32 (a - b)
@[inline] def mul_i32 (a b : Int) : Int := bmod_signed 32 (a * b)
@[inline] def div_i32 (a b : Int) : Int := if b = 0 then 0 else bmod_signed 32 (a / b)
@[inline] def rem_i32 (a b : Int) : Int := if b = 0 then 0 else bmod_signed 32 (a % b)
@[inline] def neg_i32 (a : Int) : Int := bmod_signed 32 (-a)
@[inline] def eq_i32  (a b : Int) : Bool := a == b
@[inline] def ne_i32  (a b : Int) : Bool := a != b
@[inline] def lt_i32  (a b : Int) : Bool := a < b
@[inline] def le_i32  (a b : Int) : Bool := a ≤ b
@[inline] def gt_i32  (a b : Int) : Bool := a > b
@[inline] def ge_i32  (a b : Int) : Bool := a ≥ b

-- Signed 64-bit operations
@[inline] def add_i64 (a b : Int) : Int := bmod_signed 64 (a + b)
@[inline] def sub_i64 (a b : Int) : Int := bmod_signed 64 (a - b)
@[inline] def mul_i64 (a b : Int) : Int := bmod_signed 64 (a * b)
@[inline] def div_i64 (a b : Int) : Int := if b = 0 then 0 else bmod_signed 64 (a / b)
@[inline] def rem_i64 (a b : Int) : Int := if b = 0 then 0 else bmod_signed 64 (a % b)
@[inline] def neg_i64 (a : Int) : Int := bmod_signed 64 (-a)
@[inline] def eq_i64  (a b : Int) : Bool := a == b
@[inline] def ne_i64  (a b : Int) : Bool := a != b
@[inline] def lt_i64  (a b : Int) : Bool := a < b
@[inline] def le_i64  (a b : Int) : Bool := a ≤ b
@[inline] def gt_i64  (a b : Int) : Bool := a > b
@[inline] def ge_i64  (a b : Int) : Bool := a ≥ b

/-! ### Signed cast operations -/

@[inline] def cast_i8_i16  (x : Int) : Int := bmod_signed 16 x
@[inline] def cast_i8_i32  (x : Int) : Int := bmod_signed 32 x
@[inline] def cast_i8_i64  (x : Int) : Int := bmod_signed 64 x
@[inline] def cast_i16_i32 (x : Int) : Int := bmod_signed 32 x
@[inline] def cast_i16_i64 (x : Int) : Int := bmod_signed 64 x
@[inline] def cast_i32_i64 (x : Int) : Int := bmod_signed 64 x
@[inline] def cast_i64_i32 (x : Int) : Int := bmod_signed 32 x
@[inline] def cast_i64_i16 (x : Int) : Int := bmod_signed 16 x
@[inline] def cast_i64_i8  (x : Int) : Int := bmod_signed 8 x
@[inline] def cast_i32_i16 (x : Int) : Int := bmod_signed 16 x
@[inline] def cast_i32_i8  (x : Int) : Int := bmod_signed 8 x
@[inline] def cast_i16_i8  (x : Int) : Int := bmod_signed 8 x

-- Cross-sign casts
@[inline] def cast_u8_i16  (x : UInt8)  : Int := bmod_signed 16 (x.toBitVec.toNat : Int)
@[inline] def cast_u16_i32 (x : UInt16) : Int := bmod_signed 32 (x.toBitVec.toNat : Int)
@[inline] def cast_u32_i64 (x : UInt32) : Int := bmod_signed 64 (x.toBitVec.toNat : Int)
@[inline] def cast_i8_u8   (x : Int) : UInt8  := UInt8.ofNat x.toNat
@[inline] def cast_i16_u16 (x : Int) : UInt16 := UInt16.ofNat x.toNat
@[inline] def cast_i32_u32 (x : Int) : UInt32 := UInt32.ofNat x.toNat
@[inline] def cast_i64_u64 (x : Int) : UInt64 := UInt64.ofNat x.toNat

/-! ### Collection operations -/

/-- Create an array filled with `n` copies of `val`. -/
@[inline] def repeat_ {α : Type} (val : α) (n : Int) : Array α :=
  (List.replicate n.toNat val).toArray

/-- Array length. -/
@[inline] def array_len {α : Type} (arr : Array α) : Int := arr.size

/-- Rotate a UInt64 right by `n` bits. -/
@[inline] def rotate_right_u64 (x : UInt64) (n : UInt32) : UInt64 :=
  let shift := n.toUInt64 % 64
  (x >>> shift) ||| (x <<< (64 - shift))

/-- Rotate right (Int version for untyped mode). -/
@[inline] def rotate_right (x n : Int) : Int :=
  let xn := x.toNat
  let shift := n.toNat % 64
  (((xn >>> shift) ||| (xn <<< (64 - shift))) % (2 ^ 64) : Nat)

/-- Rotate a UInt32 left by `n` bits. -/
@[inline] def rotate_left_u32 (x : UInt32) (n : UInt32) : UInt32 :=
  let shift := n % 32
  (x <<< shift) ||| (x >>> (32 - shift))

/-- Rotate a UInt64 left by `n` bits. -/
@[inline] def rotate_left_u64 (x : UInt64) (n : UInt32) : UInt64 :=
  let shift := n.toUInt64 % 64
  (x <<< shift) ||| (x >>> (64 - shift))

/-- Rotate left (Int version for untyped mode). -/
@[inline] def rotate_left (x n : Int) : Int :=
  let xn := x.toNat
  let shift := n.toNat % 64
  (((xn <<< shift) ||| (xn >>> (64 - shift))) % (2 ^ 64) : Nat)

/-- Wrapping add — alias for width-aware addition. -/
@[inline] def wrapping_add_u32 (a b : UInt32) : UInt32 := a + b
@[inline] def wrapping_add_u64 (a b : UInt64) : UInt64 := a + b
@[inline] def wrapping_sub_u32 (a b : UInt32) : UInt32 := a - b
@[inline] def wrapping_sub_u64 (a b : UInt64) : UInt64 := a - b
@[inline] def wrapping_mul_u32 (a b : UInt32) : UInt32 := a * b
@[inline] def wrapping_mul_u64 (a b : UInt64) : UInt64 := a * b

/-- Wrapping arithmetic (polymorphic for untyped mode). -/
@[inline] def wrapping_add {α : Type} [_root_.Add α] (a b : α) : α := a + b
@[inline] def wrapping_sub {α : Type} [_root_.Sub α] (a b : α) : α := a - b
@[inline] def wrapping_mul {α : Type} [_root_.Mul α] (a b : α) : α := a * b

/-- Update array element at index `i` with value `v`. Out-of-bounds is a no-op. -/
@[inline] def array_update {α : Type} (arr : Array α) (i : Int) (v : α) : Array α :=
  let n := i.toNat
  if h : n < arr.size then arr.set n v else arr

/-- Functional field update on a tuple-encoded struct: replace the head field.
    A field at position `i` of `n` (with `i < n - 1`) updates as
    `struct_update_snd^i` around one `struct_update_fst`; the last field uses
    `struct_update_snd` at depth `n - 2`. The emitter composes these from the
    `struct_update#S#i#n` head. -/
@[inline] def struct_update_fst {α β : Type} (s : α × β) (v : α) : α × β := (v, s.2)

/-- Functional field update on a tuple-encoded struct: replace the tail
    (the fields after the first), keeping the head field. -/
@[inline] def struct_update_snd {α β : Type} (s : α × β) (t : β) : α × β := (s.1, t)

/-- Push an element onto an array. -/
@[inline] def push {α : Type} (arr : Array α) (x : α) : Array α := arr.push x

-- Array literal — surface code uses `#[...]` syntax instead.
-- Not called directly; `array_lit` in ImpExpr maps to `#[...]` in surface Lean.

/-- Byte string literal: the default value of the expected type. -/
@[inline] def literal {α : Type} [Inhabited α] : α := default

/-- Copy from slice — identity in untyped extraction. -/
@[inline] def copy_from_slice {α : Type} (_dst : Array α) (src : Array α) : Array α := src

/-- Extend from slice — append in untyped extraction. -/
@[inline] def extend_from_slice {α : Type} (dst : Array α) (src : Array α) : Array α := dst ++ src

/-- Into iter — identity in untyped extraction. -/
@[inline] def into_iter {α : Type} (x : α) : α := x

/-- Into vec — identity in untyped extraction. -/
@[inline] def into_vec {α : Type} (x : α) : α := x

/-- Next (iterator) — identity in untyped extraction. -/
@[inline] def next {α : Type} (x : α) : α := x

/-- Enumerate — identity in untyped extraction. -/
@[inline] def enumerate {α : Type} (x : α) : α := x

/-- With capacity — empty array in untyped extraction. -/
@[inline] def with_capacity {α : Type} (_n : Int) : Array α := #[]

/-- From elem — repeat in untyped extraction. -/
@[inline] def from_elem {α : Type} (val : α) (n : Int) : Array α :=
  (List.replicate n.toNat val).toArray

/-- Check if array is empty (Vec::is_empty). -/
@[inline] def is_empty {α : Type} (arr : Array α) : Bool := arr.isEmpty

/-- Truncate — identity in untyped extraction. -/
@[inline] def truncate {α : Type} (arr : Array α) (_n : Int) : Array α := arr

/-- Mutable index — element access in untyped extraction.
    Same as `index` (returns element at position). The mutation tracking
    is handled separately by the pipeline's local mutation phase. -/
@[inline] def index_mut {α : Type} [Inhabited α] (a : Array α) (i : Int) : α :=
  index a i

/-- Range-to constructor (0..hi). -/
@[inline] def RangeTo (hi : Int) : Int := hi

/-- Range-from constructor (lo..). -/
@[inline] def RangeFrom (lo : Int) : Int := lo

/-- Deref — identity in untyped extraction. -/
@[inline] def deref {α : Type} (x : α) : α := x

/-- Clone — identity in untyped extraction (Rust Clone::clone). -/
@[inline] def clone {α : Type} (x : α) : α := x

/-- to_vec — identity in untyped extraction (Rust [T]::to_vec / clone). -/
@[inline] def to_vec {α : Type} (x : α) : α := x

/-- Assignment: the identity. -/
@[inline] def assign {α : Type} (x : α) : α := x


/-- `From::from`: the identity. -/
@[inline] def from_val {α : Type} (x : α) : α := x

-- USize casts
@[inline] def cast_usize_u64 (x : USize) : UInt64 := UInt64.ofNat x.toNat
@[inline] def cast_u64_usize (x : UInt64) : USize := USize.ofNat x.toBitVec.toNat

/-- Slice: take first n elements (arr[..n]). -/
@[inline] def slice_to {α : Type} (arr : Array α) (n : Int) : Array α :=
  arr.extract 0 n.toNat

/-- Slice: drop first n elements (arr[n..]). -/
@[inline] def slice_from {α : Type} (arr : Array α) (n : Int) : Array α :=
  arr.extract n.toNat arr.size

/-- Slice: range (arr[lo..hi]). -/
@[inline] def slice_range {α : Type} (arr : Array α) (lo hi : Int) : Array α :=
  arr.extract lo.toNat hi.toNat

/-- Range update: `arr` with position `lo + k` set to `src[k]` for every `k`
    below both `hi - lo` and `src.size`. Positions outside `lo ..< hi`, and
    positions of that range beyond `src`'s length or `arr`'s size, keep their
    values, so the result has the size of `arr`.

    The functional form of `arr[lo..hi].copy_from_slice(src)`, whose Rust
    precondition is `hi - lo = src.len()`. -/
def slice_update {α : Type} (arr : Array α) (lo hi : Int) (src : Array α) : Array α :=
  let l := lo.toNat
  let n := min (hi.toNat - l) src.size
  (List.range n).foldl
    (fun acc k => match src[k]? with
      | some v => acc.setIfInBounds (l + k) v
      | none => acc) arr

/-- The integers `lo, lo + 1, …` below `hi`, as an array (for `collect(0..n)`). -/
@[inline] def range (lo hi : Int) : Array Int :=
  (List.range (hi - lo).toNat |>.map (· + lo.toNat) |>.map Int.ofNat).toArray

/-- Range constructor (lo..hi) — returns Array of values for into_iter. -/
@[inline] def Range (lo hi : Int) : Array Int := range lo hi

/-- iter — identity (iterator representation = array in untyped mode). -/
@[inline] def iter {α : Type} (arr : Array α) : Array α := arr

/-- map — apply a function to each element of an array. -/
@[inline] def map_arr {α β : Type} (arr : Array α) (f : α → β) : Array β := arr.map f

/-- concatMap — flat_map equivalent: apply f to each element and concatenate results. -/
@[inline] def concatMap {α β : Type} (arr : Array α) (f : α → Array β) : Array β :=
  arr.foldl (fun acc x => acc ++ f x) #[]

/-- collect — identity for arrays, range for integers. -/
@[inline] def collect {α : Type} (arr : Array α) : Array α := arr

/-- assert_failed — Rust's assertion-failure panic, as the unit value. -/
@[inline] def assert_failed {α β γ δ : Type} (_kind : α) (_left : β) (_right : γ) (_msg : δ) : Unit := ()

/-- one — numeric literal 1. -/
@[inline] def one : Int := 1

/-- Number of `1` bits in the binary representation of a natural number. -/
def bitCount (n : Nat) : Nat :=
  if h : n = 0 then 0 else n % 2 + bitCount (n / 2)
decreasing_by omega

/-- count_ones — Rust's population count.

    Defined on non-negative arguments, which is the range of every
    width-aware bit operation in this runtime (`bitand_w`, `bitxor_w`,
    `mod2w` all return `Int.ofNat`). A negative argument has no finite
    binary representation and yields `-1`, a value outside the range of a
    population count. -/
@[inline] def count_ones (x : Int) : Int :=
  if 0 ≤ x then (bitCount x.toNat : Int) else -1

/-- assert_failed' — Rust's `assert!` macro failure, as the unit value. -/
@[inline] def assert_failed' {α β γ δ : Type} (_ : α) (_ : β) (_ : γ) (_ : δ) : Unit := ()

/-- Re-wrap a nested forFoldReturn result for use in an outer forFoldReturn body.
    Converts `ControlFlow β (ControlFlow γ α)` → `ControlFlow (ControlFlow β γ) α`.
    This is needed when one `forFoldReturn` is directly nested inside another. -/
def rewrapForFoldReturn {α β γ : Type}
    (x : ControlFlow β (ControlFlow γ α)) : ControlFlow (ControlFlow β γ) α :=
  match x with
  | .Break v => .Break (.Break v)
  | .Continue (.Break v) => .Break (.Continue v)
  | .Continue (.Continue a) => .Continue a

/-! ### Width-indexed byte (de)serialization and overflowing arithmetic

The inherent integer methods `uN::to_be_bytes`, `uN::from_le_bytes`,
`uN::overflowing_add`, … depend on the width `N`. The adapter suffixes each
call with its width (`to_be_bytes#32`), and the printer renders it as the
builtin of that width below, so the extraction carries no untyped dependency
field for them. -/

/-- The `w / 8` big-endian bytes of `a mod 2^w`, most significant first. -/
@[inline] def to_be_bytes_w (w : Nat) (a : Int) : Array Int :=
  let n := w / 8
  let v := mod2w w a
  (Array.range n).map fun k => v / (256 : Int) ^ (n - 1 - k) % 256

/-- The `w / 8` little-endian bytes of `a mod 2^w`, least significant first. -/
@[inline] def to_le_bytes_w (w : Nat) (a : Int) : Array Int :=
  let v := mod2w w a
  (Array.range (w / 8)).map fun k => v / (256 : Int) ^ k % 256

/-- The big-endian integer of a byte array, reduced to width `w`; the first
    element is the most significant byte. -/
@[inline] def from_be_bytes_w (w : Nat) (a : Array Int) : Int :=
  mod2w w (a.foldl (fun acc b => acc * 256 + b % 256) 0)

/-- The little-endian integer of a byte array, reduced to width `w`; the first
    element is the least significant byte. -/
@[inline] def from_le_bytes_w (w : Nat) (a : Array Int) : Int :=
  mod2w w (a.foldr (fun b acc => acc * 256 + b % 256) 0)

/-- `(a + b) mod 2^w`, with the carry-out. -/
@[inline] def overflowing_add_w (w : Nat) (a b : Int) : Int × Bool :=
  let s := a + b
  (mod2w w s, decide (s ≥ (2 : Int) ^ w))

/-- `(a - b) mod 2^w`, with the borrow-out. -/
@[inline] def overflowing_sub_w (w : Nat) (a b : Int) : Int × Bool :=
  let d := a - b
  (mod2w w d, decide (d < 0))

/-! ### Uninterpreted conversions -/

/-- Zip — pairs two iterables element-wise. Polymorphic in both element
    types so that `Hax.zip (xs : Array A) (ys : Array B) : Array (A × B)`
    typechecks for any A, B. Returns the empty array in the untyped
    extraction. -/
@[inline] def zip {α β : Type} (_xs : Array α) (_ys : Array β) : Array (α × β) := #[]

/-- `Into::into`: identity. The typed extraction emits
    `Hax.into x` for Rust `x.into()` calls where the target type is
    deduced from context; the emitted Lean code is already typed at the
    target, so the conversion is the identity. -/
@[inline] def into {α : Type} (x : α) : α := x

/-- Bridge cast: an uninterpreted conversion from `α` to a nonempty type `β`,
    modelling Rust constructors and trait conversions whose semantics a
    CatCrypt-side bridge supplies. The `Nonempty β` argument makes the
    declaration a consistent opaque constant. -/
noncomputable opaque bridgeCast {α β : Type} [Nonempty β] : α → β

/-- Tuple-newtype positional projection: `Commitment(inner).0` style access.
    The Rust source has `struct Commitment(Vec<u8>)` and bodies use `c.0`
    to unwrap. Identity at the surface; the bridge adapter materializes
    the unwrap. -/
@[inline] def «.0» {α : Type} (x : α) : α := x

/-- SHA-256 as an uninterpreted hash on byte arrays. The protocol's
    concrete instance supplies the function through the bridge-adapter pattern
    at the CatCrypt surface. -/
noncomputable opaque sha256 : Array Int → Array Int

/-- Uninterpreted constructor for tuple-struct / wrapper constructors
    (`T::new(arg)`). Heterogeneous-polymorphic so the typed-pipeline
    pattern `(new (into key) : Aes256)` typechecks: the outer
    ascription pins β to `Aes256`, the inner `into key : α` keeps
    `α = Array Int`. -/
@[no_expose] noncomputable def «new» {α β : Type} [Nonempty β] (x : α) : β := bridgeCast x

end Hax

/-- Default value for unbound mutation accumulators.
    When the code generator emits `_assign` as a fold accumulator initial value
    before it has been bound, this top-level definition provides a default. -/
@[inline] def _assign {α : Type} [Inhabited α] : α := default

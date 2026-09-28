/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import HaxLean.Rust
public meta import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# A prelude for the Aeneas Lean backend over the vendored Aeneas `Std` model

The Aeneas Lean backend prints code against the package `Aeneas`. This module gives the
names that output uses beyond the vendored `Aeneas.Std` (`HaxLean/Rust`, Aeneas commit
`6852e647`), so a backend file elaborates with `import Aeneas` replaced by
`import HaxLean.AeneasBackendPrelude`:

* `Result` is `Aeneas.Std.RustM`, with `Result.ok`, `Result.fail`, `Result.div`;
* `core.iter.range.Step`, `core.iter.range.StepUsize` and
  `core.iter.range.IteratorRange.next`, the iteration of `start..end`;
* the simp attributes `global_simps`, `rust_loop_body` and `rust_loop`, which the backend
  places on its definitions.

The Aeneas release that printed the output (commit `b08bf81`) defines `Result` as an
interaction tree over the effect `RustEffect`; the vendored model defines it as the flat
type with `ok`, `fail` and `div`. `core.iter.range.Step` here carries the comparison and
`forward_checked` only; upstream it also carries the `Clone` and `PartialOrd` instances
and `steps_between`, `backward_checked`. `IteratorRange.next` follows the upstream
definition with `clone` the identity and `lt` the comparison of values.
-/

register_simp_attr global_simps
register_simp_attr rust_loop_body
register_simp_attr rust_loop

@[expose] public section

set_option autoImplicit false

namespace Aeneas.Std

/-- The result type of the Aeneas backend output. -/
abbrev Result := RustM

/-- A value. -/
abbrev Result.ok {α : Type} (v : α) : Result α := RustM.ok v

/-- A failure. -/
abbrev Result.fail {α : Type} (e : Error) : Result α := RustM.fail e

/-- Divergence. -/
abbrev Result.div {α : Type} : Result α := RustM.div

/-- The operations of `core::iter::Step` that `Range::next` uses. -/
structure core.iter.range.Step (Self : Type) where
  lt : Self → Self → RustM Bool
  forward_checked : Self → Usize → RustM (Option Self)

/-- `forward_checked` on an unsigned scalar: `start + n` when it is in range. -/
def core.iter.range.UScalarStep.forward_checked {ty : UScalarTy}
    (start : UScalar ty) (n : Usize) : RustM (Option (UScalar ty)) :=
  if h : start.val + n.val < 2 ^ ty.numBits then
    .ok (some (UScalar.ofNatCore (start.val + n.val) h))
  else .ok none

/-- `Step` on an unsigned scalar type. -/
def core.iter.range.UScalarStep (ty : UScalarTy) : core.iter.range.Step (UScalar ty) where
  lt a b := .ok (decide (a.val < b.val))
  forward_checked := core.iter.range.UScalarStep.forward_checked

/-- `Step` on `usize`. -/
abbrev core.iter.range.StepUsize := core.iter.range.UScalarStep .Usize

/-- `Range::next`: `some start` and the range from `start + 1` when `start < end`, `none`
    and the range unchanged otherwise. -/
def core.iter.range.IteratorRange.next {A : Type} (StepInst : core.iter.range.Step A)
    (range : core.ops.range.Range A) : RustM (Option A × core.ops.range.Range A) := do
  let cmp ← StepInst.lt range.start range.end
  if cmp then
    let n ← StepInst.forward_checked range.start (UScalar.ofNatCore 1 (by
      show 1 < 2 ^ System.Platform.numBits
      rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide))
    match n with
    | none => .fail .panic
    | some n => .ok (some range.start, { range with start := n })
  else .ok (none, range)

end Aeneas.Std

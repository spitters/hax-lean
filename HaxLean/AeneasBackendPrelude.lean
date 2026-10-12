/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import HaxLean.Rust
public meta import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Elab.Command

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
  places on its definitions;
* the command `open N hiding namespace a b` and the `CoreModels.core` names the output of
  the hax 0.4.2 Lean backend (Aeneas `build-183e4f0`) uses beside `Aeneas.Std`: `Option`
  with `Some` and `None`, `ops.range.Range`, `iter.range.Step`,
  `Usize.Insts.CoreIterRangeStep`, `Range::next`, and `wrapping_add`, `wrapping_sub`,
  `wrapping_mul` on unsigned scalars in `RustM`. A file of that output elaborates with
  `import Aeneas` replaced by `import HaxLean.AeneasBackendPrelude`, `import CoreModels`
  removed, and the Mathlib linter options removed.

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

namespace CoreModels.Command

open Lean Elab Command

/-- `open N hiding namespace a b`: opens the namespace `N` except every declaration under
    `N.a` and `N.b`. The command of the hax Lean library `CoreModels.Command`
    (cryspen/hax, `hax-lib/proof-libs/lean`, Apache-2.0). -/
syntax (name := openHidingNs) "open" ident "hiding" "namespace" ident+ : command

/-- Elaborates `open N hiding namespace a b` as `open N hiding` the declarations under
    `N.a` and `N.b`. -/
@[command_elab openHidingNs]
meta def elabOpenHidingNs : CommandElab := fun stx => do
  let nsStx : Ident := ⟨stx[1]⟩
  let subs : Array Ident := stx[4].getArgs.map (⟨·⟩)
  let ns ← resolveUniqueNamespace nsStx
  let except : List Name := (← getEnv).constants.fold (init := []) fun acc nm _ =>
    if subs.any (fun sub => (ns ++ sub.getId).isPrefixOf nm) then
      nm.replacePrefix ns .anonymous :: acc
    else acc
  activateScoped ns
  modifyScope fun s => { s with openDecls := OpenDecl.simple ns except :: s.openDecls }

end CoreModels.Command

/-! ## The `CoreModels.core` names of the Aeneas backend output

The hax Lean library `CoreModels` gives the `core` items the backend output calls, under
`CoreModels.core`; the output opens `Aeneas.Std` without its `core` namespace. The names
below are those items over the vendored `Aeneas.Std` model. -/

namespace CoreModels.core

open Aeneas.Std Aeneas.Std.ScalarElab

namespace option

/-- Rust's `Option`: Lean's `Option`. -/
abbrev Option := _root_.Option

/-- `Option::Some`. -/
@[match_pattern] abbrev Option.Some {T : Type} (x : T) : Option T := _root_.Option.some x

/-- `Option::None`. -/
@[match_pattern] abbrev Option.None {T : Type} : Option T := _root_.Option.none

end option

/-- `core::ops::range::Range`: the vendored `Range`. -/
abbrev ops.range.Range := Aeneas.Std.core.ops.range.Range

/-- `core::iter::range::Step`: the comparison and `forward_checked`. -/
abbrev iter.range.Step := Aeneas.Std.core.iter.range.Step

/-- `Step` on `usize`. -/
abbrev Usize.Insts.CoreIterRangeStep : iter.range.Step Usize :=
  Aeneas.Std.core.iter.range.StepUsize

/-- `Iterator::next` on `Range<A>`. -/
abbrev ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next :=
  @Aeneas.Std.core.iter.range.IteratorRange.next

uscalar /-- `wrapping_add` on an unsigned scalar, in `RustM`. -/
def num.«%S».wrapping_add (x y : «%S») : RustM «%S» :=
  .ok (Aeneas.Std.core.num.«%S».wrapping_add x y)

uscalar /-- `wrapping_sub` on an unsigned scalar, in `RustM`. -/
def num.«%S».wrapping_sub (x y : «%S») : RustM «%S» :=
  .ok (Aeneas.Std.core.num.«%S».wrapping_sub x y)

uscalar /-- `wrapping_mul` on an unsigned scalar, in `RustM`. -/
def num.«%S».wrapping_mul (x y : «%S») : RustM «%S» :=
  .ok (Aeneas.Std.core.num.«%S».wrapping_mul x y)

end CoreModels.core

/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

public import HaxLean.AeneasBackendPrelude

/-!
# The `Std` names of the Aeneas front, resolved under the prelude

Each declaration below is written in the form the Aeneas Lean backend (commit `b08bf81`)
prints, with the header `open Aeneas Aeneas.Std Result ControlFlow Error` of its output,
and uses the `Std` names of one group of constructs the Aeneas front of the CatCrypt
compiler reads (rows AE-1 to AE-6 of the Aeneas front design of 2026-11-03). The module
elaborates exactly when every such name resolves under `HaxLean.AeneasBackendPrelude` at the
type the output gives it. The comparison of each name with its upstream definition is
`docs/aeneas-std-names.md`.

No module imports this one; it is built by name.
-/

@[expose] public section

set_option autoImplicit false

namespace HaxLean.AeneasBackendNames

open Aeneas Aeneas.Std Result ControlFlow Error

/-! ## Scalars (row AE-1) -/

/-- Checked `+`, `-`, `*` on `u8`, `u16`, `u32`, `u64` and `usize`. -/
def checkedArith (a b : Std.U8) (c d : Std.U16) (e f : Std.U32) (x y : Std.U64)
    (i j : Std.Usize) : Result (Std.U64 × Std.Usize) := do
  let _ ← a + b
  let _ ← c - d
  let _ ← e * f
  let x1 ← x + y
  let x2 ← x1 - y
  let x3 ← x2 * y
  let i1 ← i + j
  ok (x3, i1)

/-- `/` and `%` on unsigned scalars (row AE-9). -/
def divRem (x y : Std.U64) : Result Std.U64 := do
  let q ← x / y
  q % y

/-- `wrapping_add`, `wrapping_sub`, `wrapping_mul`, `wrapping_shl`, `wrapping_shr`,
    `rotate_left`, `rotate_right`, read through `lift`. -/
def wrapping (x y : Std.U64) (s : Std.U32) (b c : Std.U8) : Result Std.U64 := do
  let _ ← lift (core.num.U8.wrapping_add b c)
  let x1 ← lift (core.num.U64.wrapping_add x y)
  let x2 ← lift (core.num.U64.wrapping_sub x1 y)
  let x3 ← lift (core.num.U64.wrapping_mul x2 y)
  let x4 ← lift (core.num.U64.wrapping_shl x3 s)
  let x5 ← lift (core.num.U64.wrapping_shr x4 s)
  let x6 ← lift (core.num.U64.rotate_left x5 s)
  lift (core.num.U64.rotate_right x6 s)

/-- `&&&`, `|||`, `^^^`, `~~~` and the checked shifts `<<<`, `>>>` with amounts of other
    unsigned widths. -/
def bitwise (x y : Std.U64) (s : Std.U32) (t : Std.U8) (u : Std.Usize) :
    Result Std.U64 := do
  let x1 := x &&& y
  let x2 := x1 ||| y
  let x3 := x2 ^^^ y
  let x4 := ~~~x3
  let x5 ← x4 <<< s
  let x6 ← x5 >>> t
  x6 <<< u

/-- Unsigned casts and the cast of a boolean. -/
def casts (b : Std.U8) (w : Std.U32) (x : Std.U64) (c : Bool) :
    Result (Std.U64 × Std.U32 × Std.Usize × Std.U64) := do
  let x1 ← lift (UScalar.cast .U64 b)
  let x2 ← lift (UScalar.cast .U32 x)
  let x3 ← lift (UScalar.cast .Usize w)
  let x4 ← lift (UScalar.cast_fromBool .U64 c)
  ok (x1, x2, x3, x4)

/-- Comparisons as decided propositions, the boolean connectives, literals. -/
def compare (x y : Std.U64) (i : Std.Usize) (b : Std.U8) : Result Bool := do
  let c1 := x < y
  let c2 := x <= y
  let c3 := x = y
  let c4 := x != y
  let c5 := i < 16#usize
  let c6 := b = 255#u8
  if c1 then ok (c2 && c3) else
  if c4 then ok (!c5 || c6) else
  if x = 0#u64 then ok true else ok (decide (y > 1#u64) && 7#u32 = 7#u32 && 3#u16 = 3#u16)

/-! ## Arrays (row AE-2) -/

/-- `index_usize`, `update`, `index_mut_usize` with its backward function, `repeat`,
    `make`. -/
def arrays (a : Array Std.U64 4#usize) (i : Std.Usize) (x : Std.U64) :
    Result (Array Std.U64 4#usize) := do
  let y ← Array.index_usize a i
  let a1 ← Array.update a i y
  let (z, index_mut_back) ← Array.index_mut_usize a1 i
  let z1 ← z + x
  let a2 := index_mut_back z1
  let r := Array.repeat 4#usize 0#u64
  let m := Array.make 4#usize [0#u64, 1#u64, 2#u64, 3#u64]
  let _ ← Array.index_usize r i
  let _ ← Array.index_usize m i
  ok a2

/-- An array whose length is a parameter. -/
def arrayGeneric {N : Std.Usize} (a : Array Std.U64 N) (i : Std.Usize) : Result Std.U64 :=
  Array.index_usize a i

/-! ## Binds, tuples, conditionals (row AE-3) -/

/-- A pair result destructured by `uncurry`, a pure `let`, a conditional. -/
def binds (x y : Std.U64) : Result Std.U64 := do
  let p ← ok (x, y)
  let s ← uncurry (fun (a b : Std.U64) => a + b) p
  let t := s
  if t < x then ok x else ok t

/-! ## Loops (row AE-4) -/

/-- The body of a loop over a carried state, in `ControlFlow`. -/
def sum_loop.body (max : Std.U32) (i : Std.U32) (s : Std.U32) :
    Result (ControlFlow (Std.U32 × Std.U32) Std.U32) := do
  if i < max then
    let s1 ← s + i
    let i1 ← i + 1#u32
    ok (cont (i1, s1))
  else ok (done s)

/-- The loop over the carried state. -/
def sum_loop (max : Std.U32) (i : Std.U32) (s : Std.U32) : Result Std.U32 :=
  loop (fun (i1, s1) => sum_loop.body max i1 s1) (i, s)

/-- The body of a `for` loop over a `usize` range, stepping the iterator by
    `IteratorRange.next`. -/
def range_loop.body (iter1 : core.ops.range.Range Std.Usize) (x : Std.U64) :
    Result (ControlFlow ((core.ops.range.Range Std.Usize) × Std.U64) Std.U64) := do
  let (o, iter2) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter1
  match o with
  | none => ok (done x)
  | some _ =>
    let x1 ← lift (core.num.U64.wrapping_add x 1#u64)
    ok (cont (iter2, x1))

/-- The `for` loop over `0..n`. -/
def range_loop (n : Std.Usize) (x : Std.U64) : Result Std.U64 :=
  loop (fun (iter2, x1) => range_loop.body iter2 x1) ({ start := 0#usize, «end» := n }, x)

/-- `IteratorRange.next` at the `Step` of each unsigned width. -/
def range_next (r8 : core.ops.range.Range Std.U8) (r16 : core.ops.range.Range Std.U16)
    (r32 : core.ops.range.Range Std.U32) (r64 : core.ops.range.Range Std.U64) :
    Result Unit := do
  let _ ← core.iter.range.IteratorRange.next core.iter.range.StepU8 r8
  let _ ← core.iter.range.IteratorRange.next core.iter.range.StepU16 r16
  let _ ← core.iter.range.IteratorRange.next core.iter.range.StepU32 r32
  let _ ← core.iter.range.IteratorRange.next core.iter.range.StepU64 r64
  ok ()

/-! ## Failure (row AE-5) -/

/-- `massert`, `fail`, and the error kind of an explicit panic. -/
def failure (x y : Std.U64) : Result Std.U64 := do
  massert (x < y)
  if x = y then fail panic else ok x

/-! ## Opaque callees (row AE-6)

An opaque callee is an `axiom` of the output, abstracted by the reader; it uses no `Std` name
beyond the types of its signature, which the declarations above use. -/

end HaxLean.AeneasBackendNames

# The `Std` names of the Aeneas front: vendored model against upstream

Row AE-8 of the Aeneas front design of 2026-11-03. The Aeneas front of the CatCrypt compiler
reads Lean output of the Aeneas backend elaborated against `HaxLean.AeneasBackendPrelude`
(the vendored `Aeneas.Std` model of `HaxLean/Rust`, ported from cryspen/aeneas `6852e647`,
no Mathlib, flat result monad) instead of upstream `Aeneas` (AeneasVerif/aeneas
`b08bf81f2524ee295a8c37444893acfc9c5f4dde`, `backends/lean/Aeneas/Std`, Mathlib v4.31,
interaction-tree result monad). This note lists, for every `Std` name the constructs of rows
AE-1 to AE-6 (and AE-9) use, where it is defined on each side and how the two definitions
compare. `HaxLean/AeneasBackendNames.lean` uses each name in the form the backend prints
it, under the header `open Aeneas Aeneas.Std Result ControlFlow Error`; that module
elaborates exactly when every name resolves under the prelude.

Paths: `HL/` is `hax-lean/HaxLean/Rust/`, `HP` is `hax-lean/HaxLean/AeneasBackendPrelude.lean`,
`AE/` is `aeneas/backends/lean/Aeneas/Std/` at `b08bf81`. Line numbers are of those commits.

## Summary

* On the value of a successful run the two models agree for every name below: each
  vendored definition returns `ok r` exactly when the upstream one returns `ok r`, with the
  same `r` read through `UScalar.bv`, `UScalar.val`, `Array.val`. The comparison is a reading
  of the definitions, not a theorem: upstream and vendored `Std` cannot be imported together
  (the same names, different toolchains and dependencies).
* The result type differs: upstream `Result α := ITree RustEffect α`, irreducible, with
  `fail e` a `vis` node and `div := ITree.div`; vendored `RustM` is the inductive
  `ok | fail | div` with the flat order. `ok`, `bind` and `pure` correspond; a statement of
  the form "`f a = ok y` implies ..." transfers name by name, while a statement about
  failure or divergence depends on the model.
* Error kinds differ: upstream has seven (`assertionFailure`, `integerOverflow`,
  `divisionByZero`, `arrayOutOfBounds`, `maximumSizeExceeded`, `panic`, `undef`), the
  vendored model two (`panic`, `undef`), and every upstream failure of the names below is a
  vendored `panic`. The front relates only `ok` values (the direction `ok` to `some` of
  `NFEntry.sound`), so the kind of a failure does not enter its statements.
* The `Array` representation differs: upstream a structure over the length-indexed
  inductive `ListN α n.val` with `Array.val := list.toList`; vendored the subtype
  `{ l : List α // l.length = n.val }`. Both expose `Array.val : List α` and the length
  property, and every operation below is defined through `val` on both sides.
* Added to the prelude for this row: `core.iter.range.StepU8`, `StepU16`, `StepU32`,
  `StepU64` (the `Step` of a `for` loop over a range of that width). Every other name was
  present.

## Results and binds (rows AE-3, AE-5)

| name | vendored | upstream | comparison |
|---|---|---|---|
| `Result` | `HP:53`, `abbrev Result := RustM`; `RustM` inductive `ok \| fail \| div` (`HL/Primitives.lean:55-59`) | `AE/Primitives.lean:92`, `ITree RustEffect α`, irreducible | flat type against interaction tree; `ok` values correspond |
| `Result.ok` / `ok` | `HP:56`, `RustM.ok` | `AE/Primitives.lean:95`, `.ret a` | same value |
| `Result.fail` / `fail` | `HP:59`, `RustM.fail e` | `AE/Primitives.lean:102`, a `vis (.fail e)` node | failure on both sides; kinds differ (above) |
| `Result.div` | `HP:62`, `RustM.div` | `AE/Primitives.lean:107`, `ITree.div` | divergence; bottom of the flat order against the coinductive order |
| `bind` (`do`, `let x ← e`) | `HL/Primitives.lean:115-119`, match on `ok`/`fail`/`div` | `AE/Primitives.lean:109-110`, `ITree.bind` | `bind (ok a) f = f a` on both; failure and divergence propagate on both |
| `Error`, `panic` | `HL/Primitives.lean:47-50`, `panic \| undef` | `AE/Primitives.lean:65-73`, seven kinds | `fail panic` exists on both |
| `massert b` | `HL/Primitives.lean:86-87`, `ok ()` or `fail panic` | `AE/Primitives.lean:250-251`, `ok ()` or `fail assertionFailure` | same `ok`; kind of the failure differs |
| `lift x` | `HL/Primitives.lean:235`, `RustM.ok x` | `AE/Primitives.lean:456`, `Result.ok x` | same value |
| `uncurry f` | `HL/Primitives.lean:184-185`, `fun (a, b) => f a b` | `AE/Primitives.lean:378-379`, the same | identical |

## Scalars (rows AE-1, AE-9)

| name | vendored | upstream | comparison |
|---|---|---|---|
| `UScalarTy`, `UScalarTy.numBits` | `HL/Scalar/Core.lean:61-68`, `Usize` of width `System.Platform.numBits` | `AE/Scalar/Core.lean:51-59`, the same | identical |
| `UScalar ty`, `.bv`, `.val` | `HL/Scalar/Core.lean:82-87`, structure over `BitVec ty.numBits`, `val := bv.toNat` | `AE/Scalar/Core.lean:71-77`, the same | identical |
| `U8` … `U64`, `Usize` | `UScalar .U8` … | the same | identical |
| literals `k#u8` … `k#u64`, `k#usize` | `HL/Scalar/Notations.lean:38-43`, `U64.ofNat k (by first \| decide \| omega)` | `AE/Scalar/Notations.lean:24-29`, `… (by first \| decide \| scalar_tac)` | same term; the bound is discharged by a different tactic |
| `x + y` (`UScalar.add`) | `HL/Scalar/Ops.lean:49-50`, `tryMk ty (x.val + y.val)` | `AE/Scalar/Ops/Add.lean:16-17`, the same | `tryMk`: `ok` of the value when in bounds; vendored `fail panic`, upstream `fail integerOverflow` otherwise (`HL/Scalar/Core.lean:643-644`, `AE/Scalar/Core.lean:601-602`) |
| `x - y` (`UScalar.sub`) | `HL/Scalar/Ops.lean:203-205` | `AE/Scalar/Ops/Sub.lean:17-19` | same `ok`; `panic` against `integerOverflow` |
| `x * y` (`UScalar.mul`) | `HL/Scalar/Ops.lean:338-339` | `AE/Scalar/Ops/Mul.lean:18-19` | as `add` |
| `x / y` (`UScalar.div`) | `HL/Scalar/Ops.lean:470-471`, `BitVec.udiv` when `y.bv ≠ 0` | `AE/Scalar/Ops/Div.lean:17-18`, the same | same `ok`; `panic` against `divisionByZero` |
| `x % y` (`UScalar.rem`) | `HL/Scalar/Ops.lean:614-615`, `BitVec.umod` when `y.val ≠ 0` | `AE/Scalar/Ops/Rem.lean:16-17`, the same | same `ok`; `panic` against `divisionByZero` |
| `core.num.U64.wrapping_add`, `_sub`, `_mul` | `HL/Scalar/WrappingOps.lean:51`, `:117`, `:184`, `@UScalar.wrapping_* .U64`, `⟨x.bv ∘ y.bv⟩` (`:42`) | `AE/Scalar/WrappingOps/Add.lean:14`, `:26`; `Sub.lean:14`; `Mul.lean:14` | identical, pure, read through `lift` |
| `core.num.U64.wrapping_shl`, `_shr` | `HL/Scalar/WrappingOps.lean:242-243`, `:288-289`, `:256`, `:302`, `x.bv.shiftLeft (s.val % ty.numBits)` | `AE/Scalar/WrappingOps/Shl.lean:16-17`, `:30`; `Shr.lean:17`, `:31` | identical |
| `core.num.U64.rotate_left`, `_right` | `HL/Scalar/Rotate.lean:37-38`, `:41`, `:55`, `⟨x.bv.rotateLeft shift.val⟩`, `shift : U32` | `AE/Scalar/Rotate.lean:17-18`, `:22`, `:34` | identical |
| `x <<< s`, `x >>> s` (`HShiftLeft`, `HShiftRight` at any unsigned amount type) | `HL/Scalar/Bitwise.lean:41-51`, `:105`, `:117`, `ok ⟨x.bv.shiftLeft s⟩` when `s < numBits` | `AE/Scalar/Bitwise.lean:19-29`, `:83`, the same | same `ok`; `panic` against `integerOverflow` |
| `&&&`, `\|\|\|`, `^^^`, `~~~` | `HL/Scalar/Bitwise.lean:136-169`, `⟨x.bv op y.bv⟩` | `AE/Scalar/Bitwise.lean:110-153`, the same | identical, pure |
| `UScalar.cast tgt x` | `HL/Scalar/Casts.lean:36-38`, `⟨x.bv.zeroExtend tgt.numBits⟩` | `AE/Scalar/Casts.lean:20-22`, the same | identical |
| `UScalar.cast_fromBool` | `HL/Scalar/Casts.lean:56` | `AE/Scalar/Casts.lean:99` | identical |
| `<`, `<=`, `=`, `!=` on `UScalar` | `HL/Scalar/Core.lean:1001-1004` (`LT`, `LE` on `.val`), `:1063-1064` (decidable), `:1089` (`DecidableEq`) | `AE/Scalar/Core.lean:894-897`, `DecidableEq` derived (`:74`) | same propositions; equality decided through `bv` on both |
| `&&`, `\|\|`, `!` on `Bool` | Lean core | Lean core | identical |

## Arrays (row AE-2)

| name | vendored | upstream | comparison |
|---|---|---|---|
| `Array α n` | `HL/Array.lean:40`, subtype `{ l : List α // l.length = n.val }` | `AE/Array/Array.lean:28-30`, structure over `ListN α n.val`; `Array.val := list.toList` (`:33`) | representation differs; `val` and its length correspond |
| `Array.index_usize v i` | `HL/Array.lean:123-126`, `v[i]?`, `ok x` or `fail panic` | `AE/Array/Array.lean:159-162`, the same with `fail arrayOutOfBounds` | same `ok` |
| `Array.update v i x` | `HL/Array.lean:173-178`, `ok` of `v.val.set i.val x` in range | `AE/Array/Array.lean:266-270`, `ok (.from (v.val.set i.val x) _)` | same `val` of the `ok` value; `panic` against `arrayOutOfBounds` |
| `Array.index_mut_usize v i` | `HL/Array.lean:195-199`, `index_usize`, then `ok (x, set v i)` | `AE/Array/Array.lean:281-284`, the same | same `ok`; `Array.set` sets `val` on both (`HL/Array.lean:150`, `AE/Array/Array.lean:179-180`) |
| `Array.repeat n x` | `HL/Array.lean:129-130`, `List.replicate n.val x` | `AE/Array/Array.lean:166-167`, `.from (List.replicate n.val x) _` | same `val` |
| `Array.make n init` | `HL/Array.lean:67-68`, `⟨init, hl⟩` | `AE/Array/Array.lean:98-99`, `.from init hl` | same `val` |

## Loops (row AE-4)

| name | vendored | upstream | comparison |
|---|---|---|---|
| `ControlFlow`, `cont`, `done` | `HL/Primitives.lean:285-288` | `AE/Primitives.lean:464-467` | identical |
| `loop body x` | `HL/Primitives.lean:292-300`, a match on the flat `body x`, `partial_fixpoint` | `AE/Primitives.lean:469-474`, `bind (body x)` with the match on the `ControlFlow`, `partial_fixpoint` over the ITree order | same unfolding at `ok`: `ok (cont x')` continues at `x'`, `ok (done y)` returns `ok y`; the fixpoint orders differ (flat against coinductive) |
| `core.ops.range.Range`, `start`, `end` | `HL/Range.lean:35-38` | `AE/Range.lean:17-20` | identical |
| `core.iter.range.Step` | `HP:66-68`: `lt`, `forward_checked` | `AE/Core/Iter.lean:19-24`: `cloneInst`, `partialOrdInst`, `steps_between`, `forward_checked`, `backward_checked` | the prelude keeps the two fields `next` reads |
| `core.iter.range.UScalarStep.forward_checked` | `HP:71-75`, `some (start + n)` when `start.val + n.val < 2 ^ numBits` | `AE/Core/Iter.lean:256-261`, the same when `start.val + n.val ≤ UScalar.max ty` | same: `UScalar.max ty = 2 ^ numBits - 1` |
| `core.iter.range.StepUsize`, `StepU8` … `StepU64` | `HP:83-95`, `UScalarStep ty` (`StepU8` … `StepU64` added by this row) | `AE/Core/Iter.lean:379`, `:431`, `UScalarStep ty CloneTy PartialOrdTy` | `lt` is `ok (decide (a.val < b.val))` on both |
| `core.iter.range.IteratorRange.next` | `HP:99-108`, `lt`, then `forward_checked start 1`, `ok (some start, {range with start := n})` | `AE/Core/Iter.lean:592-604`, the same after `clone`, which is the identity on scalars | same `ok` values; `fail panic` when `forward_checked` returns `none` on both |

## Opaque callees (row AE-6)

An opaque function of the output is an `axiom` of the output file, not a `Std` name; the
reader abstracts it. Its signature uses only the types above.

## Not in the fragment

`U128`, `IScalar` arithmetic, `Slice`, `Vec`, structures, `core.iter` adapters (`step_by`,
`enumerate`, `zip`, slice iterators) and recursive `partial_fixpoint` definitions are
refused by the front (design, section 4) and are not compared here.

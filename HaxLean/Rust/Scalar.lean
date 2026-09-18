/-
Copyright (c) the Aeneas contributors. Licensed under the Apache License,
Version 2.0 (the "License"); you may not use this file except in compliance with
the License. You may obtain a copy of the License at
http://www.apache.org/licenses/LICENSE-2.0. Unless required by applicable law or
agreed to in writing, software distributed under the License is distributed on
an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and
limitations under the License.

Ported to Lean v4.33.1 without Mathlib by the CatCrypt Contributors.
Source: cryspen/aeneas at 6852e6474ec508930acba4df79977b3483a10d10,
  backends/lean/Aeneas/Std/Scalar.lean
-/

module

public import HaxLean.Rust.Scalar.Elab
public import HaxLean.Rust.Scalar.Core
public import HaxLean.Rust.Scalar.Misc
public import HaxLean.Rust.Scalar.Notations
public import HaxLean.Rust.Scalar.Ops
public import HaxLean.Rust.Scalar.Bitwise
public import HaxLean.Rust.Scalar.Casts
public import HaxLean.Rust.Scalar.WrappingOps
public import HaxLean.Rust.Scalar.Rotate
public import HaxLean.Rust.Scalar.CheckedOps
public import HaxLean.Rust.Scalar.OverflowingOps

/-!
# Machine integers

The unsigned and signed scalar types `u8`…`u128`, `usize`, `i8`…`i128`, `isize` over
`BitVec`, with checked, wrapping, overflowing, bitwise, shift, rotate and cast operations.
-/

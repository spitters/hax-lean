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
  backends/lean/Aeneas/Std.lean
-/

module

public import HaxLean.Rust.Primitives
public import HaxLean.Rust.WP
public import HaxLean.Rust.Core
public import HaxLean.Rust.Arith
public import HaxLean.Rust.Scalar
public import HaxLean.Rust.Data.List
public import HaxLean.Rust.RawPtr
public import HaxLean.Rust.Range
public import HaxLean.Rust.Array.Core
public import HaxLean.Rust.Slice
public import HaxLean.Rust.Array
public import HaxLean.Rust.Vec

/-!
# The Rust standard-library model of the Aeneas `Std` library

The `RustM` monad (`ok`, `fail` with `panic` or `undef`, `div`) with its weakest-precondition
interpretation, the machine-integer types, and `Array`, `Slice` and `alloc.vec.Vec`, under
the namespace `Aeneas.Std`. Names and signatures follow the Aeneas library; the modules
here depend on the Lean core library only.
-/

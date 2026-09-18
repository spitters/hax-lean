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
  backends/lean/Aeneas/Std/Scalar/Notations.lean
-/

module

public import HaxLean.Rust.Scalar.Core
public meta import Lean

/-!
# Scalar literals

`n#u32`, `n#i8`, … are the scalar literals of extracted code; `v#uscalar` and
`v#iscalar` are the constructor patterns.
-/

@[expose] public section

set_option autoImplicit false

namespace Aeneas

namespace Std

open Lean Meta Elab Term PrettyPrinter

macro:max x:term:max noWs "#u8"    : term => `(U8.ofNat $x (by first | decide | omega))
macro:max x:term:max noWs "#u16"   : term => `(U16.ofNat $x (by first | decide | omega))
macro:max x:term:max noWs "#u32"   : term => `(U32.ofNat $x (by first | decide | omega))
macro:max x:term:max noWs "#u64"   : term => `(U64.ofNat $x (by first | decide | omega))
macro:max x:term:max noWs "#u128"  : term => `(U128.ofNat $x (by first | decide | omega))
macro:max x:term:max noWs "#usize" : term => `(Usize.ofNat $x (by first | decide | omega))

macro:max x:term:max noWs "#i8"    : term => `(I8.ofInt $x (by first | decide | omega))
macro:max x:term:max noWs "#i16"   : term => `(I16.ofInt $x (by first | decide | omega))
macro:max x:term:max noWs "#i32"   : term => `(I32.ofInt $x (by first | decide | omega))
macro:max x:term:max noWs "#i64"   : term => `(I64.ofInt $x (by first | decide | omega))
macro:max x:term:max noWs "#i128"  : term => `(I128.ofInt $x (by first | decide | omega))
macro:max x:term:max noWs "#isize" : term => `(Isize.ofInt $x (by first | decide | omega))

@[app_unexpander U8.ofNat]
meta def unexpU8ofNat : Unexpander | `($_ $n $_) => `($n#u8) | _ => throw ()

@[app_unexpander U16.ofNat]
meta def unexpU16ofNat : Unexpander | `($_ $n $_) => `($n#u16) | _ => throw ()

@[app_unexpander U32.ofNat]
meta def unexpU32ofNat : Unexpander | `($_ $n $_) => `($n#u32) | _ => throw ()

@[app_unexpander U64.ofNat]
meta def unexpU64ofNat : Unexpander | `($_ $n $_) => `($n#u64) | _ => throw ()

@[app_unexpander U128.ofNat]
meta def unexpU128ofNat : Unexpander | `($_ $n $_) => `($n#u128) | _ => throw ()

@[app_unexpander Usize.ofNat]
meta def unexpUsizeofNat : Unexpander | `($_ $n $_) => `($n#usize) | _ => throw ()

@[app_unexpander I8.ofInt]
meta def unexpI8ofInt : Unexpander | `($_ $n $_) => `($n#i8) | _ => throw ()

@[app_unexpander I16.ofInt]
meta def unexpI16ofInt : Unexpander | `($_ $n $_) => `($n#i16) | _ => throw ()

@[app_unexpander I32.ofInt]
meta def unexpI32ofInt : Unexpander | `($_ $n $_) => `($n#i32) | _ => throw ()

@[app_unexpander I64.ofInt]
meta def unexpI64ofInt : Unexpander | `($_ $n $_) => `($n#i64) | _ => throw ()

@[app_unexpander I128.ofInt]
meta def unexpI128ofInt : Unexpander | `($_ $n $_) => `($n#i128) | _ => throw ()

@[app_unexpander Isize.ofInt]
meta def unexpIsizeofInt : Unexpander | `($_ $n $_) => `($n#isize) | _ => throw ()

/-- Pattern-matching notation for unsigned scalars. -/
notation:70 a:70 "#uscalar" => UScalar.mk (a)
/-- Pattern-matching notation for signed scalars. -/
notation:70 a:70 "#iscalar" => IScalar.mk (a)

example := 0#u32
example := (-1)#isize
example (x : U32) : Bool :=
  match x with
  | 0#uscalar => true
  | _ => false

end Std

end Aeneas

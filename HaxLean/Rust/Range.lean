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
  backends/lean/Aeneas/Std/Range.lean
-/

module

/-!
# Ranges

The `core::ops::range` structures used to index slices, arrays and vectors.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Aeneas

namespace Std

/-- `core::ops::range::Range` (`a..b`). -/
structure core.ops.range.Range (Idx : Type u) where
  mk ::
  start: Idx
  «end»: Idx

/-- `core::ops::range::RangeTo` (`..b`). -/
structure core.ops.range.RangeTo (Idx : Type u) where
  mk ::
  «end»: Idx

/-- `core::ops::range::RangeFull` (`..`): indexing a slice with it yields the whole slice. -/
@[reducible]
def core.ops.range.RangeFull := Unit

/-- `core::ops::range::RangeInclusive` (`a..=b`): the bounds and the `exhausted` flag,
set once `a..=a` has yielded its element. -/
structure core.ops.range.RangeInclusive (Idx : Type u) where
  mk ::
  start : Idx
  «end» : Idx
  exhausted : Bool

end Std

end Aeneas

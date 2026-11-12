/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import HaxLean.Range.Heads
public import HaxLean.Range.Heads

/-!
# Slices and facts through the addition of a constant in the range checker

Regression checks of `Hax.Range.check` with `Hax.Range.stdSpec`:

* a slice `s[2..6]` of an array of length 16 has length 4, so an index `3` into it is
  accepted and an index `4` refused; a slice `s[2..17]` is refused;
* a variable `x` with the fact `x + 1 < len s` gives `y = x + 1` the fact `y < len s`, so
  `s[y]` is accepted for an array of unknown length; `y = x + 2` is refused;
* `Hax.Range.refusal` names the refused call of the out-of-bounds slice index.
-/

set_option autoImplicit false

namespace HaxLean.Range.SliceTest

open Hax

/-- The standard specification without summaries, refining by Boolean guards. -/
abbrev spec : Range.Spec := Range.stdSpec [] [] true

/-- An array `s` of length 16. -/
def Γs : Range.AEnv := [("s", .arr (16, 16))]

/-- `let t = s[lo..hi]; t[k]`. -/
def sliceIdx (lo hi k : Int) : ImpExpr :=
  .letBind "t" (.app "index" [.var "s", .app "Range" [.lit (.int lo), .lit (.int hi)]])
    (.app "index" [.var "t", .lit (.int k)])

-- The slice `s[2..6]` has length 4: index 3 is accepted, index 4 refused.
#guard (Range.check spec [] Γs (sliceIdx 2 6 3)).isSome
#guard (Range.check spec [] Γs (sliceIdx 2 6 4)).isNone
-- A slice past the end of `s` is refused.
#guard (Range.check spec [] Γs (sliceIdx 2 17 0)).isNone

/-- An array `s` of unknown length and an index `x ∈ [0, 100]` with `x + 1 < len s`. -/
def Γx : Range.AEnv :=
  [("x", .idx 0 (some 100) [("s", 1)]), ("s", .arr (0, 2 ^ 64 - 1))]

/-- `let y = x + k; s[y]`. -/
def shiftIdx (k : Int) : ImpExpr :=
  .letBind "y" (.app "Add#size" [.var "x", .lit (.int k)]) (.app "index" [.var "s", .var "y"])

-- `y = x + 1` lies below `len s`; `y = x + 2` need not.
#guard (Range.check spec [] Γx (shiftIdx 1)).isSome
#guard (Range.check spec [] Γx (shiftIdx 2)).isNone

-- The refusal names the index into the slice.
#guard (Range.refusal spec [] Γs (sliceIdx 2 6 4)).any (·.startsWith "call index on")
#guard (Range.refusal spec [] Γs (sliceIdx 2 6 3)).isNone

end HaxLean.Range.SliceTest

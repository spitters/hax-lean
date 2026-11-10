/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.RangeProbe

/-!
# The entry point of `lake exe rangeprobe`

The executable that runs the interval inference of `HaxLean/RangeProbe.lean` over hax frontend
exports (`Hax.RangeProbe.run`).
-/

@[expose] public section

set_option autoImplicit false

/-- The entry point of `lake exe rangeprobe`. -/
def main (args : List String) : IO UInt32 :=
  Hax.RangeProbe.run args

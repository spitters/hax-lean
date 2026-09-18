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
  backends/lean/Aeneas/Tactic/Solver/Arith/Lemmas.lean
-/

module

/-!
# Balanced modulus on powers of two

`Int.bmod x (2 ^ n) = x` for `x` in the two's-complement range of width `n`.
-/

@[expose] public section

set_option autoImplicit false

namespace Aeneas.Arith

/-- `Int.bmod x (2 ^ (n + 1)) = x` for `x` in `[-2^n, 2^n)`. -/
theorem Int.bmod_pow2_eq_of_inBounds (n : Nat) (x : Int)
  (h0 : - 2 ^ n ≤ x)
  (h1 : x < 2 ^ n) :
  Int.bmod x (2 ^ (n + 1)) = x := by
  have hp : ((2 ^ (n + 1) : Nat) : Int) = 2 * (2 ^ n : Int) := by
    rw [Int.natCast_pow, Int.pow_succ]; simp [Int.mul_comm]
  apply _root_.Int.bmod_eq_of_le <;> rw [hp] <;> omega

/-- `Int.bmod x (2 ^ n) = x` for `n ≠ 0` and `x` in `[-2^(n-1), 2^(n-1))`. -/
theorem Int.bmod_pow2_eq_of_inBounds' (n : Nat) (x : Int)
  (hn : n ≠ 0)
  (h0 : - 2 ^ (n - 1) ≤ x)
  (h1 : x < 2 ^ (n - 1)) :
  Int.bmod x (2 ^ n) = x := by
  have h := Int.bmod_pow2_eq_of_inBounds (n - 1) x h0 h1
  have : n - 1 + 1 = n := by omega
  simpa [this] using h

end Aeneas.Arith

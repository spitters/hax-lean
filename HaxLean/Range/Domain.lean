/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module


/-!
# The interval domain of a lane-wise range analysis

An integer interval `i = (lo, hi)` bounds a `w`-bit word `x` when `x` is the residue
mod `2^w` of some integer in `[lo, hi]` (`Iv.Mem`). The interval may reach below zero or
past `2^w`, so a subtraction that wraps keeps an exact bound. The lane interval
`ivLane w i` is the shift of `i` into `[0, 2^w)` when `i` meets one multiple of `2^w`
only, and the full lane range otherwise; it bounds `x.toNat` itself.

The module is independent of any IR: its statements are over `BitVec w` and its
operations, so an analysis over any word-level IR instantiates it. It imports no Mathlib, so
that the range checker of the typed extraction (`HaxLean/Range/Check.lean`) and the compiler
share it; the compiler module `CatCrypt.Crypto.SecureCompilation.RangeDomain` re-exports it, and
the declarations keep that module's namespace.

## Main definitions

* `Iv`, `Iv.Mem`, `ivTop`, `ivNorm`, `ivLane`, `ivConst`, `ivSingle?`: the domain.
* `ivAdd`, `ivSub`, `ivMul`, `ivAnd`, `ivShr`, `ivShl`, `ivMulhi`, `ivCast`: the
  transfer functions.
* `condAdd`, `umin`, `ivCondAdd?`: the conditional add `d + ((0 - (d >>> (w-1))) &&& C)`
  and its range.
* `barrettBound`, `ivBarrett?`: the range of the Barrett remainder.
* `ivSTop`, `ivSFits`, `ivSar`, `ivCenter`, `ivCorner`, `ivMulS`, `ivNarrow`, `ivHull`,
  `ivShlExt`: the signed transfer functions (arithmetic shift as floor division, the
  corner product, the narrower of two intervals, the hull, and the left shift of a zero
  extension).

* `Iv.Has`, `ivLe`, `ivMeet`, `ivAddZ`, `ivSubZ`, `ivPoint`: exact integer membership and
  the exact transfer functions of checked arithmetic.
* `two_pow_pos_int`, `two_pow_ne_zero_int`, `two_pow_dvd_int`: the facts about `2^w` in the
  integers that the proofs use.

## Main results

* `Iv.mem_lane`: a member of `i` has its `toNat` in the lane interval;
  `Iv.toNat_eq_of_single`: a one-point lane interval fixes `toNat`.
* `Iv.mem_add`, `Iv.mem_sub`, `Iv.mem_mul`, `Iv.mem_and`, `Iv.mem_shr`, `Iv.mem_shl`,
  `Iv.mem_mulhi`, `Iv.mem_cast`, `Iv.mem_const`: soundness of the transfer functions.
* `Iv.mem_condAdd`, `Iv.mem_ivCondAdd`: soundness of the conditional-add rule.
* `condAdd_eq_umin`, `condAdd_sub_eq_umin`: the conditional add of a constant is the
  unsigned minimum of `d` and `d + C`, and of `x` and `x - C` when `d = x - C`.
* `barrett_nat`, `Iv.mem_barrett_toNat`, `Iv.mem_barrett`, `Iv.mem_ivBarrett`: the
  Barrett remainder lies in
  `[0, min X (X·δ/2^(s+t) + p·m/2^t + p + 1)]`, `δ = 2^(s+t) - m·p`.
* `mul_eq_mul_setWidth32`: a 64-bit product of operands below `2^32` is the product of
  their zero-extended low halves.
* `extractLsb'_sub_of_setWidth_eq`: the high half of a 64-bit difference of words with
  equal low halves is the difference of their high halves.
* `Iv.mem_sar`, `Iv.mem_mulS`, `Iv.mem_narrow`, `Iv.mem_hull_left`, `Iv.mem_hull_right`,
  `Iv.mem_trunc`, `Iv.mem_shlExt`: soundness of the signed transfer functions;
  `Iv.toInt_of_mem_sFits`: a member of an interval in the signed lane has its signed value
  in the interval.
* `Iv.Has.le`, `Iv.Has.meet`, `Iv.Has.hull_left`, `Iv.Has.hull_right`, `Iv.Has.add`,
  `Iv.Has.sub`, `Iv.Has.mul`: the exact integer membership `Iv.Has` under inclusion,
  intersection, hull and the exact arithmetic `ivAddZ`, `ivSubZ`, `ivCorner`;
  `Iv.mem_of_has`, `Iv.Mem.has_lane`: its relation to `Iv.Mem`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RangeDomain

/-- `2^w` is a positive integer. -/
theorem two_pow_pos_int (w : Nat) : (0 : Int) < 2 ^ w := by
  have := Nat.two_pow_pos w
  exact_mod_cast this

/-- `2^m` divides `2^n` in the integers when `m ≤ n`. -/
theorem two_pow_dvd_int {m n : Nat} (h : m ≤ n) : (2 : Int) ^ m ∣ 2 ^ n := by
  have := Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 h)
  exact_mod_cast this

/-- `2^w` is a nonzero integer. -/
theorem two_pow_ne_zero_int (w : Nat) : (2 : Int) ^ w ≠ 0 :=
  Int.ne_of_gt (two_pow_pos_int w)

/-! ## 1. The domain -/

/-- An integer interval `[lo, hi]`. -/
abbrev Iv := Int × Int

/-- `x` is the residue mod `2^w` of an integer in `[i.1, i.2]`. -/
def Iv.Mem (w : Nat) (i : Iv) (x : BitVec w) : Prop :=
  ∃ v : Int, i.1 ≤ v ∧ v ≤ i.2 ∧ v % 2 ^ w = (x.toNat : Int)

/-- The full lane range `[0, 2^w - 1]`. -/
def ivTop (w : Nat) : Iv := (0, 2 ^ w - 1)

/-- `i` when it spans fewer than `2^w` integers, else the full lane range. -/
def ivNorm (w : Nat) (i : Iv) : Iv :=
  if i.2 - i.1 < 2 ^ w then i else ivTop w

/-- The lane values of `i`: its shift into `[0, 2^w)` when `i` meets one multiple of
    `2^w` only, else the full lane range. -/
def ivLane (w : Nat) (i : Iv) : Iv :=
  if i.2 / 2 ^ w = i.1 / 2 ^ w then
    (i.1 - i.1 / 2 ^ w * 2 ^ w, i.2 - i.1 / 2 ^ w * 2 ^ w)
  else ivTop w

/-- The interval of the constant `BitVec.ofNat w n`. -/
def ivConst (w n : Nat) : Iv := (((n % 2 ^ w : Nat) : Int), ((n % 2 ^ w : Nat) : Int))

/-- The value of a one-point interval `[k, k]` with `0 ≤ k`. -/
def ivSingle? (i : Iv) : Option Nat :=
  if 0 ≤ i.1 ∧ i.1 = i.2 then some i.1.toNat else none

namespace Iv

variable {w : Nat}

theorem mem_iff_ofInt (i : Iv) (x : BitVec w) :
    i.Mem w x ↔ ∃ v : Int, i.1 ≤ v ∧ v ≤ i.2 ∧ BitVec.ofInt w v = x := by
  have key : ∀ v : Int, v % 2 ^ w = (x.toNat : Int) ↔ BitVec.ofInt w v = x := by
    intro v
    constructor
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofInt]; push_cast; rw [h]; simp
    · intro h
      subst h
      rw [BitVec.toNat_ofInt]
      push_cast
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (two_pow_ne_zero_int _))]
  unfold Iv.Mem
  constructor
  · rintro ⟨v, h1, h2, h3⟩; exact ⟨v, h1, h2, (key v).1 h3⟩
  · rintro ⟨v, h1, h2, h3⟩; exact ⟨v, h1, h2, (key v).2 h3⟩

/-- A natural-number witness: `x` is `n mod 2^w` for `n` in `i`. -/
theorem mem_of_nat {i : Iv} {x : BitVec w} (n : Nat) (h1 : i.1 ≤ (n : Int))
    (h2 : (n : Int) ≤ i.2) (hx : x.toNat = n % 2 ^ w) : i.Mem w x :=
  ⟨n, h1, h2, by rw [hx]; push_cast; rfl⟩

theorem mem_of_bounds {i : Iv} {x : BitVec w} (h1 : i.1 ≤ (x.toNat : Int))
    (h2 : (x.toNat : Int) ≤ i.2) : i.Mem w x :=
  mem_of_nat x.toNat h1 h2 (Nat.mod_eq_of_lt x.isLt).symm

theorem toNat_lt_int (x : BitVec w) : (x.toNat : Int) < 2 ^ w := by
  exact_mod_cast x.isLt

theorem mem_top (x : BitVec w) : (ivTop w).Mem w x :=
  mem_of_bounds (by simp [ivTop]) (by have := toNat_lt_int x; simp only [ivTop]; omega)

theorem Mem.norm {i : Iv} {x : BitVec w} (h : i.Mem w x) : (ivNorm w i).Mem w x := by
  unfold ivNorm; split
  · exact h
  · exact mem_top x

/-- A member of `i` has its `toNat` in the lane interval of `i`. -/
theorem mem_lane {i : Iv} {x : BitVec w} (h : i.Mem w x) :
    (ivLane w i).1 ≤ (x.toNat : Int) ∧ (x.toNat : Int) ≤ (ivLane w i).2 := by
  obtain ⟨v, h1, h2, hv⟩ := h
  have hM : (0 : Int) < 2 ^ w := two_pow_pos_int _
  unfold ivLane
  split
  · rename_i hk
    have e1 : i.1 / 2 ^ w ≤ v / 2 ^ w := Int.ediv_le_ediv hM h1
    have e2 : v / 2 ^ w ≤ i.2 / 2 ^ w := Int.ediv_le_ediv hM h2
    have hq : v / 2 ^ w = i.1 / 2 ^ w := by omega
    have hd := Int.emod_def v (2 ^ w)
    rw [hq] at hd
    constructor
    · show i.1 - i.1 / 2 ^ w * 2 ^ w ≤ _
      rw [← hv, hd, Int.mul_comm (2 ^ w)]; omega
    · show _ ≤ i.2 - i.1 / 2 ^ w * 2 ^ w
      rw [← hv, hd, Int.mul_comm (2 ^ w)]; omega
  · have := toNat_lt_int x
    simp only [ivTop]; omega

theorem lane_fst_nonneg (i : Iv) : 0 ≤ (ivLane w i).1 := by
  unfold ivLane
  split
  · show 0 ≤ i.1 - i.1 / 2 ^ w * 2 ^ w
    have := Int.ediv_mul_le i.1 (b := 2 ^ w) (two_pow_ne_zero_int _)
    omega
  · simp [ivTop]

/-- The lane interval as an interval of members. -/
theorem Mem.lane {i : Iv} {x : BitVec w} (h : i.Mem w x) : (ivLane w i).Mem w x :=
  mem_of_bounds (mem_lane h).1 (mem_lane h).2

/-- A member of `i` whose lane interval is the point `k` has `toNat = k`. -/
theorem toNat_eq_of_single {i : Iv} {x : BitVec w} {k : Nat} (h : i.Mem w x)
    (hk : ivSingle? (ivLane w i) = some k) : x.toNat = k := by
  obtain ⟨h1, h2⟩ := mem_lane h
  unfold ivSingle? at hk
  split at hk
  · rename_i hc
    obtain ⟨hc1, hc2⟩ := hc
    cases hk
    omega
  · cases hk

end Iv

/-! ## 2. Transfer functions -/

/-- The interval of a sum. -/
def ivAdd (w : Nat) (a b : Iv) : Iv :=
  ivNorm w (a.1 + b.1, a.2 + b.2)

/-- The interval of a difference. -/
def ivSub (w : Nat) (a b : Iv) : Iv :=
  ivNorm w (a.1 - b.2, a.2 - b.1)

/-- The interval of a low product, from the lane intervals. -/
def ivMul (w : Nat) (a b : Iv) : Iv :=
  ivNorm w ((ivLane w a).1 * (ivLane w b).1, (ivLane w a).2 * (ivLane w b).2)

/-- The interval of a bitwise `and`. -/
def ivAnd (w : Nat) (a b : Iv) : Iv :=
  (0, min (ivLane w a).2 (ivLane w b).2)

/-- The interval of a logical right shift by `k`. A count of at least `w` gives 0 (the
    shift is by the count's value, as `JasminBinOp.shr` is), and no power `2^k` is formed. -/
def ivShr (w : Nat) (a : Iv) (k : Nat) : Iv :=
  if w ≤ k then (0, 0) else ((ivLane w a).1 / 2 ^ k, (ivLane w a).2 / 2 ^ k)

/-- The interval of a left shift by `k`; a count of at least `w` gives 0. -/
def ivShl (w : Nat) (a : Iv) (k : Nat) : Iv :=
  if w ≤ k then (0, 0) else ivNorm w ((ivLane w a).1 * 2 ^ k, (ivLane w a).2 * 2 ^ k)

/-- The interval of the high multiply `(a·b) / 2^w`. -/
def ivMulhi (w : Nat) (a b : Iv) : Iv :=
  ((ivLane w a).1 * (ivLane w b).1 / 2 ^ w, (ivLane w a).2 * (ivLane w b).2 / 2 ^ w)

/-- The interval of the zero-extension or truncation to `w'` bits. -/
def ivCast (w w' : Nat) (a : Iv) : Iv :=
  if (ivLane w a).2 < 2 ^ w' then ivLane w a else ivTop w'

namespace Iv

variable {w : Nat} {a b : Iv} {x y : BitVec w}

theorem mem_const (n : Nat) : (ivConst w n).Mem w (BitVec.ofNat w n) :=
  mem_of_bounds (by simp [ivConst]) (by simp [ivConst])

theorem mem_add (ha : a.Mem w x) (hb : b.Mem w y) : (ivAdd w a b).Mem w (x + y) := by
  apply Mem.norm
  rw [mem_iff_ofInt] at ha hb ⊢
  obtain ⟨u, hu1, hu2, rfl⟩ := ha
  obtain ⟨v, hv1, hv2, rfl⟩ := hb
  exact ⟨u + v, by simp only; omega, by simp only; omega, BitVec.ofInt_add u v⟩

theorem mem_sub (ha : a.Mem w x) (hb : b.Mem w y) : (ivSub w a b).Mem w (x - y) := by
  apply Mem.norm
  rw [mem_iff_ofInt] at ha hb ⊢
  obtain ⟨u, hu1, hu2, rfl⟩ := ha
  obtain ⟨v, hv1, hv2, rfl⟩ := hb
  refine ⟨u - v, by simp only; omega, by simp only; omega, ?_⟩
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem mem_mul (ha : a.Mem w x) (hb : b.Mem w y) : (ivMul w a b).Mem w (x * y) := by
  apply Mem.norm
  obtain ⟨ha1, ha2⟩ := mem_lane ha
  obtain ⟨hb1, hb2⟩ := mem_lane hb
  have h0a := lane_fst_nonneg (w := w) a
  have h0b := lane_fst_nonneg (w := w) b
  refine mem_of_nat (x.toNat * y.toNat) ?_ ?_ (BitVec.toNat_mul x y)
  · push_cast; exact Int.mul_le_mul ha1 hb1 h0b (by omega)
  · push_cast; exact Int.mul_le_mul ha2 hb2 (by omega) (by omega)

theorem mem_and (ha : a.Mem w x) (hb : b.Mem w y) : (ivAnd w a b).Mem w (x &&& y) := by
  have h1 := (mem_lane ha).2
  have h2 := (mem_lane hb).2
  refine mem_of_bounds (by simp [ivAnd]) ?_
  rw [BitVec.toNat_and]
  have e1 : x.toNat &&& y.toNat ≤ x.toNat := Nat.and_le_left
  have e2 : x.toNat &&& y.toNat ≤ y.toNat := Nat.and_le_right
  simp only [ivAnd, Int.le_min]
  constructor <;> omega

theorem mem_shr (ha : a.Mem w x) (k : Nat) : (ivShr w a k).Mem w (x >>> k) := by
  unfold ivShr
  split
  · rename_i hk
    have h0 : (x >>> k).toNat = 0 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hk))
    exact mem_of_bounds (by simp [h0]) (by simp [h0])
  obtain ⟨h1, h2⟩ := mem_lane ha
  have hk : (0 : Int) < 2 ^ k := two_pow_pos_int _
  refine mem_of_bounds ?_ ?_
  · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; push_cast
    exact Int.ediv_le_ediv hk h1
  · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; push_cast
    exact Int.ediv_le_ediv hk h2

theorem mem_shl (ha : a.Mem w x) (k : Nat) : (ivShl w a k).Mem w (x <<< k) := by
  unfold ivShl
  split
  · rename_i hk
    have h0 : (x <<< k).toNat = 0 := by
      rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 hk) _)
    exact mem_of_bounds (by simp [h0]) (by simp [h0])
  apply Mem.norm
  obtain ⟨h1, h2⟩ := mem_lane ha
  have hk : (0 : Int) ≤ 2 ^ k := Int.le_of_lt (two_pow_pos_int _)
  refine mem_of_nat (x.toNat * 2 ^ k) ?_ ?_ ?_
  · push_cast; exact Int.mul_le_mul_of_nonneg_right h1 hk
  · push_cast; exact Int.mul_le_mul_of_nonneg_right h2 hk
  · rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem mem_mulhi (ha : a.Mem w x) (hb : b.Mem w y) :
    (ivMulhi w a b).Mem w (BitVec.ofNat w (x.toNat * y.toNat / 2 ^ w)) := by
  obtain ⟨ha1, ha2⟩ := mem_lane ha
  obtain ⟨hb1, hb2⟩ := mem_lane hb
  have h0a := lane_fst_nonneg (w := w) a
  have h0b := lane_fst_nonneg (w := w) b
  have hM : (0 : Int) < 2 ^ w := two_pow_pos_int _
  refine mem_of_nat (x.toNat * y.toNat / 2 ^ w) ?_ ?_ (BitVec.toNat_ofNat _ _)
  · push_cast
    exact Int.ediv_le_ediv hM (Int.mul_le_mul ha1 hb1 h0b (by omega))
  · push_cast
    exact Int.ediv_le_ediv hM (Int.mul_le_mul ha2 hb2 (by omega) (by omega))

theorem mem_cast {w' : Nat} (ha : a.Mem w x) : (ivCast w w' a).Mem w' (x.setWidth w') := by
  obtain ⟨h1, h2⟩ := mem_lane ha
  unfold ivCast
  split
  · rename_i hlt
    have hx : x.toNat < 2 ^ w' := by
      have : (x.toNat : Int) < 2 ^ w' := by omega
      exact_mod_cast this
    refine mem_of_bounds ?_ ?_ <;> rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx] <;> assumption
  · exact mem_top _

end Iv

/-! ## 3. The conditional add -/

/-- The conditional add of `C`: `d + C` when the top bit of `d` is set, else `d`. -/
def condAdd {w : Nat} (d C : BitVec w) : BitVec w :=
  d + ((0 - (d >>> (w - 1))) &&& C)

/-- The unsigned minimum. -/
def umin {w : Nat} (a b : BitVec w) : BitVec w :=
  if a.toNat ≤ b.toNat then a else b

theorem umin_comm {w : Nat} (a b : BitVec w) : umin a b = umin b a := by
  unfold umin
  split <;> split
  · exact BitVec.eq_of_toNat_eq (by omega)
  · rfl
  · rfl
  · exact absurd (by omega : a.toNat ≤ b.toNat) ‹_›

theorem two_pow_eq {w : Nat} (hw : 0 < w) : 2 ^ w = 2 * 2 ^ (w - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]

theorem condAdd_of_lt {w : Nat} (d C : BitVec w) (h : d.toNat < 2 ^ (w - 1)) :
    condAdd d C = d := by
  have hs : d >>> (w - 1) = 0#w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]
    simp
  simp [condAdd, hs]

theorem condAdd_of_ge {w : Nat} (hw : 0 < w) (d C : BitVec w) (h : 2 ^ (w - 1) ≤ d.toNat) :
    condAdd d C = d + C := by
  have hM := two_pow_eq hw
  have hd := d.isLt
  have hs : d >>> (w - 1) = 1#w := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
    simp only [BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  simp [condAdd, hs, BitVec.zero_sub, BitVec.neg_one_eq_allOnes, BitVec.allOnes_and]

/-- The two cases of a member `d` of `id` with `-C ≤ id.1` and `id.2 < 2^(w-1)`: `d` is
    an integer `v ∈ [0, 2^(w-1))`, or `d = v + 2^w` for `v ∈ [-C, 0)`. -/
theorem condAdd_cases {w : Nat} (hw : 0 < w) {id : Iv} {d : BitVec w} (c : Int)
    (hd : id.Mem w d) (hlo : -c ≤ id.1) (hhi : id.2 < 2 ^ (w - 1)) (hc : c < 2 ^ (w - 1)) :
    ∃ v : Int, id.1 ≤ v ∧ v ≤ id.2 ∧
      ((0 ≤ v ∧ (d.toNat : Int) = v) ∨ (v < 0 ∧ (d.toNat : Int) = v + 2 ^ w)) := by
  obtain ⟨v, h1, h2, hv⟩ := hd
  have hM : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by exact_mod_cast two_pow_eq hw
  refine ⟨v, h1, h2, ?_⟩
  rcases (show 0 ≤ v ∨ v < 0 by omega) with h0 | h0
  · left
    refine ⟨h0, ?_⟩
    rw [← hv, Int.emod_eq_of_lt h0 (by omega)]
  · right
    refine ⟨h0, ?_⟩
    rw [← hv, ← Int.add_mul_emod_self_right v 1 (2 ^ w), Int.one_mul,
      Int.emod_eq_of_lt (by omega) (by omega)]

variable {w : Nat}

/-- The range of the conditional add for `d ∈ id` and the lanes of `C` in `ic`. -/
def condAddIv (id ic : Iv) : Iv :=
  if 0 ≤ id.1 then id else (0, max id.2 (ic.2 - 1))

/-- The range of the conditional add, when the sign test reads the sign of `d`:
    `ic.2 < 2^(w-1)`, `-ic.1 ≤ id.1`, `id.2 < 2^(w-1)`. -/
def ivCondAdd? (w : Nat) (id ic : Iv) : Option Iv :=
  if 0 < w ∧ ic.2 < 2 ^ (w - 1) ∧ -ic.1 ≤ id.1 ∧ id.2 < 2 ^ (w - 1) then
    some (condAddIv id ic)
  else none

theorem Iv.mem_condAdd (hw : 0 < w) {id ic : Iv} {d C : BitVec w} (hd : id.Mem w d)
    (hC1 : ic.1 ≤ (C.toNat : Int)) (hC2 : (C.toNat : Int) ≤ ic.2)
    (hc : ic.2 < 2 ^ (w - 1)) (hlo : -ic.1 ≤ id.1) (hhi : id.2 < 2 ^ (w - 1)) :
    (condAddIv id ic).Mem w (condAdd d C) := by
  have hM : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by exact_mod_cast two_pow_eq hw
  obtain ⟨v, h1, h2, hcase⟩ := condAdd_cases hw ic.1 hd hlo hhi (by omega)
  rcases hcase with ⟨h0, hv⟩ | ⟨h0, hv⟩
  · have hlt : d.toNat < 2 ^ (w - 1) := by
      have : (d.toNat : Int) < 2 ^ (w - 1) := by omega
      exact_mod_cast this
    rw [condAdd_of_lt d C hlt]
    unfold condAddIv
    split
    · exact Iv.mem_of_bounds (by omega) (by omega)
    · exact Iv.mem_of_bounds (by simp only; omega) (by simp only; omega)
  · have hge : 2 ^ (w - 1) ≤ d.toNat := by
      have : (2 : Int) ^ (w - 1) ≤ d.toNat := by omega
      exact_mod_cast this
    rw [condAdd_of_ge hw d C hge]
    have hidneg : ¬ 0 ≤ id.1 := by omega
    simp only [condAddIv, hidneg, ite_false]
    have hlt : d.toNat + C.toNat - 2 ^ w < 2 ^ w := by
      have := d.isLt; have := C.isLt; omega
    have hsum : (d + C).toNat = d.toNat + C.toNat - 2 ^ w := by
      rw [BitVec.toNat_add]
      have hge' : 2 ^ w ≤ d.toNat + C.toNat := by
        have : (2 : Int) ^ w ≤ d.toNat + C.toNat := by omega
        exact_mod_cast this
      rw [← Nat.mod_eq_of_lt hlt, Nat.mod_eq_sub_mod hge']
    have hcast : ((d + C).toNat : Int) = v + C.toNat := by
      rw [hsum]
      have hge' : 2 ^ w ≤ d.toNat + C.toNat := by
        have : (2 : Int) ^ w ≤ d.toNat + C.toNat := by omega
        exact_mod_cast this
      push_cast [hge']
      omega
    exact Iv.mem_of_bounds (by simp only; omega) (by simp only; omega)

/-- `ivCondAdd?` is sound: its interval holds the conditional add of a member of `id` and
    a constant whose `toNat` lies in `ic`. -/
theorem Iv.mem_ivCondAdd {id ic r : Iv} {d C : BitVec w} (hd : id.Mem w d)
    (hC1 : ic.1 ≤ (C.toNat : Int)) (hC2 : (C.toNat : Int) ≤ ic.2)
    (hr : ivCondAdd? w id ic = some r) : r.Mem w (condAdd d C) := by
  unfold ivCondAdd? at hr
  split at hr
  · rename_i hc
    obtain ⟨hw, h1, h2, h3⟩ := hc
    cases hr
    exact Iv.mem_condAdd hw hd hC1 hC2 h1 h2 h3
  · cases hr

/-- The conditional add of a constant `C < 2^(w-1)` on `d ∈ [-C, 2^(w-1))` is the
    unsigned minimum of `d` and `d + C`. -/
theorem condAdd_eq_umin (hw : 0 < w) {id : Iv} {d C : BitVec w} (hd : id.Mem w d)
    (hc : C.toNat < 2 ^ (w - 1)) (hlo : -(C.toNat : Int) ≤ id.1)
    (hhi : id.2 < 2 ^ (w - 1)) :
    condAdd d C = umin d (d + C) := by
  have hM : (2 : Int) ^ w = 2 * 2 ^ (w - 1) := by exact_mod_cast two_pow_eq hw
  have hMn := two_pow_eq hw
  have hcI : (C.toNat : Int) < 2 ^ (w - 1) := by exact_mod_cast hc
  obtain ⟨v, h1, h2, hcase⟩ := condAdd_cases hw C.toNat hd hlo hhi hcI
  rcases hcase with ⟨h0, hv⟩ | ⟨h0, hv⟩
  · have hlt : d.toNat < 2 ^ (w - 1) := by
      have : (d.toNat : Int) < 2 ^ (w - 1) := by omega
      exact_mod_cast this
    rw [condAdd_of_lt d C hlt]
    have hsum : (d + C).toNat = d.toNat + C.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    unfold umin
    rw [ite_eq_left (by omega)]
  · have hge : 2 ^ (w - 1) ≤ d.toNat := by
      have : (2 : Int) ^ (w - 1) ≤ d.toNat := by omega
      exact_mod_cast this
    have hge' : 2 ^ w ≤ d.toNat + C.toNat := by
      have : (2 : Int) ^ w ≤ d.toNat + C.toNat := by omega
      exact_mod_cast this
    rw [condAdd_of_ge hw d C hge]
    have hsum : (d + C).toNat = d.toNat + C.toNat - 2 ^ w := by
      rw [BitVec.toNat_add, Nat.mod_eq_sub_mod hge', Nat.mod_eq_of_lt]
      have := d.isLt; have := C.isLt; omega
    unfold umin
    rw [ite_eq_right (by have := C.isLt; omega)]

/-- The direct form: for `d = x - C` in range, the conditional add is the unsigned
    minimum of `x` and `x - C`. -/
theorem condAdd_sub_eq_umin (hw : 0 < w) {id : Iv} {x C : BitVec w} (hd : id.Mem w (x - C))
    (hc : C.toNat < 2 ^ (w - 1)) (hlo : -(C.toNat : Int) ≤ id.1)
    (hhi : id.2 < 2 ^ (w - 1)) :
    condAdd (x - C) C = umin x (x - C) := by
  rw [condAdd_eq_umin hw hd hc hlo hhi, BitVec.sub_add_cancel, umin_comm]

/-! ## 4. The Barrett remainder -/

/-- The Barrett bound `X·δ/2^(s+t) + p·m/2^t + p + 1`, `δ = 2^(s+t) - m·p`. -/
def barrettBound (X s t m p : Nat) : Nat :=
  X * (2 ^ (s + t) - m * p) / 2 ^ (s + t) + p * m / 2 ^ t + p + 1

/-- The Barrett quotient `q = ⌊⌊x/2^s⌋·m/2^t⌋` satisfies `q·p ≤ x`, and the remainder
    `x - q·p` is at most `min X (barrettBound X s t m p)` for `x ≤ X`, when
    `m·p ≤ 2^(s+t)`. -/
theorem barrett_nat (x X s t m p : Nat) (hx : x ≤ X) (hmp : m * p ≤ 2 ^ (s + t)) :
    x / 2 ^ s * m / 2 ^ t * p ≤ x ∧
      x - x / 2 ^ s * m / 2 ^ t * p ≤ min X (barrettBound X s t m p) := by
  have hS : 0 < 2 ^ s := Nat.two_pow_pos s
  have hT : 0 < 2 ^ t := Nat.two_pow_pos t
  rw [Nat.pow_add] at hmp
  unfold barrettBound
  rw [Nat.pow_add]
  generalize 2 ^ s = S at *
  generalize 2 ^ t = T at *
  have f1 : x / S * S ≤ x := Nat.div_mul_le_self x S
  have f1' : x < x / S * S + S := Nat.lt_div_mul_add hS
  generalize x / S = h at *
  have f2 : h * m / T * T ≤ h * m := Nat.div_mul_le_self (h * m) T
  have f2' : h * m < h * m / T * T + T := Nat.lt_div_mul_add hT
  generalize h * m / T = q at *
  have hlow : q * p ≤ x := by
    have e1 : q * T * p ≤ h * m * p := Nat.mul_le_mul_right p f2
    have e2 : h * (m * p) ≤ h * (S * T) := Nat.mul_le_mul_left h hmp
    have e3 : q * p * T ≤ x * T := by
      have : h * S * T ≤ x * T := Nat.mul_le_mul_right T f1
      calc q * p * T = q * T * p := Nat.mul_right_comm q p T
        _ ≤ h * m * p := e1
        _ = h * (m * p) := Nat.mul_assoc h m p
        _ ≤ h * (S * T) := e2
        _ = h * S * T := (Nat.mul_assoc h S T).symm
        _ ≤ x * T := this
    exact Nat.le_of_mul_le_mul_right e3 hT
  refine ⟨hlow, ?_⟩
  refine Nat.le_min.2 ⟨by omega, ?_⟩
  have hδ' : (S * T - m * p) + m * p = S * T := by omega
  generalize S * T - m * p = δ at *
  have f3 : X * δ < X * δ / (S * T) * (S * T) + S * T :=
    Nat.lt_div_mul_add (Nat.mul_pos hS hT)
  have f4 : p * m < p * m / T * T + T := Nat.lt_div_mul_add hT
  generalize X * δ / (S * T) = A at *
  generalize p * m / T = B at *
  have g1 : x * δ ≤ X * δ := Nat.mul_le_mul_right δ hx
  -- `x·m·p + m·p ≤ (h+1)·S·m·p`
  have g2 : (x + 1) * (m * p) ≤ (h * S + S) * (m * p) := Nat.mul_le_mul_right _ f1'
  -- `(h·m + 1)·p ≤ (q·T + T)·p`, scaled by `S`
  have g3 : (h * m + 1) * p * S ≤ (q * T + T) * p * S :=
    Nat.mul_le_mul_right S (Nat.mul_le_mul_right p f2')
  -- `(p·m + 1)·S ≤ (B·T + T)·S`
  have g4 : (p * m + 1) * S ≤ (B * T + T) * S := Nat.mul_le_mul_right S f4
  have key : x * (S * T) < (q * p + A + B + p + 2) * (S * T) := by
    have e : x * (S * T) = x * δ + x * (m * p) := by rw [← hδ', Nat.mul_add]
    rw [e]
    grind
  have := Nat.lt_of_mul_lt_mul_right key
  omega

/-- The range of the Barrett remainder for `x ∈ ix`, when `ix` lies in `[0, 2^w)`. -/
def ivBarrett? (w : Nat) (ix : Iv) (s t m p : Nat) : Option Iv :=
  if 0 ≤ ix.1 ∧ ix.2 < 2 ^ w ∧ m * p ≤ 2 ^ (s + t) then
    some (0, ((min ix.2.toNat (barrettBound ix.2.toNat s t m p) : Nat) : Int))
  else none

/-- The Barrett remainder `x - ((((x >>> s) * M) >>> t) * P)` with no wrapping product
    lies in `[0, min X (barrettBound X s t m p)]` for `x ≤ X`, `m = M.toNat`,
    `p = P.toNat`. -/
theorem Iv.mem_barrett_toNat {x y : BitVec w} {s t m p X : Nat} (hx : x.toNat ≤ X)
    (hmp : m * p ≤ 2 ^ (s + t)) (hy : y.toNat = x.toNat / 2 ^ s * m / 2 ^ t * p) :
    Iv.Mem w (0, ((min X (barrettBound X s t m p) : Nat) : Int)) (x - y) := by
  obtain ⟨hl, hu⟩ := barrett_nat x.toNat X s t m p hx hmp
  have hle : y ≤ x := by
    rw [BitVec.le_def, hy]; exact hl
  refine Iv.mem_of_bounds (Int.natCast_nonneg _) ?_
  show _ ≤ ((min X (barrettBound X s t m p) : Nat) : Int)
  rw [BitVec.toNat_sub_of_le hle, hy]
  exact_mod_cast hu

/-- The Barrett remainder `x - ((((x >>> s) * M) >>> t) * P)` with no wrapping product
    lies in `[0, min X (barrettBound X s t m p)]` for `x ≤ X`, `m = M.toNat`,
    `p = P.toNat`. -/
theorem Iv.mem_barrett {x M P : BitVec w} (s t X : Nat) (hx : x.toNat ≤ X)
    (hmp : M.toNat * P.toNat ≤ 2 ^ (s + t)) (hg : x.toNat / 2 ^ s * M.toNat < 2 ^ w)
    (hy : x.toNat / 2 ^ s * M.toNat / 2 ^ t * P.toNat < 2 ^ w) :
    Iv.Mem w (0, ((min X (barrettBound X s t M.toNat P.toNat) : Nat) : Int))
      (x - (((x >>> s) * M) >>> t) * P) := by
  refine Iv.mem_barrett_toNat hx hmp ?_
  rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, BitVec.toNat_mul,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hg, Nat.mod_eq_of_lt hy]

/-- `ivBarrett?` is sound: its interval holds `x - y` for a member `x` of `ix` and `y`
    the Barrett product `⌊⌊x/2^s⌋·m/2^t⌋·p`. -/
theorem Iv.mem_ivBarrett {ix r : Iv} {x y : BitVec w} {s t m p : Nat} (h : ix.Mem w x)
    (hr : ivBarrett? w ix s t m p = some r)
    (hy : y.toNat = x.toNat / 2 ^ s * m / 2 ^ t * p) :
    r.Mem w (x - y) := by
  unfold ivBarrett? at hr
  split at hr
  · rename_i hc
    obtain ⟨h1, h2, h3⟩ := hc
    cases hr
    have hl := (Iv.mem_lane h).2
    have hx : x.toNat ≤ ix.2.toNat := by
      have hlane : ivLane w ix = ix := by
        unfold ivLane
        have hM : (0 : Int) < 2 ^ w := two_pow_pos_int _
        have e1 : ix.1 / 2 ^ w = 0 := Int.ediv_eq_zero_of_lt h1 (by
          have : ix.1 ≤ ix.2 := by
            obtain ⟨v, hv1, hv2, _⟩ := h; omega
          omega)
        have e2 : ix.2 / 2 ^ w = 0 := Int.ediv_eq_zero_of_lt (by
          obtain ⟨v, hv1, hv2, _⟩ := h; omega) h2
        simp [e1, e2]
      rw [hlane] at hl
      omega
    exact Iv.mem_barrett_toNat hx h3 hy
  · cases hr

/-! ## 5. The narrow multiply -/

/-- A 64-bit product of operands below `2^32` is the product of their low 32 bits
    zero-extended to 64 bits (the `vpmuludq` semantics). -/
theorem mul_eq_mul_setWidth32 (a b : BitVec 64) (ha : a.toNat < 2 ^ 32)
    (hb : b.toNat < 2 ^ 32) :
    a * b = (a.setWidth 32).setWidth 64 * (b.setWidth 32).setWidth 64 := by
  have ea : (a.setWidth 32).setWidth 64 = a := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt a.isLt]
  have eb : (b.setWidth 32).setWidth 64 = b := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt b.isLt]
  rw [ea, eb]

/-- The high half of a 64-bit difference whose operands have equal low halves is the
    difference of their high halves: the odd dword of a `vpsubq` of two such lanes is the
    `vpsubd` of their odd dwords. -/
theorem extractLsb'_sub_of_setWidth_eq (x y : BitVec 64) (h : x.setWidth 32 = y.setWidth 32) :
    (x - y).extractLsb' 32 32 = x.extractLsb' 32 32 - y.extractLsb' 32 32 := by
  apply BitVec.eq_of_toNat_eq
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth] at h'
  have hx := x.isLt
  have hy := y.isLt
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow] at *
  omega

/-! ## 6. Signed transfer functions -/

/-- The signed lane `[-2^(w-1), 2^(w-1) - 1]`, written without `w - 1`. -/
def ivSTop (w : Nat) : Iv := (-(2 ^ w / 2), (2 ^ w - 1) / 2)

/-- `i` lies in the signed lane: `-2^w ≤ 2·i.1` and `2·i.2 < 2^w`. -/
def ivSFits (w : Nat) (i : Iv) : Bool :=
  decide (-2 ^ w ≤ 2 * i.1) && decide (2 * i.2 < 2 ^ w)

/-- The interval of an arithmetic right shift by `k`: floor division by `2^k` of `a` when
    `a` lies in the signed lane, else of the signed lane. -/
def ivSar (w : Nat) (a : Iv) (k : Nat) : Iv :=
  let j := if ivSFits w a then a else ivSTop w
  (j.1 / 2 ^ k, j.2 / 2 ^ k)

/-- `i` moved down by `2^w` when it lies in the upper half `[2^(w-1), 2^w)` of the lane, so
    that a constant above `2^(w-1)` is read as a negative integer. -/
def ivCenter (w : Nat) (i : Iv) : Iv :=
  if 2 ^ w ≤ 2 * i.1 ∧ i.2 < 2 ^ w then (i.1 - 2 ^ w, i.2 - 2 ^ w) else i

/-- The interval of all products of an integer of `a` and an integer of `b`: the hull of
    the four corner products. -/
def ivCorner (a b : Iv) : Iv :=
  (min (min (a.1 * b.1) (a.1 * b.2)) (min (a.2 * b.1) (a.2 * b.2)),
   max (max (a.1 * b.1) (a.1 * b.2)) (max (a.2 * b.1) (a.2 * b.2)))

/-- The interval of a low product from the corner products of the centred operand
    intervals. -/
def ivMulS (w : Nat) (a b : Iv) : Iv :=
  ivNorm w (ivCorner (ivCenter w a) (ivCenter w b))

/-- The narrower of two intervals, `a` on a tie. -/
def ivNarrow (a b : Iv) : Iv :=
  if b.2 - b.1 < a.2 - a.1 then b else a

/-- The hull of two intervals. -/
def ivHull (a b : Iv) : Iv := (min a.1 b.1, max a.2 b.2)

/-- The interval of `(z.setWidth w) <<< k` for a `w0`-bit word `z` in `i`, when
    `w ≤ w0 + k`. -/
def ivShlExt (w : Nat) (i : Iv) (k : Nat) : Iv :=
  ivNorm w (i.1 * 2 ^ k, i.2 * 2 ^ k)

namespace Iv

variable {w : Nat} {a b : Iv} {x y : BitVec w}

/-- A word whose signed value lies in `i` is a member of `i`. -/
theorem mem_of_toInt {i : Iv} (h1 : i.1 ≤ x.toInt) (h2 : x.toInt ≤ i.2) : i.Mem w x := by
  refine ⟨x.toInt, h1, h2, ?_⟩
  have h := BitVec.toNat_ofInt (n := w) x.toInt
  rw [BitVec.ofInt_toInt] at h
  have hnn : 0 ≤ x.toInt % 2 ^ w := Int.emod_nonneg _ (two_pow_ne_zero_int _)
  push_cast at h
  rw [h, Int.toNat_of_nonneg hnn]

theorem toInt_mem_sTop (x : BitVec w) : (ivSTop w).1 ≤ x.toInt ∧ x.toInt ≤ (ivSTop w).2 := by
  have h1 := BitVec.le_two_mul_toInt (x := x)
  have h2 := BitVec.two_mul_toInt_lt (x := x)
  simp only [ivSTop]
  constructor <;> omega

/-- A member of an interval in the signed lane has its signed value in the interval. -/
theorem toInt_of_mem_sFits {i : Iv} (h : i.Mem w x) (hf : ivSFits w i = true) :
    i.1 ≤ x.toInt ∧ x.toInt ≤ i.2 := by
  obtain ⟨v, h1, h2, hv⟩ := h
  simp only [ivSFits, Bool.and_eq_true, decide_eq_true_eq] at hf
  have hM : (0 : Int) < 2 ^ w := two_pow_pos_int _
  have hxv : x.toInt = v := by
    have e : (2 : Int) ^ w = ((2 ^ w : Nat) : Int) := by push_cast; rfl
    rw [BitVec.toInt_eq_toNat_bmod, ← hv, e, Int.emod_bmod]
    rw [e] at hf
    exact Int.bmod_eq_of_le_mul_two (by omega) (by omega)
  rw [hxv]
  exact ⟨h1, h2⟩

theorem mem_sar (ha : a.Mem w x) (k : Nat) : (ivSar w a k).Mem w (x.sshiftRight k) := by
  have hj : (if ivSFits w a then a else ivSTop w).1 ≤ x.toInt ∧
      x.toInt ≤ (if ivSFits w a then a else ivSTop w).2 := by
    split
    · rename_i hf; exact toInt_of_mem_sFits ha hf
    · exact toInt_mem_sTop x
  have hk : (0 : Int) < 2 ^ k := two_pow_pos_int _
  have e : (x.sshiftRight k).toInt = x.toInt / 2 ^ k := by
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]; norm_cast
  exact mem_of_toInt (by rw [e]; exact Int.ediv_le_ediv hk hj.1)
    (by rw [e]; exact Int.ediv_le_ediv hk hj.2)

theorem Mem.center {i : Iv} (h : i.Mem w x) : (ivCenter w i).Mem w x := by
  unfold ivCenter
  split
  · obtain ⟨v, h1, h2, hv⟩ := h
    refine ⟨v - 2 ^ w, by simp only; omega, by simp only; omega, ?_⟩
    rw [Int.sub_emod, Int.emod_self, Int.sub_zero, Int.emod_emod, hv]
  · exact h

theorem mem_corner {x' y' : Int} (hx1 : a.1 ≤ x') (hx2 : x' ≤ a.2) (hy1 : b.1 ≤ y')
    (hy2 : y' ≤ b.2) : (ivCorner a b).1 ≤ x' * y' ∧ x' * y' ≤ (ivCorner a b).2 := by
  have seg : ∀ {a1 a2 u : Int} (z : Int), a1 ≤ u → u ≤ a2 →
      min (a1 * z) (a2 * z) ≤ u * z ∧ u * z ≤ max (a1 * z) (a2 * z) := by
    intro a1 a2 u z h1 h2
    rcases Int.le_total 0 z with hz | hz
    · exact ⟨Int.le_trans (Int.min_le_left _ _) (Int.mul_le_mul_of_nonneg_right h1 hz),
        Int.le_trans (Int.mul_le_mul_of_nonneg_right h2 hz) (Int.le_max_right _ _)⟩
    · exact ⟨Int.le_trans (Int.min_le_right _ _) (Int.mul_le_mul_of_nonpos_right h2 hz),
        Int.le_trans (Int.mul_le_mul_of_nonpos_right h1 hz) (Int.le_max_left _ _)⟩
  obtain ⟨l, u⟩ := seg y' hx1 hx2
  have e1 := seg a.1 hy1 hy2
  have e2 := seg a.2 hy1 hy2
  rw [Int.mul_comm b.1, Int.mul_comm b.2, Int.mul_comm y'] at e1 e2
  have mm : ∀ {p q r t : Int}, p ≤ r → q ≤ t → min p q ≤ min r t := by intros; omega
  have xx : ∀ {p q r t : Int}, p ≤ r → q ≤ t → max p q ≤ max r t := by intros; omega
  exact ⟨Int.le_trans (mm e1.1 e2.1) l, Int.le_trans u (xx e1.2 e2.2)⟩

theorem mem_mulS (ha : a.Mem w x) (hb : b.Mem w y) : (ivMulS w a b).Mem w (x * y) := by
  apply Mem.norm
  have ha' := ha.center
  have hb' := hb.center
  rw [mem_iff_ofInt] at ha' hb' ⊢
  obtain ⟨u, hu1, hu2, rfl⟩ := ha'
  obtain ⟨v, hv1, hv2, rfl⟩ := hb'
  obtain ⟨l, r⟩ := mem_corner hu1 hu2 hv1 hv2
  exact ⟨u * v, l, r, BitVec.ofInt_mul u v⟩

theorem mem_narrow (ha : a.Mem w x) (hb : b.Mem w x) : (ivNarrow a b).Mem w x := by
  unfold ivNarrow
  split
  · exact hb
  · exact ha

theorem mem_hull_left (ha : a.Mem w x) : (ivHull a b).Mem w x := by
  obtain ⟨v, h1, h2, hv⟩ := ha
  exact ⟨v, Int.le_trans (Int.min_le_left _ _) h1, Int.le_trans h2 (Int.le_max_left _ _), hv⟩

theorem mem_hull_right (hb : b.Mem w x) : (ivHull a b).Mem w x := by
  obtain ⟨v, h1, h2, hv⟩ := hb
  exact ⟨v, Int.le_trans (Int.min_le_right _ _) h1, Int.le_trans h2 (Int.le_max_right _ _), hv⟩

/-- A truncation keeps the interval: `x.setWidth w'` is a member of `ivNorm w' a` for a
    member `x` of `a` when `w' ≤ w`. -/
theorem mem_trunc {w' : Nat} (ha : a.Mem w x) (hw : w' ≤ w) :
    (ivNorm w' a).Mem w' (x.setWidth w') := by
  apply Mem.norm
  obtain ⟨v, h1, h2, hv⟩ := ha
  refine ⟨v, h1, h2, ?_⟩
  have hd : (2 : Int) ^ w' ∣ 2 ^ w := two_pow_dvd_int hw
  rw [BitVec.toNat_setWidth, ← Int.emod_emod_of_dvd v hd, hv]
  push_cast
  rfl

/-- The left shift by `k` of a zero extension to `w` bits of a `w0`-bit member `z` of `i`
    is a member of `ivShlExt w i k` when `w ≤ w0 + k`. -/
theorem mem_shlExt {w0 : Nat} {i : Iv} {z : BitVec w0} (hz : i.Mem w0 z) (k : Nat)
    (hw : w ≤ w0 + k) : (ivShlExt w i k).Mem w ((z.setWidth w) <<< k) := by
  apply Mem.norm
  obtain ⟨v, h1, h2, hv⟩ := hz
  have hk : (0 : Int) ≤ 2 ^ k := Int.le_of_lt (two_pow_pos_int _)
  refine ⟨v * 2 ^ k, Int.mul_le_mul_of_nonneg_right h1 hk,
    Int.mul_le_mul_of_nonneg_right h2 hk, ?_⟩
  have hd : (2 : Int) ^ w ∣ 2 ^ w0 * 2 ^ k := by
    rw [← Int.pow_add]; exact two_pow_dvd_int hw
  have hv' : v = (z.toNat : Int) + 2 ^ w0 * (v / 2 ^ w0) := by
    have := Int.emod_def v (2 ^ w0)
    rw [← hv]; omega
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_setWidth]
  push_cast
  obtain ⟨c, hc⟩ := hd
  conv => rhs; rw [Int.mul_emod, Int.emod_emod, ← Int.mul_emod]
  rw [hv', Int.add_mul, Int.mul_right_comm (2 ^ w0) (v / 2 ^ w0) (2 ^ k), hc, Int.mul_assoc,
    Int.add_mul_emod_self_left]

end Iv

/-! ## 7. Exact integer membership

A checked operation of Rust (`HaxLean/RuntimeM.lean`) acts on the integer a word denotes, not
on its residue: its guard bounds the exact result. `Iv.Has i n` reads `i` as a set of
integers; `Iv.mem_of_has` and `Iv.Mem.lane` relate it to the residue membership `Iv.Mem`. -/

/-- The integer `n` lies in `[i.1, i.2]`. -/
def Iv.Has (i : Iv) (n : Int) : Prop := i.1 ≤ n ∧ n ≤ i.2

/-- Every integer of `a` lies in `b`. -/
def ivLe (a b : Iv) : Bool := decide (b.1 ≤ a.1) && decide (a.2 ≤ b.2)

/-- The intersection of two intervals. -/
def ivMeet (a b : Iv) : Iv := (max a.1 b.1, min a.2 b.2)

/-- The interval of the exact sums. -/
def ivAddZ (a b : Iv) : Iv := (a.1 + b.1, a.2 + b.2)

/-- The interval of the exact differences. -/
def ivSubZ (a b : Iv) : Iv := (a.1 - b.2, a.2 - b.1)

/-- The one-point interval `[n, n]`. -/
def ivPoint (n : Int) : Iv := (n, n)

namespace Iv

theorem has_point (n : Int) : (ivPoint n).Has n := ⟨Int.le_refl n, Int.le_refl n⟩

theorem Has.le {a b : Iv} {n : Int} (h : a.Has n) (hab : ivLe a b = true) : b.Has n := by
  simp only [ivLe, Bool.and_eq_true, decide_eq_true_eq] at hab
  exact ⟨by have := h.1; omega, by have := h.2; omega⟩

theorem Has.meet {a b : Iv} {n : Int} (ha : a.Has n) (hb : b.Has n) : (ivMeet a b).Has n :=
  ⟨by have := ha.1; have := hb.1; simp only [ivMeet]; omega,
   by have := ha.2; have := hb.2; simp only [ivMeet]; omega⟩

theorem Has.hull_left {a b : Iv} {n : Int} (ha : a.Has n) : (ivHull a b).Has n :=
  ⟨by have := ha.1; simp only [ivHull]; omega, by have := ha.2; simp only [ivHull]; omega⟩

theorem Has.hull_right {a b : Iv} {n : Int} (hb : b.Has n) : (ivHull a b).Has n :=
  ⟨by have := hb.1; simp only [ivHull]; omega, by have := hb.2; simp only [ivHull]; omega⟩

theorem Has.add {a b : Iv} {m n : Int} (ha : a.Has m) (hb : b.Has n) :
    (ivAddZ a b).Has (m + n) :=
  ⟨by have := ha.1; have := hb.1; simp only [ivAddZ]; omega,
   by have := ha.2; have := hb.2; simp only [ivAddZ]; omega⟩

theorem Has.sub {a b : Iv} {m n : Int} (ha : a.Has m) (hb : b.Has n) :
    (ivSubZ a b).Has (m - n) :=
  ⟨by have := ha.1; have := hb.2; simp only [ivSubZ]; omega,
   by have := ha.2; have := hb.1; simp only [ivSubZ]; omega⟩

theorem Has.mul {a b : Iv} {m n : Int} (ha : a.Has m) (hb : b.Has n) :
    (ivCorner a b).Has (m * n) :=
  mem_corner ha.1 ha.2 hb.1 hb.2

/-- A word whose `toNat` lies in `i` is a member of `i`. -/
theorem mem_of_has {w : Nat} {i : Iv} {x : BitVec w} (h : i.Has x.toNat) : i.Mem w x :=
  mem_of_bounds h.1 h.2

/-- A member of `i` has its `toNat` in the lane interval of `i`. -/
theorem Mem.has_lane {w : Nat} {i : Iv} {x : BitVec w} (h : i.Mem w x) :
    (ivLane w i).Has x.toNat :=
  mem_lane h

end Iv

end CatCrypt.Crypto.SecureCompilation.RangeDomain

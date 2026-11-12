/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Range.Sound

/-!
# The heads of the typed extraction for the range checker

`rustGuard f vs` is the condition under which the Rust operation of the head `f` does not
panic on the arguments `vs`: the guards of `HaxLean/RuntimeM.lean` on the integers the
values denote (checked `+ - *` in the range of the width, a nonzero divisor and, signed,
not `MIN / -1`, a shift amount in `[0, w)`, an index in `[0, n)` of an array of length `n`,
and for an index by a range `start..end`, the value `(start, end)` of `Range`,
`0 ≤ start ≤ end ≤ n`: `sliceGuard`). A head named by an operation that panics in other ways
(`unwrap`, `expect`, `panic`, `assert`, the slicing heads `slice_to`, `slice_from`,
`slice_range`, `slice_update` and copying between slices) has guard `false`: the checker
never accepts it. Every other head has guard `true`. The width of an operation is that of its tag
(`Add#32`, `Mul#i64`, `Sub#size`); a tag that names no machine width (a field tag) and an
untagged operation on unbounded integers (`Value.int`) do not panic; an untagged operation on
words takes the width of its first argument.

`stdSpec sums` gives the transfer functions: exact interval arithmetic on the shared domain
(`ivAddZ`, `ivSubZ`, `ivCorner`) checked against the range of the width, the divisor and
shift-amount checks, index bounds against the least array length, `len` as the length
interval, the length of an array built by `repeat` or `array_lit`, a range `Range a b` as
`AV.rng` of the bounds' intervals, the slice of an array by such a range (`sliceXfer`,
accepted when the intervals prove `sliceGuard`, with the slice's length interval), and a
function of the crate through its summary `(pre, post)` in `sums`: a call is
accepted when its arguments lie in `pre`, with result in `post`. Its relational transfer
function `stdXrel` accepts an index into an array, and an update of it, when the index has a
nonnegative lower bound and a fact of the environment bounds it below the array's length
(`idxRel`), whatever the length interval.

`stdSpec_sound` instantiates `Sound` for `rustGuard` and `stdSpec sums` under `HeadSem`,
which states what the builtin table computes at these heads and that the summaries hold.
The summaries need not be assumed: `checkSums` checks each against the body of the function
it summarises, with the summaries of its callees, and `headSem_of_checkSums` derives
`HeadSem bi sums` from `HeadSem bi []` and `DefsSem`, the reading of the crate's definitions
by the table.

## Main definitions

* `splitHead`, `tagWidth`, `opWidth`, `rangeOf`: heads, tags and widths.
* `rustGuard`: the panic guards.
* `stdXfer`, `stdXrel`, `stdSpec`: the transfer functions.
* `HeadSem`: the semantics of the heads that the transfer functions read.
* `DefsSem`, `checkSums`: the crate's definitions read by the table, and the check of the
  summaries against their bodies.

## Main results

* `stdXfer_guard`, `stdXrel_guard`: an accepted call has its guard.
* `idxGuard_of_rel`: facts that bound a nonnegative index below an array's length prove the
  guard of an index into it.
* `stdSpec_sound`: `Sound rustGuard (stdSpec sums ann logic) bi` under `HeadSem bi sums`.
* `checkT_rust_sound`: a checked typed literal never fails a Rust guard under `denote'`.
* `headSem_of_checkSums`: summaries that `checkSums` accepts hold.
* `checkT_rust_sound_defs`: `checkT_rust_sound` with checked summaries.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Range

open CatCrypt.Crypto.SecureCompilation.RangeDomain

/-! ## Heads and widths -/

/-- The base and the tag of a head `Op#tag`. -/
def splitHead (f : String) : String × Option String :=
  match f.splitOn "#" with
  | [b] => (b, none)
  | b :: t :: _ => (b, some t)
  | [] => (f, none)

/-- The width and signedness a tag names: `8` … `128`, `size` (64 bits), each with an `i`
    prefix when signed. -/
def tagWidth (tag : String) : Option (Nat × Bool) :=
  let (signed, t) := if tag.startsWith "i" then (true, (tag.drop 1).toString) else (false, tag)
  if t == "size" then some (64, signed)
  else t.toNat?.bind fun n =>
    if n == 8 || n == 16 || n == 32 || n == 64 || n == 128 then some (n, signed) else none

/-- The width of an operation: from its tag, else from its first argument when that is a
    word. -/
def opWidth (tag : Option String) (vs : List Value) : Option (Nat × Bool) :=
  match tag with
  | some t => tagWidth t
  | none =>
    match vs with
    | .uint w _ :: _ => some (w.bits, false)
    | .sint w _ :: _ => some (w.bits, true)
    | _ => none

/-- The integers of a width. -/
def rangeOf : Nat × Bool → Iv
  | (bits, true) => (-2 ^ (bits - 1), 2 ^ (bits - 1) - 1)
  | (bits, false) => (0, 2 ^ bits - 1)

/-- Whether `n` lies in `i`. -/
def inIv (i : Iv) (n : Int) : Bool := decide (i.1 ≤ n) && decide (n ≤ i.2)

theorem inIv_of_has {i : Iv} {n : Int} (h : i.Has n) : inIv i n = true := by
  simp [inIv, h.1, h.2]

/-- The exact result of a checked operation. -/
def arithOp (base : String) (a b : Int) : Int :=
  if base = "Add" then a + b else if base = "Sub" then a - b else a * b

/-- The interval of the exact results of a checked operation. -/
def arithIv (base : String) (a b : Iv) : Iv :=
  if base = "Add" then ivAddZ a b else if base = "Sub" then ivSubZ a b else ivCorner a b

theorem arithIv_has {base : String} {a b : Iv} {m n : Int} (ha : a.Has m) (hb : b.Has n) :
    (arithIv base a b).Has (arithOp base m n) := by
  unfold arithIv arithOp
  split
  · exact ha.add hb
  split
  · exact ha.sub hb
  · exact ha.mul hb

/-- The checked arithmetic bases. -/
def isArith (base : String) : Bool := base == "Add" || base == "Sub" || base == "Mul"

/-- Division and remainder. -/
def isDivRem (base : String) : Bool := base == "Div" || base == "Rem"

/-- Shifts. -/
def isShift (base : String) : Bool := base == "Shl" || base == "Shr"

/-- Element access by index. -/
def isIndex (f : String) : Bool := f == "index" || f == "index_mut" || f == "vec_remove"

/-- Heads whose Rust counterpart panics in a way the domain does not express. -/
def opaquePartial (f : String) : Bool :=
  ["unwrap", "expect", "panic", "assert", "assert_failed", "unreachable", "todo",
    "unimplemented", "slice_update", "copy_from_slice", "slice_to", "slice_from",
    "slice_range", "Neg"].contains (splitHead f).1

/-! ## Guards -/

/-- The guard of an index into an array: the index lies in `[0, n)`. -/
def idxGuard (arr idx : Value) : Bool :=
  match arr.arrayLen, idx.toInt with
  | some n, some k => decide (0 ≤ k) && decide (k < (n : Int))
  | _, _ => false

/-- The guard of slicing an array by a range `start..end`, the value `(start, end)`:
    `0 ≤ start ≤ end ≤ n` for an array of length `n`. -/
def sliceGuard (arr r : Value) : Bool :=
  match arr.arrayLen, r with
  | some n, .tuple [x, y] =>
    match x.toInt, y.toInt with
    | some a, some b => decide (0 ≤ a) && decide (a ≤ b) && decide (b ≤ (n : Int))
    | _, _ => false
  | _, _ => false

/-- The condition under which the Rust operation of the head `f` does not panic on `vs`
    (the guards of `HaxLean/RuntimeM.lean`). -/
def rustGuard (f : String) (vs : List Value) : Bool :=
  let (base, tag) := splitHead f
  if isArith base then
    match opWidth tag vs, vs with
    | none, _ => true
    | some w, [x, y] =>
      match x.toInt, y.toInt with
      | some a, some b => inIv (rangeOf w) (arithOp base a b)
      | _, _ => false
    | some _, _ => false
  else if isDivRem base then
    match vs with
    | [x, y] =>
      match x.toInt, y.toInt with
      | some a, some b =>
        decide (b ≠ 0) &&
          match opWidth tag vs with
          | some (bits, true) => !(decide (a = -2 ^ (bits - 1)) && decide (b = -1))
          | _ => true
      | _, _ => false
    | _ => false
  else if isShift base then
    match opWidth tag vs, vs with
    | none, _ => true
    | some (bits, _), [_, y] =>
      match y.toInt with
      | some b => decide (0 ≤ b) && decide (b < (bits : Int))
      | none => false
    | some _, _ => false
  else if isIndex f then
    match vs with
    | [arr, idx] => idxGuard arr idx || sliceGuard arr idx
    | _ => false
  else if f == "array_update" then
    match vs with
    | [arr, idx, _] => idxGuard arr idx
    | _ => false
  else !opaquePartial f

/-! ## Transfer functions -/

/-- Checked `+ - *`: the exact interval, accepted when it lies in the range of the tag's
    width, or in `[0, 127]` (inside every width) for an untagged operation. A field tag gives
    no information and no guard. -/
def arithXfer (base : String) (tag : Option String) (avs : List AV) : Option AV :=
  match avs with
  | [.num a, .num b] =>
    let r := arithIv base a b
    match tag with
    | some t =>
      match tagWidth t with
      | some w => if ivLe r (rangeOf w) then some (.num r) else none
      | none => some .top
    | none => if ivLe r (0, 127) then some (.num r) else none
  | [_, _] =>
    match tag with
    | some t => if (tagWidth t).isNone then some .top else none
    | none => none
  | _ => none

/-- Division and remainder: the divisor's interval excludes `0`, and `MIN / -1` is
    excluded by a nonnegative dividend or a divisor that excludes `-1`. A remainder of a
    nonnegative dividend by a positive divisor lies below the divisor. -/
def divXfer (base : String) (avs : List AV) : Option AV :=
  match avs with
  | [.num a, .num b] =>
    if (decide (0 < b.1) || decide (b.2 < 0)) &&
        (decide (0 ≤ a.1) || decide (0 ≤ b.1) || decide (b.2 < -1)) then
      if base == "Rem" && decide (0 ≤ a.1) && decide (0 < b.1) then some (.num (0, b.2 - 1))
      else some .top
    else none
  | _ => none

/-- Shifts: the amount lies in `[0, w)` for the tag's width, or in `[0, 7]` (inside every
    width) for an untagged shift. -/
def shiftXfer (tag : Option String) (avs : List AV) : Option AV :=
  match avs with
  | [_, .num b] =>
    match tag with
    | some t =>
      match tagWidth t with
      | some (bits, _) => if ivLe b (0, (bits : Int) - 1) then some .top else none
      | none => none
    | none => if ivLe b (0, 7) then some .top else none
  | _ => none

/-- Element access: the index lies in `[0, l.1)` for the least length `l.1`. An update keeps
    the length. -/
def idxXfer (update : Bool) (avs : List AV) : Option AV :=
  match avs with
  | [.arr l, .num i] => if !update && ivLe i (0, l.1 - 1) then some .top else none
  | [.arr l, .num i, _] => if update && ivLe i (0, l.1 - 1) then some (.arr l) else none
  | _ => none

/-- A call that slices: `index` or `index_mut` on an array and a range. -/
def isSlice (f : String) (avs : List AV) : Bool :=
  (f == "index" || f == "index_mut") && match avs with
    | [_, .rng _ _] => true
    | _ => false

/-- Slicing an array of length in `l` by a range with bounds in `a` and `b`: accepted when
    `0 ≤ a.1`, `a.2 ≤ b.1` and `b.2 ≤ l.1`; the slice has a length in
    `[b.1 - a.2, b.2 - a.1]`. -/
def sliceXfer (avs : List AV) : Option AV :=
  match avs with
  | [.arr l, .rng a b] =>
    if decide (0 ≤ a.1) && decide (a.2 ≤ b.1) && decide (b.2 ≤ l.1) then
      some (.arr (b.1 - a.2, b.2 - a.1))
    else none
  | _ => none

/-- `len` of an array: its length interval. -/
def lenXfer (avs : List AV) : Option AV :=
  match avs with
  | [.arr l] => some (.num l)
  | _ => some .top

/-- A total head: the length of `len`, the length of an array built by `repeat` or
    `array_lit`, no information otherwise. -/
def defaultXfer (f : String) (avs : List AV) : Option AV :=
  if f == "len" then lenXfer avs
  else if f == "repeat" then
    match avs with
    | [_, .num i] => some (.arr i)
    | _ => some .top
  else if f == "array_lit" then some (.arr (avs.length, avs.length))
  else if f == "Range" then
    match avs with
    | [.num a, .num b] => some (.rng a b)
    | _ => some .top
  else some .top

/-- Each abstract value is included in the one at its position. -/
def leList : List AV → List AV → Bool
  | [], [] => true
  | a :: as, b :: bs => a.le b && leList as bs
  | _, _ => false

/-- The transfer functions of the heads, with the summaries `sums` of the crate's
    functions. -/
def stdXfer (sums : List (String × (List AV × AV))) (f : String) (avs : List AV) :
    Option AV :=
  let (base, tag) := splitHead f
  if isArith base then arithXfer base tag avs
  else if isDivRem base then divXfer base avs
  else if isShift base then shiftXfer tag avs
  else if isSlice f avs then sliceXfer avs
  else if isIndex f then idxXfer false avs
  else if f == "array_update" then idxXfer true avs
  else if opaquePartial f then none
  else
    match sums.lookup f with
    | some (pre, post) => if leList avs pre then some post else none
    | none => defaultXfer f avs

/-- The lower bound of an integer abstract value. -/
def AV.lo? : AV → Option Int
  | .num i => some i.1
  | .idx lo _ _ => some lo
  | _ => none

/-- The facts `rs` give `(1, 0, c)` with `0 ≤ c`: the argument at position 1 lies below the
    length of the array at position 0. -/
def idxRel (rs : List (Nat × Nat × Int)) : Bool :=
  rs.any fun r => r.1 == 1 && r.2.1 == 0 && decide (0 ≤ r.2.2)

/-- Element access with facts between the arguments: the index has a nonnegative lower bound
    and a fact bounds it below the length of the array. An update keeps the length. -/
def stdXrel (f : String) (avs : List AV) (rs : List (Nat × Nat × Int)) : Option AV :=
  let (base, _) := splitHead f
  if isArith base || isDivRem base || isShift base then none
  else if !(idxRel rs && ((avs[1]?).bind AV.lo?).any (0 ≤ ·)) then none
  else if isIndex f then (if avs.length == 2 then some .top else none)
  else if f == "array_update" then
    match avs with
    | [a, _, _] => some (match a with
      | .arr l => .arr l
      | _ => .top)
    | _ => none
  else none

/-- The specification of the heads with the summaries `sums`, the loop annotation `ann`, and
    the refinement by Boolean guards when `logic`. -/
def stdSpec (sums : List (String × (List AV × AV))) (ann : AEnv := []) (logic : Bool := false) :
    Spec :=
  { xfer := stdXfer sums, xrel := stdXrel, ann, logic }

/-! ## Accepted calls have their guards -/

theorem memList_two {a b : AV} {vs : List Value} (h : MemList [a, b] vs) :
    ∃ x y, vs = [x, y] ∧ a.Mem x ∧ b.Mem y := by
  match vs, h with
  | [x, y], ⟨hx, hy, _⟩ => exact ⟨x, y, rfl, hx, hy⟩

theorem memList_three {a b c : AV} {vs : List Value} (h : MemList [a, b, c] vs) :
    ∃ x y z, vs = [x, y, z] ∧ a.Mem x ∧ b.Mem y ∧ c.Mem z := by
  match vs, h with
  | [x, y, z], ⟨hx, hy, hz, _⟩ => exact ⟨x, y, z, rfl, hx, hy, hz⟩

theorem memList_le {as bs : List AV} {vs : List Value} (h : MemList as vs)
    (hle : leList as bs = true) : MemList bs vs := by
  induction as generalizing bs vs with
  | nil =>
    cases bs with
    | nil => exact h
    | cons _ _ => simp [leList] at hle
  | cons a as ih =>
    cases bs with
    | nil => simp [leList] at hle
    | cons b bs =>
      cases vs with
      | nil => exact absurd h id
      | cons v vs =>
        simp only [leList, Bool.and_eq_true] at hle
        exact ⟨h.1.le hle.1, ih h.2 hle.2⟩

theorem IntWidth.bits_ge (w : IntWidth) : 8 ≤ w.bits := by cases w <;> decide

/-- `[0, 127]` lies in the range of every width. -/
theorem has_rangeOf_small {bits : Nat} {s : Bool} (hb : 8 ≤ bits) {n : Int}
    (h : Iv.Has (0, 127) n) : (rangeOf (bits, s)).Has n := by
  have h8 : (2 : Int) ^ 8 ≤ 2 ^ bits := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hb
    exact_mod_cast this
  have h7 : (2 : Int) ^ 7 ≤ 2 ^ (bits - 1) := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ bits - 1)
    exact_mod_cast this
  have := two_pow_pos_int (bits - 1)
  obtain ⟨h1, h2⟩ := h
  cases s <;> simp only [rangeOf] <;> constructor <;> simp only at h1 h2 <;> omega

theorem toInt_some_of_mem_num {i : Iv} {v : Value} (h : (AV.num i).Mem v) :
    ∃ n, v.toInt = some n ∧ i.Has n := h

/-- An addition head has the base `Add`. -/
theorem splitHead_fst_of_isAddHead {f : String} (h : isAddHead f = true) :
    (splitHead f).1 = "Add" := by
  unfold isAddHead at h
  unfold splitHead
  rcases hs : f.splitOn "#" with _ | ⟨b, _ | ⟨t, _⟩⟩ <;> simp_all

/-- A slicing call is an element-access head. -/
theorem isIndex_of_isSlice {f : String} {avs : List AV} (h : isSlice f avs = true) :
    isIndex f = true := by
  unfold isSlice at h
  unfold isIndex
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h ⊢
  rcases h.1 with h | h <;> simp [h]

/-- An accepted call has its Rust guard. -/
theorem stdXfer_guard {sums : List (String × (List AV × AV))} {f : String} {avs : List AV}
    {a : AV} {vs : List Value} (h : stdXfer sums f avs = some a) (hm : MemList avs vs) :
    rustGuard f vs = true := by
  unfold stdXfer at h
  unfold rustGuard
  generalize splitHead f = p at h ⊢
  obtain ⟨base, tag⟩ := p
  dsimp only at h ⊢
  by_cases harith : isArith base = true
  · simp only [harith, ↓reduceIte] at h ⊢
    unfold arithXfer at h
    match avs, h, hm with
    | [.num ia, .num ib], h, hm =>
      obtain ⟨x, y, rfl, ⟨m, hmx, hmi⟩, ⟨n, hny, hni⟩⟩ := memList_two hm
      have hr := arithIv_has (base := base) hmi hni
      cases tag with
      | some t =>
        rcases hw : tagWidth t with _ | w <;> simp only [hw] at h
        · simp [opWidth, hw]
        · simp only [opWidth, hw, hmx, hny]
          by_cases hle : ivLe (arithIv base ia ib) (rangeOf w) = true
          · exact inIv_of_has (hr.le hle)
          · simp [hle] at h
      | none =>
        by_cases hle : ivLe (arithIv base ia ib) (0, 127) = true
        · have hs := hr.le hle
          cases x with
          | uint w _ =>
            simp only [opWidth, hmx, hny]
            exact inIv_of_has (has_rangeOf_small (IntWidth.bits_ge w) hs)
          | sint w _ =>
            simp only [opWidth, hmx, hny]
            exact inIv_of_has (has_rangeOf_small (IntWidth.bits_ge w) hs)
          | _ => simp [opWidth]
        · simp [hle] at h
    | [.top, _], h, hm | [.arr _, _], h, hm | [.num _, .top], h, hm
    | [.num _, .arr _], h, hm | [.idx _ _ _, _], h, hm | [.num _, .idx _ _ _], h, hm
    | [.rng _ _, _], h, hm | [.num _, .rng _ _], h, hm =>
      obtain ⟨x, y, rfl, -, -⟩ := memList_two hm
      cases tag with
      | some t =>
        rcases hw : tagWidth t with _ | w <;> simp [hw] at h
        simp [opWidth, hw]
      | none => simp at h
    | [], h, _ | [_], h, _ | _ :: _ :: _ :: _, h, _ => simp at h
  simp only [harith, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases hdiv : isDivRem base = true
  · simp only [hdiv, ↓reduceIte] at h ⊢
    unfold divXfer at h
    match avs, h, hm with
    | [.num ia, .num ib], h, hm =>
      obtain ⟨x, y, rfl, ⟨m, hmx, hmi⟩, ⟨n, hny, hni⟩⟩ := memList_two hm
      simp only [hmx, hny]
      by_cases hc : ((decide (0 < ib.1) || decide (ib.2 < 0)) &&
          (decide (0 ≤ ia.1) || decide (0 ≤ ib.1) || decide (ib.2 < -1))) = true
      · simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
        obtain ⟨h1, h2⟩ := hc
        obtain ⟨hm1, hm2⟩ := hmi
        obtain ⟨hn1, hn2⟩ := hni
        have hnz : n ≠ 0 := by omega
        simp only [ne_eq, hnz, not_false_eq_true, decide_true, Bool.true_and]
        split
        · rename_i bits _
          have := two_pow_pos_int (bits - 1)
          simp only [Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
          omega
        · rfl
      · simp [hc] at h
    | [], h, _ | [_], h, _ | _ :: _ :: _ :: _, h, _ => simp at h
    | [.top, _], h, _ | [.arr _, _], h, _ | [.num _, .top], h, _
    | [.num _, .arr _], h, _ | [.idx _ _ _, _], h, _ | [.num _, .idx _ _ _], h, _ => simp at h
  simp only [hdiv, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases hsh : isShift base = true
  · simp only [hsh, ↓reduceIte] at h ⊢
    unfold shiftXfer at h
    match avs, h, hm with
    | [ax, .num ib], h, hm =>
      obtain ⟨x, y, rfl, -, ⟨n, hny, hni⟩⟩ := memList_two hm
      cases tag with
      | some t =>
        rcases hw : tagWidth t with _ | ⟨bits, s⟩ <;> simp only [hw] at h
        · simp at h
        simp only [opWidth, hw, hny]
        by_cases hle : ivLe ib (0, (bits : Int) - 1) = true
        · have := hni.le hle
          simp only [Iv.Has] at this
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          omega
        · simp [hle] at h
      | none =>
        by_cases hle : ivLe ib (0, 7) = true
        · have := hni.le hle
          simp only [Iv.Has] at this
          cases x with
          | uint w _ =>
            have := IntWidth.bits_ge w
            simp only [opWidth, hny, Bool.and_eq_true, decide_eq_true_eq]
            omega
          | sint w _ =>
            have := IntWidth.bits_ge w
            simp only [opWidth, hny, Bool.and_eq_true, decide_eq_true_eq]
            omega
          | _ => simp [opWidth]
        · simp [hle] at h
    | [], h, _ | [_], h, _ | _ :: _ :: _ :: _, h, _ => simp at h
    | [_, .top], h, _ | [_, .arr _], h, _ | [_, .idx _ _ _], h, _ => simp at h
  simp only [hsh, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases hsl : isSlice f avs = true
  · simp only [hsl, ↓reduceIte, isIndex_of_isSlice hsl] at h ⊢
    unfold sliceXfer at h
    split at h
    · rename_i l a b
      obtain ⟨x, r, rfl, ⟨n, hn, hnl⟩, ⟨y1, y2, rfl, ⟨m1, hm1, ha⟩, m2, hm2, hb⟩⟩ :=
        memList_two hm
      by_cases hc : (decide (0 ≤ a.1) && decide (a.2 ≤ b.1) && decide (b.2 ≤ l.1)) = true
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        simp only [Iv.Has] at ha hb hnl
        refine Bool.or_eq_true_iff.2 (Or.inr ?_)
        simp only [sliceGuard, hn, hm1, hm2, Bool.and_eq_true, decide_eq_true_eq]
        omega
      · simp [hc] at h
    · simp at h
  simp only [hsl, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hix : isIndex f = true
  · simp only [hix, ↓reduceIte] at h ⊢
    unfold idxXfer at h
    match avs, h, hm with
    | [.arr l, .num i], h, hm =>
      obtain ⟨x, y, rfl, ⟨k, hk, hkl⟩, ⟨n, hn, hni⟩⟩ := memList_two hm
      simp only [Bool.not_false, Bool.true_and] at h
      by_cases hle : ivLe i (0, l.1 - 1) = true
      · have := hni.le hle
        simp only [Iv.Has] at this hkl
        refine Bool.or_eq_true_iff.2 (Or.inl ?_)
        simp only [idxGuard, hk, hn, Bool.and_eq_true, decide_eq_true_eq]
        omega
      · simp [hle] at h
    | [], h, _ | [_], h, _ => simp at h
    | [.arr _, .num _, _], h, _ => simp at h
    | [.top, _], h, _ | [.num _, _], h, _ | [.arr _, .top], h, _
    | [.arr _, .arr _], h, _ | [.idx _ _ _, _], h, _ | [.arr _, .idx _ _ _], h, _
    | [.rng _ _, _], h, _ | [.arr _, .rng _ _], h, _ => simp at h
    | [.top, _, _], h, _ | [.num _, _, _], h, _ | [.arr _, .top, _], h, _
    | [.arr _, .arr _, _], h, _ | [.idx _ _ _, _, _], h, _ | [.arr _, .idx _ _ _, _], h, _
    | [.rng _ _, _, _], h, _ | [.arr _, .rng _ _, _], h, _ =>
      simp at h
    | _ :: _ :: _ :: _ :: _, h, _ => simp at h
  simp only [hix, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases hup : (f == "array_update") = true
  · simp only [hup, ↓reduceIte] at h ⊢
    unfold idxXfer at h
    match avs, h, hm with
    | [.arr l, .num i, c], h, hm =>
      obtain ⟨x, y, z, rfl, ⟨k, hk, hkl⟩, ⟨n, hn, hni⟩, -⟩ := memList_three hm
      simp only [Bool.true_and] at h
      by_cases hle : ivLe i (0, l.1 - 1) = true
      · have := hni.le hle
        simp only [Iv.Has] at this hkl
        simp only [idxGuard, hk, hn, Bool.and_eq_true, decide_eq_true_eq]
        omega
      · simp [hle] at h
    | [], h, _ | [_], h, _ => simp at h
    | [.arr _, .num _], h, _ => simp at h
    | [.top, _], h, _ | [.num _, _], h, _ | [.arr _, .top], h, _
    | [.arr _, .arr _], h, _ | [.idx _ _ _, _], h, _ | [.arr _, .idx _ _ _], h, _
    | [.rng _ _, _], h, _ | [.arr _, .rng _ _], h, _ => simp at h
    | [.top, _, _], h, _ | [.num _, _, _], h, _ | [.arr _, .top, _], h, _
    | [.arr _, .arr _, _], h, _ | [.idx _ _ _, _, _], h, _ | [.arr _, .idx _ _ _, _], h, _
    | [.rng _ _, _, _], h, _ | [.arr _, .rng _ _, _], h, _ =>
      simp at h
    | _ :: _ :: _ :: _ :: _, h, _ => simp at h
  simp only [hup, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases hop : opaquePartial f = true
  · simp [hop] at h
  · simpa using hop

theorem memList_length {as : List AV} {vs : List Value} (h : MemList as vs) :
    as.length = vs.length := by
  induction as generalizing vs with
  | nil => cases vs with
    | nil => rfl
    | cons _ _ => exact absurd h id
  | cons a as ih => cases vs with
    | nil => exact absurd h id
    | cons v vs => simp [ih h.2]

/-- A value at a position of a list lies in the abstract value at that position. -/
theorem memList_getElem? :
    ∀ {avs : List AV} {vs : List Value} {i : Nat} {a : AV} {v : Value}, MemList avs vs →
      avs[i]? = some a → vs[i]? = some v → a.Mem v
  | [], _, _, _, _, _, ha, _ => by simp at ha
  | _ :: _, [], _, _, _, hm, _, _ => absurd hm id
  | b :: avs, w :: vs, 0, a, v, hm, ha, hv => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hv
    subst ha hv
    exact hm.1
  | b :: avs, w :: vs, i + 1, a, v, hm, ha, hv => by
    simp only [List.getElem?_cons_succ] at ha hv
    exact memList_getElem? hm.2 ha hv

theorem AV.lo?_le {a : AV} {lo : Int} {v : Value} (h : a.lo? = some lo) (hm : a.Mem v) :
    ∃ k, v.toInt = some k ∧ lo ≤ k := by
  cases a with
  | num i =>
    simp only [AV.lo?, Option.some.injEq] at h
    subst h
    obtain ⟨k, hk, hi⟩ := hm
    exact ⟨k, hk, hi.1⟩
  | idx lo' hi rs =>
    simp only [AV.lo?, Option.some.injEq] at h
    subst h
    obtain ⟨k, hk, h1, -⟩ := hm
    exact ⟨k, hk, h1⟩
  | _ => simp [AV.lo?] at h

/-- Facts that bound a nonnegative index below the length of an array prove the guard of an
    index into it. -/
theorem idxGuard_of_rel {avs : List AV} {rs : List (Nat × Nat × Int)} {vs : List Value}
    (hm : MemList avs vs) (hr : RelArgs rs vs) (hi : idxRel rs = true)
    (hlo : ((avs[1]?).bind AV.lo?).any (0 ≤ ·) = true) {arr idx : Value}
    (hv0 : vs[0]? = some arr) (hv1 : vs[1]? = some idx) : idxGuard arr idx = true := by
  obtain ⟨r, hr1, hr2⟩ := List.any_eq_true.1 hi
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr2
  obtain ⟨⟨h1, h2⟩, h3⟩ := hr2
  obtain ⟨k, n, hk, hn, hlt⟩ := hr r hr1
  rw [h1, hv1, Option.bind_some] at hk
  rw [h2, hv0, Option.bind_some] at hn
  obtain ⟨lo, hlo1, hlo2⟩ := (Option.any_eq_true _ _).1 hlo
  obtain ⟨a1, ha1, hlo1'⟩ := Option.bind_eq_some_iff.1 hlo1
  obtain ⟨k', hk', hk'lo⟩ := AV.lo?_le hlo1' (memList_getElem? hm ha1 hv1)
  rw [hk] at hk'
  cases hk'
  simp only [decide_eq_true_eq] at hlo2
  simp only [idxGuard, hn, hk, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- A call accepted with facts has its Rust guard. -/
theorem stdXrel_guard {f : String} {avs : List AV} {rs : List (Nat × Nat × Int)} {a : AV}
    {vs : List Value} (h : stdXrel f avs rs = some a) (hm : MemList avs vs)
    (hr : RelArgs rs vs) : rustGuard f vs = true := by
  unfold stdXrel at h
  unfold rustGuard
  generalize splitHead f = p at h ⊢
  obtain ⟨base, tag⟩ := p
  dsimp only at h ⊢
  rcases h1 : isArith base <;> rcases h2 : isDivRem base <;> rcases h3 : isShift base <;>
    simp only [h1, h2, h3, Bool.or_true, Bool.or_false, ↓reduceIte,
      reduceCtorEq, Bool.false_eq_true] at h ⊢
  cases hok : (idxRel rs && ((avs[1]?).bind AV.lo?).any (0 ≤ ·))
  · simp [hok] at h
  simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  simp only [Bool.and_eq_true] at hok
  by_cases hix : isIndex f = true
  · simp only [hix, ↓reduceIte] at h ⊢
    have hl : avs.length = 2 := by
      by_cases h2 : (avs.length == 2) = true
      · simpa using h2
      · simp [h2] at h
    have hvl : vs.length = 2 := (memList_length hm).symm.trans hl
    match vs, hvl with
    | [x, y], _ =>
      exact Bool.or_eq_true_iff.2 (Or.inl (idxGuard_of_rel hm hr hok.1 hok.2 rfl rfl))
  simp only [hix, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases hup : (f == "array_update") = true
  · simp only [hup, ↓reduceIte] at h ⊢
    match avs, h, hm with
    | [_, _, _], _, hm =>
      obtain ⟨x, y, z, rfl, -⟩ := memList_three hm
      exact idxGuard_of_rel hm hr hok.1 hok.2 rfl rfl
    | [], h, _ | [_], h, _ | [_, _], h, _ | _ :: _ :: _ :: _ :: _, h, _ => simp at h
  · simp [hup] at h

/-! ## Semantics of the heads -/

/-- What the builtin table computes at the heads whose results the transfer functions
    read, and the summaries of the crate's functions: values free of control flow, the
    truth of comparisons, the exact result of a checked operation whose guard holds, the
    remainder of a nonnegative dividend by a positive divisor, the length kept by an update,
    the length returned by `len`, the length of an array built by `repeat` or `array_lit`,
    the pair `(start, end)` built by `Range`, the length `end - start` of a slice by such a
    pair, and each summary's postcondition on arguments in its precondition that are free of
    control flow. -/
structure HeadSem (bi : Builtins) (sums : List (String × (List AV × AV))) : Prop where
  deep : Builtins.DeepNoControlFlow bi
  cmp : ∀ op strict swapped vl vr b m n, cmpOf op = some (strict, swapped) →
    bi op [vl, vr] = some (.bool b) → vl.toInt = some m → vr.toInt = some n →
    (b = true ↔ cmpRel strict swapped m n)
  arith : ∀ f x y v a b, isArith (splitHead f).1 = true → rustGuard f [x, y] = true →
    bi f [x, y] = some v → x.toInt = some a → y.toInt = some b →
    v.toInt = some (arithOp (splitHead f).1 a b)
  rem : ∀ f x y v a b, (splitHead f).1 = "Rem" → bi f [x, y] = some v → x.toInt = some a →
    y.toInt = some b → 0 ≤ a → 0 < b → v.toInt = some (a % b)
  update : ∀ arr i u v, bi "array_update" [arr, i, u] = some v → v.arrayLen = arr.arrayLen
  repeatLen : ∀ x y v n, bi "repeat" [x, y] = some v → y.toInt = some n →
    ∃ k : Nat, v.arrayLen = some k ∧ (k : Int) = n
  arrayLit : ∀ vs v, bi "array_lit" vs = some v → v.arrayLen = some vs.length
  len : ∀ arr v, bi "len" [arr] = some v → ∃ n, arr.arrayLen = some n ∧ v.toInt = some n
  range : ∀ x y r, bi "Range" [x, y] = some r → r = .tuple [x, y]
  slice : ∀ f arr x y v a b, (f == "index" || f == "index_mut") = true →
    bi f [arr, .tuple [x, y]] = some v → x.toInt = some a → y.toInt = some b → a ≤ b →
    ∃ k : Nat, v.arrayLen = some k ∧ (k : Int) = b - a
  sums : ∀ g pre post, sums.lookup g = some (pre, post) → ∀ vs v, MemList pre vs →
    (∀ w ∈ vs, w.deepNoControlFlow = true) → bi g vs = some v → post.Mem v

/-- The result of a call accepted with facts lies in the relational transfer function's
    value. -/
theorem stdXrel_result {bi : Builtins} {sums : List (String × (List AV × AV))}
    (hH : HeadSem bi sums) {f : String} {avs : List AV} {rs : List (Nat × Nat × Int)} {a : AV}
    {vs : List Value} {v : Value} (h : stdXrel f avs rs = some a) (hm : MemList avs vs)
    (hb : bi f vs = some v) : a.Mem v := by
  unfold stdXrel at h
  generalize splitHead f = p at h
  obtain ⟨base, tag⟩ := p
  dsimp only at h
  by_cases hb0 : (isArith base || isDivRem base || isShift base) = true
  · simp [hb0] at h
  simp only [hb0, Bool.false_eq_true, ↓reduceIte] at h
  cases hok : (idxRel rs && ((avs[1]?).bind AV.lo?).any (0 ≤ ·))
  · simp [hok] at h
  simp only [hok, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hix : isIndex f = true
  · simp only [hix, ↓reduceIte] at h
    by_cases h2 : (avs.length == 2) = true
    · simp only [h2, ↓reduceIte, Option.some.injEq] at h
      subst h
      trivial
    · simp [h2] at h
  simp only [hix, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hup : (f == "array_update") = true
  · simp only [hup, ↓reduceIte] at h
    have hf : f = "array_update" := by simpa using hup
    subst hf
    match avs, h, hm with
    | [a0, _, _], h, hm =>
      obtain ⟨x, y, z, rfl, hx, -, -⟩ := memList_three hm
      simp only [Option.some.injEq] at h
      subst h
      cases a0 with
      | arr l =>
        obtain ⟨k, hk, hkl⟩ := hx
        exact ⟨k, by rw [hH.update x y z v hb, hk], hkl⟩
      | _ => trivial
    | [], h, _ | [_], h, _ | [_, _], h, _ | _ :: _ :: _ :: _ :: _, h, _ => simp at h
  · simp [hup] at h

/-- The result of a total head lies in its transfer function's value. -/
theorem defaultXfer_result {bi : Builtins} {sums : List (String × (List AV × AV))}
    (hH : HeadSem bi sums) {f : String} {avs : List AV} {a : AV} {vs : List Value} {v : Value}
    (h : defaultXfer f avs = some a) (hm : MemList avs vs) (hb : bi f vs = some v) :
    a.Mem v := by
  unfold defaultXfer at h
  by_cases hlen : (f == "len") = true
  · simp only [hlen, ↓reduceIte] at h
    have hf : f = "len" := by simpa using hlen
    subst hf
    unfold lenXfer at h
    match avs, h, hm with
    | [.arr l], h, hm =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨x, rfl, ⟨n, hn, hnl⟩⟩ : ∃ x, vs = [x] ∧ (AV.arr l).Mem x := by
        match vs, hm with
        | [x], ⟨hx, _⟩ => exact ⟨x, rfl, hx⟩
      obtain ⟨n', hn', hv⟩ := hH.len x v hb
      rw [hn] at hn'
      cases hn'
      exact ⟨_, hv, hnl⟩
    | [], h, _ | _ :: _ :: _, h, _ => simp only [Option.some.injEq] at h; subst h; trivial
    | [.top], h, _ | [.num _], h, _ | [.idx _ _ _], h, _ | [.rng _ _], h, _ =>
      simp only [Option.some.injEq] at h; subst h; trivial
  simp only [hlen, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hrep : (f == "repeat") = true
  · simp only [hrep, ↓reduceIte] at h
    have hf : f = "repeat" := by simpa using hrep
    subst hf
    match avs, h, hm with
    | [_, .num i], h, hm =>
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨x, y, rfl, -, ⟨n, hn, hni⟩⟩ := memList_two hm
      obtain ⟨k, hk, hkn⟩ := hH.repeatLen x y v n hb hn
      exact ⟨k, hk, hkn ▸ hni⟩
    | [], h, _ | [_], h, _ | _ :: _ :: _ :: _, h, _ =>
      simp only [Option.some.injEq] at h; subst h; trivial
    | [_, .top], h, _ | [_, .arr _], h, _ | [_, .idx _ _ _], h, _ | [_, .rng _ _], h, _ =>
      simp only [Option.some.injEq] at h; subst h; trivial
  simp only [hrep, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hlit : (f == "array_lit") = true
  · simp only [hlit, ↓reduceIte, Option.some.injEq] at h
    have hf : f = "array_lit" := by simpa using hlit
    subst hf h
    refine ⟨vs.length, hH.arrayLit vs v hb, ?_⟩
    rw [memList_length hm]
    exact ⟨Int.le_refl _, Int.le_refl _⟩
  simp only [hlit, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hrng : (f == "Range") = true
  · simp only [hrng, ↓reduceIte] at h
    have hf : f = "Range" := by simpa using hrng
    subst hf
    split at h
    · rename_i ia ib
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨x, y, rfl, hx, hy⟩ := memList_two hm
      exact ⟨x, y, hH.range x y v hb, hx, hy⟩
    · simp only [Option.some.injEq] at h
      subst h
      trivial
  · simp only [hrng, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
    subst h
    trivial

/-- An accepted call's result lies in the transfer function's value. -/
theorem stdXfer_result {bi : Builtins} {sums : List (String × (List AV × AV))}
    (hH : HeadSem bi sums) {f : String} {avs : List AV} {a : AV} {vs : List Value} {v : Value}
    (h : stdXfer sums f avs = some a) (hm : MemList avs vs)
    (hd : ∀ w ∈ vs, w.deepNoControlFlow = true) (hb : bi f vs = some v) :
    a.Mem v := by
  have hg := stdXfer_guard h hm
  unfold stdXfer at h
  rcases hp : splitHead f with ⟨base, tag⟩
  rw [hp] at h
  dsimp only at h
  by_cases harith : isArith base = true
  · simp only [harith, ↓reduceIte] at h
    unfold arithXfer at h
    match avs, h, hm with
    | [.num ia, .num ib], h, hm =>
      obtain ⟨x, y, rfl, ⟨m, hmx, hmi⟩, ⟨n, hny, hni⟩⟩ := memList_two hm
      have hr := arithIv_has (base := base) hmi hni
      have hv := hH.arith f x y v m n (by rw [hp]; exact harith) hg hb hmx hny
      rw [hp] at hv
      cases tag with
      | some t =>
        rcases hw : tagWidth t with _ | w <;> simp only [hw] at h
        · cases h; trivial
        · by_cases hle : ivLe (arithIv base ia ib) (rangeOf w) = true
          · simp only [hle, ↓reduceIte, Option.some.injEq] at h
            subst h
            exact ⟨_, hv, hr⟩
          · simp [hle] at h
      | none =>
        by_cases hle : ivLe (arithIv base ia ib) (0, 127) = true
        · simp only [hle, ↓reduceIte, Option.some.injEq] at h
          subst h
          exact ⟨_, hv, hr⟩
        · simp [hle] at h
    | [.top, _], h, _ | [.arr _, _], h, _ | [.num _, .top], h, _
    | [.num _, .arr _], h, _ | [.idx _ _ _, _], h, _ | [.num _, .idx _ _ _], h, _
    | [.rng _ _, _], h, _ | [.num _, .rng _ _], h, _ =>
      cases tag with
      | some t =>
        rcases hw : tagWidth t with _ | w <;> simp [hw] at h
        subst h; trivial
      | none => simp at h
    | [], h, _ | [_], h, _ | _ :: _ :: _ :: _, h, _ => simp at h
  simp only [harith, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hdiv : isDivRem base = true
  · simp only [hdiv, ↓reduceIte] at h
    unfold divXfer at h
    match avs, h, hm with
    | [.num ia, .num ib], h, hm =>
      obtain ⟨x, y, rfl, ⟨m, hmx, hmi⟩, ⟨n, hny, hni⟩⟩ := memList_two hm
      by_cases hc : ((decide (0 < ib.1) || decide (ib.2 < 0)) &&
          (decide (0 ≤ ia.1) || decide (0 ≤ ib.1) || decide (ib.2 < -1))) = true
      · by_cases hrem : (base == "Rem" && decide (0 ≤ ia.1) && decide (0 < ib.1)) = true
        · simp only [hc, hrem, ↓reduceIte, Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrem
          obtain ⟨⟨hr, h0⟩, h1⟩ := hrem
          have ha0 : 0 ≤ m := by have := hmi.1; omega
          have hb0 : 0 < n := by have := hni.1; omega
          have hv := hH.rem f x y v m n (by rw [hp]; exact hr) hb hmx hny ha0 hb0
          refine ⟨_, hv, ?_, ?_⟩
          · exact Int.emod_nonneg _ (by omega)
          · have := Int.emod_lt_of_pos m hb0
            have := hni.2
            simp only
            omega
        · simp only [hc, hrem, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
          subst h
          trivial
      · simp [hc] at h
    | [], h, _ | [_], h, _ | _ :: _ :: _ :: _, h, _ => simp at h
    | [.top, _], h, _ | [.arr _, _], h, _ | [.num _, .top], h, _
    | [.num _, .arr _], h, _ | [.idx _ _ _, _], h, _ | [.num _, .idx _ _ _], h, _ => simp at h
  simp only [hdiv, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hsh : isShift base = true
  · simp only [hsh, ↓reduceIte] at h
    unfold shiftXfer at h
    match avs, h with
    | [_, .num ib], h =>
      cases tag with
      | some t =>
        rcases hw : tagWidth t with _ | ⟨bits, s⟩ <;> simp only [hw] at h
        · simp at h
        by_cases hle : ivLe ib (0, (bits : Int) - 1) = true
        · simp only [hle, ↓reduceIte, Option.some.injEq] at h
          subst h
          trivial
        · simp [hle] at h
      | none =>
        by_cases hle : ivLe ib (0, 7) = true
        · simp only [hle, ↓reduceIte, Option.some.injEq] at h
          subst h
          trivial
        · simp [hle] at h
    | [], h | [_], h | _ :: _ :: _ :: _, h => simp at h
    | [_, .top], h | [_, .arr _], h | [_, .idx _ _ _], h => simp at h
  simp only [hsh, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hsl : isSlice f avs = true
  · simp only [hsl, ↓reduceIte] at h
    have hfi : (f == "index" || f == "index_mut") = true := by
      unfold isSlice at hsl
      simp only [Bool.and_eq_true] at hsl
      exact hsl.1
    unfold sliceXfer at h
    split at h
    · rename_i l a b
      obtain ⟨x, r, rfl, -, ⟨y1, y2, rfl, ⟨m1, hm1, ha⟩, m2, hm2, hb'⟩⟩ := memList_two hm
      by_cases hc : (decide (0 ≤ a.1) && decide (a.2 ≤ b.1) && decide (b.2 ≤ l.1)) = true
      · simp only [hc, ↓reduceIte, Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        simp only [Iv.Has] at ha hb'
        obtain ⟨k, hk, hkv⟩ := hH.slice f x y1 y2 v m1 m2 hfi hb hm1 hm2 (by omega)
        exact ⟨k, hk, by constructor <;> dsimp only <;> omega⟩
      · simp [hc] at h
    · simp at h
  simp only [hsl, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hix : isIndex f = true
  · simp only [hix, ↓reduceIte] at h
    unfold idxXfer at h
    match avs, h with
    | [.arr l, .num i], h =>
      simp only [Bool.not_false, Bool.true_and] at h
      by_cases hle : ivLe i (0, l.1 - 1) = true
      · simp only [hle, ↓reduceIte, Option.some.injEq] at h
        subst h
        trivial
      · simp [hle] at h
    | [], h | [_], h => simp at h
    | [.arr _, .num _, _], h => simp at h
    | [.top, _], h | [.num _, _], h | [.arr _, .top], h | [.arr _, .arr _], h
    | [.idx _ _ _, _], h | [.arr _, .idx _ _ _], h | [.rng _ _, _], h | [.arr _, .rng _ _], h =>
      simp at h
    | [.top, _, _], h | [.num _, _, _], h | [.arr _, .top, _], h
    | [.arr _, .arr _, _], h | [.idx _ _ _, _, _], h | [.arr _, .idx _ _ _, _], h
    | [.rng _ _, _, _], h | [.arr _, .rng _ _, _], h => simp at h
    | _ :: _ :: _ :: _ :: _, h => simp at h
  simp only [hix, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hup : (f == "array_update") = true
  · simp only [hup, ↓reduceIte] at h
    have hf : f = "array_update" := by simpa using hup
    subst hf
    unfold idxXfer at h
    match avs, h, hm with
    | [.arr l, .num i, c], h, hm =>
      obtain ⟨x, y, z, rfl, ⟨k, hk, hkl⟩, -, -⟩ := memList_three hm
      simp only [Bool.true_and] at h
      by_cases hle : ivLe i (0, l.1 - 1) = true
      · simp only [hle, ↓reduceIte, Option.some.injEq] at h
        subst h
        exact ⟨k, by rw [hH.update x y z v hb, hk], hkl⟩
      · simp [hle] at h
    | [], h, _ | [_], h, _ => simp at h
    | [.arr _, .num _], h, _ => simp at h
    | [.top, _], h, _ | [.num _, _], h, _ | [.arr _, .top], h, _
    | [.arr _, .arr _], h, _ | [.idx _ _ _, _], h, _ | [.arr _, .idx _ _ _], h, _
    | [.rng _ _, _], h, _ | [.arr _, .rng _ _], h, _ => simp at h
    | [.top, _, _], h, _ | [.num _, _, _], h, _ | [.arr _, .top, _], h, _
    | [.arr _, .arr _, _], h, _ | [.idx _ _ _, _, _], h, _ | [.arr _, .idx _ _ _, _], h, _
    | [.rng _ _, _, _], h, _ | [.arr _, .rng _ _, _], h, _ =>
      simp at h
    | _ :: _ :: _ :: _ :: _, h, _ => simp at h
  simp only [hup, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hop : opaquePartial f = true
  · simp [hop] at h
  simp only [hop, Bool.false_eq_true, ↓reduceIte] at h
  cases hs : sums.lookup f with
  | none =>
    simp only [hs] at h
    exact defaultXfer_result hH h hm hb
  | some pp =>
    obtain ⟨pre, post⟩ := pp
    simp only [hs] at h
    by_cases hle : leList avs pre = true
    · simp only [hle, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact hH.sums f pre post hs vs v (memList_le hm hle) hd hb
    · simp [hle] at h

/-- The standard specification is sound for the Rust guards under `HeadSem`, and under
    `LogicSem` when it refines by Boolean guards. -/
theorem stdSpec_sound {bi : Builtins} {sums : List (String × (List AV × AV))} {ann : AEnv}
    {logic : Bool} (hH : HeadSem bi sums)
    (hL : logic = true → LogicSem bi := by intro h; cases h) :
    Sound rustGuard (stdSpec sums ann logic) bi where
  deep := hH.deep
  guard := fun _ _ _ _ h hm => stdXfer_guard h hm
  result := fun _ _ _ _ _ h hm hd hb => stdXfer_result hH h hm hd hb
  relGuard := fun _ _ _ _ _ h hm hr => stdXrel_guard h hm hr
  relResult := fun _ _ _ _ _ _ h hm _ _ hb => stdXrel_result hH h hm hb
  cmp := hH.cmp
  len := hH.len
  add := fun f x y v m n hf hg hb hx hy => by
    have hs := splitHead_fst_of_isAddHead hf
    have := hH.arith f x y v m n (by rw [hs]; rfl) hg hb hx hy
    rwa [hs] at this
  logic := hL

/-- A typed literal the checker accepts with the standard specification fails no Rust guard
    under `denote'`: from every environment in `Γ` with no control-flow value, at every
    fuel, its run with the guarded table `guardBi rustGuard bi` is its run with `bi`, and a
    value it returns lies in `a`. -/
theorem checkT_rust_sound {bi : Builtins} {sums : List (String × (List AV × AV))}
    {ann : AEnv} {logic : Bool} (hH : HeadSem bi sums)
    (hL : logic = true → LogicSem bi := by intro h; cases h) {e : TExpr} {Γ Γ' : AEnv}
    {a : AV} (h : checkT (stdSpec sums ann logic) Γ e = some (a, Γ')) (fuel : Nat) {env : Env}
    (hΓ : Sat Γ env) (hN : Env.NoControlFlow env) :
    denote' (guardBi rustGuard bi) fuel e.erase env = denote' bi fuel e.erase env ∧
      ∀ v env', denote' bi fuel e.erase env = (.val v, env') → v.isControlFlow = false →
        a.Mem v :=
  checkT_sound (stdSpec_sound hH hL) h fuel hΓ hN

/-! ## Summaries of the crate's functions -/

/-- The crate's definitions (name, parameters, body) read by the builtin table: a call of a
    defined function on arguments free of control flow that the table answers with `v` is
    answered by a run of its body from `paramEnv` that returns `v`. -/
def DefsSem (bi : Builtins) (defs : List (String × List String × ImpExpr)) : Prop :=
  ∀ g ps body, defs.lookup g = some (ps, body) → ∀ vs v,
    (∀ w ∈ vs, w.deepNoControlFlow = true) → bi g vs = some v →
    ∃ fuel e, denote' bi fuel body (paramEnv ps vs) = (.val v, e)

/-- The check of a list of summaries against the bodies of `defs`: each summary
    `(g, (pre, post))` is checked with the summaries after it in the list, the body of `g`
    accepted from its parameters at `pre` without facts with a value included in `post`
    (loop annotation `ann g`). A callee's summary comes after its callers'; a call of a
    function without a summary in the rest, a recursive call among them, is read as an
    unknown head. -/
def checkSums (defs : List (String × List String × ImpExpr)) (ann : String → AEnv)
    (logic : Bool) : List (String × (List AV × AV)) → Bool
  | [] => true
  | (g, (pre, post)) :: rest => checkSums defs ann logic rest &&
    match defs.lookup g with
    | some (ps, body) =>
      match check (stdSpec rest (ann g) logic) [] (ps.zip (pre.map AV.strip)) body with
      | some (a, _) => a.le post
      | none => false
    | none => false

/-- Summaries that `checkSums` accepts hold: from the semantics of the heads without
    summaries and the reading of the crate's definitions by the table, `HeadSem` holds with
    the summaries. -/
theorem headSem_of_checkSums {bi : Builtins} {defs : List (String × List String × ImpExpr)}
    {ann : String → AEnv} {logic : Bool} (hH : HeadSem bi [])
    (hL : logic = true → LogicSem bi) (hD : DefsSem bi defs) :
    ∀ sums, checkSums defs ann logic sums = true → HeadSem bi sums
  | [], _ => hH
  | (g, (pre, post)) :: rest, hc => by
    simp only [checkSums, Bool.and_eq_true] at hc
    obtain ⟨hrest, hg⟩ := hc
    have ih := headSem_of_checkSums hH hL hD rest hrest
    rcases hdef : defs.lookup g with _ | ⟨ps, body⟩
    · simp [hdef] at hg
    rcases hck : check (stdSpec rest (ann g) logic) [] (ps.zip (pre.map AV.strip)) body with
      _ | ⟨a, Γ'⟩
    · simp [hdef, hck] at hg
    simp only [hdef, hck] at hg
    refine { ih with sums := fun h pre' post' hl vs v hm hd hb => ?_ }
    by_cases hh : h = g
    · subst hh
      simp only [List.lookup_cons, BEq.rfl, Option.some.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      obtain ⟨fuel, e, hr⟩ := hD h ps body hdef vs v hd hb
      have hv : v.isControlFlow = false :=
        Value.deepNoControlFlow_implies_isControlFlow_false (hH.deep h vs v hb hd)
      exact (mem_of_body (stdSpec_sound ih hL) hck hm hd hr hv).le hg
    · have hbe : (h == g) = false := by simpa using hh
      have hl' : rest.lookup h = some (pre', post') := by
        simpa only [List.lookup_cons, hbe] using hl
      exact ih.sums h pre' post' hl' vs v hm hd hb

/-- `checkT_rust_sound` with the summaries discharged by `checkSums` against the bodies of
    the crate's definitions, under the semantics of the heads without summaries. -/
theorem checkT_rust_sound_defs {bi : Builtins} {defs : List (String × List String × ImpExpr)}
    {anns : String → AEnv} {sums : List (String × (List AV × AV))} {ann : AEnv} {logic : Bool}
    (hH : HeadSem bi []) (hL : logic = true → LogicSem bi) (hD : DefsSem bi defs)
    (hs : checkSums defs anns logic sums = true) {e : TExpr} {Γ Γ' : AEnv} {a : AV}
    (h : checkT (stdSpec sums ann logic) Γ e = some (a, Γ')) (fuel : Nat) {env : Env}
    (hΓ : Sat Γ env) (hN : Env.NoControlFlow env) :
    denote' (guardBi rustGuard bi) fuel e.erase env = denote' bi fuel e.erase env ∧
      ∀ v env', denote' bi fuel e.erase env = (.val v, env') → v.isControlFlow = false →
        a.Mem v :=
  checkT_rust_sound (headSem_of_checkSums hH hL hD sums hs) hL h fuel hΓ hN

end Hax.Range

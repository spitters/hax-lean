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
not `MIN / -1`, a shift amount in `[0, w)`, an index in `[0, n)` of an array of length `n`).
A head named by an operation that panics in other ways (`unwrap`, `expect`, `panic`,
`assert`, slicing and copying between slices) has guard `false`: the checker never accepts
it. Every other head has guard `true`. The width of an operation is that of its tag
(`Add#32`, `Mul#i64`, `Sub#size`); a tag that names no machine width (a field tag) and an
untagged operation on unbounded integers (`Value.int`) do not panic; an untagged operation on
words takes the width of its first argument.

`stdSpec sums` gives the transfer functions: exact interval arithmetic on the shared domain
(`ivAddZ`, `ivSubZ`, `ivCorner`) checked against the range of the width, the divisor and
shift-amount checks, index bounds against the least array length, `len` as the length
interval, and a function of the crate through its summary `(pre, post)` in `sums`: a call is
accepted when its arguments lie in `pre`, with result in `post`.

`stdSpec_sound` instantiates `Sound` for `rustGuard` and `stdSpec sums` under `HeadSem`,
which states what the builtin table computes at these heads and that the summaries hold.

## Main definitions

* `splitHead`, `tagWidth`, `opWidth`, `rangeOf`: heads, tags and widths.
* `rustGuard`: the panic guards.
* `stdXfer`, `stdSpec`: the transfer functions.
* `HeadSem`: the semantics of the heads that the transfer functions read.

## Main results

* `stdXfer_guard`: an accepted call has its guard.
* `stdSpec_sound`: `Sound rustGuard (stdSpec sums ann) bi` under `HeadSem bi sums`.
* `checkT_rust_sound`: a checked typed literal never fails a Rust guard under `denote'`.
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
    | [arr, idx] => idxGuard arr idx
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

/-- `len` of an array: its length interval. -/
def lenXfer (avs : List AV) : Option AV :=
  match avs with
  | [.arr l] => some (.num l)
  | _ => some .top

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
  else if isIndex f then idxXfer false avs
  else if f == "array_update" then idxXfer true avs
  else if opaquePartial f then none
  else
    match sums.lookup f with
    | some (pre, post) => if leList avs pre then some post else none
    | none => if f == "len" then lenXfer avs else some .top

/-- The specification of the heads with the summaries `sums` and the loop annotation
    `ann`. -/
def stdSpec (sums : List (String × (List AV × AV))) (ann : AEnv := []) : Spec :=
  { xfer := stdXfer sums, ann }

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
    | [.num _, .arr _], h, hm =>
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
    | [.num _, .arr _], h, _ => simp at h
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
    | [_, .top], h, _ | [_, .arr _], h, _ => simp at h
  simp only [hsh, Bool.false_eq_true, ↓reduceIte] at h ⊢
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
        simp only [idxGuard, hk, hn, Bool.and_eq_true, decide_eq_true_eq]
        omega
      · simp [hle] at h
    | [], h, _ | [_], h, _ => simp at h
    | [.arr _, .num _, _], h, _ => simp at h
    | [.top, _], h, _ | [.num _, _], h, _ | [.arr _, .top], h, _
    | [.arr _, .arr _], h, _ => simp at h
    | [.top, _, _], h, _ | [.num _, _, _], h, _ | [.arr _, .top, _], h, _
    | [.arr _, .arr _, _], h, _ => simp at h
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
    | [.arr _, .arr _], h, _ => simp at h
    | [.top, _, _], h, _ | [.num _, _, _], h, _ | [.arr _, .top, _], h, _
    | [.arr _, .arr _, _], h, _ => simp at h
    | _ :: _ :: _ :: _ :: _, h, _ => simp at h
  simp only [hup, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases hop : opaquePartial f = true
  · simp [hop] at h
  · simpa using hop

/-! ## Semantics of the heads -/

/-- What the builtin table computes at the heads whose results the transfer functions
    read, and the summaries of the crate's functions: values free of control flow, the
    truth of comparisons, the exact result of a checked operation whose guard holds, the
    remainder of a nonnegative dividend by a positive divisor, the length kept by an update,
    the length returned by `len`, and each summary's postcondition on arguments in its
    precondition. -/
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
  len : ∀ arr v, bi "len" [arr] = some v → ∃ n, arr.arrayLen = some n ∧ v.toInt = some n
  sums : ∀ g pre post, sums.lookup g = some (pre, post) → ∀ vs v, MemList pre vs →
    bi g vs = some v → post.Mem v

/-- An accepted call's result lies in the transfer function's value. -/
theorem stdXfer_result {bi : Builtins} {sums : List (String × (List AV × AV))}
    (hH : HeadSem bi sums) {f : String} {avs : List AV} {a : AV} {vs : List Value} {v : Value}
    (h : stdXfer sums f avs = some a) (hm : MemList avs vs) (hb : bi f vs = some v) :
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
    | [.num _, .arr _], h, _ =>
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
    | [.num _, .arr _], h, _ => simp at h
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
    | [_, .top], h | [_, .arr _], h => simp at h
  simp only [hsh, Bool.false_eq_true, ↓reduceIte] at h
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
    | [.top, _], h | [.num _, _], h | [.arr _, .top], h | [.arr _, .arr _], h => simp at h
    | [.top, _, _], h | [.num _, _, _], h | [.arr _, .top, _], h
    | [.arr _, .arr _, _], h => simp at h
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
    | [.arr _, .arr _], h, _ => simp at h
    | [.top, _, _], h, _ | [.num _, _, _], h, _ | [.arr _, .top, _], h, _
    | [.arr _, .arr _, _], h, _ => simp at h
    | _ :: _ :: _ :: _ :: _, h, _ => simp at h
  simp only [hup, Bool.false_eq_true, ↓reduceIte] at h
  by_cases hop : opaquePartial f = true
  · simp [hop] at h
  simp only [hop, Bool.false_eq_true, ↓reduceIte] at h
  cases hs : sums.lookup f with
  | none =>
    simp only [hs] at h
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
      | [.top], h, _ | [.num _], h, _ => simp only [Option.some.injEq] at h; subst h; trivial
    · simp only [hlen, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      trivial
  | some pp =>
    obtain ⟨pre, post⟩ := pp
    simp only [hs] at h
    by_cases hle : leList avs pre = true
    · simp only [hle, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact hH.sums f pre post hs vs v (memList_le hm hle) hb
    · simp [hle] at h

/-- The standard specification is sound for the Rust guards under `HeadSem`. -/
theorem stdSpec_sound {bi : Builtins} {sums : List (String × (List AV × AV))} {ann : AEnv}
    (hH : HeadSem bi sums) : Sound rustGuard (stdSpec sums ann) bi where
  deep := hH.deep
  guard := fun _ _ _ _ h hm => stdXfer_guard h hm
  result := fun _ _ _ _ _ h hm hb => stdXfer_result hH h hm hb
  cmp := hH.cmp

/-- A typed literal the checker accepts with the standard specification fails no Rust guard
    under `denote'`: from every environment in `Γ` with no control-flow value, at every
    fuel, its run with the guarded table `guardBi rustGuard bi` is its run with `bi`, and a
    value it returns lies in `a`. -/
theorem checkT_rust_sound {bi : Builtins} {sums : List (String × (List AV × AV))}
    {ann : AEnv} (hH : HeadSem bi sums) {e : TExpr} {Γ Γ' : AEnv} {a : AV}
    (h : checkT (stdSpec sums ann) Γ e = some (a, Γ')) (fuel : Nat) {env : Env}
    (hΓ : Sat Γ env) (hN : Env.NoControlFlow env) :
    denote' (guardBi rustGuard bi) fuel e.erase env = denote' bi fuel e.erase env ∧
      ∀ v env', denote' bi fuel e.erase env = (.val v, env') → v.isControlFlow = false →
        a.Mem v :=
  checkT_sound (stdSpec_sound hH) h fuel hΓ hN

end Hax.Range

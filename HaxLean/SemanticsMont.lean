/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.FieldTag

/-!
# Montgomery-form field calls

A call of a method of the prime-field interface on elements stored in the Montgomery
representation with radix `R = 2^k` has the head `<method>#p<modulus>#r<k>`, both numbers in
decimal, for example `mul#p2013265921#r32`. An element `x` is stored as `x R mod p`.

## Main definitions

* `FieldTag.fieldTagM?` reads the method, the modulus and the radix exponent off such a head.
* `FieldTag.fieldCallMont` is its meaning on stored representatives: `add`, `sub`, `neg` and
  `double` are the canonical operations on representatives, and `mul` and `square` are the
  Montgomery products `a b R⁻¹ mod p` and `a a R⁻¹ mod p`. The encoding of a representative
  in words is that of `FieldTag.fieldCall`. A Montgomery head is defined at an odd modulus
  only.
* `FieldTag.evalMontHead?` is the value of a call of a Montgomery head on argument values.

## Main results

* `FieldTag.fieldTagM?_head`: the head `<method>#p<p>#r<k>` reads back as `(method, p, k)`.
* `FieldTag.fieldTag?_of_fieldTagM?`: `fieldTag?` rejects a Montgomery head.
* `FieldTag.montRInv_mul_pow`: `montRInv p k` is the inverse of `2^k` modulo an odd `p`.
* `FieldTag.fieldCallMont_mul`: the value of the `mul` head on two words.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax

namespace FieldTag

/-- The characters before and after the first `#r`. -/
def splitMontTag : List Char → List Char × List Char
  | [] => ([], [])
  | '#' :: 'r' :: cs => ([], cs)
  | c :: cs => (c :: (splitMontTag cs).1, (splitMontTag cs).2)

/-- When characters follow the first `#r`, the characters are those before it, `#r`, and
    those after it. -/
theorem splitMontTag_eq : ∀ cs : List Char, (splitMontTag cs).2 ≠ [] →
    cs = (splitMontTag cs).1 ++ '#' :: 'r' :: (splitMontTag cs).2
  | [], h => absurd rfl h
  | c :: cs, h => by
      by_cases hc : ∃ cs', c = '#' ∧ cs = 'r' :: cs'
      · obtain ⟨cs', rfl, rfl⟩ := hc
        rfl
      · have he := splitMontTag.eq_3 c cs (fun cs' h1 h2 => hc ⟨cs', h1, h2⟩)
        rw [he] at h ⊢
        exact congrArg (c :: ·) (splitMontTag_eq cs h)

/-- The method, the modulus and the radix exponent of the characters of a Montgomery head: the
    characters before the first `#r` read by `fieldTagChars?`, and the number of the decimal
    digits after it. -/
def fieldTagMChars? (cs : List Char) : Option (FieldMethod × Nat × Nat) :=
  if digitsOk (splitMontTag cs).2 then
    (fieldTagChars? (splitMontTag cs).1).map fun mp =>
      (mp.1, mp.2, digitsVal 0 (splitMontTag cs).2)
  else none

/-- **The method, the modulus and the radix exponent of a Montgomery head**
    `<method>#p<modulus>#r<k>`; `none` when the characters before the first `#r` are not a
    tagged head of `fieldTag?` or the characters after it are not a nonempty list of decimal
    digits. -/
def fieldTagM? (f : String) : Option (FieldMethod × Nat × Nat) := fieldTagMChars? f.toList

/-- The characters of a method name contain no `#`. -/
theorem not_hash_mem_nameChars (m : FieldMethod) : '#' ∉ m.nameChars := by
  cases m <;> decide

/-- A tagged head of `fieldTag?` contains exactly one `#`. -/
theorem count_hash_of_fieldTag? {f : String} {m : FieldMethod} {p : Nat}
    (h : fieldTag? f = some (m, p)) : f.toList.count '#' = 1 := by
  obtain ⟨ds, hf, hd, -⟩ := toList_of_fieldTag? h
  have hds : '#' ∉ ds := fun hm => by
    simp only [digitsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hd
    have := (hd.2 '#' hm).1
    simp at this
  rw [hf, List.count_append, List.count_eq_zero.mpr (not_hash_mem_nameChars m),
    List.count_cons_self, List.count_cons_of_ne (by decide), List.count_eq_zero.mpr hds]

/-- **`fieldTag?` rejects a Montgomery head**: a head `fieldTagM?` reads is not a canonical
    tagged head. -/
theorem fieldTag?_of_fieldTagM? {f : String} {m : FieldMethod} {p k : Nat}
    (h : fieldTagM? f = some (m, p, k)) : fieldTag? f = none := by
  unfold fieldTagM? fieldTagMChars? at h
  split at h
  · rename_i hd
    obtain ⟨mp, hmp, -⟩ := Option.map_eq_some_iff.mp h
    have hne : (splitMontTag f.toList).2 ≠ [] := by
      intro h0
      rw [h0] at hd
      cases hd
    have hcs := splitMontTag_eq _ hne
    have hh : '#' ∈ (splitMontTag f.toList).1 := by
      have hm' : fieldTag? (String.ofList (splitMontTag f.toList).1) = some (mp.1, mp.2) := by
        simpa [fieldTag?, String.toList_ofList] using hmp
      simpa [String.toList_ofList] using mem_toList_of_fieldTag? hm'
    rcases hc : fieldTag? f with _ | ⟨m', p'⟩
    · rfl
    · have h1 := count_hash_of_fieldTag? hc
      rw [hcs, List.count_append, List.count_cons_self] at h1
      have := List.count_pos_iff.mpr hh
      omega
  · cases h

/-- **The inverse of the radix `2^k` modulo an odd `p`**: `((p + 1) / 2)^k mod p`, the half
    of `p + 1` being the inverse of `2` modulo `p`. -/
def montRInv (p k : Nat) : Nat := ((p + 1) / 2) ^ k % p

/-- At an odd modulus, `montRInv p k` is the inverse of `2^k` modulo `p`. -/
theorem montRInv_mul_pow {p : Nat} (hp : p % 2 = 1) (k : Nat) :
    montRInv p k * 2 ^ k % p = 1 % p := by
  have h2 : (p + 1) / 2 * 2 = p + 1 := by omega
  rw [montRInv, Nat.mod_mul_mod, ← Nat.mul_pow, h2, Nat.pow_mod]
  simp only [Nat.add_mod_left]
  rw [← Nat.pow_mod, Nat.one_pow]

/-- **The value of a method on Montgomery representatives** `a` and `b` at the modulus `p`
    and the radix `2^k`: the Montgomery products `a b R⁻¹ mod p` for `mul` and
    `a a R⁻¹ mod p` for `square`, with `R⁻¹ = montRInv p k`, and the canonical value
    `fieldVal` otherwise. -/
def fieldValMont (m : FieldMethod) (p k a b : Nat) : Nat :=
  match m with
  | .mul => a * b * montRInv p k % p
  | .square => a * a * montRInv p k % p
  | .add | .sub | .neg | .double => fieldVal m p a b

/-- The arm of a Montgomery head of `m` at `p` and `2^k` on the representatives `a` and `b`
    below `p`, at a modulus below `2^64`. -/
def fieldArmMont (m : FieldMethod) (p k a b : Nat) : Option Value :=
  if a < p ∧ (m.binary = true → b < p) then some (.int (fieldValMont m p k a b)) else none

/-- The arm of a Montgomery head of `m` at a modulus `p ≥ 2^64` and `2^k` on the
    representatives `a` and `b` below `p`, with the limbs of the value in `fieldLimbs p`
    words. -/
def fieldArmWideMont (m : FieldMethod) (p k a b : Nat) : Option Value :=
  if a < p ∧ (m.binary = true → b < p) then
    some (.array (limbsOf (fieldLimbs p) (fieldValMont m p k a b)))
  else none

/-- **The value of a Montgomery head** of the method `m` at an odd modulus `p` and the radix
    `2^k` on the argument values `args`, in the encoding of `fieldCall`: at a modulus below
    `2^64` on integers, at a modulus `p ≥ 2^64` on arrays of `fieldLimbs p` limbs, the value
    `fieldValMont` on representatives below `p`; no value at an even modulus or otherwise. -/
def fieldCallMont (m : FieldMethod) (p k : Nat) : List Value → Option Value
  | [.int a, .int b] =>
      if p % 2 = 1 ∧ p < 2 ^ 64 ∧ m.binary = true ∧ 0 ≤ a ∧ 0 ≤ b then
        fieldArmMont m p k a.toNat b.toNat
      else none
  | [.int a] =>
      if p % 2 = 1 ∧ p < 2 ^ 64 ∧ m.binary = false ∧ 0 ≤ a then fieldArmMont m p k a.toNat 0
      else none
  | [.array xs, .array ys] =>
      if p % 2 = 1 ∧ 2 ^ 64 ≤ p ∧ m.binary = true ∧ xs.length = fieldLimbs p ∧
          ys.length = fieldLimbs p then
        (limbsDec xs).bind fun a => (limbsDec ys).bind fun b => fieldArmWideMont m p k a b
      else none
  | [.array xs] =>
      if p % 2 = 1 ∧ 2 ^ 64 ≤ p ∧ m.binary = false ∧ xs.length = fieldLimbs p then
        (limbsDec xs).bind fun a => fieldArmWideMont m p k a 0
      else none
  | _ => none

/-- **The value of a call of a Montgomery head** `f` on the argument values `args`:
    `fieldCallMont` at the method, the modulus and the radix exponent `fieldTagM?` reads off
    `f`, and no value at a head `fieldTagM?` does not read. -/
def evalMontHead? (f : String) (args : List Value) : Option Value :=
  match fieldTagM? f with
  | some (m, p, k) => fieldCallMont m p k args
  | none => none

/-- At an odd modulus below `2^64`, the Montgomery head of `mul` on two representatives below
    the modulus is their Montgomery product. -/
theorem fieldCallMont_mul {p k a b : Nat} (hp : p % 2 = 1) (hp64 : p < 2 ^ 64) (ha : a < p)
    (hb : b < p) :
    fieldCallMont .mul p k [.int a, .int b] = some (.int (a * b * montRInv p k % p : Nat)) := by
  rw [fieldCallMont, ite_eq_left ⟨hp, hp64, rfl, by omega, by omega⟩, Int.toNat_natCast,
    Int.toNat_natCast, fieldArmMont, ite_eq_left ⟨ha, fun _ => hb⟩]
  rfl

/-- Test: at the modulus `13` and the radix `2^4`, the Montgomery product of `5` and `6` is
    `5 · 6 · 16⁻¹ mod 13 = 10`. -/
theorem fieldCallMont_mul_13 : fieldCallMont .mul 13 4 [.int 5, .int 6] = some (.int 10) := by
  rfl

/-- `digitsVal` is `Nat.ofDigitChars` in base `10`. -/
theorem digitsVal_eq_ofDigitChars (acc : Nat) (cs : List Char) :
    digitsVal acc cs = Nat.ofDigitChars 10 cs acc := by
  induction cs generalizing acc with
  | nil => exact Nat.ofDigitChars_nil.symm
  | cons c cs ih => exact (ih _).trans Nat.ofDigitChars_cons.symm

/-- The digits of `toString n` evaluate to `n` under `digitsVal`. -/
theorem digitsVal_toDigits (n : Nat) : digitsVal 0 (Nat.toDigits 10 n) = n := by
  rw [digitsVal_eq_ofDigitChars, Nat.ofDigitChars_ten_toDigits]

/-- The digits of `toString n` are a nonempty list of decimal digits. -/
theorem digitsOk_toDigits (n : Nat) : digitsOk (Nat.toDigits 10 n) = true := by
  simp only [digitsOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, decide_eq_true_eq]
  refine ⟨List.ne_nil_of_length_pos Nat.length_toDigits_pos, fun c hc => ?_⟩
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  simp [Char.isDigit] at this
  grind [Char.toNat, UInt32.le_iff_toNat_le]

/-- Before characters without `#`, `splitMontTag` keeps them in front. -/
theorem splitMontTag_append {xs : List Char} (h : '#' ∉ xs) (ys : List Char) :
    splitMontTag (xs ++ ys) = (xs ++ (splitMontTag ys).1, (splitMontTag ys).2) := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ '#' := fun e => h (e ▸ List.mem_cons_self)
    have h' : '#' ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    rw [List.cons_append, splitMontTag.eq_3 c _ (fun _ e _ => hc e), ih h']
    rfl

/-- `splitMontTag` passes over `#p`. -/
theorem splitMontTag_hash_p (ys : List Char) :
    splitMontTag ('#' :: 'p' :: ys) =
      ('#' :: 'p' :: (splitMontTag ys).1, (splitMontTag ys).2) := by
  rw [splitMontTag.eq_3 '#' _ (fun _ _ e => by cases e),
    splitMontTag.eq_3 'p' _ (fun _ e _ => by cases e)]

/-- Before characters without `#`, `splitTag` keeps them in front. -/
theorem splitTag_append {xs : List Char} (h : '#' ∉ xs) (ys : List Char) :
    splitTag (xs ++ ys) = (xs ++ (splitTag ys).1, (splitTag ys).2) := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ '#' := fun e => h (e ▸ List.mem_cons_self)
    have h' : '#' ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    rw [List.cons_append, splitTag.eq_3 c _ (fun _ e _ => hc e), ih h']
    rfl

/-- The method named by the characters of a method name is the method. -/
theorem ofChars?_nameChars (m : FieldMethod) : FieldMethod.ofChars? m.nameChars = some m := by
  cases m <;> decide

/-- `fieldTagChars?` reads the method and the modulus off `<method>#p<p>`, the modulus
    written by `Nat.toDigits`. -/
theorem fieldTagChars?_head (m : FieldMethod) (p : Nat) :
    fieldTagChars? (m.nameChars ++ '#' :: 'p' :: Nat.toDigits 10 p) = some (m, p) := by
  unfold fieldTagChars?
  rw [splitTag_append (not_hash_mem_nameChars m), splitTag.eq_2]
  simp only [List.append_nil, digitsOk_toDigits, if_true, ofChars?_nameChars, Option.map_some,
    digitsVal_toDigits]

/-- **The Montgomery heads round-trip**: `fieldTagM?` reads the method, the modulus and the
    radix exponent back off the head `<method>#p<p>#r<k>`, both numbers written by
    `toString`. -/
theorem fieldTagM?_head (m : FieldMethod) (p k : Nat) :
    fieldTagM? (String.ofList m.nameChars ++ "#p" ++ toString p ++ "#r" ++ toString k) =
      some (m, p, k) := by
  have hs : ∀ n : Nat, (toString n).toList = Nat.toDigits 10 n := fun _ => Nat.toList_repr
  have hl : (String.ofList m.nameChars ++ "#p" ++ toString p ++ "#r" ++ toString k).toList =
      m.nameChars ++ '#' :: 'p' :: (Nat.toDigits 10 p ++ '#' :: 'r' :: Nat.toDigits 10 k) := by
    simp only [String.toList_append, String.toList_ofList, hs]
    simp
  have hp : '#' ∉ Nat.toDigits 10 p := fun hm => by
    have hd := digitsOk_toDigits p
    simp only [digitsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hd
    have := (hd.2 '#' hm).1
    simp at this
  rw [fieldTagM?, fieldTagMChars?, hl, splitMontTag_append (not_hash_mem_nameChars m),
    splitMontTag_hash_p, splitMontTag_append hp, splitMontTag.eq_2]
  simp only [List.append_nil, digitsOk_toDigits, if_true, fieldTagChars?_head, Option.map_some,
    digitsVal_toDigits]

/-- `evalMontHead?` at a head `fieldTagM?` reads is `fieldCallMont` of the head. -/
theorem evalMontHead?_of_fieldTagM? {f : String} {m : FieldMethod} {p k : Nat}
    (h : fieldTagM? f = some (m, p, k)) (args : List Value) :
    evalMontHead? f args = fieldCallMont m p k args := by
  unfold evalMontHead?
  rw [h]

/-- `fieldTag?` reads no method off the Montgomery head `<method>#p<p>#r<k>`. -/
theorem fieldTag?_head_mont (m : FieldMethod) (p k : Nat) :
    fieldTag? (String.ofList m.nameChars ++ "#p" ++ toString p ++ "#r" ++ toString k) = none :=
  fieldTag?_of_fieldTagM? (fieldTagM?_head m p k)

end FieldTag

end Hax

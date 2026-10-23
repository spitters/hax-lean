/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Value

/-!
# Modulus-tagged field calls

A call of a method of the prime-field interface at a concrete field has the head
`<method>#p<modulus in decimal>`, for example `mul#p2013265921`. `FieldTag.fieldTag?` reads the
method and the modulus off a head. `FieldTag.fieldCall` is the meaning of a tagged head on the
canonical representatives of the field. At a modulus below `2^64` an element is one word, the
integer of its canonical representative. At a modulus `p ≥ 2^64` an element is an array of
`n = FieldTag.fieldLimbs p` words, the least `n` with `p ≤ 2^(64 n)`: the little-endian limbs
`FieldTag.limbsOf n a` of its canonical representative `a < p`, the word `i` holding
`a / 2^(64 i) mod 2^64`. A tagged head is defined on arguments below the modulus, with the value of
the field operation in the same encoding, and undefined otherwise.
-/

@[expose] public section

namespace Hax

namespace FieldTag

/-- The tagged methods of the prime-field interface. -/
inductive FieldMethod where
  | add | sub | mul | neg | square | double
  deriving DecidableEq, Repr

namespace FieldMethod

/-- The characters of the name of a method. -/
def nameChars : FieldMethod → List Char
  | .add => ['a', 'd', 'd']
  | .sub => ['s', 'u', 'b']
  | .mul => ['m', 'u', 'l']
  | .neg => ['n', 'e', 'g']
  | .square => ['s', 'q', 'u', 'a', 'r', 'e']
  | .double => ['d', 'o', 'u', 'b', 'l', 'e']

/-- A method with two arguments. -/
def binary : FieldMethod → Bool
  | .add | .sub | .mul => true
  | .neg | .square | .double => false

/-- The method with the name of the characters `s`. -/
def ofChars? (s : List Char) : Option FieldMethod :=
  [add, sub, mul, neg, square, double].find? fun m => m.nameChars == s

/-- A method read off the characters `s` has the name `s`. -/
theorem nameChars_of_ofChars? {s : List Char} {m : FieldMethod} (h : ofChars? s = some m) :
    m.nameChars = s := by
  simp only [ofChars?, List.find?] at h
  repeat' split at h
  all_goals first
    | (cases h; rename_i hb; exact beq_iff_eq.mp hb)
    | cases h

end FieldMethod

/-- The character of a decimal digit. -/
def digitChar : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'

/-- The decimal digits of `n` before the characters `acc`, in at most `fuel` steps. -/
def decDigitsAux : Nat → Nat → List Char → List Char
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
      if n < 10 then digitChar n :: acc
      else decDigitsAux fuel (n / 10) (digitChar (n % 10) :: acc)

/-- The decimal digits of a number. -/
def decDigits (n : Nat) : List Char := decDigitsAux (n + 1) n []

/-- **The head of the method `m` at the modulus `p`**: the name of the method, `#p`, and `p`
    in decimal. -/
def fieldHead (m : FieldMethod) (p : Nat) : String :=
  String.ofList (m.nameChars ++ '#' :: 'p' :: decDigits p)

/-- The number the decimal digits `cs` denote after the digits of `acc`. -/
def digitsVal (acc : Nat) : List Char → Nat
  | [] => acc
  | c :: cs => digitsVal (10 * acc + (c.toNat - 48)) cs

/-- A nonempty list of decimal digits. -/
def digitsOk (cs : List Char) : Bool :=
  !cs.isEmpty && cs.all fun c => decide (48 ≤ c.toNat ∧ c.toNat ≤ 57)

/-- The characters before and after the first `#p`. -/
def splitTag : List Char → List Char × List Char
  | [] => ([], [])
  | '#' :: 'p' :: cs => ([], cs)
  | c :: cs => (c :: (splitTag cs).1, (splitTag cs).2)

/-- When characters follow the first `#p`, the characters are those before it, `#p`, and
    those after it. -/
theorem splitTag_eq : ∀ cs : List Char, (splitTag cs).2 ≠ [] →
    cs = (splitTag cs).1 ++ '#' :: 'p' :: (splitTag cs).2
  | [], h => absurd rfl h
  | c :: cs, h => by
      by_cases hc : ∃ cs', c = '#' ∧ cs = 'p' :: cs'
      · obtain ⟨cs', rfl, rfl⟩ := hc
        rfl
      · have he := splitTag.eq_3 c cs (fun cs' h1 h2 => hc ⟨cs', h1, h2⟩)
        rw [he] at h ⊢
        exact congrArg (c :: ·) (splitTag_eq cs h)

/-- The method and the modulus of the characters of a head: the method named before the
    first `#p` and the number of the decimal digits after it. -/
def fieldTagChars? (cs : List Char) : Option (FieldMethod × Nat) :=
  if digitsOk (splitTag cs).2 then
    (FieldMethod.ofChars? (splitTag cs).1).map fun m => (m, digitsVal 0 (splitTag cs).2)
  else none

/-- **The method and the modulus of a head**: the method named before the first `#p` and the
    number of the decimal digits after it; `none` when no method has the name or the
    characters after `#p` are not a nonempty list of decimal digits. -/
def fieldTag? (f : String) : Option (FieldMethod × Nat) := fieldTagChars? f.toList

/-- **A tagged head is the name of its method, `#p` and the decimal digits of its
    modulus.** -/
theorem toList_of_fieldTag? {f : String} {m : FieldMethod} {p : Nat}
    (h : fieldTag? f = some (m, p)) :
    ∃ ds, f.toList = m.nameChars ++ '#' :: 'p' :: ds ∧ digitsOk ds = true ∧
      p = digitsVal 0 ds := by
  unfold fieldTag? fieldTagChars? at h
  split at h
  · rename_i hd
    obtain ⟨m', hm', he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hne : (splitTag f.toList).2 ≠ [] := by
      intro h0
      rw [h0] at hd
      cases hd
    refine ⟨(splitTag f.toList).2, ?_, hd, rfl⟩
    rw [FieldMethod.nameChars_of_ofChars? hm']
    exact splitTag_eq _ hne
  · cases h

/-- A tagged head contains `#`. -/
theorem mem_toList_of_fieldTag? {f : String} {m : FieldMethod} {p : Nat}
    (h : fieldTag? f = some (m, p)) : '#' ∈ f.toList := by
  obtain ⟨ds, hf, -⟩ := toList_of_fieldTag? h
  rw [hf]
  simp

/-- **The value of a method** on the canonical representatives `a` and `b` at the modulus
    `p`; a method with one argument does not read `b`. -/
def fieldVal (m : FieldMethod) (p a b : Nat) : Nat :=
  match m with
  | .add => (a + b) % p
  | .sub => (a + p - b) % p
  | .mul => (a * b) % p
  | .neg => (p - a) % p
  | .square => (a * a) % p
  | .double => (2 * a) % p

/-- The value of a method at a positive modulus is below the modulus. -/
theorem fieldVal_lt (m : FieldMethod) {p : Nat} (hp : 0 < p) (a b : Nat) :
    fieldVal m p a b < p := by
  cases m <;> exact Nat.mod_lt _ hp

/-- The number of `64`-bit words of the binary digits of `q`, in at most `fuel` steps. -/
def wordsAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, q => if q = 0 then 0 else wordsAux fuel (q / 2 ^ 64) + 1

/-- With at least `q` steps, `q` is below `2^(64 · wordsAux fuel q)`. -/
theorem lt_pow_wordsAux : ∀ (fuel q : Nat), q ≤ fuel → q < 2 ^ (64 * wordsAux fuel q)
  | 0, q, h => by simp only [wordsAux]; omega
  | fuel + 1, q, h => by
      simp only [wordsAux]
      split
      · omega
      · rename_i hq
        have hd : q / 2 ^ 64 ≤ fuel := by
          have : q / 2 ^ 64 < q := Nat.div_lt_self (by omega) (by decide)
          omega
        have ih := lt_pow_wordsAux fuel (q / 2 ^ 64) hd
        rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
        exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64)).mp ih

/-- **The number of limbs of an element at the modulus `p`**: the number of `64`-bit words of
    `p - 1`, the least `n` with `p ≤ 2^(64 n)`. -/
def fieldLimbs (p : Nat) : Nat := wordsAux p (p - 1)

/-- The modulus is at most `2^(64 · fieldLimbs p)`. -/
theorem le_pow_fieldLimbs (p : Nat) : p ≤ 2 ^ (64 * fieldLimbs p) := by
  have := lt_pow_wordsAux p (p - 1) (by omega)
  unfold fieldLimbs
  omega

/-- **The little-endian limbs of `a`** in `n` words: the word `i` holds
    `a / 2^(64 i) mod 2^64`. -/
def limbsOf : Nat → Nat → List Value
  | 0, _ => []
  | n + 1, a => .int (a % 2 ^ 64 : Nat) :: limbsOf n (a / 2 ^ 64)

/-- There are `n` limbs in `n` words. -/
theorem length_limbsOf : ∀ (n a : Nat), (limbsOf n a).length = n
  | 0, _ => rfl
  | n + 1, a => by simp [limbsOf, length_limbsOf n]

/-- A limb is the integer of a number below `2^64`. -/
theorem limbsOf_word : ∀ (n a : Nat), ∀ v ∈ limbsOf n a, ∃ r : Nat, v = .int r ∧ r < 2 ^ 64
  | 0, _, v, h => by simp [limbsOf] at h
  | n + 1, a, v, h => by
      simp only [limbsOf, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨_, rfl, Nat.mod_lt _ (by decide)⟩
      · exact limbsOf_word n _ v h

/-- **The number of a list of little-endian limbs**: defined when every value is the integer of
    a number below `2^64`. -/
def limbsDec : List Value → Option Nat
  | [] => some 0
  | .int l :: vs =>
      if 0 ≤ l ∧ l < 2 ^ 64 then (limbsDec vs).map fun r => l.toNat + 2 ^ 64 * r else none
  | _ :: _ => none

/-- The limbs of `a` in `n` words denote `a mod 2^(64 n)`. -/
theorem limbsDec_limbsOf : ∀ (n a : Nat), limbsDec (limbsOf n a) = some (a % 2 ^ (64 * n))
  | 0, a => by simp [limbsOf, limbsDec, Nat.mod_one]
  | n + 1, a => by
      have hl : ((a % 2 ^ 64 : Nat) : Int) < 2 ^ 64 := by
        exact_mod_cast Nat.mod_lt _ (by decide)
      simp only [limbsOf, limbsDec, limbsDec_limbsOf n, Option.map_some, Int.toNat_natCast,
        ite_eq_left (And.intro (Int.natCast_nonneg _) hl)]
      rw [Nat.mul_succ, Nat.add_comm (64 * n) 64, Nat.pow_add, Nat.mod_mul]

/-- **The arm of the head of `m` at a modulus `p ≥ 2^64`** on the numbers `a` and `b`: defined
    when `a`, and `b` for a method with two arguments, is below `p`, with the limbs of the value
    `fieldVal m p a b` in `fieldLimbs p` words. -/
def fieldArmWide (m : FieldMethod) (p a b : Nat) : Option Value :=
  if a < p ∧ (m.binary = true → b < p) then
    some (.array (limbsOf (fieldLimbs p) (fieldVal m p a b)))
  else none

/-- The argument values of a call of a method on the limbs of the numbers `a` and `b` in `n`
    words. -/
def fieldArgsWide (m : FieldMethod) (n a b : Nat) : List Value :=
  if m.binary then [.array (limbsOf n a), .array (limbsOf n b)] else [.array (limbsOf n a)]

/-- The argument values of a call of a method on the numbers `a` and `b`. -/
def fieldArgs (m : FieldMethod) (a b : Nat) : List Value :=
  if m.binary then [.int a, .int b] else [.int a]

/-- **The arm of the head of `m` at `p`** on the numbers `a` and `b`: defined when `a`, and
    `b` for a method with two arguments, is below `p`, with the value `fieldVal m p a b`. -/
def fieldArm (m : FieldMethod) (p a b : Nat) : Option Value :=
  if a < p ∧ (m.binary = true → b < p) then some (.int (fieldVal m p a b)) else none

/-- **The value of a tagged head** of the method `m` at the modulus `p` on the argument values
    `args`: at a modulus below `2^64`, on two non-negative integers for a method with two
    arguments and on one for a method with one, the arm `fieldArm`; at a modulus `p ≥ 2^64`, on
    two arrays of `fieldLimbs p` limbs for a method with two arguments and on one for a method
    with one, the arm `fieldArmWide` of the numbers `limbsDec` reads off the limbs; no value
    otherwise. -/
def fieldCall (m : FieldMethod) (p : Nat) : List Value → Option Value
  | [.int a, .int b] =>
      if p < 2 ^ 64 ∧ m.binary = true ∧ 0 ≤ a ∧ 0 ≤ b then fieldArm m p a.toNat b.toNat
      else none
  | [.int a] => if p < 2 ^ 64 ∧ m.binary = false ∧ 0 ≤ a then fieldArm m p a.toNat 0 else none
  | [.array xs, .array ys] =>
      if 2 ^ 64 ≤ p ∧ m.binary = true ∧ xs.length = fieldLimbs p ∧ ys.length = fieldLimbs p then
        (limbsDec xs).bind fun a => (limbsDec ys).bind fun b => fieldArmWide m p a b
      else none
  | [.array xs] =>
      if 2 ^ 64 ≤ p ∧ m.binary = false ∧ xs.length = fieldLimbs p then
        (limbsDec xs).bind fun a => fieldArmWide m p a 0
      else none
  | _ => none

/-- At a modulus below `2^64`, a tagged head on the argument values of the numbers `a` and
    `b` is the arm `fieldArm`. -/
theorem fieldCall_fieldArgs {m : FieldMethod} {p : Nat} (hp : p < 2 ^ 64) (a b : Nat) :
    fieldCall m p (fieldArgs m a b) = fieldArm m p a b := by
  cases m <;> simp [fieldArgs, FieldMethod.binary, fieldCall, hp, fieldArm, fieldVal]

/-- A value of the arm `fieldArm` is an integer below the modulus. -/
theorem fieldArm_lt {m : FieldMethod} {p a b : Nat} {v : Value} (h : fieldArm m p a b = some v) :
    ∃ n : Nat, v = .int n ∧ n < p := by
  unfold fieldArm at h
  split at h
  · rename_i hl
    cases h
    exact ⟨_, rfl, fieldVal_lt m (Nat.lt_of_le_of_lt (Nat.zero_le _) hl.1) _ _⟩
  · cases h

/-- A value of the arm `fieldArmWide` is the array of the limbs of a number below the modulus in
    `fieldLimbs p` words. -/
theorem fieldArmWide_lt {m : FieldMethod} {p a b : Nat} {v : Value}
    (h : fieldArmWide m p a b = some v) :
    ∃ n : Nat, v = .array (limbsOf (fieldLimbs p) n) ∧ n < p := by
  unfold fieldArmWide at h
  split at h
  · rename_i hl
    cases h
    exact ⟨_, rfl, fieldVal_lt m (Nat.lt_of_le_of_lt (Nat.zero_le _) hl.1) _ _⟩
  · cases h

/-- **A value of a tagged head is an element of the field**: at a modulus below `2^64` the
    integer of a number below the modulus; at a modulus `p ≥ 2^64` the array of the limbs of a
    number below the modulus in `fieldLimbs p` words. -/
theorem fieldCall_some {m : FieldMethod} {p : Nat} {args : List Value} {v : Value}
    (h : fieldCall m p args = some v) :
    (∃ n : Nat, v = .int n ∧ n < p ∧ p < 2 ^ 64) ∨
      (2 ^ 64 ≤ p ∧ ∃ n : Nat, v = .array (limbsOf (fieldLimbs p) n) ∧ n < p) := by
  unfold fieldCall at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨n, rfl, hn⟩ := fieldArm_lt h
      exact Or.inl ⟨n, rfl, hn, hc.1⟩
    · cases h
  · split at h
    · rename_i hc
      obtain ⟨n, rfl, hn⟩ := fieldArm_lt h
      exact Or.inl ⟨n, rfl, hn, hc.1⟩
    · cases h
  · split at h
    · rename_i hc
      obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact Or.inr ⟨hc.1, fieldArmWide_lt h⟩
    · cases h
  · split at h
    · rename_i hc
      obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact Or.inr ⟨hc.1, fieldArmWide_lt h⟩
    · cases h
  · cases h

/-- At a modulus below `2^64`, a value of a tagged head is an integer below its modulus. -/
theorem fieldCall_lt {m : FieldMethod} {p : Nat} (hp : p < 2 ^ 64) {args : List Value}
    {v : Value} (h : fieldCall m p args = some v) : ∃ n : Nat, v = .int n ∧ n < p := by
  rcases fieldCall_some h with ⟨n, hv, hn, -⟩ | ⟨hp', -⟩
  · exact ⟨n, hv, hn⟩
  · omega

/-- At a modulus `p ≥ 2^64`, a tagged head on the limbs of the numbers `a` and `b` below `p` in
    `fieldLimbs p` words is the arm `fieldArmWide`. -/
theorem fieldCall_fieldArgsWide {m : FieldMethod} {p : Nat} (hp : 2 ^ 64 ≤ p) {a b : Nat}
    (ha : a < p) (hb : b < p) :
    fieldCall m p (fieldArgsWide m (fieldLimbs p) a b) = fieldArmWide m p a b := by
  have hpow := le_pow_fieldLimbs p
  have hda := limbsDec_limbsOf (fieldLimbs p) a
  have hdb := limbsDec_limbsOf (fieldLimbs p) b
  rw [Nat.mod_eq_of_lt (by omega)] at hda hdb
  cases m <;>
    simp [fieldArgsWide, FieldMethod.binary, fieldCall, hp, length_limbsOf, hda, hdb,
      fieldArmWide, fieldVal]

end FieldTag

end Hax

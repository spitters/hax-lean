/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.FieldTag
public import HaxLean.SemanticsMont
public import HaxLean.Semantics

/-!
# Montgomery-form field calls in the `u64` table

The lemmas of the canonical tagged heads `<method>#p<modulus>` in `HaxLean.FieldTag` and
`HaxLean.Semantics`, stated for the Montgomery heads `<method>#p<modulus>#r<k>` of
`HaxLean.SemanticsMont`.

## Main definitions

* `FieldTag.fieldHeadB`: a head that `fieldTag?` or `fieldTagM?` reads.

## Main results

* `FieldTag.fieldCallMont_some`: a value of a Montgomery head is an element of the field, in the
  encoding of `fieldCall`.
* `FieldTag.fieldArmMont_lt`, `FieldTag.fieldArmWideMont_lt`: the values of the arms.
* `FieldTag.mem_hash_of_fieldTagM?`: a Montgomery head contains `#`.
* `FieldTag.toList_of_fieldTagM?`: a Montgomery head is the method name, `#p` and further
  characters.
* `FieldTag.widthArrayOps_of_fieldTagM?`: no array operation has a Montgomery head.
* `hax64WordOps_of_fieldTagM?`, `hax64Builtins_of_fieldTagM?`: the `u64` table at a Montgomery
  head is `fieldCallMont`.
* `hax64Builtins_fieldArgsMont`, `hax64Builtins_fieldArgsWideMont`: the `u64` table on the
  argument values of numbers is the arm of the head.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax

namespace FieldTag

/-- The value of a method on Montgomery representatives at a positive modulus is below the
    modulus. -/
theorem fieldValMont_lt (m : FieldMethod) {p : Nat} (hp : 0 < p) (k a b : Nat) :
    fieldValMont m p k a b < p := by
  cases m
  all_goals first
    | exact Nat.mod_lt _ hp
    | exact fieldVal_lt _ hp _ _

/-- A value of the arm `fieldArmMont` is an integer below the modulus. -/
theorem fieldArmMont_lt {m : FieldMethod} {p k a b : Nat} {v : Value}
    (h : fieldArmMont m p k a b = some v) : ∃ n : Nat, v = .int n ∧ n < p := by
  unfold fieldArmMont at h
  split at h
  · rename_i hl
    cases h
    exact ⟨_, rfl, fieldValMont_lt m (Nat.lt_of_le_of_lt (Nat.zero_le _) hl.1) _ _ _⟩
  · cases h

/-- A value of the arm `fieldArmWideMont` is the array of the limbs of a number below the
    modulus in `fieldLimbs p` words. -/
theorem fieldArmWideMont_lt {m : FieldMethod} {p k a b : Nat} {v : Value}
    (h : fieldArmWideMont m p k a b = some v) :
    ∃ n : Nat, v = .array (limbsOf (fieldLimbs p) n) ∧ n < p := by
  unfold fieldArmWideMont at h
  split at h
  · rename_i hl
    cases h
    exact ⟨_, rfl, fieldValMont_lt m (Nat.lt_of_le_of_lt (Nat.zero_le _) hl.1) _ _ _⟩
  · cases h

/-- **A value of a Montgomery head is an element of the field**: at a modulus below `2^64` the
    integer of a number below the modulus; at a modulus `p ≥ 2^64` the array of the limbs of a
    number below the modulus in `fieldLimbs p` words. -/
theorem fieldCallMont_some {m : FieldMethod} {p k : Nat} {args : List Value} {v : Value}
    (h : fieldCallMont m p k args = some v) :
    (∃ n : Nat, v = .int n ∧ n < p ∧ p < 2 ^ 64) ∨
      (2 ^ 64 ≤ p ∧ ∃ n : Nat, v = .array (limbsOf (fieldLimbs p) n) ∧ n < p) := by
  unfold fieldCallMont at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨n, rfl, hn⟩ := fieldArmMont_lt h
      exact Or.inl ⟨n, rfl, hn, hc.2.1⟩
    · cases h
  · split at h
    · rename_i hc
      obtain ⟨n, rfl, hn⟩ := fieldArmMont_lt h
      exact Or.inl ⟨n, rfl, hn, hc.2.1⟩
    · cases h
  · split at h
    · rename_i hc
      obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact Or.inr ⟨hc.2.1, fieldArmWideMont_lt h⟩
    · cases h
  · split at h
    · rename_i hc
      obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact Or.inr ⟨hc.2.1, fieldArmWideMont_lt h⟩
    · cases h
  · cases h

/-- At an odd modulus below `2^64`, a Montgomery head on the argument values of the numbers `a`
    and `b` is the arm `fieldArmMont`. -/
theorem fieldCallMont_fieldArgs {m : FieldMethod} {p : Nat} (hodd : p % 2 = 1)
    (hp : p < 2 ^ 64) (k a b : Nat) :
    fieldCallMont m p k (fieldArgs m a b) = fieldArmMont m p k a b := by
  cases m <;> simp [fieldArgs, FieldMethod.binary, fieldCallMont, hodd, hp, fieldArmMont,
    fieldValMont, fieldVal]

/-- At an odd modulus `p ≥ 2^64`, a Montgomery head on the limbs of the numbers `a` and `b`
    below `p` in `fieldLimbs p` words is the arm `fieldArmWideMont`. -/
theorem fieldCallMont_fieldArgsWide {m : FieldMethod} {p : Nat} (hodd : p % 2 = 1)
    (hp : 2 ^ 64 ≤ p) (k : Nat) {a b : Nat} (ha : a < p) (hb : b < p) :
    fieldCallMont m p k (fieldArgsWide m (fieldLimbs p) a b) = fieldArmWideMont m p k a b := by
  have hpow := le_pow_fieldLimbs p
  have hda := limbsDec_limbsOf (fieldLimbs p) a
  have hdb := limbsDec_limbsOf (fieldLimbs p) b
  rw [Nat.mod_eq_of_lt (by omega)] at hda hdb
  cases m <;>
    simp [fieldArgsWide, FieldMethod.binary, fieldCallMont, hodd, hp, length_limbsOf, hda, hdb,
      fieldArmWideMont, fieldValMont, fieldVal]

/-- A Montgomery head contains `#`. -/
theorem mem_hash_of_fieldTagM? {f : String} {m : FieldMethod} {p k : Nat}
    (h : fieldTagM? f = some (m, p, k)) : '#' ∈ f.toList := by
  unfold fieldTagM? fieldTagMChars? at h
  split at h
  · rename_i hd
    have hne : (splitMontTag f.toList).2 ≠ [] := by
      intro h0
      rw [h0] at hd
      cases hd
    rw [splitMontTag_eq _ hne]
    simp
  · cases h

/-- A Montgomery head of the method `m` is the name of `m`, `#p` and further characters. -/
theorem toList_of_fieldTagM? {f : String} {m : FieldMethod} {p k : Nat}
    (h : fieldTagM? f = some (m, p, k)) :
    ∃ ds, f.toList = m.nameChars ++ '#' :: 'p' :: ds := by
  unfold fieldTagM? fieldTagMChars? at h
  split at h
  · rename_i hd
    obtain ⟨mp, hmp, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨hm, hp, -⟩ := he
    have hne : (splitMontTag f.toList).2 ≠ [] := by
      intro h0
      rw [h0] at hd
      cases hd
    have ht : fieldTag? (String.ofList (splitMontTag f.toList).1) = some (m, p) := by
      rw [← hm, ← hp]
      simpa [fieldTag?, String.toList_ofList] using hmp
    obtain ⟨ds, hds, -⟩ := toList_of_fieldTag? ht
    rw [String.toList_ofList] at hds
    refine ⟨ds ++ '#' :: 'r' :: (splitMontTag f.toList).2, ?_⟩
    calc f.toList = (splitMontTag f.toList).1 ++ '#' :: 'r' :: (splitMontTag f.toList).2 :=
          splitMontTag_eq _ hne
      _ = _ := by rw [hds]; simp
  · cases h

/-- No array operation of `widthArrayOps` has a Montgomery head. -/
theorem widthArrayOps_of_fieldTagM? {f : String} {m : FieldMethod} {p k : Nat}
    (h : fieldTagM? f = some (m, p, k)) (args : List Value) : widthArrayOps f args = none := by
  unfold widthArrayOps
  split <;> first | rfl | (subst_vars; cases h) | simp_all

/-- **A field head**: a head that `fieldTag?` reads as a method at a modulus or `fieldTagM?`
    reads as a method at a modulus and a Montgomery radix. -/
def fieldHeadB (f : String) : Bool := (fieldTag? f).isSome || (fieldTagM? f).isSome

/-- A tagged head is a field head. -/
theorem fieldHeadB_of_fieldTag? {f : String} {m : FieldMethod} {p : Nat}
    (h : fieldTag? f = some (m, p)) : fieldHeadB f = true := by
  simp [fieldHeadB, h]

/-- A Montgomery head is a field head. -/
theorem fieldHeadB_of_fieldTagM? {f : String} {m : FieldMethod} {p k : Nat}
    (h : fieldTagM? f = some (m, p, k)) : fieldHeadB f = true := by
  simp [fieldHeadB, h]

/-- A field head is a tagged head or a Montgomery head. -/
theorem fieldHeadB_iff {f : String} :
    fieldHeadB f = true ↔
      (∃ m p, fieldTag? f = some (m, p)) ∨ ∃ m p k, fieldTagM? f = some (m, p, k) := by
  unfold fieldHeadB
  rcases h1 : fieldTag? f with _ | ⟨m, p⟩ <;> rcases h2 : fieldTagM? f with _ | ⟨m', p', k'⟩ <;>
    simp

/-- A head is not a field head exactly when neither `fieldTag?` nor `fieldTagM?` reads it. -/
theorem fieldHeadB_eq_false_iff {f : String} :
    fieldHeadB f = false ↔ fieldTag? f = none ∧ fieldTagM? f = none := by
  simp [fieldHeadB, Option.isNone_iff_eq_none]

/-- A field head contains `#`. -/
theorem mem_hash_of_fieldHeadB {f : String} (h : fieldHeadB f = true) : '#' ∈ f.toList := by
  rcases fieldHeadB_iff.mp h with ⟨m, p, h⟩ | ⟨m, p, k, h⟩
  · exact mem_toList_of_fieldTag? h
  · exact mem_hash_of_fieldTagM? h

/-- No array operation of `widthArrayOps` has a field head. -/
theorem widthArrayOps_of_fieldHeadB {f : String} (h : fieldHeadB f = true) (args : List Value) :
    widthArrayOps f args = none := by
  rcases fieldHeadB_iff.mp h with ⟨m, p, h⟩ | ⟨m, p, k, h⟩
  · exact widthArrayOps_of_fieldTag? h args
  · exact widthArrayOps_of_fieldTagM? h args

end FieldTag

/-- At a Montgomery head, `hax64WordOps` is the value `FieldTag.fieldCallMont` of the head. -/
theorem hax64WordOps_of_fieldTagM? {f : String} {m : FieldTag.FieldMethod} {p k : Nat}
    (h : FieldTag.fieldTagM? f = some (m, p, k)) (args : List Value) :
    hax64WordOps f args = FieldTag.fieldCallMont m p k args := by
  unfold hax64WordOps
  rw [FieldTag.fieldTag?_of_fieldTagM? h, h]

/-- **The `u64` table answers a Montgomery head by its arm**: at a head `FieldTag.fieldTagM?`
    reads as the method `m` at an odd modulus `p` below `2^64` and the radix `2^k`, the call on
    the argument values of the numbers `a` and `b` is `FieldTag.fieldArmMont m p k a b`. -/
theorem hax64Builtins_fieldArgsMont {f : String} {m : FieldTag.FieldMethod} {p k : Nat}
    (h : FieldTag.fieldTagM? f = some (m, p, k)) (hodd : p % 2 = 1) (hp : p < 2 ^ 64)
    (a b : Nat) :
    hax64Builtins f (FieldTag.fieldArgs m a b) = FieldTag.fieldArmMont m p k a b := by
  unfold hax64Builtins
  rw [hax64WordOps_of_fieldTagM? h, FieldTag.fieldCallMont_fieldArgs hodd hp,
    FieldTag.widthArrayOps_of_fieldTagM? h]
  cases FieldTag.fieldArmMont m p k a b <;> rfl

/-- **The `u64` table answers a wide Montgomery head on limbs**: at a head
    `FieldTag.fieldTagM?` reads as the method `m` at an odd modulus `p ≥ 2^64` and the radix
    `2^k`, the call on the limbs of numbers `a` and `b` below `p` in `FieldTag.fieldLimbs p`
    words is the array of the limbs of `FieldTag.fieldValMont m p k a b`. -/
theorem hax64Builtins_fieldArgsWideMont {f : String} {m : FieldTag.FieldMethod} {p k : Nat}
    (h : FieldTag.fieldTagM? f = some (m, p, k)) (hodd : p % 2 = 1) (hp : 2 ^ 64 ≤ p)
    {a b : Nat} (ha : a < p) (hb : b < p) :
    hax64Builtins f (FieldTag.fieldArgsWide m (FieldTag.fieldLimbs p) a b) =
      some (.array (FieldTag.limbsOf (FieldTag.fieldLimbs p)
        (FieldTag.fieldValMont m p k a b))) := by
  unfold hax64Builtins
  rw [hax64WordOps_of_fieldTagM? h, FieldTag.fieldCallMont_fieldArgsWide hodd hp k ha hb]
  unfold FieldTag.fieldArmWideMont
  rw [if_pos ⟨ha, fun _ => hb⟩]
  rfl

/-- A value of the `u64` table at a Montgomery head is the value `FieldTag.fieldCallMont` of the
    head. -/
theorem hax64Builtins_of_fieldTagM? {f : String} {m : FieldTag.FieldMethod} {p k : Nat}
    (h : FieldTag.fieldTagM? f = some (m, p, k)) {args : List Value} {v : Value}
    (hv : hax64Builtins f args = some v) : FieldTag.fieldCallMont m p k args = some v := by
  unfold hax64Builtins at hv
  rw [hax64WordOps_of_fieldTagM? h, FieldTag.widthArrayOps_of_fieldTagM? h] at hv
  cases hc : FieldTag.fieldCallMont m p k args with
  | none => rw [hc] at hv; cases hv
  | some w => rw [hc] at hv; exact hv

end Hax

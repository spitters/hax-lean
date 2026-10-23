/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Runtime
public import HaxLean.Semantics
public import HaxLean.SemanticsCF

/-!
# ControlFlow freedom of the width-aware builtin tables

## Contents

1. **Bitwise builtins**: `bitwiseBuiltins`, the default builtin table extended with
   the bitwise operations on `Int`
2. **`NoControlFlow`** for the width tables and `widthAwareBuiltins`
3. **`DeepNoControlFlow`** for `panicOps`, `widthOps` and `fullBuiltins`
-/

@[expose] public section

namespace Hax

/-! ## 1. Semantic Builtins Extension

Extend `defaultBuiltins` with bitwise operations for the denotational
semantics. Compatible with pipeline correctness proofs since `Builtins`
is a parameter — adding new entries doesn't affect existing theorems. -/

/-- Extended builtins with bitwise operations.
    Falls back to `Hax.defaultBuiltins` for arithmetic/comparison. -/
def bitwiseBuiltins : Hax.Builtins
  | "Shl",    [.int a, .int b] => some (.int (↑(a.toNat <<< b.toNat)))
  | "Shr",    [.int a, .int b] => some (.int (↑(a.toNat >>> b.toNat)))
  | "BitAnd", [.int a, .int b] => some (.int (↑(a.toNat &&& b.toNat)))
  | "BitOr",  [.int a, .int b] => some (.int (↑(a.toNat ||| b.toNat)))
  | "BitXor", [.int a, .int b] => some (.int (↑(a.toNat ^^^ b.toNat)))
  | "shl",    [.int a, .int b] => some (.int (↑(a.toNat <<< b.toNat)))
  | "shr",    [.int a, .int b] => some (.int (↑(a.toNat >>> b.toNat)))
  | "bitand", [.int a, .int b] => some (.int (↑(a.toNat &&& b.toNat)))
  | "bitor",  [.int a, .int b] => some (.int (↑(a.toNat ||| b.toNat)))
  | "bitxor", [.int a, .int b] => some (.int (↑(a.toNat ^^^ b.toNat)))
  | "cast",   [v] => some v
  | f, args => Hax.defaultBuiltins f args

/-! ## 2. widthAwareBuiltins NoControlFlow

Prove that `widthAwareBuiltins` never produces ControlFlow values,
which is required by `Builtins.DeepNoControlFlow` for pipeline correctness. -/

theorem widthArithOps_noControlFlow :
    Hax.Builtins.NoControlFlow Hax.widthArithOps := by
  intro f args v h isBreak w heq; subst heq; revert h
  simp only [Hax.widthArithOps, Hax.wrapUint]
  split <;> intro h
  all_goals (first | cases h | (split at h <;> cases h))

theorem widthBitwiseOps_noControlFlow :
    Hax.Builtins.NoControlFlow Hax.widthBitwiseOps := by
  intro f args v h isBreak w heq; subst heq; revert h
  simp only [Hax.widthBitwiseOps, Hax.wrapUint]
  split <;> (intro h; cases h)

theorem widthCmpOps_noControlFlow :
    Hax.Builtins.NoControlFlow Hax.widthCmpOps := by
  intro f args v h isBreak w heq; subst heq; revert h
  simp only [Hax.widthCmpOps]
  split <;> (intro h; cases h)

theorem widthCastOps_noControlFlow :
    Hax.Builtins.NoControlFlow Hax.widthCastOps := by
  intro f args v h isBreak w heq; subst heq; revert h
  simp only [Hax.widthCastOps]
  split <;> (intro h; cases h)

theorem widthArrayOps_noControlFlow :
    Hax.Builtins.NoControlFlow Hax.widthArrayOps := by
  intro f args v h isBreak w heq; subst heq; revert h
  simp only [Hax.widthArrayOps]
  split
  · -- index with uint: vs[i]?.bind guard — result is guarded
    intro h; simp only [Option.bind] at h
    split at h
    · exact absurd h (by intro hc; cases hc)
    · -- val is not controlFlow, but h says result is controlFlow
      rename_i val _
      cases val <;> simp at h
  · -- index with int: guarded via if + bind
    intro h
    split at h
    · simp only [Option.bind] at h
      split at h
      · exact absurd h (by intro hc; cases hc)
      · rename_i val _
        cases val <;> simp at h
    · exact absurd h (by intro hc; cases hc)
  all_goals (intro h; first | cases h | ((repeat' split at h) <;> simp_all))

theorem signedArithOps_noControlFlow :
    Hax.Builtins.NoControlFlow Hax.signedArithOps := by
  intro f args v h isBreak w heq; subst heq; revert h
  simp only [Hax.signedArithOps, Hax.wrapSint]
  split <;> intro h
  all_goals (first | cases h | (split at h <;> cases h))

theorem signedCmpOps_noControlFlow :
    Hax.Builtins.NoControlFlow Hax.signedCmpOps := by
  intro f args v h isBreak w heq; subst heq; revert h
  simp only [Hax.signedCmpOps]
  split <;> (intro h; cases h)

theorem signedBitwiseOps_noControlFlow :
    Hax.Builtins.NoControlFlow Hax.signedBitwiseOps := by
  intro f args v h isBreak w heq; subst heq; revert h
  simp only [Hax.signedBitwiseOps, Hax.wrapSint]
  split <;> intro h
  all_goals (first | cases h | (split at h <;> cases h))

/-- `widthOps` never produces ControlFlow values.
    Proved via composition of NoControlFlow for each sub-helper. -/
theorem widthOps_noControlFlow :
    Hax.Builtins.NoControlFlow Hax.widthOps := by
  intro f args v h isBreak w heq; subst heq
  simp only [Hax.widthOps] at h
  -- Decompose <|> chain by case-splitting on each component
  cases ha : Hax.widthArithOps f args with
  | some va =>
    simp [ha] at h; subst h
    exact widthArithOps_noControlFlow f args _ ha isBreak w rfl
  | none =>
    simp [ha] at h
    cases hb : Hax.widthBitwiseOps f args with
    | some vb =>
      simp [hb] at h; subst h
      exact widthBitwiseOps_noControlFlow f args _ hb isBreak w rfl
    | none =>
      simp [hb] at h
      cases hc : Hax.widthCmpOps f args with
      | some vc =>
        simp [hc] at h; subst h
        exact widthCmpOps_noControlFlow f args _ hc isBreak w rfl
      | none =>
        simp [hc] at h
        cases hd : Hax.widthCastOps f args with
        | some vd =>
          simp [hd] at h; subst h
          exact widthCastOps_noControlFlow f args _ hd isBreak w rfl
        | none =>
          simp [hd] at h
          cases he : Hax.widthArrayOps f args with
          | some ve =>
            simp [he] at h; subst h
            exact widthArrayOps_noControlFlow f args _ he isBreak w rfl
          | none =>
            simp [he] at h
            cases hf : Hax.signedArithOps f args with
            | some vf =>
              simp [hf] at h; subst h
              exact signedArithOps_noControlFlow f args _ hf isBreak w rfl
            | none =>
              simp [hf] at h
              cases hg : Hax.signedCmpOps f args with
              | some vg =>
                simp [hg] at h; subst h
                exact signedCmpOps_noControlFlow f args _ hg isBreak w rfl
              | none =>
                simp [hg] at h
                exact signedBitwiseOps_noControlFlow f args _ h isBreak w rfl

/-- `widthAwareBuiltins` never produces ControlFlow values. -/
theorem widthAwareBuiltins_noControlFlow :
    Hax.Builtins.NoControlFlow Hax.widthAwareBuiltins := by
  intro f args v h isBreak w heq; subst heq
  delta Hax.widthAwareBuiltins at h
  cases hwo : Hax.widthOps f args with
  | some v' =>
    rw [hwo] at h; cases h
    exact widthOps_noControlFlow f args _ hwo isBreak w rfl
  | none =>
    rw [hwo] at h
    exact Hax.Builtins.defaultBuiltins_noControlFlow f args _ h isBreak w rfl

/-! ## 3. Panic/Unwrap Operations DeepNoControlFlow

`panicOps` returns the payload of an `option` or `result` argument, which may
itself be a ControlFlow value, so `panicOps` and `fullBuiltins` satisfy
`DeepNoControlFlow` (no ControlFlow in the output when none is in the inputs)
and not `NoControlFlow`. -/

/-- A list is deep-ControlFlow-free exactly when each of its elements is. -/
theorem deepNoControlFlowList_iff (vs : List Value) :
    Value.deepNoControlFlow.deepNoControlFlowList vs = true ↔
      ∀ v ∈ vs, v.deepNoControlFlow = true := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp [ih]

/-- `panicOps` keeps its inputs' freedom from ControlFlow values. -/
theorem panicOps_deepNoControlFlow :
    Hax.Builtins.DeepNoControlFlow Hax.panicOps := by
  intro f args v h hargs
  revert h
  simp only [Hax.panicOps]
  split <;> intro h <;> cases h <;> simp_all [Value.deepNoControlFlow]

/-- `widthOps` keeps its inputs' freedom from ControlFlow values. -/
theorem widthOps_deepNoControlFlow :
    Hax.Builtins.DeepNoControlFlow Hax.widthOps := by
  intro f args v h hargs
  simp [Hax.widthOps] at h
  rcases h with h | ⟨-, h | ⟨-, h | ⟨-, h | ⟨-, h | ⟨-, h | ⟨-, h | ⟨-, h⟩⟩⟩⟩⟩⟩⟩ <;> revert h
  · simp only [Hax.widthArithOps, Hax.wrapUint]
    split <;> intro h <;> (repeat' split at h) <;> cases h <;>
      simp_all [Value.deepNoControlFlow]
  · simp only [Hax.widthBitwiseOps, Hax.wrapUint]
    split <;> intro h <;> (repeat' split at h) <;> cases h <;>
      simp_all [Value.deepNoControlFlow]
  · simp only [Hax.widthCmpOps]
    split <;> intro h <;> (repeat' split at h) <;> cases h <;>
      simp_all [Value.deepNoControlFlow]
  · simp only [Hax.widthCastOps]
    split <;> intro h <;> (repeat' split at h) <;> cases h <;>
      simp_all [Value.deepNoControlFlow]
  · simp only [Hax.widthArrayOps]
    split <;> intro h <;> (repeat' split at h)
    all_goals first
      | (cases h; done)
      | (obtain rfl := Option.some.inj h
         simp_all [Value.deepNoControlFlow, deepNoControlFlowList_iff, or_imp, forall_and]
         try (intro x hx; rcases List.mem_or_eq_of_mem_set hx with hx | rfl <;> simp_all))
      | (simp only [Option.bind_eq_some_iff] at h
         obtain ⟨a, ha, hm⟩ := h
         simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
           Value.deepNoControlFlow, deepNoControlFlowList_iff] at hargs
         have := hargs.1 a (List.mem_of_getElem? ha)
         split at hm <;> cases hm
         assumption)
      | (simp only [Option.map_eq_some_iff] at h
         obtain ⟨a, ha, rfl⟩ := h
         simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
           Value.deepNoControlFlow, deepNoControlFlowList_iff] at hargs
         simp_all [Value.deepNoControlFlow, deepNoControlFlowList_iff]
         exact ⟨hargs a (List.mem_of_getElem? ha),
           fun x hx => hargs x (List.mem_of_mem_eraseIdx hx)⟩)
  · simp only [Hax.signedArithOps, Hax.wrapSint]
    split <;> intro h <;> (repeat' split at h) <;> cases h <;>
      simp_all [Value.deepNoControlFlow]
  · simp only [Hax.signedCmpOps]
    split <;> intro h <;> (repeat' split at h) <;> cases h <;>
      simp_all [Value.deepNoControlFlow]
  · simp only [Hax.signedBitwiseOps, Hax.wrapSint]
    split <;> intro h <;> (repeat' split at h) <;> cases h <;>
      simp_all [Value.deepNoControlFlow]

/-- `fullBuiltins` keeps its inputs' freedom from ControlFlow values. -/
theorem fullBuiltins_deepNoControlFlow :
    Hax.Builtins.DeepNoControlFlow Hax.fullBuiltins := by
  intro f args v h hargs
  delta Hax.fullBuiltins at h
  cases hwo : Hax.widthOps f args with
  | some v' =>
    simp [hwo] at h; subst h
    exact widthOps_deepNoControlFlow f args _ hwo hargs
  | none =>
    simp [hwo] at h
    cases hpo : Hax.panicOps f args with
    | some v' =>
      simp [hpo] at h; subst h
      exact panicOps_deepNoControlFlow f args _ hpo hargs
    | none =>
      simp [hpo] at h
      exact Hax.Builtins.defaultBuiltins_deepNoControlFlow f args _ h hargs

/-! ## 4. The runtime field operations

A modulus-tagged head of the method `m` at the modulus `p` prints as the runtime function
`fieldN m p` at a modulus below `2^64` and as `fieldW m p` at a modulus `p ≥ 2^64`
(`fieldRuntimeHead?`). On canonical representatives these functions compute the arms
`FieldTag.fieldArm` and `FieldTag.fieldArmWide` of the semantics. -/

namespace FieldTag

/-- The runtime function of the method `m` on integers: `Hax.field_<m>`; a method with one
    argument does not read its second argument. -/
def fieldN : FieldMethod → Nat → Int → Int → Int
  | .add => Hax.field_add
  | .sub => Hax.field_sub
  | .mul => Hax.field_mul
  | .neg => fun p a _ => Hax.field_neg p a
  | .square => fun p a _ => Hax.field_square p a
  | .double => fun p a _ => Hax.field_double p a

/-- The runtime function of the method `m` on limb arrays: `Hax.field_<m>_wide`; a method with
    one argument does not read its second argument. -/
def fieldW : FieldMethod → Nat → Array Int → Array Int → Array Int
  | .add => Hax.field_add_wide
  | .sub => Hax.field_sub_wide
  | .mul => Hax.field_mul_wide
  | .neg => fun p a _ => Hax.field_neg_wide p a
  | .square => fun p a _ => Hax.field_square_wide p a
  | .double => fun p a _ => Hax.field_double_wide p a

/-- On numbers, the runtime function of a method is its value `fieldVal`. -/
theorem fieldN_natCast (m : FieldMethod) (p a b : Nat) :
    fieldN m p a b = (fieldVal m p a b : Int) := by
  cases m <;> rfl

/-- **The integer runtime function of a method computes its arm**: on numbers `a`, and `b` for
    a method with two arguments, below `p`, the arm `fieldArm m p a b` is the integer
    `fieldN m p a b`. -/
theorem fieldN_eq_fieldArm {m : FieldMethod} {p a b : Nat} (ha : a < p)
    (hb : m.binary = true → b < p) :
    fieldArm m p a b = some (.int (fieldN m p a b)) := by
  rw [fieldN_natCast]
  unfold fieldArm
  rw [ite_eq_left ⟨ha, hb⟩]

/-- At a modulus below `2^64`, a tagged head on numbers below `p` is the integer runtime
    function of its method. -/
theorem fieldCall_fieldArgs_eq_fieldN {m : FieldMethod} {p : Nat} (hp : p < 2 ^ 64) {a b : Nat}
    (ha : a < p) (hb : m.binary = true → b < p) :
    fieldCall m p (fieldArgs m a b) = some (.int (fieldN m p a b)) := by
  rw [fieldCall_fieldArgs hp, fieldN_eq_fieldArm ha hb]

/-- The runtime function of a method on limb arrays is the limbs, in as many words as its first
    argument has, of the integer runtime function at the numbers of the arrays. -/
theorem fieldW_eq (m : FieldMethod) (p : Nat) (x y : Array Int) :
    fieldW m p x y = (Hax.fieldNatLimbs x.size
      (fieldN m p (Hax.fieldLimbsNat x.toList) (Hax.fieldLimbsNat y.toList)).toNat).toArray := by
  cases m <;> rfl

/-- The limbs of the semantics are the integers of the runtime limbs. -/
theorem limbsOf_eq_map : ∀ (n a : Nat), limbsOf n a = (Hax.fieldNatLimbs n a).map .int
  | 0, _ => rfl
  | n + 1, a => by
      simp only [limbsOf, Hax.fieldNatLimbs, List.map_cons, limbsOf_eq_map n]

/-- There are `n` runtime limbs in `n` words. -/
theorem length_fieldNatLimbs : ∀ (n a : Nat), (Hax.fieldNatLimbs n a).length = n
  | 0, _ => rfl
  | n + 1, a => by simp [Hax.fieldNatLimbs, length_fieldNatLimbs n]

/-- The runtime limbs of `a` in `n` words denote `a mod 2^(64 n)`. -/
theorem fieldLimbsNat_fieldNatLimbs : ∀ (n a : Nat),
    Hax.fieldLimbsNat (Hax.fieldNatLimbs n a) = a % 2 ^ (64 * n)
  | 0, a => by simp [Hax.fieldNatLimbs, Hax.fieldLimbsNat, Nat.mod_one]
  | n + 1, a => by
      simp only [Hax.fieldNatLimbs, Hax.fieldLimbsNat, Int.toNat_natCast,
        fieldLimbsNat_fieldNatLimbs n]
      rw [Nat.mul_succ, Nat.add_comm (64 * n) 64, Nat.pow_add, Nat.mod_mul]

/-- **The limb array of `a` at the modulus `p`**: its runtime limbs in `fieldLimbs p` words. -/
def limbArr (p a : Nat) : Array Int := (Hax.fieldNatLimbs (fieldLimbs p) a).toArray

/-- **The limb-array runtime function of a method computes its wide arm**: on numbers `a`, and
    `b` for a method with two arguments, below `p`, the arm `fieldArmWide m p a b` is the array
    of the integers of `fieldW m p` at the limb arrays of `a` and `b`. -/
theorem fieldW_eq_fieldArmWide {m : FieldMethod} {p a b : Nat} (ha : a < p) (hb : b < p) :
    fieldArmWide m p a b =
      some (.array ((fieldW m p (limbArr p a) (limbArr p b)).toList.map .int)) := by
  have hpow := le_pow_fieldLimbs p
  unfold fieldArmWide
  rw [ite_eq_left ⟨ha, fun _ => hb⟩, fieldW_eq]
  simp only [limbArr, List.size_toArray, List.toList_toArray, length_fieldNatLimbs,
    fieldLimbsNat_fieldNatLimbs, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ha hpow),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb hpow), fieldN_natCast, Int.toNat_natCast,
    limbsOf_eq_map]

/-- At a modulus `p ≥ 2^64`, a tagged head on the limbs of numbers below `p` is the limb-array
    runtime function of its method. -/
theorem fieldCall_fieldArgsWide_eq_fieldW {m : FieldMethod} {p : Nat} (hp : 2 ^ 64 ≤ p)
    {a b : Nat} (ha : a < p) (hb : b < p) :
    fieldCall m p (fieldArgsWide m (fieldLimbs p) a b) =
      some (.array ((fieldW m p (limbArr p a) (limbArr p b)).toList.map .int)) := by
  rw [fieldCall_fieldArgsWide hp ha hb, fieldW_eq_fieldArmWide ha hb]

end FieldTag

end Hax

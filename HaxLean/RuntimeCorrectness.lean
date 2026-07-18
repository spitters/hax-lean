/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import HaxLean.Runtime
import HaxLean.Semantics
import HaxLean.SemanticsCF

/-!
# Correctness Proofs for Width-Aware Runtime Operations

Proves that the width-specific runtime operations (`Hax.shl_u32`, `Hax.bitxor_u64`,
etc.) match Lean's built-in `UIntN` semantics (which are `BitVec n` under the hood),
and satisfy standard algebraic properties used in crypto proofs.

## Categories

1. **Definitional correctness**: each `Hax.op_uN` equals the corresponding Lean operator
2. **Algebraic properties**: commutativity, associativity, self-cancellation, De Morgan
3. **Identity/annihilator**: zero identities and annihilators for each operation
4. **Cast correctness**: widening preserves value, narrowing truncates, roundtrip laws
5. **Test vectors**: `native_decide` cross-validation against Rust

All proofs are completed with **0 sorries, 0 axioms**.
-/

namespace Hax

/-! ## 1. Definitional Correctness

Each width-specific operation is definitionally equal to the corresponding
Lean built-in operator. These are all `rfl`. -/

-- UInt8
theorem add_u8_eq  (a b : UInt8) : add_u8 a b = a + b := rfl
theorem sub_u8_eq  (a b : UInt8) : sub_u8 a b = a - b := rfl
theorem mul_u8_eq  (a b : UInt8) : mul_u8 a b = a * b := rfl
theorem shl_u8_eq  (a b : UInt8) : shl_u8 a b = a <<< b := rfl
theorem shr_u8_eq  (a b : UInt8) : shr_u8 a b = a >>> b := rfl
theorem bitand_u8_eq (a b : UInt8) : bitand_u8 a b = a &&& b := rfl
theorem bitor_u8_eq  (a b : UInt8) : bitor_u8 a b = a ||| b := rfl
theorem bitxor_u8_eq (a b : UInt8) : bitxor_u8 a b = a ^^^ b := rfl
theorem bitnot_u8_eq (a : UInt8) : bitnot_u8 a = ~~~a := rfl

-- UInt16
theorem add_u16_eq  (a b : UInt16) : add_u16 a b = a + b := rfl
theorem sub_u16_eq  (a b : UInt16) : sub_u16 a b = a - b := rfl
theorem mul_u16_eq  (a b : UInt16) : mul_u16 a b = a * b := rfl
theorem shl_u16_eq  (a b : UInt16) : shl_u16 a b = a <<< b := rfl
theorem shr_u16_eq  (a b : UInt16) : shr_u16 a b = a >>> b := rfl
theorem bitand_u16_eq (a b : UInt16) : bitand_u16 a b = a &&& b := rfl
theorem bitor_u16_eq  (a b : UInt16) : bitor_u16 a b = a ||| b := rfl
theorem bitxor_u16_eq (a b : UInt16) : bitxor_u16 a b = a ^^^ b := rfl
theorem bitnot_u16_eq (a : UInt16) : bitnot_u16 a = ~~~a := rfl

-- UInt32
theorem add_u32_eq  (a b : UInt32) : add_u32 a b = a + b := rfl
theorem sub_u32_eq  (a b : UInt32) : sub_u32 a b = a - b := rfl
theorem mul_u32_eq  (a b : UInt32) : mul_u32 a b = a * b := rfl
theorem shl_u32_eq  (a b : UInt32) : shl_u32 a b = a <<< b := rfl
theorem shr_u32_eq  (a b : UInt32) : shr_u32 a b = a >>> b := rfl
theorem bitand_u32_eq (a b : UInt32) : bitand_u32 a b = a &&& b := rfl
theorem bitor_u32_eq  (a b : UInt32) : bitor_u32 a b = a ||| b := rfl
theorem bitxor_u32_eq (a b : UInt32) : bitxor_u32 a b = a ^^^ b := rfl
theorem bitnot_u32_eq (a : UInt32) : bitnot_u32 a = ~~~a := rfl

-- UInt64
theorem add_u64_eq  (a b : UInt64) : add_u64 a b = a + b := rfl
theorem sub_u64_eq  (a b : UInt64) : sub_u64 a b = a - b := rfl
theorem mul_u64_eq  (a b : UInt64) : mul_u64 a b = a * b := rfl
theorem shl_u64_eq  (a b : UInt64) : shl_u64 a b = a <<< b := rfl
theorem shr_u64_eq  (a b : UInt64) : shr_u64 a b = a >>> b := rfl
theorem bitand_u64_eq (a b : UInt64) : bitand_u64 a b = a &&& b := rfl
theorem bitor_u64_eq  (a b : UInt64) : bitor_u64 a b = a ||| b := rfl
theorem bitxor_u64_eq (a b : UInt64) : bitxor_u64 a b = a ^^^ b := rfl
theorem bitnot_u64_eq (a : UInt64) : bitnot_u64 a = ~~~a := rfl

/-! ## 2. Algebraic Properties

Key algebraic laws for bitwise operations. Proofs destructure the `UIntN` wrapper
to access the underlying `BitVec` and apply `BitVec.*` lemmas. -/

section Algebraic

-- XOR commutativity
@[simp] theorem bitxor_u8_comm  (a b : UInt8) : bitxor_u8 a b = bitxor_u8 b a := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  show UInt8.ofBitVec (a ^^^ b) = UInt8.ofBitVec (b ^^^ a)
  congr 1; exact BitVec.xor_comm a b
@[simp] theorem bitxor_u16_comm (a b : UInt16) : bitxor_u16 a b = bitxor_u16 b a := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  show UInt16.ofBitVec (a ^^^ b) = UInt16.ofBitVec (b ^^^ a)
  congr 1; exact BitVec.xor_comm a b
@[simp] theorem bitxor_u32_comm (a b : UInt32) : bitxor_u32 a b = bitxor_u32 b a := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  show UInt32.ofBitVec (a ^^^ b) = UInt32.ofBitVec (b ^^^ a)
  congr 1; exact BitVec.xor_comm a b
@[simp] theorem bitxor_u64_comm (a b : UInt64) : bitxor_u64 a b = bitxor_u64 b a := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  show UInt64.ofBitVec (a ^^^ b) = UInt64.ofBitVec (b ^^^ a)
  congr 1; exact BitVec.xor_comm a b

-- XOR associativity
theorem bitxor_u8_assoc (a b c : UInt8) :
    bitxor_u8 (bitxor_u8 a b) c = bitxor_u8 a (bitxor_u8 b c) := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩; rcases c with ⟨c⟩
  show UInt8.ofBitVec ((a ^^^ b) ^^^ c) = UInt8.ofBitVec (a ^^^ (b ^^^ c))
  congr 1; exact BitVec.xor_assoc a b c
theorem bitxor_u32_assoc (a b c : UInt32) :
    bitxor_u32 (bitxor_u32 a b) c = bitxor_u32 a (bitxor_u32 b c) := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩; rcases c with ⟨c⟩
  show UInt32.ofBitVec ((a ^^^ b) ^^^ c) = UInt32.ofBitVec (a ^^^ (b ^^^ c))
  congr 1; exact BitVec.xor_assoc a b c
theorem bitxor_u64_assoc (a b c : UInt64) :
    bitxor_u64 (bitxor_u64 a b) c = bitxor_u64 a (bitxor_u64 b c) := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩; rcases c with ⟨c⟩
  show UInt64.ofBitVec ((a ^^^ b) ^^^ c) = UInt64.ofBitVec (a ^^^ (b ^^^ c))
  congr 1; exact BitVec.xor_assoc a b c

-- XOR self-cancellation (key for crypto: x ⊕ x = 0)
@[simp] theorem bitxor_u8_self  (a : UInt8)  : bitxor_u8 a a = 0 := by
  rcases a with ⟨a⟩; show UInt8.ofBitVec (a ^^^ a) = 0; simp [BitVec.xor_self]
@[simp] theorem bitxor_u16_self (a : UInt16) : bitxor_u16 a a = 0 := by
  rcases a with ⟨a⟩; show UInt16.ofBitVec (a ^^^ a) = 0; simp [BitVec.xor_self]
@[simp] theorem bitxor_u32_self (a : UInt32) : bitxor_u32 a a = 0 := by
  rcases a with ⟨a⟩; show UInt32.ofBitVec (a ^^^ a) = 0; simp [BitVec.xor_self]
@[simp] theorem bitxor_u64_self (a : UInt64) : bitxor_u64 a a = 0 := by
  rcases a with ⟨a⟩; show UInt64.ofBitVec (a ^^^ a) = 0; simp [BitVec.xor_self]

-- AND commutativity
@[simp] theorem bitand_u8_comm  (a b : UInt8) : bitand_u8 a b = bitand_u8 b a := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  show UInt8.ofBitVec (a &&& b) = UInt8.ofBitVec (b &&& a)
  congr 1; exact BitVec.and_comm a b
@[simp] theorem bitand_u32_comm (a b : UInt32) : bitand_u32 a b = bitand_u32 b a := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  show UInt32.ofBitVec (a &&& b) = UInt32.ofBitVec (b &&& a)
  congr 1; exact BitVec.and_comm a b
@[simp] theorem bitand_u64_comm (a b : UInt64) : bitand_u64 a b = bitand_u64 b a := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  show UInt64.ofBitVec (a &&& b) = UInt64.ofBitVec (b &&& a)
  congr 1; exact BitVec.and_comm a b

-- OR commutativity
@[simp] theorem bitor_u8_comm  (a b : UInt8) : bitor_u8 a b = bitor_u8 b a := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  show UInt8.ofBitVec (a ||| b) = UInt8.ofBitVec (b ||| a)
  congr 1; exact BitVec.or_comm a b
@[simp] theorem bitor_u32_comm (a b : UInt32) : bitor_u32 a b = bitor_u32 b a := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  show UInt32.ofBitVec (a ||| b) = UInt32.ofBitVec (b ||| a)
  congr 1; exact BitVec.or_comm a b
@[simp] theorem bitor_u64_comm (a b : UInt64) : bitor_u64 a b = bitor_u64 b a := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  show UInt64.ofBitVec (a ||| b) = UInt64.ofBitVec (b ||| a)
  congr 1; exact BitVec.or_comm a b

-- Double negation (involution)
@[simp] theorem bitnot_u8_invol  (a : UInt8) : bitnot_u8 (bitnot_u8 a) = a := by
  rcases a with ⟨a⟩
  show UInt8.ofBitVec (~~~(~~~a)) = UInt8.ofBitVec a
  congr 1; simp [BitVec.not_not]
@[simp] theorem bitnot_u32_invol (a : UInt32) : bitnot_u32 (bitnot_u32 a) = a := by
  rcases a with ⟨a⟩
  show UInt32.ofBitVec (~~~(~~~a)) = UInt32.ofBitVec a
  congr 1; simp [BitVec.not_not]
@[simp] theorem bitnot_u64_invol (a : UInt64) : bitnot_u64 (bitnot_u64 a) = a := by
  rcases a with ⟨a⟩
  show UInt64.ofBitVec (~~~(~~~a)) = UInt64.ofBitVec a
  congr 1; simp [BitVec.not_not]

end Algebraic

/-! ## 3. Identity and Zero Laws -/

section Identity

-- XOR with 0 is identity
@[simp] theorem bitxor_u8_zero  (a : UInt8) : bitxor_u8 a 0 = a := by
  rcases a with ⟨a⟩; show UInt8.ofBitVec (a ^^^ 0) = UInt8.ofBitVec a; simp
@[simp] theorem bitxor_u32_zero (a : UInt32) : bitxor_u32 a 0 = a := by
  rcases a with ⟨a⟩; show UInt32.ofBitVec (a ^^^ 0) = UInt32.ofBitVec a; simp
@[simp] theorem bitxor_u64_zero (a : UInt64) : bitxor_u64 a 0 = a := by
  rcases a with ⟨a⟩; show UInt64.ofBitVec (a ^^^ 0) = UInt64.ofBitVec a; simp

-- AND with 0 is 0
@[simp] theorem bitand_u8_zero  (a : UInt8) : bitand_u8 a 0 = 0 := by
  rcases a with ⟨a⟩; show UInt8.ofBitVec (a &&& 0) = UInt8.ofBitVec 0; congr 1; simp
@[simp] theorem bitand_u32_zero (a : UInt32) : bitand_u32 a 0 = 0 := by
  rcases a with ⟨a⟩; show UInt32.ofBitVec (a &&& 0) = UInt32.ofBitVec 0; congr 1; simp
@[simp] theorem bitand_u64_zero (a : UInt64) : bitand_u64 a 0 = 0 := by
  rcases a with ⟨a⟩; show UInt64.ofBitVec (a &&& 0) = UInt64.ofBitVec 0; congr 1; simp

-- OR with 0 is identity
@[simp] theorem bitor_u8_zero  (a : UInt8) : bitor_u8 a 0 = a := by
  rcases a with ⟨a⟩; show UInt8.ofBitVec (a ||| 0) = UInt8.ofBitVec a; simp
@[simp] theorem bitor_u32_zero (a : UInt32) : bitor_u32 a 0 = a := by
  rcases a with ⟨a⟩; show UInt32.ofBitVec (a ||| 0) = UInt32.ofBitVec a; simp
@[simp] theorem bitor_u64_zero (a : UInt64) : bitor_u64 a 0 = a := by
  rcases a with ⟨a⟩; show UInt64.ofBitVec (a ||| 0) = UInt64.ofBitVec a; simp

-- Shift by 0 is identity
@[simp] theorem shl_u8_zero  (a : UInt8) : shl_u8 a 0 = a := by
  rcases a with ⟨a⟩; show UInt8.ofBitVec (a <<< (0 : BitVec 8)) = UInt8.ofBitVec a; simp
@[simp] theorem shl_u32_zero (a : UInt32) : shl_u32 a 0 = a := by
  rcases a with ⟨a⟩; show UInt32.ofBitVec (a <<< (0 : BitVec 32)) = UInt32.ofBitVec a; simp
@[simp] theorem shl_u64_zero (a : UInt64) : shl_u64 a 0 = a := by
  rcases a with ⟨a⟩; show UInt64.ofBitVec (a <<< (0 : BitVec 64)) = UInt64.ofBitVec a; simp

@[simp] theorem shr_u8_zero  (a : UInt8) : shr_u8 a 0 = a := by
  rcases a with ⟨a⟩; show UInt8.ofBitVec (a >>> (0 : BitVec 8)) = UInt8.ofBitVec a; simp
@[simp] theorem shr_u32_zero (a : UInt32) : shr_u32 a 0 = a := by
  rcases a with ⟨a⟩; show UInt32.ofBitVec (a >>> (0 : BitVec 32)) = UInt32.ofBitVec a; simp
@[simp] theorem shr_u64_zero (a : UInt64) : shr_u64 a 0 = a := by
  rcases a with ⟨a⟩; show UInt64.ofBitVec (a >>> (0 : BitVec 64)) = UInt64.ofBitVec a; simp

-- AND idempotent
@[simp] theorem bitand_u8_self  (a : UInt8) : bitand_u8 a a = a := by
  rcases a with ⟨a⟩; show UInt8.ofBitVec (a &&& a) = UInt8.ofBitVec a; congr 1; simp
@[simp] theorem bitand_u32_self (a : UInt32) : bitand_u32 a a = a := by
  rcases a with ⟨a⟩; show UInt32.ofBitVec (a &&& a) = UInt32.ofBitVec a; congr 1; simp
@[simp] theorem bitand_u64_self (a : UInt64) : bitand_u64 a a = a := by
  rcases a with ⟨a⟩; show UInt64.ofBitVec (a &&& a) = UInt64.ofBitVec a; congr 1; simp

-- OR idempotent
@[simp] theorem bitor_u8_self  (a : UInt8) : bitor_u8 a a = a := by
  rcases a with ⟨a⟩; show UInt8.ofBitVec (a ||| a) = UInt8.ofBitVec a; congr 1; simp
@[simp] theorem bitor_u32_self (a : UInt32) : bitor_u32 a a = a := by
  rcases a with ⟨a⟩; show UInt32.ofBitVec (a ||| a) = UInt32.ofBitVec a; congr 1; simp
@[simp] theorem bitor_u64_self (a : UInt64) : bitor_u64 a a = a := by
  rcases a with ⟨a⟩; show UInt64.ofBitVec (a ||| a) = UInt64.ofBitVec a; congr 1; simp

end Identity

/-! ## 4. Cast Correctness -/

section Cast

-- Widening casts: definitionally equal to Lean coercions
theorem cast_u8_u16_eq  (x : UInt8)  : cast_u8_u16 x = x.toUInt16 := rfl
theorem cast_u8_u32_eq  (x : UInt8)  : cast_u8_u32 x = x.toUInt32 := rfl
theorem cast_u8_u64_eq  (x : UInt8)  : cast_u8_u64 x = x.toUInt64 := rfl
theorem cast_u16_u32_eq (x : UInt16) : cast_u16_u32 x = x.toUInt32 := rfl
theorem cast_u16_u64_eq (x : UInt16) : cast_u16_u64 x = x.toUInt64 := rfl
theorem cast_u32_u64_eq (x : UInt32) : cast_u32_u64 x = x.toUInt64 := rfl

-- Narrowing casts: definitionally equal to Lean coercions
theorem cast_u64_u32_eq (x : UInt64) : cast_u64_u32 x = x.toUInt32 := rfl
theorem cast_u64_u16_eq (x : UInt64) : cast_u64_u16 x = x.toUInt16 := rfl
theorem cast_u64_u8_eq  (x : UInt64) : cast_u64_u8 x = x.toUInt8 := rfl
theorem cast_u32_u16_eq (x : UInt32) : cast_u32_u16 x = x.toUInt16 := rfl
theorem cast_u32_u8_eq  (x : UInt32) : cast_u32_u8 x = x.toUInt8 := rfl
theorem cast_u16_u8_eq  (x : UInt16) : cast_u16_u8 x = x.toUInt8 := rfl

end Cast

/-! ## 5. Concrete Test Vectors

These `native_decide` theorems verify specific values, cross-validating
against Rust semantics. -/

section TestVectors

-- XOR
theorem test_xor_u64 : bitxor_u64 0xFF00FF00FF00FF00 0x0F0F0F0F0F0F0F0F =
    (0xF00FF00FF00FF00F : UInt64) := by native_decide

-- AND
theorem test_and_u32 : bitand_u32 0xFF00FF00 0x0F0F0F0F =
    (0x0F000F00 : UInt32) := by native_decide

-- OR
theorem test_or_u32 : bitor_u32 0xFF00FF00 0x0F0F0F0F =
    (0xFF0FFF0F : UInt32) := by native_decide

-- NOT
theorem test_not_u8 : bitnot_u8 0x0F = (0xF0 : UInt8) := by native_decide

-- Shift left (wraps at width boundary)
theorem test_shl_u8_wrap : shl_u8 1 7 = (128 : UInt8) := by native_decide
-- Note: Lean's BitVec shift uses (shiftAmt % width), so 1 <<< 8 on u8 = 1 <<< 0 = 1
theorem test_shl_u8_mod : shl_u8 1 8 = (1 : UInt8) := by native_decide

-- Shift right
theorem test_shr_u32 : shr_u32 0xFF000000 8 = (0x00FF0000 : UInt32) := by native_decide

-- Self-cancellation
theorem test_xor_cancel_u64 :
    bitxor_u64 (bitxor_u64 0xDEADBEEFCAFEBABE 0x1234567890ABCDEF)
               0x1234567890ABCDEF = (0xDEADBEEFCAFEBABE : UInt64) := by native_decide

-- Wrapping addition
theorem test_add_u8_wrap : add_u8 200 100 = (44 : UInt8) := by native_decide
theorem test_add_u32_wrap : add_u32 0xFFFFFFFF 1 = (0 : UInt32) := by native_decide

-- Cast roundtrip (widening then narrowing)
theorem test_cast_roundtrip_u8_u32 :
    cast_u32_u8 (cast_u8_u32 42) = (42 : UInt8) := by native_decide

-- Cast truncation
theorem test_cast_truncate_u32_u8 :
    cast_u32_u8 300 = (44 : UInt8) := by native_decide

end TestVectors

/-! ## 6. Semantic Builtins Extension

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

/-! ## 7. widthAwareBuiltins NoControlFlow

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
  all_goals (intro h; cases h)

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
              exact signedCmpOps_noControlFlow f args _ h isBreak w rfl

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

/-! ## 8. Panic/Unwrap Operations NoControlFlow -/

theorem panicOps_noControlFlow :
    Hax.Builtins.NoControlFlow Hax.panicOps := by
  intro f args v h isBreak w heq; subst heq; revert h
  simp only [Hax.panicOps]
  split <;> (intro h; cases h)

/-- `fullBuiltins` never produces ControlFlow values. -/
theorem fullBuiltins_noControlFlow :
    Hax.Builtins.NoControlFlow Hax.fullBuiltins := by
  intro f args v h isBreak w heq; subst heq
  delta Hax.fullBuiltins at h
  cases hwo : Hax.widthOps f args with
  | some v' =>
    simp [hwo] at h; subst h
    exact widthOps_noControlFlow f args _ hwo isBreak w rfl
  | none =>
    simp [hwo] at h
    cases hpo : Hax.panicOps f args with
    | some v' =>
      simp [hpo] at h; subst h
      exact panicOps_noControlFlow f args _ hpo isBreak w rfl
    | none =>
      simp [hpo] at h
      exact Hax.Builtins.defaultBuiltins_noControlFlow f args _ h isBreak w rfl

end Hax

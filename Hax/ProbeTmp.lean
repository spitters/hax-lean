import Hax.Json.Lexer
import Std.Data.String.ToInt
open Hax.Json.Lexer

theorem isDigit_bridge (c : Char) (h : c.isDigit = true) : isDigit c = true := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq]; exact h
theorem dropDigits_all (l : List Char) (h : ∀ c ∈ l, isDigit c = true) : dropDigits l = [] := by
  induction l with
  | nil => rfl
  | cons d rest ih => simp only [dropDigits, if_pos (h d (by simp))]; exact ih (fun c hc => h c (by simp [hc]))
theorem toDigits_all_digit (k : Nat) : ∀ c ∈ Nat.toDigits 10 k, isDigit c = true := fun c hc =>
  isDigit_bridge c (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)
theorem toDigits_head_ne_zero (k : Nat) (hk : k ≠ 0) : (Nat.toDigits 10 k).headD 'x' ≠ '0' := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hlt : k < 10
    · rw [Nat.toDigits_of_lt_base hlt]; simp only [List.headD_cons]
      rw [Ne, Nat.digitChar_eq_zero]; exact hk
    · rw [Nat.toDigits_of_base_le (by decide) (by omega)]
      have hne : Nat.toDigits 10 (k/10) ≠ [] := Nat.toDigits_ne_nil
      have hkd : k / 10 ≠ 0 := by omega
      have hkdlt : k / 10 < k := Nat.div_lt_self (by omega) (by decide)
      cases hh : Nat.toDigits 10 (k/10) with
      | nil => exact absurd hh hne
      | cons a as =>
        simp only [List.cons_append, List.headD_cons]
        have := ih (k/10) hkdlt hkd; rw [hh] at this; simpa using this
theorem validNumberLitL_cons_ne_minus (c : Char) (r : List Char) (hc : c ≠ '-') :
    validNumberLitL (c :: r)
      = (match validIntPart (c :: r) with | some tail => validFracExp tail | none => false) := by
  unfold validNumberLitL
  split
  · next h => exact absurd h (by simp)
  · next r' h => rw [List.cons.injEq] at h; exact absurd h.1 hc
  · rfl
theorem validNumberLitL_digits (ds : List Char) (hne : ds ≠ [])
    (hall : ∀ c ∈ ds, isDigit c = true) (hhead : ds = ['0'] ∨ ds.headD 'x' ≠ '0') :
    validNumberLitL ds = true := by
  cases ds with
  | nil => exact absurd rfl hne
  | cons d rest =>
    by_cases hd0 : d = '0'
    · rcases hhead with h1 | h2
      · rw [h1]; decide
      · exact absurd hd0 (by simpa using h2)
    · have hdd : isDigit d = true := hall d (by simp)
      have hrest : dropDigits rest = [] := dropDigits_all rest (fun c hc => hall c (by simp [hc]))
      have hdneg : d ≠ '-' := by rintro rfl; simp [isDigit] at hdd
      rw [validNumberLitL_cons_ne_minus d rest hdneg]
      have hvip : validIntPart (d :: rest) = some (dropDigits rest) := by
        unfold validIntPart; simp only [hd0, if_pos hdd]
      rw [hvip, hrest]; rfl

theorem validNumberLitL_toDigits (k : Nat) : validNumberLitL (Nat.toDigits 10 k) = true := by
  apply validNumberLitL_digits _ Nat.toDigits_ne_nil (toDigits_all_digit k)
  by_cases hk : k = 0
  · left; subst hk; decide
  · right; exact toDigits_head_ne_zero k hk

theorem validNumberLit_repr (m : Int) : validNumberLit (Int.repr m) = true := by
  unfold validNumberLit
  rw [Int.repr_eq_if]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm]
    show validNumberLitL (Nat.repr m.toNat).toList = true
    rw [Nat.toList_repr]; exact validNumberLitL_toDigits _
  · rw [if_neg hm]
    show validNumberLitL ("-" ++ Nat.repr (-m).toNat).toList = true
    rw [String.toList_append]
    have : ("-" : String).toList = ['-'] := rfl
    rw [this, Nat.toList_repr]
    -- validNumberLitL ('-' :: toDigits ...) : the '-' arm reduces to the same
    -- `validIntPart` match as the leading-digit case, which `validNumberLitL_toDigits`
    -- already establishes.
    show validNumberLitL ('-' :: Nat.toDigits 10 (-m).toNat) = true
    have hvv := validNumberLitL_toDigits (-m).toNat
    cases hcd : Nat.toDigits 10 (-m).toNat with
    | nil => exact absurd hcd Nat.toDigits_ne_nil
    | cons d rest =>
      have hdd : isDigit d = true :=
        toDigits_all_digit (-m).toNat d (by rw [hcd]; simp)
      have hdneg : d ≠ '-' := by rintro rfl; simp [isDigit] at hdd
      rw [hcd] at hvv
      rw [validNumberLitL_cons_ne_minus d rest hdneg] at hvv
      show (match validIntPart (d :: rest) with
              | some tail => validFracExp tail | none => false) = true
      exact hvv

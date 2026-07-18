/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

import HaxLean.Json.Lexer
import HaxLean.Json.Parser
import HaxLean.Json.Roundtrip
import Std.Data.String.ToInt

set_option autoImplicit false

/-!
# JSON Number Roundtrip — the `num` leaf (JSON gap 2)

The `Simple` fragment of `Hax.Json.Roundtrip` deliberately excludes `num`
because its roundtrip leaf needs two independent facts, neither of which the
no-`mathlib` project had:

* **Shape acceptance:** the serialized mantissa `Int.repr i` is an RFC 8259
  number literal (so the lexer emits a `numT` token and does not reject it).
* **Value inversion:** `parseJsonNumber (Int.repr i) = some (JsonNumber.fromInt i)`
  — a left-inverse of `Int.toString`/`Int.repr` under `String.toInt?`.

This file supplies both. The shape half proves `validNumberLit_repr`; the value
half proves `(Int.repr i).toInt? = some i` from the digit-inversion lemmas in
Lean core / Std.
-/

namespace Hax.Json.RoundtripNum

open Hax.Json.Lexer
open Hax.Json.Parser
open Hax.Json.Roundtrip

/-! ## Shape acceptance: `Int.repr i` is a valid number literal -/

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
        unfold validIntPart; simp only [if_pos hdd]
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

/-! ## Value inversion

`parseJsonNumber` inverts `Int.repr` on the integer-mantissa fragment. The
crux is the Std lemma `Int.toInt?_repr : a.repr.toInt? = some a`, so the parser's
`String.toInt?` branch recovers the mantissa exactly. -/

theorem parseJsonNumber_repr (i : Int) :
    parseJsonNumber (Int.repr i) = some (Lean.JsonNumber.fromInt i) := by
  unfold parseJsonNumber
  rw [Int.toInt?_repr]

/-! ## Tokenize half: `Int.repr i` lexes back to a single `numT` token -/

theorem isNumChar_of_isDigit {c : Char} (h : isDigit c = true) : isNumChar c = true := by
  simp only [isNumChar, h, Bool.true_or]

/-- A digit or a `-` is routed to the number branch of `tokenizeAux`: it is not
whitespace, not a structural punctuation character, and not a keyword head. -/
theorem numChar_routing (c : Char) (h : isDigit c = true ∨ c = '-') :
    isWs c = false ∧ c ≠ '{' ∧ c ≠ '}' ∧ c ≠ '[' ∧ c ≠ ']' ∧ c ≠ ':' ∧
      c ≠ ',' ∧ c ≠ '"' ∧ c ≠ 't' ∧ c ≠ 'f' ∧ c ≠ 'n' := by
  rcases h with h | rfl
  · simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h0, h9⟩ := h
    have hws : isWs c = false := by
      simp only [isWs, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> (rintro rfl; exact absurd h0 (by decide))
    refine ⟨hws, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (rintro rfl; first | exact absurd h0 (by decide) | exact absurd h9 (by decide))
  · refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide⟩

theorem takeKeyword_eq_none_of_head (c : Char) (rest : List Char)
    (h8 : c ≠ 't') (h9 : c ≠ 'f') (h10 : c ≠ 'n') : takeKeyword (c :: rest) = none := by
  rcases rest with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, rest'⟩⟩⟩⟩ <;> simp_all [takeKeyword]

/-- `takeNumber` on an all-`isNumChar` list (with enough fuel) consumes the
entire list, leaving an empty tail. -/
theorem takeNumber_all (cs : List Char) (hall : ∀ c ∈ cs, isNumChar c = true) :
    ∀ (fuel : Nat) (acc : List Char), cs.length < fuel →
      takeNumber fuel acc cs = (acc.reverse ++ cs, []) := by
  induction cs with
  | nil =>
    intro fuel acc hf
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    simp [takeNumber]
  | cons c rest ih =>
    intro fuel acc hf
    obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
    have hc : isNumChar c = true := hall c (by simp)
    have hrest : ∀ x ∈ rest, isNumChar x = true := fun x hx => hall x (by simp [hx])
    have hlen : rest.length < n := by simp only [List.length_cons] at hf; omega
    simp only [takeNumber, if_pos hc]
    rw [ih hrest n (c :: acc) hlen]
    simp [List.reverse_cons]

/-- One reduction step of `tokenizeAux` at a number-leading character: skip the
whitespace / punctuation / keyword dispatch and land in the number branch. -/
theorem tokenizeAux_num_head (n : Nat) (c : Char) (rest : List Char)
    (hroute : isDigit c = true ∨ c = '-') :
    tokenizeAux (n + 1) (c :: rest) =
      (let (num, tail) := takeNumber n [c] rest
       if validNumberLitL num then
         (tokenizeAux n tail).map (JsonToken.numT (String.ofList num) :: ·)
       else .error "malformed number literal") := by
  obtain ⟨hws, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := numChar_routing c hroute
  have hnum : isNumChar c = true := by
    rcases hroute with h | rfl
    · exact isNumChar_of_isDigit h
    · simp [isNumChar]
  have hkw : takeKeyword (c :: rest) = none := takeKeyword_eq_none_of_head c rest h8 h9 h10
  rw [tokenizeAux, if_neg (by simp [hws]), if_neg h1, if_neg h2, if_neg h3, if_neg h4,
    if_neg h5, if_neg h6, if_neg h7, hkw]
  simp only [hnum, if_true]

/-- A number literal `c :: cs` (all `isNumChar`, valid, digit/`-` head) lexes to a
single `numT` token carrying the same characters. -/
theorem tokenizeAux_numberLit (c : Char) (cs : List Char)
    (hhead : isDigit c = true ∨ c = '-')
    (hall : ∀ x ∈ c :: cs, isNumChar x = true)
    (hvalid : validNumberLitL (c :: cs) = true) :
    ∀ fuel, (c :: cs).length + 1 < fuel →
      tokenizeAux fuel (c :: cs) = .ok [JsonToken.numT (String.ofList (c :: cs))] := by
  intro fuel hf
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  rw [tokenizeAux_num_head n c cs hhead]
  have hcs : ∀ x ∈ cs, isNumChar x = true := fun x hx => hall x (by simp [hx])
  have htn : takeNumber n [c] cs = (c :: cs, []) := by
    have h := takeNumber_all cs hcs n [c] (by simp only [List.length_cons] at hf; omega)
    simpa using h
  have hn1 : tokenizeAux n [] = .ok [] := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp only [List.length_cons] at hf; omega⟩
    rfl
  simp only [htn, hvalid, if_true, hn1, Except.map]

/-! ## Shape of `Int.repr i` as a character list -/

theorem repr_toList_numChars (i : Int) : ∀ x ∈ (Int.repr i).toList, isNumChar x = true := by
  rw [Int.repr_eq_if]
  by_cases hm : 0 ≤ i
  · rw [if_pos hm]
    show ∀ x ∈ (Nat.repr i.toNat).toList, isNumChar x = true
    rw [Nat.toList_repr]
    exact fun x hx => isNumChar_of_isDigit (toDigits_all_digit _ x hx)
  · rw [if_neg hm]
    show ∀ x ∈ ("-" ++ Nat.repr (-i).toNat).toList, isNumChar x = true
    rw [String.toList_append]
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · have h : ("-" : String).toList = ['-'] := rfl
      rw [h] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx; simp [isNumChar]
    · rw [Nat.toList_repr] at hx
      exact isNumChar_of_isDigit (toDigits_all_digit _ x hx)

theorem repr_toList_cons (i : Int) :
    ∃ c cs, (Int.repr i).toList = c :: cs ∧ (isDigit c = true ∨ c = '-') := by
  rw [Int.repr_eq_if]
  by_cases hm : 0 ≤ i
  · rw [if_pos hm]
    show ∃ c cs, (Nat.repr i.toNat).toList = c :: cs ∧ _
    rw [Nat.toList_repr]
    cases hcd : Nat.toDigits 10 i.toNat with
    | nil => exact absurd hcd Nat.toDigits_ne_nil
    | cons d rest =>
      exact ⟨d, rest, rfl, Or.inl (toDigits_all_digit _ d (by rw [hcd]; simp))⟩
  · rw [if_neg hm]
    show ∃ c cs, ("-" ++ Nat.repr (-i).toNat).toList = c :: cs ∧ _
    rw [String.toList_append]
    have h : ("-" : String).toList = ['-'] := rfl
    rw [h]
    exact ⟨'-', (Nat.repr (-i).toNat).toList, rfl, Or.inr rfl⟩

/-! ## The `num` roundtrip leaf on the integer fragment -/

theorem tokenize_serialize_num (i : Int) :
    tokenize (serialize (.num (Lean.JsonNumber.fromInt i))) = .ok [JsonToken.numT (Int.repr i)] := by
  have hchars : (serialize (Lean.Json.num (Lean.JsonNumber.fromInt i))).toList = (Int.repr i).toList := by
    rw [serialize, serialize_toList]
    simp only [toTokens, Lean.JsonNumber.fromInt, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, serTokChars, JsonToken.serialize]
    rfl
  obtain ⟨c, cs, hcons, hhead⟩ := repr_toList_cons i
  have hall : ∀ x ∈ c :: cs, isNumChar x = true := hcons ▸ repr_toList_numChars i
  have hvalid : validNumberLitL (c :: cs) = true := by
    have h := validNumberLit_repr i
    unfold validNumberLit at h
    rwa [hcons] at h
  rw [tokenize, hchars, hcons]
  rw [tokenizeAux_numberLit c cs hhead hall hvalid (2 * (c :: cs).length + 1)
    (by simp only [List.length_cons]; omega)]
  rw [← hcons, String.ofList_toList]

theorem parse_numT_repr (i : Int) :
    parse [JsonToken.numT (Int.repr i)] = .ok (.num (Lean.JsonNumber.fromInt i)) := by
  have hpv : parseValue 3 [JsonToken.numT (Int.repr i)]
      = .ok (.num (Lean.JsonNumber.fromInt i), []) := by
    show (match parseJsonNumber (Int.repr i) with
          | some n => Except.ok (Lean.Json.num n, [])
          | none => .error _) = _
    rw [parseJsonNumber_repr]
  unfold parse
  rw [show (2 * [JsonToken.numT (Int.repr i)].length + 1) = 3 from rfl, hpv]
  rfl

/-- **`num` roundtrip leaf.** Serialize, tokenize, then parse recovers the
integer-mantissa `JsonNumber`. Mirrors `Hax.Json.Roundtrip.roundtrip` for the
`num` fragment excluded from `Simple`. -/
theorem roundtrip_num (i : Int) :
    (tokenize (serialize (.num (Lean.JsonNumber.fromInt i))) >>= parse)
      = .ok (.num (Lean.JsonNumber.fromInt i)) := by
  rw [tokenize_serialize_num i]
  exact parse_numT_repr i

end Hax.Json.RoundtripNum

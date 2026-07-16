/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

import Hax.Json.Lexer

set_option autoImplicit false

/-!
# JSON number / string conformance to RFC 8259 — task B3

The lexer (`Hax.Json.Lexer`) already proves *soundness*: every emitted `numT` /
`strT` token carries a payload accepted by the RFC-8259 lexical validators
(`tokenize_numbers_valid`, `tokenize_strings_valid`). This module closes the
converse and general directions requested by task B3:

* **Numbers (RFC 8259 §6).** We name the grammar predicate `RfcNumber` and prove
  that `tokenize` accepts *exactly* the RFC number grammar
  `-? int frac? exp?` with `int = 0 | [1-9][0-9]*`, `frac = . [0-9]+`,
  `exp = [eE] [+-]? [0-9]+`:
  - `tokenize_accepts_number` — every RFC-valid number literal is tokenized to a
    single `numT` token (fully general, `∀ s`).
  - `tokenize_number_reject` — a run of number-characters that fails the grammar
    is rejected at lex time (fully general, `∀ cs`). Leading zeros, a lone `-`,
    a lone `.`, and empty exponents are covered as instances.

* **Strings (RFC 8259 §7 + §8.2).** We name the grammar predicate
  `RfcStringBody` and generalise the lexer's concrete escape / surrogate lemmas
  to `∀`-quantified statements over arbitrary hex quads:
  - `validStringContentL_singleEscape` — a `\` + `["\/bfnrt]` escape is accepted.
  - `isolated_high_surrogate_rejected'`, `isolated_low_surrogate_rejected'` —
    an unpaired UTF-16 surrogate is rejected (any hex quad).
  - `valid_surrogate_pair'` — a high+low surrogate pair is accepted (any quads).
  Representative `tokenize`-level acceptance / rejection cases are given as
  clearly-labelled concrete checks.

## Method

The number results reduce `tokenize` on a single numeric literal by:
1. showing any number-character routes past the whitespace / punctuation / quote
   / keyword dispatch of `tokenizeAux` to the numeric branch (`*_of_numChar`);
2. proving `takeNumber` consumes a maximal run of number-characters wholesale
   (`takeNumber_consumes`);
3. feeding the run to the lexer's own `validNumberLitL` gate.

`validNumberLitL_all_numChar` (every RFC-valid number literal consists only of
number-characters) upgrades the two-hypothesis `tokenize_number_singleton` to the
single-hypothesis capstone `tokenize_accepts_number`.
-/

namespace Hax.Json.Conformance

open Hax.Json.Lexer

/-! ## Number-character routing

Every JSON number character (`isNumChar`) is neither whitespace, structural
punctuation, a quote, nor the head of a `true`/`false`/`null` keyword, so the
`tokenizeAux` dispatch falls through to the numeric branch. -/

/-- Digits are number characters. -/
private theorem isNumChar_of_isDigit (c : Char) (h : isDigit c = true) :
    isNumChar c = true := by simp [isNumChar, h]

/-- A number character is never whitespace. -/
private theorem isWs_of_numChar (c : Char) (h : isNumChar c = true) : isWs c = false := by
  simp only [isNumChar, isDigit, Bool.or_eq_true, decide_eq_true_eq] at h
  cases hw : isWs c with
  | false => rfl
  | true =>
    exfalso
    simp only [isWs, Bool.or_eq_true, decide_eq_true_eq] at hw
    rcases hw with ((rfl | rfl) | rfl) | rfl <;> revert h <;> decide

/-- A number character never starts a `true`/`false`/`null` keyword. -/
private theorem takeKeyword_none_of_numChar (c : Char) (rest : List Char)
    (h : isNumChar c = true) : takeKeyword (c :: rest) = none := by
  simp only [isNumChar, isDigit, Bool.or_eq_true, decide_eq_true_eq] at h
  have ht : c ≠ 't' := by rintro rfl; revert h; decide
  have hf : c ≠ 'f' := by rintro rfl; revert h; decide
  have hn : c ≠ 'n' := by rintro rfl; revert h; decide
  unfold takeKeyword
  split <;> simp_all

/-- A number character is none of the structural / quote characters. -/
private theorem punct_ne_of_numChar (c : Char) (h : isNumChar c = true) :
    c ≠ '{' ∧ c ≠ '}' ∧ c ≠ '[' ∧ c ≠ ']' ∧ c ≠ ':' ∧ c ≠ ',' ∧ c ≠ '"' := by
  simp only [isNumChar, isDigit, Bool.or_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rintro rfl; revert h; decide)

/-! ## `takeNumber` consumes a maximal number-character run -/

/-- Given enough fuel, `takeNumber` consumes an all-number-character list
wholesale, leaving no tail. -/
theorem takeNumber_consumes (cs : List Char) (acc : List Char) (n : Nat)
    (hnc : ∀ c ∈ cs, isNumChar c = true) (hfuel : cs.length ≤ n) :
    takeNumber n acc cs = (acc.reverse ++ cs, []) := by
  induction cs generalizing acc n with
  | nil =>
    cases n with
    | zero => simp [takeNumber]
    | succ m => simp [takeNumber]
  | cons c rest ih =>
    cases n with
    | zero => simp at hfuel
    | succ m =>
      have hc : isNumChar c = true := hnc c (by simp)
      have hrest : ∀ x ∈ rest, isNumChar x = true := fun x hx => hnc x (by simp [hx])
      have hlen : rest.length ≤ m := by simp only [List.length_cons] at hfuel; omega
      simp only [takeNumber, hc, if_true]
      rw [ih (c :: acc) m hrest hlen]
      simp [List.reverse_cons]

/-- `tokenizeAux` on the empty input with positive fuel returns the empty token
list. -/
theorem tokenizeAux_nil (n : Nat) (hn : 0 < n) : tokenizeAux n [] = .ok [] := by
  cases n with
  | zero => omega
  | succ m => simp [tokenizeAux]

/-! ## Every RFC-valid number literal is a run of number-characters

`validNumberLitL` only accepts strings consisting entirely of number-characters,
so acceptance needs no separate `isNumChar` hypothesis. -/

private theorem dropDigits_nil_all_digit (l : List Char) (h : dropDigits l = []) :
    ∀ c ∈ l, isDigit c = true := by
  induction l with
  | nil => intro c hc; simp at hc
  | cons d rest ih =>
    simp only [dropDigits] at h
    by_cases hd : isDigit d = true
    · rw [if_pos hd] at h
      intro c hc; rcases List.mem_cons.1 hc with rfl | hc'
      · exact hd
      · exact ih h c hc'
    · rw [if_neg hd] at h; simp at h

private theorem dropDigits1_nil_all_digit (l : List Char) (h : dropDigits1 l = some []) :
    ∀ c ∈ l, isDigit c = true := by
  cases l with
  | nil => simp [dropDigits1] at h
  | cons d rest =>
    simp only [dropDigits1] at h
    by_cases hd : isDigit d = true
    · rw [if_pos hd] at h
      have hdrop : dropDigits rest = [] := by simpa using h
      intro c hc; rcases List.mem_cons.1 hc with rfl | hc'
      · exact hd
      · exact dropDigits_nil_all_digit rest hdrop c hc'
    · rw [if_neg hd] at h; simp at h

private theorem dropDigits_split (l : List Char) :
    ∃ pre, l = pre ++ dropDigits l ∧ (∀ c ∈ pre, isDigit c = true) := by
  induction l with
  | nil => exact ⟨[], by simp [dropDigits], by simp⟩
  | cons d rest ih =>
    simp only [dropDigits]
    by_cases hd : isDigit d = true
    · rw [if_pos hd]
      obtain ⟨pre, hpre, hall⟩ := ih
      refine ⟨d :: pre, by rw [List.cons_append, ← hpre], ?_⟩
      intro c hc; rcases List.mem_cons.1 hc with rfl | hc'
      · exact hd
      · exact hall c hc'
    · rw [if_neg hd]; exact ⟨[], by simp, by simp⟩

private theorem dropDigits1_split (l tail : List Char) (h : dropDigits1 l = some tail) :
    ∃ pre, l = pre ++ tail ∧ (∀ c ∈ pre, isDigit c = true) := by
  cases l with
  | nil => simp [dropDigits1] at h
  | cons d rest =>
    simp only [dropDigits1] at h
    by_cases hd : isDigit d = true
    · rw [if_pos hd] at h
      have htail : tail = dropDigits rest := by simpa using h.symm
      obtain ⟨pre, hpre, hall⟩ := dropDigits_split rest
      refine ⟨d :: pre, by rw [htail, List.cons_append, ← hpre], ?_⟩
      intro c hc; rcases List.mem_cons.1 hc with rfl | hc'
      · exact hd
      · exact hall c hc'
    · rw [if_neg hd] at h; simp at h

private theorem allNumChar_cons (d : Char) (rest : List Char)
    (hd : isNumChar d = true) (hrest : ∀ c ∈ rest, isNumChar c = true) :
    ∀ c ∈ d :: rest, isNumChar c = true := by
  intro c hc; rcases List.mem_cons.1 hc with rfl | hc'
  · exact hd
  · exact hrest c hc'

private theorem allDigit_imp_allNumChar (l : List Char) (h : ∀ c ∈ l, isDigit c = true) :
    ∀ c ∈ l, isNumChar c = true := fun c hc => isNumChar_of_isDigit c (h c hc)

private theorem allNumChar_append (pre tail : List Char)
    (hp : ∀ c ∈ pre, isNumChar c = true) (ht : ∀ c ∈ tail, isNumChar c = true) :
    ∀ c ∈ pre ++ tail, isNumChar c = true := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact hp c h
  · exact ht c h

private theorem validExpAfter_all (l : List Char) (h : validExpAfter l = true) :
    ∀ c ∈ l, isNumChar c = true := by
  unfold validExpAfter at h
  split at h
  · simp at h
  · rename_i rest
    cases hd : dropDigits1 rest with
    | none => rw [hd] at h; simp at h
    | some t => cases t with
      | cons _ _ => rw [hd] at h; simp at h
      | nil =>
        refine allNumChar_cons _ _ (by decide) ?_
        exact allDigit_imp_allNumChar rest (dropDigits1_nil_all_digit rest hd)
  · rename_i rest
    cases hd : dropDigits1 rest with
    | none => rw [hd] at h; simp at h
    | some t => cases t with
      | cons _ _ => rw [hd] at h; simp at h
      | nil =>
        refine allNumChar_cons _ _ (by decide) ?_
        exact allDigit_imp_allNumChar rest (dropDigits1_nil_all_digit rest hd)
  · cases hd : dropDigits1 l with
    | none => rw [hd] at h; simp at h
    | some t => cases t with
      | cons _ _ => rw [hd] at h; simp at h
      | nil => exact allDigit_imp_allNumChar l (dropDigits1_nil_all_digit l hd)

private theorem validExpOpt_all (l : List Char) (h : validExpOpt l = true) :
    ∀ c ∈ l, isNumChar c = true := by
  unfold validExpOpt at h
  split at h
  · intro c hc; simp at hc
  · rename_i rest
    refine allNumChar_cons _ _ (by decide) ?_
    exact validExpAfter_all rest h
  · rename_i rest
    refine allNumChar_cons _ _ (by decide) ?_
    exact validExpAfter_all rest h
  · simp at h

private theorem validFracExp_all (l : List Char) (h : validFracExp l = true) :
    ∀ c ∈ l, isNumChar c = true := by
  unfold validFracExp at h
  split at h
  · intro c hc; simp at hc
  · rename_i rest
    cases hd : dropDigits1 rest with
    | none => rw [hd] at h; simp at h
    | some tail =>
      rw [hd] at h
      obtain ⟨pre, hpre, hdig⟩ := dropDigits1_split rest tail hd
      refine allNumChar_cons _ _ (by decide) ?_
      rw [hpre]
      exact allNumChar_append pre tail (allDigit_imp_allNumChar pre hdig)
        (validExpOpt_all tail h)
  · exact validExpOpt_all l h

-- `hd0` (the `d ≠ '0'` hypothesis) is genuinely required to select the
-- non-zero-leading-digit arm of `validIntPart`; the unused-simp-arg linter
-- misfires on the generated matcher, so it is disabled for this proof.
set_option linter.unusedSimpArgs false in
private theorem validIntPart_split (cs tail : List Char) (h : validIntPart cs = some tail) :
    ∃ pre, cs = pre ++ tail ∧ (∀ c ∈ pre, isNumChar c = true) := by
  cases cs with
  | nil => simp [validIntPart] at h
  | cons d rest =>
    by_cases hd0 : d = '0'
    · subst hd0
      have htr : tail = rest := by simpa [validIntPart] using h.symm
      refine ⟨['0'], by simp [htr], ?_⟩
      intro c hc; simp only [List.mem_singleton] at hc; subst hc; decide
    · have hstep : validIntPart (d :: rest) =
          (if isDigit d then some (dropDigits rest) else none) := by
        unfold validIntPart; simp only [hd0]
      rw [hstep] at h
      by_cases hd : isDigit d = true
      · rw [if_pos hd] at h
        have htail : tail = dropDigits rest := by simpa using h.symm
        obtain ⟨pre, hpre, hdig⟩ := dropDigits_split rest
        refine ⟨d :: pre, by rw [htail, List.cons_append, ← hpre], ?_⟩
        exact allNumChar_cons _ _ (isNumChar_of_isDigit d hd) (allDigit_imp_allNumChar pre hdig)
      · rw [if_neg hd] at h; simp at h

/-- Every RFC-valid JSON number literal consists solely of number-characters. -/
theorem validNumberLitL_all_numChar (cs : List Char) (h : validNumberLitL cs = true) :
    ∀ c ∈ cs, isNumChar c = true := by
  unfold validNumberLitL at h
  split at h
  · simp at h
  · rename_i rest
    cases hip : validIntPart rest with
    | none => rw [hip] at h; simp at h
    | some tail =>
      rw [hip] at h
      obtain ⟨pre, hpre, hnc⟩ := validIntPart_split rest tail hip
      refine allNumChar_cons _ _ (by decide) ?_
      rw [hpre]
      exact allNumChar_append pre tail hnc (validFracExp_all tail h)
  · cases hip : validIntPart cs with
    | none => rw [hip] at h; simp at h
    | some tail =>
      rw [hip] at h
      obtain ⟨pre, hpre, hnc⟩ := validIntPart_split cs tail hip
      rw [hpre]
      exact allNumChar_append pre tail hnc (validFracExp_all tail h)

/-! ## Number grammar predicate (RFC 8259 §6)

`RfcNumber s` holds iff `s` matches the RFC 8259 number grammar

```
number = [ "-" ] int [ frac ] [ exp ]
int    = "0" | [1-9] [0-9]*
frac   = "." [0-9]+
exp    = ("e" | "E") [ "+" | "-" ] [0-9]+
```

encoded by the lexer's decidable validator `validNumberLit`. It is decidable
(a `Bool` equality). -/

/-- The RFC 8259 §6 number-literal grammar, as a decidable predicate on strings. -/
def RfcNumber (s : String) : Prop := validNumberLit s = true

instance (s : String) : Decidable (RfcNumber s) := by
  unfold RfcNumber; infer_instance

/-! ## Number acceptance / rejection through `tokenize` -/

/-- **General acceptance (run form).** A non-empty run of number-characters that
satisfies the RFC number grammar is tokenized to exactly one `numT` token. -/
theorem tokenize_number_singleton (cs : List Char)
    (hnc : ∀ c ∈ cs, isNumChar c = true) (hne : cs ≠ [])
    (hv : validNumberLitL cs = true) :
    tokenize (String.ofList cs) = .ok [.numT (String.ofList cs)] := by
  obtain ⟨c, rest, rfl⟩ : ∃ c rest, cs = c :: rest := by
    cases cs with
    | nil => exact absurd rfl hne
    | cons c rest => exact ⟨c, rest, rfl⟩
  have hc : isNumChar c = true := hnc c (by simp)
  have hws : isWs c = false := isWs_of_numChar c hc
  have hkw : takeKeyword (c :: rest) = none := takeKeyword_none_of_numChar c rest hc
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := punct_ne_of_numChar c hc
  have hrest : ∀ x ∈ rest, isNumChar x = true := fun x hx => hnc x (by simp [hx])
  have hfuel : rest.length ≤ 2 * (c :: rest).length := by simp [List.length_cons]; omega
  have htn : takeNumber (2 * (c :: rest).length) [c] rest = (c :: rest, []) := by
    rw [takeNumber_consumes rest [c] _ hrest hfuel]; simp
  have hpos : 0 < 2 * (c :: rest).length := by simp [List.length_cons]
  unfold tokenize
  rw [String.toList_ofList]
  simp only [tokenizeAux, hws, if_false, p1, p2, p3, p4, p5, p6, p7, hkw, hc, if_true,
    htn, hv, tokenizeAux_nil _ hpos]
  simp [Except.map, String.ofList]

/-- **General acceptance (capstone).** Every RFC-valid number literal string is
tokenized to a single `numT` token carrying that literal. -/
theorem tokenize_accepts_number (s : String) (h : RfcNumber s) :
    tokenize s = .ok [.numT s] := by
  have hv : validNumberLitL s.toList = true := h
  have hne : s.toList ≠ [] := by
    intro he; rw [he] at hv; revert hv; decide
  have hnc := validNumberLitL_all_numChar s.toList hv
  have hmain := tokenize_number_singleton s.toList hnc hne hv
  rwa [String.ofList_toList] at hmain

/-- **General rejection.** A non-empty run of number-characters that *fails* the
RFC number grammar is rejected at lex time. -/
theorem tokenize_number_reject (cs : List Char)
    (hnc : ∀ c ∈ cs, isNumChar c = true) (hne : cs ≠ [])
    (hv : validNumberLitL cs = false) :
    tokenize (String.ofList cs) = .error "malformed number literal" := by
  obtain ⟨c, rest, rfl⟩ : ∃ c rest, cs = c :: rest := by
    cases cs with
    | nil => exact absurd rfl hne
    | cons c rest => exact ⟨c, rest, rfl⟩
  have hc : isNumChar c = true := hnc c (by simp)
  have hws : isWs c = false := isWs_of_numChar c hc
  have hkw : takeKeyword (c :: rest) = none := takeKeyword_none_of_numChar c rest hc
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := punct_ne_of_numChar c hc
  have hrest : ∀ x ∈ rest, isNumChar x = true := fun x hx => hnc x (by simp [hx])
  have htn : takeNumber (2 * (rest.length + 1)) [c] rest = (c :: rest, []) := by
    rw [takeNumber_consumes rest [c] _ hrest (by omega)]; simp
  unfold tokenize
  rw [String.toList_ofList]
  simp [tokenizeAux, hws, p1, p2, p3, p4, p5, p6, p7, hkw, hc, htn, hv]

/-! ### Concrete number conformance (RFC 8259 §6 corner cases)

Representative acceptance / rejection instances, evaluated directly by `decide`.
These pin the general theorems to the specific grammar corner cases named in the
task: leading zeros, a lone `-`, a lone `.`, and empty exponents. -/

-- Acceptance
example : tokenize "0" = .ok [.numT "0"] := by decide
example : tokenize "-0" = .ok [.numT "-0"] := by decide
example : tokenize "42" = .ok [.numT "42"] := by decide
example : tokenize "-7" = .ok [.numT "-7"] := by decide
example : tokenize "1.5" = .ok [.numT "1.5"] := by decide
example : tokenize "1.5e10" = .ok [.numT "1.5e10"] := by decide
example : tokenize "1.5E-10" = .ok [.numT "1.5E-10"] := by decide
example : tokenize "123e+45" = .ok [.numT "123e+45"] := by decide

-- Rejection (RFC 8259 §6 violations)
/-- Leading zero rejected. -/
example : tokenize "01" = .error "malformed number literal" := by decide
/-- Lone minus rejected. -/
example : tokenize "-" = .error "malformed number literal" := by decide
/-- Lone fraction (no int part) rejected. -/
example : tokenize ".5" = .error "malformed number literal" := by decide
/-- Trailing dot (empty fraction) rejected. -/
example : tokenize "1." = .error "malformed number literal" := by decide
/-- Empty exponent rejected. -/
example : tokenize "1e" = .error "malformed number literal" := by decide
/-- Exponent with sign but no digits rejected. -/
example : tokenize "1e+" = .error "malformed number literal" := by decide
/-- Leading plus rejected. -/
example : tokenize "+1" = .error "malformed number literal" := by decide
/-- Double decimal point rejected. -/
example : tokenize "1.2.3" = .error "malformed number literal" := by decide

/-! ## String grammar predicate (RFC 8259 §7 + §8.2)

`RfcStringBody s` holds iff the *unquoted body* `s` matches the RFC 8259 string
grammar: every `\` is followed by one of `["\/bfnrt]` or `uXXXX`, and every
UTF-16 surrogate is properly paired. This is the lexer's decidable validator
`validStringContent`. -/

/-- The RFC 8259 §7/§8.2 string-body grammar, as a decidable predicate. -/
def RfcStringBody (s : String) : Prop := validStringContent s = true

instance (s : String) : Decidable (RfcStringBody s) := by
  unfold RfcStringBody; infer_instance

/-! ### General escape / surrogate validity (RFC 8259 §7, §8.2)

Generalisations of the lexer's concrete escape / surrogate checks to arbitrary
hex quads. These operate on the string-body validator `validStringContentL`. -/

/-- A single-character escape `\c` for `c ∈ ["\/bfnrt]` is accepted, and the
remaining body's validity is preserved. -/
theorem validStringContentL_singleEscape (c : Char) (rest : List Char)
    (hc : isSingleEscape c = true) (hrest : validStringContentL rest = true) :
    validStringContentL ('\\' :: c :: rest) = true := by
  have hcu : c ≠ 'u' := by rintro rfl; simp [isSingleEscape] at hc
  simp [validStringContentL, hcu, hc, hrest]

/-- A high UTF-16 surrogate and a low UTF-16 surrogate can never coincide. -/
theorem isHighSurrogate_eq_false_of_isLowSurrogate (a b c d : Char)
    (h : isLowSurrogate a b c d = true) : isHighSurrogate a b c d = false := by
  simp only [isLowSurrogate, Bool.and_eq_true] at h
  obtain ⟨⟨⟨_, hb⟩, _⟩, _⟩ := h
  simp only [Bool.or_eq_true, decide_eq_true_eq, or_assoc] at hb
  have hfalse : (b = '8' || b = '9' || b = 'A' || b = 'a' || b = 'B' || b = 'b') = false := by
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  simp [isHighSurrogate, hfalse]

/-- **Generalised** isolated-high-surrogate rejection: any lone high surrogate
`\uD8XX..\uDBXX` (any hex quad) is rejected. -/
theorem isolated_high_surrogate_rejected' (a b c d : Char)
    (h : isHighSurrogate a b c d = true) :
    validStringContentL ['\\', 'u', a, b, c, d] = false := by
  simp [validStringContentL, h]

/-- **Generalised** isolated-low-surrogate rejection: any lone low surrogate
`\uDCXX..\uDFXX` (any hex quad) is rejected. -/
theorem isolated_low_surrogate_rejected' (a b c d : Char)
    (h : isLowSurrogate a b c d = true) :
    validStringContentL ['\\', 'u', a, b, c, d] = false := by
  have hh : isHighSurrogate a b c d = false := isHighSurrogate_eq_false_of_isLowSurrogate a b c d h
  simp [validStringContentL, hh, h]

/-- **Generalised** surrogate-pair acceptance: a high surrogate immediately
followed by a low surrogate (any hex quads) is accepted. -/
theorem valid_surrogate_pair' (a b c d e f g h : Char)
    (hhi : isHighSurrogate a b c d = true) (hlo : isLowSurrogate e f g h = true) :
    validStringContentL ['\\', 'u', a, b, c, d, '\\', 'u', e, f, g, h] = true := by
  simp [validStringContentL, hhi, hlo]

/-! ### Concrete string conformance through `tokenize`

`takeString`'s quote/escape scanning makes a *fully* general `tokenize`-level
string theorem heavier than the number case; we give representative concrete
cases (evaluated by `decide`) alongside the general validator-level lemmas
above. -/

-- Acceptance: valid escapes
/-- A simple string tokenizes to a `strT` token. -/
example : tokenize "\"hello\"" = .ok [.strT "hello"] := by decide
/-- A `\n` escape is accepted. -/
example : tokenize "\"a\\nb\"" = .ok [.strT "a\\nb"] := by decide
/-- A `\"` escape is accepted. -/
example : tokenize "\"x\\\"y\"" = .ok [.strT "x\\\"y"] := by decide
/-- A `\uXXXX` BMP escape is accepted. -/
example : tokenize "\"\\u0041\"" = .ok [.strT "\\u0041"] := by decide
/-- A valid surrogate pair is accepted. -/
example : tokenize "\"\\uD83D\\uDE00\"" = .ok [.strT "\\uD83D\\uDE00"] := by decide

-- Rejection: invalid escapes / unpaired surrogates
/-- An unknown escape `\x` is rejected. -/
example : tokenize "\"\\x\"" = .error "malformed string escape sequence" := by decide
/-- A truncated `\u12` escape is rejected. -/
example : tokenize "\"\\u12\"" = .error "malformed string escape sequence" := by decide
/-- An isolated high surrogate is rejected. -/
example : tokenize "\"\\uD800\"" = .error "malformed string escape sequence" := by decide
/-- An isolated low surrogate is rejected. -/
example : tokenize "\"\\uDC00\"" = .error "malformed string escape sequence" := by decide
/-- A high surrogate followed by a non-low `\u` is rejected. -/
example : tokenize "\"\\uD800\\u0041\"" = .error "malformed string escape sequence" := by decide

end Hax.Json.Conformance

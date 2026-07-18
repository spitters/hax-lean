/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

import HaxLean.Json.Parser

set_option autoImplicit false

/-!
# JSON Token-Stream Parser — soundness (task B2)

This file discharges task B2 from `Hax/Json/Parser.lean`: a **soundness**
theorem for the fuel-based recursive-descent parser
`parseValue`/`parseArrayBody`/`parseObjectBody`.

## Which statement, and why

The task suggests two shapes:

1. a canonical token serializer `toTokens : Lean.Json → List JsonToken` with
   `parse toks = .ok j → toks = toTokens j`, or
2. a relational grammar `JsonParses : List JsonToken → Lean.Json → Prop` with
   `parse toks = .ok j → JsonParses toks j`.

We take **shape 2 (relational grammar)**. Shape 1 is *unsound* for this parser:

* **Numbers.** `parseValue` maps `numT s` to `.num (parseJsonNumber s)`, and
  `parseJsonNumber` is not injective — e.g. `"1"`, `"1.0"`, and `"1e0"` all
  denote the same `Lean.JsonNumber`. So `j` does not determine the token `s`,
  and no `toTokens` can recover it.
* **Objects.** `parseObjectBody` builds its result with `Lean.Json.mkObj`,
  which inserts pairs into a tree, dropping insertion order and de-duplicating
  keys. The `Json.obj` value therefore cannot recover the original key/`:`/
  value/`,` token stream.

The relational grammar sidesteps both: its number rule is quantified over the
*witness* `parseJsonNumber s = some n`, and its object rule records the parsed
pair list and states the value is `mkObj` of it. The relation is thus a clean
declarative spec of *which* token streams the parser accepts and *what* value
each yields — with the fuel abstracted away.

## Structure

* `ValueP`, `ArrayP`, `ObjectP` — a fuel-free `mutual inductive` transcribing
  the parser's grammar. Each relation carries the unconsumed tail, exactly as
  the parser threads it.
* `arrayStep`, `objectStep` — per-production helper lemmas for the body loops'
  "general" arm (parse a value, then dispatch on the following `]`/`}`/`,`).
* `sound_core` — the mutual soundness invariant, proved by a single induction
  on the fuel `n`: every recursive descent drops to fuel `n`, so one induction
  hypothesis feeds all three relations.
* `parse_sound` — the top-level theorem: `parse toks = .ok j → ValueP toks j []`
  (a successful parse derives a value with empty remainder).

The relation is a *sound over-approximation*: it also admits the trailing-comma
streams the parser rejects (e.g. `[1,]`), since soundness (`parse ⟹ relates`)
does not require the converse. Completeness/faithful rejection is out of scope
for B2.
-/

namespace Hax.Json.Parser

open Hax.Json.Lexer

/-! ## Relational grammar -/

mutual

/-- `ValueP toks v rest`: parsing a single JSON value off `toks` yields `v`,
leaving `rest` unconsumed. Mirrors `parseValue`. -/
inductive ValueP : List JsonToken → Lean.Json → List JsonToken → Prop where
  | str {s : String} {rest : List JsonToken} :
      ValueP (JsonToken.strT s :: rest) (Lean.Json.str (decodeString s)) rest
  | trueT {rest : List JsonToken} :
      ValueP (JsonToken.trueT :: rest) (Lean.Json.bool true) rest
  | falseT {rest : List JsonToken} :
      ValueP (JsonToken.falseT :: rest) (Lean.Json.bool false) rest
  | nullT {rest : List JsonToken} :
      ValueP (JsonToken.nullT :: rest) Lean.Json.null rest
  | num {s : String} {n : Lean.JsonNumber} {rest : List JsonToken}
      (h : parseJsonNumber s = some n) :
      ValueP (JsonToken.numT s :: rest) (Lean.Json.num n) rest
  | arr {rest : List JsonToken} {v : Lean.Json} {rest' : List JsonToken}
      (h : ArrayP rest #[] v rest') :
      ValueP (JsonToken.lbracket :: rest) v rest'
  | obj {rest : List JsonToken} {v : Lean.Json} {rest' : List JsonToken}
      (h : ObjectP rest [] v rest') :
      ValueP (JsonToken.lbrace :: rest) v rest'

/-- `ArrayP toks acc v rest`: parsing an array body off `toks` with values
accumulated in `acc` yields `v`, leaving `rest`. Mirrors `parseArrayBody`. -/
inductive ArrayP : List JsonToken → Array Lean.Json → Lean.Json → List JsonToken → Prop where
  | close {rest : List JsonToken} {acc : Array Lean.Json} :
      ArrayP (JsonToken.rbracket :: rest) acc (Lean.Json.arr acc) rest
  | valClose {toks : List JsonToken} {acc : Array Lean.Json} {v : Lean.Json}
      {rest' : List JsonToken}
      (hv : ValueP toks v (JsonToken.rbracket :: rest')) :
      ArrayP toks acc (Lean.Json.arr (acc.push v)) rest'
  | valComma {toks : List JsonToken} {acc : Array Lean.Json} {v : Lean.Json}
      {rest' : List JsonToken} {w : Lean.Json} {rest'' : List JsonToken}
      (hv : ValueP toks v (JsonToken.comma :: rest'))
      (hbody : ArrayP rest' (acc.push v) w rest'') :
      ArrayP toks acc w rest''

/-- `ObjectP toks acc v rest`: parsing an object body off `toks` with pairs
accumulated (in reverse insertion order) in `acc` yields `v`, leaving `rest`.
Mirrors `parseObjectBody`. -/
inductive ObjectP : List JsonToken → List (String × Lean.Json) → Lean.Json → List JsonToken → Prop where
  | close {rest : List JsonToken} {acc : List (String × Lean.Json)} :
      ObjectP (JsonToken.rbrace :: rest) acc (Lean.Json.mkObj acc.reverse) rest
  | pairClose {k : String} {rest : List JsonToken} {v : Lean.Json}
      {rest'' : List JsonToken} {acc : List (String × Lean.Json)}
      (hv : ValueP rest v (JsonToken.rbrace :: rest'')) :
      ObjectP (JsonToken.strT k :: JsonToken.colon :: rest) acc
        (Lean.Json.mkObj ((k, v) :: acc).reverse) rest''
  | pairComma {k : String} {rest : List JsonToken} {v : Lean.Json}
      {rest'' : List JsonToken} {acc : List (String × Lean.Json)} {w : Lean.Json}
      {rest3 : List JsonToken}
      (hv : ValueP rest v (JsonToken.comma :: rest''))
      (hbody : ObjectP rest'' ((k, v) :: acc) w rest3) :
      ObjectP (JsonToken.strT k :: JsonToken.colon :: rest) acc w rest3

end

/-! ## Per-production helpers for the body "general" arms -/

/-- Soundness of `parseArrayBody`'s general arm: after parsing a value off
`toks`, the parser dispatches on the following `]`/`,`. -/
private theorem arrayStep {n : Nat} {toks : List JsonToken} {acc : Array Lean.Json}
    {v : Lean.Json} {rest : List JsonToken}
    (ihV : ∀ t v r, parseValue n t = .ok (v, r) → ValueP t v r)
    (ihA : ∀ t a v r, parseArrayBody n t a = .ok (v, r) → ArrayP t a v r)
    (h : (match parseValue n toks with
          | Except.error e => Except.error e
          | Except.ok (v0, r0) =>
            match r0 with
            | JsonToken.rbracket :: rest' => Except.ok (Lean.Json.arr (acc.push v0), rest')
            | JsonToken.comma :: JsonToken.rbracket :: _ => Except.error "trailing comma in array"
            | JsonToken.comma :: rest' => parseArrayBody n rest' (acc.push v0)
            | _ => Except.error "expected ',' or ']' in array") = Except.ok (v, rest)) :
    ArrayP toks acc v rest := by
  cases hpv : parseValue n toks with
  | error e => simp only [hpv] at h; contradiction
  | ok p =>
    obtain ⟨v0, r0⟩ := p
    simp only [hpv] at h
    split at h <;>
      first
      | contradiction
      | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         exact ArrayP.valClose (ihV toks v0 _ hpv))
      | exact ArrayP.valComma (ihV toks v0 _ hpv) (ihA _ _ v rest h)

/-- Soundness of `parseObjectBody`'s general (`key : value`) arm. -/
private theorem objectStep {n : Nat} {k : String} {rest : List JsonToken}
    {acc : List (String × Lean.Json)} {v : Lean.Json} {rest_out : List JsonToken}
    (ihV : ∀ t v r, parseValue n t = .ok (v, r) → ValueP t v r)
    (ihO : ∀ t a v r, parseObjectBody n t a = .ok (v, r) → ObjectP t a v r)
    (h : (match parseValue n rest with
          | Except.error e => Except.error e
          | Except.ok (v0, rest') =>
            match rest' with
            | JsonToken.rbrace :: rest'' =>
                Except.ok (Lean.Json.mkObj ((k, v0) :: acc).reverse, rest'')
            | JsonToken.comma :: JsonToken.rbrace :: _ => Except.error "trailing comma in object"
            | JsonToken.comma :: rest'' => parseObjectBody n rest'' ((k, v0) :: acc)
            | _ => Except.error "expected ',' or '}' in object") = Except.ok (v, rest_out)) :
    ObjectP (JsonToken.strT k :: JsonToken.colon :: rest) acc v rest_out := by
  cases hpv : parseValue n rest with
  | error e => simp only [hpv] at h; contradiction
  | ok p =>
    obtain ⟨v0, rest'⟩ := p
    simp only [hpv] at h
    split at h <;>
      first
      | contradiction
      | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         exact ObjectP.pairClose (ihV rest v0 _ hpv))
      | exact ObjectP.pairComma (ihV rest v0 _ hpv) (ihO _ _ v rest_out h)

/-! ## Mutual soundness invariant -/

/-- The mutual soundness invariant, proved by induction on the fuel `n`. Every
recursive descent in `parseValue`/`parseArrayBody`/`parseObjectBody` drops the
fuel to `n`, so a single induction hypothesis at `n` feeds all three arms at
`n + 1`. -/
theorem sound_core :
    ∀ n : Nat,
      (∀ toks v rest, parseValue n toks = .ok (v, rest) → ValueP toks v rest) ∧
      (∀ toks acc v rest, parseArrayBody n toks acc = .ok (v, rest) → ArrayP toks acc v rest) ∧
      (∀ toks acc v rest, parseObjectBody n toks acc = .ok (v, rest) → ObjectP toks acc v rest) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun toks v rest h => ?_, fun toks acc v rest h => ?_, fun toks acc v rest h => ?_⟩
    · simp only [parseValue] at h; contradiction
    · simp only [parseArrayBody] at h; contradiction
    · simp only [parseObjectBody] at h; contradiction
  | succ n ih =>
    obtain ⟨ihV, ihA, ihO⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · -- parseValue
      intro toks v rest h
      cases toks with
      | nil => simp only [parseValue] at h; contradiction
      | cons c cs =>
        cases c with
        | lbrace => exact ValueP.obj (ihO cs [] v rest h)
        | lbracket => exact ValueP.arr (ihA cs #[] v rest h)
        | strT s =>
            simp only [parseValue, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h; exact ValueP.str
        | trueT =>
            simp only [parseValue, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h; exact ValueP.trueT
        | falseT =>
            simp only [parseValue, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h; exact ValueP.falseT
        | nullT =>
            simp only [parseValue, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h; exact ValueP.nullT
        | numT s =>
            simp only [parseValue] at h
            split at h <;>
              first
              | contradiction
              | (rename_i m hm
                 simp only [Except.ok.injEq, Prod.mk.injEq] at h
                 obtain ⟨rfl, rfl⟩ := h
                 exact ValueP.num hm)
        | rbrace => simp only [parseValue] at h; contradiction
        | rbracket => simp only [parseValue] at h; contradiction
        | colon => simp only [parseValue] at h; contradiction
        | comma => simp only [parseValue] at h; contradiction
    · -- parseArrayBody
      intro toks acc v rest h
      cases toks with
      | nil => simp only [parseArrayBody] at h; contradiction
      | cons c cs =>
        cases c with
        | rbracket =>
            simp only [parseArrayBody, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h; exact ArrayP.close
        | strT s => exact arrayStep ihV ihA h
        | numT s => exact arrayStep ihV ihA h
        | trueT => exact arrayStep ihV ihA h
        | falseT => exact arrayStep ihV ihA h
        | nullT => exact arrayStep ihV ihA h
        | lbrace => exact arrayStep ihV ihA h
        | rbrace => exact arrayStep ihV ihA h
        | lbracket => exact arrayStep ihV ihA h
        | colon => exact arrayStep ihV ihA h
        | comma => exact arrayStep ihV ihA h
    · -- parseObjectBody
      intro toks acc v rest h
      cases toks with
      | nil => simp only [parseObjectBody] at h; contradiction
      | cons c cs =>
        cases c with
        | rbrace =>
            simp only [parseObjectBody, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h; exact ObjectP.close
        | strT k =>
            cases cs with
            | nil => simp only [parseObjectBody] at h; contradiction
            | cons c2 rest0 =>
              cases c2 with
              | colon => exact objectStep ihV ihO h
              | lbrace => simp only [parseObjectBody] at h; contradiction
              | rbrace => simp only [parseObjectBody] at h; contradiction
              | lbracket => simp only [parseObjectBody] at h; contradiction
              | rbracket => simp only [parseObjectBody] at h; contradiction
              | comma => simp only [parseObjectBody] at h; contradiction
              | trueT => simp only [parseObjectBody] at h; contradiction
              | falseT => simp only [parseObjectBody] at h; contradiction
              | nullT => simp only [parseObjectBody] at h; contradiction
              | numT s2 => simp only [parseObjectBody] at h; contradiction
              | strT s2 => simp only [parseObjectBody] at h; contradiction
        | lbrace => simp only [parseObjectBody] at h; contradiction
        | lbracket => simp only [parseObjectBody] at h; contradiction
        | rbracket => simp only [parseObjectBody] at h; contradiction
        | colon => simp only [parseObjectBody] at h; contradiction
        | comma => simp only [parseObjectBody] at h; contradiction
        | trueT => simp only [parseObjectBody] at h; contradiction
        | falseT => simp only [parseObjectBody] at h; contradiction
        | nullT => simp only [parseObjectBody] at h; contradiction
        | numT s => simp only [parseObjectBody] at h; contradiction

/-! ## Top-level soundness -/

/-- **Soundness of `parse`.** If the parser accepts `toks` and returns `j`,
then `toks` is derivable in the JSON grammar as the value `j` with no
unconsumed tail. -/
theorem parse_sound (toks : List JsonToken) (j : Lean.Json)
    (h : parse toks = .ok j) : ValueP toks j [] := by
  simp only [parse, bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i p hpv
    obtain ⟨v, tl⟩ := p
    split at h
    · rename_i hempty
      simp only [Except.ok.injEq] at h
      subst h
      have htl : tl = [] := by
        cases tl with
        | nil => rfl
        | cons a as => simp at hempty
      subst htl
      exact (sound_core _).1 toks v [] hpv
    · contradiction

end Hax.Json.Parser

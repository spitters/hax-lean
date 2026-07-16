/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

import Hax.Json.ParserSound

set_option autoImplicit false

/-!
# JSON Token-Stream Parser — completeness / faithful rejection (JSON gap 1)

`Hax/Json/ParserSound.lean` proves **soundness**: `parse toks = .ok j → ValueP toks j []`.
Its relation `ValueP`/`ArrayP`/`ObjectP` is a *sound over-approximation* — it also
admits streams the parser rejects, e.g. the trailing-comma array `[1,]`. So `ValueP`
is **not** an exact inverse of the parser, and completeness `ValueP toks j [] → parse
toks = .ok j` is false as stated (a `ValueP` witness for `[1,]` exists, yet `parse`
errors with "trailing comma").

This file supplies the missing **completeness** direction against a *tightened* grammar
`ValuePStrict` that mirrors the parser's dispatch exactly (trailing commas forbidden):

* `ValuePStrict` / `ArrayBodyStrict` / `ArrayElemsStrict` / `ObjectBodyStrict` /
  `ObjectElemsStrict` — the strict grammar. The element relations reject a `,`
  that is not immediately followed by a value, exactly as `parseArrayBody` /
  `parseObjectBody` do.
* `complete_core` — the mutual completeness invariant: a strict derivation with
  `toks.length ≤ n + rest.length` fuel drives the parser to `.ok (v, rest)`.
* `parse_complete` — the top-level theorem: `ValuePStrict toks j [] → parse toks = .ok j`.
* `ValuePStrict_ValueP` — strict refines loose (`ValuePStrict → ValueP`), so the strict
  grammar is a genuine sub-relation of the soundness relation.
* Faithful rejection lemmas for the leaf non-grammar cases (empty input, trailing
  commas in arrays/objects).
-/

namespace Hax.Json.Parser

open Hax.Json.Lexer

/-! ## Tightened relational grammar

Mirrors `parseValue`/`parseArrayBody`/`parseObjectBody` exactly. The key difference
from `ValueP`: after a `,` in an array/object body, the continuation must be a
non-empty element sequence (`…ElemsStrict`), never an immediate close. This forbids
the trailing-comma streams the parser rejects. -/

mutual

/-- `ValuePStrict toks v rest`: strict single-value parse. Mirrors `parseValue`. -/
inductive ValuePStrict : List JsonToken → Lean.Json → List JsonToken → Prop where
  | str {s : String} {rest : List JsonToken} :
      ValuePStrict (JsonToken.strT s :: rest) (Lean.Json.str s) rest
  | trueT {rest : List JsonToken} :
      ValuePStrict (JsonToken.trueT :: rest) (Lean.Json.bool true) rest
  | falseT {rest : List JsonToken} :
      ValuePStrict (JsonToken.falseT :: rest) (Lean.Json.bool false) rest
  | nullT {rest : List JsonToken} :
      ValuePStrict (JsonToken.nullT :: rest) Lean.Json.null rest
  | num {s : String} {n : Lean.JsonNumber} {rest : List JsonToken}
      (h : parseJsonNumber s = some n) :
      ValuePStrict (JsonToken.numT s :: rest) (Lean.Json.num n) rest
  | arr {rest : List JsonToken} {v : Lean.Json} {rest' : List JsonToken}
      (h : ArrayBodyStrict rest #[] v rest') :
      ValuePStrict (JsonToken.lbracket :: rest) v rest'
  | obj {rest : List JsonToken} {v : Lean.Json} {rest' : List JsonToken}
      (h : ObjectBodyStrict rest [] v rest') :
      ValuePStrict (JsonToken.lbrace :: rest) v rest'

/-- Strict array body: either an immediate `]` (empty array) or a non-empty element
sequence. Mirrors `parseArrayBody`'s dispatch (`]` first, else a value). -/
inductive ArrayBodyStrict : List JsonToken → Array Lean.Json → Lean.Json → List JsonToken → Prop where
  | close {rest : List JsonToken} {acc : Array Lean.Json} :
      ArrayBodyStrict (JsonToken.rbracket :: rest) acc (Lean.Json.arr acc) rest
  | elems {toks : List JsonToken} {acc : Array Lean.Json} {v : Lean.Json}
      {rest : List JsonToken} (h : ArrayElemsStrict toks acc v rest) :
      ArrayBodyStrict toks acc v rest

/-- Strict non-empty array element sequence: `value ( ']' | ',' value … )`. The
`,` case recurses into `ArrayElemsStrict`, which requires a value at its head, so a
trailing comma (`,` then `]`) is unreachable — exactly as the parser rejects it. -/
inductive ArrayElemsStrict : List JsonToken → Array Lean.Json → Lean.Json → List JsonToken → Prop where
  | last {toks : List JsonToken} {acc : Array Lean.Json} {v : Lean.Json}
      {rest' : List JsonToken}
      (hv : ValuePStrict toks v (JsonToken.rbracket :: rest')) :
      ArrayElemsStrict toks acc (Lean.Json.arr (acc.push v)) rest'
  | cons {toks : List JsonToken} {acc : Array Lean.Json} {v : Lean.Json}
      {rest' : List JsonToken} {w : Lean.Json} {rest'' : List JsonToken}
      (hv : ValuePStrict toks v (JsonToken.comma :: rest'))
      (hbody : ArrayElemsStrict rest' (acc.push v) w rest'') :
      ArrayElemsStrict toks acc w rest''

/-- Strict object body: either an immediate `}` (empty object) or a non-empty
key/value element sequence. Mirrors `parseObjectBody`. -/
inductive ObjectBodyStrict : List JsonToken → List (String × Lean.Json) → Lean.Json → List JsonToken → Prop where
  | close {rest : List JsonToken} {acc : List (String × Lean.Json)} :
      ObjectBodyStrict (JsonToken.rbrace :: rest) acc (Lean.Json.mkObj acc.reverse) rest
  | elems {toks : List JsonToken} {acc : List (String × Lean.Json)} {v : Lean.Json}
      {rest : List JsonToken} (h : ObjectElemsStrict toks acc v rest) :
      ObjectBodyStrict toks acc v rest

/-- Strict non-empty object element sequence: `key ':' value ( '}' | ',' key ':' … )`.
The `,` case recurses into `ObjectElemsStrict`, forbidding a trailing comma. -/
inductive ObjectElemsStrict : List JsonToken → List (String × Lean.Json) → Lean.Json → List JsonToken → Prop where
  | last {k : String} {rest : List JsonToken} {v : Lean.Json}
      {rest'' : List JsonToken} {acc : List (String × Lean.Json)}
      (hv : ValuePStrict rest v (JsonToken.rbrace :: rest'')) :
      ObjectElemsStrict (JsonToken.strT k :: JsonToken.colon :: rest) acc
        (Lean.Json.mkObj ((k, v) :: acc).reverse) rest''
  | cons {k : String} {rest : List JsonToken} {v : Lean.Json}
      {rest'' : List JsonToken} {acc : List (String × Lean.Json)} {w : Lean.Json}
      {rest3 : List JsonToken}
      (hv : ValuePStrict rest v (JsonToken.comma :: rest''))
      (hbody : ObjectElemsStrict rest'' ((k, v) :: acc) w rest3) :
      ObjectElemsStrict (JsonToken.strT k :: JsonToken.colon :: rest) acc w rest3

end

/-! ## Progress: every strict production consumes at least one token

Needed to rule out fuel exhaustion: a strict derivation leaves a strictly shorter
remainder, so `toks.length ≤ n + rest.length` forces `n ≥ 1` in every recursive
case. Rather than recurse on the (mutual) derivation, we bundle the five relations
and induct on a `Nat` bound `k` on `toks.length` — the same fuel-style induction as
`sound_core`. Within a step, the "same-`toks`" wrappers (`Body → Elems → Value`) are
discharged locally, and the strictly-shorter recursions fall to the `k`-level IH. -/

theorem strict_progress_aux : ∀ k : Nat,
    (∀ toks v rest, toks.length ≤ k → ValuePStrict toks v rest → rest.length < toks.length) ∧
    (∀ toks acc v rest, toks.length ≤ k → ArrayBodyStrict toks acc v rest → rest.length < toks.length) ∧
    (∀ toks acc v rest, toks.length ≤ k → ArrayElemsStrict toks acc v rest → rest.length < toks.length) ∧
    (∀ toks acc v rest, toks.length ≤ k → ObjectBodyStrict toks acc v rest → rest.length < toks.length) ∧
    (∀ toks acc v rest, toks.length ≤ k → ObjectElemsStrict toks acc v rest → rest.length < toks.length) := by
  intro k
  induction k with
  | zero =>
    have hVnil : ∀ v rest, ¬ ValuePStrict [] v rest := fun v rest h => by cases h
    have hAEnil : ∀ acc v rest, ¬ ArrayElemsStrict [] acc v rest := fun acc v rest h => by
      cases h with
      | last hv => exact hVnil _ _ hv
      | cons hv hbody => exact hVnil _ _ hv
    have hOEnil : ∀ acc v rest, ¬ ObjectElemsStrict [] acc v rest := fun acc v rest h => by
      cases h
    refine ⟨fun toks v rest hlen hd => ?_, fun toks acc v rest hlen hd => ?_,
            fun toks acc v rest hlen hd => ?_, fun toks acc v rest hlen hd => ?_,
            fun toks acc v rest hlen hd => ?_⟩ <;>
      simp only [Nat.le_zero, List.length_eq_zero_iff] at hlen <;> subst hlen
    · exact absurd hd (hVnil _ _)
    · cases hd with
      | elems h' => exact absurd h' (hAEnil _ _ _)
    · exact absurd hd (hAEnil _ _ _)
    · cases hd with
      | elems h' => exact absurd h' (hOEnil _ _ _)
    · exact absurd hd (hOEnil _ _ _)
  | succ k ih =>
    obtain ⟨ihV, ihAB, ihAE, ihOB, ihOE⟩ := ih
    have hV : ∀ toks v rest, toks.length ≤ k + 1 → ValuePStrict toks v rest →
        rest.length < toks.length := by
      intro toks v rest hlen hd
      cases hd with
      | str => simp
      | trueT => simp
      | falseT => simp
      | nullT => simp
      | num => simp
      | arr hh =>
          have := ihAB _ _ _ _ (by simp only [List.length_cons] at hlen; omega) hh
          simp only [List.length_cons]; omega
      | obj hh =>
          have := ihOB _ _ _ _ (by simp only [List.length_cons] at hlen; omega) hh
          simp only [List.length_cons]; omega
    have hAE : ∀ toks acc v rest, toks.length ≤ k + 1 → ArrayElemsStrict toks acc v rest →
        rest.length < toks.length := by
      intro toks acc v rest hlen hd
      cases hd with
      | last hv => have := hV _ _ _ hlen hv; simp only [List.length_cons] at this; omega
      | cons hv hbody =>
          have h1 := hV _ _ _ hlen hv
          have h2 := ihAE _ _ _ _ (by simp only [List.length_cons] at h1 hlen; omega) hbody
          simp only [List.length_cons] at h1; omega
    have hOE : ∀ toks acc v rest, toks.length ≤ k + 1 → ObjectElemsStrict toks acc v rest →
        rest.length < toks.length := by
      intro toks acc v rest hlen hd
      cases hd with
      | last hv =>
          have := hV _ _ _ (by simp only [List.length_cons] at hlen ⊢; omega) hv
          simp only [List.length_cons] at this ⊢; omega
      | cons hv hbody =>
          have h1 := hV _ _ _ (by simp only [List.length_cons] at hlen ⊢; omega) hv
          have h2 := ihOE _ _ _ _ (by simp only [List.length_cons] at h1 hlen; omega) hbody
          simp only [List.length_cons] at h1 ⊢; omega
    refine ⟨hV, ?_, hAE, ?_, hOE⟩
    · intro toks acc v rest hlen hd
      cases hd with
      | close => simp
      | elems h' => exact hAE _ _ _ _ hlen h'
    · intro toks acc v rest hlen hd
      cases hd with
      | close => simp
      | elems h' => exact hOE _ _ _ _ hlen h'

theorem valuePStrict_progress {toks : List JsonToken} {v : Lean.Json}
    {rest : List JsonToken} (h : ValuePStrict toks v rest) : rest.length < toks.length :=
  (strict_progress_aux toks.length).1 toks v rest (Nat.le_refl _) h

theorem arrayBodyStrict_progress {toks : List JsonToken} {acc : Array Lean.Json}
    {v : Lean.Json} {rest : List JsonToken} (h : ArrayBodyStrict toks acc v rest) :
    rest.length < toks.length :=
  (strict_progress_aux toks.length).2.1 toks acc v rest (Nat.le_refl _) h

theorem objectBodyStrict_progress {toks : List JsonToken}
    {acc : List (String × Lean.Json)} {v : Lean.Json} {rest : List JsonToken}
    (h : ObjectBodyStrict toks acc v rest) : rest.length < toks.length :=
  (strict_progress_aux toks.length).2.2.2.1 toks acc v rest (Nat.le_refl _) h

theorem arrayElemsStrict_progress {toks : List JsonToken} {acc : Array Lean.Json}
    {v : Lean.Json} {rest : List JsonToken} (h : ArrayElemsStrict toks acc v rest) :
    rest.length < toks.length :=
  (strict_progress_aux toks.length).2.2.1 toks acc v rest (Nat.le_refl _) h

theorem objectElemsStrict_progress {toks : List JsonToken}
    {acc : List (String × Lean.Json)} {v : Lean.Json} {rest : List JsonToken}
    (h : ObjectElemsStrict toks acc v rest) : rest.length < toks.length :=
  (strict_progress_aux toks.length).2.2.2.2 toks acc v rest (Nat.le_refl _) h

/-! ## Head-shape helpers

A strict value parse starts with a value token (never `]`); a strict object element
sequence starts with `strT k ':'`. These let the parser's outer dispatch reduce. -/

/-- A strict value parse consumes a leading value token; its head is not `]`. -/
theorem valuePStrict_head {toks : List JsonToken} {v : Lean.Json} {rest : List JsonToken}
    (h : ValuePStrict toks v rest) :
    ∃ t ts, toks = t :: ts ∧ t ≠ JsonToken.rbracket := by
  cases h <;> exact ⟨_, _, rfl, by nofun⟩

/-- A strict array element sequence starts with a value token; its head is not `]`. -/
theorem arrayElemsStrict_head {toks : List JsonToken} {acc : Array Lean.Json}
    {v : Lean.Json} {rest : List JsonToken} (h : ArrayElemsStrict toks acc v rest) :
    ∃ t ts, toks = t :: ts ∧ t ≠ JsonToken.rbracket := by
  cases h with
  | last hv => exact valuePStrict_head hv
  | cons hv hbody => exact valuePStrict_head hv

/-- A strict object element sequence starts with `strT k ':'`. -/
theorem objectElemsStrict_shape {toks : List JsonToken} {acc : List (String × Lean.Json)}
    {v : Lean.Json} {rest : List JsonToken} (h : ObjectElemsStrict toks acc v rest) :
    ∃ k rest0, toks = JsonToken.strT k :: JsonToken.colon :: rest0 := by
  cases h with
  | last hv => exact ⟨_, _, rfl⟩
  | cons hv hbody => exact ⟨_, _, rfl⟩

/-! ## One-step reduction of the body "general" arms

Given the parsed-value result, these rewrite `parseArrayBody`/`parseObjectBody` one
element forward, matching the parser's post-value dispatch. -/

/-- General-arm unfolding of `parseArrayBody` when the head is not `]`. -/
theorem parseArrayBody_step {n : Nat} {t : JsonToken} {ts : List JsonToken}
    {acc : Array Lean.Json} (ht : t ≠ JsonToken.rbracket) :
    parseArrayBody (n + 1) (t :: ts) acc =
      (match parseValue n (t :: ts) with
       | Except.error e => Except.error e
       | Except.ok (v0, r0) =>
         match r0 with
         | JsonToken.rbracket :: rest' => Except.ok (Lean.Json.arr (acc.push v0), rest')
         | JsonToken.comma :: JsonToken.rbracket :: _ => Except.error "trailing comma in array"
         | JsonToken.comma :: rest' => parseArrayBody n rest' (acc.push v0)
         | _ => Except.error "expected ',' or ']' in array") := by
  cases t <;> first | exact absurd rfl ht | rfl

/-- After a value closed by `]`, `parseArrayBody` returns the array. -/
theorem parseArrayBody_valClose {n : Nat} {t : JsonToken} {ts : List JsonToken}
    {acc : Array Lean.Json} {v : Lean.Json} {rest' : List JsonToken}
    (ht : t ≠ JsonToken.rbracket)
    (hpv : parseValue n (t :: ts) = .ok (v, JsonToken.rbracket :: rest')) :
    parseArrayBody (n + 1) (t :: ts) acc = .ok (Lean.Json.arr (acc.push v), rest') := by
  rw [parseArrayBody_step ht, hpv]

/-- After a value closed by `,` and another value-start `t2`, `parseArrayBody` recurses. -/
theorem parseArrayBody_valComma {n : Nat} {t : JsonToken} {ts : List JsonToken}
    {acc : Array Lean.Json} {v : Lean.Json} {t2 : JsonToken} {ts2 : List JsonToken}
    (ht : t ≠ JsonToken.rbracket) (ht2 : t2 ≠ JsonToken.rbracket)
    (hpv : parseValue n (t :: ts) = .ok (v, JsonToken.comma :: t2 :: ts2)) :
    parseArrayBody (n + 1) (t :: ts) acc = parseArrayBody n (t2 :: ts2) (acc.push v) := by
  rw [parseArrayBody_step ht, hpv]
  cases t2 <;> first | exact absurd rfl ht2 | rfl

/-- General-arm unfolding of `parseObjectBody` on a `strT k ':'` head. -/
theorem parseObjectBody_step {n : Nat} {k : String} {rest : List JsonToken}
    {acc : List (String × Lean.Json)} :
    parseObjectBody (n + 1) (JsonToken.strT k :: JsonToken.colon :: rest) acc =
      (match parseValue n rest with
       | Except.error e => Except.error e
       | Except.ok (v0, rest') =>
         match rest' with
         | JsonToken.rbrace :: rest'' => Except.ok (Lean.Json.mkObj ((k, v0) :: acc).reverse, rest'')
         | JsonToken.comma :: JsonToken.rbrace :: _ => Except.error "trailing comma in object"
         | JsonToken.comma :: rest'' => parseObjectBody n rest'' ((k, v0) :: acc)
         | _ => Except.error "expected ',' or '}' in object") := rfl

/-- After a key/value closed by `}`, `parseObjectBody` returns the object. -/
theorem parseObjectBody_valClose {n : Nat} {k : String} {rest : List JsonToken}
    {acc : List (String × Lean.Json)} {v : Lean.Json} {rest'' : List JsonToken}
    (hpv : parseValue n rest = .ok (v, JsonToken.rbrace :: rest'')) :
    parseObjectBody (n + 1) (JsonToken.strT k :: JsonToken.colon :: rest) acc =
      .ok (Lean.Json.mkObj ((k, v) :: acc).reverse, rest'') := by
  rw [parseObjectBody_step, hpv]

/-- After a key/value closed by `,` and another `strT k2`, `parseObjectBody` recurses. -/
theorem parseObjectBody_valComma {n : Nat} {k : String} {rest : List JsonToken}
    {acc : List (String × Lean.Json)} {v : Lean.Json} {k2 : String} {ts2 : List JsonToken}
    (hpv : parseValue n rest = .ok (v, JsonToken.comma :: JsonToken.strT k2 :: ts2)) :
    parseObjectBody (n + 1) (JsonToken.strT k :: JsonToken.colon :: rest) acc =
      parseObjectBody n (JsonToken.strT k2 :: ts2) ((k, v) :: acc) := by
  rw [parseObjectBody_step, hpv]

/-! ## Completeness core

The mutual completeness invariant, proved by induction on the fuel `n` (the same
shape as `sound_core`). At fuel `0` every strict derivation contradicts its fuel
bound via `progress`. At `n + 1`, the atom/close arms reduce by `rfl`; the value
inside a body is parsed at fuel `n` (`ihV`); and the "same-`toks`" wrappers
(`Body → Elems`) are discharged by the locally-established element completeness. -/

theorem complete_core : ∀ n : Nat,
    (∀ toks v rest, ValuePStrict toks v rest →
        toks.length ≤ n + rest.length → parseValue n toks = .ok (v, rest)) ∧
    (∀ toks acc v rest, ArrayBodyStrict toks acc v rest →
        toks.length ≤ n + rest.length → parseArrayBody n toks acc = .ok (v, rest)) ∧
    (∀ toks acc v rest, ArrayElemsStrict toks acc v rest →
        toks.length ≤ n + rest.length → parseArrayBody n toks acc = .ok (v, rest)) ∧
    (∀ toks acc v rest, ObjectBodyStrict toks acc v rest →
        toks.length ≤ n + rest.length → parseObjectBody n toks acc = .ok (v, rest)) ∧
    (∀ toks acc v rest, ObjectElemsStrict toks acc v rest →
        toks.length ≤ n + rest.length → parseObjectBody n toks acc = .ok (v, rest)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun toks v rest hd hlen => ?_, fun toks acc v rest hd hlen => ?_,
            fun toks acc v rest hd hlen => ?_, fun toks acc v rest hd hlen => ?_,
            fun toks acc v rest hd hlen => ?_⟩
    · exact absurd hlen (by have := valuePStrict_progress hd; omega)
    · exact absurd hlen (by have := arrayBodyStrict_progress hd; omega)
    · exact absurd hlen (by have := arrayElemsStrict_progress hd; omega)
    · exact absurd hlen (by have := objectBodyStrict_progress hd; omega)
    · exact absurd hlen (by have := objectElemsStrict_progress hd; omega)
  | succ n ih =>
    obtain ⟨ihV, ihAB, ihAE, ihOB, ihOE⟩ := ih
    -- value completeness at `n + 1`
    have hVc : ∀ toks v rest, ValuePStrict toks v rest →
        toks.length ≤ (n + 1) + rest.length → parseValue (n + 1) toks = .ok (v, rest) := by
      intro toks v rest hd hlen
      cases hd with
      | str => rfl
      | trueT => rfl
      | falseT => rfl
      | nullT => rfl
      | num h => simp only [parseValue, h]
      | arr hh => exact ihAB _ _ _ _ hh (by simp only [List.length_cons] at hlen; omega)
      | obj hh => exact ihOB _ _ _ _ hh (by simp only [List.length_cons] at hlen; omega)
    -- array-element completeness at `n + 1` (the value inside is parsed at fuel `n`)
    have hAEc : ∀ toks acc v rest, ArrayElemsStrict toks acc v rest →
        toks.length ≤ (n + 1) + rest.length → parseArrayBody (n + 1) toks acc = .ok (v, rest) := by
      intro toks acc v rest hd hlen
      cases hd with
      | last hv =>
          obtain ⟨t, ts, rfl, ht⟩ := valuePStrict_head hv
          have hpv := ihV _ _ _ hv (by simp only [List.length_cons] at hlen ⊢; omega)
          exact parseArrayBody_valClose ht hpv
      | cons hv hbody =>
          obtain ⟨t, ts, rfl, ht⟩ := valuePStrict_head hv
          obtain ⟨t2, ts2, hrest', ht2⟩ := arrayElemsStrict_head hbody
          subst hrest'
          have hpe := valuePStrict_progress hv
          have hae := arrayElemsStrict_progress hbody
          have hpv := ihV _ _ _ hv (by simp only [List.length_cons] at hlen hpe hae ⊢; omega)
          rw [parseArrayBody_valComma ht ht2 hpv]
          have hb : (t2 :: ts2).length ≤ n + rest.length := by
            simp only [List.length_cons] at hlen hpe ⊢; omega
          exact ihAE _ _ _ _ hbody hb
    -- object-element completeness at `n + 1`
    have hOEc : ∀ toks acc v rest, ObjectElemsStrict toks acc v rest →
        toks.length ≤ (n + 1) + rest.length → parseObjectBody (n + 1) toks acc = .ok (v, rest) := by
      intro toks acc v rest hd hlen
      cases hd with
      | last hv =>
          have hpv := ihV _ _ _ hv (by simp only [List.length_cons] at hlen ⊢; omega)
          exact parseObjectBody_valClose hpv
      | cons hv hbody =>
          obtain ⟨k2, rest3, hshape⟩ := objectElemsStrict_shape hbody
          subst hshape
          have hpe := valuePStrict_progress hv
          have hoe := objectElemsStrict_progress hbody
          have hpv := ihV _ _ _ hv (by simp only [List.length_cons] at hlen hpe hoe ⊢; omega)
          rw [parseObjectBody_valComma hpv]
          have hb : (JsonToken.strT k2 :: JsonToken.colon :: rest3).length ≤ n + rest.length := by
            simp only [List.length_cons] at hlen hpe ⊢; omega
          exact ihOE _ _ _ _ hbody hb
    refine ⟨hVc, ?_, hAEc, ?_, hOEc⟩
    · intro toks acc v rest hd hlen
      cases hd with
      | close => rfl
      | elems h' => exact hAEc _ _ _ _ h' hlen
    · intro toks acc v rest hd hlen
      cases hd with
      | close => rfl
      | elems h' => exact hOEc _ _ _ _ h' hlen

/-! ## Top-level completeness -/

/-- **Value-level completeness.** A strict value derivation leaving `rest` is
reproduced by `parseValue` at any sufficient fuel. -/
theorem parseValue_complete {n : Nat} {toks : List JsonToken} {v : Lean.Json}
    {rest : List JsonToken} (h : ValuePStrict toks v rest)
    (hn : toks.length ≤ n + rest.length) : parseValue n toks = .ok (v, rest) :=
  (complete_core n).1 toks v rest h hn

/-- **Completeness of `parse`.** If `toks` is derivable in the strict grammar as the
value `j` with no unconsumed tail, then `parse toks = .ok j`. Together with
`parse_sound` (soundness into the loose grammar), this pins down the parser: it
accepts exactly the strict-grammar streams. -/
theorem parse_complete {toks : List JsonToken} {j : Lean.Json}
    (h : ValuePStrict toks j []) : parse toks = .ok j := by
  have hpv : parseValue (2 * toks.length + 1) toks = .ok (j, []) :=
    parseValue_complete h (by simp only [List.length_nil]; omega)
  simp only [parse, hpv, bind, Except.bind, List.isEmpty_nil, if_true]

/-! ## Strict refines loose

`ValuePStrict → ValueP`: the tightened grammar is a sub-relation of the soundness
grammar. Bundled and driven by a `Nat` bound on `toks.length` (the same shape as
`strict_progress_aux`), since the relations are mutually inductive. -/

theorem strict_implies_loose_aux : ∀ k : Nat,
    (∀ toks v rest, toks.length ≤ k → ValuePStrict toks v rest → ValueP toks v rest) ∧
    (∀ toks acc v rest, toks.length ≤ k → ArrayBodyStrict toks acc v rest → ArrayP toks acc v rest) ∧
    (∀ toks acc v rest, toks.length ≤ k → ArrayElemsStrict toks acc v rest → ArrayP toks acc v rest) ∧
    (∀ toks acc v rest, toks.length ≤ k → ObjectBodyStrict toks acc v rest → ObjectP toks acc v rest) ∧
    (∀ toks acc v rest, toks.length ≤ k → ObjectElemsStrict toks acc v rest → ObjectP toks acc v rest) := by
  intro k
  induction k with
  | zero =>
    have hVnil : ∀ v rest, ¬ ValuePStrict [] v rest := fun v rest h => by cases h
    have hAEnil : ∀ acc v rest, ¬ ArrayElemsStrict [] acc v rest := fun acc v rest h => by
      cases h with
      | last hv => exact hVnil _ _ hv
      | cons hv hbody => exact hVnil _ _ hv
    have hOEnil : ∀ acc v rest, ¬ ObjectElemsStrict [] acc v rest := fun acc v rest h => by
      cases h
    refine ⟨fun toks v rest hlen hd => ?_, fun toks acc v rest hlen hd => ?_,
            fun toks acc v rest hlen hd => ?_, fun toks acc v rest hlen hd => ?_,
            fun toks acc v rest hlen hd => ?_⟩ <;>
      simp only [Nat.le_zero, List.length_eq_zero_iff] at hlen <;> subst hlen
    · exact absurd hd (hVnil _ _)
    · cases hd with
      | elems h' => exact absurd h' (hAEnil _ _ _)
    · exact absurd hd (hAEnil _ _ _)
    · cases hd with
      | elems h' => exact absurd h' (hOEnil _ _ _)
    · exact absurd hd (hOEnil _ _ _)
  | succ k ih =>
    obtain ⟨ihV, ihAB, ihAE, ihOB, ihOE⟩ := ih
    have hV : ∀ toks v rest, toks.length ≤ k + 1 → ValuePStrict toks v rest →
        ValueP toks v rest := by
      intro toks v rest hlen hd
      cases hd with
      | str => exact ValueP.str
      | trueT => exact ValueP.trueT
      | falseT => exact ValueP.falseT
      | nullT => exact ValueP.nullT
      | num h => exact ValueP.num h
      | arr hh =>
          exact ValueP.arr (ihAB _ _ _ _ (by simp only [List.length_cons] at hlen; omega) hh)
      | obj hh =>
          exact ValueP.obj (ihOB _ _ _ _ (by simp only [List.length_cons] at hlen; omega) hh)
    have hAE : ∀ toks acc v rest, toks.length ≤ k + 1 → ArrayElemsStrict toks acc v rest →
        ArrayP toks acc v rest := by
      intro toks acc v rest hlen hd
      cases hd with
      | last hv => exact ArrayP.valClose (hV _ _ _ hlen hv)
      | cons hv hbody =>
          have hpe := valuePStrict_progress hv
          refine ArrayP.valComma (hV _ _ _ hlen hv) (ihAE _ _ _ _ ?_ hbody)
          simp only [List.length_cons] at hlen hpe ⊢; omega
    have hOE : ∀ toks acc v rest, toks.length ≤ k + 1 → ObjectElemsStrict toks acc v rest →
        ObjectP toks acc v rest := by
      intro toks acc v rest hlen hd
      cases hd with
      | last hv =>
          exact ObjectP.pairClose (hV _ _ _ (by simp only [List.length_cons] at hlen ⊢; omega) hv)
      | cons hv hbody =>
          have hpe := valuePStrict_progress hv
          refine ObjectP.pairComma (hV _ _ _ (by simp only [List.length_cons] at hlen ⊢; omega) hv)
            (ihOE _ _ _ _ ?_ hbody)
          simp only [List.length_cons] at hlen hpe ⊢; omega
    refine ⟨hV, ?_, hAE, ?_, hOE⟩
    · intro toks acc v rest hlen hd
      cases hd with
      | close => exact ArrayP.close
      | elems h' => exact hAE _ _ _ _ hlen h'
    · intro toks acc v rest hlen hd
      cases hd with
      | close => exact ObjectP.close
      | elems h' => exact hOE _ _ _ _ hlen h'

/-- **Strict refines loose.** Every strict value derivation is a loose (`ValueP`)
derivation. -/
theorem ValuePStrict_ValueP {toks : List JsonToken} {v : Lean.Json} {rest : List JsonToken}
    (h : ValuePStrict toks v rest) : ValueP toks v rest :=
  (strict_implies_loose_aux toks.length).1 toks v rest (Nat.le_refl _) h

/-! ## Faithful rejection

The parser rejects the leaf non-grammar streams. The trailing-comma cases exhibit the
gap between the loose and strict grammars: the loose `ValueP` *admits* `[true,]`
(witnessed below), yet `parse` rejects it — which is exactly why completeness is stated
against `ValuePStrict`, not `ValueP`. -/

/-- Empty input is rejected: `parse` never returns `.ok`. -/
theorem parse_empty_rejected' : ∀ j : Lean.Json, parse [] ≠ .ok j := by
  intro j h; rw [parse_empty_not_out_of_fuel] at h; cases h

/-- The parser rejects a trailing comma in an array. -/
theorem parse_array_trailing_comma_rejected :
    parse [.lbracket, .trueT, .comma, .rbracket] = .error "trailing comma in array" := rfl

/-- The parser rejects a trailing comma in an object. -/
theorem parse_object_trailing_comma_rejected :
    parse [.lbrace, .strT "k", .colon, .trueT, .comma, .rbrace] =
      .error "trailing comma in object" := rfl

/-- The *loose* grammar admits the trailing-comma array `[true,]` — exhibiting that
`ValueP` is a strict over-approximation of the parser (which rejects it above). -/
theorem valueP_admits_array_trailing_comma :
    ValueP [.lbracket, .trueT, .comma, .rbracket] (.arr (#[].push (.bool true))) [] :=
  ValueP.arr (ArrayP.valComma ValueP.trueT ArrayP.close)

/-- The *strict* grammar rejects the trailing-comma array `[true,]`: no strict value
derivation exists for it. This is the faithful counterpart to the loose admission above. -/
theorem valuePStrict_rejects_array_trailing_comma :
    ∀ j rest, ¬ ValuePStrict [.lbracket, .trueT, .comma, .rbracket] j rest := by
  intro j rest h
  cases h with
  | arr hh =>
    cases hh with
    | elems h' =>
      cases h' with
      | last hv => cases hv
      | cons hv hbody =>
        cases hv
        cases hbody with
        | last hv2 => cases hv2
        | cons hv2 hbody2 => cases hv2

end Hax.Json.Parser

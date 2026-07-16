/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

import Hax.Json.Lexer
import Hax.Json.Parser
import Hax.Json.Conformance
import Hax.Json.Roundtrip

set_option autoImplicit false

/-!
# JSON string conformance + string roundtrip — JSON gap 3

Placeholder module docstring (to be finalised).
-/

namespace Hax.Json.RoundtripStr

open Hax.Json.Lexer
open Hax.Json.Conformance
open Hax.Json.Parser

/-! ## `takeString` recoverability predicate -/

/-- A `List Char` body is *`takeString`-recoverable* iff `takeString` walking it
consumes exactly the body and stops at the following closing quote. Every raw
`"` would terminate early, and a trailing lone `\` is a premature EOF, so both
are excluded; a `\` followed by any character escapes it (collected verbatim). -/
def wfBody : List Char → Bool
  | [] => true
  | '"' :: _ => false
  | '\\' :: _ :: rest => wfBody rest
  | '\\' :: [] => false
  | _ :: rest => wfBody rest

/-! ### `takeString` step lemmas -/

theorem takeString_quoteHead (m : Nat) (acc rest : List Char) :
    takeString (m + 1) acc ('"' :: rest) = some (acc.reverse, rest) := rfl

theorem takeString_escHead (m : Nat) (acc : List Char) (c : Char) (rest : List Char) :
    takeString (m + 1) acc ('\\' :: c :: rest) = takeString m (c :: '\\' :: acc) rest := rfl

theorem takeString_plain (m : Nat) (acc : List Char) (c : Char) (xs : List Char)
    (h1 : c ≠ '"') (h2 : c ≠ '\\') :
    takeString (m + 1) acc (c :: xs) = takeString m (c :: acc) xs := by
  generalize hR : takeString m (c :: acc) xs = R
  unfold takeString
  split <;> simp_all

/-- `wfBody` reduces past a plain (non-`"`, non-`\`) leading character. -/
theorem wfBody_plain (c : Char) (rest : List Char) (h1 : c ≠ '"') (h2 : c ≠ '\\') :
    wfBody (c :: rest) = wfBody rest := by
  generalize hR : wfBody rest = R
  unfold wfBody
  split <;> simp_all

/-- `takeString` consumes a `wfBody` body wholesale, stopping at the closing
quote and returning the accumulated reversed prefix appended to the body. -/
theorem takeString_wf :
    ∀ (n : Nat) (bs acc tail : List Char),
      wfBody bs = true → bs.length < n →
      takeString n acc (bs ++ '"' :: tail) = some (acc.reverse ++ bs, tail) := by
  intro n
  induction n with
  | zero => intro bs acc tail _ hf; omega
  | succ m ih =>
    intro bs acc tail hwf hf
    cases bs with
    | nil =>
      simp only [List.nil_append, takeString_quoteHead, List.append_nil]
    | cons c rest =>
      by_cases hq : c = '"'
      · subst hq; simp [wfBody] at hwf
      · by_cases hbs : c = '\\'
        · subst hbs
          cases rest with
          | nil => simp [wfBody] at hwf
          | cons c2 rest2 =>
            have hwf' : wfBody rest2 = true := by
              simpa [wfBody] using hwf
            have hlen : rest2.length < m := by
              simp only [List.length_cons] at hf; omega
            rw [show ('\\' :: c2 :: rest2) ++ '"' :: tail
                  = '\\' :: c2 :: (rest2 ++ '"' :: tail) from rfl,
                takeString_escHead, ih rest2 (c2 :: '\\' :: acc) tail hwf' hlen]
            simp
        · have hwf' : wfBody rest = true := by
            rw [wfBody_plain c rest hq hbs] at hwf; exact hwf
          have hlen : rest.length < m := by
            simp only [List.length_cons] at hf; omega
          rw [show (c :: rest) ++ '"' :: tail = c :: (rest ++ '"' :: tail) from rfl,
              takeString_plain m acc c _ hq hbs, ih rest (c :: acc) tail hwf' hlen]
          simp

/-! ## Tokenizer quote-branch dispatch -/

/-- The `tokenizeAux` dispatch on a `"`-headed input reduces to the string
branch: run `takeString`, then gate on `validStringContentL`. -/
theorem tokenizeAux_quote (n : Nat) (rest : List Char) :
    tokenizeAux (n + 1) ('"' :: rest) =
      (match takeString n [] rest with
       | none => .error "unterminated string literal"
       | some (body, tail) =>
         if validStringContentL body then
           (tokenizeAux n tail).map (JsonToken.strT (String.ofList body) :: ·)
         else .error "malformed string escape sequence") := by
  rfl

end Hax.Json.RoundtripStr

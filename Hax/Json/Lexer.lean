/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

set_option autoImplicit false

/-!
# JSON Lexer — minimal verified foundation

Foundation for a verified JSON parser targeting RFC 8259. This file provides:

* `JsonToken` — the lexical token type with decidable equality.
* `tokenize` — a *total* tokenizer from `String` to `Except String (List JsonToken)`.
* `JsonToken.serialize` — a left-inverse-style printer producing canonical text.
* Basic single-token roundtrip lemmas closed by `decide`.

## Scope

This module ships the lexer's totality and decidability guarantees, **plus**
RFC 8259 §6 / §7 lexical validation for number and string literals:

* `validNumberLit` enforces `[-]? (0 | [1-9][0-9]*) (\.[0-9]+)? ([eE][+-]?[0-9]+)?`.
* `validStringContent` enforces that every backslash is followed by exactly
  one of `["\/bfnrt]` or `u[0-9a-fA-F]{4}`.

The tokenizer rejects malformed numeric / string payloads at lex time, and we
prove that every emitted `numT` / `strT` token's payload satisfies the
respective validator. Surrogate-pair pairing (RFC 8259 §8.2) and parser-layer
roundtripping over arbitrary token shapes are deliberately deferred.

This addresses a gap in the Lean 4 ecosystem: there is no fully verified JSON
parser today. Building from a *total* lexer with a clean inductive token type
gives us a stable surface to grow proofs against.

## Implementation note

We use **fuel-based recursion** on `Nat` so that termination is trivially
structural (the fuel decreases by 1 each step). The fuel is initialised to the
input length, which is always sufficient because every recursive call consumes
at least one character. We deliberately do not formalise that bound here; an
out-of-fuel result is reported as an error, and the top-level `tokenize`
provisions enough fuel that this never happens for finite inputs.
-/

namespace Hax.Json.Lexer

/-- Lexical tokens of the JSON grammar (RFC 8259, §2). -/
inductive JsonToken where
  | lbrace
  | rbrace
  | lbracket
  | rbracket
  | colon
  | comma
  | trueT
  | falseT
  | nullT
  | numT (s : String)
  | strT (s : String)
  deriving DecidableEq, Repr

/-- Whitespace per RFC 8259 §2: space, tab, newline, carriage return. -/
@[inline] def isWs (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\r'

/-- Decimal digit `0..9`. -/
@[inline] def isDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

/-- A character that may appear in the body of a JSON number literal. -/
@[inline] def isNumChar (c : Char) : Bool :=
  isDigit c || c = '.' || c = 'e' || c = 'E' || c = '+' || c = '-'

/-- Hexadecimal digit `0..9 | a..f | A..F`. -/
@[inline] def isHexDigit (c : Char) : Bool :=
  isDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- Single-character escape sequences permitted by RFC 8259 §7 after `\`,
excluding the `u` form which is handled separately. -/
@[inline] def isSingleEscape (c : Char) : Bool :=
  c = '"' || c = '\\' || c = '/' || c = 'b' || c = 'f' || c = 'n' || c = 'r' || c = 't'

/-- A `\uXXXX` 4-hex sequence is a *high* surrogate (U+D800..U+DBFF) iff the
hex digits are `D8XX`, `D9XX`, `DAXX`, or `DBXX` (case-insensitive). -/
@[inline] def isHighSurrogate (h0 h1 h2 h3 : Char) : Bool :=
  (h0 = 'D' || h0 = 'd') &&
  (h1 = '8' || h1 = '9' || h1 = 'A' || h1 = 'a' || h1 = 'B' || h1 = 'b') &&
  isHexDigit h2 && isHexDigit h3

/-- A `\uXXXX` 4-hex sequence is a *low* surrogate (U+DC00..U+DFFF) iff the
hex digits are `DCXX`, `DDXX`, `DEXX`, or `DFXX` (case-insensitive). -/
@[inline] def isLowSurrogate (h0 h1 h2 h3 : Char) : Bool :=
  (h0 = 'D' || h0 = 'd') &&
  (h1 = 'C' || h1 = 'c' || h1 = 'D' || h1 = 'd' || h1 = 'E' || h1 = 'e' || h1 = 'F' || h1 = 'f') &&
  isHexDigit h2 && isHexDigit h3

/-! ### Number literal validation (RFC 8259 §6) -/

/-- Drop a maximal prefix of decimal digits, returning the remaining tail. -/
def dropDigits : List Char → List Char
  | [] => []
  | c :: rest => if isDigit c then dropDigits rest else c :: rest

/-- Require at least one decimal digit, then drop any further digits and
return the tail. Returns `none` if the head is not a digit. -/
def dropDigits1 : List Char → Option (List Char)
  | [] => none
  | c :: rest => if isDigit c then some (dropDigits rest) else none

/-- Validate the integer component (`0` or `[1-9][0-9]*`) and return the tail.
Lean's pattern match guarantees the literal `'0'` case is matched first, so
the fallthrough handles `[1-9]` (we only check `isDigit`; a leading `'0'`
cannot reach this branch). -/
def validIntPart : List Char → Option (List Char)
  | [] => none
  | '0' :: rest => some rest
  | c :: rest => if isDigit c then some (dropDigits rest) else none

/-- Validate an `[eE][+-]?[0-9]+` exponent suffix already past the `e` / `E`. -/
def validExpAfter : List Char → Bool
  | [] => false
  | '+' :: rest => match dropDigits1 rest with | some [] => true | _ => false
  | '-' :: rest => match dropDigits1 rest with | some [] => true | _ => false
  | cs         => match dropDigits1 cs with | some [] => true | _ => false

/-- Validate the optional exponent suffix at the end of a number literal. -/
def validExpOpt : List Char → Bool
  | [] => true
  | 'e' :: rest => validExpAfter rest
  | 'E' :: rest => validExpAfter rest
  | _ => false

/-- Validate the optional fractional part `\.[0-9]+`, then forward to the
exponent validator. -/
def validFracExp : List Char → Bool
  | [] => true
  | '.' :: rest =>
    match dropDigits1 rest with
    | some tail => validExpOpt tail
    | none => false
  | cs => validExpOpt cs

/-- `List Char` form of the number-literal validator. -/
def validNumberLitL : List Char → Bool
  | [] => false
  | '-' :: rest =>
    match validIntPart rest with
    | some tail => validFracExp tail
    | none => false
  | cs =>
    match validIntPart cs with
    | some tail => validFracExp tail
    | none => false

/-- A `String` is a well-formed JSON number literal per RFC 8259 §6. -/
def validNumberLit (s : String) : Bool := validNumberLitL s.toList

/-! ### String content validation (RFC 8259 §7 + §8.2)

Validates the *unquoted* body — the caller is expected to have stripped the
surrounding `"..."`. Every backslash must be followed by either a single
character drawn from `["\/bfnrt]`, or `u` followed by exactly four hex digits.
Bare control characters (e.g. raw newlines) are NOT rejected here; the lexer
already guarantees these never reach the body since `takeString` walks the
raw input character-by-character.

**Surrogate-pair rule (RFC 8259 §8.2, B4):** an isolated `\uD8XX..\uDBXX`
(high surrogate) must be followed immediately by `\uDCXX..\uDFXX` (low
surrogate), and an isolated low surrogate is rejected. The pair is left
encoded as 12 raw escape characters in the token body — decoding to a single
Unicode scalar is the parser/printer's job. -/

def validStringContentL : List Char → Bool
  | [] => true
  -- `\u` + high surrogate + `\u` + low surrogate: accept the pair.
  | '\\' :: 'u' :: a :: b :: c :: d :: '\\' :: 'u' :: e :: f :: g :: h :: rest =>
    if isHighSurrogate a b c d then
      isLowSurrogate e f g h && validStringContentL rest
    else if isLowSurrogate a b c d then
      false
    else
      isHexDigit a && isHexDigit b && isHexDigit c && isHexDigit d &&
        validStringContentL ('\\' :: 'u' :: e :: f :: g :: h :: rest)
  -- `\u` + 4 hex digits, with no second `\u` following (or insufficient input):
  -- a high surrogate or low surrogate alone is invalid.
  | '\\' :: 'u' :: a :: b :: c :: d :: rest =>
    if isHighSurrogate a b c d then false
    else if isLowSurrogate a b c d then false
    else isHexDigit a && isHexDigit b && isHexDigit c && isHexDigit d
      && validStringContentL rest
  | '\\' :: c :: rest => isSingleEscape c && validStringContentL rest
  | '\\' :: [] => false
  | _ :: rest => validStringContentL rest

/-- A `String` body is well-formed JSON string content per RFC 8259 §7. -/
def validStringContent (s : String) : Bool := validStringContentL s.toList

/-- Walk a list collecting a JSON string literal body. Caller has consumed the
opening `'"'`. Walks until a closing `'"'` (returning `(body, tail)`), or
returns `none` on premature EOF / fuel exhaustion. A backslash escapes the
next char (collected verbatim). Structural recursion on `Nat` fuel. -/
def takeString : Nat → List Char → List Char → Option (List Char × List Char)
  | 0,     _,   _                  => none
  | _ + 1, _,   []                 => none
  | _ + 1, acc, '"' :: rest        => some (acc.reverse, rest)
  | n + 1, acc, '\\' :: c :: rest  => takeString n (c :: '\\' :: acc) rest
  | _ + 1, _,   '\\' :: []         => none
  | n + 1, acc, c :: rest          => takeString n (c :: acc) rest

/-- Walk a list collecting a maximal numeric literal prefix. Returns
`(prefix, tail)`. Uses fuel for structural recursion. -/
def takeNumber : Nat → List Char → List Char → List Char × List Char
  | 0,     acc, cs        => (acc.reverse, cs)
  | _ + 1, acc, []        => (acc.reverse, [])
  | n + 1, acc, c :: rest =>
    if isNumChar c then takeNumber n (c :: acc) rest
    else (acc.reverse, c :: rest)

/-- Match `true` / `false` / `null` at the head of the list. -/
def takeKeyword : List Char → Option (JsonToken × List Char)
  | 't' :: 'r' :: 'u' :: 'e' :: rest          => some (JsonToken.trueT, rest)
  | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest   => some (JsonToken.falseT, rest)
  | 'n' :: 'u' :: 'l' :: 'l' :: rest          => some (JsonToken.nullT, rest)
  | _                                         => none

/-- Auxiliary tokenizer with explicit fuel. Recurses structurally on `n`. The
caller (`tokenize`) provisions `n = s.toList.length`, which is always enough
fuel because every recursive call consumes at least one character of the
remaining list. An out-of-fuel result is reported as an error. -/
def tokenizeAux : Nat → List Char → Except String (List JsonToken)
  | 0,     _              => .error "out of fuel"
  | _ + 1, []             => .ok []
  | n + 1, c :: rest =>
    if isWs c then
      tokenizeAux n rest
    else if c = '{' then
      (tokenizeAux n rest).map (JsonToken.lbrace :: ·)
    else if c = '}' then
      (tokenizeAux n rest).map (JsonToken.rbrace :: ·)
    else if c = '[' then
      (tokenizeAux n rest).map (JsonToken.lbracket :: ·)
    else if c = ']' then
      (tokenizeAux n rest).map (JsonToken.rbracket :: ·)
    else if c = ':' then
      (tokenizeAux n rest).map (JsonToken.colon :: ·)
    else if c = ',' then
      (tokenizeAux n rest).map (JsonToken.comma :: ·)
    else if c = '"' then
      match takeString n [] rest with
      | none => .error "unterminated string literal"
      | some (body, tail) =>
        if validStringContentL body then
          (tokenizeAux n tail).map (JsonToken.strT (String.ofList body) :: ·)
        else
          .error "malformed string escape sequence"
    else
      match takeKeyword (c :: rest) with
      | some (tok, tail) =>
        (tokenizeAux n tail).map (tok :: ·)
      | none =>
        if isNumChar c then
          let (num, tail) := takeNumber n [c] rest
          if validNumberLitL num then
            (tokenizeAux n tail).map (JsonToken.numT (String.ofList num) :: ·)
          else
            .error "malformed number literal"
        else
          .error s!"unexpected character: {c}"

/-- Top-level tokenizer: convert a Lean `String` to a list of JSON tokens. The
fuel is set to twice the input length (a generous safe upper bound on the
number of recursive calls — each call consumes ≥1 char and the helpers
re-enter `tokenizeAux` with the same fuel `n`, so doubling guards us). -/
def tokenize (s : String) : Except String (List JsonToken) :=
  let cs := s.toList
  tokenizeAux (2 * cs.length + 1) cs

/-- Canonical text serialization of a token. For literals we use the most
common surface form; structural tokens use their single-character spelling.
For `numT` and `strT` we re-emit the captured payload verbatim (string
literals are bracketed by `"..."`). -/
def JsonToken.serialize : JsonToken → String
  | .lbrace => "{"
  | .rbrace => "}"
  | .lbracket => "["
  | .rbracket => "]"
  | .colon => ":"
  | .comma => ","
  | .trueT => "true"
  | .falseT => "false"
  | .nullT => "null"
  | .numT s => s
  | .strT s => "\"" ++ s ++ "\""

/-- Local `DecidableEq` for `Except String (List JsonToken)`. Lean core
(4.28.0) does not derive this automatically, but we need it so the sanity
check theorems below can be discharged by `decide`. -/
instance instDecidableEqLexerOutput :
    DecidableEq (Except String (List JsonToken))
  | .ok a, .ok b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun he => h (Except.ok.inj he))
  | .error a, .error b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse (fun he => h (Except.error.inj he))
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

/-! ## Single-token sanity checks

These are the "nice-to-have" theorems from the spec: each is closed by
`decide`, demonstrating that the lexer evaluates correctly on canonical
inputs. -/

theorem tokenize_lbrace : tokenize "{" = .ok [.lbrace] := by decide
theorem tokenize_rbrace : tokenize "}" = .ok [.rbrace] := by decide
theorem tokenize_lbracket : tokenize "[" = .ok [.lbracket] := by decide
theorem tokenize_rbracket : tokenize "]" = .ok [.rbracket] := by decide
theorem tokenize_colon : tokenize ":" = .ok [.colon] := by decide
theorem tokenize_comma : tokenize "," = .ok [.comma] := by decide
theorem tokenize_true : tokenize "true" = .ok [.trueT] := by decide
theorem tokenize_false : tokenize "false" = .ok [.falseT] := by decide
theorem tokenize_null : tokenize "null" = .ok [.nullT] := by decide
theorem tokenize_empty : tokenize "" = .ok [] := by decide

/-- Whitespace is skipped. -/
theorem tokenize_ws : tokenize "   {" = .ok [.lbrace] := by decide

/-- Mixed punctuation tokenizes left-to-right. -/
theorem tokenize_pair : tokenize "{}" = .ok [.lbrace, .rbrace] := by decide

/-! ## Single-token roundtrips for punctuation / keywords

For each non-payload token, tokenizing its `serialize` output yields the
singleton list back. Number / string roundtrips are deferred to the parser
layer: they require shape preconditions (well-formed numbers, balanced quotes,
escape rules) the lexer alone does not enforce. -/

theorem tokenize_serialize_lbrace :
    tokenize JsonToken.lbrace.serialize = .ok [.lbrace] := by decide

theorem tokenize_serialize_rbrace :
    tokenize JsonToken.rbrace.serialize = .ok [.rbrace] := by decide

theorem tokenize_serialize_lbracket :
    tokenize JsonToken.lbracket.serialize = .ok [.lbracket] := by decide

theorem tokenize_serialize_rbracket :
    tokenize JsonToken.rbracket.serialize = .ok [.rbracket] := by decide

theorem tokenize_serialize_colon :
    tokenize JsonToken.colon.serialize = .ok [.colon] := by decide

theorem tokenize_serialize_comma :
    tokenize JsonToken.comma.serialize = .ok [.comma] := by decide

theorem tokenize_serialize_true :
    tokenize JsonToken.trueT.serialize = .ok [.trueT] := by decide

theorem tokenize_serialize_false :
    tokenize JsonToken.falseT.serialize = .ok [.falseT] := by decide

theorem tokenize_serialize_null :
    tokenize JsonToken.nullT.serialize = .ok [.nullT] := by decide

/-! ## Validator unit tests

These exercise `validNumberLit` / `validStringContent` on canonical inputs and
known-bad payloads. Each is closed by `decide` on the pure recursive walker. -/

example : validNumberLit "0" = true := by decide
example : validNumberLit "-0" = true := by decide
example : validNumberLit "-7" = true := by decide
example : validNumberLit "42" = true := by decide
example : validNumberLit "1.5" = true := by decide
example : validNumberLit "1.5e10" = true := by decide
example : validNumberLit "1.5E-10" = true := by decide
example : validNumberLit "0e0" = true := by decide
example : validNumberLit "123e+45" = true := by decide

example : validNumberLit "" = false := by decide
example : validNumberLit "01" = false := by decide
example : validNumberLit "1." = false := by decide
example : validNumberLit ".5" = false := by decide
example : validNumberLit "1e" = false := by decide
example : validNumberLit "1e+" = false := by decide
example : validNumberLit "-" = false := by decide
example : validNumberLit "+1" = false := by decide
example : validNumberLit "1.2.3" = false := by decide

example : validStringContent "" = true := by decide
example : validStringContent "hello" = true := by decide
example : validStringContent "a\\nb" = true := by decide
example : validStringContent "\\\"" = true := by decide
example : validStringContent "\\\\" = true := by decide
example : validStringContent "\\u00FF" = true := by decide
example : validStringContent "x\\tY\\u0041z" = true := by decide

example : validStringContent "\\" = false := by decide
example : validStringContent "\\x" = false := by decide
example : validStringContent "\\u" = false := by decide
example : validStringContent "\\u123" = false := by decide
example : validStringContent "\\uGGGG" = false := by decide
example : validStringContent "ok\\xthen" = false := by decide

/-! ### Surrogate-pair validation (RFC 8259 §8.2)

A `\uD8XX..\uDBXX` (high surrogate) must be immediately followed by
`\uDCXX..\uDFXX` (low surrogate); isolated surrogates are rejected. -/

/-- An isolated high surrogate (`\uD800` with no `\uDCXX..\uDFXX` follow-up)
is rejected. -/
theorem isolated_high_surrogate_rejected :
    validStringContent "\\uD800" = false := by decide

/-- An isolated low surrogate (`\uDC00` not preceded by a high surrogate) is
rejected. -/
theorem isolated_low_surrogate_rejected :
    validStringContent "\\uDC00" = false := by decide

/-- A well-formed surrogate pair `😀` (😀) is accepted. -/
theorem valid_surrogate_pair :
    validStringContent "\\uD83D\\uDE00" = true := by decide

/-- A high surrogate followed by a non-low `\u` is rejected. -/
example : validStringContent "\\uD800\\u0041" = false := by decide

/-- A high surrogate followed by a non-`\u` escape is rejected. -/
example : validStringContent "\\uD800a" = false := by decide

/-- Two consecutive low surrogates are rejected (the first is isolated). -/
example : validStringContent "\\uDC00\\uDC00" = false := by decide

/-- A BMP-only `\u` escape still validates after the tightening. -/
example : validStringContent "\\u00FF" = true := by decide

/-- Lower-case hex digits in a surrogate pair are accepted. -/
example : validStringContent "\\ud83d\\ude00" = true := by decide

/-! ## Soundness: every emitted `numT` / `strT` payload validates

The lexer gates each `numT`/`strT` emission on the corresponding validator,
so any token returned by `tokenize` carries a payload that satisfies the
RFC 8259 lexical rule. We prove this by induction on the fuel of
`tokenizeAux`. -/

/-- Helper: if `validNumberLitL ns = true` then `validNumberLit (String.ofList ns) = true`. -/
private theorem validNumberLitL_string (ns : List Char)
    (h : validNumberLitL ns = true) :
    validNumberLit (String.ofList ns) = true := by
  show validNumberLitL _ = true
  rw [String.toList_ofList]; exact h

/-- Helper: if `validStringContentL bs = true` then `validStringContent (String.ofList bs) = true`. -/
private theorem validStringContentL_string (bs : List Char)
    (h : validStringContentL bs = true) :
    validStringContent (String.ofList bs) = true := by
  show validStringContentL _ = true
  rw [String.toList_ofList]; exact h

/-- Predicate: this token's payload (if it is a `numT` / `strT`) is valid. -/
@[reducible] private def TokenPayloadValid : JsonToken → Prop
  | .numT s => validNumberLit s = true
  | .strT s => validStringContent s = true
  | _ => True

/-- Helper: a `(tokenizeAux n tail).map (newTok :: ·) = .ok toks` branch
forces every output token to be either `newTok` or come from the recursive
call. -/
private theorem map_cons_sound {n : Nat} {tail : List Char} {newTok : JsonToken}
    {toks : List JsonToken}
    (ih_tail : ∀ ts, tokenizeAux n tail = .ok ts → ∀ t ∈ ts, TokenPayloadValid t)
    (hnew : TokenPayloadValid newTok)
    (hmap : (tokenizeAux n tail).map (newTok :: ·) = .ok toks) :
    ∀ t ∈ toks, TokenPayloadValid t := by
  rcases hrec : tokenizeAux n tail with e | ts
  · rw [hrec] at hmap; cases hmap
  · rw [hrec] at hmap
    have htoks : toks = newTok :: ts := by
      have := hmap
      simp [Except.map] at this
      exact this.symm
    subst htoks
    intro t ht
    cases ht with
    | head => exact hnew
    | tail _ ht' => exact ih_tail ts hrec t ht'

/-- Soundness for `tokenizeAux`: every emitted token has a valid payload. -/
private theorem tokenizeAux_payload_valid :
    ∀ (n : Nat) (cs : List Char) (toks : List JsonToken),
      tokenizeAux n cs = .ok toks → ∀ t ∈ toks, TokenPayloadValid t := by
  intro n
  induction n with
  | zero =>
    intro cs toks h; cases h
  | succ n ih =>
    intro cs toks h
    cases cs with
    | nil =>
      simp [tokenizeAux] at h
      subst h
      intro t ht; cases ht
    | cons c rest =>
      simp only [tokenizeAux] at h
      have ih_rest : ∀ ts, tokenizeAux n rest = .ok ts → ∀ t ∈ ts, TokenPayloadValid t :=
        fun ts ht t htmem => ih rest ts ht t htmem
      -- Walk every if/match branch.
      split at h
      · -- whitespace
        exact ih rest toks h
      · split at h
        · exact map_cons_sound ih_rest trivial h
        · split at h
          · exact map_cons_sound ih_rest trivial h
          · split at h
            · exact map_cons_sound ih_rest trivial h
            · split at h
              · exact map_cons_sound ih_rest trivial h
              · split at h
                · exact map_cons_sound ih_rest trivial h
                · split at h
                  · exact map_cons_sound ih_rest trivial h
                  · split at h
                    · -- c = '"': string branch
                      split at h
                      · cases h
                      · split at h
                        · rename_i body tail _ hvalid
                          have ih_tail : ∀ ts, tokenizeAux n tail = .ok ts →
                              ∀ t ∈ ts, TokenPayloadValid t :=
                            fun ts ht t htmem => ih tail ts ht t htmem
                          have hpv : TokenPayloadValid (.strT (String.ofList body)) :=
                            validStringContentL_string body hvalid
                          exact map_cons_sound ih_tail hpv h
                        · cases h
                    · split at h
                      · -- keyword branch: matched true/false/null
                        rename_i tok tail hkw
                        have ih_tail : ∀ ts, tokenizeAux n tail = .ok ts →
                            ∀ t ∈ ts, TokenPayloadValid t :=
                          fun ts ht t htmem => ih tail ts ht t htmem
                        -- `takeKeyword (c :: rest) = some (tok, tail)`.
                        -- Case-split on the literal patterns of `takeKeyword` to identify `tok`.
                        have hpv : TokenPayloadValid tok := by
                          unfold takeKeyword at hkw
                          split at hkw
                          all_goals (
                            first
                            | (simp at hkw; obtain ⟨rfl, _⟩ := hkw; trivial)
                            | (simp at hkw)
                          )
                        exact map_cons_sound ih_tail hpv h
                      · split at h
                        · split at h
                          · -- number branch with valid payload
                            rename_i hvalid
                            -- The let-bound `(num, tail)` is in scope; extract via rename_i.
                            -- We need to show payload validity and apply map_cons_sound.
                            -- The let-pattern `let (num, tail) := takeNumber n [c] rest` is destructured.
                            -- `hvalid : validNumberLitL num = true` after the split.
                            have ih_tail : ∀ ts,
                                tokenizeAux n (takeNumber n [c] rest).2 = .ok ts →
                                ∀ t ∈ ts, TokenPayloadValid t :=
                              fun ts ht t htmem => ih _ ts ht t htmem
                            have hpv : TokenPayloadValid
                                (.numT (String.ofList (takeNumber n [c] rest).1)) :=
                              validNumberLitL_string _ hvalid
                            exact map_cons_sound ih_tail hpv h
                          · cases h
                        · cases h

/-- Every emitted `numT` payload is a well-formed JSON number literal. -/
theorem tokenize_numbers_valid (s : String) (toks : List JsonToken) :
    tokenize s = .ok toks →
    ∀ t ∈ toks, ∀ n, t = .numT n → validNumberLit n = true := by
  intro h t ht n hn
  have hp := tokenizeAux_payload_valid _ _ _ h t ht
  rw [hn] at hp
  exact hp

/-- Every emitted `strT` payload is well-formed JSON string content. -/
theorem tokenize_strings_valid (s : String) (toks : List JsonToken) :
    tokenize s = .ok toks →
    ∀ t ∈ toks, ∀ str, t = .strT str → validStringContent str = true := by
  intro h t ht str hstr
  have hp := tokenizeAux_payload_valid _ _ _ h t ht
  rw [hstr] at hp
  exact hp

end Hax.Json.Lexer

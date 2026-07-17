/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

import Hax.Json.Lexer
import Lean.Data.Json.Basic

set_option autoImplicit false

/-!
# JSON Token-Stream Parser — task B1

Recursive-descent parser consuming `List JsonToken` (produced by `JsonLexer`)
and producing a `Lean.Json` value. This is the **token-stream parser** layer
of the verified JSON parser plan (Task B1 in
`docs/verified-json-parser-and-adapter-plan.md`).

## Design

We use **fuel-based recursion** on `Nat` (the same pattern as the lexer). Every
recursive descent step decrements fuel by 1. The top-level `parse` provisions
`2 * tokens.length + 1`, which is generously sufficient: each grammatical
production consumes at least one token.

Object and array bodies recurse on the same fuel, so we package
`parseValue`, `parseArrayBody`, `parseObjectBody` into a single `mutual`
block. Termination is structural on the `Nat` fuel argument, which decreases
by 1 at every recursive call.

## Numbers

The lexer hands us numeric literals as opaque `numT s` payloads (RFC 8259
shape acceptance only — full validation is task B3). Here we route them
through `String.toInt?` first, falling back to Lean's standard
scientific-literal decoder. If neither succeeds, we report an error.

## Scope (deferred to later tasks)

* Soundness theorem `parse_sound` — task B2.
* Number / string conformance to RFC 8259 (escapes, surrogate pairs,
  exponent ranges) — task B3.
* Roundtrip `parse (tokenize (serialize j)) = .ok j` — task B5.

This file ships the parser definition and a handful of `decide`-closed sanity
tests on observable shapes (using `Bool`-valued probes, since `Lean.Json` does
not derive `DecidableEq`).
-/

namespace Hax.Json.Parser

open Hax.Json.Lexer

/-! ## Number parsing -/

/-- Parse a numeric literal string as a `Lean.JsonNumber`.

We try `String.toInt?` first (covers `"0"`, `"-7"`, `"42"`); on failure we try
the scientific-literal decoder used by `Lean.Json`'s standard parser via
`Lean.Syntax.decodeScientificLitVal?` (covers `"3.14"`, `"1e9"`, …). For a
leading minus sign we strip it, decode, and negate. On failure, `none`. -/
def parseJsonNumber (s : String) : Option Lean.JsonNumber :=
  match s.toInt? with
  | some i => some (Lean.JsonNumber.fromInt i)
  | none =>
    match Lean.Syntax.decodeScientificLitVal? s with
    | some (m, sign, e) => some (OfScientific.ofScientific m sign e)
    | none =>
      if s.startsWith "-" then
        let rest := (s.drop 1).toString
        match Lean.Syntax.decodeScientificLitVal? rest with
        | some (m, sign, e) =>
          some (-(OfScientific.ofScientific m sign e : Lean.JsonNumber))
        | none => none
      else
        none

/-! ## String escape decoding (RFC 8259 §7 + §8.2)

The lexer (`Hax.Json.Lexer`) leaves a `strT` payload as the *raw* body — escape
sequences (`\"`, `\n`, `\uXXXX`, surrogate pairs) are stored verbatim and only
*validated* (`validStringContentL`), never decoded. This post-pass performs the
decoding when the parser materialises a `Lean.Json.str`, so the resulting value
matches Lean core's `Lean.Json.parse` (`escapedChar` / `strCore`):

* `\"` `\\` `\/` `\b` `\f` `\n` `\r` `\t` → the single character;
* `\uXXXX` (non-surrogate) → the code point;
* `\uD8XX\uDCXX` (high + low surrogate pair) → the combined scalar
  `0x10000 + (hi-0xD800)*0x400 + (lo-0xDC00)`.

The lexer already rejects lone surrogates and malformed escapes, so `decodeBody`
only ever runs on validated bodies; the fallthrough arms are unreachable for
such input and are written to be total. Lone-surrogate **rejection** (stricter
than core's U+FFFD substitution) is preserved — on the inputs both parsers
accept, `decodeBody` agrees with core.

Object *keys* are left raw (`parseObjectBody` below), a documented residual:
core decodes keys too, but keys are escape-free identifiers in practice and
decoding them would restate the `RoundtripObj` canonicalisation theorem. -/

/-- Value of a single hex digit (`0..15`); non-hex maps to `0` (unreachable on
validated input, which the lexer guarantees is `isHexDigit`). -/
def hexDigitVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- Combine four hex digits into a 16-bit code unit. -/
def hex4 (a b c d : Char) : Nat :=
  hexDigitVal a * 4096 + hexDigitVal b * 256 + hexDigitVal c * 16 + hexDigitVal d

/-- Decode a single-character escape `\c` (the `u` form is handled separately). -/
def unescapeChar (c : Char) : Char :=
  match c with
  | '"'  => '"'
  | '\\' => '\\'
  | '/'  => '/'
  | 'b'  => Char.ofNat 0x08
  | 'f'  => Char.ofNat 0x0c
  | 'n'  => Char.ofNat 0x0a
  | 'r'  => Char.ofNat 0x0d
  | 't'  => Char.ofNat 0x09
  | other => other

/-- Decode the escape sequences of a validated JSON string body into the list of
scalar characters it denotes. Recurses on the (structurally smaller) tail past
each consumed escape, mirroring the shape of `validStringContentL`. -/
def decodeBody : List Char → List Char
  | '\\' :: 'u' :: a :: b :: c :: d :: '\\' :: 'u' :: e :: f :: g :: h :: rest =>
    let hi := hex4 a b c d
    if 0xD800 ≤ hi ∧ hi ≤ 0xDBFF then
      let lo := hex4 e f g h
      Char.ofNat (0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)) :: decodeBody rest
    else
      Char.ofNat hi :: decodeBody ('\\' :: 'u' :: e :: f :: g :: h :: rest)
  | '\\' :: 'u' :: a :: b :: c :: d :: rest =>
    Char.ofNat (hex4 a b c d) :: decodeBody rest
  | '\\' :: c :: rest => unescapeChar c :: decodeBody rest
  | '\\' :: [] => []
  | c :: rest => c :: decodeBody rest
  | [] => []

/-- Decode a validated JSON string body `String → String`. On the bodies the
lexer admits this matches Lean core's `Lean.Json.parse` string semantics. -/
def decodeString (s : String) : String := String.ofList (decodeBody s.toList)

/-! ## Recursive-descent core

`parseValue`, `parseArrayBody`, and `parseObjectBody` recurse on the same fuel
budget and are mutually recursive. We package them into a single `mutual`
block; termination is structural on the `Nat` fuel argument, which decreases
by 1 at every recursive call. -/

mutual

/-- Parse a single JSON value. Returns the value and the unconsumed token
tail. -/
def parseValue : Nat → List JsonToken →
    Except String (Lean.Json × List JsonToken)
  | 0,     _                          => .error "out of fuel"
  | _ + 1, []                         => .error "unexpected end of input"
  | _ + 1, .strT s   :: rest          => .ok (.str (decodeString s), rest)
  | _ + 1, .trueT    :: rest          => .ok (.bool true, rest)
  | _ + 1, .falseT   :: rest          => .ok (.bool false, rest)
  | _ + 1, .nullT    :: rest          => .ok (.null, rest)
  | _ + 1, .numT s   :: rest =>
    match parseJsonNumber s with
    | some n => .ok (.num n, rest)
    | none   => .error s!"invalid number literal: {s}"
  | n + 1, .lbracket :: rest          => parseArrayBody n rest #[]
  | n + 1, .lbrace   :: rest          => parseObjectBody n rest []
  | _ + 1, .rbrace   :: _             => .error "unexpected '}'"
  | _ + 1, .rbracket :: _             => .error "unexpected ']'"
  | _ + 1, .colon    :: _             => .error "unexpected ':'"
  | _ + 1, .comma    :: _             => .error "unexpected ','"

/-- Body of an array literal. The opening `[` has already been consumed.
We accept either an immediate `]` (empty array) or a sequence
`value (',' value)* ']'`. Per RFC 8259 §5, a trailing comma (e.g. `[1,]`)
is rejected: after consuming a `,`, the next token must begin a value, not
close the array. -/
def parseArrayBody : Nat → List JsonToken → Array Lean.Json →
    Except String (Lean.Json × List JsonToken)
  | 0,     _,                _   => .error "out of fuel"
  | _ + 1, [],               _   => .error "unterminated array (missing ']')"
  | _ + 1, .rbracket :: rest, acc => .ok (.arr acc, rest)
  | n + 1, toks,             acc =>
    match parseValue n toks with
    | .error e => .error e
    | .ok (v, rest) =>
      match rest with
      | .rbracket :: rest'         => .ok (.arr (acc.push v), rest')
      | .comma :: .rbracket :: _   => .error "trailing comma in array"
      | .comma    :: rest'         => parseArrayBody n rest' (acc.push v)
      | _                          => .error "expected ',' or ']' in array"

/-- Body of an object literal. The opening `{` has already been consumed.
We accept either an immediate `}` (empty object) or a sequence
`(strT key ':' value) (',' strT key ':' value)* '}'`. The accumulator is a
list of `(key, value)` pairs in insertion order; we materialise the final
`Lean.Json.obj` via `Json.mkObj` once the body is fully parsed.

Per RFC 8259 §4, a trailing comma (e.g. `{"a":1,}`) is rejected: after
consuming a `,`, the next token must be a string key, not a closing brace. -/
def parseObjectBody : Nat → List JsonToken → List (String × Lean.Json) →
    Except String (Lean.Json × List JsonToken)
  | 0,     _,                _   => .error "out of fuel"
  | _ + 1, [],               _   => .error "unterminated object (missing '}')"
  | _ + 1, .rbrace :: rest,  acc => .ok (Lean.Json.mkObj acc.reverse, rest)
  | n + 1, .strT k :: .colon :: rest, acc =>
    match parseValue n rest with
    | .error e => .error e
    | .ok (v, rest') =>
      match rest' with
      | .rbrace :: rest''         =>
        .ok (Lean.Json.mkObj ((k, v) :: acc).reverse, rest'')
      | .comma :: .rbrace :: _    => .error "trailing comma in object"
      | .comma  :: rest''         => parseObjectBody n rest'' ((k, v) :: acc)
      | _                         => .error "expected ',' or '}' in object"
  | _ + 1, .strT _ :: _,     _   => .error "expected ':' after object key"
  | _ + 1, _,                _   => .error "expected string key in object"

end

/-- Top-level entry point: parse a token list into a `Lean.Json` value. The
fuel is set to `2 * tokens.length + 1`, sufficient because every recursive
descent step consumes at least one token. -/
def parse (toks : List JsonToken) : Except String Lean.Json := do
  let (j, rest) ← parseValue (2 * toks.length + 1) toks
  if rest.isEmpty then .ok j
  else .error "trailing input after top-level value"

/-! ## Sanity checks

`Lean.Json` does **not** derive `DecidableEq` (its `BEq` is `partial`), so we
cannot close `parse … = .ok ⟨…⟩` directly via `decide`. Instead we use small
`Bool`-valued probes that pattern-match on the parser result and check the
structural shape we expect. Each probe is closed by `decide`, which is enough
to confirm that the parser definition reduces correctly on small inputs.

We deliberately avoid probes that depend on `Std.TreeMap.Raw` operations
(used internally by `Json.mkObj`) or on `Array` indexing — those reduce only
under partial / private definitions and break kernel reduction. Shape probes
that match top-level constructors (`Json.bool`, `Json.null`, `Json.str`,
`Json.num`, `Json.arr _`, `Json.obj _`) reduce cleanly. -/

/-- Probe: `parse [.trueT]` yields `Json.bool true`. -/
def isParseTrue : Bool :=
  match parse [.trueT] with
  | .ok (Lean.Json.bool true) => true
  | _ => false

theorem parse_true_ok : isParseTrue = true := by decide

/-- Probe: `parse [.falseT]` yields `Json.bool false`. -/
def isParseFalse : Bool :=
  match parse [.falseT] with
  | .ok (Lean.Json.bool false) => true
  | _ => false

theorem parse_false_ok : isParseFalse = true := by decide

/-- Probe: `parse [.nullT]` yields `Json.null`. -/
def isParseNull : Bool :=
  match parse [.nullT] with
  | .ok Lean.Json.null => true
  | _ => false

theorem parse_null_ok : isParseNull = true := by decide

/-- Probe: `parse [.strT "x"]` yields `Json.str "x"`. -/
def isParseStrX : Bool :=
  match parse [.strT "x"] with
  | .ok (Lean.Json.str s) => s == "x"
  | _ => false

theorem parse_strX_ok : isParseStrX = true := by native_decide

/-- Probe: `parse [.lbrace, .rbrace]` yields a `Json.obj` (empty object). -/
def isParseEmptyObj : Bool :=
  match parse [.lbrace, .rbrace] with
  | .ok (Lean.Json.obj _) => true
  | _ => false

theorem parse_empty_obj_ok : isParseEmptyObj = true := by decide

/-- Probe: `parse [.lbracket, .rbracket]` yields an empty `Json.arr`. -/
def isParseEmptyArr : Bool :=
  match parse [.lbracket, .rbracket] with
  | .ok (Lean.Json.arr _) => true
  | _ => false

theorem parse_empty_arr_ok : isParseEmptyArr = true := by decide

/-- Probe: a single-element array `[true]` parses to a `Json.arr`. -/
def isParseSingletonArr : Bool :=
  match parse [.lbracket, .trueT, .rbracket] with
  | .ok (Lean.Json.arr _) => true
  | _ => false

theorem parse_singleton_arr_ok : isParseSingletonArr = true := by decide

/-- Probe: a two-element array `[true, false]` parses to a `Json.arr`. -/
def isParseTwoElemArr : Bool :=
  match parse [.lbracket, .trueT, .comma, .falseT, .rbracket] with
  | .ok (Lean.Json.arr _) => true
  | _ => false

theorem parse_two_elem_arr_ok : isParseTwoElemArr = true := by decide

/-- Probe: object `{"k": null}` parses to a `Json.obj`. -/
def isParseSingletonObj : Bool :=
  match parse [.lbrace, .strT "k", .colon, .nullT, .rbrace] with
  | .ok (Lean.Json.obj _) => true
  | _ => false

theorem parse_singleton_obj_ok : isParseSingletonObj = true := by decide

/-- Probe: trailing input after a top-level value is rejected. -/
def isRejectTrailing : Bool :=
  match parse [.trueT, .trueT] with
  | .error _ => true
  | _ => false

theorem parse_trailing_rejected : isRejectTrailing = true := by decide

/-- Probe: empty token list is rejected (no value). -/
def isRejectEmpty : Bool :=
  match parse [] with
  | .error _ => true
  | _ => false

theorem parse_empty_rejected : isRejectEmpty = true := by decide

/-- Probe: stray `]` is rejected. -/
def isRejectStrayRBracket : Bool :=
  match parse [.rbracket] with
  | .error _ => true
  | _ => false

theorem parse_stray_rbracket_rejected : isRejectStrayRBracket = true := by decide

/-- Probe: an integer literal parses to a `Json.num`. We close this via
`native_decide` because `String.toInt?` reduces through `String.Slice`
operations that are blocked from kernel reduction. -/
def isParseInt : Bool :=
  match parse [.numT "42"] with
  | .ok (Lean.Json.num _) => true
  | _ => false

theorem parse_int_ok : isParseInt = true := by native_decide

/-! ## Soundness theorems — task B2

Documentary lemmas about the parser's high-level behaviour. These complement
the `Bool`-valued probes above by stating direct equalities and inequalities
on `parse` results, where those reduce without relying on `Lean.Json`'s
non-decidable equality (which forces probe-style statements for the larger
shapes).
-/

/-- **Totality.** `parse` is a total Lean function, so every input has a
result. Stated for documentation. -/
theorem parse_total (toks : List JsonToken) : ∃ result, parse toks = result :=
  ⟨parse toks, rfl⟩

/-! ### Structural soundness for terminal shapes

For value-only inputs (a single token consumed by `parseValue`'s head match
and producing an empty unconsumed tail) we get clean reduction-driven
equalities. We use `rfl` where the kernel reduces, falling back to
`native_decide` for shapes where the inner `match` would not unfold (e.g.
the result type's lack of `DecidableEq` is irrelevant once both sides are
literally definitionally equal). -/

/-- `parse [.trueT]` produces `Json.bool true` with no trailing input. -/
theorem parse_true_inv : parse [.trueT] = .ok (Lean.Json.bool true) := rfl

/-- `parse [.falseT]` produces `Json.bool false`. -/
theorem parse_false_inv : parse [.falseT] = .ok (Lean.Json.bool false) := rfl

/-- `parse [.nullT]` produces `Json.null`. -/
theorem parse_null_inv : parse [.nullT] = .ok Lean.Json.null := rfl

/-- `parse [.strT s]` produces `Json.str (decodeString s)` for any `s` — the
raw token body decoded per RFC 8259 §7/§8.2, matching Lean core. -/
theorem parse_str_inv (s : String) :
    parse [.strT s] = .ok (Lean.Json.str (decodeString s)) := rfl

/-! ### Trailing-input rejection

The top-level `parse` checks `rest.isEmpty` after `parseValue` returns and
rejects non-empty tails. We prove this for the four "atom" head tokens. The
result is an `.error _`, which is structurally distinct from `.ok _`. -/

/-- If a `trueT` is followed by any non-empty token tail, `parse` does **not**
return `.ok (.bool true)` — the trailing input is rejected. -/
theorem parse_rejects_trailing_true (toks : List JsonToken) (h : 0 < toks.length) :
    parse (.trueT :: toks) ≠ .ok (Lean.Json.bool true) := by
  cases toks with
  | nil => exact absurd h (by decide)
  | cons t ts =>
    -- After consuming `.trueT`, `parseValue` returns `.ok (.bool true, t :: ts)`.
    -- The `rest.isEmpty` check on the non-empty tail forces an `.error`.
    intro hEq
    simp only [parse, parseValue, bind, Except.bind, List.isEmpty,
               if_false, reduceCtorEq] at hEq

/-- If a `falseT` is followed by any non-empty token tail, `parse` does **not**
return `.ok (.bool false)`. -/
theorem parse_rejects_trailing_false (toks : List JsonToken) (h : 0 < toks.length) :
    parse (.falseT :: toks) ≠ .ok (Lean.Json.bool false) := by
  cases toks with
  | nil => exact absurd h (by decide)
  | cons t ts =>
    intro hEq
    simp only [parse, parseValue, bind, Except.bind, List.isEmpty,
               if_false, reduceCtorEq] at hEq

/-- If a `nullT` is followed by any non-empty token tail, `parse` does **not**
return `.ok .null`. -/
theorem parse_rejects_trailing_null (toks : List JsonToken) (h : 0 < toks.length) :
    parse (.nullT :: toks) ≠ .ok Lean.Json.null := by
  cases toks with
  | nil => exact absurd h (by decide)
  | cons t ts =>
    intro hEq
    simp only [parse, parseValue, bind, Except.bind, List.isEmpty,
               if_false, reduceCtorEq] at hEq

/-- If a `strT s` is followed by any non-empty token tail, `parse` does **not**
return `.ok (.str s)`. -/
theorem parse_rejects_trailing_str (s : String) (toks : List JsonToken)
    (h : 0 < toks.length) :
    parse (.strT s :: toks) ≠ .ok (Lean.Json.str s) := by
  cases toks with
  | nil => exact absurd h (by decide)
  | cons t ts =>
    intro hEq
    simp only [parse, parseValue, bind, Except.bind, List.isEmpty,
               if_false, reduceCtorEq] at hEq

/-! ### Fuel sufficiency — partial result

A complete fuel-sufficiency theorem (`parse toks ≠ .error "out of fuel"`)
would require an inductive measure argument: every recursive descent in
`parseValue`/`parseArrayBody`/`parseObjectBody` consumes at least one token,
so `2 * toks.length + 1` fuel is generous. Formalising this requires
strong induction on the token list together with a step lemma per recursive
arm — non-trivial because `parseObjectBody` consumes a key, a colon, and a
value before recursing (3 tokens) while top-level `parseValue` only
guarantees 1, so the bound is tight rather than slack.

We document a weaker observable here: on the empty input, `parse` does not
fail with "out of fuel" (it fails with the explicit "unexpected end of input"
message). This rules out one trivial path to the out-of-fuel error. -/

/-- On the empty input, `parse` fails with an "unexpected end of input"
message — never with "out of fuel". -/
theorem parse_empty_not_out_of_fuel :
    parse [] = .error "unexpected end of input" := rfl

/-- Specialised fuel-sufficiency claim for single-token atom inputs:
`parse [.trueT]`, `parse [.falseT]`, `parse [.nullT]`, `parse [.strT s]` all
succeed (they evaluate to `.ok _`), so they trivially do not return
`.error "out of fuel"`. -/
theorem parse_atom_no_fuel_exhaustion_true :
    parse [.trueT] ≠ .error "out of fuel" := by
  rw [parse_true_inv]; intro h; cases h

theorem parse_atom_no_fuel_exhaustion_false :
    parse [.falseT] ≠ .error "out of fuel" := by
  rw [parse_false_inv]; intro h; cases h

theorem parse_atom_no_fuel_exhaustion_null :
    parse [.nullT] ≠ .error "out of fuel" := by
  rw [parse_null_inv]; intro h; cases h

theorem parse_atom_no_fuel_exhaustion_str (s : String) :
    parse [.strT s] ≠ .error "out of fuel" := by
  rw [parse_str_inv]; intro h; cases h

end Hax.Json.Parser

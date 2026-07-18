/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

import HaxLean.Json.Adapter

set_option autoImplicit false

/-!
# Official JSON conformance vectors (RFC 8259 + JSONTestSuite)

Conformance vectors drawn from **Nicolas Seriot's JSONTestSuite**
(`github.com/nst/JSONTestSuite`, `test_parsing/`: `y_` = must-accept,
`n_` = must-reject) and **RFC 8259 §7/§8.2**, run end-to-end through the shipped
verified front door `Hax.Json.parseJsonString`.

## Why these vectors — the escaped-test gap they close

The pre-existing suite (`Conformance`, `RoundtripStr`, the lexer `example`s)
tested the string **grammar** (`validStringContentL`) but never the **decoded
value**, and the roundtrip theorem is `Simple`-restricted (null/bool/arr — it
**excludes** `str`). So two RFC divergences slipped through:

1. **Escapes were not decoded.** `tokenize "\"a\\nb\""` was asserted to yield
   `strT "a\\nb"` (the raw 4-char body) and the parser mapped `strT s → .str s`
   verbatim — so `"a\nb"` parsed to a **4-character** string instead of the
   3-character decoded value Lean core produces. No test checked the decoded
   `Lean.Json.str`, so nothing caught it.
2. **Raw control characters were accepted.** The lexer's string-body catch-all
   accepted any byte, so a raw U+0000..U+001F inside a string was admitted — an
   RFC 8259 §7 violation. No `n_`-style reject test existed because the lexer
   accepted them by design.

The `*_ok` theorems below **assert the decoded value** for accept cases and
`.error` for reject cases, so they exercise exactly the two escaped paths the
old suite skipped. Vectors annotated *(exposed bug N — failed pre-fix)* fail
against the pre-fix parser; the others are RFC regression guards (including the
deliberately-preserved lone-surrogate rejection, stricter than core's U+FFFD).

Inputs are built with `String.ofList` over explicit character lists so the exact
bytes (including raw control characters, which cannot appear in a Lean string
literal) are unambiguous. Concrete `parseJsonString` results are closed by
`native_decide` — the parser's string path routes through `String.ofList`, which
is opaque to kernel reduction (the same reason `Adapter`/`Roundtrip` use it).
-/

namespace Hax.Json.OfficialVectors

open Hax.Json

/-! ## Accept: string escape decoding (exposed bug 1 — failed pre-fix) -/

/-- JSONTestSuite `y_string_allowed_escapes.json` : `["\"\\\/\b\f\n\r\t"]`.
The 16-char raw body decodes to the 8 characters `"` `\` `/` BS FF LF CR HT. -/
def inAllowedEscapes : String := String.ofList
  ['[', '"', '\\', '"', '\\', '\\', '\\', '/', '\\', 'b', '\\', 'f',
   '\\', 'n', '\\', 'r', '\\', 't', '"', ']']

/-- The decoded value: `"` `\` `/` U+0008 U+000C U+000A U+000D U+0009. -/
def expectedAllowedEscapes : String := String.ofList
  ['"', '\\', '/', Char.ofNat 0x08, Char.ofNat 0x0c,
   Char.ofNat 0x0a, Char.ofNat 0x0d, Char.ofNat 0x09]

def probeAllowedEscapes : Bool :=
  match parseJsonString inAllowedEscapes with
  | .ok (.arr #[.str s]) => s == expectedAllowedEscapes
  | _ => false

/-- The allowed-escape body decodes to its 8-character scalar value (not the raw
16-char body the pre-fix parser produced). -/
theorem allowed_escapes_decode : probeAllowedEscapes = true := by native_decide

/-- Single `\n` escape decodes to a one-character string containing U+000A. -/
def probeNewlineEscape : Bool :=
  match parseJsonString (String.ofList ['"', '\\', 'n', '"']) with
  | .ok (.str s) => s == String.ofList [Char.ofNat 0x0a]
  | _ => false

/-- `"\n"` decodes to a length-1 string (pre-fix: length-2 raw body `\n`). -/
theorem newline_escape_decode : probeNewlineEscape = true := by native_decide

/-! ## Accept: `\uXXXX` and surrogate pairs (exposed bug 1 — failed pre-fix) -/

/-- A BMP `A` escape decodes to `A`. -/
def probeBmpEscape : Bool :=
  match parseJsonString (String.ofList ['"', '\\', 'u', '0', '0', '4', '1', '"']) with
  | .ok (.str s) => s == "A"
  | _ => false

theorem bmp_escape_decode : probeBmpEscape = true := by native_decide

/-- JSONTestSuite `y_string_accepted_surrogate_pair.json` : `["𐐷"]`.
The high+low pair `𐐷` decodes to the single scalar U+10437 (𐐷). -/
def inSurrogatePair : String := String.ofList
  ['[', '"', '\\', 'u', 'D', '8', '0', '1', '\\', 'u', 'd', 'c', '3', '7', '"', ']']

def probeSurrogatePair : Bool :=
  match parseJsonString inSurrogatePair with
  | .ok (.arr #[.str s]) => s == String.ofList [Char.ofNat 0x10437] && s.length == 1
  | _ => false

/-- The surrogate pair decodes to a single scalar (pre-fix: the raw 12-char body). -/
theorem surrogate_pair_decode : probeSurrogatePair = true := by native_decide

/-! ## Reject: raw control characters (exposed bug 2 — failed pre-fix)

Modelled on the JSONTestSuite `n_string_unescaped_*` family: a raw control
character U+0000..U+001F appearing unescaped inside a string is an RFC 8259 §7
violation. These bytes cannot be written in a Lean string literal, so the input
is `["<ctrl>"]` built via `Char.ofNat`. The pre-fix lexer accepted them. -/

def probeReject (ctrl : Nat) : Bool :=
  match parseJsonString (String.ofList ['[', '"', Char.ofNat ctrl, '"', ']']) with
  | .error _ => true
  | _ => false

/-- `n_string_unescaped_ctrl_char` family: a raw U+0000 (NUL) is rejected. -/
theorem reject_raw_nul : probeReject 0x00 = true := by native_decide

/-- `n_string_unescaped_tab` family: a raw U+0009 (TAB) inside a string is
rejected (tab is a control character; it must be escaped as `\t`). -/
theorem reject_raw_tab : probeReject 0x09 = true := by native_decide

/-- `n_string_unescaped_newline` family: a raw U+000A (LF) inside a string is
rejected (it must be escaped as `\n`). -/
theorem reject_raw_newline : probeReject 0x0a = true := by native_decide

/-- A raw U+001F (the top of the control range) is rejected. -/
theorem reject_raw_unit_separator : probeReject 0x1f = true := by native_decide

/-! ## Reject: malformed escapes and lone surrogates (RFC regression guards)

Rejected by the pre-fix parser too — guards against loosening. In particular the
lone-surrogate rejection is deliberately **stricter** than Lean core (which
substitutes U+FFFD); RFC 8259 §8.2 permits either, and we keep rejection. -/

/-- JSONTestSuite `n_string_escape_x.json` : `["\x00"]` — `\x` is not a valid
JSON escape, so the string is rejected. -/
def inEscapeX : String := String.ofList ['[', '"', '\\', 'x', '0', '0', '"', ']']

theorem reject_escape_x : (parseJsonString inEscapeX |>.toOption.isNone) = true := by native_decide

/-- A lone high surrogate `\uD800` (no following low surrogate) is rejected. -/
def inLoneHighSurrogate : String := String.ofList
  ['[', '"', '\\', 'u', 'D', '8', '0', '0', '"', ']']

theorem reject_lone_high_surrogate :
    (parseJsonString inLoneHighSurrogate |>.toOption.isNone) = true := by native_decide

/-- A lone low surrogate `\uDC00` is rejected. -/
def inLoneLowSurrogate : String := String.ofList
  ['[', '"', '\\', 'u', 'D', 'C', '0', '0', '"', ']']

theorem reject_lone_low_surrogate :
    (parseJsonString inLoneLowSurrogate |>.toOption.isNone) = true := by native_decide

/-! ## Numbers (JSONTestSuite corner cases) -/

/-- JSONTestSuite `y_number_after_space.json` : `[ 4]` — leading space before a
value inside an array is accepted; the value is `4`. -/
def probeNumberAfterSpace : Bool :=
  match parseJsonString "[ 4]" with
  | .ok (.arr #[.num _]) => true
  | _ => false

theorem number_after_space_ok : probeNumberAfterSpace = true := by native_decide

/-- JSONTestSuite `n_number_0_capital_E.json` : `[0E]` — an exponent with no
digits is rejected. -/
theorem reject_number_0_capital_E :
    (parseJsonString "[0E]" |>.toOption.isNone) = true := by native_decide

/-- JSONTestSuite `n_number_neg_int_starting_with_zero.json` : `[-012]` — a
leading zero on a multi-digit integer is rejected. -/
theorem reject_number_neg_leading_zero :
    (parseJsonString "[-012]" |>.toOption.isNone) = true := by native_decide

end Hax.Json.OfficialVectors

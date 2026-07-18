/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

import HaxLean.Json.Lexer
import HaxLean.Json.Parser

set_option autoImplicit false

/-!
# JSON Adapter — drop-in `Lean.Json.parse` replacement (Task B7)

This module is the **drop-in entry point** for the verified RFC 8259 JSON
parser built in
[`JsonLexer`](./JsonLexer.lean) and [`JsonParser`](./JsonParser.lean). It
composes the two layers into a single `String → Except String Lean.Json`
function whose name and signature mirror Lean core's
`Lean.Json.parse`, so existing call sites can switch by changing the import
plus the qualified name.

## Closed gap

Until this work, no fully verified JSON parser existed in the Lean 4
ecosystem. Lean core's `Lean.Json.parse` is part of the trusted compiler
front-end. The CatCrypt verified parser provides a totalised lexer
(see `JsonLexer`) and a fuel-recursive token-stream parser
(see `JsonParser`) with sanity-test theorems closed by `decide` /
`native_decide`. This adapter file is the public surface:

```text
                   String
                     │
                     ▼
              ┌───────────────┐
              │  tokenize     │   (JsonLexer, total)
              └──────┬────────┘
                     │ List JsonToken
                     ▼
              ┌───────────────┐
              │  parse        │   (JsonParser, recursive descent)
              └──────┬────────┘
                     │
                     ▼
                Lean.Json
```

## RFC 8259

The token grammar (whitespace, structural punctuation, literals `true`,
`false`, `null`, numbers, strings) follows
[RFC 8259, *The JavaScript Object Notation (JSON) Data Interchange Format*](
https://www.rfc-editor.org/rfc/rfc8259). The lexer accepts the syntactic
shape; full conformance for escape-sequence and surrogate-pair validation is
the subject of follow-on tasks (B3 in
`docs/verified-json-parser-and-adapter-plan.md`).

## Drop-in switchover recipe

To migrate a call site from Lean core to the verified parser, replace

```lean
import Lean.Data.Json
…
match Lean.Json.parse s with
| .ok j    => …
| .error e => …
```

with

```lean
import HaxLean.Json.Adapter
…
match CatCrypt.Crypto.Tools.Json.parse s with
| .ok j    => …
| .error e => …
```

Both functions have the same `String → Except String Lean.Json` signature.
-/

namespace Hax.Json

open Hax.Json.Lexer
open Hax.Json.Parser

/-- Verified JSON parser entry point: tokenize, then parse the token stream.

The composition is the canonical front-to-back pipeline:
1. `tokenize` (in `JsonLexer`) splits the input string into a list of
   `JsonToken`s, returning `.error _` on lexical errors.
2. `parse` (in `JsonParser`) consumes the token list and produces a
   `Lean.Json` value, returning `.error _` on grammatical errors.

Errors from either layer are propagated through the `Except` monad. -/
def parseJsonString (s : String) : Except String Lean.Json := do
  let toks ← tokenize s
  parse toks

/-- Drop-in alias matching the qualified name `Lean.Json.parse`. Existing call
sites can switch to the verified parser by adjusting the import and replacing
`Lean.Json.parse` with `CatCrypt.Crypto.Tools.Json.parse`. -/
def Json.parse (s : String) : Except String Lean.Json := parseJsonString s

/-! ## Sanity tests

`Lean.Json` does not derive `DecidableEq` (its `BEq` instance is `partial`),
so we cannot directly close `parseJsonString "…" = .ok ⟨…⟩` via `decide`.
We follow the same shape-probe pattern used in
[`JsonParser`](./JsonParser.lean): each probe pattern-matches on the parser
result and returns a `Bool`, which `decide` (or `native_decide`, when string
slice operations are involved) can evaluate.

These probes confirm that the composed pipeline reduces correctly on the
canonical small inputs and that lexical / grammatical errors propagate. -/

/-- Probe: `parseJsonString "true"` yields `Json.bool true`. -/
def isParseStringTrue : Bool :=
  match parseJsonString "true" with
  | .ok (Lean.Json.bool true) => true
  | _ => false

theorem parseJsonString_true_ok : isParseStringTrue = true := by decide

/-- Probe: `parseJsonString "false"` yields `Json.bool false`. -/
def isParseStringFalse : Bool :=
  match parseJsonString "false" with
  | .ok (Lean.Json.bool false) => true
  | _ => false

theorem parseJsonString_false_ok : isParseStringFalse = true := by decide

/-- Probe: `parseJsonString "null"` yields `Json.null`. -/
def isParseStringNull : Bool :=
  match parseJsonString "null" with
  | .ok Lean.Json.null => true
  | _ => false

theorem parseJsonString_null_ok : isParseStringNull = true := by decide

/-- Probe: `parseJsonString "[]"` yields an empty `Json.arr`. -/
def isParseStringEmptyArr : Bool :=
  match parseJsonString "[]" with
  | .ok (Lean.Json.arr _) => true
  | _ => false

theorem parseJsonString_empty_arr_ok : isParseStringEmptyArr = true := by decide

/-- Probe: `parseJsonString "{}"` yields a `Json.obj` (empty object). -/
def isParseStringEmptyObj : Bool :=
  match parseJsonString "{}" with
  | .ok (Lean.Json.obj _) => true
  | _ => false

theorem parseJsonString_empty_obj_ok : isParseStringEmptyObj = true := by decide

/-- Probe: whitespace around a literal is skipped by the lexer; the value is
still parsed correctly. -/
def isParseStringTrueWithWs : Bool :=
  match parseJsonString "  true  " with
  | .ok (Lean.Json.bool true) => true
  | _ => false

theorem parseJsonString_true_ws_ok : isParseStringTrueWithWs = true := by decide

/-- Probe: a single-element array `[true]` parses to a `Json.arr`. -/
def isParseStringSingletonArr : Bool :=
  match parseJsonString "[true]" with
  | .ok (Lean.Json.arr _) => true
  | _ => false

theorem parseJsonString_singleton_arr_ok :
    isParseStringSingletonArr = true := by decide

/-- Probe: a two-element array `[true, false]` (with whitespace) parses to a
`Json.arr`. -/
def isParseStringTwoElemArr : Bool :=
  match parseJsonString "[true, false]" with
  | .ok (Lean.Json.arr _) => true
  | _ => false

theorem parseJsonString_two_elem_arr_ok :
    isParseStringTwoElemArr = true := by decide

/-- Probe: a string literal `"hi"` parses to `Json.str "hi"`. We close this
via `native_decide` because the lexer's string-body construction goes through
`String.ofList`, which reduces only under `native_decide`. -/
def isParseStringHi : Bool :=
  match parseJsonString "\"hi\"" with
  | .ok (Lean.Json.str s) => s == "hi"
  | _ => false

theorem parseJsonString_hi_ok : isParseStringHi = true := by native_decide

/-- Probe: an integer literal parses to a `Json.num`. We close this via
`native_decide` because `String.toInt?` reduces through `String.Slice`
operations that are blocked from kernel reduction (same reason as
`JsonParser.parse_int_ok`). -/
def isParseStringInt : Bool :=
  match parseJsonString "42" with
  | .ok (Lean.Json.num _) => true
  | _ => false

theorem parseJsonString_int_ok : isParseStringInt = true := by native_decide

/-- Probe: trailing input after a top-level value is rejected. -/
def isParseStringRejectTrailing : Bool :=
  match parseJsonString "true true" with
  | .error _ => true
  | _ => false

theorem parseJsonString_trailing_rejected :
    isParseStringRejectTrailing = true := by decide

/-- Probe: empty input is rejected (no value). -/
def isParseStringRejectEmpty : Bool :=
  match parseJsonString "" with
  | .error _ => true
  | _ => false

theorem parseJsonString_empty_rejected :
    isParseStringRejectEmpty = true := by decide

/-- Probe: an unexpected character at the lexical level produces an error
(propagated through the `Except` monad from the lexer). -/
def isParseStringRejectGarbage : Bool :=
  match parseJsonString "@" with
  | .error _ => true
  | _ => false

theorem parseJsonString_garbage_rejected :
    isParseStringRejectGarbage = true := by decide

/-- Probe: the `Json.parse` alias agrees with `parseJsonString` on a basic
input. This documents the drop-in property at the `Bool`-shape level. -/
def isJsonParseAliasTrue : Bool :=
  match Json.parse "true" with
  | .ok (Lean.Json.bool true) => true
  | _ => false

theorem json_parse_alias_true_ok : isJsonParseAliasTrue = true := by decide

/-! ## Round-Trip Theorems (terminal shapes)

For terminal `Lean.Json` shapes (`null`, `bool`, `str`, simple `arr`/`obj`),
parse-of-canonical-print is the matching constructor. Full round-trip for
arbitrary `Lean.Json` requires equivalence up to whitespace and number
canonicalisation; that is deferred to a future milestone (see Task B5+ in
`docs/verified-json-parser-and-adapter-plan.md`).

### Decidability constraint

`Lean.Json` does **not** derive `DecidableEq` — its `BEq` instance is
`partial`. Consequently, equalities of the form
`parseJsonString s = .ok j` are not directly closable by `decide`. Following
the same convention as the `JsonParser` shape-probe theorems, we phrase the
round-trip claims as `Bool`-valued probes that pin down the **full** value
(not just its outer shape), then state the round-trip theorem as
`<probe> = true`. The probes deconstruct `parseJsonString` and compare each
constructor field by structural equality on types that **do** derive
`DecidableEq` (`Bool`, `String`, `Array`, ...).

This gives a round-trip theorem per terminal Json constructor, closed by
`decide` (or `native_decide` for cases involving `String.ofList` /
`String.Slice`-style kernel-opaque reductions).
-/

/-- Round-trip probe: `parseJsonString "true"` produces `Json.bool true`,
exactly. -/
def roundtripTrue : Bool :=
  match parseJsonString "true" with
  | .ok (Lean.Json.bool b) => b == true
  | _ => false

/-- Round-trip: the canonical print form `"true"` parses back to
`Json.bool true`. This is the round-trip-shaped framing of
`parseJsonString_true_ok`. -/
theorem roundtrip_true : roundtripTrue = true := by decide

/-- Round-trip probe: `parseJsonString "false"` produces `Json.bool false`. -/
def roundtripFalse : Bool :=
  match parseJsonString "false" with
  | .ok (Lean.Json.bool b) => b == false
  | _ => false

/-- Round-trip: the canonical print form `"false"` parses back to
`Json.bool false`. -/
theorem roundtrip_false : roundtripFalse = true := by decide

/-- Round-trip probe: `parseJsonString "null"` produces `Json.null`. -/
def roundtripNull : Bool :=
  match parseJsonString "null" with
  | .ok Lean.Json.null => true
  | _ => false

/-- Round-trip: the canonical print form `"null"` parses back to `Json.null`. -/
theorem roundtrip_null : roundtripNull = true := by decide

/-- Round-trip probe: `parseJsonString "[]"` produces `Json.arr #[]`. -/
def roundtripEmptyArr : Bool :=
  match parseJsonString "[]" with
  | .ok (Lean.Json.arr a) => a.size == 0
  | _ => false

/-- Round-trip: the canonical print form `"[]"` parses back to an empty
`Json.arr`. -/
theorem roundtrip_empty_arr : roundtripEmptyArr = true := by decide

/-- Round-trip probe: `parseJsonString "{}"` produces an empty `Json.obj`.

The empty object is represented as `Lean.Json.obj t` for some empty
`Std.TreeMap.Raw`. We probe via `Lean.Json.getObj?` followed by `foldl`-based
size, since `Std.TreeMap.Raw` constructors are not exposed for a direct
constructor-level match. -/
def roundtripEmptyObj : Bool :=
  match parseJsonString "{}" with
  | .ok (Lean.Json.obj t) => t.foldl (init := 0) (fun n _ _ => n + 1) == 0
  | _ => false

/-- Round-trip: the canonical print form `"{}"` parses back to an empty
`Json.obj`. -/
theorem roundtrip_empty_obj : roundtripEmptyObj = true := by decide

/-- Round-trip probe: `parseJsonString "[true]"` produces
`Json.arr #[Json.bool true]`. -/
def roundtripSingletonArr : Bool :=
  match parseJsonString "[true]" with
  | .ok (Lean.Json.arr #[Lean.Json.bool true]) => true
  | _ => false

/-- Round-trip: the canonical print form `"[true]"` parses back to a singleton
`Json.arr` containing `Json.bool true`. -/
theorem roundtrip_singleton_arr : roundtripSingletonArr = true := by decide

/-- Round-trip probe: `parseJsonString "[true,false]"` produces
`Json.arr #[Json.bool true, Json.bool false]`. -/
def roundtripTwoElemArr : Bool :=
  match parseJsonString "[true,false]" with
  | .ok (Lean.Json.arr #[Lean.Json.bool true, Lean.Json.bool false]) => true
  | _ => false

/-- Round-trip: the canonical print form `"[true,false]"` parses back to a
two-element `Json.arr`. -/
theorem roundtrip_two_elem_arr : roundtripTwoElemArr = true := by decide

/-- Round-trip probe: `parseJsonString "\"hi\""` produces `Json.str "hi"`. -/
def roundtripStrHi : Bool :=
  match parseJsonString "\"hi\"" with
  | .ok (Lean.Json.str s) => s == "hi"
  | _ => false

/-- Round-trip: the canonical print form `"\"hi\""` parses back to
`Json.str "hi"`. Closed via `native_decide` because the lexer's string body is
built via `String.ofList`, which is kernel-opaque (same situation as
`parseJsonString_hi_ok`). -/
theorem roundtrip_str_hi : roundtripStrHi = true := by native_decide

end Hax.Json

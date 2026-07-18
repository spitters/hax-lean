# Verified RFC 8259 JSON parser

A self-contained JSON parser for Lean 4 (Lean core + `Std`, **no Mathlib**),
with machine-checked soundness, conformance, and roundtrip theorems. `haxpipeT`
uses it to parse hax's JSON AST dumps; it is also usable standalone.

## Modules

| Module | Contents |
|---|---|
| `Lexer` | Tokeniser + the RFC number/string validators (`validNumberLit`, `validStringContentL`). |
| `Parser` | Fuel-based recursive-descent parser (`parse`), `parse_total`, trailing-content rejection. |
| `ParserSound` | **Soundness**: `parse toks = .ok j → ValueP toks j []` (a fuel-free relational grammar). |
| `ParserComplete` | **Completeness**: a tightened `ValuePStrict` with `parse_complete` and `ValuePStrict → ValueP`, pinning the parser from *both* sides, plus faithful rejection of empty / trailing-comma streams. |
| `Conformance` | RFC 8259 §6/§7 number & string conformance (general accept/reject for the number grammar; escape/surrogate lemmas for strings). |
| `Roundtrip` | `tokenize (serialize j) >>= parse = .ok j` on the `null`/`bool`/`arr` fragment (nested induction). |
| `RoundtripNum` | The `num` leaf on the integer-mantissa fragment (value inversion via `Std`'s `Int.toInt?_repr`). |
| `RoundtripStr` | General tokenise-level string acceptance (`tokenize_string_singleton`, escapes included). |
| `RoundtripObj` | The `obj` leaf, **roundtrip modulo canonicalisation** (structural equality is unattainable — the parser rebuilds objects via `mkObj = Json.obj ∘ TreeMap.Raw.ofList`). |
| `All` | Import manifest forcing the whole suite into the build (CI rot-guard). |
| `Adapter` | hax-JSON → `Lean.Json` glue (trusted at the top level). |

## Documented scope limits

- `num` roundtrip is proved for the integer-mantissa fragment (the serialiser
  drops `JsonNumber.exponent`).
- `obj` roundtrip is *modulo canonicalisation*, since `Json.obj` stores a
  `Std.TreeMap.Raw` and distinct trees with equal contents share a `toList`.
- Full escaped-string roundtrip is open (general string *acceptance* is proved).

See [BUILDING.md](../../BUILDING.md) to build the parser suite (the
`HaxLean.Json.All` target).

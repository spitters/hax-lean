/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Json.Lexer
public import HaxLean.Json.Parser
public import HaxLean.Json.ParserSound
public import HaxLean.Json.Conformance
public import HaxLean.Json.Roundtrip
public import HaxLean.Json.ParserComplete
public import HaxLean.Json.RoundtripNum
public import HaxLean.Json.RoundtripStr
public import HaxLean.Json.RoundtripObj
public import HaxLean.Json.OfficialVectors

/-!
# JSON verified-parser suite — build aggregator

Import manifest forcing the RFC 8259 JSON parser's proof modules into the build.
Every module here is a 0-importer proof orphan relative to the `haxpipeT`
pipeline (the CLI only needs `Lexer`/`Parser`), so without this aggregator a
change to the lexer/parser substrate silently rots the proofs. CI builds
`Hax.Json.All` to keep the whole suite green:

* `Lexer` / `Parser` — the tokeniser + fuel-based recursive-descent parser.
* `ParserSound` — parser soundness (`parse ⟹ ValueP`, relational grammar).
* `ParserComplete` — the converse: a tightened `ValuePStrict` with
  `parse_complete` and `ValuePStrict → ValueP`, pinning the parser from both
  sides, plus faithful-rejection lemmas.
* `Conformance` — RFC 8259 §6/§7 number/string conformance.
* `Roundtrip` — `tokenize (serialize j) >>= parse = .ok j` on the `Simple`
  fragment (null/bool/arr).
* `RoundtripNum` — the `num` leaf on the integer fragment.
* `RoundtripStr` — general tokenize-level string acceptance.
* `RoundtripObj` — the `obj` leaf, roundtrip modulo canonicalisation.
* `OfficialVectors` — JSONTestSuite / RFC 8259 accept/reject vectors run through
  `parseJsonString`, asserting decoded string values and control-char rejection.
-/

@[expose] public section

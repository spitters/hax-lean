# Trusted vs. verified

The pipeline follows CompCert-style TCB minimization: the AST-to-AST
transformations are proved; the I/O ring around them is trusted.

| Component             | Status                                          |
|-----------------------|-------------------------------------------------|
| `TPhase/*`, `Phase/*` | **Verified.** `_erase` / `_ty` / `*_correct`.   |
| `TPipeline`, `Pipeline`, `TPipelineErase` | **Verified.** Composition + full-chain commuting square. |
| `Json/*.lean` (forced into the build by `Json/All.lean`) | **Verified against RFC 8259, with documented scope limits.** The parser is pinned from both sides: soundness (`parse_sound`, a fuel-free relational grammar) and completeness (`parse_complete` over a tightened `ValuePStrict`), plus rejection of the empty and trailing-comma streams. Number conformance §6 is general (`tokenize_accepts_number` / `tokenize_number_reject`, `∀`); string conformance §7/§8.2 has a general tokenize-acceptance capstone (`tokenize_string_singleton`, escaped bodies included) over the escape/surrogate validator lemmas. Roundtrip `tokenize (serialize j) >>= parse = .ok j` holds on the `null`/`bool`/`arr` fragment (nested induction), the integer-mantissa `num` fragment (`Int.toInt?_repr` inversion), and — since `Json.obj` stores a `Std.TreeMap.Raw` the parser rebuilds via `mkObj`, so structural equality is unattainable — the `obj` case modulo canonicalization. Totality (`parse_total`) and trailing-content rejection are proved. Open: `num` beyond integer mantissa (the serializer drops the exponent) and full escaped-string roundtrip. |
| `HaxAdapter.lean`     | Trusted at the top level. Companion `AdapterRefinement.lean` proves per-constructor JSON-to-AST refinement (`JsonRefinesExpr`, ~30 theorems including the `reconstructForLoops` preservation cases); the end-to-end `parseHaxExpr_refines` is open, blocked on `partial def` equational lemmas and a JSON-size termination measure. |
| `PrettyPrint{T}.lean` | Trusted. AST → Lean source; a structural emit, since control-flow encoding is done by the verified `EncodeControlFlow` phase. No preservation proof. |
| `Runtime.lean`        | Trusted. Width-aware builtins; declares two interface axioms (`bridgeCast`, `sha256`) that the CatCrypt-side bridge instantiates. |
| Lean 4 compiler       | Assumed correct.                                |

# Changelog

## 0.1.0-alpha.1 — 2026-07-18 (pre-release)

Pre-release research code (SemVer pre-release; major version 0). Interfaces,
proofs, and the emitted surface may change without notice — do not depend on it
as a stable API. A verified hax/Aeneas Rust-to-functional pipeline in Lean 4,
with the `haxpipeT` CLI.

- Typed, syntax-directed `TExpr → TExpr` pipeline with per-phase feature
  elimination, preservation, and semantics-preservation guarantees.
- End-to-end capstone `pipeline_full_correct`: the pipeline preserves big-step
  denotation (up to control-flow encoding).
- Module root is `HaxLean` (de-conflicted from vendored `Hax` libraries).
- Packaging: MIT `LICENSE`, `CITATION.cff` (ePrint 2026/604), CI, docgen4
  (`env=doc`) + a leanblueprint scaffold.

> Experimental research prototype — interfaces and the emitted surface are still
> evolving.

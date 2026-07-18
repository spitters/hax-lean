# Changelog

## 0.0.1 — 2026-07-18

First tagged release of hax-lean: a verified hax/Aeneas Rust-to-functional
pipeline in Lean 4, with the `haxpipeT` CLI.

- Typed, syntax-directed `TExpr → TExpr` pipeline with per-phase feature
  elimination, preservation, and semantics-preservation guarantees.
- End-to-end capstone `pipeline_full_correct`: the pipeline preserves big-step
  denotation (up to control-flow encoding). Axiom ledger is the three standard
  Lean axioms only (`propext`, `Classical.choice`, `Quot.sound`) — no
  `native_decide`, no custom axiom, no `sorry` (`AxiomAudit.lean`).
- Module root is `HaxLean` (de-conflicted from vendored `Hax` libraries).
- Packaging: MIT `LICENSE`, `CITATION.cff` (ePrint 2026/604), CI, docgen4
  (`env=doc`) + a leanblueprint scaffold.

> Experimental research prototype — interfaces and the emitted surface are still
> evolving.

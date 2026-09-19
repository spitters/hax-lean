# Changelog

## Unreleased

- `haxpipeT` refuses to emit when a call through `&mut` falls outside the
  write-back rewrite (a callee with two `&mut` parameters or a value result,
  or an argument that is not a variable, field place or slice range): the
  emitted function would keep the argument's initial value and ignore the
  callee's effect. Each such call is reported as `ERROR dropped-writeback`,
  with `INFO dropped-writeback-calls=<n>`; `--allow-dropped-writeback` emits
  anyway. (`tDroppedMutCalls` in `ThreadMutations`.)
- The renderer's accumulator extraction reads a statement-`if` branch's
  mutations through nested `if`s, `match`es and loops, and a branch that
  mutates a variable under nested control is joined by a tuple rebinding
  (`let (v₁, …, vₙ) := if c then … else …`). A loop whose body assigned a
  variable only under a nested `if` previously omitted it from the fold state
  (FIPS 205 `base_w`: `total` and `in_idx`).

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

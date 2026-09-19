# Changelog

## Unreleased

- `--emit-certified` emits the typed literal of each function beside its
  `ImpExpr` literal: `def f_texpr : TExpr` carrying the node types of the
  pipelined `TExpr`, and `example : f_texpr.erase = f_impExpr := rfl`. The
  literal's tree is the emitted `ImpExpr` re-typed node by node
  (`retypeWith`), so a node the untyped post-erase passes rewrote is typed
  `.unknown` rather than mistyped. The types a file repeats are shared as
  `abbrev ty_<i> : ImpType` above the definitions. A function whose rebuilt
  term does not erase to its literal — one with an `ImpExpr.typeAscription`
  node, which no `TExpr` constructor erases to — gets neither, and a file
  emitted `partial` gets the literals without the identity.
  (`impTypeToConstructor`, `retypeWith`, `toLeanTExpr`, `mkTyAbbrevs` in
  `PrettyPrintT`.)
- The `&mut` write-back rewrite covers a callee with several `&mut`
  parameters and a callee whose Rust result carries a value. Such a callee
  returns the tuple of its result and its written parameters, and a call to it
  in `let`, assignment or statement position binds that tuple to `_wb` and
  assigns each written variable from a component of that binder. A table entry
  is `(function, positions, parameters, hasResult)`, resolved to a fixpoint,
  and splits into a single-parameter call table and a tuple-parameter one, so
  the call sites and the definition read one table. A callee that carries its
  value out of tail position through a `return` or a `?` keeps its original
  form. The signature of such a callee is annotated with that product
  (`def p (dst : Array (Int)) (pos : Int) : Int × Array (Int) :=`), since its
  Rust result type no longer describes what it returns. (`mutWriteFns`,
  `tTupleBind`, `tReturnMutParams` in `ThreadMutations`, `mutWriteTupleReturns`
  read by `toLeanDefTyped`, with the erasure twins and commuting squares in
  `ThreadMutationsErase`.)
- `haxpipeT` refuses to emit when a call through `&mut` falls outside the
  write-back rewrite (a tuple-form call in an expression position the rewrite
  does not reach, or an argument that is not a variable, field place or slice
  range): the emitted function would keep the argument's initial value and
  ignore the callee's effect. Each such call is reported as
  `ERROR dropped-writeback`,
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

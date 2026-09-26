# Changelog

## Unreleased

- `haxpipeT --hax --emit-certified --emit-classes <trait-export.json>` emits
  Rust traits as Lean classes (`HaxLean/ClassEmit.lean`). The trait export is
  the hax frontend export of the crate that defines the traits; the traits the
  extracted crate defines itself are read from its own export. The mode emits
  one `class` per trait over its `Self` type, with a field per associated type
  (its trait bounds as instance fields), associated constant and method, and
  its supertraits outside `core`/`alloc`/`std` as `extends`; an `export` of
  every trait item the crate reads through a trait bound (`LocalBound`), which
  is then not a `Deps` field; each generic function with binders
  `{F : Type} [Inhabited F] [Trait F]`; each generic struct as a
  type-parametric tuple abbreviation with constructor and projections, so
  `RPoint<F>` prints as `RPoint_T F` and `RPoint<Fe51>` as `RPoint_T Fe51_T`;
  and each trait `impl` of the crate as an `instance` whose fields name the
  emitted method bodies and associated-constant values of the `impl`
  (`buildTraitImplConstMap`, with a `Concrete` constant read resolved to its
  definition). Definitions and instances are emitted in dependency order
  outside `mutual` when the call graph has no cycle beyond self-recursion. A
  type parameter reaches the renderer as `ImpType.typeVar`, which the surface
  stringifier prints by name. The `ImpExpr` and `TExpr` literals are as in the
  default mode. Without the flag the output is byte-identical.
- The emitted file carries a module docstring and sets no heartbeat budget. The
  docstring (`moduleDocstring` in `PrettyPrintT`) sits after the imports in the
  `/-! ... -/` form with a `## Main definitions` section, and is derived from the
  emit: the crate the export came from (the directory holding
  `hax_frontend_export.json`, passed as `crateName`), the `Deps` class and
  whether the definitions stand under its `variable` binder, the number of
  extracted functions, and the types left as `axiom`. The header sets no
  `maxHeartbeats`: thirteen extractions, among them the five largest, elaborate
  inside the 200000 default, and whole-module elaboration of the largest
  measures 16 s. `maxRecDepth 2048` stays, the nested `ImpExpr`/`TExpr` literals
  needing it.
- An export whose trait `impl`s cannot be resolved without giving one `Deps`
  field two types is read with every trait `impl` opaque. Resolving an `impl`
  emits its method bodies at the concrete self type, and those bodies reach the
  self type's components through the trait methods and associated constants of
  a further `impl` — of a dependency crate, or of a type the export does not
  define — which stay opaque; where the crate is also generic over the trait,
  its generic functions use those same names at a type parameter. The `Deps`
  class carries one field, hence one type, per name, so the two readings have
  to print alike. They do when the wrapped type is transparent at the surface
  (a newtype over a limb array prints as `Array (Int)`, as a type parameter
  does) and they do not when it is a type the emitter declares as an axiom.
  `traitImplDepTypeConflicts` (`PrettyPrintT`) names the fields that disagree,
  reading the emitted types through the preamble's struct lookup, and
  `parseHaxFileWithTExpr`'s `resolveTraitImpls := false` (`HaxAdapter`) is the
  uniform reading it selects: every method of every trait `impl` keeps its bare
  name and reaches `Deps`, and the `impl` contributes no definition. Of the 121
  exports available, nine resolve a trait `impl` and one (`hash-to-curve-hax`,
  whose `Fe51H2C` wraps `ristretto255_hax::Fe51` and forwards `Field`,
  `CtField` and `SqrtRatio` to it) disagrees.
- The axiom block declares the opaque wrapped type of every emitted newtype
  alias. `abbrev <Name> := <Inner>` and its two definitional wrappers are
  emitted from the crate's struct declarations, so they name the wrapped type
  whichever definitions survive to the emit, while the axiom set was collected
  from call-site and signature types alone; a wrapped type reached only through
  the alias then had no declaration, and the alias no right-hand side. Of the
  121 exports available, one (`hash-to-curve-hax`, whose `Fe51H2C` wraps
  `ristretto255_hax::Fe51`) has a newtype over an opaque wrapped type.
  (`opaqueFromNewtypes` in `toLeanCertifiedFileTyped`.)
- A trait-method call resolving to a trait `impl` of the crate being extracted
  reaches that method's body instead of the generated `Deps` class. The hax
  `Call` names the trait's associated function and carries its resolution
  beside it, in `fun.contents.GlobalName.item.value.in_trait.impl`; a
  `Concrete` atom there names the `impl` block by its `DefId`. The `impl`
  blocks the crate defines are indexed by that interning id, their methods are
  emitted as top-level definitions named `<Trait>_<method>` (or
  `<Trait>_<SelfTy>_<method>` when the crate has several `impl`s of the trait),
  and the call sites take the same name. A call whose `impl` is outside the
  crate, and a method the `impl` inherits as a trait default, keep the bare
  method name and reach the `Deps` class. (`defIdLeafName`,
  `traitCallImplMethod`, `resolveTraitImplCall`, `collectLocalTraitImplMethods`
  and `buildTraitImplMethodMap` in `HaxAdapter`, read by `parseHaxTExpr`'s
  `Call` arm and by `parseHaxFileWithTExpr`'s item walk.)

  `collectLocalTraitImplMethods` requires the trait's krate not to be in
  `builtinKrates`, so an `impl` of a `core`, `alloc` or `std` trait keeps
  opaque methods even when the `impl` itself is local. That is what
  `#[derive(Debug)]`, `#[derive(Clone)]` and their siblings produce: the body
  is compiler-generated rather than written, it is not part of any
  specification, and for `Debug` it calls the `core::fmt` builder through
  `&mut`, which the write-back gate refuses. Testing `owner_id.is_local` alone
  admitted them. The filter is keyed on the trait rather than on the type, so
  it also covers a hand-written `impl Default`, `impl From` or `impl Iterator`
  on a type carrying no derive.
- The definitional constructor of a newtype tuple struct is emitted as
  `«T.mk»`, matching the `«T.0»` unwrap, and its call sites carry that name
  in the surface rendering and in both literals. The bare name `T` belongs to
  the transparent alias `abbrev T := <Inner>`, so emitting the constructor as
  `def T` declared the same name twice and Lean rejected the file; the
  collision was hidden wherever the alias took the `<T>_T` clash rename.
  (`rewriteNewtypeCtors` and `newtypeBlock` in `PrettyPrintT`.)
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

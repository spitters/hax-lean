# haxpipeT vs lean_refines: Precision Comparison

Both backends are ours. `haxpipeT` (this repo, `Hax/PrettyPrintT.lean` + the
`TPhase` rewriters) is the **verified** typed pipeline. `lean_refines`
(upstream hax, `engine/backends/lean/lean_refines/`) is the **unverified**
OCaml port of the Rocq SSProve backend. This document compares precision of
the Lean output each produces.

## Summary

| Dimension | Winner |
|---|---|
| **Verification** | haxpipeT (machine-checked TPhase rewriters + renderer; lean_refines is unverified OCaml) |
| **Loop handling** | haxpipeT (`fold_range_cf`, `while_loop_cf`; lean_refines emits `Sorry`) |
| **Mutable assignment** | haxpipeT (StateLoop accumulator pattern; lean_refines `Sorry`) |
| **Type-alias emission** | parity as of 2026-05-21 (haxpipeT now emits `abbrev` for `pub type` aliases) |
| **`[u8; N]` rendering** | parity at the alias/deps layer; surface bodies still use `Array Int` to keep `Hax.repeat_` compatibility |
| **Native `structure` for structs** | lean_refines (haxpipeT uses tuple-encoded `abbrev X_T := T1 × T2` + `def «.field»`) |
| **Native `instance` for trait impls** | lean_refines (haxpipeT collapses to flat `<Module>Deps` class) |
| **Borrow / `AddressOf`** | haxpipeT partial; lean_refines `Sorry` |
| **Macros** | haxpipeT partial (panic stripping, assert erasure); lean_refines unimplemented |
| **Opaque ADT preservation** | haxpipeT (lean_refines emits `sorry /- opaque type -/`) |
| **Float types** | both unimplemented |

## Type-level features

| Feature | lean_refines (805 LOC, OCaml) | haxpipeT (5444 LOC, Lean) |
|---|---|---|
| `[T; N]` arrays | `Vector T N` (`lean_ast.ml:204`) | `Vector T N` at typed deps layer, `Array (T)` at surface |
| `&[T]` slices | `Slice T` | `Array (T)` |
| `Vec<T>` | `Vec.t T` | `Array (T)` |
| `Option<T>` / `Result<T,E>` | preserved | preserved |
| `Char` | `Char` | collapses to `Int` |
| Floats | `unimplemented` | `unimplemented` |
| Associated types | `sorry /- ... -/` | preserved as opaque ADT name |
| Opaque types | `sorry /- ... -/` | preserved as opaque ADT name |
| `pub type X = T` aliases | `abbrev X := T` (`lean_refines_backend.ml:663`) | `abbrev X := T` (since 2026-05-21) |
| Generic params on aliases | preserved (binders) | not yet (most crypto aliases are monomorphic) |

## Item-level features

| Feature | lean_refines | haxpipeT |
|---|---|---|
| Rust struct | Native `structure X where field : T` (`lean_refines_backend.ml:673`) | Tuple-encoded `abbrev X_T := T1 × T2` + per-field projection functions |
| Rust enum (unit) | Native `inductive X` | Native `inductive X` |
| Rust enum (payload) | Native `inductive X where \| C : T → X` | Native (added recently) |
| Trait declarations | Native `class Trait` | Implicit via flat `<Module>Deps` typeclass |
| Trait impls | Native `instance` | Bundled in `Deps` consumer |
| Generic functions | preserved | preserved |
| `const` declarations | yes | yes |

## Expression-level features

| Feature | lean_refines | haxpipeT |
|---|---|---|
| `if`/`then`/`else` | yes | yes |
| Pattern matching (constructors, tuples, or-patterns, ascription) | yes | yes |
| `let` bindings (monadic + pure) | yes | yes |
| Closures | yes | yes (recent `UpvarRef` work for captures) |
| **Loops** (`for`, `while`, `loop`) | **`Sorry`** (deferred to upstream phase) | **`fold_range_cf` / `while_loop_cf`** |
| **Mutable assignment** | **`Sorry`** | **StateLoop accumulator pattern** |
| Borrow (`&x`) | `Sorry` | partial |
| AddressOf (`&raw`) | `Sorry` | partial |
| Macros | unimplemented | partial (panic stripped, asserts erased) |
| Trait method calls | dispatcher | Deps class method (single flat dispatcher) |
| Type ascription | yes | yes (recent `typeAscription` AST node) |
| Array literals | yes | yes |

## Meta features

| Aspect | lean_refines | haxpipeT |
|---|---|---|
| Verification | Unverified OCaml | Machine-checked Lean (`TPhase` rewriters + renderer) |
| Type system | Implicit (passes through hax's `ty`) | Explicit `ImpType` Lean-side type system |
| Architecture | Single OCaml pass per expression | Multi-phase: `TPhase` rewriters → `ImpExpr` → render |
| TCB pinning | OCaml whole-engine | `scripts/haxpipe_tcb_baseline.txt` (Lean files) |
| Output size | Compact (one-shot) | Larger (more annotations, mutual blocks) |

## Where haxpipeT can borrow from lean_refines

Concrete improvements, ordered by ease.

### 1. `pub type X = T` → `abbrev X := T` ✅ landed 2026-05-21

`lean_refines` walks the top-level items and emits an `Abbrev` AST node for
`TyAlias` (`lean_refines_backend.ml:663`). haxpipeT previously skipped these
entirely (so the alias name `Scalar` was lost; uses got inlined as `Vector
UInt8 32`).

**Implementation**:
- `Hax/HaxAdapter.lean`: added `TypeAliasInfo`, `parseTypeAliasDefs`,
  `parseTypeAliasDefsFromJson`.
- `Hax/ImpType.lean`: added `toLeanTypeStrPrecise` (preserves `Vector UInt8 N`
  for `[u8; N]`) — used only by item-level emitters that want type-rich
  output (alias bodies, typed deps signatures). Surface rendering retains
  `Array (Int)` for compatibility with `Hax.repeat_` body emission.
- `Hax/PrettyPrintT.lean`: added `aliasMeta` parameter to
  `toLeanCertifiedFileTyped`, emits a `typeAliasBlock`; ADT-bodied aliases
  resolve to the named struct `_T` form so cross-references remain visible.
- `Hax/MainT.lean`: wires `parseTypeAliasDefsFromJson` into the entry point.

**Effect** on zkgroup-hax: previously-missing top-level alias declarations
now appear:

```lean
abbrev MacMucmzAtTag := MacMucmzTag_T
abbrev IssuanceAtUserMsg := IssuanceUserMsg_T
abbrev IssuanceAtSignerMsg := IssuanceSignerMsg_T
abbrev Scalar := Vector UInt8 32
abbrev RistrettoPoint := Vector UInt8 32
```

**Caveat** (shared with lean_refines): hax resolves type aliases at
field-use sites before serialization, so struct fields still render as the
underlying type (`Vector UInt8 32`), not as the alias name (`Scalar`). The
alias emission is therefore documentation + tooling only, not a
type-checker-visible reference at struct fields.

### 2. Native `structure` for Rust structs (deferred)

`lean_refines` emits

```lean
structure MacMucmzKey where
  x0 : Scalar
  x_r : Scalar
  x1 : Scalar
```

haxpipeT instead emits

```lean
abbrev MacMucmzKey_T := Vector UInt8 32 × Vector UInt8 32 × Vector UInt8 32
def MacMucmzKey (x0 ...) (x_r ...) (x1 ...) : MacMucmzKey_T := (x0, x_r, x1)
def «MacMucmzKey.x0» (x : MacMucmzKey_T) := x.1
def «.x_r» (x : MacMucmzKey_T) := x.2.1
def «MacMucmzKey.x1» (x : MacMucmzKey_T) := x.2.2
```

**Downstream impact** (investigated 2026-05-21): **surprisingly low**. Grep
across CatCrypt finds 0 non-extraction references to the `<X>_T` names, the
constructor `def`s, or the `«.field»` projection functions. The tuple
encoding is effectively extraction-file-internal; consumers use the
`<Module>Deps` typeclass API.

**Migration**:
1. Struct emission: `structure FooStruct where ...`.
2. Projection-call sites within bodies: `«FooStruct.field1» x` → `x.field1`.
3. Constructor sites: tuple form → record form.

**Estimate**: ~3-4 days. Right thing to do; not blocking.

### 3. Native `instance` for trait impls (deferred — larger lift)

haxpipeT currently collapses ALL external functions into one flat
`<Module>Deps` typeclass per extraction (e.g., `zkgroupDeps` lumps the
`RistrettoGroup` trait together with anything else the module references).

`lean_refines` preserves trait identity:

```lean
class RistrettoGroup (C : Type) where
  point_mul : Scalar → RistrettoPoint → RistrettoPoint
  basepoint : RistrettoPoint
  ...

instance : RistrettoGroup FooImpl where
  point_mul := ...
```

**Migration impact**: high. Function signatures become parametric over
`{C : Type} [RistrettoGroup C]`; method dispatch in bodies changes; all 89
SurfaceDeps consumers' typeclass-search and method-resolution behavior
shifts. Best done as a coordinated sweep, not piecemeal.

**Estimate**: ~1-2 weeks. Biggest quality improvement; right thing to do
when there's a quiet window for a multi-file pattern change.

## Where lean_refines could borrow from haxpipeT

1. **Loop handling.** `lean_refines` emits `Sorry` for any `for`/`while`/
   `loop`. haxpipeT has the entire `fold_range_cf` / `while_loop_cf`
   machinery in `Hax.Rust_primitives.Folds` and uses it to turn Rust loops
   into total Lean recursions. This is the biggest functional gap.

2. **Mutable variable handling.** Same — `Assign _ → Sorry`. haxpipeT's
   StateLoop accumulator pattern handles this end-to-end.

3. **Verified type-preservation.** The `TPhase` work (94/94 typed
   rewriters) gives type-preservation proofs for each rewriter.
   `lean_refines` has no such guarantees.

4. **Opaque ADT name preservation.** lean_refines emits `sorry /- opaque -/`;
   haxpipeT preserves opaque ADT names and declares them as `axiom <Name> :
   Type`, so downstream consumers can supply concrete instances via the
   bridge adapter.

## References

- `lean_refines` source: `~/tracked/hax/engine/backends/lean/lean_refines/`
  (also available at https://github.com/hacspec/hax under the same path).
- haxpipeT source: this repo (`Hax/PrettyPrintT.lean`, `Hax/ImpType.lean`,
  `Hax/HaxAdapter.lean`, `Hax/MainT.lean`).
- TCB baseline: `~/Claude/SSProve-lean/scripts/haxpipe_tcb_baseline.txt`.

# Verified Hax Compiler Phases in Lean 4

Formal verification of the [hax](https://github.com/hacspec/hax) compiler
phases that lower a Rust subset into a purely functional form. Each phase is
implemented as a syntax-directed transformation on an imperative expression
AST (`ImpExpr`) and equipped with:

1. **Feature elimination** -- the phase removes certain AST constructors
2. **Preservation** -- the phase does not re-introduce constructors removed by earlier phases
3. **Semantics preservation** -- the phase preserves a fuel-bounded big-step denotation

The project also includes a **typed pipeline** (`TExpr`) with commuting
diagrams between the untyped and typed phases, a **width-aware runtime**
for integer/bitwise/array operations, and a **CLI tool** (`haxpipeT`) for
extracting Rust functions from hax JSON into Lean.

## Pipeline

```
ImpExpr
  ──[dropReferences]──────→  ImpExpr  (NoReferences)
  ──[localMutation]───────→  ImpExpr  (NoMutation)
  ──[functionalizeLoops]──→  ImpExpr  (NoLoops)
  ──[cfIntoMonads]────────→  ImpExpr  (NoEarlyExit)
  ──[explicitMonadic]─────→  ImpExpr  (ExplicitMonadic)
  ──[toRawCode]───────────→  RawCode   (free monad)
```

After all five phases the output satisfies `FullyFunctional` (conjunction of
all feature predicates) and can be translated to a free-monad deep
embedding (`RawCode`).

## Verified properties

| Theorem | Statement |
|---------|-----------|
| `pipeline_fullyFunctional` | Output has no references, mutation, loops, or early exits |
| `pipeline_correct` | Pipeline preserves big-step semantics |
| `pipelineToRawCode_noOracleCall` | Translated code contains no oracle calls |

Each individual phase also has its own correctness theorem:
`dropReferences_correct`, `localMutation_correct`,
`functionalizeLoops_correct`, `cfIntoMonads_correct`,
`explicitMonadic_correct`.

## Statistics

- **38 files**, ~22 800 lines of Lean 4
- **0 sorries, 0 axioms** — everything is proved
- **0 Mathlib dependency** — the project is self-contained

## File structure

```
Hax.lean                             # Root import
Hax/
├── AST.lean                         # ImpExpr: imperative expression AST
├── Value.lean                       # Runtime values
├── ImpType.lean                     # Type language for typed AST
├── Features.lean                    # Feature predicates (NoReferences, etc.)
├── TFeatures.lean                   # Typed feature predicates
├── FreeVars.lean                    # Free variable analysis
├── Semantics.lean                   # Fuel-bounded big-step semantics
├── SemanticsCF.lean                 # Semantics with control flow
├── Runtime.lean                     # Runtime builtins (width-aware ops)
├── RuntimeCorrectness.lean          # Runtime correctness proofs
├── TExpr.lean                       # Typed expression AST
├── Json.lean                        # JSON parsing for hax IR
├── HaxAdapter.lean                  # Adapter from hax JSON to ImpExpr
├── PrettyPrint.lean                 # Pretty-printer for ImpExpr
├── PrettyPrintT.lean                # Pretty-printer for TExpr
├── CLI.lean                         # Command-line interface (haxpipe)
├── MainT.lean                       # Main entry point for typed pipeline
├── Phase/
│   ├── DropReferences.lean          # Phase 1: erase borrow/deref
│   ├── LocalMutation.lean           # Phase 2: mutable vars → state passing
│   ├── FunctionalizeLoops.lean      # Phase 3: loops → fold patterns
│   ├── FunctionalizeLoopsCF.lean    # Phase 3 with control flow
│   ├── CfIntoMonads.lean            # Phase 4: early return/? → monadic ops
│   ├── CfIntoMonadsCF.lean          # Phase 4 with control flow
│   ├── ExplicitMonadic.lean         # Phase 5: explicit monadic lowering
│   └── ExplicitMonadicCF.lean       # Phase 5 with control flow
├── TPhase/
│   ├── DropReferences.lean          # Typed phase 1
│   ├── LocalMutation.lean           # Typed phase 2
│   ├── FunctionalizeLoops.lean      # Typed phase 3
│   ├── CfIntoMonads.lean            # Typed phase 4
│   └── ExplicitMonadic.lean         # Typed phase 5
├── Pipeline.lean                    # End-to-end composition + correctness
├── PipelineCF.lean                  # Pipeline with control flow
├── TPipeline.lean                   # Typed pipeline (commuting diagrams)
├── ToRawCode.lean                   # Translation to RawCode free monad
├── TestCompile.lean                 # Compilation tests
├── TestNested.lean                  # Nested expression tests
├── Tests.lean                       # Test suite
└── Deep/
    └── RawCode.lean                 # Minimal RawCode stub (ret/bind/fail)
```

## Building

```bash
lake build              # verify the proofs (0 sorry, 0 axiom)
lake build haxpipeT     # build the CLI: .lake/build/bin/haxpipeT
```

## Running the CLI

`haxpipeT` reads a hax JSON dump and emits one of five output formats,
selected by flag:

| Flag | Output |
|------|--------|
| `--emit-lean` (default) | Lean 4 surface code (purely functional, imports `Hax.Runtime`) |
| `--emit-certified` | Surface code **plus** the post-pipeline `ImpExpr` literal, for agreement proofs |
| `--emit-json` | The transformed `ImpExpr` AST serialized as JSON (the imperative IR) |
| `--emit-bridge` | A CatCrypt `HaxBridge.lean` template wiring extraction into a protocol |
| `--emit-debug-meta` | Debug metadata about hax types and struct layouts |

```bash
# Default: untyped surface code
haxpipeT --hax INPUT.json --emit-lean --name MyModule -o out.lean

# Typed certified output (surface code + ImpExpr literals)
haxpipeT --hax INPUT.json --emit-certified --name MyModule -o out.lean

# Transformed AST as JSON
haxpipeT --hax INPUT.json --emit-json --name MyModule -o out.json
```

To produce the JSON input from a Rust crate, run `cargo hax json` from the
[hax](https://github.com/hacspec/hax) toolchain. Generated Lean files
compile standalone against this repo's `Hax.*` modules — no Mathlib, no
other deps.

## Relationship to hax

The AST constructors in `ImpExpr` mirror the hax intermediate representation
after macro expansion. The five phases correspond to hax's Rust-to-functional
lowering pipeline:

| Phase | hax phase | Consumed constructors |
|-------|-----------|----------------------|
| 1. `dropReferences` | Drop references | `borrow`, `deref` |
| 2. `localMutation` | Local mutation | `assign` |
| 3. `functionalizeLoops` | Functionalize loops | `forLoop`, `whileLoop`, `break_`, `continue_` |
| 4. `cfIntoMonads` | CF into monads | `earlyReturn`, `questionMark` |
| 5. `explicitMonadic` | Explicit monadic | Implicit control flow |

## Relationship to CatCrypt

The `RawCode` stub in `Hax/Deep/RawCode.lean` is a minimal extract of
CatCrypt's free-monad deep embedding (ret/bind/fail only). In the full
CatCrypt project the output of `toRawCode` connects to game-based
cryptographic proofs via the deep embedding.

## License

MIT — see [LICENSE](LICENSE).

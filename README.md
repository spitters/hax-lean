# Verified Hax Compiler Phases in Lean 4

Formal verification of the [hax](https://github.com/hacspec/hax) compiler
phases that lower a Rust subset into a purely functional form. Each phase is
implemented as a syntax-directed transformation on an imperative expression
AST (`ImpExpr`) and equipped with:

1. **Feature elimination** — the phase removes certain AST constructors
2. **Preservation** — the phase does not re-introduce constructors removed by earlier phases
3. **Semantics preservation** — the phase preserves a fuel-bounded big-step denotation

## Pipeline

```
ImpExpr
  ──[dropReferences]──────→  ImpExpr  (NoReferences)
  ──[localMutation]───────→  ImpExpr  (NoMutation)
  ──[functionalizeLoops]──→  ImpExpr  (NoLoops)
  ──[cfIntoMonads]────────→  ImpExpr  (NoEarlyExit)
  ──[toRawCode]───────────→  RawCode   (free monad)
```

After all four phases the output satisfies `FullyFunctional` (conjunction of
all four feature predicates) and can be translated to a free-monad deep
embedding (`RawCode`).

## Verified properties

| Theorem | Statement |
|---------|-----------|
| `pipeline_fullyFunctional` | Output has no references, mutation, loops, or early exits |
| `pipeline_correct` | Pipeline preserves big-step semantics |
| `pipelineToRawCode_noOracleCall` | Translated code contains no oracle calls |

Each individual phase also has its own correctness theorem:
`dropReferences_correct`, `localMutation_correct`,
`functionalizeLoops_correct`, `cfIntoMonads_correct`.

## Statistics

- **16 files**, 4 323 lines of Lean 4
- **0 sorries, 0 axioms** — everything is proved
- **0 Mathlib dependency** — the project is self-contained

## File structure

```
CatCrypt/
├── Hax.lean                         # Root import
├── Hax/
│   ├── AST.lean                     # ImpExpr: imperative expression AST
│   ├── Value.lean                   # Runtime values
│   ├── Features.lean                # Feature predicates (NoReferences, etc.)
│   ├── FreeVars.lean                # Free variable analysis
│   ├── Semantics.lean               # Fuel-bounded big-step semantics
│   ├── SemanticsCF.lean             # Semantics with control flow
│   ├── Phase/
│   │   ├── DropReferences.lean      # Phase 1: erase borrow/deref
│   │   ├── LocalMutation.lean       # Phase 2: mutable vars → state passing
│   │   ├── FunctionalizeLoops.lean  # Phase 3: loops → fold patterns
│   │   ├── FunctionalizeLoopsCF.lean# Phase 3 with control flow
│   │   ├── CfIntoMonads.lean        # Phase 4: early return/? → monadic ops
│   │   └── CfIntoMonadsCF.lean      # Phase 4 with control flow
│   ├── ToRawCode.lean               # Translation to RawCode free monad
│   ├── Pipeline.lean                # End-to-end composition + correctness
│   └── PipelineCF.lean              # Pipeline with control flow
└── Deep/
    └── RawCode.lean                 # Minimal RawCode stub (ret/bind/fail)
```

## Building

```bash
lake build
```

## Relationship to hax

The AST constructors in `ImpExpr` mirror the hax intermediate representation
after macro expansion. The four phases correspond to hax's Rust-to-functional
lowering pipeline:

| Phase | hax phase | Consumed constructors |
|-------|-----------|----------------------|
| 1. `dropReferences` | Drop references | `borrow`, `deref` |
| 2. `localMutation` | Local mutation | `assign` |
| 3. `functionalizeLoops` | Functionalize loops | `forLoop`, `whileLoop`, `break_`, `continue_` |
| 4. `cfIntoMonads` | CF into monads | `earlyReturn`, `questionMark` |

## Relationship to CatCrypt

The `RawCode` stub in `CatCrypt/Deep/RawCode.lean` is a minimal extract of
CatCrypt's free-monad deep embedding (ret/bind/fail only). In the full
CatCrypt project the output of `toRawCode` connects to game-based
cryptographic proofs via the deep embedding.

## License

Apache 2.0

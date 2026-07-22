# Known limitations

The frontend limitations mirror hax's own Rust subset:

- **Expression-level only** — no recursive functions, modules, or item-level
  structure.
- **Closures** — first-class `lam` values; the pre-pass inlines local closure
  calls, and higher-order use is otherwise unresolved.
- **Generics** — complex types fall back to `.unknown`.
- **Traits** — no dispatch; trait methods are unresolved function names.

Two limitations are specific to the Lean modeling:

- **Fuel-bounded semantics** — non-termination is not modeled.
- **Runtime folds** — `Hax.forFold` / `Hax.whileFold` use `partial def`.

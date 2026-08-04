import Lake
open Lake DSL

package «hax-lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]
  -- `-E <kind>` reports Lean messages of that kind as errors. `hasSorry` is the
  -- kind Lean attaches to a declaration whose proof term reaches `sorryAx`, so
  -- building this package refuses such a declaration and no separate step has to
  -- read the build's output. The word in a comment, a docstring or a string
  -- literal carries no such message; a declaration reaching `sorryAx` through a
  -- tactic carries one even though the word appears nowhere in its source.
  moreLeanArgs := #["-E", "hasSorry"]

@[default_target]
lean_lib HaxLean where
  srcDir := "."

lean_exe haxpipeT where
  root := `HaxLean.MainT

-- API documentation (opt-in, dev only). Generate with:
--   lake -R -Kenv=doc update && lake -R -Kenv=doc build HaxLean:docs
-- Output: .lake/build/doc/ (open index.html). Fast — no mathlib dependency.
meta if get_config? env = some "doc" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.30.0"

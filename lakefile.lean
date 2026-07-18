import Lake
open Lake DSL

package «hax-lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

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

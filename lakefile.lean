import Lake
open Lake DSL

package «hax-lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib HaxLean where
  srcDir := "."

lean_exe haxpipeT where
  root := `HaxLean.MainT

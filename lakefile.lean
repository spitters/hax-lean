import Lake
open Lake DSL

package «hax-lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib SSProve where
  srcDir := "."

lean_exe haxpipe where
  root := `SSProve.Hax.Main

lean_exe haxpipeT where
  root := `SSProve.Hax.MainT

import Lake
open Lake DSL

package «rsfFormalProofs» where
  -- nothing custom

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.5.0"

@[default_target]
lean_lib «RSF» where
  srcDir := "formal_proofs"
  globs := #[.submodules `RSF]

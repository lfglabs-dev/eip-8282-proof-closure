import Lake
open Lake DSL

package «eip-8282-proof-closure» where
  version := v!"0.1.0"

@[default_target]
lean_lib «Eip8282» where
  globs := #[.andSubmodules `Eip8282]

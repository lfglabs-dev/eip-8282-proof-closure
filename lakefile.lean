import Lake
open Lake DSL

package «eip-8282-proof-closure» where
  version := v!"0.1.0"

require evmyul from git
  "https://github.com/lfglabs-dev/EVMYulLean.git"@"f7e4ee0dc8f8d5265ce822a937ab5be771f182e9"

@[default_target]
lean_lib «Eip8282» where
  globs := #[.andSubmodules `Eip8282]

import Lake
open Lake DSL

package «eip-8282-proof-closure» where
  version := v!"0.1.0"

require evmyul from git
  "https://github.com/lfglabs-dev/EVMYulLean.git"@"0ff72b2db35302305fccb1d4f42b480434b77bfe"

/-- EVMYulLean's keccak/sha2 FFI, needed by the interpreter `native_decide`
runs. `libleanffi.so` must precede the module dynlib, otherwise `memset_zero`
is unresolved. Run `lake build EvmYul.FFI.ffi:dynlib` before building this lib. -/
def ffiDynlibs : Array String :=
  #[ "--load-dynlib=.lake/packages/evmyul/.lake/build/lib/libleanffi.so"
   , "--load-dynlib=.lake/packages/evmyul/.lake/build/lib/lean/evmyul_EvmYul_FFI_ffi.so" ]

@[default_target]
lean_lib «Eip8282» where
  globs := #[.andSubmodules `Eip8282]
  moreLeanArgs := ffiDynlibs

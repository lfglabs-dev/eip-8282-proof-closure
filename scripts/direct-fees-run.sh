#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
lean_lake=${LEAN_LAKE:-lake}
cd "$repo_dir"
mkdir -p output/direct-fees
python3 scripts/direct-fees-arithmetic.py | tee output/direct-fees/arithmetic.json >/dev/null
"$lean_lake" build EvmYul.FFI.ffi:dynlib Eip8282.Audit.EvmRunner
"$lean_lake" env lean \
  --load-dynlib=.lake/packages/evmyul/.lake/build/lib/libleanffi.so \
  --load-dynlib=.lake/packages/evmyul/.lake/build/lib/lean/evmyul_EvmYul_FFI_ffi.so \
  --run scripts/direct-fees-evm.lean | tee output/direct-fees/evm.txt
python3 scripts/direct-fees-verify.py

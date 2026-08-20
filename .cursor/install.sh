#!/usr/bin/env bash
# Idempotent Cloud Agent install. Runs from the repo root on every Build.
set -euo pipefail

export PATH="${ELAN_HOME:-$HOME/.elan}/bin:/usr/local/elan/bin:$PATH"

if ! command -v elan >/dev/null 2>&1; then
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
    | sh -s -- -y --default-toolchain none
  export PATH="$HOME/.elan/bin:$PATH"
fi

elan toolchain install "$(cat lean-toolchain)"
lake update
# native_decide traces (and later kill-lines) need the keccak/sha2 FFI.
lake build EvmYul.FFI.ffi:dynlib

SHELL := /usr/bin/env bash
.SHELLFLAGS := -euo pipefail -c

.PHONY: bootstrap ffi audit-check prove test check

bootstrap:
	@lake env lean --version
	@lake --version

# native_decide runs the compiled EVMYulLean interpreter, which needs the
# keccak/sha2 FFI as shared objects. lakefile.lean --load-dynlib's them.
ffi:
	@lake build EvmYul.FFI.ffi:dynlib

audit-check:
	@python3 scripts/audit_metadata.py

prove: ffi
	@lake build
	@printf '%s\n' 'prove ok: abstract model, three guarantees, and the P-SUBMIT-1 / P-DRAIN-1 / P-CONTROL-1 bytecode parents built'

test: prove
	@lake build Eip8282.Tests.Mutants Eip8282.Tests.PSubmit1Mutant Eip8282.Tests.PDrain1Mutant Eip8282.Tests.PControl1Mutant
	@printf '%s\n' 'test ok: model mutants and the P-SUBMIT-1 / P-DRAIN-1 / P-CONTROL-1 bytecode kill-lines compiled'

check: audit-check test
	@printf '%s\n' 'check ok'

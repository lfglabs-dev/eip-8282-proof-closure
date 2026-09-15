SHELL := /usr/bin/env bash
.SHELLFLAGS := -euo pipefail -c

.PHONY: bootstrap ffi audit-check prove candidates test check direct-regressions nested-regressions factory-regressions

bootstrap:
	@lake env lean --version
	@lake --version

# native_decide runs the compiled EVMYulLean interpreter, which needs the
# keccak/sha2 FFI as shared objects. lakefile.lean --load-dynlib's them.
ffi:
	@lake build EvmYul.FFI.ffi:dynlib

audit-check:
	@python3 scripts/audit_metadata.py
	@python3 scripts/library_layout.py

# Fast path: only the registered correctness theorem import closure.
prove: ffi
	@lake build Eip8282
	@printf '%s\n' 'prove ok: three registered direct guarantees built'

# Keep historical proofs and conditional protocol/history adapters reproducible.
candidates: ffi
	@lake build Eip8282Candidates
	@printf '%s\n' 'candidates ok: historical and protocol/history support built'

test: prove candidates
	@lake build Eip8282Tests
	@printf '%s\n' 'test ok: registered kill-lines, trust report and all candidate regressions built'

check: audit-check test
	@printf '%s\n' 'check ok'

# Optional corroboration on a local Anvil/revm instance; not a Lean proof.
direct-regressions:
	@python3 scripts/check_direct_semantics.py

# Optional finite nested journal rollback corroboration; injected-state only.
nested-regressions:
	@python3 scripts/check_nested_rollback.py

# Optional actual CREATE2 deployment/rollback corroboration on injected setup.
factory-regressions:
	@python3 scripts/check_factory_deployment.py

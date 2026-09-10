SHELL := /usr/bin/env bash
.SHELLFLAGS := -euo pipefail -c

.PHONY: bootstrap ffi audit-check prove test check direct-regressions nested-regressions factory-regressions

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
	@lake build Eip8282.Tests.Mutants Eip8282.Tests.PSubmit1Mutant Eip8282.Tests.PDrain1Mutant Eip8282.Tests.PControl1Mutant Eip8282.Tests.DirectMutations Eip8282.Tests.DirectThetaMutations Eip8282.Tests.DirectThetaDrainMutations Eip8282.Tests.DirectThetaKills
	@printf '%s\n' 'test ok: model mutants and the P-SUBMIT-1 / P-DRAIN-1 / P-CONTROL-1 bytecode kill-lines compiled'

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

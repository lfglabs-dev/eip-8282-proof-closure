SHELL := /usr/bin/env bash
.SHELLFLAGS := -euo pipefail -c

.PHONY: bootstrap audit-check prove test check

bootstrap:
	@lake env lean --version
	@lake --version

audit-check:
	@python3 scripts/audit_metadata.py

prove:
	@lake build
	@printf '%s\n' 'prove ok: Eip8282 abstract model and three guarantees built'

test: prove
	@lake build Eip8282.Tests.Mutants
	@printf '%s\n' 'test ok: mutants compiled'

check: audit-check test
	@printf '%s\n' 'check ok'

# Agent instructions

This repository contains Lean 4.31 evidence for three EIP-8282 predeploy
guarantees: P-SUBMIT-1, P-DRAIN-1 and P-CONTROL-1. Lean statements are
authoritative; `audit/guarantees.yaml` must describe their actual scope.

## Working in this repository

- Read `audit/DIRECT-CLOSURE.md` for the current clause-level evidence map.
- Use the toolchain in `lean-toolchain` and preserve the normative and interpreter
  pins unless the task explicitly changes them.
- Build `EvmYul.FFI.ffi:dynlib` before compiling project modules. `make prove`
  builds registered correctness; `make check` validates the complete delivery.
- Run metadata and library-partition checks before opening or updating a PR.
- No `sorry` or project `axiom`. Do not add finite `native_decide` traces as a
  replacement for universal proofs. Existing native receipts are confined to
  the disclosed mutation evidence; correctness must use standard Lean axioms.
- Keep the six registered same-predicate mutation refutations load-bearing.
  Preserve the resource-assumption derivation and explicit protocol limits.
- Use an isolated worktree and private mutable build cache for concurrent work.
  Keep one heavy build on this Mac. Do not touch unrelated work or live caches.
- Keep only material needed for current proofs, regressions, source provenance,
  or reproduction. Git preserves superseded campaign history. Document the
  reason for retaining historical material and verify references before deletion.
- Do not merge a PR unless the user authorizes that merge.

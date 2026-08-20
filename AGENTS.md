# Agent instructions

This repository is Lean 4.31 evidence for three EIP-8282 predeploy guarantees
(P-SUBMIT-1, P-DRAIN-1, P-CONTROL-1). Lean theorem statements are authoritative.
`audit/guarantees.yaml` classifies them and must not overclaim.

## Cursor Cloud specific instructions

- Read `audit/CAMPAIGN.md` before writing proofs. That file is the campaign
  source of truth (workers, modules, PR stack, bars).
- If you are the **orchestrator**, follow `audit/CLOUD_ORCHESTRATOR.md`.
- Environment: `elan` + toolchain in `lean-toolchain` (4.31.0). Always
  `lake build EvmYul.FFI.ffi:dynlib` before compiling Eip8282 modules.
- Verify with `make prove` and the relevant kill-line module. Run
  `python3 scripts/audit_metadata.py` before opening a PR.
- Do not add more finite `native_decide` traces as a substitute for `∀`.
  Wave 5 (P-CONTROL-1 nonempty) and Wave 6 (P-SUBMIT-1 underpay + second
  image; P-DRAIN-1 more stale slots) already landed on `main` at `85dab78`.
- Keep existing kill-lines. A new parent that a one-byte mutant cannot
  refute is not load-bearing.
- No `sorry`. No project `axiom`. `native_decide` only for finite jumpdest
  tables in `Eip8282/Audit/Jumpdests.lean` if still forced by `D_J_aux`.
- Do not edit sibling guarantee files from a claim worker. Integrators only
  edit parent theorems, `Eip8282.lean`, `Trust.lean`, YAML, README.
- Do not merge the three campaign PRs to `main`. Humans review them in order
  P-SUBMIT-1 → P-CONTROL-1 → P-DRAIN-1.

## Local prove

```bash
lake build EvmYul.FFI.ffi:dynlib
make prove
```

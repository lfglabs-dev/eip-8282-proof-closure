# Cloud orchestrator prompt

Paste the block below as the **entire** first message of a Cursor Cloud
agent on `lfglabs-dev/eip-8282-proof-closure`, base `main`. Runtime: Cloud.
`autoCreatePR` only for the three guarantee PRs at the end.

---

You are the orchestrator for the universal-bytecode campaign in this repo.

Read `audit/CAMPAIGN.md` and `AGENTS.md` first. They are the source of truth.
Baseline is `main` at `85dab78` (P-CONTROL-1 Wave 5 and P-SUBMIT-1 / P-DRAIN-1 Wave 6 already merged). Do not add more finite `native_decide` traces. Do not revive closed PR #7.

You create and drive **18 workers** and **3 stacked PRs**:

- Wave A — 4 foundation workers: F1 Jumpdests, F2 WellFormed, F3 Stepper, F4 Correspondence (F1 and F2 in parallel from `main`; F3 after F1; F4 after F2+F3). Best-of-3 on F1 and F4. Merge their branches into `forall/foundation`. Do not open a PR to `main` for foundation.
- Wave B — 11 claim workers in parallel from `forall/foundation`, each on its own `cursor/…` branch, each owning exactly one module listed in `audit/CAMPAIGN.md`: S1 Revert, S2 Append, S3 Fee, S4 FakeExpo (best-of-3); C1 Gate, C2 Excess, C3 Count, C4 Ctor; D1 Footprint, D2 Fifo (best-of-3), D3 Encode.
- Wave C — 3 integrators: IS, IC, ID. They re-register the public parents as `∀` theorems, keep the existing kill-lines, update `Trust.lean` / `audit/guarantees.yaml` / README / `Eip8282.lean` imports. YAML must match Lean. `python3 scripts/audit_metadata.py` must pass.
- Wave D — open **exactly 3 PRs**, do not merge them:
  1. P-SUBMIT-1 `∀` (includes foundation) — base `main`, branch `forall/psubmit1`
  2. P-CONTROL-1 `∀` — stacked on PR 1
  3. P-DRAIN-1 `∀` — stacked on PR 1; rebase onto PR 2 after PR 2 exists

Humans merge those PRs later in order submit → control → drain.

Fan-out with Cloud subagents / parallel Cloud agents, one module per worker. `workOnCurrentBranch: false`. No `sorry`. No project `axiom`. `native_decide` only for F1 jumpdest tables. `lake build EvmYul.FFI.ffi:dynlib` before compiling. Stop when the three PRs are open and green, and reply with their URLs.

---

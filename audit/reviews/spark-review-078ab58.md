# Independent review — grok slot/withdrawal extraction lot-44 (078ab58)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commits: 7d8fc7b (proof), 078ab58 (receipt)
Delta base: ccb8f2f (prior CLEAN, already merged via PR #36)
Head: 078ab58 on branch `grok/eip-slot-withdrawal-extraction-20260911`
Started at: 2026-09-11

## Scope observed

Two commits, three files, +316 / -6 lines.

- `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean` (+166/-6): adds `CREDENTIAL_BYTES`, `CREDENTIAL_ADDRESS_OFFSET`, `EXECUTION_ADDRESS_BYTES` constants; `credAddressBytes`, `eth1Credential`, `sampleExecutionAddr` definitions; layout/width theorems (`credential_layout`, `address_slice_width`, `credAddressBytes_length`); `eth1Credential_{length,hasEth1,hasExecution,pad}`; `credAddress_of_eth1`; sample kill-line `cred_address_is_not_take20`; SSZ container `SszWithdrawal` with `sszElFields` / `sszClFields` projections; four field-projection ignore lemmas; adapter `sszAsArchived`; three archived-composition lemmas.
- `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean` (+28/-0): re-exports four kill-lines (`cred_address_is_not_first_twenty`, `eth1_layout_keeps_prefix`, `el_fields_ignore_validator_index`, `el_address_is_not_validator_index`).
- `audit/receipts/grok-slot-withdrawal-extraction-7d8fc7b1bf4353be85fb27a5cde72f87bee273fd.json` (+128): the receipt itself.

No parallel framework directory added. No changes outside these three paths.

## Checks

1. `sorry` / `admit` — none. Grep on the delta diff (`^\+` additions filtered for `sorry|admit\b`) returns nothing. Surrounding-file `admit`/`admits` occurrences are pre-existing field-name identifiers (`engineAdmits`, `validate_header_admits_duplicate_slots`), not tactic uses.
2. Axiom drift — no `axiom` keyword introduced. All 16 new declarations listed in the receipt as axioms depend only on subsets of `{propext, Classical.choice, Quot.sound}`. Receipt shows `credAddress_of_eth1` and `cred_address_is_not_take20` use `{propext, Quot.sound}`; several lemmas (`credential_layout`, `address_slice_width`, `eth1Credential_hasEth1`, `eth1Credential_hasExecution`, `sszEl_ignores_*`, `sszCl_ignores_address`, `sszEl_ne_validator_as_address`) list `[]` (pure `rfl`/`decide`). No project axiom. No `native_decide`.
3. Scope — exactly the three files above.
4. Pinned reference — receipt records `previous_lot.receipt = ccb8f2f…8752`, base `681d186…`, and the current commit is `7d8fc7b…`. `next_obligation` and `wiring_not_applied` explicitly keep this lane off SYSTEM/block/gas modules.
5. Mutants — non-trivial: `cred_address_is_not_take20` (byte-slice `drop 12 ≠ take 20` on a concrete 32-byte layout with `EXECUTION_ADDRESS_BYTES = 20`); `sszEl_ne_validator_as_address` (a specific `{addressBytes := [9], validatorIndex := 7}` witness); `el_fields_ignore_validator_index` (functional-extensional projection); `eth1_layout_keeps_prefix` (first-byte-tag persistence). None are `True` or self-implying; the `≠` kill-lines both discharge by concrete computation (`decide`) against a spec-cited alternative implementation (Capella:454 vs `[:20]`; fork.py:1118 EL fields).
6. Commit 7d8fc7b accuracy — subject "bind Withdrawal field order and credentials[12:]". The diff introduces a `SszWithdrawal` record whose field order (`index`, `validatorIndex`, `addressBytes`, `amount`) matches Capella:153-157 and cites it; `sszAsArchived` binds those fields to `ArchivedWithdrawal` under `w.amount = item.gwei.val`; `credAddressBytes = List.drop 12` (`CREDENTIAL_ADDRESS_OFFSET`) with `credAddress_of_eth1` demonstrating the recovery on the Capella:639 layout. The extraction module's OPEN paragraph and mutants ledger are updated to say "field order and `credentials[12:]` are extracted" — the byte-string SSZ decode and `ExecutionAddress → AccountAddress` mapping remain explicitly OPEN in the same paragraph and in `named_hypotheses_still_open` in the receipt. Nothing is adopted as policy; the receipt's `not_claimed` lists SSZ injectivity and AccountAddress-decode.
7. No parallel framework — no new directory or module tree; changes are in-place extensions of existing extraction/mutants files.

## Findings

None (no BLOCKING or ADVISORY findings).

Notes:
- Receipt `classification` is `compiled_additive_extraction_not_adoption_not_guarantee_closure`, consistent with the delta being additive-only lemmas + kill-lines + doc-string tightening (the two edited comment blocks explicitly move items from OPEN to "extracted (field order and credentials[12:])" while preserving the named byte-string decode as OPEN).
- Receipt records `make check` exit 0 with tail "check ok" and `lake build` exit 0 for both integrator modules and the mutants module; this reviewer did not rerun the build per instructions.
- Receipt's `files_sha256` lists a hash for `ProtocolSlotExtraction.lean` even though the delta does not touch that file — this is the pinned neighbour file that also compiled clean in this lot and is not a mismatch. `ProtocolWithdrawalExtraction.lean` and `ProtocolSlotWithdrawalMutants.lean` are the two edited-in-this-lot files.

VERDICT: CLEAN

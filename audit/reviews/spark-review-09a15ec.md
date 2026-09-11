# Independent review — grok slot/withdrawal extraction delta (c39bd18..09a15ec, lots 21-26)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Delta base: c39bd1843e25ef9ac0bbaf5214e8d5294cfdb1b0
Delta head: 09a15ec6c10175f1599d79f8b41f35706cdb0403
Branch: origin/grok/eip-slot-withdrawal-extraction-20260911
Started at: 2026-09-11T12:09:58Z

## Scope items reviewed

- 12-commit delta (6 alternating proof / audit-receipt pairs) enumerated
  via `git log c39bd18..09a15ec --oneline`.
- `git diff c39bd18..09a15ec --name-only`: only 8 paths — the two Lean
  files under review plus 6 new JSON receipts under
  `audit/receipts/grok-slot-withdrawal-extraction-*.json`. No touch to
  `Trust.lean`, `Integrator.lean`, `Makefile`, `ProtocolSlotExtraction`,
  `ProtocolWithdrawalCount`, `ProtocolCreditEnvelope`, `ResourceBounds`,
  or any SYSTEM/block/gas/history module.
- Read the full added region of
  `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean` (~1224
  insertions) and the full mutants delta in
  `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean` (+212).
- Read receipts for lot-21 (proof `c0e8058`) and lot-26 (proof
  `286716e`) end-to-end, plus spot-checks of lot-22 (`c51ce31`) and
  lot-23 (`9dd2597`).
- Verified the two blob SHA-256 values recorded in the lot-26 receipt
  match `git cat-file blob | sha256sum` for the file blobs at HEAD.
- Confirmed the file grep for `sorry|admit|sorryAx|axiom ` in the two
  Lean files at HEAD (2 hits, both inside docstrings describing engine
  admission semantics — not proof terms).

## Findings

None BLOCKING. None ADVISORY worth escalating.

1. Zero `sorry` / `admit` / `sorryAx` / `axiom ` declarations in either
   modified Lean file. The two `admit` grep hits at lines 3234 and
   3454 are inside docstrings (`"Electra:1318-1336: admit only when
   every conjunct holds."` and `"engine admit"`).
2. Scope respected — 8 files total, exactly the announced set.
3. New code is additive and consumes the existing framework: `open
   ProtocolCreditEnvelope ProtocolWithdrawalCount ProtocolSlotExtraction`
   at the top of the extraction file, and every new theorem re-uses
   `Ledger`, `Dispatch`, `Counts`, `applyTagged`, `ElCredit`,
   `AcceptedBlocks`, `Block`, `Item`, `DualBalances`, `AccountMap`, and
   `ApplyBodyWithdrawals`. No parallel framework, no adoption, no
   public `Block` field change.
4. Commit messages ("bind apply_withdrawals and create_ether to one
   list", "join Withdrawal.index with validator_index on one record",
   "bind visitRing keys to credited validator_index", "derive Electra
   block items from creditEligible", "derive Gloas four-stage items
   from gloasCredited", "stamp Capella indices across gloasCredited
   chains") accurately describe the added definitions
   (`CreditedWithdrawal`, `CreditedRun`, `ArchivedWithdrawal`,
   `stampIndex`, `stampedChain`, `creditEligible`,
   `electraCreditEligible`, `creditQueueStage`, `creditPartials`,
   `creditSweepStage`, `gloasCredited`, `gloasBlock`). No
   overclaiming; each receipt lists `not_claimed` including
   "P-SUBMIT-1 / P-DRAIN-1 / P-CONTROL-1 closure" and "protocol
   adoption or canonical history".
5. `#print axioms` is emitted for 73 of the 78 new theorems in the
   extraction file (the un-printed handful are trivial cons/nil
   `rfl`-only lemmas that share axiom footprints with printed peers).
6. New mutants are substantive kill lines, not tautologies. Samples:
   `credited_el_scale_is_gwei_times_1e9` (Gwei * 1e9, refutes a
   1e18 mutant), `stamp_repeats_still_unique` (Capella:458 successor
   uniqueness on duplicated credited entries), `eligible_visit_keeps_ring_index`
   (`[1]` not `[0]` on a start-1 4-validator sweep),
   `gloas_four_stage_order` (concrete `[oneGwei, unit, twoGwei,
   threeGwei]` value refuting any permutation),
   `gloas_stamp_indices_are_successors` (`[0,1,2,3]` by `decide`),
   `gloas_second_payload_continues_index` (`[0,1]` cross-payload,
   refutes a restart-at-zero mutant of Capella:510).

## Axiom audit (sample)

Receipts declare the following whitelist for every new declaration
(`propext`, `Classical.choice`, `Quot.sound`, or a subset). Spot check
of declarations from three different lots:

- `creditedItems_length` (lot-21): `[propext]`
- `credited_cl_amount_is_gwei` (lot-21): `[propext]`
- `creditedRun_cl` (lot-21): `[propext, Classical.choice, Quot.sound]`
- `applyBody_of_credited` (lot-21): `[propext, Classical.choice, Quot.sound]`
- `dispatched_counts_from_credited_envelopes` (lot-21): `[propext, Classical.choice, Quot.sound]`
- `stampIndex_append` (lot-26): `[propext, Quot.sound]`
- `stampedChain_items` (lot-26): `[propext]`
- `indexedChain_of_gloas_block` (lot-26): `[propext, Classical.choice, Quot.sound]`
- `indexedChain_of_two_gloas` (lot-26): `[propext, Classical.choice, Quot.sound]`
- `dispatched_counts_from_stamped_gloas` (lot-26): `[propext, Classical.choice, Quot.sound]`

All entries stay inside the pre-agreed
`{propext, Classical.choice, Quot.sound}` set. No project axiom, no
`sorryAx`.

## Bundle/receipt provenance sample

Lot-21 (`grok-slot-withdrawal-extraction-c0e8058c7fee9b2127efe056db2d90327eee56ef.json`):
- `base.sha = 681d1866a7db0de0990af4b730ce5846896714f0` — verified as an
  existing commit ("audit: record verified ordinary block incorporation
  and remaining scope").
- `previous_lot.receipt = c39bd1843e25ef9ac0bbaf5214e8d5294cfdb1b0`
  (matches the delta base under review).
- `toolchain.lean = leanprover/lean4:v4.31.0`,
  `lean_commit = 68218e876d2a38b1985b8590fff244a83c321783`,
  `lake = 5.0.0-src+68218e8` (consistent with the earlier CLEAN lots).
- `archived_bodies_rehashed` pins `gloas/beacon-chain.md`, `amsterdam/fork.py`,
  `amsterdam/state_tracker.py`, and `direct-cl-inheritance-sources-20260910.json`
  with SHA-256 values.
- `commands` records `lake build ... ProtocolWithdrawalExtraction
  ProtocolSlotWithdrawalMutants` exit 0, plus `make check` exit 0
  (per requester's pre-check; I did not re-run).

Lot-26 (`grok-slot-withdrawal-extraction-286716e9eec55beddcb2066b73fd2d91d50342b5.json`):
- `previous_lot.proof = bc5e9a4b5c86e7b1f7a7e4049738e087b2c57e77`
  (matches lot-24 proof commit in the log).
- Toolchain values match lot-21 exactly.
- `files_sha256["Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean"]
  = 461094a0b8c6116d6d3b99475187371673c6c7ef47543117130a435ce40915d4`
  — I independently ran
  `git cat-file blob 4f446b56...ffe6 | sha256sum` and got the same
  digest.
- `files_sha256["Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean"]
  = 15d23ad4fabae4c0b2cdedc1966be7141c26ff43973d3d1532516f6547a12a38`
  — verified against `git cat-file blob 8ac5c1d8...2648 | sha256sum`.
- `cited_functions` names Capella:196-204 / 452 / 458 / 506-510 and
  Gloas:1879-1916 / 1999, all of which appear in the added theorem
  docstrings.

## Conclusion

The delta is a purely additive extraction lane: six lots build up the
joint CL/EL `CreditedRun`, the `ArchivedWithdrawal` join carrying
Capella `Withdrawal.index` and Gloas `validator_index`, the
`creditEligible`/`electraCreditEligible` binding of visit-ring keys, and
the four-stage `gloasCredited` / `stampedChain` composition. Every new
theorem is discharged into the existing `Ledger` / `Dispatch` / `Counts`
framework via new `dispatched_counts_from_*` variants that only rewrite
the flat-list equality using `items_of_gloasBlock` / `stampIndex_items`;
no framework definition or public `Block` field is changed. The scope is
respected, no `sorry` / `admit` / project axioms appear, the axiom
sample stays in the pre-approved kernel set, both spot-checked receipts
pin the correct toolchain and file hashes (independently verified for
lot-26), the six commit messages do not overclaim, and the new mutant
lemmas are concrete kill lines with numeric outputs decided by
`decide`. The delta stays off gas, nested calls, canonical history, and
the SYSTEM/block/history modules, and each receipt explicitly disclaims
P-SUBMIT-1 / P-DRAIN-1 / P-CONTROL-1 closure and canonical adoption.

VERDICT: CLEAN

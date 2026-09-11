# Independent review — grok delta lots 33-34 (15d04df..ee5cdc4)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Delta base: 15d04df
Delta head: ee5cdc4
Branch: origin/grok/eip-slot-withdrawal-extraction-20260911
Started at: 2026-09-11T12:44:54Z

## Scope items reviewed
- Sorry/admit grep on the modified regions (`ProtocolWithdrawalExtraction.lean`, `ProtocolSlotWithdrawalMutants.lean`).
- Axiom drift on the 24 new declarations advertised in the two receipts.
- Scope respected: only 4 files touched (`git diff 15d04df..ee5cdc4 --name-only`).
- Pinned reference correctness for the two receipts (`grok-slot-withdrawal-extraction-499c079…` and `…-971dad9…`).
- New mutants in `ProtocolSlotWithdrawalMutants.lean` (8 new theorems) — non-trivial kill lines and fixture reuse.
- Commit message accuracy for `499c079` (applyTagged index bounds) and `971dad9` (n>2^40 visit keys builder-tagged).
- No parallel framework introduced (grepped `axiom` in the +hunks).

## Findings
1. Zero `sorry` / `admit` in the diff of both modified `.lean` files. The only match `grep -E 'sorry|admit'` returned is a pre-existing `#print axioms empty_tx_not_admitted` line context — no new tokens introduced.
2. Zero new `axiom` declarations in the diff (grep `^\+axiom|^\+.*axiom `). New theorems in receipts advertise only `propext`, `Quot.sound`, and (for two) `Classical.choice` — all standard Lean core, consistent with pre-existing whitelist. `visitRing_pos` is even axiom-free.
3. Scope is exactly 4 files: the extraction module (+398), the mutants module (+95), and two new JSON receipts. No touches to `Makefile`, `Trust`, DIRECT-CLOSURE, SYSTEM/block/gas/history/canonical lanes, StageExtraction, Integrator dispatch, or the parallel `ProtocolSlotExtraction.lean` (the receipts even hash the latter unchanged at `e4098a…`).
4. Receipt for `499c079`: `previous_lot.receipt = 15d04df…` matches the delta base; `commit = 499c079…`; `files_sha256` includes both edited modules; recorded_at 2026-09-11T12:38:31Z sits before the commit timestamp shown by `git show 499c079` (12:38:21Z + subsequent hashing). Coherent chain.
5. Receipt for `971dad9`: `previous_lot.proof = 499c079…`, `previous_lot.receipt = c9b99d3…`, `commit = 971dad9…`. Extraction file hash progressed from `4798c0…` to `6aefa6…`, mutants from `5b8fc4…` to `567d29f…`. Chain is monotone.
6. New mutant `mixed_gloas_keeps_builder_past_len` reuses pre-existing fixtures `mixedQueue/mixedPartials/mixedSweeps/mixed_sweep_start` (defined in mutants file at lines 874-891 pre-delta — verified via `git show 15d04df:`). Not fabricated.
7. New mutant `large_registry_electra_writes_builder_zero` arithmetic: `sampleBalances.builders _ = 100` (pre-existing at line 314), `oneGwei.gwei.val = 1`, so the claim `builders 0 = 99` matches `applyTagged_electra_gt_flag_writes_builder_zero`. Non-trivial: it exhibits the OOB write on the flag.
8. `hnflag_drop_refuted` is a genuine refutation mutant (`¬ ∀ …`), showing the `n ≤ 2^40` hypothesis in `electraCreditEligible_pairs_not_builder` is load-bearing — matches the 971dad9 commit message and receipt's `hnflag_load_bearing` claim.
9. `IndexInRange` is a definitional predicate (not an axiom), branching on `isBuilderIndex`. Its accompanying `_builder` / `_validator` / `_toValidatorIndex` characterizations are proved by `simp`+rw, not by fiat.
10. `applyTagged_keeps_validator_oob` / `_builder_oob` proceed by structural induction on the ws list, discharging both branches via existing `applyOneWithdrawal_*_other` and `_keeps_*` lemmas — no gadgetry.
11. Commit message `499c079` ("bind applyTagged index bounds from archived guards") accurately captures the payload: `IndexInRange`, `applyTagged_keeps_*_oob`, per-stage `_inRange` lemmas, and `gloasFromBuilders_pairs_inRange`.
12. Commit message `971dad9` ("show n>2^40 visit keys are builder-tagged") accurately captures: `visitRing_pos/_start_mem/_mem_offset/_flag_mem/_mem_flag`, `visitRing_exists_builder`, and the `electraCreditEligible_gt_flag_*` witness family.
13. Module header block-comment update (lines 106-116) correctly folds the new IndexInRange guard and the n>2^40 clause into the OPEN list, consistent with `named_hypotheses_still_open` in both receipts.
14. `wiring_not_applied` in both receipts explicitly notes Makefile still omits `ProtocolSlotWithdrawalMutants` from `make check` — no adoption drift claimed.
15. Local pre-check (`lake build ProtocolWithdrawalExtraction ProtocolSlotWithdrawalMutants` = 1221 jobs OK) confirmed by caller; I did not rerun.

## Axiom audit (sample)
- `indexInRange_toValidatorIndex` — receipt lists `[propext, Quot.sound]`; declared as pure `simp`+rw proof over a definitional predicate. Consistent.
- `applyTagged_keeps_validator_oob` — receipt lists `[propext]`; structural induction over list with case analysis on `isBuilderIndex v`, discharged by existing `applyOneWithdrawal_*` lemmas. Consistent.
- `electraCreditEligible_inRange` — receipt lists `[propext, Quot.sound]`; combines `electraCreditEligible_pairs_not_builder` (existing) with `visitRing_lt`+`creditEligible_indices_sublist` (existing). Consistent.
- `visitRing_pos` — receipt lists `[]` (axiom-free); trivial `cases fuel` proof. Consistent.
- `visitRing_mem_offset` — receipt lists `[propext, Classical.choice, Quot.sound]`; uses `List.getElem_mem` and `Option.some.inj`. `Classical.choice` plausibly enters via `List.getElem_mem`/`Sublist.mem` machinery. Consistent with standard mathlib/core.
- `applyTagged_electra_gt_flag_writes_builder_zero` — receipt lists `[propext, Quot.sound]`; explicit witness computation via `applyTagged_singleton` + `applyOneWithdrawal_builder_written` + `toBuilderIndex_flag`. Consistent.

## Bundle/receipt provenance sample
- `audit/receipts/grok-slot-withdrawal-extraction-499c079e82be4b1a62ca09fa50468a63ce99d3b6.json`: base sha `681d186…` matches local `main`-lane HEAD (`git log`); previous_lot chains to `15d04df…` (delta base); scope enumerates exactly the two edited `.lean` modules plus the receipt itself. `commands` include `make check` exit 0 with 3608 jobs. `not_claimed` correctly disclaims P-SUBMIT-1/DRAIN-1/CONTROL-1 closure and adoption.
- `audit/receipts/grok-slot-withdrawal-extraction-971dad91cf2c7e427d50d2b011ac2244db9fde53.json`: previous_lot chains to `499c079…` (lot-33 proof) and `c9b99d3…` (lot-33 receipt). `proved_under_hypotheses.hnflag_load_bearing` accurately describes the eight-lemma witness chain. `not_claimed` correctly disclaims that `n ≤ 2^40` has been discharged for arbitrary registries — only shown load-bearing.

## Conclusion
The delta is a tight, additive proof extension. Two new definition-level guards (`IndexInRange`, `visitRing_mem_offset` and friends) are introduced with faithful characterization lemmas, plus stage-wise `_inRange` inheritance that composes into `gloasFromBuilders_pairs_inRange` and the OOB-preservation corollaries. Lot-34 exhibits the concrete counter-witness that the `n ≤ 2^40` hypothesis of `electraCreditEligible_pairs_not_builder` cannot be dropped, and the receipts correctly disclaim that this only shows load-bearing rather than discharge. No sorries, no new axioms, no scope creep into SYSTEM/block/history/gas lanes, no adoption claims, no Makefile changes. Both receipts chain correctly to prior lots and to the pre-delta base. New mutants reuse pre-existing fixtures and prove non-trivial kill lines (an OOB write on the flag; a genuine `¬∀` refutation of the dropped hypothesis).

VERDICT: CLEAN

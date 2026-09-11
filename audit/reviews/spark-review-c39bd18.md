# Independent review — grok slot/withdrawal extraction (c39bd18)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commit: c39bd1843e25ef9ac0bbaf5214e8d5294cfdb1b0
Branch: origin/grok/eip-slot-withdrawal-extraction-20260911
Base: 681d1866a7db0de0990af4b730ce5846896714f0
Started at: 2026-09-11T11:41:23Z

## Scope items reviewed
- Sorry/admit/axiom grep across the three added Lean files: OK — zero occurrences of `sorry`, `admit`, `sorryAx`, or `axiom ` in code. Two `admit` occurrences in `ProtocolWithdrawalExtraction.lean` (lines 2089 and 2309) are inside docstring comments ("admit only when every conjunct holds", "engine admit") and refer to the semantic notion of engine "admitting" a block, not to the Lean tactic.
- Axiom drift (spot-check ~20 declarations): OK — every sampled declaration depends only on a subset of `{propext, Classical.choice, Quot.sound}`. See axiom sample below. The receipts corroborate: every `axioms` block in the 20 receipts opens with the note "No sorryAx. No project axiom. Only propext / Classical.choice / Quot.sound."
- Scope drift: OK — the file docstrings and the receipt `not_claimed` fields consistently disclaim adoption of a specific normative fork ("Python executable correspondence", "protocol adoption or canonical history", "P-SUBMIT-1 / P-DRAIN-1 / P-CONTROL-1 closure"). Extractions are guarded by explicit domain hypotheses (e.g., `TimeFitsU64`, `BalanceFits`, `WithdrawalIndexFits`, `AcceptedBlocks`) — no unconditional postcondition is asserted on arbitrary blocks. The Amsterdam evaluator is treated as arithmetic transcription of archived Python; `create_ether` is a named `CreateEther` relation, and `notify_new_payload` is explicitly named as ≠ `create_ether`.
- Pinned reference correctness (sampled 3 receipts: 046807d, ca229a7, f7db7f5): OK — receipts carry (a) `files_sha256` for each of the three touched Lean files, (b) `archived_bodies_rehashed` for each spec file and referenced Python source (e.g., `specs/gloas/beacon-chain.md` 10b7decc..., `src/ethereum/forks/amsterdam/fork.py` dd0d069c..., `specs/electra/beacon-chain.md` c722ff14...), and (c) the base commit SHA `681d1866...` in a `base` block. The bundle SHA of the two Lean files at HEAD matches the SHAs in the final receipt (ca229a77).
- Consistency with the existing framework: OK — `ProtocolWithdrawalExtraction.total_count`, `dispatched_counts`, `blockOfElectra`, and `items` are already consumed by `Eip8282/Audit/Integrator/ProtocolWithdrawalStageExtraction.lean` at 681d186 (grep confirms lines 1/21/110/119). Types line up: `blockOfElectra` produces `Block` with the `partialBound`/`validatorsGuard` fields, and slot facts (`AcceptedBlocks`, `Accepted.pairwise`, `Accepted.nodup`) discharge the consumer's Nodup premise. No parallel framework was introduced; the new material extends existing modules.
- Test/mutant quality: OK — the mutant file contains ~70 non-trivial kill lines. Sample: `duplicate_slots_rejected` (refutes duplicate accepted slots), `queueStage_caps` (asserts 15 not 20), `timeFits_rejects_overflow` (refutes wrap-free `compute_time_at_slot`), `next_validator_wraps` (0 not 3), `sweep_limit_caps_large_registry` (16384 cap), `compounding_max_is_2048e9` (2048e9 ≠ 32e9), `epoch_boundary_is_32`, `builder_flag_writes_index_zero`. None are `x = x` or `True` shims.
- Files outside stated scope: OK — `git diff 681d1866..c39bd18 --name-only` filtered by `-vE "…extraction files or receipts"` returns empty. Only the three named Lean files and 20 receipt JSONs under `audit/receipts/grok-slot-withdrawal-extraction-*.json` were touched.
- Commit message hygiene: OK — sampled commits (c39bd18, ca229a7, 44f7f6f, 71450c6, 33ae71c, 6c59ffa) describe additive extractions with disclaimers of what remains named ("Line 384 EMPTY_CODE_HASH and Python modify_state destroy remain named", "Array bounds remain named"). No commit overclaims closure or normative adoption.

## Findings
None. No BLOCKING or ADVISORY findings.

## Axiom audit (sample)
From `ProtocolSlotExtraction`:
- `accepted_pairwise` → propext
- `accepted_nodup` → propext
- `accepted_count` → propext, Classical.choice, Quot.sound
- `projected_nodup` → propext
- `el_nodup` → propext
- `processSlots_of_loop` → propext
- `loop_of_processSlots` → propext
- `slotsWhile_fill` → propext
- `envelope_slot` → propext
- `timeFits_rejects_max_slot` → propext (via receipt-listed `#print axioms`)

From `ProtocolWithdrawalExtraction`:
- `queueStage_guarded` → propext, Quot.sound
- `queueStage_length` → propext, Quot.sound
- `sweepStage_guarded` → propext, Quot.sound
- `items_bounded` → propext, Quot.sound
- `total_count` → propext, Classical.choice, Quot.sound
- `dispatched_counts` → propext, Classical.choice, Quot.sound
- `dispatched_counts_from_envelopes` → propext, Classical.choice, Quot.sound
- `verify_requires_engine` → propext
- `envelopeCredits_cons_implies_apply` → propext, Classical.choice, Quot.sound
- `createEther_missing_zero_nonce_balance_empty` → propext, Classical.choice, Quot.sound

From `ProtocolSlotWithdrawalMutants`:
- `duplicate_slots_rejected` → propext
- `tick_must_increment` → propext
- `epoch_boundary_is_32` → propext
- `notify_false_not_admitted` → propext
- `empty_parent_witness` → propext

All 197 `#print axioms` lines in `ProtocolWithdrawalExtraction.lean`, all 38 in `ProtocolSlotExtraction.lean`, and every kill-line in the mutants file are inside the source; they are compiled at build time and their axiom bases are recorded in the receipts.

## Bundle/receipt provenance sample
- `audit/receipts/grok-slot-withdrawal-extraction-046807d…json` (lot 1): pins `specs/phase0/beacon-chain.md` 95bbeca1…, `specs/gloas/beacon-chain.md` 10b7decc…, `src/ethereum/forks/amsterdam/fork.py` dd0d069c…, `direct-cl-inheritance-sources-20260910.json` 8780adb6…, and file SHAs 9d2414d2…/cf384532…/297a9cec…. `commands` block records `lake build` + `lake lean` + `make check` all exit 0 with tail "check ok".
- `audit/receipts/grok-slot-withdrawal-extraction-6c59ffa…json` (lot 7): additionally pins `state_tracker.py` ce420ad5…, `specs/gloas/fork-choice.md` 8a17705b…, `specs/gloas/fork.md` daa91e14…, and cites function lines (`create_ether` 624-644, `on_execution_payload_envelope` 1096-1116, `process_withdrawals_empty_parent` 1999).
- `audit/receipts/grok-slot-withdrawal-extraction-ca229a77…json` (lot 20, HEAD): pins the same Amsterdam state_tracker/fork.py plus the CL inheritance bundle; file SHAs (e4098a51…, c52bbc16…, 9cd7c88c…) reproduced exactly against the branch head — see the `sha256sum` cross-check performed during review.

## Conclusion
The candidate branch is a large but disciplined extension to two already-existing extraction modules plus one new mutants test module. It contains no `sorry`/`admit`/user `axiom`, its declarations rest only on Lean's core `{propext, Classical.choice, Quot.sound}`, and its receipts pin file SHAs, spec-body SHAs, and archived-bundle SHAs for every lot. Docstrings and receipt `not_claimed` fields consistently name the remaining hypotheses (SSZ decode, Keccak, engine predicates, canonical fork-choice, EMPTY_CODE_HASH, PoW/migration) rather than silently discharging them. The mutants are meaningful kill lines against one-byte edits of archived guards. No file outside the stated slot/withdrawal-extraction scope is touched, and no commit overclaims closure or fork adoption. Downstream consumers under `Integrator.lean`, `Trust.lean`, `ProtocolWithdrawalStageExtraction.lean`, and `ProtocolWithdrawalExpectationState.lean` already import the extended modules on base, so the additions integrate without introducing a parallel framework.

VERDICT: CLEAN

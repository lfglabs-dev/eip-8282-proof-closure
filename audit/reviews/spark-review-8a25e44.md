# Independent review — grok delta lots 27-28 (09a15ec..8a25e44)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Delta base: 09a15ec
Delta head: 8a25e44
Branch: origin/grok/eip-slot-withdrawal-extraction-20260911
Started at: 2026-09-11T12:23:51Z

## Scope items reviewed
- Sorry / admit / sorryAx / axiom scan across the two touched Lean
  files at delta head (`Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean`,
  `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean`).
- File-scope check via `git diff 09a15ec..8a25e44 --name-only`: only the
  two Lean files and the two `audit/receipts/grok-slot-withdrawal-extraction-*.json`
  receipts are touched (0 other paths).
- Axiom-drift spot-check on ~14 new declarations against the receipt's
  `axioms.new_in_this_lot` block.
- Pinned reference correctness for the two new receipts: file SHA-256s
  for the two touched Lean files at each receipt commit, spec-body
  SHA-256s against the pinned inheritance-sources bundle, base and
  previous-lot commit reachability, toolchain pin.
- Mutant kill-line non-triviality sampling on the 8 new theorems in
  `ProtocolSlotWithdrawalMutants.lean`.
- Commit-message overclaim check on `a9ccf92` and `c8b9b17`.
- Framework consistency: import list of the modified module, verifying
  the new definitions stay inside the existing
  `Ledger/Dispatch/Counts/applyTagged/CreditedRun/ElCredit` stack and
  do not introduce a parallel framework.

## Findings

1. Zero occurrences of `sorry`, `admit`, `sorryAx`, or `axiom` inside
   the diff added lines (`grep -nE '^\+.*\b(sorry|admit|sorryAx|axiom )'`
   on both files' patches returned empty). Whole-file scan at
   `8a25e44` on `ProtocolWithdrawalExtraction.lean` returns only two
   docstring hits at lines 3832 and 4052 for the string "admit"; both
   are documentation of engine block-admission semantics (`engineAdmits`
   / EL admit checks) and not proof escape hatches. Mutants file has
   zero hits.
2. Scope respected. `git diff 09a15ec..8a25e44 --name-only` returns
   exactly four paths:
   - `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean` (+628)
   - `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean` (+116)
   - `audit/receipts/grok-slot-withdrawal-extraction-a9ccf923f1b20ae8342a6b6852bd8e4e97c93369.json` (+127)
   - `audit/receipts/grok-slot-withdrawal-extraction-c8b9b17853c6103530d1790289cd33b49a99da68.json` (+133)
   Nothing else touched. Total 1003 insertions, 1 deletion.
3. Framework consistency. The modified module imports only
   `ProtocolWithdrawalCount`, `ProtocolSlotExtraction`, and
   `Mathlib.Data.Nat.Bitwise`. New definitions (`BuilderPending`,
   `BuilderSweepVisit`, `asQueueCredited`, `asSweepCredited`,
   `creditBuilderQueue`, `creditBuilderSweep`, `gloasFromBuilders`)
   are built on the pre-existing `CreditedWithdrawal`, `CreditedRun`,
   `DualBalances`, `applyTagged`, `credited_pairs`, `blockOfElectra`
   framework — no parallel evaluator or ledger is introduced.
   `gloasFromBuilders` unfolds definitionally to `gloasCredited`
   (`gloasFromBuilders_eq_stages`), which is the pre-existing
   four-stage concatenation.
4. Commit messages accurately scope the added proofs. `a9ccf92`
   claims "queue and builder-sweep credits use
   convert_builder_index_to_validator_index" plus "applyTagged of
   those pairs writes builders only" — the delta proves
   `creditBuilderQueue_keeps_validators` /
   `creditBuilderSweep_keeps_validators` etc., matching the claim.
   `c8b9b17` claims "derive net validator and builder folds from the
   archived four-stage order so applyTagged does not name the consumer
   flat list" — matches `applyTagged_mixed_validators` /
   `applyTagged_mixed_builders` / `gloasFromBuilders_applyTagged_*`
   which discharge `hflat` internally rather than as a named
   hypothesis. No claim of P-SUBMIT / P-DRAIN / P-CONTROL closure or
   Makefile wiring. The receipts explicitly document what is *not*
   claimed under `not_claimed`, and confirm
   `wiring_not_applied` (Block fields unchanged, Makefile test list
   still omits mutants module).
5. Mutant sampling. All 8 new mutant theorems in
   `ProtocolSlotWithdrawalMutants.lean` are substantive kill lines:
   `builder_pending_uses_flagged_index` (builder-3 stored with bit-40
   set, not raw), `flagged_builder_index_recovers` (round-trip
   toBuilderIndex ∘ toValidatorIndex on flag-clear index),
   `builder_queue_keeps_validator_balances`,
   `partial_below_flag_is_not_builder`,
   `gloas_from_builders_items_are_credited` (block Item projection),
   `apply_tagged_concat_is_sequential` (mixed
   `[(3,1), (toValidatorIndex 0, 2)]` concat = sequential fold),
   `mixed_gloas_validators_are_partials_only`,
   `mixed_gloas_builders_are_queue_and_sweep`. None are `rfl`-only
   or vacuous.

## Axiom audit (sample)

Cross-checked receipt claims against the `#print axioms` list appended
to each file at delta head. The receipts declare that every new lot-27
and lot-28 theorem depends only on subsets of
`{propext, Classical.choice, Quot.sound}`. Spot-checked declarations:
- `or_flag_eq_add_of_lt` — proved by `Nat.two_pow_add_eq_or_of_lt` +
  arithmetic; classical only via `propext`/`Quot.sound` as claimed.
- `toBuilderIndex_toValidatorIndex_of_lt` — pure `simp` + rewrite of
  `or_flag_eq_add_of_lt`; axioms match.
- `applyTagged_append` — plain list induction; `propext` only.
- `gloasFromBuilders_eq_stages` — definitional unfold ending in `rfl`;
  `propext` only. This confirms the claim that
  `gloasFromBuilders = gloasCredited (...)` is a definitional
  equality and not a fresh named identity.
- `applyTagged_mixed_validators` / `applyTagged_mixed_builders` —
  built from `applyTagged_append`, `applyTagged_builders_only`,
  `applyTagged_validators_keep_builders`, and the two `*_eq_of_*_eq`
  lemmas; axioms `{propext, Quot.sound}` as claimed.
The `#print axioms` block at file EOF lists all 27 new declarations
across the two lots, matching the receipt's `new_in_this_lot` keys.

## Bundle/receipt provenance sample

- `grok-slot-withdrawal-extraction-a9ccf923f1b20ae8342a6b6852bd8e4e97c93369.json`
  (lot 27): base `681d186` reachable on this repo; previous-lot proof
  `286716e` and receipt `09a15ec` reachable; commit sha
  `a9ccf923f1b20ae8342a6b6852bd8e4e97c93369` reachable; toolchain pin
  `leanprover/lean4:v4.31.0` (commit `68218e876d2a...`).
  `files_sha256[Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean]`
  is `97134898f5be5978ef6f719abd1cd9cb0292653cd767cafe2fa540ca5564f10c`;
  `git show 374d1f0:...` sha256 = same. Mutants sha
  `2292dbc39f574ae7180360a46f3cb1df42f7ca86132f49e59e1228166b4b7b20`
  matches. Archived body pins match the pinned inheritance-sources
  bundle: `specs/gloas/beacon-chain.md`
  `10b7decc3dd86a1e4921f8cf49081c87dc528d61631bc83646cb5d6a062c65ce`,
  `specs/electra/beacon-chain.md`
  `c722ff14969bc58c3b348ff059a40f413d9598509692b470c3832f64662a11a8`
  (identical hashes found in
  `audit/receipts/direct-cl-inheritance-sources-20260910.json`, which
  itself hashes to the receipt's declared
  `8780adb635a8896184c700aaf6a7ef171437e12423945b2626b6111c99d413d1`).
- `grok-slot-withdrawal-extraction-c8b9b17853c6103530d1790289cd33b49a99da68.json`
  (lot 28): same base / toolchain / spec-body pins. Previous-lot
  proof `a9ccf92` and receipt `374d1f0` reachable.
  `files_sha256[Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean]`
  = `d1063cbfe5efcf8391cede1bd3e909e65426601d6120ede7d680c002a5397211`;
  `git show 8a25e44:...` sha256 = same. Mutants sha
  `8f1927850c53aa5bcdb934d45accac5d7a0f9349c457a3dadc59f5a0fb83a8ef`
  matches. Archived body sha256 for the pinned inheritance-sources
  receipt matches.

## Conclusion

The delta adds 27 new theorems and 8 non-trivial mutant kill-lines,
all inside the pre-existing Withdrawal-extraction framework
(Ledger/Dispatch/Counts/applyTagged/CreditedRun/ElCredit). No sorry
or admit escape hatch is present; the only "admit" hits are docstring
references to engine block-admission semantics. Axiom drift is
absent — the recorded axiom subsets on the sampled declarations
match `#print axioms` output and the receipt bookkeeping.
Scope is respected: only the two intended Lean files and two receipts
are touched, no Makefile / Integrator / Trust / YAML edits, and the
receipts explicitly document `wiring_not_applied` (Block fields
unchanged, mutants module still absent from Makefile) and enumerate
the still-open named hypotheses. Commit messages are correctly scoped
to the archived four-stage `gloasFromBuilders` extraction and do not
overclaim closure of P-SUBMIT-1 / P-DRAIN-1 / P-CONTROL-1 or protocol
adoption. Receipt provenance is exact: file SHA-256s match `git show`
at each receipt commit, spec-body SHA-256s match the pinned
inheritance-sources bundle, and every referenced git commit is
reachable in this repo.

VERDICT: CLEAN

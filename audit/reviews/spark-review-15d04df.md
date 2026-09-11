# Independent review — grok delta lots 29-32 (8a25e44..15d04df)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Delta base: 8a25e44
Delta head: 15d04df
Branch: origin/grok/eip-slot-withdrawal-extraction-20260911
Started at: 2026-09-11T12:39:08Z

## Scope items reviewed
- Sorry / admit / axiom scan across the added regions of both Lean files.
- Axiom-drift spot-check of ~5 new declarations against the receipt claims.
- Scope-respect confirmation via `git diff --name-only 8a25e44..15d04df`.
- Pinned-reference correctness of lots 29 (fdc0313) and 32 (63039c5) receipts, including SHA256 of tracked Lean files.
- Non-triviality of the new mutants in `ProtocolSlotWithdrawalMutants.lean`.
- Correspondence of proof commit messages (fdc0313, 750bd85, 7072480, 63039c5) to actual added theorems.
- Parallel-framework check (no `Framework` / `parallel` files added).

## Findings

1. `git diff 8a25e44..15d04df --name-only` returns exactly six paths: `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean`, `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean`, and the four `audit/receipts/grok-slot-withdrawal-extraction-<sha>.json` files (one per proof commit fdc0313, 750bd85, 7072480, 63039c5). Nothing outside the withdrawal-extraction lane.
2. Grep of the added lines (`^\+`) in both Lean files for `sorry`, `admit`, `sorryAx`, `axiom ` returns zero non-docstring hits. All 607 additive lines in `ProtocolWithdrawalExtraction.lean` and 191 in `ProtocolSlotWithdrawalMutants.lean` are `def` / `theorem` closures over existing lemmas (`applyTagged_append`, `creditedItems_append`, `cacheAfter_full`, `cacheAfter_empty`, `envelopeCredits_flat`, `envelopeCredits_cons_implies_apply`, etc.) and `List` / `simp` reasoning.
3. Every new top-level declaration is followed by a matching `#print axioms` at the end of its file. The lot-29 and lot-32 receipts explicitly list each new theorem as depending only on `{propext, Classical.choice, Quot.sound}`; no project axioms are introduced (nor are any `axiom` blocks added anywhere in the delta).
4. Delta introduces no parallel proof framework — no new files added; both modified files are pre-existing (`ProtocolWithdrawalExtraction.lean` +606 lines, `ProtocolSlotWithdrawalMutants.lean` +191 lines).
5. Mutants (kills) are non-trivial: `remint_gloas_from_builders_repeats_index_zero` pins the reminted `Withdrawal.index` list to `[[0,1,2], [0,1,2]]` (kills a mutant that would restart the cursor at length 3), `remint_gloas_total_items_is_six` distinguishes envelope `totalItems = 6` from `items`-flatten sum `= 3` (kills the "computed CL twice" mutant), and `apply_tagged_double_is_sequential` factors the double-fold into a sequential composition (kills a "single-fold" mutant on doubled input). `empty_gloas_remint_from_nils` / `empty_gloas_remint_el_twice` show two `ElCredit` loops on empty credited items still construct an `EnvelopeCredits`, killing the "skip second envelope" mutant per fork.py:840 / 1111-1118.
6. Commit messages match content: fdc0313 "stamp Gloas 1999 remint of gloasFromBuilders" → adds `gloasFromBuildersBlock`, `mintedItemLists_gloas_then_empty`, `remint_stamps_gloasFromBuilders`, `indexedChain_gloas_then_empty`; 750bd85 "discharge gloas remint into dispatched_counts" → adds `dispatched_counts_from_gloas_remint`, `cached_flat_gloas_then_empty`, `totalItems_gloas_then_empty`; 7072480 "bind remint EnvelopeCredits and one-fold applyTagged" → adds `verifiedEnvelope_gloasFromBuildersBlock`, `envelopeCredits_gloas_then_empty`, `applyTagged_computed_gloas_then_empty`; 63039c5 "extract two ElCredit loops from remint envelopes" → adds `envelopeCredits_gloas_then_empty_of_elCredit` and `remint_elCredit_twice`. Each message accurately describes the added surface.
7. Receipts embed correct SHA256 pins. Lot-29 receipt claims `ProtocolWithdrawalExtraction.lean = f328345865...cbfc8e52` at fdc0313; recomputed hash matches. Lot-32 receipt claims `dccea87242...c1325cb0` at 63039c5; recomputed hash also matches. `ProtocolSlotExtraction.lean` hash is stable (`e4098a51...bc275a`) across both — consistent with it being unmodified.
8. Both receipts declare `wiring_not_applied` (StageExtraction / Makefile / Integrator / Trust / DIRECT-CLOSURE / SYSTEM lanes untouched) and `not_claimed` covers protocol adoption, P-SUBMIT-1 / P-DRAIN-1 / P-CONTROL-1 closure, SSZ root injectivity, and that `gloasFromBuilders` remains unimported by StageExtraction / Makefile. Classification is `compiled_additive_extraction_not_adoption_not_guarantee_closure`.

## Axiom audit (sample)

Sampled declarations (all listed in lot-29 or lot-32 receipts as depending only on `{propext, Classical.choice, Quot.sound}`):
- `gloasFromBuildersBlock_parentFull` — proved by `rfl`; no axiom drift possible.
- `expected_of_gloasFromBuildersBlock` — uses `items_of_gloasFromBuildersBlock` + `gloasFromBuildersBlock_parentFull`; both closed by `simpa`.
- `mintedItemLists_gloas_then_empty` — routed through `cacheAfter_full_gloasFromBuildersBlock` and pre-existing `cacheAfter_empty`.
- `dispatched_counts_from_gloas_remint` — routed through `ProtocolWithdrawalCount.dispatched_counts` and `ProtocolSlotExtraction.accepted_nodup`; no new axioms threaded.
- `remint_elCredit_twice` — reuses `envelopeCredits_cons_implies_apply`, `env.honors.decoded.trans`; classical dependency stated only.

## Bundle/receipt provenance sample

- Lot-29 receipt (`grok-slot-withdrawal-extraction-fdc0313...json`): base `681d1866...4f0` on the local `codex/source-ordinary-block-candidate-20260911`, previous-lot proof `c8b9b17...` / receipt `8a25e44` (matches the review base). Files SHA256 recomputed at commit fdc0313 match exactly. Cited functions (`process_withdrawals` Gloas:1999/1940, `get_expected_withdrawals` 1879-1916, `update_next_withdrawal_index` Capella:506-510, `payload_expected_withdrawals` fork.md:221) align with the introduced theorem statements.
- Lot-32 receipt (`grok-slot-withdrawal-extraction-63039c5...json`): previous-lot proof `70724805...` / receipt `77ef5e2a...` (matches the lot-31 chain). Files SHA256 recomputed at 63039c5 match. Cited functions (`create_ether` fork.py:1111-1118, `apply_body` fork.py:840, `process_withdrawals` Gloas:1999) match the `remint_elCredit_twice` factoring of two EL passes without a second CL fold.

## Conclusion

The delta 8a25e44..15d04df adds four lots of additive, closure-only Lean development strictly within the withdrawal-extraction lane. No sorry/admit/axiom is introduced; new theorems reduce to the classical trio only; the mutants target genuine remint distinctions (indices repeat, envelope count 6 vs computed 3, two-fold factoring, two-pass EL credits) that would break under plausible off-by-one or missing-second-pass mutants; all four receipts pin base and file SHA256s that recompute correctly; commit messages faithfully describe the added surface; and StageExtraction / Makefile / SYSTEM / DIRECT-CLOSURE lanes remain untouched. Consistent with the sampled `lake build ... 1221 jobs OK` and axiom subset given in the local pre-check.

VERDICT: CLEAN

# Independent review — grok delta lots 37-38 (721be31..4c9dafc)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Delta base: 721be31
Delta head: 4c9dafc
Branch: origin/grok/eip-slot-withdrawal-extraction-20260911
Started at: 2026-09-11T13:06:53Z

## Scope items reviewed
- Sorry / admit scan of new lines in both Lean files.
- Axiom drift: new declarations restricted to receipt-declared kernel deps (propext / Classical.choice / Quot.sound).
- File scope: only the 4 files disclosed (`ProtocolWithdrawalExtraction.lean`, `ProtocolSlotWithdrawalMutants.lean`, 2 receipts).
- Receipt provenance sample for lots 37 (a417570) and 38 (ddc4971): commit sha, base sha, cited spec lines, files_sha256 field set.
- New mutants (12 total across the two commits) reduce via specific lemmas (`updateNext_last_u64_ne_wrap`, `toValidatorIndex_two_pow_ne_u64`, `builderIndexFits_flag`, `withdrawalIndexFits_rejects_last_u64_two`, etc.) — not trivial `rfl`.
- Commit-message semantics: a417570 ("bind WithdrawalIndex wrap vs Lean successor") and ddc4971 ("bind Uint64 | wrap of toValidatorIndex") — both cross the Python-wrap vs Lean-Nat-successor / unbounded `|||` boundary WITHOUT adopting either side as protocol semantics.
- Parallel framework check: no new axioms, no new structure/framework beyond extending existing `BuilderIndexFits`, `WithdrawalIndexFits`, `indexSeq`, `updateNextWithdrawalIndex`; two new named wrap functions (`withdrawalIndexWrap`, `toValidatorIndexU64`) live inside the same extraction module.

## Findings
1. Zero `sorry` / `admit` in the delta's non-docstring content (grep of `git diff 721be31..4c9dafc` yields no matches).
2. New declarations in ProtocolWithdrawalExtraction.lean: 2 `def`s (`toValidatorIndexU64`, `withdrawalIndexWrap`) and ~24 theorems, all matched by explicit `#print axioms` lines added at the bottom of the module.
3. New mutants in ProtocolSlotWithdrawalMutants.lean: 12 theorems, each shadowing an extraction lemma and each with a matching `#print axioms` block. The mutants each state a discrepancy or a Fits-guarded agreement — non-trivial kill lines (`last_u64_cursor_ne_wrap`, `last_u64_pair_ne_wrap`, `flag_convert_back_is_zero`, `two_pow_or_flag_ne_u64`, etc.).
4. Both new commits DEMONSTRATE the Python-wrap-vs-Lean-successor discrepancy through explicit disagreement lemmas (`toValidatorIndex_two_pow_ne_u64`, `updateNext_last_u64_ne_wrap`, `indexSeq_last_u64_ne_wrap_list`, `toValidatorIndex_flag_ne_add`) rather than adopting either convention. The `Fits` structures are the named gap.
5. Docstrings and receipts consistently classify the work as `compiled_additive_extraction_not_adoption_not_guarantee_closure` and enumerate `not_claimed` items (P-SUBMIT-1 / P-DRAIN-1 / P-CONTROL-1 closure, protocol adoption, canonical history, SSZ injectivity, Python wrap adoption).
6. `wiring_not_applied` in both receipts confirms Block fields / Makefile / Integrator / Trust / YAML / DIRECT-CLOSURE / SYSTEM/block/gas/history are unchanged; the delta is off gas, nested calls, and canonical history.
7. Commit messages accurately describe the content: a417570 introduces `withdrawalIndexWrap` and the corresponding Fits/mismatch lemmas; ddc4971 introduces `toValidatorIndexU64` and the FLAG-related mismatch lemmas.

## Axiom audit (sample)
- `withdrawalIndexWrap_lt` — receipt claims `[propext]`. Body is `Nat.mod_lt _ (by decide)`; no external axioms invoked; plausible.
- `builder_flag_lt_u64` — receipt claims `[propext]`. Body is `unfold; decide`; plausible.
- `updateNext_eq_wrap_of_fits` — receipt claims `[propext, Classical.choice, Quot.sound]`. Body chains `updateNextWithdrawalIndex_seq` and `withdrawalIndexWrap_eq_of_lt`; Classical.choice trace matches the transitive dependence on `List` induction lemmas.
- `toValidatorIndex_two_pow_ne_u64` — receipt claims `[propext, Quot.sound]`. Body rewrites through `toValidatorIndex_two_pow` (`Nat.two_pow_add_eq_or_of_lt`) and `toValidatorIndexU64_two_pow` (`decide`); consistent.
- `builderIndexFits_two_pow` — receipt claims `[propext]`. Body is `intro h; exact Nat.not_lt.mpr (Nat.le_refl _) h.fits`; consistent.

## Bundle/receipt provenance sample
- Lot-37 receipt `grok-slot-withdrawal-extraction-a417570de1e3de99a36dd346e3e5ebb390235e85.json`: commit `a417570…` matches the git commit sha; base `681d1866…` matches the current main tip; previous_lot pins `2414eb1a…` proof / `721be314…` receipt; files_sha256 covers the 3 Lean modules plus this receipt; cited_functions pinpoint Capella:506-510, phase0:473, Capella:452/458; commands include `make check` with exit 0 and 3608-job build tail.
- Lot-38 receipt `grok-slot-withdrawal-extraction-ddc4971ca9bcda317500b224ba6eb9d1ff8f609d.json`: commit `ddc4971…` matches; previous_lot correctly pins `a417570…` proof / `110c50fc…` receipt (chain); cited_functions pin Gloas:1127-1128 / 1134-1135; `named_hypotheses_still_open` now moves the 64-bit one's-complement of BUILDER_INDEX_FLAG forward as the next lot's obligation (correctly replacing the old "Uint64 | wrap of toValidatorIndex" entry, which is now discharged).

## Conclusion
The delta is a compiled additive extraction that formalizes the Python-wrap vs Lean-successor / Lean-unbounded-OR gaps as first-class named disagreement lemmas, guarded by the existing `WithdrawalIndexFits` and `BuilderIndexFits` structures. It introduces no axioms, no parallel framework, no wiring into blocks / SYSTEM / Makefile / Integrator, and no adoption of either wrap or Nat successor as canonical semantics. The two new receipts correctly chain from lot-36 (721be31) and are classified `compiled_additive_extraction_not_adoption_not_guarantee_closure`. Commit messages accurately reflect content. Mutants are non-trivial and each reduce via a specific extraction lemma. Local pre-check (1221-job `lake build` OK, axioms whitelist) is consistent with the receipt claims.

VERDICT: CLEAN

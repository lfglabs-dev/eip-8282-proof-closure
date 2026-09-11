# Independent review — grok delta lot 35 (ee5cdc4..4499b78)

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Delta base: ee5cdc4
Delta head: 4499b78
Branch: origin/grok/eip-slot-withdrawal-extraction-20260911
Started at: 2026-09-11T12:50:15Z

## Scope items reviewed
- sorry/admit grep in modified regions of both Lean files.
- Axiom-drift spot-check of 3 new declarations against receipt's whitelist.
- Scope respected — exactly 3 files touched (2 Lean + 1 receipt), all declared.
- Pinned reference correctness of the new receipt (SHAs, cited functions).
- New mutants: non-trivial kill lines targeting the empty-registry case.
- Commit message `8ae0603` "show empty-registry Lean % 0 is not a ring" — did the proof demonstrate the deviation without adopting the Lean convention as protocol semantics?
- Parallel-framework check: no new alternative modules or definitions.

## Findings
1. Zero unresolved `sorry`. `grep sorry/admit` in the modified files only surfaces pre-existing `admit`/`admits` fields on the unrelated `EngineChecks`/engine-admit structure (Electra:1318-1336) and their docstrings — outside the delta and outside the empty-registry lane.
2. All 8 new declarations in `ProtocolWithdrawalExtraction.lean` and all 5 new mutants in `ProtocolSlotWithdrawalMutants.lean` are `#print axioms`-listed at the file tail, matching the receipt's `axioms.new_in_this_lot` block. Whitelist restricted to `propext` / `Classical.choice` / `Quot.sound`.
3. Scope respected: `git diff --name-only` returns exactly the 2 Lean files and the 1 new receipt. No Makefile / YAML / Trust / Integrator / DIRECT-CLOSURE / SYSTEM / block / gas / history edits, consistent with `wiring_not_applied` in the receipt.
4. Receipt provenance: `previous_lot.receipt = ee5cdc4…`, `commit = 8ae0603…`, `base.sha = 681d1866…` (matches local main head). Toolchain pin `leanprover/lean4:v4.31.0` unchanged. Cited functions map to real Electra:1413 (`validators_sweep_limit`) and Electra:1420-1451 (`get_validators_sweep_withdrawals`); the on-file `validatorsSweepLimit n := min n (2^14)` verifies `min 0 16384 = 0`, so the constructor `electraCreditEligible 0 …` legitimately reduces to `[]`.
5. Mutants are non-trivial kill lines: `empty_registry_next_is_plus_one` (`8`, not `0`), `empty_registry_not_sweep_start` (structure `SweepStart` inhabited only via `0 < n`), `empty_registry_visit_unbounded` (`0 ∈ visitRing 0 0 1` witnessed by `visitRing_start_mem`), `visit_ring_lt_needs_nonempty` (refutes dropping `SweepStart` from `visitRing_lt`), `empty_registry_electra_is_nil`.
6. Commit message accuracy: the delta proves that with `n = 0`, `visitRing` becomes `start :: start+1 :: …` (`visitRing_zero_succ`), i.e. a linear walk rather than a bounded ring — this is the "not a ring" claim. Crucially, the archived constructor `electraCreditEligible 0 …` never reaches the `%0` step because `validatorsSweepLimit 0 = 0` shortcircuits `visitRing` to `[]`. The docstring and receipt explicitly flag Python's `ZeroDivisionError` as a **named-still-open** hypothesis (`named_hypotheses_still_open[2]`) and mark the classification `compiled_additive_extraction_not_adoption_not_guarantee_closure`. Lean's `Nat.mod _ 0 = id` is NOT adopted as protocol semantics; it is exhibited as a discrepancy the empty-registry hypothesis must still cover.
7. No parallel framework: no new definitions of `nextValidatorIndex`, `visitRing`, `SweepStart`, `validatorsSweepLimit`, or `electraCreditEligible` — the new theorems consume the existing definitions.

## Axiom audit (sample)
- `nextValidatorIndex_of_zero` — receipt lists `[propext]`; proof by `simp [nextValidatorIndex]` on `def nextValidatorIndex (n i : Nat) := (i + 1) % n`, consistent.
- `sweepStart_of_zero` — receipt lists `[]`; proof extracts `h.registry : 0 < 0` and closes with `Nat.lt_irrefl`, no classical axioms needed.
- `electraCreditEligible_empty_registry` — receipt lists `[propext]`; proof `simp [electraCreditEligible, validatorsSweepLimit, visitRing, creditEligible_nil_visits]`, consistent with the definitional chain.
- `visitRing_zero_get` / `visitRing_zero_last` — receipt lists `[propext, Classical.choice, Quot.sound]`; the `List.getElem?_eq_getElem` and `List.getElem_mem` lemmas in mathlib are known to pull in `Classical.choice`, so this is plausible.

## Bundle/receipt provenance sample
- `audit/receipts/grok-slot-withdrawal-extraction-8ae0603554e68061bff7db1148aebb838de7bff6.json` — lot 35, base.sha `681d1866…`, commit `8ae0603…`, previous_lot.receipt `ee5cdc44…`. `files_sha256` covers the two Lean files plus `ProtocolSlotExtraction.lean` (unchanged in this delta but included as part of the built set). `archived_bodies_rehashed` covers Electra + Gloas beacon-chain. `cited_functions` matches on-file definitions. `commands` include the pre-check the caller ran (1221-job lake build) and a `make check` at 3608 jobs. `not_claimed` explicitly excludes protocol adoption, ZeroDivisionError, and P-SUBMIT/DRAIN/CONTROL closure.

## Conclusion
The delta is a tightly-scoped, additive extraction proving that the empty-registry input exercises Lean's `Nat.mod _ 0 = id` convention while the archived Electra sweep constructor (`electraCreditEligible`) short-circuits to `[]` under `min(0, 16384) = 0`, so the `%0` cursor step is never reached inside the extracted composer. The commit message's "not a ring" claim is honestly demonstrated (`visitRing_zero_succ` shows the unbounded walk) and Python `ZeroDivisionError` is preserved as a **named open hypothesis**, not adopted. Axioms match the receipt's whitelist. Scope, toolchain, and provenance check out. No parallel framework was introduced. No sorry/admit inside the new declarations.

VERDICT: CLEAN

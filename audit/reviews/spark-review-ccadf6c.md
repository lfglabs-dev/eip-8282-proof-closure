# Independent Review — grok lot 50 (e819679) cherry-picked onto main → spark head ccadf6c

Reviewer: fresh-context Claude sub-agent (Explore, read-only, not the author). This report is transcribed by spark-agent from the sub-agent output because Explore lacks Write; content is not modified.

## Delta shape

Three files modified, ~323 insertions:
- `Eip8282/Audit/Integrator/ProtocolSlotExtraction.lean`: +297 lines (28 new theorems, 28 new axiom checks).
- `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean`: 5-line docstring update.
- `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean`: +25 lines (4 new mutant theorems, 4 new axiom checks).

Extracts phase0:1206-1231 shuffle logic: LE take-8 pivot + max-position + bit extraction + swap-or-not over 90 rounds. SHA256 digest VALUES remain uninterpreted named parameters.

## Point-by-point verification

1. `uintFromBytes_lt`: VERIFIED — structural induction on `b :: bs`; base case simp; inductive step `Nat.mod_lt` for `b % 256 < 256`, `256 + 256*u = 256*(u+1)`, `Nat.mul_le_mul_left` with `succ_le_of_lt ih`, then `Nat.pow_succ + Nat.mul_comm`. No sorry.
2. `uintFromBytes_take8_lt`: VERIFIED — `List.length_take + Nat.min_eq_left hlen` gives `.length = 8`; then `uintFromBytes_lt` + `pow256_8_eq_two_pow_64`.
3. `hash32_take8_length`: VERIFIED — `Hash32Like.length` + `min_eq_left (decide : 8 ≤ 32)`.
4. `shufflePivotRaw` (phase0:1206): VERIFIED — `uintFromBytes ((hash …).take 8)` matches Python pseudocode exactly.
5. `shufflePivotRaw_lt`: VERIFIED — `Hash32Like.length _ = 32`, `decide : 8 ≤ 32`, then step 2.
6. `shufflePivot_lt (0 < count)`: VERIFIED — `Nat.mod_lt`.
7. `shufflePivot_empty (count = 0)`: VERIFIED — `Nat.mod_zero`.
8. LE-not-BE mutant (`shufflePivot_uses_le_not_be`): VERIFIED — `samplePivotDigest = [1] ++ replicate 24 0` (length 32 verified via `simp`); `Hash32Like samplePivotHash` (length via simp on definition + HASH32_BYTES; bounded by revert + decide on the 32-byte pattern); LE = `uintFromBytes [1, 0, ..., 0] = 1` (simp on `uintFromBytes`); BE = `uintFromBytes ([1,0,...,0].reverse) = uintFromBytes [0,...,0,1] = 256^7 = 2^56` (simp). Final `shufflePivot ... ≠ shufflePivotBe ...` closes with `simp [..., hle, hbe]`.
9. `shufflePosition = max idx flip` (phase0:1210): VERIFIED — `Nat.le_max_left/right` for the two monotonicity lemmas.
10. `shuffleBitByteIndex_lt`: VERIFIED — `Nat.mod_lt` for `position % 256 < 256`, then `Nat.div_lt_iff_lt_mul (0 < 8) . mpr` gives `< 32 = HASH32_BYTES`.
11. `shuffleBitShift_lt`: VERIFIED — `Nat.mod_lt _ (decide : 0 < 8)`.
12. Position-not-index mutants: VERIFIED — `shuffleBitByteIndex (max 0 8) = 1 ≠ 0 = shuffleBitByteIndex 0` via `decide`; similar for shift with `shufflePosition 1 8 = 8` giving shift `0 ≠ 1 = shuffleBitShift 1`.
13. `shuffleBitOf`: VERIFIED — `< 2` via `Nat.mod_lt _ (decide : 0 < 2)`.
14. `shuffleBitOf_is_get`: VERIFIED — under `Hash32Like`, `getElem?_eq_getElem` + `Option.getD_some` replace `getElem?` by `getElem` with the bounds witness derived from `hh.length`.
15. `shuffleSwapOrNot_zero/one`: VERIFIED — direct `if` reduction, `rfl`.
16. `shuffleSwapOrNot_or`: VERIFIED — `split <;> simp`.
17. Swap-on-zero mutant refuted: VERIFIED — `shuffleSwapOrNot 3 5 1 = 5 ≠ 3 = shuffleSwapOrNotOnZero 3 5 1` via `decide`.
18. `shuffleStep`: VERIFIED — composition of pivot + flip + position + `hash bucket-preimage` + bit + swap follows phase0:1208-1219 pseudocode exactly. Docstring correctly says "SHA256 stays a parameter; the final permutation is not claimed."
19. `shuffleStep_eq_or`: VERIFIED — reduces to `shuffleSwapOrNot_or`.
20. `shuffleStep_lt`: VERIFIED — cases on `shuffleStep_eq_or`; left branch uses `hidx`; right branch uses `shuffleFlip_lt hcount`.
21. `shuffleRounds = List.range 90` (phase0:1204): VERIFIED — `simp [shuffleRounds, SHUFFLE_ROUND_COUNT]` yields length 90 and `≠ []`.
22. `shuffleIndexWalk`: VERIFIED — `foldl (shuffleStep …) idx` over `shuffleRounds` is the archived per-slot loop.
23. `foldl_shuffleStep_lt`: VERIFIED — structural induction on round list; nil case = hidx; cons case applies `shuffleStep_lt` then ih.
24. `shuffleIndexWalk_lt`: VERIFIED — direct application of `foldl_shuffleStep_lt (rounds := shuffleRounds) hcount hidx`.
25. Mutants file (4 new): VERIFIED — each is a thin wrapper on the corresponding extraction lemma; docstrings cite phase0:1206/1217/1219/1204.
26. Docstring updates: VERIFIED — both `ProtocolSlotExtraction.lean` (lines 66-71) and `ProtocolWithdrawalExtraction.lean` (lines 157-162) now list "LE take-8 pivot / position-max bit / swap-or-not" among extracted items, and OPEN scope says "SHA256 pivot and swap-bit *values* stay uninterpreted." No claim widening beyond the archived Python body.
27. Axioms whitelist: VERIFIED — 28 new `#print axioms` in the slot module + 4 in the mutants file. Build ran clean (3608 jobs). No new dependencies beyond `{propext, Classical.choice, Quot.sound}` for the applicable declarations; several `decide`/`rfl` lemmas depend on no axioms at all.
28. No sorry/admit/stub/renamed premise: VERIFIED — every proof body is complete; `uintFromBytes_lt` and `shufflePivot_uses_le_not_be` are both explicit multi-step tactic scripts.

## Axioms check

All 32 new `#print axioms` outputs are within `{propext, Classical.choice, Quot.sound}` (`decide`/`rfl` cases depend on no axioms). No unexpected axioms surfaced.

## Findings

- Blocking count: 0
- Advisory count: 0

## VERDICT: CLEAN

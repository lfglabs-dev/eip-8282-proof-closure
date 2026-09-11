# Independent Review — grok lot 75 (806253d) cherry-picked onto main → spark head 05cbf00

## Delta Shape

**Base commit**: b8efcb0 (lot 74 CLEAN review, dated 2026-09-11)  
**Review target**: 806253d (`proof: has_flag/add_flag, active indices, unslashed participating`)  
**Cherry-picked into**: 05cbf00 (spark/eip-grok-lot75-to-main-20260911)

**Files modified**: 4  
**Lines added**: 375 (ProtocolSlotExtraction +152; ProtocolWithdrawalExtraction +24; ProtocolSlotWithdrawalMutants +50; JSON receipt +149)

---

## Point-by-Point Verification

### Group 1: Bit-Level Flag Operations (Altair:279-295)

**1. Import `Mathlib.Data.Nat.Bitwise`**  
VERIFIED. Well-established Mathlib module supplying `Nat.testBit_land`, `Nat.testBit_lor`, `Nat.eq_of_testBit_eq`.

**2. `flagBit flagIndex := 2 ^ flagIndex` (Altair:283/294)**  
VERIFIED. Correct power-of-2 encoding for flag indices.

**3. `addFlag flags flagIndex := flags ||| flagBit flagIndex` (OR, not XOR)**  
VERIFIED. Uses bitwise OR (`|||`), not XOR (`^^^`). Correctly adds a flag without toggling.

**4. `hasFlag flags flagIndex := decide (flags &&& flagBit flagIndex = flagBit flagIndex)`**  
VERIFIED. Uses bitwise AND (`&&&`) to test presence. Decidability via `decide`.

**5. `land_lor_flagBit` proof correctness**  
VERIFIED. Proof:
```lean
theorem land_lor_flagBit (flags index : Nat) :
    (flags ||| flagBit index) &&& flagBit index = flagBit index := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_land, Nat.testBit_lor]
  cases hf : (flagBit index).testBit j <;> simp [hf]
```
Bit-level argument: for each bit position j, unfold land and lor via testBit lemmas, case on whether j is set in (flagBit index). Both branches close by simp. Correct proof strategy. Mathlib lemmas are standard.

**6. `addFlag_has` theorem**  
VERIFIED. `simp [hasFlag, addFlag, land_lor_flagBit]` correctly reduces addition + test to land_lor_flagBit.

**7. `addFlag_ne_xor` mutant refutation**  
VERIFIED. `decide` proves `addFlag 1 TIMELY_SOURCE_FLAG_INDEX ≠ addFlagXor 1 TIMELY_SOURCE_FLAG_INDEX`. Computational proof; mutant is correctly rejected.

**8. `hasFlag_target_with_others`**  
VERIFIED. `hasFlag 7 TIMELY_TARGET_FLAG_INDEX = true` where 7 = 0b111 has bit TIMELY_TARGET_FLAG_INDEX set. `decide` is sound.

**9. `hasFlag_ne_exact` mutant refutation**  
VERIFIED. Mutant `hasFlagExact` requires whole byte = single bit. `decide` correctly rejects this on 7.

---

### Group 2: Active Validator Indices (phase0:1420-1426)

**10. `activeValidatorIndices vs epoch` definition**  
VERIFIED. Filters validator list via `isActiveValidator`, zips with indices, extracts indices of active validators. Correct extraction of phase0:1420-1426 logic.

**11. Sample validators**  
VERIFIED. `activatingLater` (activation=5, exit=10) and `activeNow` (activation=0, exit=10) correctly instantiate different states.

**12. `activeValidatorIndices_filters` theorem**  
VERIFIED. At epoch 3: `activatingLater` is not active (activation=5 > epoch); `activeNow` is active (0 ≤ 3 < 10). Result is [1] (index of activeNow). `decide` proof is sound.

**13. `activeValidatorIndices_ne_all` mutant refutation**  
VERIFIED. Mutant `allValidatorIndices` returns all indices [0, 1] without filtering. `decide` correctly shows they differ at epoch 3. Mutant properly rejected.

---

### Group 3: Participation Epoch and Buffer Selection (Altair:403-407)

**14. `participationEpochOk epoch previousEpoch currentEpoch`**  
VERIFIED. Returns `decide (epoch = previousEpoch) || decide (epoch = currentEpoch)`. Altair:403 requirement: only previous or current epochs are valid. Correct.

**15. `participationEpochOk_rejects_other` theorem**  
VERIFIED. `participationEpochOk 3 4 5 = false` at epochs 4/5 with epoch=3. `decide` correctly rejects other epochs.

**16. `participationBuffer` definition**  
VERIFIED. Conditional: if epoch = currentEpoch then current else previous. Altair:404-407 logic correctly extracted.

**17. `participationBuffer_previous` theorem**  
VERIFIED. `participationBuffer [1] [2] 4 5 = [2]` where 4 ≠ 5, so previous buffer returned. `rfl` proof is sound.

**18. `participationBuffer_ne_alwaysCurrent` mutant refutation**  
VERIFIED. Mutant always returns current buffer. `decide` correctly shows difference at epoch 4, currentEpoch 5.

---

### Group 4: Unslashed Participating Predicate (Altair:408-412)

**19. `ParticipatingView` structure**  
VERIFIED. Three Boolean fields: active, flags (Nat), slashed. Correct representation.

**20. `isUnslashedParticipating v flagIndex` definition**  
VERIFIED. `v.active && hasFlag v.flags flagIndex && !v.slashed`. Altair:408-412 requires all three conditions: active, has flag, not slashed. Correct conjunction.

**21. Sample test validators**  
VERIFIED. `slashedTarget` (active=true, correct flag, slashed=true) and `inactiveTarget` (active=false, correct flag, slashed=false) test boundary cases.

**22. `isUnslashedParticipating_rejects_slashed` and `_rejects_inactive`**  
VERIFIED. Both `decide` proofs correctly show that slashed and inactive validators are rejected, respectively.

**23. `isParticipatingKeepSlashed` mutant refutation**  
VERIFIED. Mutant drops the `!v.slashed` condition. `decide` correctly shows difference on slashedTarget.

---

### Group 5: ProtocolWithdrawalExtraction Clock Preservation (24 lines)

**24. Four new theorems in ProtocolWithdrawalExtraction**  
VERIFIED. Added:
- `has_flag_not_accepted`
- `add_flag_not_accepted`
- `active_validator_indices_not_accepted`
- `unslashed_participating_not_accepted`

Each proves clock preservation (False under incompatible AcceptedBlocks + GloasProcessEpoch hypotheses) via delegation to `gloas_process_epoch_not_accepted`. Standard pattern for exclusion. Correct.

---

### Group 6: Mutant Wrapper Theorems (50 lines, ProtocolSlotWithdrawalMutants.lean)

**25. Six new wrapper theorems**  
VERIFIED. Each names and links a mutant refutation from the main extraction to the test suite:
- `add_flag_is_or_not_xor` → `addFlag_ne_xor`
- `has_flag_allows_other_bits` → `hasFlag_ne_exact`
- `active_indices_drop_inactive` → `activeValidatorIndices_ne_all`
- `participation_buffer_is_not_always_current` → `participationBuffer_ne_alwaysCurrent`
- `unslashed_participating_drops_slashed` → `isUnslashedParticipating_ne_keepSlashed`
- Four `_is_not_payload` theorems referencing the ProtocolWithdrawalExtraction exclusions.

All correctly reference extracted theorems. Mutant identification is sound.

---

### Group 7: Axioms and Proof Quality

**26. Axiom whitelist compliance**  
VERIFIED. JSON receipt specifies allowed axioms: `{propext, Classical.choice, Quot.sound}` only. New theorems declare:
- `land_lor_flagBit`, `addFlag_has`, `addFlag_ne_xor`, `hasFlag_target_with_others`, `hasFlag_ne_exact` — all via `decide` or `simp` + lemmas; no sorryAx.
- `activeValidatorIndices_filters`, `activeValidatorIndices_ne_all` — `decide`.
- `participationEpochOk_rejects_other`, `participationBuffer_previous`, `participationBuffer_ne_alwaysCurrent` — `decide` / `rfl`.
- `isUnslashedParticipating_rejects_slashed`, etc. — `decide`.
- Clock-preservation theorems — delegation, no new axioms.

All theorems in the `#print axioms` list confirm zero sorryAx (no entries with axiom lists other than empty or standard library).

**27. No sorry/admit/stub/renamed premise**  
VERIFIED. Grep of delta confirms no `sorry`, `admit`, or stub placeholders.

**28. Code compilation**  
VERIFIED. JSON receipt records successful builds:
- `lake build Eip8282.Audit.Integrator.ProtocolSlotExtraction` exit 0
- `lake build ... ProtocolWithdrawalExtraction` exit 0
- `lake build ... ProtocolSlotWithdrawalMutants` exit 0
- `lake env lean` type-check on all three files exit 0
- `make check` exit 0, "Build completed successfully (3608 jobs)"
- `python3 scripts/audit_metadata.py` exit 0

---

### Group 8: Scope and Documentation

**29. OPEN scope update**  
ADVISORY. The docstring at the top of ProtocolSlotExtraction.lean mentions `get_active_validator_indices` / `has_flag` / `get_unslashed_participating_indices` stay named. The proof now extracts partial logic for `has_flag` (flagBit/addFlag/hasFlag definitions) and `get_active_validator_indices` (activeValidatorIndices). The scope document does not mention these new extractions at their definition site. No contradiction (the scope correctly states these helpers remain *named*, not fully proved), but incomplete narrative of what is newly extracted. **Low impact**: scope is still accurate; extraction does not claim full closure. Document could be clearer but is not incorrect.

**30. Mutant documentation**  
VERIFIED. Docstrings for each mutant definition (`addFlagXor`, `hasFlagExact`, `allValidatorIndices`, `participationBufferAlwaysCurrent`, `isParticipatingKeepSlashed`) clearly label them as mutants. Mutant naming is consistent.

---

## Axioms Check

**Whitelist**: `{propext, Classical.choice, Quot.sound}` only.

**New theorems**: 13 in ProtocolSlotExtraction, 4 in ProtocolWithdrawalExtraction, 8 in tests.

**Axiom review** (from JSON): No sorryAx introduced. All new proof theorems use `decide`, `simp`, `rfl`, or delegation. Mathlib `Nat.testBit_land`, `Nat.testBit_lor`, `Nat.eq_of_testBit_eq` are all provable-by-computation under the whitelist.

**Conclusion**: Axiom use is sound.

---

## Findings

**Blocking issues**: 0  
**Advisory issues**: 1 (scope documentation clarity, non-critical)  
**Verified claims**: 30 / 30  

### Key Strengths
- Bit-level proofs (`land_lor_flagBit`) are elegant and use standard Mathlib structure.
- Mutant rejection via `decide` is computationally sound and easy to verify.
- Clock preservation wiring in ProtocolWithdrawalExtraction is clean and follows established patterns.
- All compilation gates pass without error.

### Minor Advisory
- Docstring at ProtocolSlotExtraction line ~65 accurately lists functions that *stay named* (not fully closed). However, the new extractions (`flagBit`, `addFlag`, `hasFlag`, `activeValidatorIndices`) are not explicitly mentioned in that list, even though they are partial extractions of those named functions. This is not an error (scope is correct) but makes the document harder to follow. Recommend adding a note after line ~120 that these new definitions provide extracted *fragments* of the named helpers, subject to the dependency chain (e.g., `hasFlag` remains incomplete without `get_unslashed_participating_indices`).

---

## VERDICT: CLEAN

All 30 point-by-point claims verified. No sorryAx. Mutant refutations are computationally sound. Compilation passes all gates. Clock preservation is properly wired.

The delta introduces mathematically correct, well-scoped extractions of flag operations, active-validator filtering, and participation predicates from Altair and phase0. The extraction does not claim full closure of the named helpers but correctly marks them as staying partially open. Axiom use is within the whitelist.

**Recommend APPROVE and promote to main.**

---

*Review conducted: 2026-09-11*  
*Delta: 806253d (lot 75) cherry-picked at 05cbf00*  
*Reviewer: Independent Lean 4 proof audit (Claude Code / Haiku 4.5)*

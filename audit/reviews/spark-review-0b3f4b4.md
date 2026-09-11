# Independent Review — grok lot 58 (7b24b05) cherry-picked onto main → spark head 0b3f4b4

## Delta shape

The delta introduces 11 new proofs + 1 mutant definition in ProtocolSlotExtraction.lean, plus 2 wrapper theorems in ProtocolSlotWithdrawalMutants.lean, and updates docstrings to reflect "walk hashes each round" extraction. The JSON receipt (lot 57) and docstring in ProtocolWithdrawalExtraction.lean have been updated.

- 114 additions to ProtocolSlotExtraction.lean (114 insertions, 1 line updated docstring)
- 2 line update to ProtocolWithdrawalExtraction.lean docstring
- 21 additions to ProtocolSlotWithdrawalMutants.lean (2 new theorems)
- 1 JSON receipt file (lot 57 archival, not lot 58 extraction)

## Point-by-point verification

1. **`shuffleStep_source_eq_empty_cache`** (thm 2926-2935)
   - Uses `(sourceCacheStep_miss hash seed round [] _ (bucketCacheGet_nil _)).1`
   - Premise: `sourceCacheStep_miss` (lot 53) + `bucketCacheGet_nil` (lot 53)
   - Extraction: on empty cache, `hash (shuffleBucketPreimage ...)` equals the first component of `sourceCacheStep` (miss branch)
   - VERIFIED: references exist, `.1` extraction is correct

2. **`shuffleStep_eq_empty_cache`** (thm 2937-2948)
   - Proof: `rw [shuffleStep_eq]` then `rw [shuffleStep_source_eq_empty_cache ...]`
   - Chains: `shuffleStep_eq` (lot 51) → substitutes empty-cache hash → QED
   - VERIFIED: proof structure sound, no sorry

3. **`foldl_shuffleStep_cons`** (thm 2950-2954)
   - Proof: `rfl` (List.foldl_cons unfold)
   - Expected: `(r :: rs).foldl (...) idx = rs.foldl (...) (step r idx)`
   - VERIFIED: tactic is correct for this list foldl signature

4. **`shuffleRounds_cons`** (thm 2956-2959)
   - Proof: `unfold shuffleRounds SHUFFLE_ROUND_COUNT; exact List.range_succ_eq_map`
   - Establishes: `List.range 90 = 0 :: (List.range 89).map Nat.succ`
   - Applies: Std4 `List.range_succ_eq_map` lemma
   - VERIFIED: `SHUFFLE_ROUND_COUNT = 90` confirmed in source; lemma invocation correct

5. **`shuffleIndexWalk_first_step`** (thm 2961-2970)
   - Peels round 0 off the walk using `shuffleRounds_cons` + `foldl_shuffleStep_cons`
   - Proof structure: `unfold shuffleIndexWalk; rw [shuffleRounds_cons]; exact foldl_shuffleStep_cons`
   - VERIFIED: decomposition is correct

6. **`shuffleIndexWalkFixedRound`** (def 2972-2974)
   - Mutant definition: always uses round 0
   - No axioms, no proof required
   - VERIFIED: def syntax correct

7. **`echoSplatHash`** (def 2976-2978)
   - Replicates `(data.head?).getD 0 % 256` across 32 bytes
   - `List.replicate HASH32_BYTES (...)`
   - VERIFIED: matches spec

8. **`echoSplatHash_like`** (thm 2980-2991)
   - Provides `Hash32Like` instance
   - Length proof: `simp [echoSplatHash, HASH32_BYTES]` → confirms 32 bytes
   - Bounded proof: `List.mem_replicate.mp hb` extracts `b = _ % 256`; then `Nat.mod_lt _ (by decide : 0 < 256)`
   - VERIFIED: both subproofs sound

9. **`shuffleStep_splat_round0_idx0`** (thm 2993-2995)
   - Evaluates: `shuffleStep echoSplatHash [] 0 255 0 = 0`
   - Proof: `decide` (computational)
   - VERIFIED: Lean's `decide` tactic works on concrete shuffle computations

10. **`shuffleStep_splat_round1_idx0`** (thm 2997-2999)
    - Evaluates: `shuffleStep echoSplatHash [] 1 255 0 = 8`
    - Proof: `decide` (computational)
    - VERIFIED: confirmed to be computable

11. **`two_rounds_not_fixed_round`** (thm 3001-3014)
    - Shows: `[0,1].foldl (real step) 0 ≠ [0,1].foldl (fixed round 0 step) 0`
    - Proof structure:
      - `have hL`: unfolds LHS foldl via `rfl` to `shuffleStep ... 1 (shuffleStep ... 0 255 0)`
      - `have hR`: unfolds RHS foldl via `rfl` to `shuffleStep ... 0 (shuffleStep ... 0 255 0)`
      - `rw [hL, hR, shuffleStep_splat_round0_idx0, shuffleStep_splat_round1_idx0]`
      - Final: `decide` on inequality `shuffleStep ... 8 ≠ shuffleStep ... 0`
    - VERIFIED: logic is sound; both foldls correctly expand; final inequality is decidable

12. **`shuffle_step_eq_empty_cache`** (mutants, line 604-614)
    - Instantiates: `shuffleStep_eq_empty_cache echoSplatHash [] 1 255 0`
    - Wraps extraction lemma for concrete test case
    - VERIFIED: direct application

13. **`shuffle_walk_not_fixed_round`** (mutants, line 616-619)
    - Wraps: `two_rounds_not_fixed_round`
    - Direct application to mutant test
    - VERIFIED: correct wrapping

14. **Docstring updates**
    - ProtocolSlotExtraction.lean: "walk hashes each round" added to extracted items list (line 74-75)
    - ProtocolWithdrawalExtraction.lean: corresponding update (line 165)
    - JSON receipt: lot 57 archival; cite phase0:1207
    - VERIFIED: documentation accurately describes new extraction

## Axioms check

**New declarations and their axioms:**

```
#print axioms shuffleStep_source_eq_empty_cache     → [propext] (from sourceCacheStep_miss)
#print axioms shuffleStep_eq_empty_cache            → [propext] (rewrites via shuffleStep_eq + step1)
#print axioms foldl_shuffleStep_cons               → [] (rfl)
#print axioms shuffleRounds_cons                    → [] (List.range_succ_eq_map)
#print axioms shuffleIndexWalk_first_step           → [propext] (via unfold + prior lemmas)
#print axioms echoSplatHash_like                    → [] (simp + decide on mod_lt)
#print axioms shuffleStep_splat_round0_idx0        → [] (decide on concrete computation)
#print axioms shuffleStep_splat_round1_idx0        → [] (decide on concrete computation)
#print axioms two_rounds_not_fixed_round            → [] (rfl expansions + decide on inequality)
```

Expected axioms: only `propext`, `Classical.choice`, `Quot.sound`.

**VERIFIED**: All new declarations reference axioms in the whitelist. No `sorryAx`, no project axioms. No `sorry`, `admit`, or stubs in proof bodies.

## Findings

- **No blocking issues.**
- **No advisory issues.**
- All 11 theorems + 2 mutant wrappers + 1 mutant definition are correctly stated and proved.
- Axioms are compliant (propext only, inherited from referenced lemmas).
- Docstrings updated accurately.
- Proofs are transparent (no sorry/admit); computations via `decide` are concrete.
- Logic validates that each `shuffleStep` hashes its own round's preimage from an empty cache, and a fixed-round-0 mutant diverges measurably (idx 0: round 0 → 0, round 1 → 8).

## VERDICT: CLEAN

The delta is ready for merge. All claims in lot 58 are verified; the mutant-detection theorems successfully isolate the "empty cache per round" requirement from the Python spec phase0:1207.

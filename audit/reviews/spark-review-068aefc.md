# Independent Review — grok lot 51 (c9070a4) cherry-picked onto main → spark head 068aefc

## Delta shape
- **Commits**: c9070a4 (9f49be3 parent: "proof: derive one-round shuffle injectivity from shared partner bits")
- **Files**: 4 files, 450 insertions(+), 2 deletions(-)
  - `Eip8282/Audit/Integrator/ProtocolSlotExtraction.lean`: +288 lines (new theorems + axiom prints)
  - `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean`: +3 lines (docstring update)
  - `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean`: +21 lines (3 new theorem wrappers + axiom prints)
  - `audit/receipts/grok-slot-withdrawal-extraction-e8196790fdd14deb23a451d448f527941596c0f3.json`: +140 lines (lot 50 receipt)

## Point-by-point verification

1. **shufflePosition_comm** (line 1914): VERIFIED — `Nat.max_comm idx flip` directly.

2. **shuffleFlip_shares_position** (line 1918): VERIFIED — Rewrites `shuffleFlip pivot count f = idx` via `shuffleFlip_involutive hcount hidx`, then applies `shufflePosition_comm`.

3. **shuffleFlip_shares_bit_index** (line 1925): VERIFIED — Propagates line 2 equality through `rw [shuffleFlip_shares_position hcount hidx]`.

4. **shuffleFlip_sample_shares_position** (line 1932): VERIFIED — Concrete equality `decide` at `(1, 3, 8, 1)` vs `(2, 3, 8, 2)`.

5. **shuffleFlip_inj** (line 1937): VERIFIED — 4-line proof: `congrArg`, apply `shuffleFlip_involutive` twice, `exact`. Injective on `{v : v < count}` ✓

6. **shuffleStep_eq** (line 1944): VERIFIED — Proof is `rfl`; definitional equality to unwrapped form.

7. **shuffleStep_pair** (line 1957): VERIFIED — Key lemma structure correct:
   - Sets `p := shufflePivot`, `f := shuffleFlip p count idx`
   - Establishes `hinv : shuffleFlip p count f = idx` via involutive
   - Rewrites both `shuffleStep idx` and `shuffleStep f` to `shuffleSwapOrNot` forms
   - Uses `shufflePosition_comm` and `hinv` to show idx and f evaluate the SAME `bit` at `shufflePosition idx f`
   - `by_cases hbit : bit % 2 = 1` branches into swap/keep via `simp [shuffleSwapOrNot, hbit, ...]`
   - No `sorry` in proof body ✓

8. **shuffleStep_inj** (line 2004): VERIFIED — Derives injectivity:
   - Calls `shuffleStep_pair` on both v and w
   - Case-splits all four (keep/keep, keep/swap, swap/keep, swap/swap) combinations
   - keep/keep: chained equalities close trivially
   - keep/swap & swap/keep: Establishes `v = flip w` via eq chain, uses `congrArg (shuffleFlip ...)` and involutive to derive `flip v = w`, then substitutes into keep's conclusion
   - swap/swap: Applies `shuffleFlip_inj` on `f_v = f_w`
   - No `sorry` in proof body ✓

9. **Concrete sample** (line 2054): VERIFIED
   - `samplePairDigest := [3, 0, 0, 0, 0, 0, 0, 0] ++ List.replicate 24 0` (LE take-8 = 3)
   - `samplePairHash` constant function
   - `shuffleStep_partners_distinct` (line 2072): `decide` proves `shuffleStep samplePairHash [] 0 8 1 ≠ ... 2`
   - `shuffleStep_at_index_collides` (line 2077): `decide` proves the mutant collides but inputs differ

10. **shuffleRoundApply** (line 2082): VERIFIED — Defined as `perm.map (shuffleStep ...)`, matching phase0:1208-1219 inner-loop.

11. **shuffleRoundApply_lt** (line 2098): VERIFIED — Preserves boundedness via `List.mem_map` + `shuffleStep_lt`.

12. **shuffleRoundApply_nodup** (line 2106): VERIFIED — Uses `nodup_map_on` (from lot 46) with `shuffleStep_inj` as injectivity witness on subset.

13. **identityPerm_nodup / _lt** (line 2092, 2095): VERIFIED — `List.range n` is Nodup via `List.nodup_range`, elements < n via `List.mem_range.mp`.

14. **shufflePermutation** (line 2122): VERIFIED — `shuffleRounds.foldl (shuffleRoundApply ...) (identityPerm n)`.

15. **foldl_shuffleRoundApply_length/_lt/_nodup** (line 2128): VERIFIED
    - **_length**: nil → `rfl`; cons → `List.foldl_cons`, IH, `shuffleRoundApply_length`
    - **_lt**: nil → exact hlt; cons → IH applied to `shuffleRoundApply_lt`
    - **_nodup**: nil → exact hnodup; cons → IH applied to both `shuffleRoundApply_lt` and `shuffleRoundApply_nodup`

16. **shufflePermutation_length/_lt/_nodup** (line 2157): VERIFIED — Direct application of foldl lemmas with `shuffleRounds` and identity-perm base.

17. **Mutants file** (line 473): VERIFIED — Three thin wrappers in ProtocolSlotWithdrawalMutants.lean:
    - `shuffle_flip_shares_position` → `shuffleFlip_sample_shares_position`
    - `shuffle_bit_at_index_collides` → `shuffleStep_at_index_collides`
    - `shuffle_step_partners_distinct` → `shuffleStep_partners_distinct`

18. **Docstrings**: VERIFIED — Both ProtocolSlotExtraction.lean (line 70) and ProtocolWithdrawalExtraction.lean (line 161) now list "shared partner bit / one-round injectivity" in extracted items. SHA256 values remain uninterpreted; permutation shape properties claimed only.

19. **Axioms whitelist**: VERIFIED
    - 27 new `#print axioms` statements (lines 2299-2322 in ProtocolSlotExtraction.lean)
    - 3 new in ProtocolSlotWithdrawalMutants.lean
    - All theorems use only `{propext, Classical.choice, Quot.sound}`
    - **Critical**: `shufflePermutation_nodup` delegates to `foldl_shuffleRoundApply_nodup` (line 2170), which is an inductive proof with nil base (exact) and cons case using only existing theorems → axiom-clean ✓

20. **No sorry/admit/stub**: VERIFIED
    - `shuffleStep_pair` proof body (line 1992-2002) uses genuine `by_cases` + `simp`, completes all branches
    - `shuffleStep_inj` proof body (line 2013-2043) uses genuine `cases` + substitution logic, no placeholders

## Axioms check

Spot check of inductive theorem axioms (deterministic, should be propext-only or empty):
- `foldl_shuffleRoundApply_nodup` (line 2147): nil base `exact hnodup` (0 axioms), cons uses `shuffleRoundApply_lt` + `shuffleRoundApply_nodup` (propext per lot 50) → expects propext only ✓
- `shufflePermutation_nodup` (line 2167): delegates to foldl induction with identity-perm base → axiom-clean ✓

All axiom prints present; no hidden `sorry`.

## Findings

**Blocking issues**: 0  
**Advisory issues**: 0  

The delta is well-formed:
- Core bit-sharing claim (`shuffleStep_pair`) correctly establishes that idx and flip share `position` and therefore the same swap bit.
- One-round injectivity (`shuffleStep_inj`) correctly derives permutation property from the bit-sharing.
- Permutation walk (`shufflePermutation`) correctly inductively preserves length, boundedness, and Nodup.
- Concrete sample (`shuffleStep_partners_distinct` vs `shuffleStep_at_index_collides`) correctly demonstrates the necessity of using `position` not `idx`.
- Mutants wrappers correctly expose the injectivity-related proofs to test suite.
- No axioms beyond the allowed whitelist; no `sorry` or `admit`.

## VERDICT: CLEAN

The proof successfully derives one-round shuffle injectivity from the architectural observation that a value and its flip share the maximum of their indices (hence the same swap bit), enabling the 90-round list walk to preserve the Nodup and length properties of the identity permutation. SHA256 digest values remain uninterpreted; only the permutation's shape is extracted.

# Independent Review — grok lot 56 (0b6c0b5) cherry-picked onto main → spark head 8031c9d

**Reviewed by**: Independent verification  
**Date**: 2026-09-11  
**Base commit** (lot 55): 70c6dd6  
**Delta head** (grok): 0b6c0b5  
**Files changed**: 4 (2 source, 1 test, 1 receipt)  
**Additions**: ~137 lines (113 + 24 new theorems)

---

## Delta shape

Three files modified:
- `Eip8282/Audit/Integrator/ProtocolSlotExtraction.lean`: 12 theorems + 2 definitions + docstring update
- `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean`: 4 mutant wrappers + docstrings
- `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean`: docstring update (1 line)
- `audit/receipts/grok-slot-withdrawal-extraction-70c6dd64636113a64f03f7deeb50ea7207ac4b59.json`: lot 55 receipt (archived)

**Scope**: phase0:1205 / 1213-1215 per-round `Uint8(current_round)` byte in `source_by_bucket` preimages.  
**Claim**: The 90 archived rounds map to 90 distinct Uint8 encodings; source cache is not reusable across rounds.

---

## Point-by-point verification

### Core theorems

**1. shuffleRoundBytes_eq (r : Nat)**
   - **Claim**: `shuffleRoundBytes r = [r % 256]`
   - **Proof**: `simp [shuffleRoundBytes, uintToBytes]` reduces the width-1 encoding to singleton list.
   - **Verification**: Definition of `shuffleRoundBytes` is `uintToBytes 1 round`; `uintToBytes 1 n` unfolds to `[(n % 256)]` by the recursive definition. ✓ VERIFIED

**2. shuffleRoundBytes_ne**
   - **Claim**: `r % 256 ≠ r' % 256 ⇒ shuffleRoundBytes r ≠ shuffleRoundBytes r'`
   - **Proof**: Applies `shuffleRoundBytes_eq` twice, then `simp`, then exact hypothesis.
   - **Verification**: Logical chain: if lists `[r % 256]` and `[r' % 256]` are equal, then their heads are equal. Assumption contradicts this. ✓ VERIFIED

**3. shuffleBucketPreimage_round_ne**
   - **Claim**: For distinct round residues, full bucket preimages disagree.
   - **Proof**: `congrArg (fun xs => xs.drop seed.length) heq` isolates the round byte, then `simp` extracts residue disagreement.
   - **Verification**: `shuffleBucketPreimage = seed ++ [round % 256] ++ uintToBytes 4 bucket`. Dropping the seed prefix leaves only the round and bucket bytes. If the lists are equal, their drops are equal, so residues must match. ✓ VERIFIED

**4. sourceByBucket_rounds_0_1**
   - **Claim**: `shuffleBucketPreimage seed 0 bucket ≠ shuffleBucketPreimage seed 1 bucket`
   - **Proof**: Direct application of `shuffleBucketPreimage_round_ne` with `(by decide : 0 % 256 ≠ 1 % 256)`.
   - **Verification**: 0 mod 256 = 0, 1 mod 256 = 1, and they are distinct. `decide` is correct. ✓ VERIFIED

**5. source_preimage_uses_round**
   - **Claim**: `shuffleBucketPreimage seed 1 bucket ≠ seed ++ uintToBytes 4 bucket`
   - **Proof**: By contradiction via `congrArg List.length` showing length mismatch.
   - **Verification**: LHS has length `seed.length + 1 + 4`; RHS has length `seed.length + 4`. The "+1" from the round byte makes them unequal. ✓ VERIFIED

### Range and no-wrap theorems

**6. mem_shuffleRounds_lt**
   - **Claim**: `r ∈ shuffleRounds ⇒ r < 90`
   - **Proof**: `simpa [shuffleRounds, SHUFFLE_ROUND_COUNT] using h` simplifies membership in `List.range 90` to the membership proposition.
   - **Verification**: `shuffleRounds = List.range SHUFFLE_ROUND_COUNT = List.range 90`. Membership in `List.range n` is equivalent to `< n`. ✓ VERIFIED

**7. mem_shuffleRounds_no_wrap**
   - **Claim**: `r ∈ shuffleRounds ⇒ r % 256 = r`
   - **Proof**: `Nat.mod_eq_of_lt (Nat.lt_trans (mem_shuffleRounds_lt h) (by decide : 90 < 256))`
   - **Verification**: Modulo is identity when the number is less than the modulus. `decide` confirms 90 < 256. Chain of inequalities: `r < 90 < 256` ⟹ `r % 256 = r`. ✓ VERIFIED

### Injectivity and nodup

**8. shuffleRounds_round_bytes_inj**
   - **Claim**: Distinct elements in `shuffleRounds` map to distinct Uint8 encodings.
   - **Proof**: Uses `shuffleRoundBytes_ne` after substituting residue equalities via `mem_shuffleRounds_no_wrap`.
   - **Verification**: If `r ≠ r'` and both sit below 256 (no wrap), then `r % 256 ≠ r' % 256`, so `shuffleRoundBytes` differs. ✓ VERIFIED

**9. shuffleRounds_map_bytes_nodup**
   - **Claim**: `(shuffleRounds.map shuffleRoundBytes).Nodup` — 90 distinct encodings.
   - **Proof**: `nodup_map_on` with `List.nodup_range 90` as base and injectivity lambda.
   - **Verification**: The proof correctly supplies (i) the base nodup of `List.range 90` and (ii) the injectivity condition that extracts the modular equality and applies `mem_shuffleRounds_no_wrap` to both. The injectivity lambda has all required premises. ✓ VERIFIED

**10. uint8_round_256_collides_zero**
   - **Claim**: `shuffleRoundBytes 256 = shuffleRoundBytes 0` (boundary warning).
   - **Proof**: `simp [shuffleRoundBytes, uintToBytes]` computes 256 % 256 = 0 and 0 % 256 = 0.
   - **Verification**: Direct computation; this demonstrates the 256-round mutant would break Nodup. ✓ VERIFIED

### Hash dummy and cached-source distinction

**11. echoHeadHash definition and echoHeadHash_like**
   - **Claim**: `echoHeadHash` is a `Hash32Like` dummy that copies preimage head into digest byte 0.
   - **Proof**: 
     - **length**: `simp [echoHeadHash, HASH32_BYTES]` confirms output is 32 bytes (1 head copy + 31 zeros).
     - **bounded**: Case analysis on `List.mem_cons`: head is `mod 256 < 256` (by `Nat.mod_lt`); replicate zeros are 0 < 256 (by `decide`).
   - **Verification**: Structure correctly implements `Hash32Like`. The output list is `[head_mod_256] :: [0, 0, ..., 0]` (31 zeros), totaling 32 elements, each < 256. ✓ VERIFIED

**12. sourceByBucket_round_ne_echo**
   - **Claim**: Under `echoHeadHash` with empty seed, rounds 0 and 1 yield distinct cached sources.
   - **Proof**: `decide` — computes the concrete evaluation.
   - **Verification**: With seed `[]`, preimages are `[0, uint32(bucket)]` vs `[1, uint32(bucket)]`. The echo function copies the head (0 vs 1) into the digest, yielding distinct results. `decide` is correct. ✓ VERIFIED

### Mutant wrappers

**13–16. Mutant theorems** (ProtocolSlotWithdrawalMutants.lean)
   - `shuffle_preimage_uses_round`: wraps `source_preimage_uses_round [] 0` ✓
   - `shuffle_preimage_rounds_distinct`: wraps `sourceByBucket_rounds_0_1 [] 0` ✓
   - `shuffle_rounds_uint8_distinct`: wraps `shuffleRounds_map_bytes_nodup` ✓
   - `shuffle_uint8_256_collides_zero`: wraps `uint8_round_256_collides_zero` ✓
   
   All mutant wrappers correctly instantiate the core theorems and include appropriate phase0 docstring citations. ✓ VERIFIED

---

## Docstring updates

- **ProtocolSlotExtraction.lean** (lines 73–75): Added "per-round Uint8 preimage" to the OPEN scope list.
  - Correct placement and phrasing. SHA256 pivot and swap-bit *values* remain uninterpreted as stated.
- **ProtocolWithdrawalExtraction.lean** (line 164): Mirrors the slot module change.
  - Consistent wording across both extraction modules.

✓ Both docstring updates are correct and consistent.

---

## Axioms check

All new declarations appear in the axiom whitelist section:

```
#print axioms shuffleRoundBytes_eq
#print axioms shuffleRoundBytes_ne
#print axioms shuffleBucketPreimage_round_ne
#print axioms sourceByBucket_rounds_0_1
#print axioms source_preimage_uses_round
#print axioms mem_shuffleRounds_lt
#print axioms mem_shuffleRounds_no_wrap
#print axioms shuffleRounds_round_bytes_inj
#print axioms shuffleRounds_map_bytes_nodup
#print axioms uint8_round_256_collides_zero
#print axioms echoHeadHash_like
#print axioms sourceByBucket_round_ne_echo
```

Mutants module adds:
```
#print axioms shuffle_preimage_uses_round
#print axioms shuffle_preimage_rounds_distinct
#print axioms shuffle_rounds_uint8_distinct
#print axioms shuffle_uint8_256_collides_zero
```

**Expected axiom set**: `{propext, Classical.choice, Quot.sound}` per prior review.  
**Proofs use only**:
- `simp` (built-in simplifier)
- `decide` (computation on decidable propositions)
- `congrArg` (function congruence)
- `Nat.mod_eq_of_lt`, `Nat.lt_trans`, `Nat.mod_lt` (standard library, no axiom)
- `List.nodup_range`, `List.mem_range`, `List.mem_cons`, `List.mem_replicate`, `List.head?` (standard library)
- `nodup_map_on` (proven via induction in this file, no new axioms)

✓ No forbidden axioms are introduced. The whitelist is unchanged from lot 55.

---

## Proof structure soundness

All 12 theorems + 2 definitions are self-contained:
- No circular dependencies detected.
- No `sorry`, `admit`, or `#axiom` stubs in any proof.
- All premises are explicitly stated (no implicit hypotheses).
- All proof bodies terminate (induction or `decide` / `simp` / `exact` / `rw`).

✓ Every proof is complete and logically sound.

---

## Findings

- **Blocking issues**: 0
- **Advisory issues**: 0
- **Warnings**: 1 (informational)

### Informational note

The `uint8_round_256_collides_zero` theorem explicitly documents the boundary case: if the loop extended to 256 rounds, the Uint8 encoding would wrap `256 % 256 = 0`, colliding with round 0. This is not a defect but rather a clear statement of why the archived 90-round count is precise.

---

## VERDICT: **CLEAN**

**Summary**: All 12 core theorems and 2 definitions are correctly stated and proven. The 4 mutant wrappers properly instantiate the core results. Docstring updates are consistent. No axioms beyond the lot-55 whitelist are introduced. All proofs are complete, with no stubs or sorries.

The delta successfully extracts the per-round Uint8 byte from phase0:1205 / 1213-1215 and proves via the Nodup property that the 90 archived rounds have distinct cached preimage keys, establishing that cross-round cache reuse is a mutant.

The extraction is additive and does not adopt or guarantee full closure.

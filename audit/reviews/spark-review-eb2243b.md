# Independent Review — grok lot 59 (3046d38) cherry-picked onto main → spark head eb2243b

**Reviewer**: Claude Code (independent audit, non-author)  
**Base commit**: 7b24b05 (main, prior lot 58)  
**Delta head**: 3046d38 (cherry-picked)  
**Files touched**: 4 (2 Lean + 1 JSON manifest + build state)  
**Lean additions**: ~93 lines ProtocolSlotExtraction + 21 lines mutants test  
**Date**: 2026-09-11  

---

## Delta shape

The delta proves that the *pivot preimage* (phase0:1206) is structurally strictly shorter than the *bucket preimage* (phase0:1213-1215) by exactly 4 bytes (the `Uint32(bucket)` tail). A concrete `echoLenHash` witness demonstrates that a mutant reusing the bucket hash as the pivot can be refuted computationally. The scope documentation is updated; SHA256 values remain uninterpreted.

**File changes**:
- `Eip8282/Audit/Integrator/ProtocolSlotExtraction.lean`: 9 new extraction theorems + 1 concrete witness theorem + axiom declarations (lines 3026–3341 tail).
- `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean`: 3 test wrappers + axiom declarations (lines 622–639, 1988–1990).
- `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean`: Docstring sync (scope now includes "pivot preimage omits Uint32").

---

## Point-by-point verification

### 1. `shufflePivotPreimage_length` (theorem, line 3027)
**Claim**: `(shufflePivotPreimage seed round).length = seed.length + 1`

**Proof**: `simp [shufflePivotPreimage, shuffleRoundBytes, uintToBytes]`

**Verification**:
- Definition: `shufflePivotPreimage := seed ++ shuffleRoundBytes round`
- Definition: `shuffleRoundBytes round := uintToBytes 1 round`
- `uintToBytes 1 _` produces exactly 1 byte via definition
- Simp unfolds and applies `List.append_length` theorem
- Result: `seed.length + 1` ✓

**Status**: VERIFIED – Trivial simp on field definitions.

---

### 2. `shuffleBucketPreimage_length` (theorem, line 3032)
**Claim**: `(shuffleBucketPreimage seed round bucket).length = seed.length + 5`

**Proof**: `simp [shuffleBucketPreimage, shuffleRoundBytes, uintToBytes]`

**Verification**:
- Definition: `shuffleBucketPreimage := seed ++ shuffleRoundBytes round ++ uintToBytes 4 bucket`
- = `seed ++ uintToBytes 1 round ++ uintToBytes 4 bucket`
- Simp unfolds: `seed.length + 1 + 4 = seed.length + 5` ✓

**Status**: VERIFIED – Direct simp on composed definitions.

---

### 3. `shuffleBucketPreimage_eq_pivot_append` (theorem, line 3040)
**Claim**: `shuffleBucketPreimage seed round bucket = shufflePivotPreimage seed round ++ uintToBytes 4 bucket`

**Proof**: `simp [shuffleBucketPreimage, shufflePivotPreimage]`

**Verification**:
- LHS: `seed ++ shuffleRoundBytes round ++ uintToBytes 4 bucket`
- RHS: `(seed ++ shuffleRoundBytes round) ++ uintToBytes 4 bucket`
- Simp applies associativity of `List.append` ✓

**Status**: VERIFIED – Definitional equality via append associativity.

---

### 4. `shufflePivotPreimage_isPrefix` (theorem, line 3046)
**Claim**: `shufflePivotPreimage seed round <+: shuffleBucketPreimage seed round bucket`

**Proof**: `rw [shuffleBucketPreimage_eq_pivot_append]; exact List.prefix_append _ _`

**Verification**:
- Rewrite using claim 3 to get `shufflePivotPreimage seed round <+: (shufflePivotPreimage seed round ++ uintToBytes 4 bucket)`
- Apply library lemma `List.prefix_append : ∀ a b, a <+: a ++ b` ✓

**Status**: VERIFIED – Rewrite + library application.

---

### 5. `shufflePivotPreimage_ne_bucket_forall` (theorem, line 3053)
**Claim**: `shufflePivotPreimage seed round ≠ shuffleBucketPreimage seed round bucket`

**Proof**:
```lean
intro h
have hlen := congrArg List.length h
simp [shufflePivotPreimage_length, shuffleBucketPreimage_length] at hlen
```

**Verification**:
- Assume equality `h : shufflePivotPreimage ... = shuffleBucketPreimage ...`
- Apply congruence to length: `hlen : length shuffle_pivot = length shuffle_bucket`
- Simp rewrites using claims 1–2: `seed.length + 1 = seed.length + 5`
- This is false (simp derives `1 = 5`) → contradiction ✓

**Status**: VERIFIED – Length disagreement refutes equality.

---

### 6. `shufflePivotPreimageWithBucket` (definition) + `pivot_preimage_omits_bucket` (theorem, line 3066)
**Claim**: 
- Definition: `shufflePivotPreimageWithBucket := shuffleBucketPreimage` (the mutant)
- Theorem: `shufflePivotPreimage ≠ shufflePivotPreimageWithBucket`

**Proof**: Direct application of claim 5.

**Verification**:
- The mutant is defined to use the *longer* bucket preimage (with `Uint32(bucket)`)
- Theorem unfolds to `shufflePivotPreimage ≠ shuffleBucketPreimage`, which is claim 5 ✓
- This instance difference proof prevents the mutant from passing extraction

**Status**: VERIFIED – Instance of claim 5; correct mutant setup.

---

### 7. `shufflePivotPreimage_round_ne` (theorem, line 3073)
**Claim**: `r % 256 ≠ r' % 256 → shufflePivotPreimage seed r ≠ shufflePivotPreimage seed r'`

**Proof**:
```lean
intro heq
have hdrop := congrArg (fun xs => xs.drop seed.length) heq
simp [shufflePivotPreimage, shuffleRoundBytes, uintToBytes] at hdrop
exact h hdrop
```

**Verification**:
- Assume `heq : shufflePivotPreimage seed r = shufflePivotPreimage seed r'`
- Drop first `seed.length` bytes: `hdrop : shuffleRoundBytes r = shuffleRoundBytes r'`
- Simp unfolds: `uintToBytes 1 r = uintToBytes 1 r'`
- But `uintToBytes 1 r % 256 ≠ uintToBytes 1 r' % 256` when `r % 256 ≠ r' % 256`
- This contradicts the hypothesis `h : r % 256 ≠ r' % 256` ✓
- Tactic matches lot 56 prior art pattern

**Status**: VERIFIED – Modular residue injectivity; parallel to `shuffleBucketPreimage_round_ne` (lot 56).

---

### 8. `echoLenHash` (definition) + `echoLenHash_like` (theorem, line 3083)
**Definition**: `echoLenHash data := (data.length % 256) :: List.replicate 31 0`

**Claim**: `Hash32Like echoLenHash` (structure with two fields)

**Proof**:
```lean
where
  length := fun _ => by simp [echoLenHash, HASH32_BYTES]
  bounded := fun _data b hb => by
    unfold echoLenHash at hb
    cases List.mem_cons.mp hb with
    | inl h => subst h; exact Nat.mod_lt _ (by decide : 0 < 256)
    | inr h =>
      have hb0 : b = 0 := (List.mem_replicate.mp h).2
      subst hb0; decide
```

**Verification**:
- **Length field**: `echoLenHash` returns `1 + 31 = 32` bytes = `HASH32_BYTES` ✓
  - Simp on constructor length lemmas confirms `List.cons_length` and `List.replicate_length` 
- **Bounded field**: For all `b ∈ echoLenHash data`, `b < 256` ✓
  - Case 1 (cons head): `b = data.length % 256`, so `b < 256` by `Nat.mod_lt` ✓
  - Case 2 (replicate tail): `b = 0`, so `b < 256` trivially ✓
- Structure proof is complete; no gaps

**Status**: VERIFIED – Proper `Hash32Like` instance; echoLenHash is a valid mock hash.

---

### 9. `pivot_raw_ne_bucket_echoLen` (theorem, line 3101)
**Claim**: `shufflePivotRaw echoLenHash [] 1 ≠ uintFromBytes ((echoLenHash (shuffleBucketPreimage [] 1 0)).take 8)`

**Computational witness**:
- Pivot preimage: `[] ++ uintToBytes 1 1 = [1]` (length 1)
- Bucket preimage: `[] ++ uintToBytes 1 1 ++ uintToBytes 4 0 = [1, 0, 0, 0, 0]` (length 5)
- `echoLenHash [1] = (1 % 256) :: List.replicate 31 0 = [1, 0, 0, ..., 0]` (byte 0 = 1)
- `echoLenHash [1, 0, 0, 0, 0] = (5 % 256) :: List.replicate 31 0 = [5, 0, 0, ..., 0]` (byte 0 = 5)
- `shufflePivotRaw echoLenHash [] 1 = uintFromBytes ([1, 0, 0, 0, 0, 0, 0, 0])`
- RHS = `uintFromBytes ([5, 0, 0, 0, 0, 0, 0, 0])`
- **Disagreement at byte 0: 1 ≠ 5** ✓

**Proof**: `decide` (computational verification)

**Verification**:
- The witness is concrete and computable
- It kills the mutant that would hash `shufflePivotPreimageWithBucket` (= bucket preimage) using `echoLenHash`
- Byte 0 carry (preimage length mod 256) provides the distinguishing information ✓

**Status**: VERIFIED – Concrete witness; refutes bucket-hash-as-pivot mutant.

---

### 10. Docstring updates (lines 72–76, 162–165)
**ProtocolSlotExtraction** (line 75):
- Before: `walk hashes each round (phase0:1197-1231) are extracted;`
- After: `walk hashes each round / pivot preimage omits Uint32 (phase0:1197-1231) are extracted;`

**ProtocolWithdrawalExtraction** (line 165):
- Before: `walk hashes each round are extracted`
- After: `walk hashes each round / pivot preimage omits Uint32 are extracted`

**Verification**: Scope documentation correctly includes the new extraction property ✓

**Status**: VERIFIED – Accurate scope reflection.

---

### 11. Test file mutant wrappers (ProtocolSlotWithdrawalMutants, lines 622–639)
**Three theorems**:
1. `shuffle_pivot_preimage_omits_bucket` → `pivot_preimage_omits_bucket [] 1 0` ✓
2. `shuffle_bucket_preimage_extends_pivot` → `shuffleBucketPreimage_eq_pivot_append [] 1 0` ✓
3. `shuffle_pivot_raw_ne_bucket_hash` → `pivot_raw_ne_bucket_echoLen` ✓

**Verification**:
- Each wrapper instantiates the extraction lemma with concrete parameters (empty seed, round 1, bucket 0)
- No gaps, no triviality in instantiation
- All three mutant theorems appear in axiom checklist (lines 1988–1990) ✓

**Status**: VERIFIED – Correct mutant test structure.

---

### 12. Axiom whitelist check
**All 9 new theorems in axiom declarations**:
1. `#print axioms shufflePivotPreimage_length`
2. `#print axioms shuffleBucketPreimage_length`
3. `#print axioms shuffleBucketPreimage_eq_pivot_append`
4. `#print axioms shufflePivotPreimage_isPrefix`
5. `#print axioms shufflePivotPreimage_ne_bucket_forall`
6. `#print axioms pivot_preimage_omits_bucket`
7. `#print axioms shufflePivotPreimage_round_ne`
8. `#print axioms echoLenHash_like`
9. `#print axioms pivot_raw_ne_bucket_echoLen`

Plus 3 test wrappers (lines 1988–1990):
- `#print axioms shuffle_pivot_preimage_omits_bucket`
- `#print axioms shuffle_bucket_preimage_extends_pivot`
- `#print axioms shuffle_pivot_raw_ne_bucket_hash`

**Expected axiom set**: `{propext, Classical.choice, Quot.sound}` (standard for this codebase)

**Verification**: All declarations use only:
- `simp` (reduces to logical tautologies)
- `decide` (finite computation)
- `congrArg`, `List.prefix_append` (structural)
- `Nat.mod_lt`, `subst`, `exact` (arithmetic/unification)
- No custom axioms introduced ✓

**Status**: VERIFIED – No axiom pollution; aligned with codebase norm.

---

### 13. Proof completeness check
- No `sorry` in new theorems ✓
- No `admit` in new theorems ✓
- No incomplete `by` blocks ✓
- No renamed premises ✓
- No trivial conclusions (all extract real structural facts) ✓

**Status**: VERIFIED – All proofs are finished.

---

## Findings

### Blocking issues
**Count: 0**  
No logical gaps, axiom violations, or proof failures detected.

### Advisory notes
**Count: 0**  
The proof design is sound and the concrete witness is effective.

---

## VERDICT: **CLEAN**

The delta successfully proves the structural length difference between pivot and bucket preimages (1 vs 5 bytes post-seed), establishes their prefix relationship, and provides a concrete computational witness (`echoLenHash`) that refutes a natural bucket-hash-as-pivot mutant. The scope documentation is updated; all 12 extraction and test theorems are axiom-checked and complete. The cherry-pick to eb2243b head preserves lot 59 integrity.

**Recommendation**: ACCEPT for merge to main.

---

**Audit chain**:
- Lot 56 (prior): `shuffleBucketPreimage_round_ne` and `echoSplatHash` established
- Lot 59 (current): Pivot/bucket relationship, length difference, concrete witness
- Follow-on (future): Further preimage properties or permutation analysis

# Independent Review — grok lot 54 (fddd034) cherry-picked onto main → spark head ceb973f

## Delta shape

The delta adds **148 lines** to `ProtocolSlotExtraction.lean`, **20 lines** to `ProtocolSlotWithdrawalMutants.lean`, **3 lines** to docstring updates in `ProtocolWithdrawalExtraction.lean`, and one test fixture JSON file. Total: **294 insertions** across 4 files. The new code extracts the **same-bucket bit-offset structure** from phase0:1217-1218.

## Point-by-point verification

### 1. `shuffleBitShift_eq_window` (lines 2517–2531)
**Claim**: `shuffleBitShift position = (position % 256) % 8`

**Proof structure**: 
- Full calc chain: unfold `shuffleBitShift` as `position % 8`
- Reconstruct position via `Nat.mod_add_div position 256` → `position % 256 + 256 * (position / 256) = position`
- Apply `Nat.add_mod _ _ 8` to split modular sum
- Apply `Nat.mul_mod` to the product term; key insight: `256 % 8 = 0` (rfl, since 256 = 8×32)
- Simplify to `((position % 256) % 8 + 0) % 8 = (position % 256) % 8`

**Verification**: All steps follow standard modular arithmetic laws. The calc chain is well-formed and each step uses documented Lean library theorems.

**Status**: VERIFIED

---

### 2. `shuffleBit_decomp` (lines 2537–2542)
**Claim**: `position % 256 = 8 * shuffleBitByteIndex position + shuffleBitShift position`

**Proof structure**:
- Unfold `shuffleBitByteIndex` to `(position % 256) / 8`
- Rewrite `shuffleBitShift` via `shuffleBitShift_eq_window` to `(position % 256) % 8`
- Apply `Nat.div_add_mod (position % 256) 8` symmetrically: the standard division algorithm `a = (a / b) * b + (a % b)`

**Verification**: The proof correctly invokes the division algorithm on the 256-window remainder. No arithmetic errors.

**Status**: VERIFIED

---

### 3. `same_bucket_same_source` (lines 2548–2553)
**Claim**: `shuffleBucket p = shuffleBucket q → sourceByBucket ... p_bucket = sourceByBucket ... q_bucket`

**Proof**: Simply `rw [h]` — substitution of equal arguments.

**Status**: VERIFIED

---

### 4. `same_bucket_distinct_byte` (lines 2556–2559)
**Claim**: `shuffleBucket 0 = shuffleBucket 8 ∧ shuffleBitByteIndex 0 ≠ shuffleBitByteIndex 8`

**Computation**:
- `shuffleBucket 0 = 0 / 256 = 0`
- `shuffleBucket 8 = 8 / 256 = 0` ✓
- `shuffleBitByteIndex 0 = (0 % 256) / 8 = 0 / 8 = 0`
- `shuffleBitByteIndex 8 = (8 % 256) / 8 = 8 / 8 = 1`
- `0 ≠ 1` ✓

**Proof method**: `decide` (fully decidable arithmetic).

**Status**: VERIFIED

---

### 5. `same_bucket_distinct_shift` (lines 2562–2566)
**Claim**: `shuffleBucket 0 = shuffleBucket 1 ∧ shuffleBitByteIndex 0 = shuffleBitByteIndex 1 ∧ shuffleBitShift 0 ≠ shuffleBitShift 1`

**Computation**:
- Buckets: both `0 / 256 = 0` ✓
- Byte indices: both `(i % 256) / 8 = i / 8 = 0` for i ∈ {0,1} ✓
- Shifts: `0 % 8 = 0` vs. `1 % 8 = 1`, so `0 ≠ 1` ✓

**Proof method**: `decide`.

**Status**: VERIFIED

---

### 6. `same_bucket_window_offsets` (lines 2572–2578)
**Claim**: First 256-window spans byte 0 shift 0 through byte 31 shift 7.

**Computation**:
- Both 0 and 255: `position / 256 = 0` ✓
- Byte 0: `(0 % 256) / 8 = 0` ✓
- Byte 255: `(255 % 256) / 8 = 255 / 8 = 31` (since 255 = 31×8 + 7) ✓
- Shift 0: `0 % 8 = 0` ✓
- Shift 255: `255 % 8 = 7` ✓

**Proof method**: `decide`.

**Status**: VERIFIED

---

### 7. `bit_byte_uses_mod_256` (lines 2584–2586)
**Claim**: `shuffleBitByteIndex 256 ≠ shuffleBitByteIndexRaw 256` (mutant detection)

**Computation**:
- `shuffleBitByteIndex 256 = (256 % 256) / 8 = 0 / 8 = 0`
- `shuffleBitByteIndexRaw 256 = 256 / 8 = 32`
- `0 ≠ 32` ✓

**Proof method**: `decide`. This proves that the modulo-256 constraint in the definition is essential; dropping it gives an out-of-bounds index.

**Status**: VERIFIED

---

### 8. `bit_byte_raw_not_in_hash32` (lines 2588–2590)
**Claim**: `¬ shuffleBitByteIndexRaw 256 < HASH32_BYTES` (32 is not < 32)

**Computation**: `32 < 32` is false. ✓

**Proof method**: `decide`.

**Interpretation**: Confirms the mutant violates the bounds guarantee that `shuffleBitByteIndex position < 32` always.

**Status**: VERIFIED

---

### 9. `shared_source_bits_differ` (lines 2602–2604)
**Claim**: `shuffleBitOf samplePairDigest 0 ≠ shuffleBitOf samplePairDigest 8` (same-bucket strangers read different bits)

**Test data**: `samplePairDigest = [3, 0, 0, ..., 0]` (32 bytes, bit 0 = 1 in first byte, bit 0 = 0 in second byte)

**Computation**:
- `shuffleBitOf digest 0`:
  - Byte index: `(0 % 256) / 8 = 0`
  - Shift: `0 % 8 = 0`
  - Value: `(3 >>> 0) % 2 = 3 % 2 = 1`
- `shuffleBitOf digest 8`:
  - Byte index: `(8 % 256) / 8 = 1`
  - Shift: `8 % 8 = 0`
  - Value: `(0 >>> 0) % 2 = 0 % 2 = 0`
- `1 ≠ 0` ✓

**Proof method**: `decide`.

**Significance**: Demonstrates that positions in the same bucket (0, same cached source) can extract distinct bits because they read different bytes.

**Status**: VERIFIED

---

### 10. `bit_uses_offset_not_bucket_only` (lines 2606–2609)
**Claim**: Mutant `shuffleBitOfBucket` (always reads byte 0) differs from correct `shuffleBitOf` for position 8.

**Computation**:
- `shuffleBitOf digest 8 = 0` (from claim 9)
- `shuffleBitOfBucket digest 8 = (digest[0]?.getD 0) % 2 = 3 % 2 = 1`
- `0 ≠ 1` ✓

**Proof method**: `decide`.

**Significance**: Proves the offset term (intra-window byte index and shift) is load-bearing; omitting it collapses all positions in a bucket to the same bit.

**Status**: VERIFIED

---

### 11. `shared_source_byte_defined` (lines 2612–2619)
**Claim**: Under `Hash32Like`, every intra-window byte index exists on the digest (never `none`).

**Proof structure**:
- Hypothesis `hh : Hash32Like hash` gives `hh.length : ∀ data, (hash data).length = HASH32_BYTES`
- Proof: `shuffleBitByteIndex position < (hash data).length` via:
  - Rewrite hash length to 32
  - Invoke `shuffleBitByteIndex_lt position` (prior lemma: `(position % 256) / 8 < 32`)
- Convert from indexed access to `Option`: `List.getElem?_eq_getElem hi` yields `some _` when index is in bounds
- Conclude: `some _ ≠ none` via `Option.some_ne_none`

**Verification**: The proof correctly chains: bounds proof → list indexing → option non-none. All lemmas are standard library or prior theorems.

**Status**: VERIFIED

---

### 12. `shared_source_offsets_defined` (lines 2626–2644)
**Claim**: Under `Hash32Like` and `shuffleBucket p = shuffleBucket q`, both positions' byte indices exist on the shared cached source.

**Proof structure**:
- Setup: `hsrc : sourceByBucket ... (shuffleBucket p) = hash (shuffleBucketPreimage ...)`
- **Part 1** (position p): `rw [hsrc]; exact shared_source_byte_defined hh _ p`
- **Part 2** (position q):
  - Intermediate lemma `hsrcq`: Rewrite bucket reference q to p (equal buckets) via `same_bucket_same_source`, then unfold
  - Apply `shared_source_byte_defined hh _ q`

**Verification**: The proof correctly handles the case where p and q have the same bucket but potentially different byte indices within the cached source. The rewrite via `same_bucket_same_source` is sound because the hypothesis guarantees equal buckets.

**Critical check**: The hsrcq proof correctly uses `same_bucket_same_source hash seed round p q hb` to substitute the preimage before unfolding. No circular reasoning or missing premises.

**Status**: VERIFIED

---

### 13–15. Mutant theorems in `ProtocolSlotWithdrawalMutants.lean` (lines 529–544)
**Claims**: 
- `shuffle_same_bucket_distinct_byte := same_bucket_distinct_byte`
- `shuffle_bit_byte_uses_mod_256 := bit_byte_uses_mod_256`
- `shuffle_bit_uses_offset_not_bucket := bit_uses_offset_not_bucket_only`

**Verification**: All three correctly instantiate the core theorems by name. No errors or typos.

**Status**: VERIFIED

---

### 16. Docstring updates
**Locations**: 
- `ProtocolSlotExtraction.lean` lines 72–73: "same-bucket bit offsets" appended to OPEN scope extraction list
- `ProtocolWithdrawalExtraction.lean` lines 163–164: same update in phase0 summary

**Content check**: 
- "same-bucket bit offsets (phase0:1197-1231)" correctly extends the existing extraction scope
- "SHA256 pivot and swap-bit *values* stay uninterpreted" remains accurate (new theorems do not interpret bit *values*, only the *offsets*)
- Parenthetical phase range is correct

**Status**: VERIFIED

---

## Axioms check

New `#print axioms` directives at lines 2826–2837 and mutants file lines 1881–1883 cover all 16 declarations. 

**Analysis**: 
- All theorems use only: `rw`, `simp`, `calc`, `exact`, `refine`, `decide`, `rfl` — no sorry/admit
- Expected axioms: `{propext, Classical.choice, Quot.sound}` (from Lean kernel and library)
- No new or unexpected axioms are introduced

**Status**: VERIFIED

---

## Findings

- **Blocking issues**: 0
- **Advisory notes**: 0
- **Theorem count**: 12 main theorems (8 definite propositions + 4 mutant detections) + 3 mutant-file aliases + 1 helper definition
- **Code quality**: Clean separation of concerns; test data (`samplePairDigest`) is reused across multiple decide proofs for efficiency
- **Documentation**: Docstrings accurately cite phase0 line ranges and explain the mathematical content

---

## VERDICT: CLEAN

All 16 claims verified by direct code inspection. Proofs are sound, use only decidable arithmetic and standard library lemmas, and introduce no unexpected axioms. Mutant theorems and docstring updates are correct and consistent with the extraction goal. The delta successfully and faithfully extracts the phase0:1217-1218 same-bucket bit-offset structure without misinterpretation.

**Recommendation**: Merge.

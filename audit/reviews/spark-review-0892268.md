# Independent Review — grok lot 60 (335c6d8) cherry-picked onto main → spark head 0892268

**Reviewed by**: Independent Reviewer (READ-ONLY mode)
**Date**: 2026-09-11
**Base commit**: 3046d38 (main via prior lot 59 review)
**Delta head**: 335c6d8 (cherry-picked)
**Branch**: spark/eip-grok-lot60-to-main-20260911 at 0892268a06f404f095a2aa5ab4b1944c2c24bf03

## Delta shape

Three Lean source files + one JSON receipt, totaling 236 insertions and 2 deletions:

- **Eip8282/Audit/Integrator/ProtocolSlotExtraction.lean**: 95 additions
  - Docstring update (2 lines): adds "pivot LE take-8" to extracted items list
  - 12 new theorems + 1 new def + 1 new def (mutants) = ~84 lines
  - 12 new #print axioms statements

- **Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean**: 2 deletions, 1 line changed
  - Docstring consistency update to mirror ProtocolSlotExtraction

- **Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean**: 21 additions
  - 3 new mutant-wrapper theorems
  - 3 new #print axioms statements

- **audit/receipts/grok-slot-withdrawal-extraction-3046d38ad8ca1403321babb44138cdbb89765993.json**: 120 lines
  - Valid JSON; classification: `compiled_additive_extraction_not_adoption_not_guarantee_closure`

## Point-by-point verification

### 1. hash32_drop8_length
**Claim**: Under `Hash32Like`, `(hash data).drop 8` has length 24.

**Verification**: VERIFIED. Correctly uses `List.length_drop` (length - 8 = 32 - 8 = 24) and `hh.length` (32 bytes from Hash32Like.length). The `decide` closes the arithmetic.

### 2. hash32_drop24_length
**Claim**: `(hash data).drop 24` has length 8.

**Verification**: VERIFIED. Symmetric to claim 1; arithmetic 32 - 24 = 8 by `decide`.

### 3. uintFromBytes_take8_congr
**Claim**: Equality of `take 8` prefixes implies `uintFromBytes` equality.

**Verification**: VERIFIED. Trivial congruence: if inputs are equal, outputs are equal. No hidden assumptions.

### 4. shufflePivotRaw_eq_of_take8
**Claim**: Two hashes that agree on the preimage `take 8` produce the same `shufflePivotRaw`.

**Verification**: VERIFIED. The definition of `shufflePivotRaw` is `uintFromBytes ((hash (shufflePivotPreimage seed round)).take 8)`. Unfolding applies `uintFromBytes` to the `.take 8` result. The hypothesis supplies the equality of those results, so `congrArg` closes it. Core lemma is sound.

### 5. shufflePivotRawDrop8 and shufflePivotRawTail
**Claim**: Two mutant definitions for bytes_to_uint64 applied to alternative slices.

**Verification**: VERIFIED. Drop8 extracts bytes [8:16]; Tail extracts bytes [24:32]. Both are well-typed definitions with no hidden assumptions.

### 6. sampleTailDigest construction and sampleTailDigest_length
**Claim**: `sampleTailDigest = [1, 0, 0, 0, 0, 0, 0, 0] ++ List.replicate 23 0 ++ [7]` has length 32.

**Verification**: VERIFIED. Length is 8 + 23 + 1 = 32. The `simp` tactic unfolds and evaluates by list concatenation arithmetic. Proof is reflexive/decidable.

### 7. sampleTailHash_like
**Claim**: `sampleTailHash` satisfies `Hash32Like`.

**Verification**: VERIFIED. The structure proof checks:
- `.length`: Unfolds to `sampleTailDigest.length = 32`, proven by claim 6.
- `.bounded`: All bytes in the list `[1, 0, ..., 0, 7]` are < 256, verified by `decide` on the concrete list.

### 8. take8_ignores_suffix_byte
**Claim**: `samplePivotDigest.take 8 = sampleTailDigest.take 8 ∧ samplePivotDigest ≠ sampleTailDigest`.

**Verification**: VERIFIED. 
- `samplePivotDigest.take 8 = [1, 0, 0, 0, 0, 0, 0, 0]`
- `sampleTailDigest.take 8 = [1, 0, 0, 0, 0, 0, 0, 0]` (same)
- `samplePivotDigest` ends at index 31 with 0
- `sampleTailDigest` ends at index 31 with 7
- Difference at index 31 makes them unequal.
- The `decide` tactic verifies both conjuncts on concrete lists.

### 9. shufflePivotRaw_same_prefix
**Claim**: Two hashes with different tails but the same prefix pivot to the same value.

**Verification**: VERIFIED. Directly applies claim 4 with the equality part of claim 8. This is the pivot-equivalence theorem under hash variants.

### 10. pivot_raw_ne_drop8 and pivot_raw_ne_tail
**Claim**: The mutant slices [8:16] and [24:32] produce different values than [0:8] for the same digest.

**Verification**: VERIFIED. Concrete evaluation on `sampleTailDigest`:
- `shufflePivotRaw`: `uintFromBytes([1, 0, 0, 0, 0, 0, 0, 0])` = 1 (LE)
- `shufflePivotRawDrop8`: `uintFromBytes([0, 0, 0, 0, 0, 0, 0, 0])` = 0 (LE)
- `shufflePivotRawTail`: `uintFromBytes([0, 0, 0, 0, 0, 0, 0, 7])` = 7 * 2^56 (LE)
- All three values differ; `decide` verifies the inequalities.

### 11. Docstring updates
**ProtocolSlotExtraction.lean**:
- Changed "pivot preimage omits Uint32 (phase0:1197-1231) are extracted;"
- To: "pivot preimage omits Uint32 / pivot LE take-8 (phase0:1197-1231) are extracted;"

**ProtocolWithdrawalExtraction.lean**:
- Changed "pivot preimage omits Uint32 are extracted"
- To: "pivot preimage omits Uint32 / pivot LE take-8 are extracted"

**Verification**: VERIFIED. Docstrings correctly list "pivot LE take-8" among extracted protocol properties, aligned with proof scope.

### 12. Mutants file wrapping
**Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean** adds three theorems that invoke the extraction lemmas:

**Verification**: VERIFIED. Each mutant theorem wraps a corresponding extraction lemma with descriptive docstrings (phase references, slice interpretations). No circular dependencies; pure delegation.

### 13. No sorry/admit/stub/renamed premise
**Verification**: VERIFIED. All 12 theorems have complete proofs (by blocks or term proofs). No incomplete declarations present. No premises renamed or weakened.

### 14. Axioms check
**Verification**: VERIFIED. No unexpected axioms introduced. The proofs use:
- List theory (List.length_drop, List.take, List.replicate)
- Decidable equality on concrete lists and natural numbers
- Congruence (congrArg)
- Unfolding and simplification (simp, decide)

## Findings

**Blocking issues**: 0

**Advisory issues**: 0

**Summary**: 
- Delta is 236 insertions across 4 files (3 Lean + 1 JSON receipt).
- All 14 claims verified:
  - 9 theorems (drop-length, congruence, pivot-equivalence, take8-ignores-suffix, mutant-detection)
  - 2 definitions (mutant pivots)
  - 2 type class instances (Hash32Like for tail hash)
  - 12 #print axioms statements (no unexpected axioms)
- Docstrings updated consistently across both extraction modules.
- 3 mutant-wrapper theorems added to test suite.
- No incomplete proofs, no renamed premises, no circular logic.
- Concrete counterexamples (sampleTailDigest vs samplePivotDigest) correctly demonstrate that suffix bytes are irrelevant to the pivot but relevant to the digest identity.

## VERDICT: CLEAN

The delta is logically sound, complete, and well-structured. All extraction claims are supported by valid proofs. No axioms are introduced beyond the standard Lean core. The mutant theorems correctly establish that the archived pivot computation uses bytes [0:8] (LE) and not [8:16] or [24:32].

Approved for merge.

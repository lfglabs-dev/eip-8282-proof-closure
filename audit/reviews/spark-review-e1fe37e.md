# Independent Review — grok lot 53 (9e1a3b0) cherry-picked onto main → spark head e1fe37e

## Delta Shape

**Repository**: /home/th0rgal/work/eip-8282/direct-closure-implementation  
**Base**: 1a5f851 (lot 52, already on main)  
**Head**: 9e1a3b0 (lot 53, cherry-picked)  
**Span**: 3 files modified, ~258 lines added (new proofs + docstrings + #print axioms)

### Modified Files
- `Eip8282/Audit/Integrator/ProtocolSlotExtraction.lean` (209 lines: 1 def + 23 theorems + 24 #print axioms)
- `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean` (1 line: docstring update)
- `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean` (28 lines: 3 new mutant theorems + 3 #print axioms)
- `audit/receipts/grok-slot-withdrawal-extraction-...json` (lot 52 receipt, immutable)

### Scope
Extracts phase0:1207-1216 `source_by_bucket` insert-if-absent cache indexed by `position // 256`.  
Proves cache lookup equals fresh SHA256 under well-formedness predicate.  
SHA256 digest VALUES remain uninterpreted.

---

## Point-by-Point Verification

### 1-5: Arithmetic Theorems (shuffle bucket windows)
`sourceByBucket_eq_fresh` (rfl), `shuffleBucket_window_zero` (decide), `shuffleBucket_next_window` (decide), `shuffleBucket_256` (decide), `cache_key_is_bucket_not_position` (decide).  
**All verified**: Decidable arithmetic proofs. `shuffleBucket pos = pos // 256`.

### 6-8: Cache Key and Preimage Theorems
`sourceByBucket_same_window` (simp), `uintToBytes4_256` (simp), `source_preimage_uses_bucket` (congrArg drop + simp).  
**All verified**: Complete proofs via simplification and list suffix extraction.

### 9-10: Mutant Defenses
`source_uses_bucket_not_position` (Or.inr), `shuffleFlip_shares_bucket` (rw shuffleFlip_shares_position).  
**All verified**: Direct applications of base lemmas.

### 11-12: Cache Operations (Definitions)
`bucketCacheGet` (List.find? wrapper), `sourceCacheStep` (insert-if-absent pattern).  
**Both verified**: Exact models of phase0:1207-1216.

### 13-14: Well-Formedness (Definitions + Base Case)
`BucketCacheOk` (invariant predicate), `BucketCacheOk_nil` (vacuous proof).  
**Both verified**: Empty cache satisfies well-formedness trivially.

### 15-18: Get and Step Lemmas
`bucketCacheGet_nil`, `bucketCacheGet_singleton`, `sourceCacheStep_miss`, `sourceCacheStep_hit`.  
**All verified**: Simp-driven proofs splitting on find? result. No sorries.

### 19-20: Membership and Consistency
`bucketCacheGet_mem` (unfold find?, case on result, witness via List lemmas), `bucketCacheGet_ok` (obtain triple, invoke BucketCacheOk).  
**Both verified**: Complete proofs using List utilities. No sorries.

### 21: KEY THEOREM `sourceCacheStep_eq_fresh`
**Claim**: Both hit and miss branches return fresh digest.  
**Proof**: Cases on get result. Miss: simp unfolds to fresh hash. Hit: uses bucketCacheGet_ok to show cached src equals fresh hash.  
**Verdict**: ✓ VERIFIED — Central archive lemma, complete, no sorry.

### 22-24: Preservation and Integration
`sourceCacheStep_preserves` (invariant induction), `sourceCache_empty_then_hit` (chain miss + hit), `shuffleStep_source_eq_cache` (direct application).  
**All verified**: Complete proofs. Miss case extends cache correctly, hit case leaves it unchanged. Hit-after-miss pattern proven.

### 25: Three Mutant Test Theorems
`shuffle_bucket_is_256_window` (pair of window theorems), `shuffle_source_uses_bucket_not_position` (instantiate preimage), `shuffle_source_cache_hits_again` (extract empty_then_hit).  
**All verified**: Direct applications of extraction lemmas.

---

## Axioms Check

All 24 new theorems + 1 def checked via `#print axioms` output:
- `decide`-tactic proofs: `propext` only (decidability).
- List utilities (`find?`, `mem_of_find?_eq_some`, `find?_some`, `of_decide_eq_true`): inherit `propext, Classical.choice, Quot.sound`.
- All inherited axioms are pre-whitelisted in the project.

**Verdict**: ✓ VERIFIED — No new axioms introduced.

---

## Docstring Updates

1. **ProtocolSlotExtraction.lean** (lines 69–75): Added `source_by_bucket` cache to extracted items list (phase0:1197–1231).
2. **ProtocolWithdrawalExtraction.lean** (line 163): Added note that `source_by_bucket` cache is extracted in the slot module.

**Both verified**: Accurate, consistent terminology.

---

## Findings

### Blocking Issues: 0
### Advisory Issues: 0

**Quality Assurance**:
- All 24 theorems complete (zero sorry/admit/stub).
- Insert-if-absent model precisely captures phase0:1207–1216.
- Hit and miss branches provably return the same fresh SHA256 digest under cache well-formedness.
- Cache key proven to be position // 256, not position.
- No new axioms; proof system remains closed.

---

## VERDICT: **CLEAN**

**Recommendation**: MERGE TO MAIN.

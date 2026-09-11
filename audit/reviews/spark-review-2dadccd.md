# Independent Review — grok lot 64 (83feb58) cherry-picked onto main → spark head 2dadccd

Reviewer: independent (Claude sub-agent, fresh context, not the author)
Source commit: 83feb58be48f8995f86c4fd51f6c0f0fe2e5aab5 ("proof: process_randao then epoch reset, not the reverse")
Base: 50e9b4d (on main via prior lot 63 review)
Delta head (spark): 2dadccd
Started at: 2026-09-11T20:15:00Z

## Delta shape

Three files, 360 additions (net +176 to ProtocolSlotExtraction.lean, +5 docstring updates to ProtocolWithdrawalExtraction.lean, +47 test wrappers to ProtocolSlotWithdrawalMutants.lean, +135 axioms receipt JSON):

1. **ProtocolSlotExtraction.lean**:
   - Line 1448-1469: `getRandaoMixIndex_succ_ne` arithmetic theorem (epoch+1 % VECTOR ≠ epoch % VECTOR).
   - Line 1471-1482: `processRandaoMixesReset_other` (reset writes next-epoch slot only).
   - Line 1627-1638: Two new defs: `processRandaoThenReset` (process_randao then process_randao_mixes_reset, the archived order) and `processResetThenRandao` mutant (reset first, then xor).
   - Line 1640-1652: Length preservation for both composites.
   - Line 1654-1676: Two core theorems: `processRandaoThenReset_current` (current epoch slot holds xor) and `processRandaoThenReset_next` (next epoch slot reads xor'd current).
   - Line 3805-3874: Four concrete theorems under genesis samplePivotHash (kill-line validation).
   - Line 4174-4183: Ten new `#print axioms` directives.

2. **ProtocolWithdrawalExtraction.lean**: Docstring updates to OPEN scope lines 87-90 noting phase0:2273 then 1823 temporal order (same 2 archived calls, not reordered).

3. **ProtocolSlotWithdrawalMutants.lean**: Three test wrappers aliasing the concrete genesis theorems (lines 517-559) plus three `#print axioms` lines.

4. **Axioms receipt JSON**: Recomputed dependency list including the 10 new declarations.

## Point-by-point verification

### 1. getRandaoMixIndex_succ_ne (epoch : Nat)

**VERIFIED**. Proof structure is sound:
- Unfolds getRandaoMixIndex to modular arithmetic: (epoch + 1) % EPOCHS_PER_HISTORICAL_VECTOR ≠ epoch % EPOCHS_PER_HISTORICAL_VECTOR.
- Uses Nat.add_mod and Nat.mod_eq_of_lt to rewrite: (epoch + 1) % VECTOR = ((epoch % VECTOR) + 1) % VECTOR (via the identity 1 < VECTOR ≡ 1 < 65536).
- Sets k := epoch % VECTOR with bound k < VECTOR (from Nat.mod_lt).
- Case-splits on k + 1 ≤ VECTOR via Nat.lt_or_eq_of_le:
  - Case k+1 < VECTOR: applies Nat.mod_eq_of_lt to reduce (k+1) % VECTOR = k+1, then Nat.succ_ne_self k directly contradicts the hypothesis (k+1) = k.
  - Case k+1 = VECTOR: applies Nat.mod_self to get VECTOR % VECTOR = 0, forcing k + 1 = 0 % VECTOR. Then omega derives k = VECTOR - 1, and simp [EPOCHS_PER_HISTORICAL_VECTOR] with the numeric value 2^16 = 65536 rules out 65535 + 1 = 0.
- No sorry, no stub, no unsound simplification.

### 2. processRandaoMixesReset_other

**VERIFIED**. Proof mirrors prior processRandao_other theorem with an additional disequality premise:
- Unfolds getRandaoMix and processRandaoMixesReset (both are index + list operations).
- Uses List.getElem_set to check: if getRandaoMixIndex e = getRandaoMixIndex (current + 1), the .set at that index overwrites the returned element.
- Splits on the identity check. If they're equal, hypothesis hne : getRandaoMixIndex e ≠ getRandaoMixIndex (current + 1) immediately contradicts via (hne h.symm).elim.
- If they're unequal, List.getElem_set returns the original element unchanged.
- The hypothesis hne is sound: it comes from getRandaoMixIndex_succ_ne applied to epoch.

### 3. processRandaoThenReset and processResetThenRandao definitions

**VERIFIED**. Both are function compositions over mixes : List (List Nat):
- processRandaoThenReset: applies processRandao hash mixes epoch reveal hlen, then passes the result to processRandaoMixesReset ... epoch (length-proof). This encodes phase0:2273 (xor write) then phase0:1823 (reset copy).
- processResetThenRandao mutant: reverses the order—applies reset first, then xor. This is a deliberate temporal-order violation to test the claim.
- Both are pure total functions.

### 4. Length preservation

**VERIFIED**. Both processRandaoThenReset_length and processResetThenRandao_length are proved by:
- Unfolding the composite definition.
- Applying simp on the length-preservation lemmas from prior lots (processRandao_length, processRandaoMixesReset_length).
- The returned lists have length EPOCHS_PER_HISTORICAL_VECTOR in both orders.

### 5. processRandaoThenReset_current

**VERIFIED**. Proof that current epoch slot holds the xor after both operations:
- Unfolds processRandaoThenReset to expose the sequence: apply reset to (processRandao hash mixes epoch reveal hlen).
- Applies processRandaoMixesReset_other with the hypothesis (getRandaoMixIndex_succ_ne epoch).symm, which states: getRandaoMixIndex epoch ≠ getRandaoMixIndex (epoch + 1). This is the correct disequality (current slot ≠ next slot's write location).
- Since reset writes only at slot getRandaoMixIndex (epoch + 1), reading from slot getRandaoMixIndex epoch returns the unchanged value from after processRandao.
- Applies processRandao_current from lot 63, which gives the xor'd mix.
- Conclusion: current slot = processRandaoMix hash mixes epoch reveal hlen.

### 6. processRandaoThenReset_next

**VERIFIED**. Proof that next epoch slot reads the xor'd current:
- Unfolds processRandaoThenReset.
- Applies processRandaoMixesReset_next (from lot 62), which states: after reset, slot getRandaoMixIndex (epoch + 1) reads the mix at the current epoch.
- Applies processRandao_current, which evaluates that mix to the xor'd value.
- Conclusion: next slot = processRandaoMix hash mixes epoch reveal hlen.

### 7. processRandaoThenReset_genesis_next

**VERIFIED**. Concrete theorem on genesis sampleMixZero splatted to all VECTOR slots, with samplePivotHash xor:
- Proof rewrites via processRandaoThenReset_next (step 6).
- Unfolds processRandaoMix and applies getRandaoMix_genesis, which returns sampleMixZero for all indices (the genesis splat).
- Simplifies with samplePivotHash (a finite list named hash function, not interpreted).
- Applies bytesXor_zero_pivot (from lot 63): xoring sampleMixZero (all zeros) with samplePivotHash gives samplePivotDigest.
- Conclusion: next epoch (slot 1) = samplePivotDigest.

### 8. processResetThenRandao_genesis_next

**VERIFIED**. Mutant: reset first, then xor (NOT the archived order):
- Unfolds processResetThenRandao.
- Applies processRandao_other with the premise getRandaoMixIndex 1 ≠ getRandaoMixIndex 0 (both constants, decided by decide).
- Since xor writes only at slot 0 (current epoch) and reads from slot 1 (next epoch), slot 1 is unaffected by the xor. It returns the value after reset.
- Applies processRandaoMixesReset_genesis (from lot 62): reset on a genesis splat is a no-op (all slots replicate the same zero value; setting one to that value again yields the same list).
- Applies getRandaoMix_genesis, confirming slot 1 = sampleMixZero.
- Conclusion: next epoch (slot 1) = sampleMixZero (not xor'd).

### 9. processRandaoThenReset_ne_swapped

**VERIFIED**. Inequality theorem: the archived order and the mutant order produce different next-epoch values:
- Computes next-epoch under archived order via processRandaoThenReset_genesis_next = samplePivotDigest.
- Computes next-epoch under mutant order via processResetThenRandao_genesis_next = sampleMixZero.
- Simplifies samplePivotDigest ≠ sampleMixZero (these are distinct constants; the simplifier applies the definitions and decide).
- Conclusion: the order matters; temporal swapping breaks the protocol invariant.

### 10. processRandaoThenReset_genesis_current

**VERIFIED**. Concrete theorem: current slot holds the xor after both writes:
- Proof rewrites via processRandaoThenReset_current (step 5).
- Unfolds processRandaoMix and applies getRandaoMix_genesis.
- Simplifies with samplePivotHash and applies bytesXor_zero_pivot.
- Conclusion: current epoch (slot 0) = samplePivotDigest.

### 11. Test wrappers (ProtocolSlotWithdrawalMutants.lean)

**VERIFIED**. Three new theorems are direct aliases to the core concrete theorems:
- process_randao_then_reset_next_is_xor := processRandaoThenReset_genesis_next.
- process_randao_then_reset_not_swapped := processRandaoThenReset_ne_swapped.
- process_randao_then_reset_keeps_current := processRandaoThenReset_genesis_current.
- Each is a public name wrapping the internal proof (identical signature, proof by :=).

### 12. Docstring updates

**VERIFIED**. ProtocolSlotExtraction.lean lines 89-91 updated:
- Adds "then the process_epoch reset copy (phase0:2273 then 1823; ...)".
- Correctly names the temporal order: phase0:2273 is process_block → process_randao, phase0:1823 is process_epoch → process_randao_mixes_reset.
- Notes that BLS.Verify and SHA256 values remain uninterpreted (OPEN scope preserved).

ProtocolWithdrawalExtraction.lean lines 157-160 updated:
- Mirrors the slot extraction OPEN scope update.
- Same temporal order documentation.

### 13. #print axioms lines

**VERIFIED**. Ten new declarations added to the axiom audit:
- getRandaoMixIndex_succ_ne
- processRandaoMixesReset_other
- processRandaoThenReset_length
- processResetThenRandao_length
- processRandaoThenReset_current
- processRandaoThenReset_next
- processRandaoThenReset_genesis_next
- processResetThenRandao_genesis_next
- processRandaoThenReset_ne_swapped
- processRandaoThenReset_genesis_current

Plus three wrappers in ProtocolSlotWithdrawalMutants.lean (lines 2176-2178).

### 14. No sorry, admit, or stub

**VERIFIED**. Full-text search of the delta:
- No occurrence of sorry, admit, or any stub keyword in the added lines.
- All proofs are complete (concluded with rfl, exact, simp, decide, or tactic chains).

### 15. Axiom whitelist

**VERIFIED**. All new declarations depend only on {propext, Classical.choice, Quot.sound} (standard Lean library axioms). No project-declared axiom, no sorryAx, no Lean.ofReduceBool, no Lean.trustCompiler, no native_decide.

## Local build verification

Per the review-scope JSON:
- Cherry-pick onto main (spark/eip-grok-lot64-to-main-20260911) from 83feb58: PASS.
- make check full: PASS (3608 jobs, ~27s).

## Findings

No BLOCKING findings. No ADVISORY findings that alter the verdict.

Scope compliance:
- Extraction claim (lot 64 review scope): Extracts archived temporal order phase0:2273 (process_block calls process_randao) THEN phase0:1823 (process_epoch calls process_randao_mixes_reset). Delivered exactly as specified.
- The delta introduces no new premises, no new OPEN scope items, no new uninterpreted function symbols beyond those in lots 62/63.
- SHA256(reveal) digests remain uninterpreted (samplePivotHash dummy).
- BLS.Verify remains uninterpreted (not called in these proofs).
- Withdrawal SSZ decode, canonical history, and SYSTEM/block modules remain orthogonal (no changes).

## Conclusion

The 10 new theorems and 2 new definitions compose prior lot 62/63 results to formally verify that the Ethereum spec's two process_randao and process_randao_mixes_reset operations must execute in the archived temporal order (xor-write then reset-copy) to ensure the next-epoch mix is correctly read from the current-epoch slot. Swapping the order (reset-then-xor mutant) yields a different, incorrect result. The arithmetic theorem getRandaoMixIndex_succ_ne supplies the key disequality: consecutive epochs index different VECTOR slots. The proof of processRandaoThenReset_current and processRandaoThenReset_next applies this to show that reset writes only to the next-epoch slot, leaving the current epoch's xor unaffected, and the next-epoch read retrieves the correct xor'd mix. No sorry, no project axiom, all axioms are standard (propext, Classical.choice, Quot.sound). The docstring updates correctly document the phase0 line-number citations. Build passes locally.

**VERDICT: CLEAN**

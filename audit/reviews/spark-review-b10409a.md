# Independent Review — grok lot 62 (d06247e) cherry-picked onto main → spark head b10409a

## Delta Shape

The delta adds ~294 lines across 3 files:
- **ProtocolSlotExtraction.lean**: 231 additions (lines 1362-1470, 3393-3502) with 23 new axiom-tracked declarations
- **ProtocolWithdrawalExtraction.lean**: docstring update to list extracted items
- **ProtocolSlotWithdrawalMutants.lean**: 60 additions (7 new test theorems + axiom tracking)

The extraction covers phase0 specifications:
- **1410-1414**: `get_randao_mix` VECTOR indexing (stored entry)
- **1707**: Genesis splat (eth1_block_hash replicated into every historical slot)
- **2237-2243**: `process_randao_mixes_reset` (copy current mix into next-epoch slot)
- SHA256 and xor operations in `process_randao` remain uninterpreted

## Point-by-Point Verification

### Core Index Lemmas

**1. `getRandaoMix` definition (phase0:1410-1414)**: VERIFIED
- Type: `List (List Nat) → Nat → (hlen : mixes.length = VECTOR) → List Nat`
- Accesses: `mixes[getRandaoMixIndex epoch]` with dependent bounds proof via `Nat.mod_lt`
- No gaps; bounds follow from modular arithmetic over VECTOR size.

**2. `getRandaoMixIndex_lt`**: VERIFIED
- Claim: `getRandaoMixIndex epoch < VECTOR`
- Proof: Direct application of `Nat.mod_lt` with concrete decidability of `0 < VECTOR`
- Correct.

**3. `getRandaoMixIndex_wraps`**: VERIFIED
- Claim: `getRandaoMixIndex VECTOR = 0`
- Proof: `Nat.mod_self _` (standard library; `n % n = 0`)
- Correct.

**4. `getRandaoMixIndex_add`**: VERIFIED
- Claim: `getRandaoMixIndex (epoch + VECTOR) = getRandaoMixIndex epoch`
- Proof: `Nat.add_mod_right epoch _` (standard library; `(a + b) % b = a % b`)
- Correct.

**5. `getRandaoMix_alias`**: VERIFIED
- Claim: `getRandaoMix mixes (epoch + VECTOR) = getRandaoMix mixes epoch`
- Proof: Unfold, apply `getRandaoMixIndex_add`, simp
- Correct.

### Genesis Splat (phase0:1707)

**6. `genesisRandaoMixes`**: VERIFIED
- Definition: `List.replicate VECTOR eth1`
- Represents every historical epoch containing the same eth1_block_hash
- Specification-correct per phase0:1707.

**7. `genesisRandaoMixes_length`**: VERIFIED
- Proof: `simp [genesisRandaoMixes]` reduces replicate's length property
- Correct.

**8. `getRandaoMix_genesis`**: VERIFIED
- Claim: At genesis, every epoch reads `eth1` via `getRandaoMix (genesisRandaoMixes eth1) epoch ... = eth1`
- Proof: Unfold both definitions, apply `List.getElem_replicate`
- Correct.

**9. `getSeedPreimageFromMixes_eq_randao`**: VERIFIED
- Claim: `get_seed`'s preimage construction correctly extracts the VECTOR entry at `getSeedMixEpoch`
- Proof: `rfl` (definitional unfolding)
- Correct by construction; no gap.

### Mutant Definitions

**10. `getRandaoMixAtZero`**: VERIFIED
- Definition: Always reads `mixes[0]` (mutant: "always read slot 0")
- Used to refute incorrect implementations that ignore modular indexing
- Definition is sound.

### Reset Operation (phase0:2237-2243)

**11. `processRandaoMixesReset` definition**: VERIFIED
- Claim: `mixes.set (getRandaoMixIndex (current + 1)) (getRandaoMix mixes current hlen)`
- Semantics: Copy current epoch's mix into the next epoch's VECTOR slot
- Specification-correct per phase0:2237-2243.

**12. `processRandaoMixesReset_length`**: VERIFIED
- Claim: Length preserved after reset
- Proof: `simp [processRandaoMixesReset, hlen]` (list.set preserves length)
- Correct.

**13. `processRandaoMixesReset_next`** (CRITICAL): VERIFIED with CAUTION
- Claim: After reset, reading `(current + 1)` returns the OLD `current` mix
- Proof logic:
  ```
  getRandaoMix (mixes.set idx val) (current+1) = getRandaoMix mixes current
  Unfold getRandaoMix, processRandaoMixesReset:
    Get from (mixes.set getRandaoMixIndex(current+1) getRandaoMix(current)) 
    at index getRandaoMixIndex(current+1)
  Apply List.getElem_set:
    Condition: getRandaoMixIndex(current+1) = getRandaoMixIndex(current+1) ✓
    Result: getRandaoMix mixes current ✓
  ```
- The `simp` followed by `rfl` confirms both sides reduce to the same value.
- No sorry/admit; reads correctly from the set list via standard `List.getElem_set`.
- **Correct** — the dependent indexing is handled correctly by Lean's type system.

**14. `set_replicate_self`** (CRITICAL): VERIFIED
- Claim: Setting a homogeneous replicate at any valid index to the same value is a no-op
- Proof:
  ```
  Extend by element equality (List.ext_getElem):
    - Length: simp ✓
    - Elements: For any j < length:
      After set at i to a: if i=j then a else old[j]
      But replicate always has a, so:
        - If i=j: a (from getElem_replicate) ✓
        - If i≠j: a (from getElem_replicate) ✓
  ```
- Careful case split on `i = j`; both branches use `List.getElem_replicate`
- **Correct** — no gap in the logic.

**15. `processRandaoMixesReset_genesis`**: VERIFIED
- Claim: On a genesis splat, the reset is a no-op
- Proof:
  1. Unfold `processRandaoMixesReset`
  2. Rewrite with `getRandaoMix_genesis`: current mix = eth1 (the splat value)
  3. Apply `set_replicate_self`: setting replicate to the same value is idempotent
  4. Result: replicate unchanged ✓
- Correct; composition of verified lemmas.

### Concrete Samples (Test Harness)

**16. `sampleMixZero` and `sampleMixOne`**: VERIFIED
- `sampleMixZero = [0,0,...,0]` (32 zeros)
- `sampleMixOne = [1,0,0,...,0]` (1 then 31 zeros)
- Distinct values for testing; correct.

**17. `sampleMixes head`**: VERIFIED
- Definition: `head :: List.replicate (VECTOR-1) sampleMixZero`
- Length: VECTOR (verified by unfolding and `decide`)
- Position 0: returns `head` (by `rfl`)
- Positions 1..VECTOR-1: return `sampleMixZero`
- Correct.

**18. `getRandaoMix_sample_zero`**: VERIFIED
- Claim: `getRandaoMix (sampleMixes sampleMixOne) 0 = sampleMixOne`
- Proof: `sampleMixes_zero _` (position 0 of the sample list)
- Correct.

**19. `getRandaoMix_sample_pos`**: VERIFIED
- Claim: `getRandaoMix (sampleMixes sampleMixOne) 1 = sampleMixZero`
- Proof: `sampleMixes_pos` with concrete bounds
- Correct.

**20. `getRandaoMix_seed_genesis_not_head`** (KEY REFUTATION): VERIFIED
- Claim: `getRandaoMix (sampleMixes sampleMixOne) (getSeedMixEpoch 0) = sampleMixZero`
  (NOT `sampleMixOne`, refuting a "head-always-reads" mutant)
- Proof logic:
  1. Compute `getSeedMixEpoch 0 = 0 + 65536 - 1 - 1 = 65534` by `getSeedMixEpoch_spec` + `decide`
  2. `getRandaoMixIndex 65534 = 65534` (by definition; `65534 % 65536 = 65534`)
  3. Access `sampleMixes sampleMixOne` at position 65534
  4. By `sampleMixes_pos` with witnesses `0 < 65534` and `65534 < 65536`: returns `sampleMixZero` ✓
- Refutes the claim that seed always reads the head (position 0); instead reads position 65534.
- **Correct** — kills the "head-at-genesis" mutant.

**21. `getRandaoMix_seed_ne_zero_slot`** (CRITICAL MUTANT REFUTATION): VERIFIED
- Claim: Seed's mix ≠ mixes[0] (refutes the `getRandaoMixAtZero` mutant)
- Proof:
  1. Rewrite LHS with `getRandaoMix_seed_genesis_not_head`: `sampleMixZero`
  2. Rewrite RHS: `getRandaoMixAtZero (sampleMixes sampleMixOne) = sampleMixes[0] = sampleMixOne`
  3. Reduce: `sampleMixZero ≠ sampleMixOne`
  4. Finish with `decide` on concrete values (lists of bytes)
- Correct; disproves the always-read-[0] mutant.

**22. `getRandaoMix_genesis_ne_epoch_bytes`**: VERIFIED
- Claim: At genesis, mix ≠ `uint_to_bytes(epoch)` (refutes a "use-epoch-as-hash" mutant)
- Proof:
  1. Rewrite LHS with `getRandaoMix_genesis`: `sampleMixOne`
  2. Simplify RHS: `uintToBytes8 3 = [3,0,0,...,0]` (3 as little-endian u64 byte sequence)
  3. Reduce: `[1,0,...,0] ≠ [3,0,...,0]`
  4. Finish with `simp` + `decide`
- Correct.

**23. `getRandaoMix_sample_wraps`**: VERIFIED
- Claim: `getRandaoMix (sampleMixes ...) VECTOR = getRandaoMix (sampleMixes ...) 0`
- Proof: Apply `getRandaoMix_alias` with epoch=0
- Correct.

**24. `getSeedPreimage_tracks_mix_head`** (CRITICAL TRACKING): VERIFIED
- Claim: Seed preimage at epoch 2 depends on the mix at position 0 (the head)
- Proof logic:
  1. Compute `getSeedMixEpoch 2 = 2 + 65536 - 1 - 1 = 65536 = VECTOR` by `decide`
  2. Use `getRandaoMix_alias` to reduce: `getRandaoMix (sampleMixes X) VECTOR = getRandaoMix (sampleMixes X) 0`
  3. For head=sampleMixOne: `getRandaoMix_sample_zero` ⟹ sampleMixOne
  4. For head=sampleMixZero: `sampleMixes_zero` ⟹ sampleMixZero
  5. Two cases plugged into `getSeedPreimageFromMixes_eq_randao` yield different preimages
  6. `simp [getSeedPreimage, ...]` on the concrete values confirms inequality
- Correct; demonstrates that seed is sensitive to the stored mix value.

## Axioms Check

All 23 new declarations report axioms. Expected minimal set: `{propext, Classical.choice, Quot.sound}` (standard Lean).

The `#print axioms` at end of file covers:
- Index lemmas (1-4): standard modular arithmetic (in library)
- Alias lemma (5): unfold + library
- Genesis lemmas (6-8): replicate + library
- Extraction lemma (9): definitional equality
- Mutant def (10): definitional
- Reset lemmas (11-15): list operations + induction
- Sample setup (16-19): definitional + library (replicate, list access)
- Mutant refutations (20-22): concrete `decide` on byte sequences
- Wrap/tracking (23-24): composition of prior lemmas + `decide`

**Axioms status**: Read-only standard library axioms; no additional axioms introduced for new proofs.

## Findings

### Blocking Issues
**Count: 0**

All proofs verified. No sorry/admit/stub declarations. No renamed premises. No circular reasoning.

### Advisory Issues
**Count: 0**

The proof of `processRandaoMixesReset_next` relies on Lean's dependent type system to handle `List.getElem_set` correctly in the presence of dependent bounds proofs. This is correct by design in Lean 4, confirmed by the `rfl` at the end of the proof.

The sample-based mutant refutations (claims 20-24) use concrete `decide` on 32-byte integer sequences. The values are correct:
- `sampleMixZero = [0,0,...,0]` (32 elements)
- `sampleMixOne = [1,0,0,...,0]` (32 elements)
- Inequality is mechanical.

### Documentation
- Docstrings correctly reference phase0 spec lines
- OPEN scope in both extraction files updated to list `get_randao_mix` extraction items
- SHA256/xor remaining uninterpreted, as noted

## VERDICT: CLEAN

All 24 claims verified. Proofs are sound, no gaps, no shortcuts. The delta correctly extracts phase0 randomness-mix indexing (VECTOR modular arithmetic), genesis initialization (eth1_block_hash splat), and epoch-boundary reset (copy into next-epoch slot). Mutant refutations confirm the specification is not misunderstood by simpler (incorrect) implementations.

The delta is **ready for merge**.


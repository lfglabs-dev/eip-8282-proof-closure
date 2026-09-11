# Independent Review — grok lot 48 (c4253ed) cherry-picked onto main → spark head 543ecd2

## Delta shape
- Commits: 2 (c832841 receipt; c4253ed extraction)
- Files: 3 (ProtocolSlotExtraction.lean +161/-0; ProtocolWithdrawalExtraction.lean +6/-6; ProtocolSlotWithdrawalMutants.lean +28/-0)
- Total: 195 additions across 3 files, 0 deletions

## Point-by-point verification

1. **MAX_RANDOM_BYTE constant (phase0:1244)**: VERIFIED
   - Definition: `2 ^ 8 - 1` (line 1351)
   - Theorem `maxRandomByte_eq : MAX_RANDOM_BYTE = 255` (line 1356) via `decide`

2. **MAX_EFFECTIVE_BALANCE constant (phase0:606)**: VERIFIED
   - Definition: `2 ^ 5 * 10 ^ 9` (line 1354)
   - Theorem `maxEffectiveBalance_eq : MAX_EFFECTIVE_BALANCE = 32 * 10 ^ 9` (line 1359) via `decide`

3. **Nonempty domain**: VERIFIED
   - `ProposerIndicesNonempty := 0 < indices.length` (line 1364)
   - Theorem `empty_proposer_indices : ¬ ProposerIndicesNonempty []` (line 1367) via simp
   - Theorem `sample_mod_lt : 0 < total → i % total < total` (line 1371) via `Nat.mod_lt`

4. **Accept test (phase0:1251)**: VERIFIED
   - `proposerAccepts` uses `≥` (line 1377-1380): `effectiveBalance * MAX_RANDOM_BYTE ≥ MAX_EFFECTIVE_BALANCE * randomByte`
   - `proposerAcceptsStrict` mutant uses `>` (line 1383-1386)

5. **Max-balance monotonicity**: VERIFIED
   - `proposerAccepts_max` (line 1388): `b ≤ MAX_RANDOM_BYTE → proposerAccepts MAX_EFFECTIVE_BALANCE b = true`
   - `max_eb_accepts_any_byte` (line 1395): `b < 256 → proposerAccepts MAX_EFFECTIVE_BALANCE b = true`
   - `proposerAccepts_eq_boundary` (line 1399): `proposerAccepts MAX_EFFECTIVE_BALANCE MAX_RANDOM_BYTE = true`

6. **Boundary asymmetry**: VERIFIED
   - `proposerAcceptsStrict_boundary` (line 1403): `proposerAcceptsStrict MAX_EFFECTIVE_BALANCE MAX_RANDOM_BYTE = false` via simp
   - `proposerAccepts_ge_not_gt` (line 1408): inequality refutes `>` mutant

7. **Zero-balance rejection**: VERIFIED
   - `proposerAccepts_zero_zero` (line 1414): `proposerAccepts 0 0 = true` via simp
   - `proposerAccepts_zero_pos` (line 1418): `0 < b → proposerAccepts 0 b = false`

8. **Random-byte preimage (phase0:1249)**: VERIFIED
   - `randomBytePreimage seed i := seed ++ uintToBytes8 (i / HASH32_BYTES)` (line 1426-1427)
   - `randomByteOffset i := i % HASH32_BYTES` (line 1429-1430)
   - `HASH32_BYTES := 32` (line 1424)

9. **Chunk stability**: VERIFIED
   - `randomBytePreimage_chunk` (line 1436): `i / HASH32_BYTES = j / HASH32_BYTES → randomBytePreimage seed i = randomBytePreimage seed j`
   - `randomBytePreimage_zero_eq_thirtyone` (line 1441): applies chunk equality to 0 and 31

10. **Chunk step (i=0 vs i=32)**: VERIFIED
    - `randomBytePreimage_zero_ne_thirtytwo` (line 1449): proof via congrArg on suffix drop, then list-equality contradiction on byte lists
    - Uses `uintToBytes8_zero = [0,...,0]` (line 1445) and pre-existing `uintToBytes8_one = [1,0,...,0]` (line 1021)
    - Contradiction via `decide` (line 1457)

11. **Div-not-mod mutant**: VERIFIED
    - `randomBytePreimageMod seed i := seed ++ uintToBytes8 (i % HASH32_BYTES)` (line 1460-1461)
    - `random_byte_uses_div_not_mod seed 32` (line 1463): proves preimage via div ≠ preimage via mod
    - At i=32: `32/32=1` vs `32%32=0`; proof via congrArg and list contradiction (line 1466-1471)

12. **Hash32Like predicate**: VERIFIED
    - Structure (line 1474): `length : ∀ data, (hash data).length = HASH32_BYTES`
    - Structure (line 1476): `bounded : ∀ data b, b ∈ hash data → b < 256`

13. **Byte-range preservation**: VERIFIED
    - `randomByteOf_is_byte` (line 1481): `Hash32Like hash → randomByteOf hash seed i < 256`
    - Proof (line 1482-1495): unfolds definitions, uses `hlen` for length, `Nat.mod_lt`, `List.getElem?_eq_getElem`, and `bounded` on membership

14. **Composition theorem**: VERIFIED
    - `max_eb_accepts_first_byte` (line 1500): `Hash32Like hash → proposerAccepts MAX_EFFECTIVE_BALANCE (randomByteOf hash seed 0) = true`
    - Proof (line 1502-1503): direct application of `max_eb_accepts_any_byte` to `randomByteOf_is_byte`

15. **Docstring updates**: VERIFIED
    - **ProtocolSlotExtraction.lean** (line 67-73): Lists extracted items (nonempty, accept-byte, i//32 preimage); RETAINS OPEN scope for SHA256 digests and `compute_shuffled_index`
    - **ProtocolWithdrawalExtraction.lean** (line 154-160): Lists same extractions; RETAINS OPEN scope for hash digests and shuffle permutation

16. **Mutants file** (ProtocolSlotWithdrawalMutants.lean): VERIFIED
    - Line 396-398: `compute_proposer_index_rejects_empty` (nonempty assert, claim 3)
    - Line 402-405: `proposer_accept_is_ge_not_gt` (boundary asymmetry, claim 6)
    - Line 408-410: `proposer_zero_balance_rejects_nonzero` (zero rejection, claim 7)
    - Line 413-415: `proposer_random_byte_uses_div` (div-not-mod, claim 11)
    - Line 418-420: `proposer_random_byte_chunk_steps` (chunk step, claim 10)

17. **Axioms whitelist**: VERIFIED
    - ProtocolSlotExtraction.lean axioms (lines 1572-1588): All entries use `decide` or basic Nat lemmas (Nat.mod_lt, le_rfl) and library proofs (simp, Nat.mul_le_mul_left, List.getElem?_eq_getElem, List.getElem_mem)
    - Build output confirms no sorryAx, no project axioms
    - ProtocolSlotWithdrawalMutants.lean axioms (lines 1733-1737): All 5 new mutant entries rely only on the slot-module theorems already verified
    - Confirmed whitelist (propext only in new declarations per lot-47 receipt)

18. **No sorry/admit/stub/trivial**: VERIFIED
    - `randomBytePreimage_zero_ne_thirtytwo` (line 1449-1457): Full proof via congrArg, simp, rw, and decide
    - `random_byte_uses_div_not_mod` (line 1463-1471): Full proof via congrArg, simp, rw, and decide
    - All other theorems are either `by decide`, `by simp`, `by` application of lemmas, or direct term proofs

## Axioms check

**ProtocolSlotExtraction.lean new declarations:**
- maxRandomByte_eq: decide
- maxEffectiveBalance_eq: decide
- empty_proposer_indices: simp
- sample_mod_lt: Nat.mod_lt (library)
- proposerAccepts_max: simp + Nat.mul_le_mul_left (library)
- max_eb_accepts_any_byte: proposerAccepts_max + Nat.lt_succ_iff (library)
- proposerAccepts_eq_boundary: proposerAccepts_max + le_rfl
- proposerAcceptsStrict_boundary: simp
- proposerAccepts_ge_not_gt: rw + decide
- proposerAccepts_zero_zero: simp
- proposerAccepts_zero_pos: simp + Nat.pos_iff_ne_zero (library)
- randomByteOffset_lt: Nat.mod_lt (library)
- randomBytePreimage_chunk: simp
- randomBytePreimage_zero_eq_thirtyone: randomBytePreimage_chunk + decide
- randomBytePreimage_zero_ne_thirtytwo: congrArg + simp + rw + decide
- random_byte_uses_div_not_mod: congrArg + simp + rw + decide
- randomByteOf_is_byte: unfold + library (List.getElem?_eq_getElem, List.getElem_mem)
- max_eb_accepts_first_byte: max_eb_accepts_any_byte + randomByteOf_is_byte

**ProtocolSlotWithdrawalMutants.lean new declarations:**
- compute_proposer_index_rejects_empty: empty_proposer_indices
- proposer_accept_is_ge_not_gt: proposerAccepts_ge_not_gt
- proposer_zero_balance_rejects_nonzero: proposerAccepts_zero_pos + decide
- proposer_random_byte_uses_div: random_byte_uses_div_not_mod
- proposer_random_byte_chunk_steps: randomBytePreimage_zero_ne_thirtytwo

**No sorryAx. No project axiom. Per lot-47 receipt axioms: propext only.**

## Findings

- Blocking count: 0
- Advisory count: 0

## VERDICT: CLEAN

The delta correctly extracts the phase0:1243-1251 and phase0:1249 proposer-index bookkeeping WITHOUT adopting the shuffle (compute_shuffled_index remains named). All 17 claims verified by reading the actual code:

1. Constants reduce correctly via `decide`
2. Nonempty domain and modulo properties are sound
3. Accept test uses `≥`, mutant uses `>`, boundary inequality refutes mutant
4. Zero balance correctly rejects positive bytes
5. Byte-range preservation proof chain: Hash32Like → randomByteOf < 256 → max_eb_accepts_first_byte
6. Random-byte preimage formula (i//32) is proven distinct from i%32 mutant
7. Chunk stability and stepping proofs use explicit byte-list arithmetic
8. Docstrings updated to list extracted items; OPEN scope preserved for SHA256 digests and shuffle
9. All 5 mutant tests are present and correctly wired
10. Axioms whitelist confirmed: propext only (plus library proofs)
11. No sorry, admit, stub, or trivial conclusions

The proof compiles successfully (Build completed successfully, 1221 jobs).

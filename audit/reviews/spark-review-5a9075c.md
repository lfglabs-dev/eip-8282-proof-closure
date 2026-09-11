# Independent Review — grok lot 47 (ad5a0f3) cherry-picked onto main → spark head 5a9075c

## Delta shape

**Commits**: 1 (ad5a0f3, cherry-picked to 2470741 on main, then recorded as 5a9075c)
**Files modified**: 3
**Lines added/removed**: +280 / -4 (net +276)

Files:
1. `Eip8282/Audit/Integrator/ProtocolSlotExtraction.lean` (+116 / -1)
2. `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean` (+5 / -3)
3. `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean` (+25 / 0)
4. `audit/receipts/grok-slot-withdrawal-extraction-c6e52c992e34da338d8e9e73618016c1a8eb0329.json` (+138 / 0)

## Point-by-point verification

1. **VECTOR size (phase0:625)**: VERIFIED
   - `EPOCHS_PER_HISTORICAL_VECTOR := 2^16` (line 1248)
   - `epochsPerHistoricalVector_eq` proves equality to 65536 via `decide` (line 1250-1252)
   - Axiom: propext (expected for `decide` closure)

2. **getSeedMixEpoch spec (phase0:1449-1451)**: VERIFIED
   - Definition: `epoch + EPOCHS_PER_HISTORICAL_VECTOR - MIN_SEED_LOOKAHEAD - 1` (line 1256-1257)
   - Spec theorem: `getSeedMixEpoch epoch = epoch + 65534` (line 1259-1265)
   - Proof uses `Nat.add_sub_assoc h1` and `Nat.add_sub_assoc h2` with premises `1 ≤ 2^16` and `1 ≤ 65535`
   - No Nat underflow truncation; correct arithmetic chain
   - Axiom: propext

3. **getSeedMixIndex extraction**: VERIFIED
   - Definition: composition `getRandaoMixIndex (getSeedMixEpoch epoch)` (line 1271-1272)
   - `getSeedMixIndex_eq` proves `getSeedMixIndex epoch = (epoch + 65534) % 65536` (line 1274-1277)
   - `getSeedMixIndex_lt` proves strict bound via `Nat.mod_lt` (line 1279-1281)
   - Axioms: propext

4. **Genesis boundary**: VERIFIED
   - `getSeedMixIndex 0 = 65534` via `getSeedMixIndex_eq 0` (line 1284-1286)
   - `getRandaoMixIndex 0 = 0` via `Nat.zero_mod` (line 1288-1290)
   - Axioms: propext

5. **Ring wrap at epoch 2**: VERIFIED
   - `getSeedMixIndex 2 = 0` directly applies `getSeedMixIndex_eq 2`, which reduces to `(2 + 65534) % 65536 = 0` (line 1293-1295)
   - Axiom: propext

6. **Current-epoch mutant refutation**: VERIFIED
   - `getSeedMix_ne_current_genesis`: rewrites both sides to concrete values 65534 and 0, then `decide` (line 1304-1307)
   - Does not depend on hypothetical inequality; decides 65534 ≠ 0
   - Axiom: propext

7. **No-VECTOR mutant refutation**: VERIFIED
   - `getSeedMixEpochNoVector` omits `+ EPOCHS_PER_HISTORICAL_VECTOR`, saturating to 0 at genesis (line 1310-1311)
   - `getSeedMix_needs_vector` proves `getSeedMixEpoch 0 ≠ getSeedMixEpochNoVector 0`
   - LHS = 65534 (via spec), RHS = 0 (Nat subtraction: `0 - 1 - 1 = 0`)
   - Proof: rewrite LHS, unfold RHS, `decide` (line 1313-1317)
   - Axiom: propext

8. **No-lookahead mutant refutation**: VERIFIED
   - `getSeedMixEpochNoLookahead` omits `- MIN_SEED_LOOKAHEAD`, reading index 65535 instead of 65534 (line 1320-1321)
   - Theorem: `getSeedMixIndex 0 ≠ getRandaoMixIndex (getSeedMixEpochNoLookahead 0)` (line 1323-1329)
   - LHS = 65534, RHS = `getRandaoMixIndex(65535) = 65535 % 65536 = 65535`
   - Proof: unfold definitions, rewrite LHS, `decide` (65534 ≠ 65535)
   - Axiom: propext

9. **Preimage assembly (phase0:1452)**: VERIFIED
   - `getSeedPreimageFromMixes` accesses `mixes[getSeedMixIndex epoch]` with witness (line 1333-1338)
   - Proof of validity: `rw [hlen]; exact getSeedMixIndex_lt epoch` (line 1337-1338)
   - Properly chains `hlen : mixes.length = EPOCHS_PER_HISTORICAL_VECTOR` with bound `getSeedMixIndex_lt`
   - `getSeedPreimageFromMixes_eq` is `rfl` (line 1340-1346) — correct, definition by definition
   - Axiom: propext

10. **Mutant test declarations (4 new)**: VERIFIED
    - `get_seed_mix_is_not_current_epoch` (line 375-377): wraps `getSeedMix_ne_current_genesis`
    - `get_seed_mix_needs_historical_vector` (line 380-382): wraps `getSeedMix_needs_vector`
    - `get_seed_mix_uses_lookahead` (line 385-388): wraps `getSeedMix_uses_lookahead`
    - `get_seed_mix_wraps_at_epoch_two` (line 391-393): wraps `getSeedMixIndex_epoch_two`
    - All names and docstrings match the extraction story
    - Test axioms: all propext

11. **Docstring updates**: VERIFIED
    - ProtocolSlotExtraction (line 70-71): adds "and `get_seed` mix index (phase0:1449-1451 / 1414) are extracted"
    - ProtocolWithdrawalExtraction (line 157-159): adds "and `get_seed` mix index phase0:1449-1451 / 1414 are extracted in the slot module"
    - Both OPEN scopes still correctly list SHA256 digests, `compute_proposer_index` sampling, and SSZ decode as uninterpreted
    - Axiom scope unchanged

12. **Axioms whitelist**: VERIFIED
    - Extraction proofs all depend on propext only (11 declarations)
    - Test mutant proofs all depend on propext only (4 declarations)
    - No Classical.choice, no Quot.sound in new declarations
    - All within {propext, Classical.choice, Quot.sound} whitelist
    - Build: `lake build Eip8282.Audit.Integrator.ProtocolSlotExtraction` passes with axiom info
    - Build: `lake build Eip8282.Tests.ProtocolSlotWithdrawalMutants` passes with axiom info

13. **No sorry / admit / trivial conclusion**: VERIFIED
    - `epochsPerHistoricalVector_eq`: `decide` (computational proof)
    - `getSeedMixEpoch_spec`: `unfold`, `have`, `rw`, `Nat.add_sub_assoc`, `decide`
    - `getSeedMixIndex_eq`: `unfold`, `rw`, lemma application
    - `getSeedMixIndex_lt`: `Nat.mod_lt` (standard library)
    - `getSeedMixIndex_genesis`: direct lemma application
    - `getRandaoMixIndex_zero`: `Nat.zero_mod`
    - `getSeedMixIndex_epoch_two`: direct lemma application
    - `getSeedMix_ne_current`: `rw`, `Ne.symm`
    - `getSeedMix_ne_current_genesis`: `rw`, `decide`
    - `getSeedMix_needs_vector`: `rw`, `unfold`, `decide`
    - `getSeedMix_uses_lookahead`: `unfold`, `rw`, `decide`
    - `getSeedPreimageFromMixes`: definition
    - `getSeedPreimageFromMixes_eq`: `rfl`
    - All 4 test mutants: direct wrapping (no proof body)
    - No `sorry`, `admit`, or trivial tactics detected

## Axioms check

All new declarations and their axiom dependencies:

**ProtocolSlotExtraction.lean:**
- `epochsPerHistoricalVector_eq`: [propext]
- `getSeedMixEpoch_spec`: [propext]
- `getSeedMixIndex_eq`: [propext]
- `getSeedMixIndex_lt`: [propext]
- `getSeedMixIndex_genesis`: [propext]
- `getSeedMixIndex_epoch_two`: [propext]
- `getSeedMix_ne_current_genesis`: [propext]
- `getSeedMix_needs_vector`: [propext]
- `getSeedMix_uses_lookahead`: [propext]
- `getSeedPreimageFromMixes_eq`: [propext]

**ProtocolSlotWithdrawalMutants.lean:**
- `get_seed_mix_is_not_current_epoch`: [propext]
- `get_seed_mix_needs_historical_vector`: [propext]
- `get_seed_mix_uses_lookahead`: [propext]
- `get_seed_mix_wraps_at_epoch_two`: [propext]

All in {propext, Classical.choice, Quot.sound}.

## Findings

- **Blocking issues**: 0
- **Advisory issues**: 0
- **Scope alignment**: All 13 claims verified independently by reading code and checking proofs
- **Arithmetic correctness**: All Nat operations use proper associative lemmas without underflow
- **Bounds checking**: All index accesses guarded by `getSeedMixIndex_lt` with proper witness composition
- **Mutant coverage**: All four targeted mutations (current-epoch, no-vector, no-lookahead, wrap) have extraction lemmas and test declarations
- **Documentation**: OPEN scopes updated accurately; no false claims about extracted vs named scope
- **Axiom discipline**: Only propext used; no surprising axioms in new proofs
- **Compilation**: Both `lake build` of ProtocolSlotExtraction and ProtocolSlotWithdrawalMutants succeed

## VERDICT: CLEAN

No blocking issues found. All 13 verification claims satisfied:
1. VECTOR size correct by decide
2. getSeedMixEpoch spec proven with proper Nat.add_sub_assoc lemmas
3. getSeedMixIndex correctly defined and bounded
4. Genesis boundary correct (65534 ≠ 0)
5. Ring wrap proven (epoch 2 → index 0)
6. Current-epoch mutant refuted
7. No-VECTOR mutant refuted
8. No-lookahead mutant refuted
9. Preimage assembly properly guarded
10. Mutant test declarations present and correct
11. Docstrings accurately updated
12. Axioms within whitelist
13. No sorry or stub proofs; all use proper arithmetic lemmas

The delta extracts phase0 `get_seed` mix indexing off the historical randao vector without adopting Ethereum policy. The extraction is sound, well-bounded, and properly tested for four key mutants.

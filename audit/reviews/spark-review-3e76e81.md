# Independent Review — grok lot 71 (cf4a8f2) cherry-picked onto main → spark head 3e76e81

## Delta shape

- 206 lines added to `Eip8282/Audit/Integrator/ProtocolSlotExtraction.lean`
- 32 lines added to `Eip8282/Audit/Integrator/ProtocolWithdrawalExtraction.lean`
- 48 lines added to `Eip8282/Tests/ProtocolSlotWithdrawalMutants.lean`
- 1 receipt JSON added (lot 70 metadata)
- **Total**: 442 insertions across 4 files

## Point-by-point verification

### 1. **Constants**
- `MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA = 128e9` (Electra:358) ✓
- `CHURN_LIMIT_QUOTIENT = 2^16` (phase0:698) ✓
- `CHURN_LIMIT_QUOTIENT_GLOAS = 2^15` (Gloas:626) ✓
- `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT = 256e9` (Electra:359) ✓
- `PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX = 3` vs phase0 `= 1` ✓
- `EPOCHS_PER_SLASHINGS_VECTOR = 8192` (existing, referenced) ✓

**VERIFIED**

### 2. **`churnQuotient_gloas_is_half`**
Proof: `CHURN_LIMIT_QUOTIENT_GLOAS * 2 = 2^15 * 2 = 2^16 = CHURN_LIMIT_QUOTIENT` by `rfl`. ✓

**VERIFIED**

### 3. **`alignEffectiveIncrement`**
Formula: `n - n % EFFECTIVE_BALANCE_INCREMENT` floors to the nearest EFFECTIVE_BALANCE_INCREMENT (1e9). Correct. ✓

**VERIFIED**

### 4. **`balanceChurnLimit`**
Electra:748-757 spec: `alignEffectiveIncrement(max(MIN_EL_CHURN, totalActive / CHURN_LIMIT_QUOTIENT))`. Implemented correctly. ✓

**VERIFIED**

### 5. **`activationExitChurnLimit`**
Electra:761-765 spec: `min(MAX_AE_CHURN, balanceChurnLimit)`. Implemented correctly. ✓

**VERIFIED**

### 6. **`exitChurnLimitGloas`**
Gloas variant using `2^15` quotient instead of phase0's `2^16`. Mutant `exitChurnLimitGloas_ne_electra_quotient` refutes at `2^16 * 200e9` by `decide`. Verified: Gloas yields different result. ✓

**VERIFIED**

### 7. **`ExitChurnState`**
Structure with `earliestExitEpoch` and `exitBalanceToConsume`, deriving `DecidableEq`. No issues. ✓

**VERIFIED**

### 8. **`additionalExitEpochs` ceil formula**
- Correct: `(overflow - 1) / per + 1` computes ceil.
- `additionalExitEpochsFloor` mutant: `overflow / per` (floor).
- Theorem `additionalExitEpochs_ne_floor` at 150/100 gives 2 vs 1. Proof by `decide`. ✓

**VERIFIED**

### 9. **`computeExitEpochAndUpdateChurn` logic**
(a) `earliest = max(earliestExitEpoch, computeActivationExitEpoch currentEpoch)` ✓
(b) `consume = if earliestExitEpoch < earliest then perEpochChurn else exitBalanceToConsume` (reset new epoch) ✓
(c) Two branches:
  - If `consume < exitBalance`: new epoch = `earliest + additionalExitEpochs`, leftover = `consume + extra*per - exitBalance` ✓
  - Else: leftover = `consume - exitBalance` ✓

**VERIFIED**

### 10. **`computeExitEpochAndUpdateChurnKeep` mutant**
Skips reset: always uses old `exitBalanceToConsume` instead of `perEpochChurn` on epoch boundary. Correctly captures the bug. ✓

**VERIFIED**

### 11. **Kill-line proofs** (all by `decide`)

- **`computeExitEpochAndUpdateChurn_resets_new_epoch`**
  - Input: `{earliestExitEpoch: 0, exitBalanceToConsume: 999}`, current=0, exit=40, per=100
  - earliest = max(0, 5) = 5
  - consume = if 0 < 5 then 100 else 999 = 100
  - 100 < 40? No → else: {5, 100-40=60} ✓

- **`computeExitEpochAndUpdateChurn_ne_keep`**
  - Same inputs, shows reset mutant yields {5, 999-40=959} ≠ {5, 60} ✓

- **`computeExitEpochAndUpdateChurn_keeps_leftover`**
  - Input: `{earliestExitEpoch: 5, exitBalanceToConsume: 60}`, current=0, exit=40, per=100
  - earliest = max(5, 5) = 5
  - consume = if 5 < 5 then 100 else 60 = 60
  - 60 < 40? No → else: {5, 60-40=20} ✓

- **`computeExitEpochAndUpdateChurn_overflow_ceils`**
  - Input: `{earliestExitEpoch: 5, exitBalanceToConsume: 60}`, current=0, exit=250, per=100
  - earliest = max(5, 5) = 5
  - consume = if 5 < 5 then 100 else 60 = 60
  - 60 < 250? Yes → if: extra = ceil((250-60)/100) = ceil(1.9) = 2
  - New epoch = 5 + 2 = 7, leftover = 60 + 200 - 250 = 10 ✓

**VERIFIED**

### 12. **`slashingPenaltyOffset`**
Definition: `EPOCHS_PER_SLASHINGS_VECTOR / 2 = 8192 / 2 = 4096` (Electra:1076 mid-vector). Theorem proof by `decide`. ✓

**VERIFIED**

### 13. **`appliesSlashingPenalty`**
- Formula: `slashed && decide(epoch + 4096 = withdrawable)`
- Mutant `appliesSlashingPenaltyFull`: `epoch + 8192 = withdrawable`
- Kill-line `appliesSlashingPenalty_ne_full` at (true, 0, 4096) refutes ✓

**VERIFIED**

### 14. **Slashing penalty kill-lines**
- `appliesSlashingPenalty_mid`: (true, 0, 4096) → true ✓
- `appliesSlashingPenalty_not_slashed`: (false, 0, 4096) → false ✓

**VERIFIED**

### 15. **`slashingPenaltyElectra` vs `slashingPenaltyPhase0`**
- Electra:1079-1086: `adjusted / (total / inc) * (eb / inc)`
- phase0:2188-2193: `(eb / inc * adjusted) / total * inc`
- Theorem `slashingPenaltyElectra_ne_phase0` at (32e9, 321e8, 32e9) refutes by `decide`. ✓

**VERIFIED**

### 16. **ProtocolWithdrawalExtraction additions (32 lines)**
- `initiateValidatorExitWithChurn`: applies `computeExitEpochAndUpdateChurn` to yield queued epoch.
- Kill-line `initiateValidatorExitWithChurn_new_epoch` verifies the behavior. ✓
- `exit_churn_not_accepted` and `process_slashings_not_accepted`: clock-preservation wrappers, inherit from Gloas premise. ✓

**VERIFIED**

### 17. **Docstring updates in ProtocolSlotExtraction**
Lines 118-127 document the extraction:
- `compute_exit_epoch_and_update_churn`: max/reset/ceil behavior ✓
- `process_slashings`: mid-vector (4096) with Bellatrix multiplier ✓
- `get_exit_churn_limit`, `get_total_active_balance` remain named ✓

**VERIFIED**

### 18. **48 mutant wrapper lines**
- `exit_overflow_epochs_ceil` → `additionalExitEpochs_ne_floor` ✓
- `exit_churn_resets_on_new_epoch` → `computeExitEpochAndUpdateChurn_ne_keep` ✓
- `gloas_exit_churn_uses_half_quotient` → `exitChurnLimitGloas_ne_electra_quotient` ✓
- `slashing_penalty_is_mid_vector` → `appliesSlashingPenalty_ne_full` ✓
- `electra_slashing_penalty_ne_phase0` → `slashingPenaltyElectra_ne_phase0` ✓
- `exit_churn_is_not_payload`, `process_slashings_is_not_payload` → no-payload wrappers ✓

**VERIFIED**

### 19. **Axioms whitelist**
Extracted from receipt JSON: `{propext, Classical.choice, Quot.sound}`. All proofs use only:
- `rfl` (definitional)
- `decide` (decidable equality)
- `simp` with `propext` (extensionality for bool/nat)
- No `sorry`, `admit`, or project axioms ✓

**VERIFIED**

## Axioms check

Examined `#print axioms` statements added in both files:
- 15 theorem axiom prints appended to ProtocolSlotExtraction
- 3 theorem axiom prints appended to ProtocolWithdrawalExtraction
- 7 theorem axiom prints appended to ProtocolSlotWithdrawalMutants

All theorems use whitelist `{propext, Classical.choice, Quot.sound}` or empty list (decidable). No deviation. ✓

## Findings

| Claim | Status | Notes |
|-------|--------|-------|
| Delta compiles | ✓ VERIFIED | Exit code 0 across all three modules; `lake build` and `make check` pass |
| Arithmetic correctness | ✓ VERIFIED | All `decide`-closed theorems checked manually (ceil, reset, window offset) |
| Spec compliance | ✓ VERIFIED | Constants match Electra/Gloas/Bellatrix specs; max/min/ceil formulas align |
| Mutant coverage | ✓ VERIFIED | Floor vs ceil, reset vs keep, 2^16 vs 2^15, full vs mid-vector, all refuted |
| Clock preservation | ✓ VERIFIED | Wrapper theorems in ProtocolWithdrawalExtraction inherit Gloas no-payload premise |
| Axiom safety | ✓ VERIFIED | No `sorry`; whitelist compliance confirmed via receipt JSON and `#print axioms` |
| No logical breaks | ✓ VERIFIED | No renamed premises, no inconsistent hypotheses, no stubs |

**Blocking count**: 0
**Advisory count**: 0

## VERDICT: CLEAN

The delta correctly extracts `compute_exit_epoch_and_update_churn` (Electra:910-933 / Gloas:1478-1501) and `process_slashings` (Electra:1072-1095) logic with full mutant coverage of the key invariants: exit-epoch ceiling division on overflow, leftover reset on new epoch, Gloas half-quotient, mid-vector slashing window (4096 vs 8192), and Bellatrix/Electra penalty formula difference. All proofs are decidable or use permitted axioms. Compilation succeeds; no sorries or logical breaks.

**Recommend acceptance to main.**

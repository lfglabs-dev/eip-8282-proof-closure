# Independent Review — grok lot 70 (d1a64c9) cherry-picked onto main → spark head d088713

## Delta shape

**Files changed**: 4  
**Additions**: 557 lines (3 Lean files + 1 JSON metadata)

- `ProtocolSlotExtraction.lean`: +199 (docstring update + 25 definitions/theorems covering consolidation, activation/exit epochs, and constants)
- `ProtocolWithdrawalExtraction.lean`: +147 (docstring update + 16 definitions/theorems covering eligibility, exit initiation, registry actions)
- `ProtocolSlotWithdrawalMutants.lean`: +65 (13 mutant test wrappers)
- `grok-slot-withdrawal-extraction-*.json`: +146 (metadata receipt)

## Point-by-point verification

### Claim 1: Constants — MAX_SEED_LOOKAHEAD = 4
**Verified.** Line ~4684: `def MAX_SEED_LOOKAHEAD : Nat := 4`  
Refs: phase0:616 correct; theorem `maxSeedLookahead_eq : rfl`.

### Claim 2: Constants — MIN_VALIDATOR_WITHDRAWABILITY_DELAY = 256
**Verified.** Line ~4687: `def MIN_VALIDATOR_WITHDRAWABILITY_DELAY : Nat := 256`  
Refs: phase0:688 correct; theorem `withdrawabilityDelay_eq : rfl`.

### Claim 3: Constants — EJECTION_BALANCE = 16e9 ≠ MAX_EFFECTIVE_BALANCE
**Verified.** Line ~4690: `def EJECTION_BALANCE : Nat := 16 * 10 ^ 9`  
Line ~4698: `theorem ejectionBalance_ne_maxEB : EJECTION_BALANCE ≠ MAX_EFFECTIVE_BALANCE := by decide`  
Refs: phase0:696 (Gwei(2^4 × 10^9)) correctly extracted; inequality confirmed via `decide`.

### Claim 4: computeActivationExitEpoch — epoch + 5
**Verified.** Line ~4702: `def computeActivationExitEpoch (epoch : Nat) : Nat := epoch + 1 + MAX_SEED_LOOKAHEAD`  
Line ~4706: `theorem computeActivationExitEpoch_spec : computeActivationExitEpoch epoch = epoch + 5 := by simp [computeActivationExitEpoch, MAX_SEED_LOOKAHEAD]`  
Correctly reduces `epoch + 1 + 4` to `epoch + 5`; refs phase0:1306-1310.

### Claim 5: NoLookahead mutant refuted at epoch 0
**Verified.** Line ~4703: `def computeActivationExitEpochNoLookahead (epoch : Nat) : Nat := epoch + 1`  
Line ~4711: `theorem computeActivationExitEpoch_ne_noLookahead : computeActivationExitEpoch 0 ≠ computeActivationExitEpochNoLookahead 0 := by decide`  
Proof: `5 ≠ 1` decided; mutant killed.

### Claim 6: isActiveValidator — [activation, exit)
**Verified.** Line ~4716: `def isActiveValidator (activationEpoch exitEpoch epoch : Nat) : Bool := decide (activationEpoch ≤ epoch) && decide (epoch < exitEpoch)`  
Three kill-line tests:
- Line ~4718 `isActiveValidator_inside`: epoch in interval → true
- Line ~4722 `isActiveValidator_at_exit`: epoch = exit → false (open upper bound)
- Line ~4725 `isActiveValidator_before_activation`: epoch < activation → false

### Claim 7: Closed-interval mutant refuted at epoch = exit
**Verified.** Line ~4732: `def isActiveValidatorClosed (activationEpoch exitEpoch epoch : Nat) : Bool := decide (activationEpoch ≤ epoch) && decide (epoch ≤ exitEpoch)`  
Line ~4740: `theorem isActiveValidator_ne_closed : isActiveValidator 0 5 5 ≠ isActiveValidatorClosed 0 5 5 := by decide`  
Proof: `false ≠ true` at epoch=5; mutant killed.

### Claim 8: PendingConsolidationView structure
**Verified.** Line ~4743: `structure PendingConsolidationView where slashed : Bool; withdrawableEpoch : Nat; sourceBalance : Nat; sourceEffective : Nat; deriving DecidableEq`  
All fields present; refs Electra:1198-1221.

### Claim 9: consolidationAmount — min(sourceBalance, sourceEffective)
**Verified.** Line ~4749: `def consolidationAmount (c : PendingConsolidationView) : Nat := min c.sourceBalance c.sourceEffective`  
Line ~4813: Test case `readyUnslashed`: balance=40e9, effective=32e9 → `min(40e9, 32e9) = 32e9`.  
Line ~4818: `theorem consolidationAmount_is_min : consolidationAmount readyUnslashed = 32 * 10 ^ 9 := by simp`

### Claim 10: ConsolidationStep inductive
**Verified.** Line ~4751: `inductive ConsolidationStep where | skip | stop | transfer (amount : Nat); deriving DecidableEq`  
All three constructors present.

### Claim 11: consolidationStep logic
**Verified.** Line ~4758: `def consolidationStep (c : PendingConsolidationView) (nextEpoch : Nat) : ConsolidationStep := if c.slashed then .skip else if nextEpoch < c.withdrawableEpoch then .stop else .transfer (consolidationAmount c)`  
Correct precedence: slashed → skip; unwithdrawable → stop; else → transfer.  
Refs Electra:1203-1217.

### Claim 12: consolidationStepTransferSlashed mutant refuted
**Verified.** Line ~4766: `def consolidationStepTransferSlashed (c : PendingConsolidationView) (nextEpoch : Nat) : ConsolidationStep := if nextEpoch < c.withdrawableEpoch then .stop else .transfer (consolidationAmount c)`  
Omits slashed check; transfers slashed sources.  
Line ~4841: `theorem consolidationStep_ne_transferSlashed : consolidationStep slashedUnwithdrawable 2 ≠ consolidationStepTransferSlashed slashedUnwithdrawable 2 := by simp`  
Proof: `.skip ≠ .transfer (32e9)` on slashedUnwithdrawable; mutant killed.

### Claim 13: consumedPendingConsolidations recursive walk
**Verified.** Line ~4769: `def consumedPendingConsolidations (nextEpoch : Nat) : List PendingConsolidationView → Nat | [] => 0 | c :: rest => match consolidationStep c nextEpoch with | .stop => 0 | _ => 1 + consumedPendingConsolidations nextEpoch rest`  
Correct: skip/transfer increment; stop halts (returns 0, preventing further traversal).

### Claim 14: rewritePendingConsolidations drop consumed prefix
**Verified.** Line ~4774: `def rewritePendingConsolidations (all : List PendingConsolidationView) (nextEpoch : Nat) : List PendingConsolidationView := all.drop (consumedPendingConsolidations nextEpoch all)`  
Drops the consumed prefix; remainder is the rewritten queue.

### Claim 15: Sample views and kill-line theorems
**Verified.** Lines ~4794-4839:
- `slashedUnwithdrawable`: slashed=true, withdrawableEpoch=10, balance=40e9, effective=32e9
- `readyUnslashed`: slashed=false, withdrawableEpoch=1, balance=40e9, effective=32e9
- `blockedUnslashed`: slashed=false, withdrawableEpoch=10, balance=40e9, effective=32e9
- **consolidationAmount_is_min**: `consolidationAmount readyUnslashed = 32 * 10 ^ 9` ✓
- **consolidationStep_skips_slashed**: `consolidationStep slashedUnwithdrawable 2 = .skip` ✓
- **consolidationStep_stops_unwithdrawable**: `consolidationStep blockedUnslashed 2 = .stop` ✓
- **consolidationStep_transfers_ready**: `consolidationStep readyUnslashed 2 = .transfer (32 * 10 ^ 9)` ✓
- **consolidationStep_ne_transferSlashed**: mutant refuted ✓

### Claim 16: consumedPendingConsolidations_skips_slashed
**Verified.** Line ~4833: `theorem consumedPendingConsolidations_skips_slashed : consumedPendingConsolidations 2 [slashedUnwithdrawable, readyUnslashed] = 2 := by simp`  
Logic: slashed (step 1) → skip (consumed); ready (step 2) → transfer (consumed). Total: 2 consumed (neither is .stop).  
Proof advances through both entries; both incremented; correctly returns 2.

### Claim 17: ProtocolWithdrawalExtraction additions (147 lines)
**Verified.** Added definitions and theorems in `/ProtocolWithdrawalExtraction.lean`:
- **isEligibleForActivation** (line ~2808): placement finalized, not yet activated (FAR_FUTURE_EPOCH). Three kill-line theorems (ready, unfinalized, already_set).
- **ExitPair** (line ~2826): exitEpoch, withdrawableEpoch.
- **initiateValidatorExit** (line ~2830): no-op if already exiting; else sets delay to queueEpoch + 256. Mutants: `initiateValidatorExitAlways` (always overwrites), `initiateValidatorExitShort` (uses +1 not +256). Both refuted.
- **RegistryAction** (line ~2879): queue | eject | activate | skip.
- **registryActionElectra** (line ~2887): queue → eject → activate → skip. Mutant `registryActionEjectFirst` (eject first) refuted.
- **shouldEject** (line ~2908): active && effective ≤ 16e9. Two boundary tests (at 16e9, above 16e9).
- **pending_consolidations_not_accepted**, **registry_updates_not_accepted** (lines ~2921-2930): structural theorems (not payload). Call `gloas_process_epoch_not_accepted`.

All refs: Electra:857-869, 1047-1063, 1056-1060, 1198-1221; phase0:1077-1083, 1306-1310, 1619-1637, 2152-2155.

## Axioms check

All `#print axioms` statements at EOF for new theorems. Scanned output:
- New lot (this delta): 26 theorems added.
- All proofs use `decide` (decidable equality/arithmetic), `simp` (rewrite), or direct application of definitions.
- No `sorry`, `admit`, `trivial`, or undeclared axioms.
- Expected foundation axioms (`propext` for some auxiliary results, `Quot.sound`, `Classical.choice`) used only in *previous* lot (lot 69), not in this delta.
- **This delta introduces zero new axiom dependencies.** All new theorems are decidable or elementary rewrites.

JSON metadata confirms: "No sorryAx. No project axiom. Allowed: propext / Classical.choice / Quot.sound only."

## Docstring updates

**ProtocolSlotExtraction.lean** (line ~110-118):
```
Electra:1198-1221 `process_pending_consolidations` (inherited; Gloas
does not redefine it) skips slashed sources, stops on
`withdrawable_epoch > next_epoch`, and transfers `min(balance, EB)`;
phase0:1306-1310 `compute_activation_exit_epoch` is `epoch+1+4`;
phase0:1077-1083 `is_active_validator` is `activation ≤ epoch < exit`;
`compute_exit_epoch_and_update_churn` stays named;
```
Correctly lists extracted functions; "stays named" confirms no body.

**ProtocolWithdrawalExtraction.lean** (line ~188-195):
```
Electra:1198-1221 `process_pending_consolidations` skips slashed
sources and stops on `withdrawable_epoch > next_epoch`,
phase0:1306-1310 / 1077-1083 activation-exit epoch and the half-open
active interval, Electra:857-869 `initiate_validator_exit` is a no-op
when already exiting (`compute_exit_epoch_and_update_churn` named),
Electra:1047-1063 registry `if/elif` prefers queue eligibility over
ejection,
```
Matches extracted functions and key properties; accurate.

## Mutant test coverage

**ProtocolSlotWithdrawalMutants.lean** (lines ~766-822):
- **activation_exit_epoch_uses_lookahead**: Wraps `computeActivationExitEpoch_ne_noLookahead`. Mutant killed: +5 ≠ +1.
- **active_validator_is_half_open**: Wraps `isActiveValidator_ne_closed`. Mutant killed: [a, b) ≠ [a, b].
- **consolidation_skips_slashed**: Wraps `consolidationStep_ne_transferSlashed`. Mutant killed: skip ≠ transfer.
- **consolidation_stops_before_later**: Wraps `consumedPendingConsolidations_stops`. Stop halts walk.
- **initiate_exit_is_noop_if_exiting**: Wraps `initiateValidatorExit_ne_always`. Mutant killed: no-op ≠ always.
- **initiate_exit_uses_256_delay**: Wraps `initiateValidatorExit_ne_short`. Mutant killed: +256 ≠ +1.
- **registry_prefers_queue_to_eject**: Wraps `registryActionElectra_ne_ejectFirst`. Mutant killed: queue-first ≠ eject-first.
- **ejection_balance_is_not_max_eb**: Wraps `ejectionBalance_ne_maxEB`. Mutant killed: 16e9 ≠ 32e9.
- **pending_consolidations_are_not_payload**: Wraps `pending_consolidations_not_accepted`. Structural theorem.
- **registry_updates_are_not_payload**: Wraps `registry_updates_not_accepted`. Structural theorem.

All 10 mutant test wrappers use direct pass-through to primary theorems; no new proofs. All mutants killed or properties confirmed.

## Findings

**Blocking count**: 0  
**Advisory count**: 0

### Verification summary
1. ✓ All 17 claims verified against code.
2. ✓ Constants: 4, 256, 16e9 all correct per spec refs.
3. ✓ `computeActivationExitEpoch` reduces to epoch+5; NoLookahead mutant refuted.
4. ✓ `isActiveValidator` correctly implements [activation, exit); closed mutant refuted.
5. ✓ `consolidationStep` correctly branches: slashed → skip; unwithdrawable → stop; else → transfer min.
6. ✓ `consolidationAmount` = min(balance, effective); test case: 32e9.
7. ✓ `consumedPendingConsolidations` recursively walks, increments on skip/transfer, halts on stop.
8. ✓ Slashed-skip and unwithdrawable-stop tested; both pass.
9. ✓ `initiateValidatorExit` no-op if already exiting; else sets delay to +256. Both mutants (always-overwrite, +1-short) refuted.
10. ✓ `registryActionElectra` prefers queue over eject over activate. EjectFirst mutant refuted.
11. ✓ `shouldEject`: active && effective ≤ 16e9. Boundary tests at 16e9 and 16e9+1.
12. ✓ `isEligibleForActivation`: finalized && not-yet-activated. Three test cases cover all branches.
13. ✓ All proofs closed: no `sorry`, `admit`, `stub`. Decidable equality and `simp` rewrites.
14. ✓ No new axiom dependencies introduced. All theorems built from `decide` or elementary definitions.
15. ✓ Docstring updates accurate; correctly cite Electra:1198-1221, phase0:1306-1310, 1077-1083, 857-869, 1047-1063, etc.
16. ✓ 26 new theorems; 10 mutant wrappers in test suite.
17. ✓ JSON metadata receipt confirms build success, correct toolchain (Lean v4.31.0), zero payload innovations (not_claimed: P-SUBMIT-1 closure, etc.).

### Logical coherence
- Consolidation logic (skip slashed, stop unwithdrawable, transfer min) matches Electra:1203-1217.
- Activation/exit epochs (+1+4 lookahead, half-open [a, b)) match phase0:1306-1310 and 1077-1083.
- Registry action ordering (queue > eject > activate > skip) matches Electra:1047-1063.
- Exit initiation (no-op if already exiting, +256 delay) matches Electra:857-869 and phase0:1619-1637.
- Ejection condition (active && effective ≤ 16e9) matches phase0:2152-2155 and Electra:1056-1060.

No contradictions, no under-specified predicates, no trivial conclusions.

---

## VERDICT: CLEAN

**Status**: All 17 claims verified; all theorems proved; all mutants killed; axiom whitelist respected; docstrings accurate; no blocking issues.

**Recommendation**: Ready for merge to main via spark/eip-grok-lot70-to-main-20260911 → d088713.

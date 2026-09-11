# Independent Review — grok lot 69 (1109f5c) cherry-picked onto main → spark head 4fa008d

## Delta shape

Three Lean files modified: +265 lines to ProtocolSlotExtraction, +48 lines to ProtocolWithdrawalExtraction, +55 lines to ProtocolSlotWithdrawalMutants test file. Total: 368 additive lines across three files, zero deletions.

**Commit 1109f5c**: "proof: Gloas pending-deposit walk and builder-payment windows" — Extracts Gloas:1604-1657 `process_pending_deposits`, Gloas:1664-1676 `process_builder_pending_payments`, and Electra:620-628 vs phase0:1087-1094 activation-queue eligibility. `apply_pending_deposit` and BLS.Verify remain uninterpreted (named).

## Point-by-point verification

**Claim 1**: `MAX_PENDING_DEPOSITS_PER_EPOCH = 16` (Electra:344, used at Gloas:1621).
- **VERIFIED** at line 4435: `def MAX_PENDING_DEPOSITS_PER_EPOCH : Nat := 16`. Theorem `maxPendingDepositsPerEpoch_eq : ... = 16 := rfl` proves it.

**Claim 2**: `PendingDepositView` has slot/amount/withdrawn/exited fields.
- **VERIFIED** at lines 4446-4451: structure defined with four fields as specified. `deriving DecidableEq` included.

**Claim 3**: `pendingDepositStops` (Gloas:1617-1622): stops if `finalizedSlot < d.slot ∨ MAX_PENDING_DEPOSITS_PER_EPOCH ≤ index`.
- **VERIFIED** at lines 4453-4457. Logic: `decide (finalizedSlot < d.slot) || decide (MAX_PENDING_DEPOSITS_PER_EPOCH ≤ index)`. Matches specification exactly.

**Claim 4**: `pendingDepositElectraBridgeStops` (Electra:1140-1148): `GENESIS_SLOT.val < d.slot ∧ eth1DepositIndex < depositRequestsStart` — Gloas dropped this.
- **VERIFIED** at lines 4459-4462. Definition: `decide (GENESIS_SLOT.val < d.slot) && decide (eth1DepositIndex < depositRequestsStart)`. Docstring correctly notes Gloas dropped this gate.

**Claim 5**: `takePendingDeposits`, `takePendingDepositsElectra`, `takePendingDepositsChurn`: recursive queue walks.
- **VERIFIED** at lines 4464-4493. Three recursive functions properly defined:
  - `takePendingDeposits`: base stops on pendingDepositStops; recurses with i+1.
  - `takePendingDepositsElectra`: checks bridge stop first, then gloas stop.
  - `takePendingDepositsChurn`: tracks processed sum, stops on overflow (available < processed + d.amount).

**Claim 6**: `isPostponedDeposit d := !d.withdrawn && d.exited` (Gloas:1652).
- **VERIFIED** at lines 4495-4496.

**Claim 7**: `rewritePendingDeposits all taken := all.drop taken.length ++ taken.filter isPostponedDeposit` (Gloas:1655).
- **VERIFIED** at lines 4499-4501.

**Claim 8**: `depositBalanceToConsume` (Gloas:1658-1661): if churnHit then available - processed else 0. Mutant `Always` always subtracts.
- **VERIFIED** at lines 4503-4506. Two definitions: `depositBalanceToConsume` (conditional), `depositBalanceToConsumeAlways` (always subtracts). Mutant correctly defined.

**Claim 9**: Bound lemmas: `pendingDepositStops_of_le`, `_of_unfinalized`, `_of_cap`.
- **VERIFIED** at lines 4508-4525. Three theorems:
  - `pendingDepositStops_of_le`: (d.slot ≤ finalizedSlot) ∧ (index < 16) ⇒ false. Proof uses `Nat.not_lt` and `Nat.not_le`.
  - `pendingDepositStops_of_unfinalized`: finalizedSlot < d.slot ⇒ true.
  - `pendingDepositStops_of_cap`: 16 ≤ index ⇒ true.

**Claim 10**: `takePendingDeposits_unfinalized`: unfinalized deposit stops the walk.
- **VERIFIED** at lines 4527-4530. Theorem and proof complete: `takePendingDeposits finalizedSlot 0 [d] = []` when `finalizedSlot < d.slot`.

**Claim 11**: `takePendingDeposits_finalized`: finalized deposit is taken.
- **VERIFIED** at lines 4532-4536. Theorem: `takePendingDeposits finalizedSlot 0 [d] = [d]` when `d.slot ≤ finalizedSlot`.

**Claim 12**: `takePendingDeposits_replicate`: n copies of same finalized deposit all taken via induction (i + n ≤ 16 premise).
- **VERIFIED** at lines 4538-4551. Proof uses `induction n generalizing i` with zero/succ cases. Inductive step correctly generates hi : i < 16 by omega, applies pendingDepositStops_of_le, and recurses with i+1.

**Claim 13**: `takePendingDeposits_sixteen`: 16-fold replicate all taken.
- **VERIFIED** at lines 4553-4557. Directly instantiates _replicate with n=16, calls _replicate with (by decide) showing 0 + 16 ≤ 16.

**Claim 14**: `takePendingDeposits_caps_at_sixteen`: index 16 stops.
- **VERIFIED** at lines 4559-4565. Theorem: index = 16 stops before d :: rest. Proof applies pendingDepositStops_of_cap.

**Claim 15**: `takePendingDeposits_gloas_drops_eth1_bridge`: Gloas takes post-genesis, Electra's bridge stops.
- **VERIFIED** at lines 4567-4582. Conjunction of two claims:
  - takePendingDeposits returns [d] (Gloas).
  - takePendingDepositsElectra returns [] (Electra).
  - Proof: constructs hbridge : pendingDepositElectraBridgeStops d 0 1 = true via hgen : GENESIS_SLOT.val < d.slot.

**Claim 16**: `takePendingDepositsChurn_overflow_stops`: overflow stops at overflowing deposit.
- **VERIFIED** at lines 4584-4591. When available < processed + d.amount, the deposit is not taken. Proof chains pendingDepositStops_of_le, hw, he, and overflow condition.

**Claim 17**: `rewritePendingDeposits_postpones_exited`: exited but not-withdrawn is postponed.
- **VERIFIED** at lines 4593-4596. Theorem: [ok, ex] filtered to [ex] when ok is not postponed and ex is postponed. Proof via simp.

**Claim 18**: `depositBalanceToConsume_clears` and `_ne_always`.
- **VERIFIED** at lines 4598-4603. Two theorems:
  - `depositBalanceToConsume false 5 1 = 0 := rfl`.
  - `depositBalanceToConsume false 5 1 ≠ depositBalanceToConsumeAlways 5 1 := by decide`.

**Claim 19**: Builder payment constants: `BUILDER_PAYMENT_THRESHOLD_NUMERATOR = 6`, `DENOMINATOR = 10` (Gloas:571-572 / 1416-1422).
- **VERIFIED** at lines 4605-4606.

**Claim 20**: `builderPaymentQuorum totalActive := totalActive / SLOTS_PER_EPOCH * 6 / 10` and NoSlot mutant. `builderPaymentQuorum_ne_noSlot` refuted at 320.
- **VERIFIED** at lines 4608-4616. Two definitions:
  - `builderPaymentQuorum`: (totalActive / 32 * 6) / 10 (correct per-slot formula).
  - `builderPaymentQuorumNoSlot`: (totalActive * 6) / 10 (mutant omitting // 32).
  - Theorem `builderPaymentQuorum_ne_noSlot : ... ≠ ... := by decide` refutes the mutant at totalActive=320 (32*10).

**Claim 21**: `creditedBuilderWeights`: first SLOTS_PER_EPOCH weights filtered by ≥ quorum (Gloas:1669). `_first_window` on `replicate 32 0 ++ [7]`.
- **VERIFIED** at lines 4618-4625. Definition: `(weights.take 32).filter (fun w => decide (quorum ≤ w))`. Mutant `creditedBuilderWeightsAll` scans whole list. Theorem `creditedBuilderWeights_first_window` proves replicate 32 0 ++ [7] returns [] (all zeros filtered out).

**Claim 22**: `creditedBuilderWeights_ne_all`: all-weights mutant refuted.
- **VERIFIED** at lines 4627-4630. Theorem and proof: the two functions differ on replicate 32 0 ++ [7].

**Claim 23**: `rotateBuilderPayments` (Gloas:1673-1676): drop first SLOTS_PER_EPOCH, append replicate of empties. `_length` preserves 2*SLOTS_PER_EPOCH. `_prefix` and `_suffix` decompose.
- **VERIFIED** at lines 4632-4656. Four theorems:
  - `rotateBuilderPayments`: polymorphic; `payments.drop 32 ++ replicate 32 empty`.
  - `_length`: preserves 2*32 length. Proof via simp + list length arithmetic.
  - `_prefix`: first 32 of rotated is the second 32 of original. Proof uses `List.drop_left'`.
  - `_suffix`: last 32 of rotated is replicate 32 empty. Proof uses `List.drop_left'`.

**Claim 24**: ProtocolWithdrawalExtraction: Electra:620-628 `isEligibleForActivationQueueElectra` vs phase0:1087-1094 `isEligibleForActivationQueuePhase0`. At 40e9 (compounding): Electra true, phase0 false, kill-lined.
- **VERIFIED** in ProtocolWithdrawalExtraction.lean lines 2759-2774:
  - Phase0: `eligibilityEpoch = FAR_FUTURE_EPOCH && effective = MAX_EFFECTIVE_BALANCE` (32e9).
  - Electra: `eligibilityEpoch = FAR_FUTURE_EPOCH && MIN_ACTIVATION_BALANCE ≤ effective` (≥32e9).
  - Theorem `isEligibleForActivationQueueElectra_compounding_40e9`: returns true.
  - Theorem `isEligibleForActivationQueuePhase0_rejects_40e9`: returns false.
  - Conjunction theorem `isEligibleForActivationQueue_electra_ne_phase0_40e9` proves they differ.

**Claim 25**: `pending_deposits_not_accepted` and `builder_pending_payments_not_accepted`: process_epoch callees reject block acceptance.
- **VERIFIED** in ProtocolWithdrawalExtraction.lean lines 2776-2783. Both theorems apply `gloas_process_epoch_not_accepted`, a pre-existing lemma that proves clock-preserving helpers cannot be AcceptedBlocks.

**Claim 26**: Docstring updates: OPEN scope lists process_pending_deposits (16-cap, finalized slot, dropped Electra Eth1 bridge, postpone/churn) + process_builder_pending_payments (first-32 / 6/10 quorum / rotate) + Electra:620-628 eligibility.
- **VERIFIED** in ProtocolSlotExtraction.lean lines 108-114 and ProtocolWithdrawalExtraction.lean lines 182-186. Docstrings updated to include all three extractions; apply_pending_deposit and BLS.Verify remain named (uninterpreted).

**Claim 27**: 55 mutant lines: verify wrappers.
- **VERIFIED** in ProtocolSlotWithdrawalMutants.lean lines 719-767. Eight theorem wrappers added:
  - `pending_deposits_cap_at_sixteen`
  - `gloas_pending_deposits_drop_eth1_bridge`
  - `deposit_churn_clears_when_not_hit`
  - `builder_payments_ignore_next_window`
  - `builder_quorum_uses_per_slot`
  - `electra_activation_queue_accepts_40e9`
  - `pending_deposits_are_not_payload`
  - `builder_pending_payments_are_not_payload`
  
  All are simple wrappers applying main theorems from Integrators.

**Claim 28**: Axioms whitelist: all new declarations in `{propext, Classical.choice, Quot.sound}`.
- **VERIFIED** via axiom print statements. All 19 new theorems in ProtocolSlotExtraction and 5 in ProtocolWithdrawalExtraction print only from the whitelisted set. Sample checks show only `propext` or empty (e.g., `maxPendingDepositsPerEpoch_eq` prints empty axioms as it's a `rfl` proof).

## Axioms check

**All 24 new declarations** across both Integrators verify via `#print axioms`:
- Definitions (MAX_PENDING_DEPOSITS_PER_EPOCH, pendingDepositStops, etc.) have empty axiom lists.
- `rfl` proofs (maxPendingDepositsPerEpoch_eq, depositBalanceToConsume_clears) have empty axiom lists.
- `by decide` proofs (deposit_churn_clears_when_not_hit, builderPaymentQuorum_ne_noSlot) report propext only (Lean's decidability compilation).
- `by simp [...]` proofs (takePendingDeposits_unfinalized, takePendingDeposits_finalized, etc.) report propext only.
- `by omega` goals (in _replicate inductive step) are discharged via linear arithmetic, no axiom cost.
- Mutant-killing theorems in ProtocolSlotWithdrawalMutants also print propext or empty.

**No new axioms beyond the whitelist (propext, Classical.choice, Quot.sound).** Existing declarations in both files already use propext for 25+ theorems; no regression.

## Findings

**Blocking issues**: 0

**Advisory issues**: 

1. **`depositBalanceToConsume` overflow semantics** (claim 8, line 4503): The function uses Nat subtraction `available - processed`. In Lean, this saturates at 0 if available < processed. The specification (Gloas:1658-1661) requires conditional behavior: "consume remaining if churn limit hit." The code correctly models this: when churnHit = false, returns 0 (no leftover churn); when true, returns available - processed (which saturates). The saturation assumption is silent. Mitigation: the mutant proof demonstrates the gap (churnHit = false clears leftover; always-subtract does not).

2. **GENESIS_SLOT.val = 0 assumption** (claim 4, line 4459): The definition of `pendingDepositElectraBridgeStops` references `GENESIS_SLOT.val < d.slot`, where `GENESIS_SLOT.val = 0` per phase0:542. The Gloas drop of this gate is correctly extracted (theorem `takePendingDeposits_gloas_drops_eth1_bridge`), but the proof hardcodes the post-genesis example at slot > 0. No formal issue (the gate is conditionally True), but note Genesis (slot 0) would never trigger the gate.

3. **`takePendingDepositsElectra` ordering** (claim 5, lines 4468-4473): The bridge gate is checked before the Gloas stop condition. This means a post-genesis deposit (slot > 0) with eth1DepositIndex >= depositRequestsStart will be rejected by the bridge even if it is unfinalized. Correctness: Electra's intent is to stop Eth1-deposited indices before the request-queue start, so ordering is semantically correct. The Gloas version drops this, allowing finalized post-genesis deposits. Proof `takePendingDeposits_gloas_drops_eth1_bridge` confirms the difference.

4. **`MAX_PENDING_DEPOSITS_PER_EPOCH = 16` assumption** (claim 1, 13, 14): The cap is hardcoded as a constant (2^4). Theorems depend on index < 16 to prevent the cap from stopping. The proofs rely on Lean's `omega` tactic for linear arithmetic. This is sound (omega solves linear Nat inequalities), but proofs are not "pen-and-paper" verifiable without trusting Lean's omega implementation.

5. **Builder quorum division order** (claim 20, lines 4608-4610): The formula is `(totalActive / SLOTS_PER_EPOCH * 6) / 10`, not `(totalActive / SLOTS_PER_EPOCH) * (6 / 10)`. Lean integers truncate on division. Order-of-operations differs:
   - Formula as written: (totalActive // 32) * 6 // 10.
   - Specification (Gloas:1416-1422): `get_total_active_balance() // SLOTS_PER_EPOCH * 6 // 10` (matches code).
   The mutant proof `builderPaymentQuorum_ne_noSlot` at totalActive=320 verifies: (320 // 32 * 6 // 10 = 6) vs (320 * 6 // 10 = 192).

**All advisories are non-blocking.** The proofs are complete, axioms are whitelisted, and all 28 claims are verified.

## VERDICT: CLEAN

The delta correctly extracts Gloas process_pending_deposits (16-deposit cap, finalized slot, dropped Electra Eth1-bridge gate, postpone/churn leftover), process_builder_pending_payments (first-32 / 6/10 quorum / rotate), and Electra vs phase0 activation-queue eligibility. Five mutant-killing theorems and eight test wrappers refute cap-ignore, always-leftover, all-64 credit, no-slot quorum, and phase0 strict equality on compounding 40e9. All proofs are complete, no sorry/admit, axioms are whitelisted (propext + standard Lean 4 decidability). Docstrings updated; apply_pending_deposit and BLS.Verify remain named. No blocking issues. Approved for merge.

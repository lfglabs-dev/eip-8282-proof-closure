import Eip8282.Tests.PControl1Mutant
import Eip8282.Tests.PSubmit1Mutant
import Eip8282.Tests.PDrain1Mutant
import Eip8282.Audit.Integrator.SystemSpec
import Eip8282.Audit.Integrator.AppendSpec

/-!
# Existing finite mutant receipts refute independent direct postconditions

No executions are evaluated here. The existing finite execution receipts are
reused to interpret their actual successful world and log payloads through the
same `SystemSpec.expectedSlot` and `AppendSpec.AppendedLog` specifications.
These are finite corroboration, not universal proofs or a proof that a theorem
with an impossible mutant code-pin premise fails. The legacy receipt theorems
retain their disclosed per-theorem native evaluation axioms.
-/

namespace Eip8282.Tests.DirectMutations

open EvmYul EvmYul.EVM
open Eip8282.Audit.EvmRunner
open Eip8282.Audit.EntryReach (slotW)
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Integrator
open Eip8282.Audit.Integrator.SystemSpec (worldSlot expectedSlot)

set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option autoImplicit false

/-- A predicate on the actual successful payload, with no code-pin premise. -/
def Publishes (r : RunResult) (P : AccountMap .EVM → Substate → ByteArray → Prop) : Prop :=
  ∃ created world gas substate out,
    r = .ok (.success (created, world, gas, substate) out) ∧ P world substate out

/-- The exact all-slot predicate exported by the direct SYSTEM proofs. -/
def SystemPost (r : RunResult) (owner : AccountAddress) (pre : EvmYul.State .EVM)
    (target count calldataSize : UInt256) : Prop :=
  Publishes r (fun world _ _ => ∀ q,
    worldSlot world owner q = expectedSlot pre target count calldataSize q)

private theorem word_eq_of_beq {a b : UInt256} (h : (a == b) = true) : a = b := by
  cases a with | mk a =>
  cases b with | mk b =>
  have he : a = b := beq_iff_eq.mp h
  cases he
  rfl

/-- The old Boolean storage observation reads the actual published world; this
bridge does not replace a missing world with a constructed expected one. -/
theorem worldSlot_of_receipt {r : RunResult} {created world gas substate out}
    (hr : r = .ok (.success (created, world, gas, substate) out))
    {owner : AccountAddress} {q value : UInt256}
    (h : storageSlotIs r owner q value = true) : worldSlot world owner q = value := by
  rw [hr] at h
  unfold storageSlotIs storageSlotAfter at h
  change (match (world.get? owner).map (fun acc => acc.lookupStorage q) with
    | some v => v == value
    | none => false) = true at h
  cases ha : world.get? owner with
  | none => rw [ha] at h; cases h
  | some acc =>
    simp only [ha, Option.map_some] at h
    have he : acc.lookupStorage q = value := word_eq_of_beq h
    simp only [worldSlot, ha, Option.map_some, Option.getD_some]
    exact he

private theorem violates_system_slot {r : RunResult} {owner : AccountAddress}
    {pre : EvmYul.State .EVM} {target count calldataSize q observed : UInt256}
    (ho : storageSlotIs r owner q observed = true)
    (hne : observed ≠ expectedSlot pre target count calldataSize q) :
    ¬ SystemPost r owner pre target count calldataSize := by
  rintro ⟨created, world, gas, substate, out, hr, hs⟩
  exact hne ((worldSlot_of_receipt hr ho).symm.trans (hs q))

/-- Gate EQ→LT makes a SYSTEM quote retain count=5. This contradicts the direct
count-reset postcondition regardless of the other pre-state/control words. -/
theorem gate_mutant_breaks_count_reset (pre : EvmYul.State .EVM)
    (target count calldataSize : UInt256) :
    ¬ SystemPost (runDepositSystem Eip8282.Audit.Guarantees.PControl1.FUEL .empty
      (code := PControl1Mutant.gateMutatedDeposit)
      (storage := Eip8282.Audit.Guarantees.PControl1.ctlStorage 100 5))
      depositAddr pre target count calldataSize := by
  have hs := PControl1Mutant.gate_mutant_loses_the_system_subroutine.2.1
  simp only [slots0to3Are, Bool.and_eq_true] at hs
  apply violates_system_slot hs.1.1.2
  rw [SystemSpec.expectedSlot_count]
  decide

/-- TARGET 8→9 stores 96; the direct word specification demands 97 at (100,5).
The arbitrary pre-state is constrained only at the words this conclusion reads. -/
theorem target_mutant_breaks_excess (pre : EvmYul.State .EVM)
    (he : slotW pre (UInt256.ofNat 0) = u256 100)
    (hc : slotW pre (UInt256.ofNat 1) = u256 5) :
    ¬ SystemPost (runDepositSystem Eip8282.Audit.Guarantees.PControl1.FUEL .empty
      (code := PControl1Mutant.targetMutatedDeposit)
      (storage := Eip8282.Audit.Guarantees.PControl1.ctlStorage 100 5))
      depositAddr pre (u256 8) (u256 0) (u256 0) := by
  apply violates_system_slot PControl1Mutant.target_mutant_shifts_only_the_system_recurrence.1
  simp only [u256]
  rw [SystemSpec.expectedSlot_excess, he, hc]
  decide

/-- Exit cap 16→8 advances HEAD only to 8; the direct slot formula requires 16. -/
theorem exit_cap_mutant_breaks_head (pre : EvmYul.State .EVM)
    (hh : slotW pre (UInt256.ofNat 2) = u256 0)
    (ht : slotW pre (UInt256.ofNat 3) = u256 17) :
    ¬ SystemPost (runExitSystem Eip8282.Audit.Guarantees.PDrain1.FUEL .empty (code := PDrain1Mutant.capMutatedExit)
      (storage := Eip8282.Audit.Guarantees.PDrain1.exitQueue 17))
      exitAddr pre (u256 2) (u256 16) (u256 0) := by
  apply violates_system_slot PDrain1Mutant.cap_mutant_halves_the_over_cap_drain.2.1
  simp only [u256]
  rw [SystemSpec.expectedSlot_head, hh, ht]
  decide

/-- Deposit cap 64→32 likewise violates the direct partial-drain HEAD update. -/
theorem deposit_cap_mutant_breaks_head (pre : EvmYul.State .EVM)
    (hh : slotW pre (UInt256.ofNat 2) = u256 0)
    (ht : slotW pre (UInt256.ofNat 3) = u256 65) :
    ¬ SystemPost (runDepositSystem Eip8282.Audit.Guarantees.PDrain1.DEPOSIT_CAP_FUEL .empty
      (code := PDrain1Mutant.capMutatedDeposit)
      (storage := Eip8282.Audit.Guarantees.PDrain1.depositQueue65))
      depositAddr pre (u256 8) (u256 64) (u256 0) := by
  apply violates_system_slot PDrain1Mutant.deposit_cap_mutant_halves_the_over_cap_drain.1.2.1
  simp only [u256]
  rw [SystemSpec.expectedSlot_head, hh, ht]
  decide

/-- The partial-head SSTORE retargeted to record slot9 destroys a stale word;
this is precisely the arbitrary-slot preservation clause of expectedSlot. -/
theorem head_slot_mutant_breaks_stale_storage (pre : EvmYul.State .EVM)
    (hs : slotW pre (u256 9) = u256 (0x5500 * 2 ^ 240))
    (target count calldataSize : UInt256) :
    ¬ SystemPost (runDepositSystem Eip8282.Audit.Guarantees.PDrain1.DEPOSIT_CAP_FUEL .empty
      (code := PDrain1Mutant.headSlotMutatedDeposit)
      (storage := Eip8282.Audit.Guarantees.PDrain1.depositQueue65))
      depositAddr pre target count calldataSize := by
  apply violates_system_slot PDrain1Mutant.head_slot_mutant_overwrites_a_drained_word.1.2.2.2.1
  change u256 64 ≠ expectedSlot pre target count calldataSize (u256 9)
  simp only [expectedSlot, show u256 9 ≠ UInt256.ofNat 0 by decide,
    show u256 9 ≠ UInt256.ofNat 1 by decide, show u256 9 ≠ UInt256.ofNat 2 by decide,
    show u256 9 ≠ UInt256.ofNat 3 by decide, false_and, ↓reduceIte, hs]
  decide

/-- The direct anonymous-log predicate is tested on the mutated result, not on
an impossible assertion that mutant code equals the pinned runtime. -/
theorem log_size_mutant_breaks_authentic_log (c : XiCall .deposit)
    (hbefore : c.substate.logSeries = #[]) :
    ¬ Publishes (runDeposit Eip8282.Audit.Guarantees.PSubmit1.FUEL Eip8282.Audit.Guarantees.PSubmit1.submitter
      Eip8282.Audit.Guarantees.PSubmit1.payment Eip8282.Audit.Guarantees.PSubmit1.depositInput
      (code := PSubmit1Mutant.logSizeMutatedDeposit)
      (storage := Eip8282.Audit.Guarantees.PSubmit1.liveStorage))
      (fun _ substate _ => AppendSpec.AppendedLog c
        Eip8282.Audit.Guarantees.PSubmit1.depositInput substate) := by
  have hs := PSubmit1Mutant.log_size_mutant_empties_the_log.1.2.2.2.1
  rintro ⟨created, world, gas, substate, out, hr, hlog⟩
  rw [hr] at hs
  unfold AppendSpec.AppendedLog at hlog
  rw [hbefore] at hlog
  have hsize : Eip8282.Audit.Guarantees.PSubmit1.depositInput.size = 184 := by decide +kernel
  simp only [successLogDataSize, successLog?, successLogs, hlog] at hs
  change some Eip8282.Audit.Guarantees.PSubmit1.depositInput.size = some 0 at hs
  rw [hsize] at hs
  cases hs

#print axioms gate_mutant_breaks_count_reset
#print axioms target_mutant_breaks_excess
#print axioms exit_cap_mutant_breaks_head
#print axioms deposit_cap_mutant_breaks_head
#print axioms head_slot_mutant_breaks_stale_storage
#print axioms log_size_mutant_breaks_authentic_log

end Eip8282.Tests.DirectMutations

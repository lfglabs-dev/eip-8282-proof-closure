import Eip8282.Tests.DirectMutations
import Eip8282.Audit.Integrator.DirectControl
import Eip8282.Audit.Integrator.DirectDrain
import Eip8282.Audit.Integrator.DirectGuarantees

/-!
# Existing finite mutation receipts at the actual Θ boundary

The zero-value fixtures below execute parameter bytecode in an ordinary real
message-call Context. The transferred world and execution environment are
proved identical to the old runner inputs, so existing Ξ receipts can be reused
without evaluating new executions. No original-code pin is a domain premise.
The reused finite receipts retain their historical native-evaluation axioms.
-/
namespace Eip8282.Tests.DirectThetaMutations

open EvmYul EvmYul.EVM
open Eip8282.Audit.EvmRunner
open Eip8282.Audit.Integrator
open MessageCall SystemSpec

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- Parameter-code, zero-value SYSTEM context matching the legacy runner. -/
def depositSystem (fuel : Nat) (code : ByteArray) (storage : Storage)
    (data : ByteArray := .empty) : Context :=
  { fuel := fuel, created := default, genesis := default, blocks := default,
    world := worldWith depositAddr code sysAddr (ZERO_U256 + oneEth) storage,
    originalWorld := worldWith depositAddr code sysAddr (ZERO_U256 + oneEth) storage,
    substate := default, caller := sysAddr, origin := sysAddr, target := depositAddr,
    code := code, gas := defaultGas, gasPrice := ZERO_U256, value := ZERO_U256,
    apparentValue := ZERO_U256, calldata := data, depth := 0, header := default,
    permission := true, blobHashes := [] }

private theorem word_add_zero (w : UInt256) : w + UInt256.ofNat 0 = w := by
  cases w with
  | mk v => change UInt256.mk (v + 0) = UInt256.mk v; rw [add_zero]

private theorem word_sub_zero (w : UInt256) : w - UInt256.ofNat 0 = w := by
  cases w with
  | mk v => change UInt256.mk (v - 0) = UInt256.mk v; rw [sub_zero]

private theorem credit_zero (a : Account .EVM) :
    { a with balance := a.balance + UInt256.ofNat 0 } = a := by rw [word_add_zero]

private theorem debit_zero (a : Account .EVM) :
    { a with balance := a.balance - UInt256.ofNat 0 } = a := by rw [word_sub_zero]

theorem deposit_entry (fuel : Nat) (code : ByteArray) (storage : Storage) (data : ByteArray) :
    (depositSystem fuel code storage data).entryWorld = (depositSystem fuel code storage data).world := by
  simp only [Context.entryWorld, depositSystem, ZERO_U256, credit_zero, debit_zero]
  rfl

theorem deposit_execution (fuel : Nat) (code : ByteArray) (storage : Storage) (data : ByteArray) :
    (depositSystem fuel code storage data).execution =
      runDepositSystem fuel data (code := code) (storage := storage) := by
  unfold Context.execution
  rw [deposit_entry]
  rfl

/-- A positive slot observation supplies its actual successful result and an
account witness; no fabricated post-world is introduced. -/
theorem success_of_slot {r : RunResult} {owner : AccountAddress} {key value : UInt256}
    (hs : storageSlotIs r owner key value = true) :
    ∃ created world gas substate out,
      r = .ok (.success (created, world, gas, substate) out) ∧
      (∃ account, world.get? owner = some account) := by
  cases r with
  | error e => simp [storageSlotIs, storageSlotAfter] at hs
  | ok result =>
    cases result with
    | revert gas out => simp [storageSlotIs, storageSlotAfter] at hs
    | success published out =>
      rcases published with ⟨created, world, gas, substate⟩
      refine ⟨created, world, gas, substate, out, rfl, ?_⟩
      unfold storageSlotIs storageSlotAfter at hs
      change (match (world.get? owner).map (fun acc => acc.storage.getD key ZERO_U256) with
        | some v => v == value | none => false) = true at hs
      cases ha : world.get? owner with
      | none => rw [ha] at hs; cases hs
      | some account => exact ⟨account, rfl⟩

/-- Transport any such zero-value deposit SYSTEM receipt through actual Θ
settlement; the observed account rules out the empty-world fallback. -/
theorem deposit_theta_slot (fuel : Nat) (code : ByteArray) (storage : Storage)
    (data : ByteArray) (key value : UInt256)
    (hs : storageSlotIs (runDepositSystem fuel data (code := code) (storage := storage))
      depositAddr key value = true) :
    ∃ created world gas substate out,
      (depositSystem fuel code storage data).result = .ok (created, world, gas, substate, true, out) ∧
      worldSlot world depositAddr key = value := by
  obtain ⟨created, world, gas, substate, out, hr, account, ha⟩ := success_of_slot hs
  have hrun : (depositSystem fuel code storage data).execution =
      .ok (.success (created, world, gas, substate) out) :=
    (deposit_execution fuel code storage data).trans hr
  exact ⟨created, world, gas, substate, out,
    success_commits_world _ _ _ _ _ _ hrun (WorldNonempty.beq_empty_false_of_get_some ha),
    DirectMutations.worldSlot_of_receipt hr hs⟩

/-- Empty queue, EXCESS100/COUNT5; code remains a free fixture parameter. -/
def controlCall (code : ByteArray) : Context :=
  depositSystem Eip8282.Audit.Guarantees.PControl1.FUEL code
    (Eip8282.Audit.Guarantees.PControl1.ctlStorage 100 5)

theorem control_slot0 (code : ByteArray) :
    worldSlot (controlCall code).world (controlCall code).target (u256 0) = u256 100 := by rfl

theorem control_slot1 (code : ByteArray) :
    worldSlot (controlCall code).world (controlCall code).target (u256 1) = u256 5 := by rfl

theorem control_slot2 (code : ByteArray) :
    worldSlot (controlCall code).world (controlCall code).target (u256 2) = u256 0 := by rfl

theorem control_slot3 (code : ByteArray) :
    worldSlot (controlCall code).world (controlCall code).target (u256 3) = u256 0 := by rfl

/-- This independent local domain is inhabited for every tested code, not only
for the original runtime. It claims no protocol-history reachability. -/
theorem control_domain (code : ByteArray) :
    DirectGuarantees.Domain .deposit (controlCall code) 105 := by
  have h0 : worldSlot (controlCall code).world (controlCall code).target (UInt256.ofNat 0) = u256 100 := control_slot0 code
  have h1 : worldSlot (controlCall code).world (controlCall code).target (UInt256.ofNat 1) = u256 5 := control_slot1 code
  have h2 : worldSlot (controlCall code).world (controlCall code).target (UInt256.ofNat 2) = u256 0 := control_slot2 code
  have h3 : worldSlot (controlCall code).world (controlCall code).target (UInt256.ofNat 3) = u256 0 := control_slot3 code
  refine ⟨?_, rfl, by change 0 < UInt256.size; decide, by decide, ?_, ?_⟩
  · exact ⟨mkAccount code ZERO_U256 (Eip8282.Audit.Guarantees.PControl1.ctlStorage 100 5), rfl⟩
  · constructor
    · rw [h2, h3]
    · rw [h3]; decide
    · rw [h1]; decide
    · intro _; rw [h0, h1]; decide
  · apply Or.inr
    change (worldSlot (controlCall code).world (controlCall code).target (u256 0)).toNat +
      ((worldSlot (controlCall code).world (controlCall code).target (u256 1)).toNat - 8) ≤ 2892
    rw [control_slot0, control_slot1]
    decide

/-- The code installed at the fixture target is also the parameter code. -/
theorem control_installed (code : ByteArray) :
    ∃ account, (controlCall code).world.get? (controlCall code).target = some account ∧ account.code = code :=
  ⟨mkAccount code ZERO_U256 (Eip8282.Audit.Guarantees.PControl1.ctlStorage 100 5), rfl, rfl⟩

theorem gate_theta_counterexample :
    ∃ created world gas substate out,
      (controlCall PControl1Mutant.gateMutatedDeposit).result =
        .ok (created, world, gas, substate, true, out) ∧
      ¬ DirectControl.Observed .deposit (controlCall PControl1Mutant.gateMutatedDeposit)
        created world substate true out := by
  have hs := PControl1Mutant.gate_mutant_loses_the_system_subroutine.2.1
  simp only [slots0to3Are, Bool.and_eq_true] at hs
  obtain ⟨created, world, gas, substate, out, hr, hslot⟩ := deposit_theta_slot
    Eip8282.Audit.Guarantees.PControl1.FUEL PControl1Mutant.gateMutatedDeposit
    (Eip8282.Audit.Guarantees.PControl1.ctlStorage 100 5) .empty (u256 1) (u256 5) hs.1.1.2
  refine ⟨created, world, gas, substate, out, hr, ?_⟩
  intro hobs
  have hc := hobs.2.2 rfl
  change SystemDataSpec.ControlSlots .deposit 0 _ _ at hc
  have hzero := hc.2
  change worldSlot world depositAddr (u256 1) = (⟨0⟩ : UInt256) at hzero
  rw [hslot] at hzero
  exact (by decide : u256 5 ≠ (⟨0⟩ : UInt256)) hzero

theorem target_theta_counterexample :
    ∃ created world gas substate out,
      (controlCall PControl1Mutant.targetMutatedDeposit).result =
        .ok (created, world, gas, substate, true, out) ∧
      ¬ DirectControl.Observed .deposit (controlCall PControl1Mutant.targetMutatedDeposit)
        created world substate true out := by
  obtain ⟨created, world, gas, substate, out, hr, hslot⟩ := deposit_theta_slot
    Eip8282.Audit.Guarantees.PControl1.FUEL PControl1Mutant.targetMutatedDeposit
    (Eip8282.Audit.Guarantees.PControl1.ctlStorage 100 5) .empty (u256 0) (u256 96)
    PControl1Mutant.target_mutant_shifts_only_the_system_recurrence.1
  refine ⟨created, world, gas, substate, out, hr, ?_⟩
  intro hobs
  have hc := hobs.2.2 rfl
  change SystemDataSpec.ControlSlots .deposit 0 _ _ at hc
  have he := hc.1
  change (worldSlot world depositAddr (u256 0)).toNat =
    (if (0 : Nat) ≠ 0 then _ else
      if worldSlot (controlCall PControl1Mutant.targetMutatedDeposit).world
        (controlCall PControl1Mutant.targetMutatedDeposit).target (u256 0) = Eip8282.Audit.EntryReach.INH then 0
      else (worldSlot (controlCall PControl1Mutant.targetMutatedDeposit).world
        (controlCall PControl1Mutant.targetMutatedDeposit).target (u256 0)).toNat +
        (worldSlot (controlCall PControl1Mutant.targetMutatedDeposit).world
        (controlCall PControl1Mutant.targetMutatedDeposit).target (u256 1)).toNat - 8) at he
  rw [hslot, control_slot0, control_slot1] at he
  have hbad : ¬ ((u256 96).toNat =
      if (0 : Nat) ≠ 0 then Eip8282.Audit.EntryReach.INH.toNat else
      if u256 100 = Eip8282.Audit.EntryReach.INH then 0 else (u256 100).toNat + (u256 5).toNat - 8) := by decide
  exact hbad he

/-- The same parameter-code universal runtime predicate is false, not an
implication made vacuous by requiring the original pin. -/
theorem gate_refutes_runtime_control :
    ¬ DirectGuarantees.RuntimeControl .deposit PControl1Mutant.gateMutatedDeposit := by
  intro hp
  obtain ⟨created, world, gas, substate, out, hr, hn⟩ := gate_theta_counterexample
  exact hn (hp _ 105 rfl (control_domain _) created world gas substate true out hr)

theorem target_refutes_runtime_control :
    ¬ DirectGuarantees.RuntimeControl .deposit PControl1Mutant.targetMutatedDeposit := by
  intro hp
  obtain ⟨created, world, gas, substate, out, hr, hn⟩ := target_theta_counterexample
  exact hn (hp _ 105 rfl (control_domain _) created world gas substate true out hr)

theorem gate_refutes_pcontrol (init : ByteArray) :
    ¬ DirectGuarantees.PControl .deposit PControl1Mutant.gateMutatedDeposit init :=
  fun h => gate_refutes_runtime_control h.1

theorem target_refutes_pcontrol (init : ByteArray) :
    ¬ DirectGuarantees.PControl .deposit PControl1Mutant.targetMutatedDeposit init :=
  fun h => target_refutes_runtime_control h.1

#print axioms deposit_execution
#print axioms control_domain
#print axioms gate_theta_counterexample
#print axioms target_theta_counterexample
#print axioms gate_refutes_pcontrol
#print axioms target_refutes_pcontrol

end Eip8282.Tests.DirectThetaMutations

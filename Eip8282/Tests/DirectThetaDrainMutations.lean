import Eip8282.Tests.DirectThetaMutations

/-!
# Direct Θ drain mutation witnesses on independently represented queues

The fixtures supply actual pre-world words and an ordinary list of those words.
Their representation and bounds are checked independently of tested code.
Existing finite Ξ receipts are transported to Θ; no new execution is evaluated.
-/
namespace Eip8282.Tests.DirectThetaDrainMutations

open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.EvmRunner
open Eip8282.Audit.Integrator
open Eip8282.Audit.EntryReach
open MessageCall SystemSpec QueueInvariant
open DirectThetaMutations

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Read precisely n physical records at HEAD0; no execution or code parameter. -/
def queueOfRead (kind : Kind) (read : UInt256 → UInt256) (n : Nat) : List (Record kind) :=
  List.ofFn (fun i : Fin n => fun j => read (key kind i.val j))

theorem represents_queueOfRead (kind : Kind) (read : UInt256 → UInt256) (n : Nat)
    (hh : head read = 0) (ht : tail read = n)
    (hw : 4 + AppendStorage.stride kind * n ≤ UInt256.size) :
    Represents kind read (queueOfRead kind read n) := by
  refine ⟨by rw [hh, ht]; omega, by rw [ht]; exact hw, ?_, ?_⟩
  · simp only [queueOfRead, List.length_ofFn, hh, ht, Nat.sub_zero]
  · intro i hi j
    simp only [hh, Nat.zero_add, queueOfRead, List.getElem_ofFn]

/-- The storage fixture is fixed; its runtime is an independent parameter. -/
def depositCall (code : ByteArray) : Context :=
  depositSystem Eip8282.Audit.Guarantees.PDrain1.DEPOSIT_CAP_FUEL code
    Eip8282.Audit.Guarantees.PDrain1.depositQueue65

def depositRead (k : UInt256) : UInt256 :=
  Eip8282.Audit.Guarantees.PDrain1.depositQueue65.getD k ZERO_U256

theorem deposit_read (code : ByteArray) :
    worldSlot (depositCall code).world (depositCall code).target = depositRead := by
  rfl

theorem deposit_slot0 : depositRead (UInt256.ofNat 0) = u256 100 := by decide
theorem deposit_slot1 : depositRead (UInt256.ofNat 1) = u256 5 := by decide
theorem deposit_slot2 : depositRead (UInt256.ofNat 2) = u256 0 := by decide
theorem deposit_slot3 : depositRead (UInt256.ofNat 3) = u256 65 := by decide
theorem deposit_slot9 : depositRead (UInt256.ofNat 9) = u256 (0x5500 * 2^240) := by decide

def depositQueue : List (Record .deposit) := queueOfRead .deposit depositRead 65

theorem deposit_represents : Represents .deposit depositRead depositQueue := by
  apply represents_queueOfRead
  · change (depositRead (UInt256.ofNat 2)).toNat = 0
    rw [deposit_slot2]; rfl
  · change (depositRead (UInt256.ofNat 3)).toNat = 65
    rw [deposit_slot3]; rfl
  · decide

/-- The actual pre-world satisfies the same independent PDrain domain for
any runtime code, including both mutants. No reachable-history claim. -/
theorem deposit_domain (code : ByteArray) :
    DirectDrain.Domain .deposit (depositCall code) depositQueue 105 := by
  refine ⟨?_, rfl, by change 0 < UInt256.size; decide, by decide, ?_, ?_, ?_, True.intro⟩
  · exact ⟨mkAccount code ZERO_U256 Eip8282.Audit.Guarantees.PDrain1.depositQueue65, rfl⟩
  · rw [deposit_read]
    constructor
    · rw [deposit_slot2, deposit_slot3]; decide
    · rw [deposit_slot3]; decide
    · rw [deposit_slot1]; decide
    · intro _; rw [deposit_slot0, deposit_slot1]; decide
  · rw [deposit_read]
    apply Or.inr
    change (depositRead (UInt256.ofNat 0)).toNat + ((depositRead (UInt256.ofNat 1)).toNat - 8) ≤ 2892
    rw [deposit_slot0, deposit_slot1]
    decide
  · rw [deposit_read]
    exact deposit_represents

/-- Actual Θ cap violation, using the old execution's actual HEAD32. -/
theorem deposit_cap_counterexample :
    ∃ created world gas substate out,
      (depositCall PDrain1Mutant.capMutatedDeposit).result = .ok (created, world, gas, substate, true, out) ∧
      ¬ DirectDrain.Observed .deposit (depositCall PDrain1Mutant.capMutatedDeposit)
        world true out depositQueue := by
  obtain ⟨created, world, gas, substate, out, hr, hslot⟩ := deposit_theta_slot
    Eip8282.Audit.Guarantees.PDrain1.DEPOSIT_CAP_FUEL PDrain1Mutant.capMutatedDeposit
    Eip8282.Audit.Guarantees.PDrain1.depositQueue65 .empty (u256 2) (u256 32)
    PDrain1Mutant.deposit_cap_mutant_halves_the_over_cap_drain.1.2.1
  refine ⟨created, world, gas, substate, out, hr, ?_⟩
  intro hobs
  have hd : SystemDataSpec.DrainSlots .deposit
      (worldSlot (depositCall PDrain1Mutant.capMutatedDeposit).world depositAddr)
      (worldSlot world depositAddr) := hobs.1
  have hread : worldSlot (depositCall PDrain1Mutant.capMutatedDeposit).world depositAddr = depositRead :=
    deposit_read PDrain1Mutant.capMutatedDeposit
  rw [hread] at hd
  have hh := hd.1
  unfold SystemDataSpec.length SystemDataSpec.cap at hh
  change worldSlot world depositAddr (UInt256.ofNat 2) = u256 32 at hslot
  rw [deposit_slot2, deposit_slot3, hslot] at hh
  have hbad : ¬ ((u256 32).toNat =
      if min ((u256 65).toNat - (u256 0).toNat) 64 = (u256 65).toNat - (u256 0).toNat
      then 0 else (u256 0).toNat + min ((u256 65).toNat - (u256 0).toNat) 64) := by decide
  exact hbad hh

/-- Actual Θ destroys a stale word, refuting the same all-stale-slot clause. -/
theorem deposit_stale_counterexample :
    ∃ created world gas substate out,
      (depositCall PDrain1Mutant.headSlotMutatedDeposit).result = .ok (created, world, gas, substate, true, out) ∧
      ¬ DirectDrain.Observed .deposit (depositCall PDrain1Mutant.headSlotMutatedDeposit)
        world true out depositQueue := by
  obtain ⟨created, world, gas, substate, out, hr, hslot⟩ := deposit_theta_slot
    Eip8282.Audit.Guarantees.PDrain1.DEPOSIT_CAP_FUEL PDrain1Mutant.headSlotMutatedDeposit
    Eip8282.Audit.Guarantees.PDrain1.depositQueue65 .empty (u256 9) (u256 64)
    PDrain1Mutant.head_slot_mutant_overwrites_a_drained_word.1.2.2.2.1
  refine ⟨created, world, gas, substate, out, hr, ?_⟩
  intro hobs
  have hd : SystemDataSpec.DrainSlots .deposit
      (worldSlot (depositCall PDrain1Mutant.headSlotMutatedDeposit).world depositAddr)
      (worldSlot world depositAddr) := hobs.1
  have hread : worldSlot (depositCall PDrain1Mutant.headSlotMutatedDeposit).world depositAddr = depositRead :=
    deposit_read PDrain1Mutant.headSlotMutatedDeposit
  rw [hread] at hd
  have hh := hd.2.2 (UInt256.ofNat 9) (by decide)
  change worldSlot world depositAddr (UInt256.ofNat 9) = u256 64 at hslot
  rw [hslot, deposit_slot9] at hh
  exact (by decide : u256 64 ≠ u256 (0x5500 * 2^240)) hh

theorem deposit_cap_refutes_pdrain :
    ¬ DirectGuarantees.PDrain .deposit PDrain1Mutant.capMutatedDeposit := by
  intro hp
  obtain ⟨created, world, gas, substate, out, hr, hn⟩ := deposit_cap_counterexample
  exact hn (hp _ depositQueue 105 rfl (deposit_domain _) created world gas substate true out hr)

theorem deposit_stale_refutes_pdrain :
    ¬ DirectGuarantees.PDrain .deposit PDrain1Mutant.headSlotMutatedDeposit := by
  intro hp
  obtain ⟨created, world, gas, substate, out, hr, hn⟩ := deposit_stale_counterexample
  exact hn (hp _ depositQueue 105 rfl (deposit_domain _) created world gas substate true out hr)

/-- Symmetric parameter-code zero-value exit context. -/
def exitSystem (fuel : Nat) (code : ByteArray) (storage : Storage)
    (data : ByteArray := .empty) : Context :=
  { fuel := fuel, created := default, genesis := default, blocks := default,
    world := worldWith exitAddr code sysAddr (ZERO_U256 + oneEth) storage,
    originalWorld := worldWith exitAddr code sysAddr (ZERO_U256 + oneEth) storage,
    substate := default, caller := sysAddr, origin := sysAddr, target := exitAddr,
    code := code, gas := defaultGas, gasPrice := ZERO_U256, value := ZERO_U256,
    apparentValue := ZERO_U256, calldata := data, depth := 0, header := default,
    permission := true, blobHashes := [] }

private theorem credit_zero (a : Account .EVM) :
    { a with balance := a.balance + UInt256.ofNat 0 } = a := by
  have hw (w : UInt256) : w + UInt256.ofNat 0 = w := by
    cases w with
    | mk v => change UInt256.mk (v + 0) = UInt256.mk v; rw [add_zero]
  rw [hw]

private theorem debit_zero (a : Account .EVM) :
    { a with balance := a.balance - UInt256.ofNat 0 } = a := by
  have hw (w : UInt256) : w - UInt256.ofNat 0 = w := by
    cases w with
    | mk v => change UInt256.mk (v - 0) = UInt256.mk v; rw [sub_zero]
  rw [hw]

theorem exit_entry (fuel : Nat) (code : ByteArray) (storage : Storage) (data : ByteArray) :
    (exitSystem fuel code storage data).entryWorld = (exitSystem fuel code storage data).world := by
  simp only [Context.entryWorld, exitSystem, ZERO_U256, credit_zero, debit_zero]
  rfl

theorem exit_execution (fuel : Nat) (code : ByteArray) (storage : Storage) (data : ByteArray) :
    (exitSystem fuel code storage data).execution =
      runExitSystem fuel data (code := code) (storage := storage) := by
  unfold Context.execution
  rw [exit_entry]
  rfl

theorem exit_theta_slot (fuel : Nat) (code : ByteArray) (storage : Storage)
    (data : ByteArray) (key value : UInt256)
    (hs : storageSlotIs (runExitSystem fuel data (code := code) (storage := storage))
      exitAddr key value = true) :
    ∃ created world gas substate out,
      (exitSystem fuel code storage data).result = .ok (created, world, gas, substate, true, out) ∧
      worldSlot world exitAddr key = value := by
  obtain ⟨created, world, gas, substate, out, hr, account, ha⟩ := success_of_slot hs
  have hrun : (exitSystem fuel code storage data).execution =
      .ok (.success (created, world, gas, substate) out) :=
    (exit_execution fuel code storage data).trans hr
  exact ⟨created, world, gas, substate, out,
    success_commits_world _ _ _ _ _ _ hrun (WorldNonempty.beq_empty_false_of_get_some ha),
    DirectMutations.worldSlot_of_receipt hr hs⟩

def exitCall (code : ByteArray) : Context :=
  exitSystem Eip8282.Audit.Guarantees.PDrain1.FUEL code (Eip8282.Audit.Guarantees.PDrain1.exitQueue 17)

def exitRead (k : UInt256) : UInt256 :=
  (Eip8282.Audit.Guarantees.PDrain1.exitQueue 17).getD k ZERO_U256

theorem exit_read (code : ByteArray) :
    worldSlot (exitCall code).world (exitCall code).target = exitRead := by rfl

theorem exit_slot0 : exitRead (UInt256.ofNat 0) = u256 100 := by decide
theorem exit_slot1 : exitRead (UInt256.ofNat 1) = u256 5 := by decide
theorem exit_slot2 : exitRead (UInt256.ofNat 2) = u256 0 := by decide
theorem exit_slot3 : exitRead (UInt256.ofNat 3) = u256 17 := by decide

def exitQueue : List (Record .exit) := queueOfRead .exit exitRead 17

theorem exit_represents : Represents .exit exitRead exitQueue := by
  apply represents_queueOfRead
  · change (exitRead (UInt256.ofNat 2)).toNat = 0
    rw [exit_slot2]; rfl
  · change (exitRead (UInt256.ofNat 3)).toNat = 17
    rw [exit_slot3]; rfl
  · decide

/-- Kernel checks only the 17 stored source words, not any EVM execution. -/
theorem exit_sources : ∀ i : Fin 17,
    (exitRead (key .exit i.val ⟨0, by decide⟩)).toNat < 2^160 := by decide

theorem exit_source_width : SourceWidth exitQueue := by
  intro record hr
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  exact exit_sources i

theorem exit_domain (code : ByteArray) :
    DirectDrain.Domain .exit (exitCall code) exitQueue 105 := by
  refine ⟨?_, rfl, by change 0 < UInt256.size; decide, by decide, ?_, ?_, ?_, exit_source_width⟩
  · exact ⟨mkAccount code ZERO_U256 (Eip8282.Audit.Guarantees.PDrain1.exitQueue 17), rfl⟩
  · rw [exit_read]
    constructor
    · rw [exit_slot2, exit_slot3]; decide
    · rw [exit_slot3]; decide
    · rw [exit_slot1]; decide
    · intro _; rw [exit_slot0, exit_slot1]; decide
  · rw [exit_read]
    apply Or.inr
    change (exitRead (UInt256.ofNat 0)).toNat + ((exitRead (UInt256.ofNat 1)).toNat - 2) ≤ 2892
    rw [exit_slot0, exit_slot1]
    decide
  · rw [exit_read]
    exact exit_represents

/-- Actual Θ exit cap violation: HEAD8 instead of16 with seventeen records. -/
theorem exit_cap_counterexample :
    ∃ created world gas substate out,
      (exitCall PDrain1Mutant.capMutatedExit).result = .ok (created, world, gas, substate, true, out) ∧
      ¬ DirectDrain.Observed .exit (exitCall PDrain1Mutant.capMutatedExit)
        world true out exitQueue := by
  obtain ⟨created, world, gas, substate, out, hr, hslot⟩ := exit_theta_slot
    Eip8282.Audit.Guarantees.PDrain1.FUEL PDrain1Mutant.capMutatedExit
    (Eip8282.Audit.Guarantees.PDrain1.exitQueue 17) .empty (u256 2) (u256 8)
    PDrain1Mutant.cap_mutant_halves_the_over_cap_drain.2.1
  refine ⟨created, world, gas, substate, out, hr, ?_⟩
  intro hobs
  have hd : SystemDataSpec.DrainSlots .exit
      (worldSlot (exitCall PDrain1Mutant.capMutatedExit).world exitAddr)
      (worldSlot world exitAddr) := hobs.1
  have hread : worldSlot (exitCall PDrain1Mutant.capMutatedExit).world exitAddr = exitRead :=
    exit_read PDrain1Mutant.capMutatedExit
  rw [hread] at hd
  have hh := hd.1
  unfold SystemDataSpec.length SystemDataSpec.cap at hh
  change worldSlot world exitAddr (UInt256.ofNat 2) = u256 8 at hslot
  rw [exit_slot2, exit_slot3, hslot] at hh
  have hbad : ¬ ((u256 8).toNat =
      if min ((u256 17).toNat - (u256 0).toNat) 16 = (u256 17).toNat - (u256 0).toNat
      then 0 else (u256 0).toNat + min ((u256 17).toNat - (u256 0).toNat) 16) := by decide
  exact hbad hh

theorem exit_cap_refutes_pdrain :
    ¬ DirectGuarantees.PDrain .exit PDrain1Mutant.capMutatedExit := by
  intro hp
  obtain ⟨created, world, gas, substate, out, hr, hn⟩ := exit_cap_counterexample
  exact hn (hp _ exitQueue 105 rfl (exit_domain _) created world gas substate true out hr)

#print axioms exit_domain
#print axioms exit_cap_refutes_pdrain
#print axioms deposit_domain
#print axioms deposit_cap_refutes_pdrain
#print axioms deposit_stale_refutes_pdrain

end Eip8282.Tests.DirectThetaDrainMutations

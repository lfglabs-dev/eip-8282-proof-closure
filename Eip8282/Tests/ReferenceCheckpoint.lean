import Eip8282.Audit.Integrator.Topics.ReferenceCheckpoint
import Eip8282.Audit.Integrator.ReferenceAdmissionExtraction

/-! Injected transaction fixture, not a canonical history or full validator
certificate. These mutations detect accidentally using the world before gas
prepayment at the selected message call. No FFI/native_decide witness. -/
namespace Eip8282.Tests.ReferenceCheckpoint
open EvmYul EvmYul.EVM
open Eip8282.Audit.Integrator
open ReferenceAdmissionExtraction.AdmissionExtractionTest
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private def senderAccount : Account .EVM := {(default : Account .EVM) with balance := ⟨30001⟩}
private def transaction : RefundAccounting.Context :=
  {context (legacy (some (ReachableCalls.address .deposit)) ⟨1⟩ .empty ⟨1⟩) 0 with
    world := (∅ : AccountMap .EVM).insert alice senderAccount, fuel := 10}

private theorem upfront_eq : TransactionFunding.upfront transaction = 30000 := by
  change 30000 + 0 * transaction.header.getBlobGasprice = 30000
  simp

private theorem admitted : TransactionFunding.Admission transaction senderAccount := by
  refine ⟨Std.TreeMap.getElem?_insert_self,?_,?_,?_⟩
  · rw [upfront_eq]; decide +kernel
  · decide +kernel
  · decide +kernel

/-- Upfront payment leaves exactly the call value at the selected checkpoint. -/
theorem call_balance :
    TransferFunding.worldBalance (ReferenceCheckpointCall.call .deposit transaction).world alice = 1 := by
  have debited := TransactionFunding.debited_balance transaction admitted
  have upfront := upfront_eq
  rw [upfront] at debited
  change TransferFunding.worldBalance transaction.checkpoint alice = 1
  unfold TransferFunding.worldBalance
  rw [TransactionFunding.checkpoint_eq transaction admitted]
  change (((transaction.world.insert alice (TransactionFunding.debited transaction senderAccount)).get? alice).map (fun a => a.balance.toNat)).getD 0 = 1
  have lookup : (transaction.world.insert alice (TransactionFunding.debited transaction senderAccount)).get? alice =
      some (TransactionFunding.debited transaction senderAccount) := Std.TreeMap.getElem?_insert_self
  rw [lookup]
  simp only [Option.map_some,Option.getD_some]
  have initial : senderAccount.balance.toNat = 30001 := rfl
  rw [initial] at debited
  exact Nat.add_right_cancel (show (TransactionFunding.debited transaction senderAccount).balance.toNat + 30000 = 1 + 30000 from debited)

/-- Replacing the checkpoint by the before-transaction world is observably
wrong even though both worlds have enough funds for the one-wei call. -/
theorem rejects_pretransaction_world :
    (ReferenceCheckpointCall.call .deposit transaction).world ≠ transaction.world := by
  intro wrong
  have after := call_balance
  rw [wrong] at after
  have before : TransferFunding.worldBalance transaction.world alice = 30001 := by
    unfold TransferFunding.worldBalance
    change ((((∅ : AccountMap .EVM).insert alice senderAccount).get? alice).map (fun a => a.balance.toNat)).getD 0 = 30001
    have lookup : ((∅ : AccountMap .EVM).insert alice senderAccount).get? alice = some senderAccount :=
      Std.TreeMap.getElem?_insert_self
    rw [lookup]
    rfl
  rw [before] at after
  exact (by decide : (30001 : Nat) ≠ 1) after

#print axioms call_balance
#print axioms rejects_pretransaction_world
end Eip8282.Tests.ReferenceCheckpoint

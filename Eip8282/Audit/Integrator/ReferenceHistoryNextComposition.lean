import Eip8282.Audit.Integrator.ReferenceFundedHistoryLifecycle

/-! Two-step composition lemmas for iterated
`ReferenceFundedHistoryLifecycle.next`.

Consumers frequently need to know that the receipt list telescopes
across two consecutive Υ receipt extensions. Rather than re-computing
`h.receipts ++ [r1] ++ [r2]` at each site, these lemmas expose the
composition directly.

No new premise; no new axiom. Each lemma is a direct equational
consequence of `receipts_extend`. -/
namespace Eip8282.Audit.Integrator.ReferenceHistoryNextComposition

open EvmYul EvmYul.EVM
open TransactionAppendBudget (Receipt BlockReceipt)
open ReleaseCandidate (History)
open ReferenceFundedHistoryLifecycle
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- Two consecutive `next` extensions telescope the receipt list to
`h.receipts ++ [r1, r2]`. -/
theorem next_next_receipts {deposit exit : Receipt} {before₀ : AccountMap .EVM}
    (h : History deposit exit before₀)
    (r1 : Receipt) (linked1 : r1.call.world = before₀)
    (account1 : EvmYul.Account .EVM)
    (admission1 : TransactionFunding.Admission r1.call account1)
    (fit1 : r1.call.transaction.base.data.size < UInt256.size)
    (resources1 : 5*(r1.call.entryGas.toNat+1) ≤ r1.call.fuel)
    (slot1 gas1 : ResourceBounds.U64)
    (freshSlot1 : slot1 ∉ h.blocks.map (fun b => b.slot))
    (admittedGas1 : r1.used.toNat ≤ gas1.val)
    (r2 : Receipt) (linked2 : r2.call.world = r1.world)
    (account2 : EvmYul.Account .EVM)
    (admission2 : TransactionFunding.Admission r2.call account2)
    (fit2 : r2.call.transaction.base.data.size < UInt256.size)
    (resources2 : 5*(r2.call.entryGas.toNat+1) ≤ r2.call.fuel)
    (slot2 gas2 : ResourceBounds.U64)
    (freshSlot2 : slot2 ∉ (next h r1 linked1 account1 admission1 fit1 resources1 slot1 gas1 freshSlot1 admittedGas1).blocks.map (fun b => b.slot))
    (admittedGas2 : r2.used.toNat ≤ gas2.val) :
    (next (next h r1 linked1 account1 admission1 fit1 resources1 slot1 gas1 freshSlot1 admittedGas1)
          r2 linked2 account2 admission2 fit2 resources2 slot2 gas2 freshSlot2 admittedGas2).receipts
      = h.receipts ++ [r1, r2] := by
  simp [receipts_extend]

/-- Two consecutive `next` extensions increase the block list length by
exactly two. -/
theorem next_next_blocks_length {deposit exit : Receipt} {before₀ : AccountMap .EVM}
    (h : History deposit exit before₀)
    (r1 : Receipt) (linked1 : r1.call.world = before₀)
    (account1 : EvmYul.Account .EVM)
    (admission1 : TransactionFunding.Admission r1.call account1)
    (fit1 : r1.call.transaction.base.data.size < UInt256.size)
    (resources1 : 5*(r1.call.entryGas.toNat+1) ≤ r1.call.fuel)
    (slot1 gas1 : ResourceBounds.U64)
    (freshSlot1 : slot1 ∉ h.blocks.map (fun b => b.slot))
    (admittedGas1 : r1.used.toNat ≤ gas1.val)
    (r2 : Receipt) (linked2 : r2.call.world = r1.world)
    (account2 : EvmYul.Account .EVM)
    (admission2 : TransactionFunding.Admission r2.call account2)
    (fit2 : r2.call.transaction.base.data.size < UInt256.size)
    (resources2 : 5*(r2.call.entryGas.toNat+1) ≤ r2.call.fuel)
    (slot2 gas2 : ResourceBounds.U64)
    (freshSlot2 : slot2 ∉ (next h r1 linked1 account1 admission1 fit1 resources1 slot1 gas1 freshSlot1 admittedGas1).blocks.map (fun b => b.slot))
    (admittedGas2 : r2.used.toNat ≤ gas2.val) :
    (next (next h r1 linked1 account1 admission1 fit1 resources1 slot1 gas1 freshSlot1 admittedGas1)
          r2 linked2 account2 admission2 fit2 resources2 slot2 gas2 freshSlot2 admittedGas2).blocks.length
      = h.blocks.length + 2 := by
  simp [blocks_extend]

#print axioms next_next_receipts
#print axioms next_next_blocks_length

end Eip8282.Audit.Integrator.ReferenceHistoryNextComposition

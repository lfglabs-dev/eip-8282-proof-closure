import Eip8282.Audit.Integrator.ReleaseCandidate

/-! Named aliases for the block-slot uniqueness and listed-receipts fields
of `ReleaseCandidate.History`.

`slots` and `listed` are structure fields of every funded History; they
already witness the two invariants required by
`ActualJournalHistory.work_lt_of_blocks` and by
`ResourceBounds.total_lt`. This module exposes them under named
theorems so consumers can quote a single `theorem` rather than
`h.slots` / `h.listed` at every call site. It also provides a
`work_lt` alias for the resulting `< 2^128` bound so downstream
resource-envelope proofs get the same treatment.

No new premise; no new axiom. -/
namespace Eip8282.Audit.Integrator.ReferenceHistorySlotsAlias

open EvmYul EvmYul.EVM
open TransactionAppendBudget (Receipt BlockReceipt)
open ReleaseCandidate (History)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- The block-slot list of any funded History has no duplicates. -/
theorem slots_nodup {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) :
    (h.blocks.map (fun b => b.slot)).Nodup := h.slots

/-- The receipts of any funded History are literally the concatenation of
each block's receipts, preserving block order. -/
theorem listed_flatMap {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) :
    h.receipts = h.blocks.flatMap (fun b => b.receipts) := h.listed

/-- Direct consequence of `slots_nodup` and `listed_flatMap`: the
accumulated actual work count fits strictly inside `2^128`. Consumers of
the block/resource envelope can quote this instead of chaining
`work_lt_of_blocks`. -/
theorem work_lt_from_slots {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) :
    ActualJournalHistory.work h.receipts < 2^128 :=
  ActualJournalHistory.work_lt_of_blocks h.receipts h.blocks h.listed h.slots

#print axioms slots_nodup
#print axioms listed_flatMap
#print axioms work_lt_from_slots

end Eip8282.Audit.Integrator.ReferenceHistorySlotsAlias

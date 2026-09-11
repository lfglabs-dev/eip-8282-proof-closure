import Eip8282.Audit.Integrator.ReleaseCandidate

/-! PoW-batch extension of `ReleaseCandidate.History`.

Completes the `ProtocolCreditEnvelope.Ledger` constructor coverage:
where `ReferenceFundedHistoryLifecycle.next` / `.next_system` /
`.next_transfer` extend via `Ledger.conserving` and
`ReferenceHistoryWithdrawalExtension.next_withdrawal` extends via
`Ledger.withdrawal`, `ReferenceHistoryPowBatchExtension.next_pow_batch`
extends via `Ledger.pow` on a `ProtocolCreditEnvelope.CreditBatch`.

The extension takes an existing `History deposit exit before`, a
`CreditBatch before amount after` witnessing the ordered protocol
credits (each `.cons` step credits one recipient by a `UInt256`
amount), an aggregate bound `amount ≤ powMaximum` and a caller-supplied
count admission `pow + 1 ≤ 2^64`. It increments the `pow` counter and
the credit total by the aggregate amount, and extends the
`ActualJournalHistory.Trace` by one `Trace.credit` step per batch entry
via a private helper `extend_trace_batch`.

`pow`, `withdrawals`, `migrations` and `baseCredits` are otherwise
preserved; receipts and blocks are preserved literally. Four
stability/accounting lemmas expose the exact shape.

Neither the extension nor its lemmas assert consensus-level scheduling
of the PoW batch, do not identify a particular fork, and do not name a
canonical batch source; the caller-supplied bounds and the
`CreditBatch` witness exactly match what `Ledger.pow` and `Trace.credit`
accept. -/
namespace Eip8282.Audit.Integrator.ReferenceHistoryPowBatchExtension

open EvmYul EvmYul.EVM
open TransactionAppendBudget (Receipt)
open ReleaseCandidate (History)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- Threading a `CreditBatch` through the `ActualJournalHistory.Trace`
produces a new Trace whose credit count is the initial count plus the
batch aggregate. The recursion is on the batch structure. -/
private theorem extend_trace_batch {initial before after : AccountMap .EVM}
    {receipts : List TransactionAppendBudget.Receipt} {credits amount : Nat}
    (trace : ActualJournalHistory.Trace initial receipts credits before)
    (batch : ProtocolCreditEnvelope.CreditBatch before amount after) :
    ActualJournalHistory.Trace initial receipts (credits + amount) after := by
  induction batch generalizing credits with
  | nil w => simpa using trace
  | cons recipient amount tail ih =>
    have next := ActualJournalHistory.Trace.credit trace recipient amount
    have step := ih next
    simpa only [Nat.add_assoc] using step

/-- Extend a funded History by one PoW batch. The credit total grows by
`amount` (the batch aggregate), the pow counter increments by one, and
the world advances from `before` to `after` along the batch. -/
def next_pow_batch {deposit exit : Receipt} {before after : AccountMap .EVM}
    (h : History deposit exit before)
    {amount : Nat} (batch : ProtocolCreditEnvelope.CreditBatch before amount after)
    (bounded : amount ≤ ProtocolCreditEnvelope.powMaximum)
    (nextCount : h.pow + 1 ≤ 2^64) :
    History deposit exit after :=
  { depositInputs := h.depositInputs
    exitInputs := h.exitInputs
    linked := h.linked
    baseCredits := h.baseCredits
    credits := h.credits + amount
    pow := h.pow + 1
    withdrawals := h.withdrawals
    migrations := h.migrations
    receipts := h.receipts
    prior := h.prior
    actual := extend_trace_batch h.actual batch
    ledger := by
      have base := ProtocolCreditEnvelope.Ledger.pow h.ledger batch bounded
      -- (baseCredits + credits) + amount = baseCredits + (credits + amount)
      simpa only [Nat.add_assoc] using base
    counts := {
      pow_count := nextCount
      withdrawal_count := h.counts.withdrawal_count
      migration_conserving := h.counts.migration_conserving }
    blocks := h.blocks
    listed := h.listed
    slots := h.slots }

/-- PoW-batch extension preserves the receipt list. -/
theorem next_pow_batch_receipts_stable {deposit exit : Receipt}
    {before after : AccountMap .EVM}
    {h : History deposit exit before}
    {amount : Nat} {batch : ProtocolCreditEnvelope.CreditBatch before amount after}
    {bounded : amount ≤ ProtocolCreditEnvelope.powMaximum}
    {nextCount : h.pow + 1 ≤ 2^64} :
    (next_pow_batch h batch bounded nextCount).receipts = h.receipts := rfl

/-- PoW-batch extension preserves the block list. -/
theorem next_pow_batch_blocks_stable {deposit exit : Receipt}
    {before after : AccountMap .EVM}
    {h : History deposit exit before}
    {amount : Nat} {batch : ProtocolCreditEnvelope.CreditBatch before amount after}
    {bounded : amount ≤ ProtocolCreditEnvelope.powMaximum}
    {nextCount : h.pow + 1 ≤ 2^64} :
    (next_pow_batch h batch bounded nextCount).blocks = h.blocks := rfl

/-- PoW-batch extension increases credit total by the batch aggregate. -/
theorem next_pow_batch_credits {deposit exit : Receipt}
    {before after : AccountMap .EVM}
    {h : History deposit exit before}
    {amount : Nat} {batch : ProtocolCreditEnvelope.CreditBatch before amount after}
    {bounded : amount ≤ ProtocolCreditEnvelope.powMaximum}
    {nextCount : h.pow + 1 ≤ 2^64} :
    (next_pow_batch h batch bounded nextCount).credits = h.credits + amount := rfl

/-- PoW-batch extension increments the pow counter by one; other
protocol counters (`withdrawals`, `migrations`) and `baseCredits` are
preserved. -/
theorem next_pow_batch_counters {deposit exit : Receipt}
    {before after : AccountMap .EVM}
    {h : History deposit exit before}
    {amount : Nat} {batch : ProtocolCreditEnvelope.CreditBatch before amount after}
    {bounded : amount ≤ ProtocolCreditEnvelope.powMaximum}
    {nextCount : h.pow + 1 ≤ 2^64} :
    (next_pow_batch h batch bounded nextCount).pow = h.pow + 1 ∧
    (next_pow_batch h batch bounded nextCount).withdrawals = h.withdrawals ∧
    (next_pow_batch h batch bounded nextCount).migrations = h.migrations ∧
    (next_pow_batch h batch bounded nextCount).baseCredits = h.baseCredits :=
  ⟨rfl, rfl, rfl, rfl⟩

#print axioms next_pow_batch
#print axioms next_pow_batch_receipts_stable
#print axioms next_pow_batch_blocks_stable
#print axioms next_pow_batch_credits
#print axioms next_pow_batch_counters

end Eip8282.Audit.Integrator.ReferenceHistoryPowBatchExtension

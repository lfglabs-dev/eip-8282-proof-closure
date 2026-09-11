import Eip8282.Audit.Integrator.ReleaseCandidate

/-! Withdrawal-batched extension of `ReleaseCandidate.History`.

Complements the three zero-credit extensions (transaction via
`ReferenceFundedHistoryLifecycle.next`, and SYSTEM Θ / bare transfer via
`ReferenceHistoryNonReceiptExtensions`) with the withdrawal case that
increments the withdrawal counter and the credit total.

`next_withdrawal` accepts a recipient, a `UInt256` amount already
admitted by `ProtocolCreditEnvelope.Ledger.withdrawal`
(`amount.toNat ≤ withdrawalMaximum`), plus a caller-supplied count
admission that the incremented `withdrawals + 1` still fits inside
`16 * 2^64`. The extension threads the underlying `Trace.credit`
constructor for the balance change, chains the ledger via
`Ledger.withdrawal`, and produces a `History` whose credit total is
`h.credits + amount.toNat`. Receipts, blocks and other counters are
preserved.

The extension does not assert any consensus-level scheduling of the
withdrawal, does not name a withdrawal index, and does not identify a
particular fork. It packages the exact input tuple that
`Ledger.withdrawal` and `Trace.credit` accept and produces the
resulting `History` structure so downstream consumers can thread
withdrawals without pattern matching. -/
namespace Eip8282.Audit.Integrator.ReferenceHistoryWithdrawalExtension

open EvmYul EvmYul.EVM
open TransactionAppendBudget (Receipt)
open ReleaseCandidate (History)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- Extend a funded History by one withdrawal-credit event. The recipient's
balance increases by `amount`; the ledger's withdrawal counter increments;
the credit total grows by `amount.toNat`. Receipts, blocks and other
counters (`pow`, `migrations`) are preserved literally. Caller supplies
the count admission `withdrawals + 1 ≤ 16 * 2^64`. -/
def next_withdrawal {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before)
    (recipient : AccountAddress) (amount : UInt256)
    (bounded : amount.toNat ≤ ProtocolCreditEnvelope.withdrawalMaximum)
    (nextCount : h.withdrawals + 1 ≤ 16 * 2^64) :
    History deposit exit (before.increaseBalance .EVM recipient amount) :=
  { depositInputs := h.depositInputs
    exitInputs := h.exitInputs
    linked := h.linked
    baseCredits := h.baseCredits
    credits := h.credits + amount.toNat
    pow := h.pow
    withdrawals := h.withdrawals + 1
    migrations := h.migrations
    receipts := h.receipts
    prior := h.prior
    actual := ActualJournalHistory.Trace.credit h.actual recipient amount
    ledger := by
      have base := ProtocolCreditEnvelope.Ledger.withdrawal h.ledger recipient amount bounded
      -- The ledger's credit-count index becomes `(baseCredits + credits) + amount.toNat`,
      -- which equals `baseCredits + (credits + amount.toNat)` — the new History's total.
      simpa only [Nat.add_assoc] using base
    counts := {
      pow_count := h.counts.pow_count
      withdrawal_count := nextCount
      migration_conserving := h.counts.migration_conserving }
    blocks := h.blocks
    listed := h.listed
    slots := h.slots }

/-- Withdrawal extension preserves the receipt list. -/
theorem next_withdrawal_receipts_stable {deposit exit : Receipt} {before : AccountMap .EVM}
    {h : History deposit exit before}
    {recipient : AccountAddress} {amount : UInt256}
    {bounded : amount.toNat ≤ ProtocolCreditEnvelope.withdrawalMaximum}
    {nextCount : h.withdrawals + 1 ≤ 16 * 2^64} :
    (next_withdrawal h recipient amount bounded nextCount).receipts = h.receipts := rfl

/-- Withdrawal extension preserves the block list. -/
theorem next_withdrawal_blocks_stable {deposit exit : Receipt} {before : AccountMap .EVM}
    {h : History deposit exit before}
    {recipient : AccountAddress} {amount : UInt256}
    {bounded : amount.toNat ≤ ProtocolCreditEnvelope.withdrawalMaximum}
    {nextCount : h.withdrawals + 1 ≤ 16 * 2^64} :
    (next_withdrawal h recipient amount bounded nextCount).blocks = h.blocks := rfl

/-- Withdrawal extension increments credit total by `amount.toNat`. -/
theorem next_withdrawal_credits {deposit exit : Receipt} {before : AccountMap .EVM}
    {h : History deposit exit before}
    {recipient : AccountAddress} {amount : UInt256}
    {bounded : amount.toNat ≤ ProtocolCreditEnvelope.withdrawalMaximum}
    {nextCount : h.withdrawals + 1 ≤ 16 * 2^64} :
    (next_withdrawal h recipient amount bounded nextCount).credits = h.credits + amount.toNat := rfl

/-- Withdrawal extension increments the withdrawal counter by one; other
protocol counters (`pow`, `migrations`) and `baseCredits` are preserved. -/
theorem next_withdrawal_counters {deposit exit : Receipt} {before : AccountMap .EVM}
    {h : History deposit exit before}
    {recipient : AccountAddress} {amount : UInt256}
    {bounded : amount.toNat ≤ ProtocolCreditEnvelope.withdrawalMaximum}
    {nextCount : h.withdrawals + 1 ≤ 16 * 2^64} :
    (next_withdrawal h recipient amount bounded nextCount).withdrawals = h.withdrawals + 1 ∧
    (next_withdrawal h recipient amount bounded nextCount).pow = h.pow ∧
    (next_withdrawal h recipient amount bounded nextCount).migrations = h.migrations ∧
    (next_withdrawal h recipient amount bounded nextCount).baseCredits = h.baseCredits :=
  ⟨rfl, rfl, rfl, rfl⟩

#print axioms next_withdrawal
#print axioms next_withdrawal_receipts_stable
#print axioms next_withdrawal_blocks_stable
#print axioms next_withdrawal_credits
#print axioms next_withdrawal_counters

end Eip8282.Audit.Integrator.ReferenceHistoryWithdrawalExtension

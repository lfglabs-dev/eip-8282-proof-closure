import Eip8282.Audit.Integrator.ReleaseCandidate

/-! Non-receipt-adding extensions of `ReleaseCandidate.History`.

Complements `ReferenceFundedHistoryLifecycle.next` (which appends one
ordinary Υ receipt to the History) with the remaining two zero-credit
`ActualJournalHistory.Trace` extension constructors that do not append
receipts: `system` (a mandatory SYSTEM Θ invocation, empty data, zero
value) and `transfer` (a protocol-level balance transfer).

Both extensions preserve the History's receipt list, block list, credit
totals and ledger credit count exactly. Only the `before` world in the
History parameter changes. The internal ledger extension goes through
`ProtocolCreditEnvelope.Ledger.conserving` on `FundingHistory.Step.system`
or `.transfer` (both carry zero credits, so the ledger's aggregate credit
total is unchanged).

Neither extension asserts:
* that any canonical Ethereum machinery has authorized the SYSTEM Θ (the
  caller/zero-value/data-fit conditions are inputs, exactly matching
  `ReferenceCanonicalHooks.SystemAuthorization`);
* that any protocol-level transfer is scheduled or admissible beyond the
  input `funded` premise (source has enough balance);
* that these extensions produce a canonical block sequence.

Consumers that already accept `ReleaseCandidate.History deposit exit before`
and then update `before` via a SYSTEM Θ or a bare transfer can now do so
by calling `next_system` or `next_transfer` without pattern matching on the
History structure. -/
namespace Eip8282.Audit.Integrator.ReferenceHistoryNonReceiptExtensions

open EvmYul EvmYul.EVM
open TransactionAppendBudget (Receipt)
open ReachableCalls (Contract Transition)
open ReleaseCandidate (History)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- Extend a funded History by one mandatory SYSTEM Θ invocation. The
receipt list, block list, credit totals and ledger credit count are all
preserved; only the pre-world advances from `before` to `after`, driven
by the actual `Transition`. -/
def next_system {deposit exit : Receipt} {before after : AccountMap .EVM}
    (h : History deposit exit before)
    {selector : Contract} (t : Transition selector before after)
    (senderIsSys : t.call.caller = Eip8282.Audit.EvmRunner.sysAddr)
    (zeroValue : t.call.value = ⟨0⟩)
    (dataFit : t.call.calldata.size < UInt256.size) :
    History deposit exit after :=
  let step : FundingHistory.Step before 0 after := by
    have base := FundingHistory.Step.system t.call senderIsSys zeroValue t.executed
    rw [t.pre] at base
    exact base
  { depositInputs := h.depositInputs
    exitInputs := h.exitInputs
    linked := h.linked
    baseCredits := h.baseCredits
    credits := h.credits
    pow := h.pow
    withdrawals := h.withdrawals
    migrations := h.migrations
    receipts := h.receipts
    prior := h.prior
    actual := ActualJournalHistory.Trace.system h.actual t senderIsSys zeroValue dataFit
    ledger := ProtocolCreditEnvelope.Ledger.conserving h.ledger step
    counts := h.counts
    blocks := h.blocks
    listed := h.listed
    slots := h.slots }

/-- Extend a funded History by one bare protocol-level balance transfer.
The receipt list, block list, credit totals and ledger credit count are
all preserved; only the pre-world advances from `before` to
`ProtocolTransfer.transfer before sender recipient amount`, gated by the
input `funded` premise (sender has enough balance). -/
def next_transfer {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before)
    (sender recipient : AccountAddress) (amount : UInt256)
    (funded : amount.toNat ≤ TransferFunding.worldBalance before sender) :
    History deposit exit (ProtocolTransfer.transfer before sender recipient amount) :=
  let step : FundingHistory.Step before 0 (ProtocolTransfer.transfer before sender recipient amount) :=
    FundingHistory.Step.transfer before sender recipient amount funded
  { depositInputs := h.depositInputs
    exitInputs := h.exitInputs
    linked := h.linked
    baseCredits := h.baseCredits
    credits := h.credits
    pow := h.pow
    withdrawals := h.withdrawals
    migrations := h.migrations
    receipts := h.receipts
    prior := h.prior
    actual := ActualJournalHistory.Trace.transfer h.actual sender recipient amount funded
    ledger := ProtocolCreditEnvelope.Ledger.conserving h.ledger step
    counts := h.counts
    blocks := h.blocks
    listed := h.listed
    slots := h.slots }

/-- Both non-receipt extensions preserve the receipt list literally. -/
theorem next_system_receipts_stable {deposit exit : Receipt} {before after : AccountMap .EVM}
    {h : History deposit exit before} {selector : Contract}
    {t : Transition selector before after}
    {senderIsSys : t.call.caller = Eip8282.Audit.EvmRunner.sysAddr}
    {zeroValue : t.call.value = ⟨0⟩}
    {dataFit : t.call.calldata.size < UInt256.size} :
    (next_system h t senderIsSys zeroValue dataFit).receipts = h.receipts := rfl

theorem next_transfer_receipts_stable {deposit exit : Receipt} {before : AccountMap .EVM}
    {h : History deposit exit before}
    {sender recipient : AccountAddress} {amount : UInt256}
    {funded : amount.toNat ≤ TransferFunding.worldBalance before sender} :
    (next_transfer h sender recipient amount funded).receipts = h.receipts := rfl

/-- Both non-receipt extensions preserve the block list literally. -/
theorem next_system_blocks_stable {deposit exit : Receipt} {before after : AccountMap .EVM}
    {h : History deposit exit before} {selector : Contract}
    {t : Transition selector before after}
    {senderIsSys : t.call.caller = Eip8282.Audit.EvmRunner.sysAddr}
    {zeroValue : t.call.value = ⟨0⟩}
    {dataFit : t.call.calldata.size < UInt256.size} :
    (next_system h t senderIsSys zeroValue dataFit).blocks = h.blocks := rfl

theorem next_transfer_blocks_stable {deposit exit : Receipt} {before : AccountMap .EVM}
    {h : History deposit exit before}
    {sender recipient : AccountAddress} {amount : UInt256}
    {funded : amount.toNat ≤ TransferFunding.worldBalance before sender} :
    (next_transfer h sender recipient amount funded).blocks = h.blocks := rfl

/-- Credit totals are preserved by both non-receipt extensions. -/
theorem next_system_credits_stable {deposit exit : Receipt} {before after : AccountMap .EVM}
    {h : History deposit exit before} {selector : Contract}
    {t : Transition selector before after}
    {senderIsSys : t.call.caller = Eip8282.Audit.EvmRunner.sysAddr}
    {zeroValue : t.call.value = ⟨0⟩}
    {dataFit : t.call.calldata.size < UInt256.size} :
    (next_system h t senderIsSys zeroValue dataFit).credits = h.credits ∧
    (next_system h t senderIsSys zeroValue dataFit).baseCredits = h.baseCredits := ⟨rfl, rfl⟩

theorem next_transfer_credits_stable {deposit exit : Receipt} {before : AccountMap .EVM}
    {h : History deposit exit before}
    {sender recipient : AccountAddress} {amount : UInt256}
    {funded : amount.toNat ≤ TransferFunding.worldBalance before sender} :
    (next_transfer h sender recipient amount funded).credits = h.credits ∧
    (next_transfer h sender recipient amount funded).baseCredits = h.baseCredits := ⟨rfl, rfl⟩

#print axioms next_system
#print axioms next_transfer
#print axioms next_system_receipts_stable
#print axioms next_transfer_receipts_stable
#print axioms next_system_blocks_stable
#print axioms next_transfer_blocks_stable
#print axioms next_system_credits_stable
#print axioms next_transfer_credits_stable

end Eip8282.Audit.Integrator.ReferenceHistoryNonReceiptExtensions

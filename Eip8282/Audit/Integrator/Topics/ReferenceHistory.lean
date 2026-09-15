import Eip8282.Audit.Integrator.Topics.Reference2
import Eip8282.Audit.Integrator.ReferenceFundedHistoryLifecycle
import Eip8282.Audit.Integrator.ReleaseCandidate

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceHistoryFailure -/

/-! Existing initialized history derives the old entry owner needed by the
PC replay proof. The same source account-aware failure then derives its catch
classification and projected rollback/meter/log settlement. No independent
owner Bool, old HasOwner, caught-fault or desired postcondition is supplied.
This is not yet full source/old-world equality or source transaction closure;
account payloads, value transfer and actual saved frame identity stay open.
-/
namespace Eip8282.Audit.Integrator.ReferenceHistoryFailure
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem code {kind : Contract} {c : MessageCall.Context} (input : ReleaseCandidate.CallInput kind c) :
    c.code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind) := by
  cases kind <;> exact input.code

theorem settled {deposit exit : TransactionAppendBudget.Receipt} {Account Hash Error : Type} [DecidableEq Hash] {kind : Contract}
    (c : MessageCall.Context)
    (history : ReleaseCandidate.History deposit exit c.world) (input : ReleaseCandidate.CallInput kind c)
    (codeHash : Account → Hash) (emptyHash : Hash)
    (accountsParent : ReferenceAccountLookup.Parent Account) (accounts : ReferenceAccountLookup.Tx Account)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (codeWrites : Hash → Option ByteArray)
    {parent : ReferenceStorageView.Parent} {tx : ReferenceStorageView.Tx}
    {warm partialWarm : Warm} {pre partialMeter : Meter} {fuel : Nat} {events : List Event}
    {view : View} {output : ByteArray} {fault : Fault} {destinations : List Nat}
    {finalAccounts : ReferenceAccountLookup.Tx Account}
    (context : ReferenceCheckedStackControlStep.DestinationContext (JournalInvariant.modelKind kind) destinations)
    (loaded : (ReferenceCodeAccountPresence.load codeHash emptyHash accountsParent accounts codeParent codeWrites
      c.target).1 = .ok c.code)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel
      (ReferenceCodeAccountPresence.load codeHash emptyHash accountsParent accounts codeParent codeWrites c.target).2
      (initial (CallBridge.codeCall c (code input) 0) tx) warm pre = some ((events,.failed fault view partialWarm partialMeter output),finalAccounts))
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c (code input) 0).entry.toState)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code input) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (calldata : c.calldata.size < UInt256.size) :
    ∃ receipt,
      ReferenceCheckedFrameOutcome.settle tx [] warm (.failed fault view partialWarm partialMeter output) = .returned receipt ∧
      receipt.beforeSettlement = view ∧ receipt.output = ByteArray.empty ∧
      receipt.meter.execution = 0 ∧ receipt.meter.reservoir = partialMeter.baseline ∧
      receipt.meter.spill = 0 ∧ receipt.meter.refund = 0 ∧
      receipt.meter.committedSpill = partialMeter.committedSpill ∧
      receipt.logsForParent = [] ∧ receipt.warmForParent = none ∧
      receipt.storage.created = view.storage.created ∧ receipt.storage.reads = view.storage.reads ∧
      ∀ p address key, ReferenceStorageView.current p receipt.storage address key =
        ReferenceStorageView.current p tx address key := by
  exact ReferenceDerivedFailure.settled (CallBridge.codeCall c (code input) 0)
    codeHash emptyHash accountsParent accounts codeParent codeWrites context loaded actual slots
    (TransferFrame.pinned_codeCall_hasOwner c (ReleaseCandidate.installed_call history input) (code input) 0)
    warmRelated grant calldata

#print axioms settled
end Eip8282.Audit.Integrator.ReferenceHistoryFailure

end

section

/-! ## ReferenceHistoryFundsBridge -/

/-! Bridge: a funded `ReleaseCandidate.History` at world `before` yields
the world-funds budget bound `worldFunds before < FundedDomain.fundingCeiling`.

`ProtocolCreditEnvelope.funding_budget` already gives this bound
conditional on a genesis-funds premise. `GenesisFundingWorld.initial_funds_le`
supplies exactly that premise for `initial = GenesisFundingWorld.world`,
which is the fixed initial world of every History via its `prior` and
`ledger` fields.

The bridge specializes those two facts to the concrete `History`
structure so consumers can quote a single named theorem
`worldFunds_lt_ceiling h` rather than re-threading the ledger, counts
and genesis premise at every call site. It also exposes a companion
`funding_trace_from_genesis` giving the accumulated
`FundingHistory.Trace GenesisFundingWorld.world (baseCredits + credits) before`
that `funding_budget` yields, keyed to the History's fields.

The bridge does not adopt any protocol policy or admit a new premise:
it packages the same fact that `funding_budget` and
`GenesisFundingWorld.initial_funds_le` already prove independently. -/
namespace Eip8282.Audit.Integrator.ReferenceHistoryFundsBridge

open EvmYul EvmYul.EVM
open TransactionAppendBudget (Receipt)
open ReleaseCandidate (History)
open ProtocolCreditEnvelope (funding_budget)
open GenesisFundingWorld (initial_funds_le)
open FundedDomain (fundingCeiling)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- Named funding-history trace from genesis to the History's before-world,
accumulating `baseCredits + credits` credits along the way. -/
theorem funding_trace_from_genesis {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) :
    FundingHistory.Trace GenesisFundingWorld.world (h.baseCredits + h.credits) before :=
  (funding_budget h.ledger initial_funds_le h.counts).1

/-- Bridge theorem: the `before`-world of any funded History has
world-funds strictly below the audited funding ceiling. This is the
consumer-facing single-lemma form of
`GenesisFundingWorld.initial_funds_le` combined with
`ProtocolCreditEnvelope.funding_budget h.ledger _ h.counts`. -/
theorem worldFunds_lt_ceiling {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) :
    TransferFunding.worldFunds before < FundedDomain.fundingCeiling := by
  have hb := (funding_budget h.ledger initial_funds_le h.counts).2
  -- hb : worldFunds initial + (baseCredits + credits) < fundingCeiling
  -- since worldFunds before ≤ worldFunds initial + (baseCredits + credits), this gives:
  have hs := FundingHistory.trace_funds (funding_trace_from_genesis h)
  exact lt_of_le_of_lt hs hb

/-- Companion: any individual account's balance in `before` is bounded
by the funding ceiling. Consumers can quote this alongside
`worldFunds_lt_ceiling`. -/
theorem worldBalance_lt_ceiling {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) (address : AccountAddress) :
    TransferFunding.worldBalance before address < FundedDomain.fundingCeiling :=
  (TransferFunding.balance_le_funds before address).trans_lt (worldFunds_lt_ceiling h)

#print axioms funding_trace_from_genesis
#print axioms worldFunds_lt_ceiling
#print axioms worldBalance_lt_ceiling

end Eip8282.Audit.Integrator.ReferenceHistoryFundsBridge

end

section

/-! ## ReferenceHistoryInvariantsAliases -/

/-! Named single-fact aliases of `ReleaseCandidate.invariants`.

`ReleaseCandidate.invariants h` returns a four-way conjunction:
`deposit.success = true`, `exit.success = true`,
`ActualJournalHistory.work h.receipts < 2^128`, and the family
`∀ kind, JournalInvariant.Invariant kind (work h.receipts) before`.
Downstream consumers frequently need only one of the four facts and
end up destructuring the conjunction at every call site. This module
exposes each fact under its own name so a consumer can quote a single
named lemma. No new premise; no new axiom; each alias is a direct
projection. -/
namespace Eip8282.Audit.Integrator.ReferenceHistoryInvariantsAliases

open EvmYul EvmYul.EVM
open TransactionAppendBudget (Receipt)
open ReleaseCandidate (History)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

/-- The deposit receipt of any funded History records a successful call. -/
theorem deposit_success {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) : deposit.success = true :=
  (ReleaseCandidate.invariants h).1

/-- The exit receipt of any funded History records a successful call. -/
theorem exit_success {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) : exit.success = true :=
  (ReleaseCandidate.invariants h).2.1

/-- The accumulated actual work count of any funded History stays strictly
below `2^128`. This is the resource envelope bound. -/
theorem work_lt {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) :
    ActualJournalHistory.work h.receipts < 2^128 :=
  (ReleaseCandidate.invariants h).2.2.1

/-- The protected `JournalInvariant.Invariant` holds at the `before` world of
any funded History, at the accumulated work count and for every kind. -/
theorem invariant_at {deposit exit : Receipt} {before : AccountMap .EVM}
    (h : History deposit exit before) (kind : ReachableCalls.Contract) :
    JournalInvariant.Invariant kind (ActualJournalHistory.work h.receipts) before :=
  (ReleaseCandidate.invariants h).2.2.2 kind

#print axioms deposit_success
#print axioms exit_success
#print axioms work_lt
#print axioms invariant_at

end Eip8282.Audit.Integrator.ReferenceHistoryInvariantsAliases

end

section

/-! ## ReferenceHistoryNextComposition -/

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

end

section

/-! ## ReferenceHistorySlotsAlias -/

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

end

section

/-! ## ReferenceHistoryWithdrawalExtension -/

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

end

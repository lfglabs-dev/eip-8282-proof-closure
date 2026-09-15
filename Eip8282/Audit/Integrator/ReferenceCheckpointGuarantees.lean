import Eip8282.Audit.Integrator.Topics.ReferenceSource
import Eip8282.Audit.Integrator.Topics.ReferenceCheckpoint

/-! Before-transaction initialized history and explicit admission supply the
actual selected checkpoint call. The same source-shaped computed terminal/EOF
carries all3 guarantees and settled balances without a funded-call hypothesis
or an artificial History after prepayment. Source pre-state fields/warm/gas
bindings and mode are still explicit. This does not identify source gas with
old replay resources or assert complete Amsterdam admission/type4 compatibility. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckpointGuarantees
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open JournalInvariant (modelKind)
open TransactionAppendBudget (Receipt)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

open ReferenceCheckpointCall (call)

private theorem input (kind : Contract) (transaction : RefundAccounting.Context) :
    ReleaseCandidate.CallInput kind (call kind transaction) := ⟨rfl,rfl,rfl⟩

private theorem code (kind : Contract) (transaction : RefundAccounting.Context) :
    (call kind transaction).code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
  cases kind <;> rfl

theorem terminal {deposit exit : Receipt} (kind : Contract) (transaction : RefundAccounting.Context)
    (history : ReleaseCandidate.History deposit exit transaction.world)
    {sender : EvmYul.Account .EVM} (admission : TransactionFunding.Admission transaction sender)
    (recipient : transaction.transaction.base.recipient = some (ReachableCalls.address kind))
    {Hash LoadError : Type} [DecidableEq Hash]
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    {parent : ReferenceStorageView.Parent}
    {warm : Warm} {pre : Meter} {fuel : Nat} {events : List Event}
    {result : ReferenceCheckedTerminalStep.End} {destinations : List Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel (entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2.accounts
      (initial (CallBridge.codeCall (call kind transaction) (code kind transaction) 0) (entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2.storage) warm pre = some ((events,.terminal result),finalAccounts))
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites (call kind transaction).target).1 = .ok (call kind transaction).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before (call kind transaction).world)
    (mode : shouldTransfer = true ∨ (call kind transaction).value = ⟨0⟩)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage (call kind transaction).target q.toByteArray = SystemSpec.worldSlot (call kind transaction).world (call kind transaction).target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall (call kind transaction) (code kind transaction) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : (call kind transaction).calldata.size < UInt256.size) :
    TransactionEventBounds.request transaction = .theta transaction.fuel
      (TransactionEventBounds.message transaction (ReachableCalls.address kind)) ∧
    (0 < transaction.fuel → (call kind transaction).result =
      (NestedEvents.Request.theta transaction.fuel (TransactionEventBounds.message transaction (ReachableCalls.address kind))).eval) ∧
    (entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).1 = .ok () ∧
    ReferenceSourceCompletedBalances.Completed emptyHash accountsParent before
      {(entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts, storage := result.view.storage}
      kind (call kind transaction) parent events result.view (decide (result.halt ≠ .reverted)) result.output ∧ finalAccounts.writes = (entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2.accounts.writes ∧
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent
      {(entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts} (call kind transaction).entryWorld := by
  have facts := ReferenceCheckpointCall.domain kind transaction history admission
  have pinned := ReferenceCheckpointCall.pinned kind transaction history admission
  have ready := ReferenceSourcePreparedBounds.prepared (call kind transaction) (input kind transaction) facts.2.2.2
    emptyHash accountsParent before codeParent shouldTransfer parent loaded balances facts.2.2.1 slots
  have stack : (initial (CallBridge.codeCall (call kind transaction) (code kind transaction) 0)
      (entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2.storage).stack.length ≤ 1024 := by simp [initial]
  have aligned := ReferenceActionMemoryBounds.empty_aligned
    (initial (CallBridge.codeCall (call kind transaction) (code kind transaction) 0)
      (entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2.storage) rfl
  obtain ⟨checked,writes⟩ := ReferenceCheckedAccountEvaluator.evaluated context actual stack aligned
  have old := ReferenceCheckedTheta.terminal pinned context checked ready.2 warmRelated grant facts.1 facts.2.1 fit
  have startBalances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent
      (fetched emptyHash accountsParent before codeParent (call kind transaction).target) (call kind transaction).world := balances
  have transported := ReferenceSourceBalanceTransport.enter_balances emptyHash accountsParent
    (fetched emptyHash accountsParent before codeParent (call kind transaction).target) (call kind transaction) shouldTransfer startBalances facts.2.2.1 facts.2.2.2 mode
  have sameBalances := ReferenceSourceBalanceOutcome.same_writes emptyHash accountsParent
    (entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2
    {(entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts}
    (call kind transaction).entryWorld transported writes
  have completed := ReferenceSourceCompletedBalances.of_completed emptyHash accountsParent before
    {(entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts, storage := result.view.storage}
    pinned old balances sameBalances
  have selected := ReferenceCheckpointCall.selected_request kind transaction recipient
  exact ⟨selected,ReferenceCheckpointCall.call_result kind transaction history admission,ready.1,completed,writes,sameBalances⟩

theorem eof {deposit exit : Receipt} (kind : Contract) (transaction : RefundAccounting.Context)
    (history : ReleaseCandidate.History deposit exit transaction.world)
    {sender : EvmYul.Account .EVM} (admission : TransactionFunding.Admission transaction sender)
    (recipient : transaction.transaction.base.recipient = some (ReachableCalls.address kind))
    {Hash LoadError : Type} [DecidableEq Hash]
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    {parent : ReferenceStorageView.Parent}
    {warm finalWarm : Warm} {pre final : Meter} {fuel : Nat} {events : List Event}
    {view : View} {output : ByteArray} {destinations : List Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel (entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2.accounts
      (initial (CallBridge.codeCall (call kind transaction) (code kind transaction) 0) (entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2.storage) warm pre = some ((events,.eof view finalWarm final output),finalAccounts))
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites (call kind transaction).target).1 = .ok (call kind transaction).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before (call kind transaction).world)
    (mode : shouldTransfer = true ∨ (call kind transaction).value = ⟨0⟩)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage (call kind transaction).target q.toByteArray = SystemSpec.worldSlot (call kind transaction).world (call kind transaction).target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall (call kind transaction) (code kind transaction) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : (call kind transaction).calldata.size < UInt256.size) :
    TransactionEventBounds.request transaction = .theta transaction.fuel
      (TransactionEventBounds.message transaction (ReachableCalls.address kind)) ∧
    (0 < transaction.fuel → (call kind transaction).result =
      (NestedEvents.Request.theta transaction.fuel (TransactionEventBounds.message transaction (ReachableCalls.address kind))).eval) ∧
    (entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).1 = .ok () ∧
    output = ByteArray.empty ∧ ReferenceSourceCompletedBalances.Completed emptyHash accountsParent before
      {(entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts, storage := view.storage}
      kind (call kind transaction) parent events view true output ∧ finalAccounts.writes = (entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2.accounts.writes ∧
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent
      {(entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts} (call kind transaction).entryWorld := by
  have facts := ReferenceCheckpointCall.domain kind transaction history admission
  have pinned := ReferenceCheckpointCall.pinned kind transaction history admission
  have ready := ReferenceSourcePreparedBounds.prepared (call kind transaction) (input kind transaction) facts.2.2.2
    emptyHash accountsParent before codeParent shouldTransfer parent loaded balances facts.2.2.1 slots
  have stack : (initial (CallBridge.codeCall (call kind transaction) (code kind transaction) 0)
      (entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2.storage).stack.length ≤ 1024 := by simp [initial]
  have aligned := ReferenceActionMemoryBounds.empty_aligned
    (initial (CallBridge.codeCall (call kind transaction) (code kind transaction) 0)
      (entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2.storage) rfl
  obtain ⟨checked,writes⟩ := ReferenceCheckedAccountEvaluator.evaluated context actual stack aligned
  obtain ⟨empty,old⟩ := ReferenceCheckedTheta.eof pinned context checked ready.2 warmRelated grant facts.1 facts.2.1 fit
  have startBalances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent
      (fetched emptyHash accountsParent before codeParent (call kind transaction).target) (call kind transaction).world := balances
  have transported := ReferenceSourceBalanceTransport.enter_balances emptyHash accountsParent
    (fetched emptyHash accountsParent before codeParent (call kind transaction).target) (call kind transaction) shouldTransfer startBalances facts.2.2.1 facts.2.2.2 mode
  have sameBalances := ReferenceSourceBalanceOutcome.same_writes emptyHash accountsParent
    (entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2
    {(entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts}
    (call kind transaction).entryWorld transported writes
  have completed := ReferenceSourceCompletedBalances.of_completed emptyHash accountsParent before
    {(entry (call kind transaction) emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts, storage := view.storage}
    pinned old balances sameBalances
  have selected := ReferenceCheckpointCall.selected_request kind transaction recipient
  exact ⟨selected,ReferenceCheckpointCall.call_result kind transaction history admission,ready.1,empty,completed,writes,sameBalances⟩

#print axioms terminal
#print axioms eof
end Eip8282.Audit.Integrator.ReferenceCheckpointGuarantees

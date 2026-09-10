import Eip8282.Audit.Integrator.ReferenceCheckpointGuarantees
import Eip8282.Audit.Integrator.ReferenceSourcePrepaidCheckpoint

/-! Stronger pretransaction-source-journal consumer for represented nonblob
transactions. Ordered source prepayment derives every after-prepayment code,
slot and balance binding used by the same checkpoint consumer. Its rollback
snapshot is after prepayment, so nonce/gas debit is not undone by call failure.
The older checkpoint APIs and their blob domain are unchanged. This narrower
source-prepayment agreement domain excludes old represented blob transactions;
it does not cover source type4, complete Python frame construction or canonical
Ethereum admission. Replay resources remain distinct from source gas. -/
namespace Eip8282.Audit.Integrator.ReferencePrepaidGuarantees
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
open ReferenceSourcePrepaidCheckpoint (prepaid)


private theorem code (kind : Contract) (transaction : RefundAccounting.Context) :
    (call kind transaction).code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
  cases kind <;> rfl

theorem terminal {deposit exit : Receipt} (kind : Contract) (transaction : RefundAccounting.Context)
    (history : ReleaseCandidate.History deposit exit transaction.world)
    {sender : EvmYul.Account .EVM} (admission : TransactionFunding.Admission transaction sender)
    (recipient : transaction.transaction.base.recipient = some (ReachableCalls.address kind))
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob transaction.transaction)
    {Hash LoadError : Type} [DecidableEq Hash]
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    {parent : ReferenceStorageView.Parent}
    {warm : Warm} {pre : Meter} {fuel : Nat} {events : List Event}
    {result : ReferenceCheckedTerminalStep.End} {destinations : List Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent shouldTransfer).2.accounts
      (initial (CallBridge.codeCall (call kind transaction) (code kind transaction) 0) (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent shouldTransfer).2.storage) warm pre = some ((events,.terminal result),finalAccounts))
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites (call kind transaction).target).1 = .ok (call kind transaction).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before transaction.world)
    (mode : shouldTransfer = true ∨ (call kind transaction).value = ⟨0⟩)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage (call kind transaction).target q.toByteArray = SystemSpec.worldSlot transaction.world (call kind transaction).target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall (call kind transaction) (code kind transaction) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : (call kind transaction).calldata.size < UInt256.size) :
    (prepaid emptyHash accountsParent before transaction).1 = .ok () ∧
    TransactionEventBounds.request transaction = .theta transaction.fuel
      (TransactionEventBounds.message transaction (ReachableCalls.address kind)) ∧
    (0 < transaction.fuel → (call kind transaction).result =
      (NestedEvents.Request.theta transaction.fuel (TransactionEventBounds.message transaction (ReachableCalls.address kind))).eval) ∧
    (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent shouldTransfer).1 = .ok () ∧
    ReferenceSourceCompletedBalances.Completed emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2
      {(entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent shouldTransfer).2 with accounts := finalAccounts, storage := result.view.storage}
      kind (call kind transaction) parent events result.view (decide (result.halt ≠ .reverted)) result.output ∧ finalAccounts.writes = (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent shouldTransfer).2.accounts.writes ∧
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent
      {(entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent shouldTransfer).2 with accounts := finalAccounts} (call kind transaction).entryWorld := by
  have ready := ReferenceSourcePrepaidCheckpoint.bindings emptyHash accountsParent before transaction kind codeParent parent
    admission nonblob balances loaded slots
  refine ⟨ready.1,?_⟩
  exact ReferenceCheckpointGuarantees.terminal kind transaction history admission recipient emptyHash accountsParent
    (prepaid emptyHash accountsParent before transaction).2 codeParent shouldTransfer context actual ready.2.1 ready.2.2.1 mode ready.2.2.2 warmRelated grant fit

theorem eof {deposit exit : Receipt} (kind : Contract) (transaction : RefundAccounting.Context)
    (history : ReleaseCandidate.History deposit exit transaction.world)
    {sender : EvmYul.Account .EVM} (admission : TransactionFunding.Admission transaction sender)
    (recipient : transaction.transaction.base.recipient = some (ReachableCalls.address kind))
    (nonblob : ReferenceSourcePrepaidCheckpoint.Nonblob transaction.transaction)
    {Hash LoadError : Type} [DecidableEq Hash]
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    {parent : ReferenceStorageView.Parent}
    {warm finalWarm : Warm} {pre final : Meter} {fuel : Nat} {events : List Event}
    {view : View} {output : ByteArray} {destinations : List Nat}
    (context : ReferenceCheckedStackControlStep.DestinationContext (modelKind kind) destinations)
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent shouldTransfer).2.accounts
      (initial (CallBridge.codeCall (call kind transaction) (code kind transaction) 0) (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent shouldTransfer).2.storage) warm pre = some ((events,.eof view finalWarm final output),finalAccounts))
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites (call kind transaction).target).1 = .ok (call kind transaction).code)
    (balances : ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent before transaction.world)
    (mode : shouldTransfer = true ∨ (call kind transaction).value = ⟨0⟩)
    (slots : ∀ q, ReferenceStorageView.current parent before.storage (call kind transaction).target q.toByteArray = SystemSpec.worldSlot transaction.world (call kind transaction).target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall (call kind transaction) (code kind transaction) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (fit : (call kind transaction).calldata.size < UInt256.size) :
    (prepaid emptyHash accountsParent before transaction).1 = .ok () ∧
    TransactionEventBounds.request transaction = .theta transaction.fuel
      (TransactionEventBounds.message transaction (ReachableCalls.address kind)) ∧
    (0 < transaction.fuel → (call kind transaction).result =
      (NestedEvents.Request.theta transaction.fuel (TransactionEventBounds.message transaction (ReachableCalls.address kind))).eval) ∧
    (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent shouldTransfer).1 = .ok () ∧
    output = ByteArray.empty ∧ ReferenceSourceCompletedBalances.Completed emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2
      {(entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent shouldTransfer).2 with accounts := finalAccounts, storage := view.storage}
      kind (call kind transaction) parent events view true output ∧ finalAccounts.writes = (entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent shouldTransfer).2.accounts.writes ∧
    ReferenceSourceTransferFunding.BalancesRelated emptyHash accountsParent
      {(entry (call kind transaction) emptyHash accountsParent (prepaid emptyHash accountsParent before transaction).2 codeParent shouldTransfer).2 with accounts := finalAccounts} (call kind transaction).entryWorld := by
  have ready := ReferenceSourcePrepaidCheckpoint.bindings emptyHash accountsParent before transaction kind codeParent parent
    admission nonblob balances loaded slots
  refine ⟨ready.1,?_⟩
  exact ReferenceCheckpointGuarantees.eof kind transaction history admission recipient emptyHash accountsParent
    (prepaid emptyHash accountsParent before transaction).2 codeParent shouldTransfer context actual ready.2.1 ready.2.2.1 mode ready.2.2.2 warmRelated grant fit

#print axioms terminal
#print axioms eof
end Eip8282.Audit.Integrator.ReferencePrepaidGuarantees

import Eip8282.Audit.Integrator.ReferenceSystemOutputReceipt
import Eip8282.Audit.Integrator.ReferenceCheckedSystemJournal

/-! One exhaustive checked mandatory SYSTEM computation, three predicates,
complete local receipt/journal settlement and top-level gas conversions.
Initialized history, represented block storage and actual pinned source code
read are the domain. No outcome/trace/post-state premise is supplied. Successful
drain within source resources is established by the stronger SystemDrainTotal;
this safety theorem preserves failures rather than silently assuming success. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemTotal
open EvmYul EvmYul.EVM ReferenceCheckedSystemEntry
open ReferenceRuntimeView ReferenceSourceReadings ReferenceCheckedDispatch
open ReferenceSettledAccountJournal (journal)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem verified {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (c : Context) (history : ReleaseCandidate.History deposit exit c.world)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    ProtocolSystemDispatchExtraction.frame (ProtocolSystemDispatchExtraction.mandatory kind c.baseFee)
      c.world c.genesis c.blocks c.header 8503 = call kind c ∧
    (∀ signature, ReferenceCallEntry.logs (call kind c) true signature = []) ∧
    (entered kind c emptyHash accountsParent codeParent).1 = .ok () ∧
    ∃ events result finalAccounts finish finalWarm final receipt,
      ReferenceCheckedSystemExecution.run kind c emptyHash accountsParent codeParent = some ((events,result),finalAccounts) ∧
      ReferenceCheckedSystemOutcome.Claims kind c events result ∧
      ReferenceCheckedRuntimeTrace.Run (JournalInvariant.modelKind kind) (storageParent c)
        (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage) ∅ (meter kind c)
        finish finalWarm final events ∧
      ReferenceCheckedDispatch.run (ReferenceInitialAccess.destinations (call kind c).code)
        (ReferenceAccountLookup.peek accountsParent (entered kind c emptyHash accountsParent codeParent).2.accounts (ReachableCalls.address kind)).isSome
        (storageParent c) finish finalWarm final ByteArray.empty = result ∧
      ReferenceCheckedFrameOutcome.settle (before Hash).storage [] finalWarm result = .returned receipt ∧
      ReferenceSystemOutputMeter.Facts (ProtocolSystemDispatchExtraction.mandatory kind c.baseFee).stateGasReservoir receipt.meter ∧
      let settled := journal (before Hash) (entered kind c emptyHash accountsParent codeParent).2 finalAccounts receipt
      settled.accounts.writes = (before Hash).accounts.writes ∧
      settled.accounts.reads = finalAccounts.reads ∧
      settled.codeWrites = (before Hash).codeWrites ∧ settled.transient = (before Hash).transient ∧
      settled.storage = receipt.storage ∧
      ∀ a, ReferenceSourceValueTransfer.account emptyHash accountsParent settled a =
        ReferenceSourceValueTransfer.account emptyHash accountsParent (before Hash) a := by
  have inputs := constructed kind c history
  have ready := (ReferenceCheckedSystemEntry.ready kind c emptyHash accountsParent codeParent loaded).2
  refine ⟨inputs.1,inputs.2.2.1,by rw [ready],?_⟩
  obtain ⟨events,result,finalAccounts,actual,supported⟩ := ReferenceCheckedSystemExecution.computed kind c history emptyHash accountsParent codeParent loaded
  obtain ⟨finish,finalWarm,final,trace,last,writes⟩ := ReferenceCheckedSystemExecution.extracted kind c history emptyHash accountsParent codeParent loaded actual
  have claims := (ReferenceCheckedSystemOutcome.proved kind c history emptyHash accountsParent codeParent loaded actual supported finalWarm).1
  have fresh : (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage).storage = ReferenceRuntimeStateBalance.emptyTx := by rw [ready]; rfl
  obtain ⟨receipt,settled,fields⟩ := ReferenceSystemOutputReceipt.settled trace
    (by simp [initial]) (ReferenceActionMemoryBounds.empty_aligned _ rfl) fresh rfl rfl inputs.2.2.2.le last claims (before Hash).storage
  exact ⟨events,result,finalAccounts,finish,finalWarm,final,receipt,actual,claims,trace,last,settled,fields,
    ReferenceCheckedSystemJournal.unchanged kind c emptyHash accountsParent codeParent loaded finalAccounts receipt writes⟩

#print axioms verified
end Eip8282.Audit.Integrator.ReferenceCheckedSystemTotal

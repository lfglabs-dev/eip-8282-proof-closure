import Eip8282.Audit.Integrator.ReferenceSystemBlockFootprint
import Eip8282.Audit.Integrator.ReferenceSystemBlockParent
import Eip8282.Audit.Integrator.Topics.ReferenceCheckedSystem

/-! The actual mandatory SYSTEM receipt has finite owner-local typed storage
support. Its source block storage incorporation is derived from that same
receipt, never from an independently supplied final world. BAL processing
before incorporation and the subsequent SYSTEM call are separate consumers.
No assertion of canonical Ethereum block admission is made here. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemBlockReceipt
open EvmYul EvmYul.EVM ReferenceCheckedSystemEntry
open ReferenceRuntimeView ReferenceSourceReadings ReferenceCheckedDispatch
open ReferenceSystemBlockFootprint
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem verified {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (c : Context) (history : ReleaseCandidate.History deposit exit c.world)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    ∃ events ended finalAccounts finalWarm receipt keys,
      ReferenceCheckedSystemExecution.run kind c emptyHash accountsParent codeParent = some ((events,.terminal ended),finalAccounts) ∧
      ReferenceCheckedSystemOutcome.Claims kind c events (.terminal ended) ∧ ended.halt = .returned ∧
      ended.view.env.codeOwner = ReachableCalls.address kind ∧
      ReferenceCheckedFrameOutcome.settle (before Hash).storage [] finalWarm (.terminal ended) = .returned receipt ∧
      ReferenceSystemOutputMeter.Facts (ProtocolSystemDispatchExtraction.mandatory kind c.baseFee).stateGasReservoir receipt.meter ∧
      receipt.error = none ∧ receipt.storage = ended.view.storage ∧ receipt.output = ended.output ∧
      receipt.meter = ended.meter ∧ receipt.logsForParent = ended.view.logs ∧
      Support (ReachableCalls.address kind) receipt.storage keys ∧
      ReferenceSystemBlockParent.CompletedRun (JournalInvariant.modelKind kind) (storageParent c)
        (ReferenceInitialAccess.destinations (call kind c).code)
        (ReferenceAccountLookup.peek accountsParent (entered kind c emptyHash accountsParent codeParent).2.accounts (ReachableCalls.address kind)).isSome
        (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage) ∅ (meter kind c)
        events ended finalWarm ∧
      let settled := ReferenceSettledAccountJournal.journal (before Hash)
        (entered kind c emptyHash accountsParent codeParent).2 finalAccounts receipt
      settled.accounts.writes = (before Hash).accounts.writes ∧
      settled.accounts.reads = finalAccounts.reads ∧
      settled.codeWrites = (before Hash).codeWrites ∧ settled.transient = (before Hash).transient ∧
      settled.storage = receipt.storage ∧
      ∀ a, ReferenceSourceValueTransfer.account emptyHash accountsParent settled a =
        ReferenceSourceValueTransfer.account emptyHash accountsParent (before Hash) a := by
  obtain ⟨_,_,_,events,ended,finalAccounts,finish,finalWarm,final,receipt,
    actual,claims,halt,trace,last,settled,fields,error,storage,output,gas,logs,journal⟩ :=
    ReferenceCheckedSystemDrainTotal.verified kind c history emptyHash accountsParent codeParent loaded
  have fresh : (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage).storage =
      (⟨fun _ _ => none,∅,∅⟩ : ReferenceStorageView.Tx) := by
    rw [(ready kind c emptyHash accountsParent codeParent loaded).2]
    rfl
  have initialSupport : Support
      (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage).env.codeOwner
      (initial (xi kind c) (entered kind c emptyHash accountsParent codeParent).2.storage).storage [] := by
    rw [fresh]
    exact empty _
  obtain ⟨env,keys,support⟩ := checked trace (by simp [initial])
    (ReferenceActionMemoryBounds.empty_aligned _ rfl) initialSupport
  obtain ⟨endEnv,endSupport⟩ := terminal last support
  have endOwner : ended.view.env.codeOwner = ReachableCalls.address kind := by
    rw [endEnv,env]
    rfl
  refine ⟨events,ended,finalAccounts,finalWarm,receipt,keys,
    actual,claims,halt,endOwner,settled,fields,error,storage,output,gas,logs,?_,⟨finish,final,trace,last⟩,journal⟩
  simpa only [List.append_nil,endOwner,storage] using endSupport

#print axioms verified
end Eip8282.Audit.Integrator.ReferenceSystemBlockReceipt

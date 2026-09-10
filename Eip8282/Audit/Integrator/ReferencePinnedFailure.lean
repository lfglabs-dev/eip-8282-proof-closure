import Eip8282.Audit.Integrator.ReferenceTransferredFailure

/-! Failed source-shaped execution and the exact pre-transfer snapshot need a
pinned call/owner, not a History at that intermediate world. The checkpoint
consumer derives this owner and transfer entry from actual admission. This
factorization retains the same error classification and four-field restoration. -/
namespace Eip8282.Audit.Integrator.ReferencePinnedFailure
open EvmYul EvmYul.EVM
open ReachableCalls (Contract)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceCheckedDispatch ReferenceTransferredFailure
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem code {kind : Contract} {c : MessageCall.Context} (pinned : ReachableCalls.PinnedCall kind c) :
    c.code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind) := by
  cases kind <;> exact pinned.code

theorem caught {Hash LoadError : Type} [DecidableEq Hash]
    {kind : Contract} (c : MessageCall.Context)
    (pinned : ReachableCalls.PinnedCall kind c)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    {parent : ReferenceStorageView.Parent} {warm partialWarm : Warm} {pre partialMeter : Meter}
    {fuel : Nat} {events : List Event} {view : View} {output : ByteArray} {fault : Fault} {destinations : List Nat}
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    (context : ReferenceCheckedStackControlStep.DestinationContext (JournalInvariant.modelKind kind) destinations)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites c.target).1 = .ok c.code)
    (_entered : (entry c emptyHash accountsParent before codeParent shouldTransfer).1 = .ok ())
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel
      (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts
      (initial (CallBridge.codeCall c (code pinned) 0) (entry c emptyHash accountsParent before codeParent shouldTransfer).2.storage)
      warm pre = some ((events,.failed fault view partialWarm partialMeter output),finalAccounts))
    (slots : ∀ q, ReferenceStorageView.current parent before.storage c.target q.toByteArray = SystemSpec.worldSlot c.world c.target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code pinned) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (calldata : c.calldata.size < UInt256.size) : ReferenceCheckedFaultClass.caught fault = true := by
  let start := fetched emptyHash accountsParent before codeParent c.target
  have fetchedLoad : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      start.accounts codeParent start.codeWrites c.target).1 = .ok c.code := loaded
  have nonempty : c.code ≠ ByteArray.empty := by
    rw [code pinned]
    cases kind <;> decide +kernel
  have hashNonempty := ReferenceSourceValueTransfer.loaded_nonempty_hash emptyHash accountsParent start codeParent c.target fetchedLoad nonempty
  have afterLoad : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts codeParent
      (entry c emptyHash accountsParent before codeParent shouldTransfer).2.codeWrites c.target).1 = .ok c.code := by
    exact (ReferenceSourceValueTransfer.enter_load emptyHash accountsParent start codeParent c.caller c.target c.target c.value shouldTransfer).trans fetchedLoad
  have afterReads := ReferenceSourceValueTransfer.enter_loaded_reads emptyHash accountsParent start codeParent
    c.caller c.target c.target c.value shouldTransfer (Set.mem_insert c.target _)
  have afterSlots : ReferenceStorageView.Related parent (entry c emptyHash accountsParent before codeParent shouldTransfer).2.storage
      (CallBridge.codeCall c (code pinned) 0).entry.toState := by
    intro q
    change ReferenceStorageView.current parent (ReferenceSourceValueTransfer.enter emptyHash accountsParent start c.caller c.target c.value shouldTransfer).2.storage c.target q.toByteArray = _
    rw [ReferenceSourceValueTransfer.enter_protected_storage emptyHash accountsParent start c.caller c.target c.target c.value shouldTransfer hashNonempty]
    exact (slots q).trans (TransferFrame.codeCall_storage c (code pinned) 0 q).symm
  have replayActual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel
      (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
        (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts codeParent
        (entry c emptyHash accountsParent before codeParent shouldTransfer).2.codeWrites c.target).2
      (initial (CallBridge.codeCall c (code pinned) 0) (entry c emptyHash accountsParent before codeParent shouldTransfer).2.storage)
      warm pre = some ((events,.failed fault view partialWarm partialMeter output),finalAccounts) := by
    have readsExact : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
        (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts codeParent
        (entry c emptyHash accountsParent before codeParent shouldTransfer).2.codeWrites c.target).2 =
        (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts := afterReads
    rw [readsExact]
    exact actual
  exact ReferenceDerivedFailure.caught (CallBridge.codeCall c (code pinned) 0) ReferenceSourceValueTransfer.Account.codeHash
    emptyHash accountsParent (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts codeParent
    (entry c emptyHash accountsParent before codeParent shouldTransfer).2.codeWrites context afterLoad replayActual afterSlots
    (TransferFrame.pinned_codeCall_hasOwner c pinned (code pinned) 0)
    warmRelated grant calldata

/-- The actual pre-transfer journal is the saved snapshot. Runtime failure
restores its four write components, retaining live read/created metadata. -/
theorem settled {Hash LoadError : Type} [DecidableEq Hash]
    {kind : Contract} (c : MessageCall.Context)
    (pinned : ReachableCalls.PinnedCall kind c)
    (emptyHash : Hash) (accountsParent : ReferenceSourceValueTransfer.Parent Hash) (before : ReferenceSourceValueTransfer.Tx Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash LoadError) (shouldTransfer : Bool)
    {parent : ReferenceStorageView.Parent} {warm partialWarm : Warm} {pre partialMeter : Meter}
    {fuel : Nat} {events : List Event} {view : View} {output : ByteArray} {fault : Fault} {destinations : List Nat}
    {finalAccounts : ReferenceAccountLookup.Tx (ReferenceSourceValueTransfer.Account Hash)}
    (context : ReferenceCheckedStackControlStep.DestinationContext (JournalInvariant.modelKind kind) destinations)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      before.accounts codeParent before.codeWrites c.target).1 = .ok c.code)
    (entered : (entry c emptyHash accountsParent before codeParent shouldTransfer).1 = .ok ())
    (actual : ReferenceCheckedAccountEvaluator.eval accountsParent destinations parent ByteArray.empty fuel
      (entry c emptyHash accountsParent before codeParent shouldTransfer).2.accounts
      (initial (CallBridge.codeCall c (code pinned) 0) (entry c emptyHash accountsParent before codeParent shouldTransfer).2.storage)
      warm pre = some ((events,.failed fault view partialWarm partialMeter output),finalAccounts))
    (slots : ∀ q, ReferenceStorageView.current parent before.storage c.target q.toByteArray = SystemSpec.worldSlot c.world c.target q)
    (warmRelated : WarmRelated warm (CallBridge.codeCall c (code pinned) 0).entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000)
    (calldata : c.calldata.size < UInt256.size) :
    let live := {(entry c emptyHash accountsParent before codeParent shouldTransfer).2 with accounts := finalAccounts, storage := view.storage}
    let restored := restore live before
    ∃ receipt,
      ReferenceCheckedFrameOutcome.settle before.storage [] warm (.failed fault view partialWarm partialMeter output) = .returned receipt ∧
      receipt.beforeSettlement = view ∧ receipt.output = ByteArray.empty ∧
      receipt.meter.execution = 0 ∧ receipt.meter.reservoir = partialMeter.baseline ∧
      receipt.meter.spill = 0 ∧ receipt.meter.refund = 0 ∧
      receipt.meter.committedSpill = partialMeter.committedSpill ∧
      receipt.logsForParent = [] ∧ receipt.warmForParent = none ∧
      receipt.storage = restored.storage ∧
      restored.accounts.writes = before.accounts.writes ∧
      restored.codeWrites = before.codeWrites ∧ restored.transient = before.transient ∧
      restored.accounts.reads = finalAccounts.reads ∧
      restored.storage.reads = view.storage.reads ∧ restored.storage.created = view.storage.created ∧
      ∀ p address key, ReferenceStorageView.current p restored.storage address key =
        ReferenceStorageView.current p before.storage address key := by
  have classified := caught c pinned emptyHash accountsParent before codeParent shouldTransfer context loaded entered actual slots warmRelated grant calldata
  refine ⟨ReferenceCheckedFrameOutcome.failure before.storage view partialWarm (ReferenceChildMeter.settle .exceptional partialMeter)
    ByteArray.empty (.exceptional fault),?_,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  · simp only [ReferenceCheckedFrameOutcome.settle,classified,if_true]
  · intro p address key
    rfl

#print axioms caught
#print axioms settled
end Eip8282.Audit.Integrator.ReferencePinnedFailure

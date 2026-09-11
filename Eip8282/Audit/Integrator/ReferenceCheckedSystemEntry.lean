import Eip8282.Audit.Integrator.ProtocolSystemDispatchExtraction
import Eip8282.Audit.Integrator.ReferenceFullGasTotal

/-! Mandatory empty-data SYSTEM entry into the checked account evaluator.
The existing dispatcher supplies caller/value, fresh transaction journal,
empty warmth and both gas pools. Code load remains an independently meaningful
initial source observation; the storage parent is the represented block world.
No ordinary transaction fee/admission rule is applied to SYSTEM. Consumers:
ReferenceCheckedSystemExecution and ReferenceCheckedSystemTotal. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemEntry
open EvmYul EvmYul.EVM
open ReferenceSourceValueTransfer
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

structure Context where
  world : AccountMap .EVM
  genesis : BlockHeader
  blocks : ProcessedBlocks
  header : BlockHeader
  baseFee : UInt256

def call (kind : ReachableCalls.Contract) (c : Context) : MessageCall.Context :=
  ProtocolSystemCalls.call kind c.world c.genesis c.blocks c.header c.baseFee 8503 ByteArray.empty

theorem code (kind : ReachableCalls.Contract) (c : Context) :
    (call kind c).code = Eip8282.Audit.Correspondence.runtimeCode (JournalInvariant.modelKind kind) := by cases kind <;> rfl

def xi (kind : ReachableCalls.Contract) (c : Context) := CallBridge.codeCall (call kind c) (code kind c) 0
def before (Hash : Type) : Tx Hash :=
  ⟨⟨fun _ => none,∅⟩,ProtocolSystemDispatchExtraction.freshTx,fun _ => none,fun _ _ => none⟩
def storageParent (c : Context) := ProtocolSystemDispatchExtraction.blockParent c.world
def meter (kind : ReachableCalls.Contract) (c : Context) :=
  let fields := ProtocolSystemDispatchExtraction.mandatory kind c.baseFee
  ReferenceChildMeter.init fields.executionGasGrant fields.stateGasReservoir

noncomputable def entered {Hash Error : Type} [DecidableEq Hash] (kind : ReachableCalls.Contract)
    (c : Context) (emptyHash : Hash) (accountsParent : Parent Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) :=
  ReferenceSourceValueTransfer.enter emptyHash accountsParent
    (ReferenceSourceDispatch.probe emptyHash accountsParent (before Hash) codeParent
      (ReachableCalls.address kind) (call kind c).value).2
    (call kind c).caller (call kind c).target (call kind c).value true

theorem constructed {deposit exit : TransactionAppendBudget.Receipt} (kind : ReachableCalls.Contract)
    (c : Context) (history : ReleaseCandidate.History deposit exit c.world) :
    ProtocolSystemDispatchExtraction.frame (ProtocolSystemDispatchExtraction.mandatory kind c.baseFee)
      c.world c.genesis c.blocks c.header 8503 = call kind c ∧
    ReleaseCandidate.CallInput kind (call kind c) ∧
    (∀ signature, ReferenceCallEntry.logs (call kind c) true signature = []) ∧
    ReferenceExecutionPotential.potential (meter kind c) = 30000000 := by
  have installed := (ReleaseCandidate.invariants history).2.2.2 kind |>.1
  refine ⟨ProtocolSystemDispatchExtraction.mandatory_call kind c.world c.genesis c.blocks c.header c.baseFee 8503 installed,
    ⟨rfl,rfl,rfl⟩,?_,rfl⟩
  intro signature
  simp [ReferenceCallEntry.logs,call,ProtocolSystemCalls.call,show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl]

theorem ready {Hash Error : Type} [DecidableEq Hash] (kind : ReachableCalls.Contract)
    (c : Context) (emptyHash : Hash) (accountsParent : Parent Hash)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    ReferenceSourceDispatch.probe emptyHash accountsParent (before Hash) codeParent
      (ReachableCalls.address kind) (call kind c).value =
      (.ready (ReachableCalls.runtime kind),ReferenceTransferredFailure.fetched emptyHash accountsParent (before Hash) codeParent (ReachableCalls.address kind)) ∧
    entered kind c emptyHash accountsParent codeParent =
      (.ok (),ReferenceTransferredFailure.fetched emptyHash accountsParent (before Hash) codeParent (ReachableCalls.address kind)) := by
  have probe := ReferenceSourceDispatch.ready_fetched emptyHash accountsParent (before Hash) codeParent kind (call kind c).value loaded
  refine ⟨probe,?_⟩
  unfold entered
  rw [probe]
  simp [ReferenceSourceValueTransfer.enter,call,ProtocolSystemCalls.call]

theorem bindings {deposit exit : TransactionAppendBudget.Receipt} {Hash Error : Type} [DecidableEq Hash]
    (kind : ReachableCalls.Contract) (c : Context) (history : ReleaseCandidate.History deposit exit c.world)
    (emptyHash : Hash) (accountsParent : Parent Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error)
    (loaded : (ReferenceCodeAccountPresence.load ReferenceSourceValueTransfer.Account.codeHash emptyHash accountsParent
      (before Hash).accounts codeParent (before Hash).codeWrites (ReachableCalls.address kind)).1 = .ok (ReachableCalls.runtime kind)) :
    ReferenceStorageView.Related (storageParent c) (entered kind c emptyHash accountsParent codeParent).2.storage (xi kind c).entry.toState ∧
    SystemSpec.HasOwner (xi kind c).entry.toState ∧
    ReferenceSourceReadings.WarmRelated (∅ : ReferenceSourceReadings.Warm) (xi kind c).entry ∧
    ReferenceCheckedStackControlStep.DestinationContext (JournalInvariant.modelKind kind)
      (ReferenceInitialAccess.destinations (call kind c).code) := by
  rw [(ready kind c emptyHash accountsParent codeParent loaded).2]
  have installed := ReleaseCandidate.installed_call history (constructed kind c history).2.1
  refine ⟨?_,TransferFrame.pinned_codeCall_hasOwner (call kind c) installed (code kind c) 0,?_,?_⟩
  · intro k
    change SystemSpec.worldSlot c.world (ReachableCalls.address kind) (ProtocolSystemDispatchExtraction.keyOf k.toByteArray) = _
    rw [ProtocolSystemDispatchExtraction.keyOf_toByteArray]
    exact (TransferFrame.codeCall_storage (call kind c) (code kind c) 0 k).symm
  · intro a k
    change (a,k.toByteArray) ∈ (∅ : ReferenceSourceReadings.Warm) ↔ (∅ : Std.TreeSet _ _).contains (a,k) = true
    simp
  · have hc : (call kind c).code = ReferenceDecodeSites.code (ReferenceRuntimeSites.reference (JournalInvariant.modelKind kind)) := by cases kind <;> rfl
    unfold ReferenceCheckedStackControlStep.DestinationContext
    rw [hc]
    unfold ReferenceInitialAccess.destinations
    rw [ReferenceDecodeSites.scan_eq_sites]
    rfl

#print axioms code
#print axioms constructed
#print axioms ready
#print axioms bindings
end Eip8282.Audit.Integrator.ReferenceCheckedSystemEntry

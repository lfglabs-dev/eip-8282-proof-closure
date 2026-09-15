import Eip8282.Audit.Integrator.Topics.ReferenceAllocated
import Eip8282.Audit.Integrator.Topics.ReferenceChecked3
import Eip8282.Audit.Integrator.Topics.ReferenceRuntime2

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceAccountedReceipt -/

/-! Resource certificates and all three guarantees share the same actual
returned message receipt. Success/REVERT certificates identify the exact trace
and source-allocated terminal payment and an executed-log bound with initial state-credit correction; exceptional failures retain the
actual error/rollback, without claiming a source exceptional replay. -/
namespace Eip8282.Audit.Integrator.ReferenceAccountedReceipt
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Correspondence (runtimeCode)
open ReachableCalls (Contract PinnedCall)
open JournalInvariant (Invariant modelKind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeGasCertificate
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2400000

def Observed {kind : Kind} (c : MessageCall.Context) (codeEq : c.code = runtimeCode kind)
    (steps cap : Nat) (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx) (w : Warm)
    (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
    (gas : UInt256) (substate : Substate) (success : Bool) (out : ByteArray) : Prop :=
  let frame := CallBridge.codeCall c codeEq steps
  if success then
    ∃ post : EVM.State,
      (post.createdAccounts,post.accountMap,post.gasAvailable,post.substate) =
        (created,world,gas,substate) ∧
      SuccessGas kind parent tx.created steps cap frame.entry post out (initial frame tx) w
  else
    world = c.world ∧ substate = c.substate ∧ created = c.created ∧
      ((frame.result = .ok (.revert gas out) ∧
          RevertGas kind parent tx.created steps cap frame.entry gas out (initial frame tx) w) ∨
        ∃ e, frame.result = .error e ∧ (e == ExecutionException.OutOfFuel) = false ∧
          gas = UInt256.ofNat 0 ∧ out = ByteArray.empty)

/-- Attach certificates to the already observed receipt. All runtime witnesses
come from that receipt; only source initial bindings and resources remain inputs. -/
theorem strengthen {kind : Kind} (c : MessageCall.Context) (codeEq : c.code = runtimeCode kind)
    (steps cap : Nat) (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx) (w : Warm)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (observed : ReferenceAllocatedReceipt.Observed c codeEq steps cap parent tx w created world gas substate success out)
    :
    Observed c codeEq steps cap parent tx w created world gas substate success out := by
  cases success with
  | true =>
    obtain ⟨post,payload,viewed⟩ := observed
    exact ⟨post,payload,ReferenceRuntimeGasCertificate.success viewed⟩
  | false =>
    obtain ⟨hw,hs,hc,hcase⟩ := observed
    refine ⟨hw,hs,hc,?_⟩
    rcases hcase with ⟨actual,viewed⟩ | exceptional
    · exact Or.inl ⟨actual,ReferenceRuntimeGasCertificate.revert viewed⟩
    · exact Or.inr exceptional

/-- Same pre-world, full receipt, all three guarantee predicates and complete
source-resource certificates. Canonical history must still produce invariant,
budget and source bindings; AllocatedBoundFor gives sufficient transaction limits plus conditional net-pool accounting, not their
protocol admission. -/
theorem guarantees (kind : Contract) (c : MessageCall.Context) (pinned : PinnedCall kind c)
    (codeEq : c.code = runtimeCode (modelKind kind)) (steps : Nat) (hf : c.fuel = steps+1)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (actual : c.result = .ok (created,world,gas,substate,success,out))
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx) (w : Warm)
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c codeEq steps).entry.toState)
    (warm : WarmRelated w (CallBridge.codeCall c codeEq steps).entry)
    (cap : Nat) (cdfit : c.calldata.size < UInt256.size)
    (threshold : RuntimeMemoryFunding.energy (CallBridge.codeCall c codeEq steps).entry <
      ReferenceMemoryCapacity.cost (cap+1)) (host : 32*cap < 2^System.Platform.numBits)
    {budget : Nat} (invariant : Invariant kind budget c.world) (bound : budget < 2^128) :
    NestedProtectedJournal.Observed kind c created world substate success out ∧
      Observed c codeEq steps cap parent tx w created world gas substate success out := by
  obtain ⟨guards,viewed⟩ := ReferenceAllocatedReceipt.guarantees kind c pinned codeEq steps hf actual
    parent tx w slots warm cap cdfit threshold host invariant bound
  exact ⟨guards,strengthen c codeEq steps cap parent tx w viewed⟩

#print axioms strengthen
#print axioms guarantees
end Eip8282.Audit.Integrator.ReferenceAccountedReceipt

end

section

/-! ## ReferenceFreshStorageEntry -/

/-! Fresh transaction storage is preserved by prepayment, account dispatch
reads and source value entry, including their partial failure states. This is
an initial journal condition, not an assumption about a final gas balance.
Consumer: same-run transaction gas settlement. Python construction/canonical
applicability of the represented fresh journal remain external. -/
namespace Eip8282.Audit.Integrator.ReferenceFreshStorageEntry
open EvmYul EvmYul.EVM ReferenceSourceValueTransfer
open ReferenceRuntimeStateBalance (emptyTx)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private theorem erase_empty (address : AccountAddress) : eraseStorage emptyTx address = emptyTx := by
  simp [eraseStorage,emptyTx]

private theorem modify_empty {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (address : AccountAddress) (balance : UInt256) (fresh : tx.storage = emptyTx) :
    (modifyBalance emptyHash parent tx address balance).storage = emptyTx := by
  unfold modifyBalance
  dsimp only
  split <;> simp only [writeAccount,fresh,erase_empty]

private theorem move_empty {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender recipient : AccountAddress) (value : UInt256) (fresh : tx.storage = emptyTx) :
    (move emptyHash parent tx sender recipient value).2.storage = emptyTx := by
  unfold move
  dsimp only
  split
  · have debit := modify_empty emptyHash parent {tx with accounts := ReferenceAccountLookup.tracked tx.accounts sender} sender
      (UInt256.ofNat ((account emptyHash parent tx sender).balance.toNat-value.toNat)) fresh
    split
    · apply modify_empty
      exact debit
    · exact debit
  · exact fresh

theorem enter {Hash : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (tx : Tx Hash) (sender recipient : AccountAddress) (value : UInt256) (mode : Bool) (fresh : tx.storage = emptyTx) :
    (ReferenceSourceValueTransfer.enter emptyHash parent tx sender recipient value mode).2.storage = emptyTx := by
  unfold ReferenceSourceValueTransfer.enter
  split
  · exact move_empty emptyHash parent tx sender recipient value fresh
  · exact fresh

theorem probe {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (before : Tx Hash) (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (target : AccountAddress) (value : UInt256) :
    (ReferenceSourceDispatch.probe emptyHash parent before codeParent target value).2.storage = before.storage := by
  simp only [ReferenceSourceDispatch.probe,ReferenceSourceDispatch.readTarget]
  repeat' (split <;> try rfl)

theorem allocated {Hash Error : Type} [DecidableEq Hash] (emptyHash : Hash) (parent : Parent Hash)
    (before : Tx Hash) (tx : RefundAccounting.Context) (kind : ReachableCalls.Contract)
    (codeParent : ReferenceCodeAccountPresence.CodeParent Hash Error) (fresh : before.storage = emptyTx) :
    (ReferenceAllocatedEntry.entered emptyHash parent before tx kind codeParent).2.storage = emptyTx := by
  apply enter
  rw [probe,(ReferenceSourcePrepaidCheckpoint.fields emptyHash parent before tx).1,fresh]

#print axioms enter
#print axioms probe
#print axioms allocated
end Eip8282.Audit.Integrator.ReferenceFreshStorageEntry

end

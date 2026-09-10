import Eip8282.Audit.Integrator.ReferenceRuntimeReceipt
import Eip8282.Audit.Integrator.ReferenceRuntimeTerminalPayment

/-! Resource certificates and all three guarantees share the same actual
returned message receipt. Success/REVERT certificates identify the exact trace
and sufficient initial source-meter grants; exceptional failures retain the
actual error/rollback, without claiming a source exceptional replay. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeResourceReceipt
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.Correspondence (runtimeCode)
open ReachableCalls (Contract PinnedCall)
open JournalInvariant (Invariant modelKind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeTerminalPayment
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
      SuccessCertificate kind parent tx.created steps cap frame.entry post out (initial frame tx) w
  else
    world = c.world ∧ substate = c.substate ∧ created = c.created ∧
      ((frame.result = .ok (.revert gas out) ∧
          RevertCertificate kind parent tx.created steps cap frame.entry gas out (initial frame tx) w) ∨
        ∃ e, frame.result = .error e ∧ (e == ExecutionException.OutOfFuel) = false ∧
          gas = UInt256.ofNat 0 ∧ out = ByteArray.empty)

/-- Attach certificates to the already observed receipt. All runtime witnesses
come from that receipt; only source initial bindings and resources remain inputs. -/
theorem strengthen {kind : Kind} (c : MessageCall.Context) (codeEq : c.code = runtimeCode kind)
    (steps cap : Nat) (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx) (w : Warm)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (observed : ReferenceRuntimeReceipt.Observed c codeEq steps parent tx created world gas substate success out)
    (warm : WarmRelated w (CallBridge.codeCall c codeEq steps).entry)
    (threshold : RuntimeMemoryFunding.energy (CallBridge.codeCall c codeEq steps).entry <
      ReferenceMemoryCapacity.cost (cap+1)) :
    Observed c codeEq steps cap parent tx w created world gas substate success out := by
  let frame := CallBridge.codeCall c codeEq steps
  have hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) frame.entry := by
    cases kind
    · exact ⟨frame.code_pinned,Or.inl RuntimeExecutionScope.deposit.entry⟩
    · exact ⟨frame.code_pinned,Or.inl RuntimeExecutionScope.exit.entry⟩
  cases success with
  | true =>
    obtain ⟨post,payload,viewed⟩ := observed
    exact ⟨post,payload,ReferenceRuntimeTerminalPayment.success viewed hat w warm rfl threshold⟩
  | false =>
    obtain ⟨hw,hs,hc,hcase⟩ := observed
    refine ⟨hw,hs,hc,?_⟩
    rcases hcase with ⟨actual,viewed⟩ | exceptional
    · exact Or.inl ⟨actual,ReferenceRuntimeTerminalPayment.revert viewed hat w warm rfl threshold⟩
    · exact Or.inr exceptional

/-- Same pre-world, full receipt, all three guarantee predicates and complete
source-resource certificates. Canonical history must still produce invariant,
budget and source bindings; PaymentFor gives sufficient grants, not their
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
  obtain ⟨guards,viewed⟩ := ReferenceRuntimeReceipt.guarantees kind c pinned codeEq steps hf actual
    parent tx slots cap cdfit threshold host invariant bound
  exact ⟨guards,strengthen c codeEq steps cap parent tx w viewed warm threshold⟩

#print axioms strengthen
#print axioms guarantees
end Eip8282.Audit.Integrator.ReferenceRuntimeResourceReceipt

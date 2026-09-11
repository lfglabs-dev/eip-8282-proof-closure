import Eip8282.Audit.Integrator.ReferenceRuntimeEndpoint
import Eip8282.Audit.Integrator.CallRevert
import Eip8282.Audit.Integrator.NestedProtectedJournal

/-! The three guarantee parents and source-shaped observations consume the
same actual message receipt. Successful and REVERT executions carry computed
views; exceptional failures carry the exact restored journal and error. This
does not equate source exceptional gas behaviour or derive canonical admission. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeReceipt
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Correspondence (runtimeCode)
open ReferenceRuntimeView ReferenceRuntimeCompletion
open ReachableCalls (Contract Transition PinnedCall)
open JournalInvariant (Invariant modelKind)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem xi_revert {kind : Kind} (c : XiCall kind) {gas : UInt256} {out : ByteArray}
    (actual : c.result = .ok (.revert gas out))
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (cap : Nat)
    (cdfit : c.env.calldata.size < UInt256.size)
    (threshold : RuntimeMemoryFunding.energy c.entry < ReferenceMemoryCapacity.cost (cap+1))
    (host : 32*cap < 2^System.Platform.numBits) :
    Reverted (kind := kind) parent c.fuel c.entry gas out (initial c tx) := by
  have hx := CallRevert.xi_revert_X c actual
  have hj : D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩ = jumpdestsOf kind := by
    cases kind
    · exact deposit_D_J
    · exact exit_D_J
  have hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) c.entry := by
    cases kind
    · exact ⟨c.code_pinned,Or.inl RuntimeExecutionScope.deposit.entry⟩
    · exact ⟨c.code_pinned,Or.inl RuntimeExecutionScope.exit.entry⟩
  rw [← hj] at hx
  exact ReferenceRuntimeCompletion.revert hx hat (initial c tx)
    (initial_related c parent tx slots owner) cdfit threshold host

def Observed {kind : Kind} (c : MessageCall.Context) (codeEq : c.code = runtimeCode kind)
    (steps : Nat) (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (created : Std.TreeSet AccountAddress compare) (world : AccountMap .EVM)
    (gas : UInt256) (substate : Substate) (success : Bool) (out : ByteArray) : Prop :=
  let frame := CallBridge.codeCall c codeEq steps
  if success then
    ∃ post : EVM.State,
      (post.createdAccounts,post.accountMap,post.gasAvailable,post.substate) =
        (created,world,gas,substate) ∧
      Successful (kind := kind) parent steps frame.entry post out (initial frame tx)
  else
    world = c.world ∧ substate = c.substate ∧ created = c.created ∧
      ((frame.result = .ok (.revert gas out) ∧
          Reverted (kind := kind) parent steps frame.entry gas out (initial frame tx)) ∨
        ∃ e, frame.result = .error e ∧ (e == ExecutionException.OutOfFuel) = false ∧
          gas = UInt256.ofNat 0 ∧ out = ByteArray.empty)

/-- Source observations of an actual returned message call, including rollback.
The installed target supplies owner existence through the actual value transfer. -/
theorem observe (kind : Contract) (c : MessageCall.Context) (pinned : PinnedCall kind c)
    (codeEq : c.code = runtimeCode (modelKind kind)) (steps : Nat) (hf : c.fuel = steps+1)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (actual : c.result = .ok (created,world,gas,substate,success,out))
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c codeEq steps).entry.toState)
    (cap : Nat) (cdfit : c.calldata.size < UInt256.size)
    (threshold : RuntimeMemoryFunding.energy (CallBridge.codeCall c codeEq steps).entry <
      ReferenceMemoryCapacity.cost (cap+1)) (host : 32*cap < 2^System.Platform.numBits) :
    Observed c codeEq steps parent tx created world gas substate success out := by
  have owner := TransferFrame.pinned_codeCall_hasOwner c pinned codeEq steps
  cases success with
  | true =>
    exact ReferenceRuntimeEndpoint.theta_success c codeEq steps hf actual
      parent tx slots owner cap cdfit threshold host
  | false =>
    obtain ⟨hw,hs,hc,hcase⟩ := CallRevert.false_cases c actual
    refine ⟨hw,hs,hc,?_⟩
    rw [CallBridge.execution_eq_codeCall c codeEq steps hf] at hcase
    rcases hcase with hr | he
    · exact Or.inl ⟨hr,xi_revert (CallBridge.codeCall c codeEq steps) hr
        parent tx slots owner cap cdfit threshold host⟩
    · exact Or.inr he

/-- All three public guarantees and the runtime observations share one complete
receipt. Internal queue/control domains are derived from the history invariant;
its history and funding producers remain required at the protocol boundary. -/
theorem guarantees (kind : Contract) (c : MessageCall.Context) (pinned : PinnedCall kind c)
    (codeEq : c.code = runtimeCode (modelKind kind)) (steps : Nat) (hf : c.fuel = steps+1)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool} {out : ByteArray}
    (actual : c.result = .ok (created,world,gas,substate,success,out))
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c codeEq steps).entry.toState)
    (cap : Nat) (cdfit : c.calldata.size < UInt256.size)
    (threshold : RuntimeMemoryFunding.energy (CallBridge.codeCall c codeEq steps).entry <
      ReferenceMemoryCapacity.cost (cap+1)) (host : 32*cap < 2^System.Platform.numBits)
    {budget : Nat} (invariant : Invariant kind budget c.world) (bound : budget < 2^128) :
    NestedProtectedJournal.Observed kind c created world substate success out ∧
      Observed c codeEq steps parent tx created world gas substate success out := by
  let t : Transition kind c.world world :=
    { call := c, pinned := pinned, pre := rfl, created := created, gas := gas,
      substate := substate, success := success, output := out, executed := actual }
  exact ⟨JournalGuarantees.completed t invariant bound cdfit,
    observe kind c pinned codeEq steps hf actual parent tx slots cap cdfit threshold host⟩

#print axioms xi_revert
#print axioms observe
#print axioms guarantees
end Eip8282.Audit.Integrator.ReferenceRuntimeReceipt

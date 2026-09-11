import Eip8282.Audit.Integrator.ReferenceRuntimeCompletion
import Eip8282.Audit.Integrator.CallSuccess
import Eip8282.Audit.Integrator.WorldNonempty

/-! Source-shaped observations of the very runtime execution published by a
successful message call. Entry and terminal owner preservation discharge the
empty-world settlement fallback. Initial storage bindings and a resource/host
threshold remain explicit; no source interpreter or source gas parity is assumed. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeEndpoint
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Correspondence (runtimeCode)
open ReferenceRuntimeView ReferenceRuntimeCompletion
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private theorem terminal_owner {parent : ReferenceStorageView.Parent} {v : View}
    {post : EVM.State} {out : ByteArray} {op : Operation .EVM}
    (terminal : SuccessEnd parent v post out op) : SystemSpec.HasOwner post.toState := by
  cases terminal with
  | stopped related _ => exact related.owner
  | returned _ related _ => exact related.owner

theorem nonempty {kind : Kind} {parent : ReferenceStorageView.Parent}
    {fuel : Nat} {pre post : EVM.State} {out : ByteArray} {initial : View}
    (observed : Successful (kind := kind) parent fuel pre post out initial) :
    (post.accountMap == ∅) = false := by
  obtain ⟨t,finish,_,_,_,terminal⟩ := observed
  exact WorldNonempty.beq_empty_false_of_hasOwner (terminal_owner terminal)

/-- Recover a complete viewed execution from actual Xi success, preserving
every published field. The memory bound is imposed only on initial resources. -/
theorem xi_success {kind : Kind} (c : XiCall kind)
    {published : Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate}
    {out : ByteArray} (actual : c.result = .ok (.success published out))
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (cap : Nat)
    (cdfit : c.env.calldata.size < UInt256.size)
    (threshold : RuntimeMemoryFunding.energy c.entry < ReferenceMemoryCapacity.cost (cap+1))
    (host : 32*cap < 2^System.Platform.numBits) :
    ∃ post : EVM.State,
      (post.createdAccounts,post.accountMap,post.gasAvailable,post.substate) = published ∧
      Successful (kind := kind) parent c.fuel c.entry post out (initial c tx) ∧
      (post.accountMap == ∅) = false := by
  obtain ⟨post,payload,hx⟩ := SuccessInversion.xi_success_X c actual
  have hj : D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩ = jumpdestsOf kind := by
    cases kind
    · exact deposit_D_J
    · exact exit_D_J
  have hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) c.entry := by
    cases kind
    · exact ⟨c.code_pinned,Or.inl RuntimeExecutionScope.deposit.entry⟩
    · exact ⟨c.code_pinned,Or.inl RuntimeExecutionScope.exit.entry⟩
  rw [← hj] at hx
  have viewed := ReferenceRuntimeCompletion.success hx hat (initial c tx)
    (initial_related c parent tx slots owner) cdfit threshold host
  exact ⟨post,payload,viewed,nonempty viewed⟩

/-- Actual Theta success produces its actual complete viewed code frame. The
published journal equals this frame's final journal: no fallback premise and
no independently selected final state is consumed. -/
theorem theta_success {kind : Kind} (c : MessageCall.Context)
    (codeEq : c.code = runtimeCode kind) (steps : Nat) (hf : c.fuel = steps+1)
    {created : Std.TreeSet AccountAddress compare} {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {out : ByteArray}
    (actual : c.result = .ok (created,world,gas,substate,true,out))
    (parent : ReferenceStorageView.Parent) (tx : ReferenceStorageView.Tx)
    (slots : ReferenceStorageView.Related parent tx (CallBridge.codeCall c codeEq steps).entry.toState)
    (owner : SystemSpec.HasOwner (CallBridge.codeCall c codeEq steps).entry.toState)
    (cap : Nat) (cdfit : c.calldata.size < UInt256.size)
    (threshold : RuntimeMemoryFunding.energy (CallBridge.codeCall c codeEq steps).entry <
      ReferenceMemoryCapacity.cost (cap+1))
    (host : 32*cap < 2^System.Platform.numBits) :
    ∃ post : EVM.State,
      (post.createdAccounts,post.accountMap,post.gasAvailable,post.substate) =
        (created,world,gas,substate) ∧
      Successful (kind := kind) parent steps (CallBridge.codeCall c codeEq steps).entry post out
        (initial (CallBridge.codeCall c codeEq steps) tx) := by
  obtain ⟨ew,es,he,hw,hs⟩ := CallSuccess.codeCall_of_success c codeEq steps hf actual
  obtain ⟨post,hp,hview,hne⟩ := xi_success (CallBridge.codeCall c codeEq steps) he
    parent tx slots owner cap cdfit threshold host
  have fields := Prod.mk.inj hp
  have worldEq : post.accountMap = ew := (Prod.mk.inj fields.2).1
  have ne : (ew == ∅) = false := by rw [← worldEq]; exact hne
  simp only [ne,Bool.false_eq_true,ite_false] at hw hs
  rw [hw,hs]
  exact ⟨post,hp,hview⟩

#print axioms nonempty
#print axioms xi_success
#print axioms theta_success
end Eip8282.Audit.Integrator.ReferenceRuntimeEndpoint

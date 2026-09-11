import Eip8282.Audit.Integrator.ReferenceSystemTrace
import Eip8282.Audit.Integrator.EndpointState
import Eip8282.Audit.Integrator.CallBridge
import Eip8282.Audit.Integrator.WorldNonempty

/-! Exact enclosing endpoints of one completed SYSTEM execution. The same
Completed witness supplies the full Ξ success tuple and actual output. Its
Observed terminal owner excludes Θ's empty-world fallback, so the message-call
result commits that very tuple. No second run, supplied nonempty world, or
assumed reference interpreter execution is used. Initial world/code/context
bindings and construction of Observed remain the caller's producers. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemEndpoint
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Correspondence (runtimeCode)
open SystemExecutionResources ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- Publish all fields of the actual successful Ξ endpoint, not just output. -/
theorem xi_result {kind : Kind} {steps cap outputBytes : Nat} (c : XiCall kind)
    (h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes c.fuel c.entry) :
    c.result = .ok (.success
      (h.finalState.createdAccounts,h.finalState.accountMap,h.finalState.gasAvailable,h.finalState.substate)
      h.output) := by
  apply EndpointState.result_of_X_success c
  have hj : D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩ = jumpdestsOf kind := by
    cases kind
    · exact deposit_D_J
    · exact exit_D_J
  rw [← hj]
  exact h.success

/-- The observed terminal owner is derived along this completed trace; its
account lookup rules out the actual boolean empty-map branch. -/
theorem nonempty {kind : Kind} {parent : ReferenceStorageView.Parent}
    {steps cap outputBytes fuel : Nat} {pre : EVM.State} {initial : View}
    (h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes fuel pre)
    (observed : ReferenceSystemTrace.Observed (parent := parent) h initial) :
    (h.finalState.accountMap == ∅) = false := by
  obtain ⟨_,_,_,_,_,_,_,_,terminal,_⟩ := observed
  exact WorldNonempty.beq_empty_false_of_hasOwner terminal.owner

/-- Bind this same completed code frame to its actual transferred-world Θ
context. Fuel consumes the existing Θ wrapper exactly once. -/
theorem commits {kind : Kind} {parent : ReferenceStorageView.Parent}
    {steps cap outputBytes : Nat} {initial : View}
    (c : MessageCall.Context) (codeEq : c.code = runtimeCode kind)
    (evalFuel : Nat) (hf : c.fuel = evalFuel+1)
    (h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes
      (CallBridge.codeCall c codeEq evalFuel).fuel (CallBridge.codeCall c codeEq evalFuel).entry)
    (observed : ReferenceSystemTrace.Observed (parent := parent) h initial) :
    c.result = .ok
      (h.finalState.createdAccounts,h.finalState.accountMap,h.finalState.gasAvailable,
        h.finalState.substate,true,h.output) := by
  exact CallBridge.commits_endpoint c codeEq evalFuel hf
    h.finalState.createdAccounts h.finalState.accountMap h.finalState.gasAvailable
    h.finalState.substate h.output
    (xi_result (CallBridge.codeCall c codeEq evalFuel) h) (nonempty h observed)

#print axioms xi_result
#print axioms nonempty
#print axioms commits
end Eip8282.Audit.Integrator.ReferenceSystemEndpoint

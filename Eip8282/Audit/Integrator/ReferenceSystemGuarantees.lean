import Eip8282.Audit.Integrator.ReferenceSystemEntry
import Eip8282.Audit.Integrator.ReferenceSystemEndpoint
import Eip8282.Audit.Integrator.NestedProtectedJournal
import Eip8282.Audit.Integrator.SystemJournal

/-! The source-shaped SYSTEM trace and payment feed the three actual receipt
guarantees through one Completed witness. The initial journal invariant is a
history-producer input here; canonical reachability and source interpretation
are not replaced by assuming that input is protocol-valid. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemGuarantees
open EvmYul EvmYul.EVM
open ReachableCalls (Contract Transition PinnedCall)
open JournalInvariant (Invariant modelKind)
open SystemExecutionResources ReferenceRuntimeView SystemMeterResources
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- The exact successful message receipt is constructed, then consumed by all
three guarantee parents. No independent receipt or poststate is supplied. -/
theorem attach (kind : Contract) (c : MessageCall.Context)
    (pinned : PinnedCall kind c)
    (codeEq : c.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind))
    (evalFuel : Nat) (hf : c.fuel = evalFuel+1)
    {steps cap outputBytes : Nat} {parent : ReferenceStorageView.Parent} {initial : View}
    (h : Completed (ReferenceRuntimeSites.runtime (modelKind kind)) steps cap outputBytes
      (CallBridge.codeCall c codeEq evalFuel).fuel (CallBridge.codeCall c codeEq evalFuel).entry)
    (observed : ReferenceSystemTrace.Observed (parent := parent) h initial)
    {budget : Nat} (invariant : Invariant kind budget c.world)
    (bound : budget < 2^128) (fit : c.calldata.size < UInt256.size) :
    c.result = .ok (h.finalState.createdAccounts,h.finalState.accountMap,
      h.finalState.gasAvailable,h.finalState.substate,true,h.output) ∧
    NestedProtectedJournal.Observed kind c h.finalState.createdAccounts h.finalState.accountMap
      h.finalState.substate true h.output := by
  have hr := ReferenceSystemEndpoint.commits c codeEq evalFuel hf h observed
  let t : Transition kind c.world h.finalState.accountMap :=
    { call := c, pinned := pinned, pre := rfl, created := h.finalState.createdAccounts,
      gas := h.finalState.gasAvailable, substate := h.finalState.substate,
      success := true, output := h.output, executed := hr }
  exact ⟨hr,JournalGuarantees.completed t invariant bound fit⟩

/-- Preserve the SYSTEM journal invariant together with the same actual
receipt, three guarantees, source-shaped trace and paid event sequence. -/
theorem system (kind : Contract) (c : MessageCall.Context)
    (pinned : PinnedCall kind c)
    (codeEq : c.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind))
    (evalFuel : Nat) (hf : c.fuel = evalFuel+1)
    {steps cap outputBytes : Nat} {parent : ReferenceStorageView.Parent} {initial : View}
    (h : Completed (ReferenceRuntimeSites.runtime (modelKind kind)) steps cap outputBytes
      (CallBridge.codeCall c codeEq evalFuel).fuel (CallBridge.codeCall c codeEq evalFuel).entry)
    (observed : ReferenceSystemTrace.Observed (parent := parent) h initial)
    (inputs : Inputs) (meter : ReferenceStorageGas.Meter) (paid : Paid inputs h meter)
    (caller : c.caller = Eip8282.Audit.EvmRunner.sysAddr) (value : c.value = ⟨0⟩)
    {budget : Nat} (invariant : Invariant kind budget c.world)
    (bound : budget < 2^128) (fit : c.calldata.size < UInt256.size) :
    c.result = .ok (h.finalState.createdAccounts,h.finalState.accountMap,
      h.finalState.gasAvailable,h.finalState.substate,true,h.output) ∧
    NestedProtectedJournal.Observed kind c h.finalState.createdAccounts h.finalState.accountMap
      h.finalState.substate true h.output ∧
    Invariant kind budget h.finalState.accountMap ∧
    ReferenceSystemTrace.Observed (parent := parent) h initial ∧ Paid inputs h meter := by
  obtain ⟨hr,hg⟩ := attach kind c pinned codeEq evalFuel hf h observed invariant bound fit
  let t : Transition kind c.world h.finalState.accountMap :=
    { call := c, pinned := pinned, pre := rfl, created := h.finalState.createdAccounts,
      gas := h.finalState.gasAvailable, substate := h.finalState.substate,
      success := true, output := h.output, executed := hr }
  exact ⟨hr,hg,SystemJournal.preserves t caller value fit bound invariant,observed,paid⟩

#print axioms attach
#print axioms system
end Eip8282.Audit.Integrator.ReferenceSystemGuarantees

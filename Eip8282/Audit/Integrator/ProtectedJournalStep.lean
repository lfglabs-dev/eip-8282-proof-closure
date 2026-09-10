import Eip8282.Audit.Integrator.JournalInvariant
import Eip8282.Audit.Integrator.NestedJournalBudget

/-!
# Atomic protected calls consume their actual execution's work budget

The storage transition and its charged event are obtained from the same
message-call receipt and inner execution certificate. Successful nonempty user
calls force a marked append event; rejected calls, getters and SYSTEM calls
have zero append weight. Lifting to the entire execution budget accommodates
rolled-back work without interpreting it as persistent records.
-/
namespace Eip8282.Audit.Integrator.ProtectedJournalStep
open EvmYul EvmYul.EVM
open NestedEvents MessageCall CallBridge
open JournalInvariant (Invariant modelKind)
open ReachableCalls (Contract Transition)
open Eip8282.Audit.Correspondence (runtimeCode)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def executionRequest (c : Context) : Request :=
  .xi c.fuel
    { created := c.created, genesis := c.genesis, blocks := c.blocks,
      world := c.entryWorld, original := c.originalWorld, gas := c.gas,
      substate := c.substate, env := c.environment }

theorem executionRequest_eval (c : Context) : (executionRequest c).eval = c.execution := rfl

private theorem executionRequest_codeCall (c : Context) {kind : Eip8282.Audit.Model.Kind}
    (hc : c.code = runtimeCode kind) (steps : Nat) (hf : c.fuel = steps+1) :
    executionRequest c = rootXi (codeCall c hc steps) := by
  unfold executionRequest rootXi rootXiArgs codeCall
  rw [hf]

/-- Actual success derives the calldata shape needed by the append-event
producer. Only the independently stated size-fit and ordinary-value inputs
are consumed; no queue state or fee completion is assumed here. -/
theorem successful_nonempty_size (kind : Contract) (c : Context)
    (hc : c.code = runtimeCode (modelKind kind))
    (hu : c.caller ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hv : c.apparentValue = c.value) (hd : c.calldata.size < UInt256.size)
    (hn : c.calldata.size ≠ 0)
    {created : Created} {world : World} {gas : UInt256} {substate : Substate} {out : ByteArray}
    (hr : c.result = .ok (created,world,gas,substate,true,out)) :
    c.calldata.size = match modelKind kind with | .deposit => 184 | .exit => 48 := by
  cases kind with
  | deposit =>
    obtain ⟨_,_,_,_,h⟩ := SuccessfulUser.deposit_admission c hc hu hv hd hr
    rcases h with h | h
    · exact False.elim (hn h.1)
    · exact h.1
  | exit =>
    obtain ⟨_,_,_,_,h⟩ := SuccessfulUser.exit_admission c hc hu hv hd hr
    rcases h with h | h
    · exact False.elim (hn h.1)
    · exact h.1

theorem weight_le_events {kind : Contract} {before after : World}
    (t : Transition kind before after) (ha : ConcreteHistory.Allowed t.call)
    {tree : EventTree} (cert : Cert (executionRequest t.call) t.call.execution tree) :
    ConcreteHistory.weight t.call t.success ≤ tree.count := by
  by_cases hu : t.call.caller = Eip8282.Audit.EvmRunner.sysAddr
  · simp only [ConcreteHistory.weight, if_pos hu, Nat.zero_le]
  by_cases hs : t.success = true ∧ t.call.calldata.size ≠ 0
  · have hr := t.executed
    rw [hs.1] at hr
    have hc : t.call.code = runtimeCode (modelKind kind) := by
      cases kind <;> exact t.pinned.code
    have hsize := successful_nonempty_size kind t.call hc hu t.pinned.ordinaryValue ha.1 hs.2 hr
    have hf : t.call.fuel = (t.call.fuel-1)+1 := by
      have h := SuccessfulQuote.positive_fuel t.call hr
      omega
    obtain ⟨ew,es,he,_,_⟩ := CallSuccess.codeCall_of_success t.call hc (t.call.fuel-1) hf hr
    unfold executionRequest at cert
    rw [hf] at cert
    change Cert (rootXi (codeCall t.call hc (t.call.fuel-1))) t.call.execution tree at cert
    obtain ⟨event,_,_,hm⟩ := successful_append_address
      (codeCall t.call hc (t.call.fuel-1)) hu (by cases kind <;> exact hsize) he cert
    have hp : 0 < tree.occurrences.length := List.length_pos_of_mem hm
    rw [EventTree.occurrences_length] at hp
    simp only [ConcreteHistory.weight, if_neg hu, UserStateInvariant.weight, if_pos hs]
    omega
  · simp only [ConcreteHistory.weight, if_neg hu, UserStateInvariant.weight, if_neg hs, Nat.zero_le]

/-- The actual inner certificate supplies the accounting extension. No
assumed aggregate charge or post-state is introduced at this journal step. -/
theorem preserves {kind : Contract} {before after : World}
    (t : Transition kind before after) (ha : ConcreteHistory.Allowed t.call)
    {tree : EventTree} (cert : Cert (executionRequest t.call) t.call.execution tree)
    {budget : Nat} (hb : budget < 2^128) (hi : Invariant kind budget before) :
    Invariant kind (budget + tree.count) after :=
  JournalInvariant.mono (JournalInvariant.protected_call t ha hb hi)
    (Nat.add_le_add_left (weight_le_events t ha cert) budget)

#print axioms executionRequest_eval
#print axioms successful_nonempty_size
#print axioms weight_le_events
#print axioms preserves
end Eip8282.Audit.Integrator.ProtectedJournalStep

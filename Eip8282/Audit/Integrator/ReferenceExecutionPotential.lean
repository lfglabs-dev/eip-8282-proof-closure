import Eip8282.Audit.Integrator.Topics.ReferenceCall

/-! Execution gas plus outstanding/committed state spill tracks executable
work independently of the sign of net state usage. Reservoir state credits
cannot create this potential. Actual source frame extraction and global call
ordering still have to supply the transitions; no foreign interpreter parity
or fresh empty storage premise is required by these local identities. -/
namespace Eip8282.Audit.Integrator.ReferenceExecutionPotential
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings
open ReferenceRuntimeReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceMeterBoundary ReferenceChildMeter ReferenceCallGrant
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def potential (m : Meter) : Nat := m.execution+m.spill+m.committedSpill

theorem paid_work {events : List Event} {pre post : Meter}
    (h : runFull events pre = some post) :
    (potential pre : Int)-potential post = (events.map ReferenceMeterConservation.actualExec).sum := by
  have hm := accounting h 0
  simp only [potential,pools,netUsed] at hm ⊢
  omega

/-- Executed logs remain bounded even when this frame starts with refundable
storage bought by another frame. No global state-potential sign is a premise. -/
theorem executed_logs {kind : Kind} {p : Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v last : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event} {meter final : Meter}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post last finalWarm events)
    (amount : Nat) (paid : runFull (events++[.ordinary amount]) meter = some final) :
    (375*ReferenceRuntimeGasBalance.logCount trace : Int) ≤ (potential meter : Int)-potential final := by
  have payment := paid_work paid
  have logs := ReferenceRuntimeGasBalance.log_cost h
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    ReferenceMeterConservation.actualExec,add_zero] at payment
  omega

theorem restore_preserves (m : Meter) : potential (restore m) = potential m := by
  simp only [potential,restore]
  omega

theorem commit_preserves {pre post : Meter} (h : ReferenceMeterRollback.commit pre = some post) : potential post = potential pre := by
  unfold ReferenceMeterRollback.commit at h
  split at h
  · cases h
    simp only [potential]
    omega
  · contradiction

theorem entry_preserves {pre post : Meter} {grant : Nat}
    (h : restoreToEntry grant pre = some post) : potential post = potential pre := by
  unfold restoreToEntry at h
  split at h
  · cases h
    simp only [potential]
    omega
  · contradiction

theorem settle_nonincrease (outcome : Outcome) (m : Meter) : potential (settle outcome m) ≤ potential m := by
  cases outcome
  · exact Nat.le_refl _
  · exact le_of_eq (restore_preserves m)
  · simp only [settle,restore,potential]
    omega

/-- Source merge and success-only spill repayment conserve the sum across
parent and child. The child committed-spill assertion comes from incorporation. -/
theorem incorporate_preserves {parent child post : Meter} {failed : Bool}
    (h : incorporate parent child failed = some post) :
    potential post = potential parent+potential child := by
  have hm := incorporate_accounting h 0
  simp only [potential,pools,netUsed] at hm ⊢
  omega

theorem credit_preserves (m : Meter) (amount : Nat) :
    potential (ReferenceCallChildBoundary.credit m amount) = potential m := by
  simp only [ReferenceCallChildBoundary.credit,core,update,ReferenceStorageGas.creditState,potential]
  omega

/-- The stipend is an explicit term in a postcharge split; the earlier CALL
value charge must cover it in the whole opcode's resource accounting. -/
theorem split_potential (hasValue : Bool) (requested : UInt256) (charged : Meter) :
    potential (split hasValue requested charged).parent+(split hasValue requested charged).childExecution =
      potential charged+stipend hasValue := by
  simp only [split,maximum,potential]
  omega

#print axioms paid_work
#print axioms executed_logs
#print axioms restore_preserves
#print axioms commit_preserves
#print axioms entry_preserves
#print axioms settle_nonincrease
#print axioms incorporate_preserves
#print axioms credit_preserves
#print axioms split_potential
end Eip8282.Audit.Integrator.ReferenceExecutionPotential

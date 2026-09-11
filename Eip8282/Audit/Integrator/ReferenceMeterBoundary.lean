import Eip8282.Audit.Integrator.ReferenceMeterRollback
import Eip8282.Audit.Integrator.ReferenceRuntimeGasBalance

/-! Bind protected-runtime meter payments to the full source frame's rollback
fields. Protected opcodes never commit a new state-gas baseline; ordinary
rollback preserves the prior committed charges and cancels this frame's state
charge/refund balance. These are source-meter identities, not a claim that an
arbitrary outer interpreter has constructed the corresponding storage journal. -/
namespace Eip8282.Audit.Integrator.ReferenceMeterBoundary
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings
open ReferenceRuntimeReadings ReferenceMeterPath ReferenceMeterRollback
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def core (m : Meter) : ReferenceStorageGas.Meter :=
  {execution := m.execution,reservoir := m.reservoir,spill := m.spill,refund := m.refund}

def update (m : Meter) (c : ReferenceStorageGas.Meter) : Meter :=
  {m with execution := c.execution,reservoir := c.reservoir,spill := c.spill,refund := c.refund}

def runFull (events : List Event) (m : Meter) : Option Meter :=
  (run events (core m)).map (update m)

/-- Lift the exact successful ordered core payments. Baseline and prior
committed spill stay fixed throughout the protected instruction sequence. -/
theorem accounting {events : List Event} {pre post : Meter}
    (h : runFull events pre = some post) (grant : Nat) :
    pools pre-pools post = (events.map ReferenceMeterConservation.actualExec).sum+
      netUsed grant post-netUsed grant pre ∧
    netUsed grant post-netUsed grant pre = (events.map ReferenceMeterConservation.stateDelta).sum ∧
    post.baseline = pre.baseline ∧ post.committedSpill = pre.committedSpill := by
  unfold runFull at h
  cases hr : run events (core pre) with
  | none => simp only [hr,Option.map_none] at h; contradiction
  | some final =>
    simp only [hr,Option.map_some,Option.some.injEq] at h
    subst post
    have hc := ReferenceMeterConservation.run_balance hr
    simp [core,update,pools,netUsed,ReferenceMeterConservation.pools,
      ReferenceMeterConservation.stateBalance] at hc ⊢
    omega

/-- At a frame baseline, ordinary rollback cancels exactly the newly accrued
state balance. Earlier committed charges survive; executed work remains paid. -/
theorem rollback_accounting {events : List Event} {pre post : Meter}
    (h : runFull events pre = some post) (grant : Nat)
    (baseline : pre.baseline = pre.reservoir) (spill : pre.spill = 0) :
    netUsed grant (restore post) = netUsed grant pre ∧
    pools pre-pools (restore post) = (events.map ReferenceMeterConservation.actualExec).sum := by
  have payment := accounting h grant
  have rolled := restore_accounting post grant
  have initial : netUsed grant pre = (grant : Int)-pre.baseline+pre.committedSpill := by
    simp only [netUsed,baseline,spill]
    omega
  omega

/-- Both executed LOG0 and the terminal charge remain paid after this frame's
state gas is restored. Logs themselves remain cancelled by the separate
journal theorem; this bound never calls them retained records. -/
theorem reverted_logs {kind : Kind} {p : Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event} {meter final : Meter}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post finish finalWarm events)
    (amount : Nat) (paid : runFull (events++[.ordinary amount]) meter = some final)
    (grant : Nat) (baseline : meter.baseline = meter.reservoir) (spill : meter.spill = 0) :
    (375*ReferenceRuntimeGasBalance.logCount trace : Int) ≤ pools meter-pools (restore final) := by
  have accounting := (rollback_accounting paid grant baseline spill).2
  have logs := ReferenceRuntimeGasBalance.log_cost h
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    ReferenceMeterConservation.actualExec,add_zero] at accounting
  omega

#print axioms accounting
#print axioms rollback_accounting
#print axioms reverted_logs
end Eip8282.Audit.Integrator.ReferenceMeterBoundary

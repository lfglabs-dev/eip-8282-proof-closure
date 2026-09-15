import Eip8282.Audit.Integrator.Topics.ReferenceRuntime2
import Eip8282.Audit.Integrator.Topics.ReferenceStorage

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceMeterRollback -/

/-! Literal source-shaped frame meter and rollback accounting. Amsterdam EL
0cc100eb190b64b23baba72dac0165652eaec252 vm/gas.py:270-337,469-601,
SHA256 41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c,
archived in audit/receipts/direct-reference-admission-sources-20260910.json.
Source assertions are explicit Option guards. State quantities are nonnegative
unbounded Uint values; signed net usage is deliberately not truncated.
This is arithmetic of an audited transcription, not a Python execution proof
or a relation to an actual nested frame, storage snapshot or refund provenance.
The existing simplified payment Meter is unchanged. -/
namespace Eip8282.Audit.Integrator.ReferenceMeterRollback
set_option autoImplicit false

structure Meter where
  execution : Nat
  reservoir : Nat
  baseline : Nat
  spill : Nat
  committedSpill : Nat
  refund : Int
  deriving DecidableEq, Repr

def pools (m : Meter) : Int := (m.execution : Int)+m.reservoir

/-- The expression returned by tx_state_gas_used, before its baseline assertion. -/
def netUsed (grant : Nat) (m : Meter) : Int :=
  (grant : Int)-m.reservoir+m.spill+m.committedSpill

def checkedNetUsed (grant : Nat) (m : Meter) : Option Int :=
  if m.baseline ≤ grant then some (netUsed grant m) else none

def commit (m : Meter) : Option Meter :=
  if m.reservoir ≤ m.baseline then
    some {m with
      committedSpill := m.committedSpill+m.spill
      baseline := m.reservoir
      spill := 0}
  else none

def restore (m : Meter) : Meter :=
  {m with
    execution := m.execution+m.spill
    spill := 0
    reservoir := m.baseline
    refund := 0}

def restoreToEntry (grant : Nat) (m : Meter) : Option Meter :=
  if m.baseline ≤ grant ∧ m.refund = 0 then
    some {m with
      execution := m.execution+m.spill+m.committedSpill
      spill := 0
      committedSpill := 0
      reservoir := grant
      baseline := grant}
  else none

/-- Source commit guards preserve signed usage, both spendable pools and refund.
The committed amount remains charged by ordinary rollback. -/
theorem commit_accounting (m : Meter) (grant : Nat)
    (guard : m.reservoir ≤ m.baseline) :
    ∃ post, commit m = some post ∧
      netUsed grant post = netUsed grant m ∧ pools post = pools m ∧
      post.baseline ≤ m.baseline ∧ post.committedSpill = m.committedSpill+m.spill ∧
      post.spill = 0 ∧ post.refund = m.refund := by
  refine ⟨_,if_pos guard,?_,rfl,guard,rfl,rfl,rfl⟩
  simp only [netUsed]
  omega

/-- Ordinary rollback restores only state gas since the baseline. The signed
pool change is exact even for hypothetical inputs whose reservoir exceeds it. -/
theorem restore_accounting (m : Meter) (grant : Nat) :
    netUsed grant (restore m) = (grant : Int)-m.baseline+m.committedSpill ∧
    pools (restore m)-pools m = netUsed grant m-netUsed grant (restore m) ∧
    (restore m).execution = m.execution+m.spill ∧
    (restore m).reservoir = m.baseline ∧ (restore m).spill = 0 ∧
    (restore m).committedSpill = m.committedSpill ∧ (restore m).refund = 0 := by
  simp [restore,netUsed,pools]
  omega

/-- The baseline guard gives nonnegative usage after ordinary rollback;
nonnegativity of arbitrary pre-rollback frames is not asserted. -/
theorem restore_nonnegative (m : Meter) (grant : Nat) (guard : m.baseline ≤ grant) :
    checkedNetUsed grant (restore m) = some (netUsed grant (restore m)) ∧
    0 ≤ netUsed grant (restore m) := by
  constructor
  · exact if_pos guard
  · have h := (restore_accounting m grant).1
    omega

/-- Predispatch rollback also undoes committed state gas. Its source assertion
that no refund accrued is retained, not inferred from a desired final state. -/
theorem entry_accounting (m : Meter) (grant : Nat)
    (baseline : m.baseline ≤ grant) (refund : m.refund = 0) :
    ∃ post, restoreToEntry grant m = some post ∧
      checkedNetUsed grant post = some 0 ∧
      pools post-pools m = netUsed grant m ∧
      post.execution = m.execution+m.spill+m.committedSpill ∧
      post.reservoir = grant ∧ post.baseline = grant ∧
      post.spill = 0 ∧ post.committedSpill = 0 ∧ post.refund = 0 := by
  refine ⟨_,if_pos ⟨baseline,refund⟩,?_,?_,rfl,rfl,rfl,rfl,rfl,refund⟩
  · simp [checkedNetUsed,netUsed]
  · simp only [pools,netUsed]
    omega

#print axioms commit_accounting
#print axioms restore_accounting
#print axioms restore_nonnegative
#print axioms entry_accounting
end Eip8282.Audit.Integrator.ReferenceMeterRollback

end

section

/-! ## ReferenceMeterBoundary -/

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

end

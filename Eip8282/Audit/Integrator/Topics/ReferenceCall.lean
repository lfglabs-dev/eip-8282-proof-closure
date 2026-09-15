import Eip8282.Audit.Integrator.ReferenceChildMeter
import Eip8282.Audit.Integrator.Topics.ReferenceMeter
import Eip8282.Audit.Integrator.Topics.Reference
import Eip8282.Audit.Integrator.ReferenceValueTransfer

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceCallGrant -/

/-! Amsterdam CALL gas is split AFTER access/value/memory/delegation execution
charges and any new-account state charge. EL0cc100eb gas.py809-872 and
instructions/system.py480-566 (archived pinned source bodies). The value stipend
is explicit; a grant split alone does not conserve execution gas. This module
transcribes resource operations, not source state reads or an outer call trace. -/
namespace Eip8282.Audit.Integrator.ReferenceCallGrant
open EvmYul ReferenceMeterRollback ReferenceMeterBoundary
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Source max_message_call_gas: retain one sixty-fourth, rounded down. -/
def maximum (gas : Nat) : Nat := gas-gas/64

def stipend (hasValue : Bool) : Nat := if hasValue then 2300 else 0

def executionCost (cold delegated delegationCold hasValue : Bool) (memoryCost : Nat) : Nat :=
  (if cold then 3000 else 100)+(if hasValue then 11300 else 0)+memoryCost+
    (if delegated then (if delegationCold then 3000 else 100) else 0)

def stateCost (hasValue deadRecipient : Bool) : Nat :=
  if hasValue && deadRecipient then 183600 else 0

/-- Literal ordered payments. Source checks before state reads and creation
predicate extraction must still be supplied by the outer operational adapter. -/
def prepare (cold delegated delegationCold hasValue deadRecipient : Bool)
    (memoryCost : Nat) (m : Meter) : Option Meter :=
  ((ReferenceStorageGas.chargeExecution (core m)
      (executionCost cold delegated delegationCold hasValue memoryCost)).bind
    (fun charged => ReferenceStorageGas.chargeState charged (stateCost hasValue deadRecipient))).map (update m)

structure Split where
  parent : Meter
  childExecution : Nat
  childState : Nat
  withheld : Nat

/-- The whole remaining state reservoir goes to the child. Its execution
stipend is included in the grant but not in the withheld share. -/
def split (hasValue : Bool) (requested : UInt256) (charged : Meter) : Split :=
  let withheld := min requested.toNat (maximum charged.execution)
  {parent := {charged with execution := charged.execution-withheld,reservoir := 0},
   childExecution := withheld+stipend hasValue,
   childState := charged.reservoir,
   withheld := withheld}

theorem split_accounting (hasValue : Bool) (requested : UInt256) (charged : Meter) :
    (split hasValue requested charged).withheld ≤ charged.execution ∧
    (split hasValue requested charged).parent.execution ≥ charged.execution/64 ∧
    (split hasValue requested charged).parent.reservoir = 0 ∧
    (split hasValue requested charged).childState = charged.reservoir ∧
    pools (split hasValue requested charged).parent+
      (split hasValue requested charged).childExecution+(split hasValue requested charged).childState =
      pools charged+stipend hasValue := by
  simp [split,maximum,pools]
  omega

private theorem prepared_cost {cold delegated delegationCold hasValue deadRecipient : Bool}
    {memoryCost : Nat} {pre post : Meter}
    (h : prepare cold delegated delegationCold hasValue deadRecipient memoryCost pre = some post) :
    pools pre-pools post = (executionCost cold delegated delegationCold hasValue memoryCost : Int)+
      stateCost hasValue deadRecipient := by
  unfold prepare at h
  cases he : ReferenceStorageGas.chargeExecution (core pre)
      (executionCost cold delegated delegationCold hasValue memoryCost) with
  | none => simp only [he,Option.bind_none,Option.map_none] at h; contradiction
  | some middle =>
    simp only [he,Option.bind_some] at h
    unfold ReferenceStorageGas.chargeExecution at he
    split at he
    · cases he
      unfold ReferenceStorageGas.chargeState at h
      split at h
      · simp only [Option.map_some,Option.some.injEq] at h
        subst post
        simp only [pools,core,update] at *
        omega
      · split at h
        · simp only [Option.map_some,Option.some.injEq] at h
          subst post
          simp only [pools,core,update] at *
          omega
        · contradiction
    · contradiction

/-- Prior CALL_VALUE includes 9000 execution gas plus the 2300 stipend.
Even after the stipend is handed to a child, that complete opcode prefix
cannot increase available pools. Actual source grant values are input-computed. -/
theorem charged_split {cold delegated delegationCold hasValue deadRecipient : Bool}
    {memoryCost : Nat} {pre charged : Meter}
    (h : prepare cold delegated delegationCold hasValue deadRecipient memoryCost pre = some charged)
    (requested : UInt256) :
    pools pre-(pools (split hasValue requested charged).parent+
      (split hasValue requested charged).childExecution+(split hasValue requested charged).childState) =
      (executionCost cold delegated delegationCold hasValue memoryCost : Int)+stateCost hasValue deadRecipient-
        stipend hasValue ∧
    pools (split hasValue requested charged).parent+
      (split hasValue requested charged).childExecution+(split hasValue requested charged).childState ≤ pools pre := by
  have paid := prepared_cost h
  have granted := (split_accounting hasValue requested charged).2.2.2.2
  have cost : stipend hasValue ≤ executionCost cold delegated delegationCold hasValue memoryCost := by
    cases hasValue <;> simp only [stipend,executionCost,Bool.false_eq_true,↓reduceIte] <;> omega
  omega

#print axioms split_accounting
#print axioms charged_split
end Eip8282.Audit.Integrator.ReferenceCallGrant

end

section

/-! ## ReferenceCallChildBoundary -/

/-! Source CALL grant, protected child payments, failed-child settlement and
parent incorporation share the same meters. New-account charge is refilled
only on failure. These conditional resource statements require actual source
frame/journal extraction; they do not equate arbitrary foreign interpreters. -/
namespace Eip8282.Audit.Integrator.ReferenceCallChildBoundary
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings
open ReferenceRuntimeReadings ReferenceMeterPath ReferenceMeterRollback
open ReferenceMeterBoundary ReferenceChildMeter ReferenceCallGrant
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def failed : Outcome → Bool
  | .success => false
  | _ => true

def start (s : Split) : Meter := init s.childExecution s.childState

def credit (m : Meter) (amount : Nat) : Meter := update m (ReferenceStorageGas.creditState (core m) amount)

def refill (hasValue deadRecipient : Bool) (outcome : Outcome) (m : Meter) : Meter :=
  if failed outcome && hasValue && deadRecipient then credit m 183600 else m

def finish (hasValue deadRecipient : Bool) (outcome : Outcome) (s : Split) (child : Meter) : Option Meter :=
  (incorporate s.parent (settle outcome child) (failed outcome)).map (refill hasValue deadRecipient outcome)

private theorem credit_pools (m : Meter) (amount : Nat) : pools (credit m amount) = pools m+amount := by
  simp only [credit,update,core,ReferenceStorageGas.creditState,pools]
  omega

private theorem failed_refill (hasValue deadRecipient : Bool) (outcome : Outcome)
    (h : outcome ≠ .success) (m : Meter) :
    pools (refill hasValue deadRecipient outcome m) = pools m+stateCost hasValue deadRecipient := by
  cases outcome <;> cases hasValue <;> cases deadRecipient <;>
    simp_all [refill,failed,stateCost,credit_pools]

/-- A protected child's actual payment run preserves its initialized zero
committed spill, discharging the source incorporation assertion. Failed child
assertions follow from ordered settlement rather than supplied return fields. -/
theorem completes {s : Split} {events : List Event} {child : Meter}
    (paid : runFull events (start s) = some child)
    (hasValue deadRecipient : Bool) (outcome : Outcome) :
    ∃ post, finish hasValue deadRecipient outcome s child = some post ∧
      (outcome ≠ .success →
        pools post = pools s.parent+pools (settle outcome child)+stateCost hasValue deadRecipient) := by
  have committed : child.committedSpill = 0 := by
    have hm := (accounting paid s.childState).2.2.2
    exact hm
  have guard : (settle outcome child).committedSpill = 0 ∧
      (failed outcome = true → (settle outcome child).spill = 0 ∧
        (settle outcome child).refund = 0 ∧
        (settle outcome child).reservoir = (settle outcome child).baseline) := by
    cases outcome
    · exact ⟨committed,by simp [failed]⟩
    · have h := settled_failure_guards child .reverted (by decide) committed
      exact ⟨h.1,fun _ => ⟨h.2.1,h.2.2.1,h.2.2.2.1⟩⟩
    · have h := settled_failure_guards child .exceptional (by decide) committed
      exact ⟨h.1,fun _ => ⟨h.2.1,h.2.2.1,h.2.2.2.1⟩⟩
  have merged : ∃ m, incorporate s.parent (settle outcome child) (failed outcome) = some m :=
    ⟨_,if_pos guard⟩
  obtain ⟨m,hm⟩ := merged
  refine ⟨refill hasValue deadRecipient outcome m,?_,?_⟩
  · simp only [finish,hm,Option.map_some]
  · intro hf
    rw [failed_refill hasValue deadRecipient outcome hf]
    have hp := (incorporate_accounting hm s.childState).2.2.1
    omega

/-- A failed paid child returns at most its grant less its executed work.
Exceptional forfeiture can only strengthen the bound after state restoration. -/
private theorem failed_work {s : Split} {events : List Event} {child : Meter}
    (paid : runFull events (start s) = some child) (outcome : Outcome) (hf : outcome ≠ .success) :
    (events.map ReferenceMeterConservation.actualExec).sum ≤ pools (start s)-pools (settle outcome child) := by
  have h := (rollback_accounting paid s.childState rfl rfl).2
  cases outcome
  · contradiction
  · exact le_of_eq h.symm
  · simp only [settle,pools,restore] at h ⊢
    omega

/-- Failed child LOG0 occurrences remain paid after both child state restore
and the caller's failed-account-creation refund. They are still cancelled logs,
not persistent queue records. The prior CALL value charge covers the stipend. -/
theorem failed_logs {kind : Kind} {p : Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v last : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post last finalWarm events)
    {cold delegated delegationCold hasValue deadRecipient : Bool} {memoryCost : Nat}
    {parent charged child final : Meter}
    (prepared : prepare cold delegated delegationCold hasValue deadRecipient memoryCost parent = some charged)
    (requested : UInt256) (amount : Nat)
    (paid : runFull (events++[.ordinary amount]) (start (split hasValue requested charged)) = some child)
    (outcome : Outcome) (hf : outcome ≠ .success)
    (finished : finish hasValue deadRecipient outcome (split hasValue requested charged) child = some final) :
    (375*ReferenceRuntimeGasBalance.logCount trace : Int) ≤ pools parent-pools final := by
  obtain ⟨known,hknown,hp⟩ := completes paid hasValue deadRecipient outcome
  have he := Option.some.inj (hknown.symm.trans finished)
  subst final
  have merged := hp hf
  have work := failed_work paid outcome hf
  have logs := ReferenceRuntimeGasBalance.log_cost h
  have grant := (charged_split prepared requested).1
  have cost : stipend hasValue ≤ executionCost cold delegated delegationCold hasValue memoryCost := by
    cases hasValue <;> simp only [stipend,executionCost,Bool.false_eq_true,↓reduceIte] <;> omega
  have startPools : pools (start (split hasValue requested charged)) =
      ((split hasValue requested charged).childExecution : Int)+(split hasValue requested charged).childState := rfl
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    ReferenceMeterConservation.actualExec,add_zero] at work
  omega

#print axioms completes
#print axioms failed_logs
end Eip8282.Audit.Integrator.ReferenceCallChildBoundary

end

section

/-! ## ReferenceCallEntry -/

/-! EL0cc process_call's value-transfer and synthetic-log guards, explicitly
separating apparent value from actual transfer. This binds the source-shaped
entry operations to the pinned Θ context. Python state-diff representation,
actual call-kind production, execution and settlement remain separate. -/
namespace Eip8282.Audit.Integrator.ReferenceCallEntry
open EvmYul EvmYul.EVM
open TransferFunding
open ReachableCalls (Contract address)
set_option autoImplicit false

def transferred (shouldTransfer : Bool) (apparent : UInt256) : UInt256 :=
  if shouldTransfer then apparent else UInt256.ofNat 0

def world (c : MessageCall.Context) (shouldTransfer : Bool) : AccountMap .EVM :=
  if shouldTransfer ∧ c.apparentValue ≠ UInt256.ofNat 0 then
    ProtocolTransfer.transfer c.world c.caller c.target c.apparentValue
  else c.world

def logs (c : MessageCall.Context) (shouldTransfer : Bool)
    (signature : UInt256) : List LogEntry :=
  if shouldTransfer ∧ c.apparentValue ≠ UInt256.ofNat 0 ∧ c.caller ≠ c.target then
    [ReferenceTransferLogs.entry signature c.caller c.target c.apparentValue]
  else []

/-- CALLVALUE continues to expose apparent value when transfer is disabled. -/
theorem apparent_value (c : MessageCall.Context) :
    c.environment.weiValue = c.apparentValue := rfl

theorem world_eq (c : MessageCall.Context) (shouldTransfer : Bool)
    (binding : c.value = transferred shouldTransfer c.apparentValue) :
    world c shouldTransfer = ReferenceValueTransfer.referenceEntry c := by
  cases shouldTransfer <;>
    simp_all [transferred,world,ReferenceValueTransfer.referenceEntry]

theorem lookup (c : MessageCall.Context) (shouldTransfer : Bool)
    (binding : c.value = transferred shouldTransfer c.apparentValue)
    (funded : c.value.toNat ≤ worldBalance c.world c.caller) (addr : AccountAddress) :
    c.entryWorld.get? addr = (world c shouldTransfer).get? addr := by
  rw [world_eq c shouldTransfer binding]
  exact ReferenceValueTransfer.entry_lookup c funded addr

theorem disabled (c : MessageCall.Context)
    (binding : c.value = transferred false c.apparentValue) (signature : UInt256) :
    (∀ addr, c.entryWorld.get? addr = c.world.get? addr) ∧
      logs c false signature = [] ∧ c.environment.weiValue = c.apparentValue := by
  have funded : c.value.toNat ≤ worldBalance c.world c.caller := by
    rw [binding]
    exact Nat.zero_le _
  exact ⟨fun addr => by simpa [world] using lookup c false binding funded addr,
    by simp [logs],rfl⟩

theorem protected_logs (kind : Contract) (c : MessageCall.Context)
    (shouldTransfer : Bool) (signature : UInt256) :
    ReferenceTransferLogs.project (address kind) (logs c shouldTransfer signature) = [] := by
  unfold logs
  split
  · exact ReferenceTransferLogs.project_entry kind signature c.caller c.target c.apparentValue
  · rfl

/-- The same ledger derives checked arithmetic at the enabled branch and
pointwise full-account entry parity; source transfer logs preserve the existing
all-topics protected-address projection, including alias and disabled cases. -/
theorem from_ledger (kind : Contract) (c : MessageCall.Context)
    (shouldTransfer : Bool) (signature : UInt256)
    (binding : c.value = transferred shouldTransfer c.apparentValue)
    {p w s credits : Nat}
    (ledger : ProtocolCreditEnvelope.Ledger GenesisFundingWorld.world p w s credits c.world)
    (counts : ProtocolCreditEnvelope.Counts p w s)
    (funded : c.value.toNat ≤ worldBalance c.world c.caller) :
    (shouldTransfer = true →
      c.apparentValue.toNat ≤ worldBalance c.world c.caller ∧
      worldBalance (ProtocolTransfer.debit c.world c.caller c.apparentValue) c.target +
        c.apparentValue.toNat < UInt256.size) ∧
    (∀ addr, c.entryWorld.get? addr = (world c shouldTransfer).get? addr) ∧
    ReferenceTransferLogs.project (address kind) (logs c shouldTransfer signature) = [] ∧
    c.environment.weiValue = c.apparentValue := by
  refine ⟨?_,lookup c shouldTransfer binding funded,protected_logs kind c shouldTransfer signature,rfl⟩
  intro enabled
  have hv : c.value = c.apparentValue := by simpa [transferred,enabled] using binding
  have guard := (ReferenceValueTransfer.from_ledger c ledger counts funded).1
  exact ⟨by simpa [hv] using funded,by simpa [hv] using guard⟩

#print axioms apparent_value
#print axioms world_eq
#print axioms lookup
#print axioms disabled
#print axioms protected_logs
#print axioms from_ledger
end Eip8282.Audit.Integrator.ReferenceCallEntry

end

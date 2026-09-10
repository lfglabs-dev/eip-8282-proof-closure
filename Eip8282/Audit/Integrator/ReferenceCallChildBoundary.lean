import Eip8282.Audit.Integrator.ReferenceCallGrant
import Eip8282.Audit.Integrator.ReferenceChildMeter

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

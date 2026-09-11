import Eip8282.Audit.Integrator.ReferenceRuntimeStateBalance
import Eip8282.Audit.Integrator.ReferenceMeterConservation

/-! Exact successful source-meter accounting on the same actual runtime.
The initial storage potential is retained for nested frames that can refund
state bought earlier. LOG0 occurrences count executed logs, not final retained
queue records. Complete outer rollback/commit selection is still required. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeGasBalance
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings
open ReferenceRuntimeReadings ReferenceMeterPath ReferenceRuntimeStateBalance
open ReferenceMeterConservation
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def logCount : List Labelled → Nat
  | [] => 0
  | label::tail => (if label.2.2.1 = .LOG0 then 1 else 0)+logCount tail

private theorem exec_nonnegative (event : Event) : 0 ≤ actualExec event := by
  cases event <;> simp [actualExec]

theorem log_cost {kind : Kind} {p : Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post finish finalWarm events) :
    (375*logCount trace : Int) ≤ (events.map actualExec).sum := by
  induction h with
  | refl => simp [logCount]
  | @cons fuel gasCost rem pre mid post v next finish w finalWarm trace event events
      actual decoded related nextRelated warm created action readings price tail ih =>
    have nonneg := exec_nonnegative event
    by_cases hl : (decodeAt pre).1 = .LOG0
    · have hn : (decodeAt pre).1 ≠ .SSTORE := by rw [hl]; decide
      simp only [Price,if_neg hn] at price
      obtain ⟨n,hprice,rfl⟩ := price
      rw [hl] at hprice
      simp only [ReferenceCopyLogGas.ordinaryCost,show (Operation.LOG0 : Operation .EVM) ≠ .CALLDATACOPY by decide,
        ↓reduceIte,Option.some.injEq] at hprice
      simp only [List.map_cons,List.sum_cons,actualExec,logCount,hl,↓reduceIte]
      unfold ReferenceCopyLogGas.logCost at hprice
      omega
    · simp only [List.map_cons,List.sum_cons,logCount,if_neg hl,Nat.zero_add]
      omega

/-- Literal pool loss equals exact execution charges plus the derived change
in all slot potentials. A prefunded slot credit is not silently discarded. -/
theorem balance {kind : Kind} {p : Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event} {meter final : ReferenceStorageGas.Meter}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post finish finalWarm events)
    (paid : run events meter = some final) :
    pools meter-pools final = (events.map actualExec).sum+totalPotential p finish.storage-totalPotential p v.storage ∧
    stateBalance final-stateBalance meter = totalPotential p finish.storage-totalPotential p v.storage := by
  have accounting := run_balance paid
  have storage := ReferenceRuntimeStateBalance.of_coupled h
  change (events.map stateDelta).sum = _ at storage
  omega

/-- Include the terminal charge once. The bound holds with the explicit
initial-potential correction; only the fresh-transaction case removes it. -/
theorem through_terminal {kind : Kind} {p : Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event} {meter final : ReferenceStorageGas.Meter}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post finish finalWarm events)
    (amount : Nat) (paid : run (events++[.ordinary amount]) meter = some final) :
    (375*logCount trace : Int) ≤ pools meter-pools final+totalPotential p v.storage := by
  have accounting := (run_balance paid).1
  have storage := ReferenceRuntimeStateBalance.of_coupled h
  change (events.map stateDelta).sum = _ at storage
  have logs := log_cost h
  have finalNonneg := ReferenceRuntimeStateBalance.nonnegative p finish.storage
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    actualExec,stateDelta,add_zero] at accounting
  omega

theorem fresh_transaction {kind : Kind} {p : Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event} {meter final : ReferenceStorageGas.Meter}
    (h : Coupled kind p initialCreated fuel pre v w trace rem post finish finalWarm events)
    (amount : Nat) (paid : run (events++[.ordinary amount]) meter = some final)
    (initial : v.storage = emptyTx) :
    (375*logCount trace : Int) ≤ pools meter-pools final := by
  have bound := through_terminal h amount paid
  rw [initial,empty_potential,add_zero] at bound
  exact bound

#print axioms log_cost
#print axioms balance
#print axioms through_terminal
#print axioms fresh_transaction
end Eip8282.Audit.Integrator.ReferenceRuntimeGasBalance

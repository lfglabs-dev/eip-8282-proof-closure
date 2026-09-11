import Eip8282.Audit.Integrator.ReferenceFullLogTotal

/-! Exact state-gas conservation from the same literal checked runtime.
Existing storage-potential algebra is consumed directly on source actions,
without requiring an old semantic trace. Consumers: actual transaction meter
settlement and fresh-journal subtraction guards. Arbitrary finite prefixes,
including prefixes later reverted, remain execution rather than commitment. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedStateGas
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceMeterPath ReferenceRuntimeStateBalance
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem source_balance {kind : Eip8282.Audit.Model.Kind} {p : ReferenceStorageView.Parent}
    {v finish : View} {w fw : Warm} {events : List Event}
    (actual : ReferenceSourceReplayTrace.Run kind p v w finish fw events) :
    (events.map ReferenceMeterConservation.stateDelta).sum = totalPotential p finish.storage-totalPotential p v.storage := by
  induction actual with
  | refl => simp
  | cons effect price stack tail ih =>
    have balance := ReferenceRuntimeStateBalance.action_balance effect price
    change ReferenceMeterConservation.stateDelta _ = _ at balance
    simp only [List.map_cons,List.sum_cons]
    omega

theorem checked_balance {kind : Eip8282.Audit.Model.Kind} {p : ReferenceStorageView.Parent}
    {v finish : View} {w fw : Warm} {m final : Meter} {events : List Event}
    (actual : ReferenceCheckedRuntimeTrace.Run kind p v w m finish fw final events)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v) (grant : Nat) :
    pools m-pools final = (ReferenceExecutionLedger.work events : Int)+totalPotential p finish.storage-totalPotential p v.storage ∧
    netUsed grant final-netUsed grant m = totalPotential p finish.storage-totalPotential p v.storage ∧
    final.baseline = m.baseline ∧ final.committedSpill = m.committedSpill := by
  obtain ⟨source,paid,_⟩ := actual.extract stack aligned
  have state := source_balance source
  have account := ReferenceMeterBoundary.accounting paid grant
  have work := ReferenceExecutionLedger.work_cast events
  exact ⟨by omega,by omega,account.2.2⟩

theorem terminal_balance {kind : Eip8282.Audit.Model.Kind} {p : ReferenceStorageView.Parent}
    {v finish : View} {w fw : Warm} {m middle final : Meter} {events : List Event} {amount : Nat}
    (actual : ReferenceCheckedRuntimeTrace.Run kind p v w m finish fw middle events)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (terminal : runFull [.ordinary amount] middle = some final) (grant : Nat) :
    pools m-pools final = (ReferenceExecutionLedger.work events : Int)+amount+totalPotential p finish.storage-totalPotential p v.storage ∧
    netUsed grant final-netUsed grant m = totalPotential p finish.storage-totalPotential p v.storage ∧
    final.baseline = m.baseline ∧ final.committedSpill = m.committedSpill := by
  have first := checked_balance actual stack aligned grant
  have last := ReferenceMeterBoundary.accounting terminal grant
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,ReferenceMeterConservation.actualExec,ReferenceMeterConservation.stateDelta,add_zero] at last
  exact ⟨by omega,by omega,last.2.2.1.trans first.2.2.1,last.2.2.2.trans first.2.2.2⟩

/-- These bounds are consequences of a same-run fresh journal and terminal
payment, not separately assumed returned-pool or net-state postconditions. -/
theorem fresh_guards {kind : Eip8282.Audit.Model.Kind} {p : ReferenceStorageView.Parent}
    {v finish : View} {w fw : Warm} {middle final : Meter} {events : List Event} {amount txGas intrinsic : Nat}
    (actual : ReferenceCheckedRuntimeTrace.Run kind p v w (ReferenceTransactionWork.initial txGas intrinsic) finish fw middle events)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (fresh : v.storage = ReferenceRuntimeStateBalance.emptyTx)
    (terminal : runFull [.ordinary amount] middle = some final)
    (affords : intrinsic ≤ txGas) (maximum : intrinsic ≤ 16777216) :
    final.execution+final.reservoir ≤ txGas ∧
    0 ≤ netUsed (ReferenceTransactionGas.allocate txGas intrinsic).reservoir final ∧
    ReferenceTransactionGas.settledState (netUsed (ReferenceTransactionGas.allocate txGas intrinsic).reservoir final) ≤ txGas-final.execution-final.reservoir ∧
    final.baseline = (ReferenceTransactionGas.allocate txGas intrinsic).reservoir ∧ final.committedSpill = 0 := by
  have balance := terminal_balance actual stack aligned terminal (ReferenceTransactionGas.allocate txGas intrinsic).reservoir
  have zero := ReferenceRuntimeStateBalance.empty_potential p
  have nonnegative := ReferenceRuntimeStateBalance.nonnegative p finish.storage
  have allocated := ReferenceTransactionGas.allocation txGas intrinsic affords maximum
  rw [fresh,zero] at balance
  simp only [ReferenceTransactionWork.initial,ReferenceChildMeter.init,pools,netUsed] at balance
  unfold ReferenceTransactionGas.settledState
  constructor
  · omega
  constructor
  · unfold netUsed; omega
  constructor
  · have nonneg : 0 ≤ netUsed (ReferenceTransactionGas.allocate txGas intrinsic).reservoir final := by unfold netUsed; omega
    rw [max_eq_right nonneg]
    have cast : ((netUsed (ReferenceTransactionGas.allocate txGas intrinsic).reservoir final).toNat : Int) = netUsed (ReferenceTransactionGas.allocate txGas intrinsic).reservoir final := Int.toNat_of_nonneg nonneg
    unfold netUsed at cast ⊢
    omega
  exact balance.2.2

#print axioms source_balance
#print axioms checked_balance
#print axioms terminal_balance
#print axioms fresh_guards
end Eip8282.Audit.Integrator.ReferenceCheckedStateGas

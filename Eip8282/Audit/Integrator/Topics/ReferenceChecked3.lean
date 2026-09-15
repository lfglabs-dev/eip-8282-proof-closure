import Eip8282.Audit.Integrator.ReferenceCheckedFrameOutcome
import Eip8282.Audit.Integrator.Topics.ReferenceFull

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceCheckedLogContext -/

/-! Log-context lens for the checked runtime. The replay View carries the fixed
incoming protected-address log prefix plus this frame's local projected logs.
Every successful running handler preserves that prefix; removing it before
parent incorporation prevents inherited logs from being counted twice.
These are executed logs, not persistent records: REVERT, failures and ancestors
can discard their contribution. Source frame initialization, transfer LOG3
projection and actual parent journal identity are separate binding producers. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedLogContext
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceMeterBoundary
open ReferencePureAction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem family_logs {kind : Kind} {v next : View} {arg : Option (UInt256 × Nat)}
    (p : Pure) (effect : familyAction kind p arg v = some next) : next.logs = v.logs := by
  cases p <;> simp only [familyAction] at effect
  all_goals repeat' first | split at effect | cases effect
  all_goals rfl

private theorem pure_logs {kind : Kind} {instr : Instruction} {v next : View}
    (effect : action kind instr v = some next) : next.logs = v.logs := by
  unfold action at effect
  cases selected : classify instr.1 with
  | none => simp only [selected,Option.bind_none] at effect; contradiction
  | some p =>
    simp only [selected,Option.bind_some] at effect
    exact family_logs p effect

/-- Only LOG0 appends a log; every other represented action preserves the
same log sequence. Its source output bytes are already fixed by that action. -/
theorem action_suffix {kind : Kind} {parent : ReferenceStorageView.Parent}
    {instr : Instruction} {v next : View}
    (actual : ReferenceRuntimeAction.Action kind parent instr v next) :
    ∃ suffix, next.logs = v.logs++suffix := by
  cases actual with
  | base base =>
    cases base with
    | pure effect => exact ⟨[],by simpa only [List.append_nil] using pure_logs effect⟩
    | load => exact ⟨[],(List.append_nil _).symm⟩
    | store => exact ⟨[],(List.append_nil _).symm⟩
    | word => exact ⟨[],(List.append_nil _).symm⟩
    | byte => exact ⟨[],(List.append_nil _).symm⟩
  | copy => exact ⟨[],(List.append_nil _).symm⟩
  | log => exact ⟨_,rfl⟩

/-- The same computed checked trace produces the suffix; it is not an assumed
matching source log list. The entry prefix is retained exactly once. -/
theorem trace_suffix {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v finish : View} {warm finalWarm : Warm} {meter final : Meter} {events : List Event}
    (actual : ReferenceCheckedRuntimeTrace.Run kind parent v warm meter finish finalWarm final events)
    (initial : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v) :
    ∃ suffix, finish.logs = v.logs++suffix := by
  induction actual with
  | refl => exact ⟨[],(List.append_nil _).symm⟩
  | cons step tail ih =>
    obtain ⟨action,_,_,_,stack⟩ := step.sound initial aligned
    obtain ⟨first,firstLogs⟩ := action_suffix action
    obtain ⟨rest,restLogs⟩ := ih stack (ReferenceActionMemoryBounds.preserves_alignment action aligned)
    exact ⟨first++rest,by rw [restLogs,firstLogs,List.append_assoc]⟩

/-- Success contributes only the generated suffix. Incoming logs are neither
omitted from the replay view nor re-emitted to the parent. -/
theorem success_contribution {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v finish : View} {warm finalWarm : Warm} {meter final : Meter} {events : List Event}
    (actual : ReferenceCheckedRuntimeTrace.Run kind parent v warm meter finish finalWarm final events)
    (initial : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (output : ByteArray) :
    ∃ suffix, finish.logs = v.logs++suffix ∧
      (ReferenceCheckedFrameOutcome.success v.logs finish finalWarm final output).logsForParent = suffix := by
  obtain ⟨suffix,logs⟩ := trace_suffix actual initial aligned
  exact ⟨suffix,logs,ReferenceCheckedFrameOutcome.success_logs v.logs suffix finish finalWarm final output logs⟩

/-- Every successful terminal preserves the exact running log list; STOP's
source PC increment is immaterial to this log-context equation. -/
theorem terminal_logs {h : ReferenceCheckedTerminalStep.Halt} {v : View} {meter : Meter}
    {output : ByteArray} {result : ReferenceCheckedTerminalStep.End}
    (actual : ReferenceCheckedTerminalStep.run h v meter output = .ok result) : result.view.logs = v.logs := by
  unfold ReferenceCheckedTerminalStep.run at actual
  repeat' first | split at actual | cases actual
  all_goals rfl

/-- The actual successful evaluated terminal contributes exactly its generated
suffix. Terminal warmth, prefix and local logs come from the same evaluation. -/
theorem terminal_contribution {kind : Kind} {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {output : ByteArray} {fuel : Nat}
    {v : View} {warm : Warm} {meter : Meter} {events : List Event}
    {result : ReferenceCheckedTerminalStep.End}
    (snapshot : ReferenceStorageView.Tx)
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent output fuel v warm meter =
      some (events,.terminal result))
    (initial : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (success : result.halt ≠ .reverted) :
    ∃ finalWarm suffix,
      result.view.logs = v.logs++suffix ∧
      ReferenceCheckedFrameOutcome.settle snapshot v.logs finalWarm (.terminal result) =
        .returned (ReferenceCheckedFrameOutcome.success v.logs result.view finalWarm result.meter result.output) ∧
      (ReferenceCheckedFrameOutcome.success v.logs result.view finalWarm result.meter result.output).logsForParent = suffix := by
  obtain ⟨finish,finalWarm,final,trace,last,_⟩ := ReferenceCheckedEvaluator.extract context actual
  obtain ⟨halt,terminal,_⟩ := ReferenceCheckedDispatchTerminal.terminal last
  obtain ⟨suffix,logs⟩ := trace_suffix trace initial aligned
  have completeLogs := (terminal_logs terminal).trans logs
  refine ⟨finalWarm,suffix,completeLogs,?_,?_⟩
  · simp only [ReferenceCheckedFrameOutcome.settle,if_neg success]
  · exact ReferenceCheckedFrameOutcome.success_logs v.logs suffix result.view finalWarm result.meter result.output completeLogs

#print axioms action_suffix
#print axioms trace_suffix
#print axioms success_contribution
#print axioms terminal_logs
#print axioms terminal_contribution
end Eip8282.Audit.Integrator.ReferenceCheckedLogContext

end

section

/-! ## ReferenceCheckedStateGas -/

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

end

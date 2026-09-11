import Eip8282.Audit.Integrator.ReferenceCheckedDispatchMetadata
import Eip8282.Audit.Integrator.ReferenceCheckedFrameOutcome

/-! Same evaluated child outcome supplies the full-meter incorporation guards.
Metadata are conserved across all computed running steps and the final partial
failure, without assuming a payment certificate or an initially bounded stack.
Starting from the literal child allocator derives committedSpill=0; caught
exceptional and reverted settlement derives the remaining failed-child guards.
Actual source CALL/CREATE context, snapshot, grants and unique frame identity
still need their producer; no arbitrary parent is identified with a call tree
merely because these numerical meter equations hold. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedFrameMeter
open EvmYul EvmYul.EVM
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceMeterBoundary ReferenceCheckedDispatch
open ReferenceCheckedDispatchMetadata
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- Derive both invariant full-meter fields from the actual entire evaluated
result, including any final failed instruction's partial meter. -/
theorem evaluated {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {output : ByteArray} {fuel : Nat}
    {v : View} {warm : Warm} {meter : Meter} {events : List Event} {result : Outcome}
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent output fuel v warm meter = some (events,result)) :
    (outcomeMeter result).baseline = meter.baseline ∧
      (outcomeMeter result).committedSpill = meter.committedSpill := by
  induction fuel generalizing v warm meter events result with
  | zero => simp only [ReferenceCheckedEvaluator.eval] at actual; contradiction
  | succ fuel ih =>
    simp only [ReferenceCheckedEvaluator.eval] at actual
    cases hd : ReferenceCheckedDispatch.run destinations ownerExists parent v warm meter output with
    | continued next nextWarm nextMeter event =>
      simp only [hd] at actual
      obtain ⟨pair,tail,same⟩ := Option.map_eq_some_iff.mp actual
      rcases pair with ⟨tailEvents,tailResult⟩
      cases same
      obtain ⟨baseline,committed⟩ := run_metadata hd
      obtain ⟨lastBaseline,lastCommitted⟩ := ih tail
      exact ⟨lastBaseline.trans baseline,lastCommitted.trans committed⟩
    | terminal terminal =>
      simp only [hd,Option.some.injEq] at actual
      cases actual
      exact run_metadata hd
    | eof last lastWarm lastMeter lastOutput =>
      simp only [hd,Option.some.injEq] at actual
      cases actual
      exact run_metadata hd
    | failed error last lastWarm lastMeter lastOutput =>
      simp only [hd,Option.some.injEq] at actual
      cases actual
      exact run_metadata hd
    | unsupported tag last lastWarm lastMeter lastOutput =>
      simp only [hd,Option.some.injEq] at actual
      cases actual
      exact run_metadata hd

/-- The failed-child assertion follows from literal initialization and the
same computed outcome. No separate committed-spill hypothesis is consumed. -/
theorem initialized {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {output : ByteArray} {fuel : Nat}
    {v : View} {warm : Warm} {execution reservoir : Nat} {events : List Event} {result : Outcome}
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent output fuel v warm
      (ReferenceChildMeter.init execution reservoir) = some (events,result)) :
    (outcomeMeter result).baseline = reservoir ∧ (outcomeMeter result).committedSpill = 0 :=
  evaluated actual

/-- A source-caught exceptional child returns no execution gas. All failed
incorporation assertions are derived after restoration and forfeiture of its
actual partial meter; its internal logs are not forwarded. -/
theorem failed_child {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {output : ByteArray} {fuel : Nat}
    {v failedView : View} {warm failedWarm : Warm} {execution reservoir : Nat} {failedMeter : Meter}
    {events : List Event} {fault : Fault} {failedOutput : ByteArray}
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent output fuel v warm
      (ReferenceChildMeter.init execution reservoir) =
      some (events,.failed fault failedView failedWarm failedMeter failedOutput))
    (caught : ReferenceCheckedFaultClass.caught fault = true)
    (parentMeter : Meter) (snapshot : ReferenceStorageView.Tx) (incomingLogs : List LogEntry) (terminalWarm : Warm) :
    ReferenceCheckedFrameOutcome.settle snapshot incomingLogs terminalWarm
        (.failed fault failedView failedWarm failedMeter failedOutput) =
      .returned (ReferenceCheckedFrameOutcome.failure snapshot failedView failedWarm
        (ReferenceChildMeter.settle .exceptional failedMeter) ByteArray.empty (.exceptional fault)) ∧
    ReferenceChildMeter.incorporate parentMeter (ReferenceChildMeter.settle .exceptional failedMeter) true =
      some (ReferenceChildMeter.absorb parentMeter (ReferenceChildMeter.settle .exceptional failedMeter)) ∧
    (ReferenceChildMeter.absorb parentMeter (ReferenceChildMeter.settle .exceptional failedMeter)).execution = parentMeter.execution ∧
    (ReferenceChildMeter.absorb parentMeter (ReferenceChildMeter.settle .exceptional failedMeter)).reservoir = parentMeter.reservoir+reservoir := by
  obtain ⟨baseline,committed⟩ := initialized actual
  simp only [outcomeMeter] at baseline committed
  have guards := ReferenceChildMeter.settled_failure_guards failedMeter .exceptional (by decide) committed
  refine ⟨?_,(ReferenceChildMeter.failed_incorporation parentMeter _ guards.1 guards.2.1 guards.2.2.1 guards.2.2.2.1).1,?_,?_⟩
  · simp only [ReferenceCheckedFrameOutcome.settle,caught,if_true]
  · simp [ReferenceChildMeter.absorb,ReferenceChildMeter.settle]
  · change parentMeter.reservoir+failedMeter.baseline = parentMeter.reservoir+reservoir
    rw [baseline]

/-- A reverted child returns unspent execution plus restored spill. The same
actual meter derives all failed-incorporation assertions; output is preserved
and its log contribution is suppressed by the separate frame projection. -/
theorem reverted_child {destinations : List Nat} {ownerExists : Bool}
    {parent : ReferenceStorageView.Parent} {output : ByteArray} {fuel : Nat}
    {v : View} {warm : Warm} {execution reservoir : Nat} {events : List Event}
    {result : ReferenceCheckedTerminalStep.End}
    (actual : ReferenceCheckedEvaluator.eval destinations ownerExists parent output fuel v warm
      (ReferenceChildMeter.init execution reservoir) = some (events,.terminal result))
    (halt : result.halt = .reverted)
    (parentMeter : Meter) (snapshot : ReferenceStorageView.Tx) (incomingLogs : List LogEntry) (terminalWarm : Warm) :
    ReferenceCheckedFrameOutcome.settle snapshot incomingLogs terminalWarm (.terminal result) =
      .returned (ReferenceCheckedFrameOutcome.failure snapshot result.view terminalWarm
        (restore result.meter) result.output .reverted) ∧
    ReferenceChildMeter.incorporate parentMeter (restore result.meter) true =
      some (ReferenceChildMeter.absorb parentMeter (restore result.meter)) ∧
    (ReferenceChildMeter.absorb parentMeter (restore result.meter)).execution =
      parentMeter.execution+result.meter.execution+result.meter.spill ∧
    (ReferenceChildMeter.absorb parentMeter (restore result.meter)).reservoir = parentMeter.reservoir+reservoir := by
  obtain ⟨baseline,committed⟩ := initialized actual
  simp only [outcomeMeter] at baseline committed
  have guards := ReferenceChildMeter.settled_failure_guards result.meter .reverted (by decide) committed
  refine ⟨?_,(ReferenceChildMeter.failed_incorporation parentMeter _ guards.1 guards.2.1 guards.2.2.1 guards.2.2.2.1).1,?_,?_⟩
  · simp only [ReferenceCheckedFrameOutcome.settle,halt,if_true,ReferenceChildMeter.settle]
  · simp only [ReferenceChildMeter.absorb,restore,Nat.add_assoc]
  · change parentMeter.reservoir+result.meter.baseline = parentMeter.reservoir+reservoir
    rw [baseline]

#print axioms evaluated
#print axioms initialized
#print axioms failed_child
#print axioms reverted_child
end Eip8282.Audit.Integrator.ReferenceCheckedFrameMeter

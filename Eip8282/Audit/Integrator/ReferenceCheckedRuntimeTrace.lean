import Eip8282.Audit.Integrator.ReferenceCheckedEnvironmentStep
import Eip8282.Audit.Integrator.ReferenceCheckedStackControlStep
import Eip8282.Audit.Integrator.ReferenceCheckedStorageStep
import Eip8282.Audit.Integrator.Topics.ReferenceChecked2
import Eip8282.Audit.Integrator.ReferenceCheckedCopyLogStep
import Eip8282.Audit.Integrator.ReferenceRuntimeWorkLength

/-! Compose the same literal checked handler results into the existing runtime
replay and resource consumers. Every step is bound to the instruction decoded
from its current code/PC; effects, prices, payments and intermediate stack
bounds are conclusions, not separate annotations supplied by the caller.
This relation covers all41 protected nonterminal opcode variants. The source
dispatch/frame and terminal/exception extraction remain distinct producers.
Audited source-handler transcription is not mechanical Python extraction.
No finite trace ceiling, independent old execution, or successful call assumed. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedRuntimeTrace
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceSourceReadings ReferenceMeterPath ReferenceExecutionPotential
open ReferenceSourceReplayTrace (instruction)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

inductive Step (kind : Kind) (parent : ReferenceStorageView.Parent) :
    View → Warm → Meter → View → Warm → Meter → Event → Prop where
  | binary (b : ReferenceWordOps.Binary) {v next : View} {warm : Warm} {meter final : Meter}
      (decoded : (instruction v).1 = ReferenceWordOps.opcode b)
      (actual : ReferenceCheckedBinaryStep.run b v meter = .ok (next,final)) :
      Step kind parent v warm meter next warm final (.ordinary (ReferenceCheckedBinaryStep.charge b))
  | environment (h : ReferenceCheckedEnvironmentStep.Handler)
      {v next : View} {warm : Warm} {meter final : Meter}
      (decoded : (instruction v).1 = ReferenceCheckedEnvironmentStep.opcode h)
      (actual : ReferenceCheckedEnvironmentStep.run h v meter = .ok (next,final)) :
      Step kind parent v warm meter next warm final (.ordinary (ReferenceCheckedEnvironmentStep.charge h))
  | stackControl (h : ReferenceCheckedStackControlStep.Handler) (destinations : List Nat)
      {v next : View} {warm : Warm} {meter final : Meter}
      (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
      (decoded : (instruction v).1 = ReferenceCheckedStackControlStep.opcode h)
      (actual : ReferenceCheckedStackControlStep.run h destinations v meter = .ok (next,final)) :
      Step kind parent v warm meter next warm final (.ordinary (ReferenceCheckedStackControlStep.charge h))
  | memoryStore (byte : Bool) {v next : View} {warm : Warm} {meter final : Meter}
      (decoded : (instruction v).1 = ReferenceCheckedMemoryStore.opcode byte)
      (actual : ReferenceCheckedMemoryStore.run byte v meter = .ok (next,final)) :
      Step kind parent v warm meter next warm final
        (.ordinary (3+(ReferenceMemoryCapacity.cost (words next)-ReferenceMemoryCapacity.cost (words v))))
  | copyLog (h : ReferenceCheckedCopyLogStep.Handler) {v next : View} {warm : Warm} {meter final : Meter}
      (decoded : (instruction v).1 = ReferenceCheckedCopyLogStep.opcode h)
      (actual : ReferenceCheckedCopyLogStep.run h v meter = .ok (next,final)) :
      Step kind parent v warm meter next warm final (.ordinary (ReferenceCheckedCopyLogStep.cost h v))
  | load {v next : View} {warm finalWarm : Warm} {meter final : Meter}
      (decoded : (instruction v).1 = .SLOAD)
      (actual : ReferenceCheckedStorageStep.load parent v warm meter = .ok (next,finalWarm,final)) :
      Step kind parent v warm meter next finalWarm final
        (.ordinary (if (sourceReading parent v warm).warm then 100 else 2100))
  | store (ownerExists : Bool) {v next : View} {warm finalWarm : Warm} {meter final : Meter}
      (decoded : (instruction v).1 = .SSTORE)
      (actual : ReferenceCheckedStorageStep.store ownerExists parent v warm meter = .ok (next,finalWarm,final)) :
      Step kind parent v warm meter next finalWarm final
        (.store (sourceReading parent v warm).warm (sourceReading parent v warm).original
          (sourceReading parent v warm).current (sourceReading parent v warm).new)

/-- Opcode dispatch binds the handler to the same source code/PC. The entire
instruction immediate is derived by CheckedDecode, rather than supplied. No effects or price proof is a Step constructor input. -/
theorem Step.sound {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v next : View} {warm finalWarm : Warm} {meter final : Meter} {event : Event}
    (step : Step kind parent v warm meter next finalWarm final event)
    (initial : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v) :
    ReferenceRuntimeAction.Action kind parent (instruction v) v next ∧
    ReferenceRuntimeReadings.Price parent v warm next (instruction v).1 event ∧
    runFull [event] meter = some final ∧
    finalWarm = warmAfter (instruction v).1 v warm ∧ next.stack.length ≤ 1024 := by
  cases step with
  | binary b decoded actual =>
    obtain ⟨_,ha,hp,hm,hb⟩ := ReferenceCheckedBinaryStep.success kind parent warm initial actual
    rw [ReferenceCheckedDecode.nonpush v _ decoded (by cases b <;> rfl)]
    refine ⟨ha,hp,hm,?_,hb⟩
    cases b <;> rfl
  | environment h decoded actual =>
    obtain ⟨_,ha,hp,hm,hb⟩ := ReferenceCheckedEnvironmentStep.success kind parent warm initial actual
    rw [ReferenceCheckedDecode.nonpush v _ decoded (by cases h <;> rfl)]
    refine ⟨ha,hp,hm,?_,hb⟩
    cases h <;> rfl
  | stackControl h destinations context decoded actual =>
    obtain ⟨_,ha,hp,hm,hb⟩ := ReferenceCheckedStackControlStep.success kind parent warm context initial actual
    rw [ReferenceCheckedDecode.stack_control h v decoded]
    refine ⟨ha,hp,hm,?_,hb⟩
    cases h <;> rfl
  | memoryStore byte decoded actual =>
    obtain ⟨ha,hp,hm,hb⟩ := ReferenceCheckedMemoryStore.success kind parent warm initial aligned actual
    rw [ReferenceCheckedDecode.nonpush v _ decoded (by cases byte <;> rfl)]
    refine ⟨ha,hp,hm,?_,hb⟩
    cases byte <;> rfl
  | copyLog h decoded actual =>
    obtain ⟨ha,hp,hm,hb⟩ := ReferenceCheckedCopyLogStep.success kind parent warm initial aligned actual
    rw [ReferenceCheckedDecode.nonpush v _ decoded (by cases h <;> rfl)]
    refine ⟨ha,hp,hm,?_,hb⟩
    cases h <;> rfl
  | load decoded actual =>
    rw [ReferenceCheckedDecode.nonpush v _ decoded rfl]
    exact ReferenceCheckedStorageStep.load_success kind initial actual
  | store ownerExists decoded actual =>
    rw [ReferenceCheckedDecode.nonpush v _ decoded rfl]
    exact ReferenceCheckedStorageStep.store_success kind initial actual

/-- One shared sequence of views, warming and meters. Every accepted step runs
a literal checked handler, and every event is its computed price. -/
inductive Run (kind : Kind) (parent : ReferenceStorageView.Parent) :
    View → Warm → Meter → View → Warm → Meter → List Event → Prop where
  | refl (v : View) (warm : Warm) (meter : Meter) : Run kind parent v warm meter v warm meter []
  | cons {v next finish : View} {warm nextWarm finalWarm : Warm} {meter nextMeter final : Meter}
      {event : Event} {events : List Event}
      (step : Step kind parent v warm meter next nextWarm nextMeter event)
      (tail : Run kind parent next nextWarm nextMeter finish finalWarm final events) :
      Run kind parent v warm meter finish finalWarm final (event::events)

/-- Full meters preserve their own baseline metadata while composing the same
core payment sequence. No alternate resource trace is introduced. -/
theorem runFull_append (first second : List Event) (meter : Meter) :
    runFull (first++second) meter = (runFull first meter).bind (runFull second) := by
  unfold runFull
  rw [ReferenceMeterPath.run_append]
  cases h : ReferenceMeterPath.run first (core meter) with
  | none => rfl
  | some mid =>
    simp only [Option.bind_some,Option.map_some,core,update]
    cases ReferenceMeterPath.run second mid <;> rfl

/-- Extract all formerly independent source actions, exact prices/payments and
stack bounds from a single checked handler history with bounded entry stack. -/
theorem Run.extract {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v finish : View} {warm finalWarm : Warm} {meter final : Meter} {events : List Event}
    (actual : Run kind parent v warm meter finish finalWarm final events)
    (initial : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v) :
    ReferenceSourceReplayTrace.Run kind parent v warm finish finalWarm events ∧
    runFull events meter = some final ∧ finish.stack.length ≤ 1024 := by
  induction actual with
  | refl => exact ⟨.refl _ _,by simp [runFull,ReferenceMeterPath.run,update,core],initial⟩
  | @cons v next finish warm nextWarm finalWarm meter nextMeter final event events step tail ih =>
    obtain ⟨ha,hp,hm,hw,hb⟩ := step.sound initial aligned
    have nextAligned := ReferenceActionMemoryBounds.preserves_alignment ha aligned
    obtain ⟨source,paid,bound⟩ := ih hb nextAligned
    refine ⟨.cons ha hp hb (by simpa only [hw] using source),?_,bound⟩
    change runFull ([event]++events) meter = some final
    rw [runFull_append,hm,Option.bind_some,paid]

/-- The number of successfully executed nonterminal handlers is bounded by
entry potential even when state refunds increase the execution pool. -/
theorem Run.length_bound {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v finish : View} {warm finalWarm : Warm} {meter final : Meter} {events : List Event}
    (actual : Run kind parent v warm meter finish finalWarm final events)
    (initial : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v) : potential final+events.length ≤ potential meter := by
  obtain ⟨source,paid,_⟩ := actual.extract initial aligned
  exact ReferenceRuntimeWorkLength.paid_length source paid

#print axioms Step.sound
#print axioms runFull_append
#print axioms Run.extract
#print axioms Run.length_bound
end Eip8282.Audit.Integrator.ReferenceCheckedRuntimeTrace

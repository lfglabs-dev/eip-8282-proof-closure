import Eip8282.Audit.Integrator.Topics.ReferenceChecked
import Eip8282.Audit.Integrator.ReferenceSystemReadingsTrace
import Eip8282.Audit.Integrator.ReferenceCheckedDispatch

/-! Accept the already paid SYSTEM action in the same checked dispatcher.
Internal consumer: Coupled trace -> actual checked evaluator success. Inputs
below are extracted from that trace, not added to a public success domain. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemForward
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceMeterPath ReferenceCheckedDispatch
open ReferenceSourceReplayTrace (instruction)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem handler {kind : Kind} {parent : ReferenceStorageView.Parent} {h : Handler}
    {destinations : List Nat} {v next : View} {warm : Warm} {meter final : Meter}
    {event : Event} (output : ByteArray)
    (context : ReferenceCheckedStackControlStep.DestinationContext kind destinations)
    (decoded : (instruction v).1 = opcode h)
    (action : ReferenceSystemAction.Action kind parent (instruction v) v next)
    (price : ReferenceSystemReadingsTrace.SourcePrice parent v warm next (instruction v).1 event)
    (bound : next.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (pcfit : v.pc+1 < UInt256.size) (paid : runFull [event] meter = some final) :
    runHandler h destinations true parent v warm meter output =
      .continued next (warmAfter (instruction v).1 v warm) final event := by
  have count := (ReferenceActionMemoryBounds.computed (.base action) aligned).2
  rw [decoded] at price count ⊢
  cases h with
  | binary b =>
    rw [ReferenceCheckedDecode.nonpush v _ decoded (by cases b <;> rfl)] at action
    have pure : ReferencePureAction.action kind (ReferenceWordOps.opcode b,none) v = some next := by
      cases b <;> cases action <;> assumption
    have wordsEq : words next = words v := by
      cases b <;> simpa [opcode,ReferenceWordOps.opcode,ReferenceActionMemoryBounds.span,MachineState.M] using count
    have eventEq : event = .ordinary (ReferenceCheckedBinaryStep.charge b) := by
      cases b <;> simpa [ReferenceSystemReadingsTrace.SourcePrice,opcode,ReferenceWordOps.opcode,
        ReferenceOrdinaryGas.ordinaryCost,ReferenceCheckedBinaryStep.charge,wordsEq] using price
    subst event
    have actual := ReferenceCheckedPureForward.binary pure bound paid
    simp only [runHandler,actual]
    cases b <;> rfl
  | environment h =>
    rw [ReferenceCheckedDecode.nonpush v _ decoded (by cases h <;> rfl)] at action
    have pure : ReferencePureAction.action kind (ReferenceCheckedEnvironmentStep.opcode h,none) v = some next := by
      cases h <;> cases action <;> assumption
    have wordsEq : words next = words v := by
      cases h <;> simpa [opcode,ReferenceCheckedEnvironmentStep.opcode,ReferenceActionMemoryBounds.span,MachineState.M] using count
    have eventEq : event = .ordinary (ReferenceCheckedEnvironmentStep.charge h) := by
      cases h <;> simpa [ReferenceSystemReadingsTrace.SourcePrice,opcode,ReferenceCheckedEnvironmentStep.opcode,
        ReferenceOrdinaryGas.ordinaryCost,ReferenceCheckedEnvironmentStep.charge,wordsEq] using price
    subst event
    have actual := ReferenceCheckedPureForward.environment pure bound paid
    simp only [runHandler,actual]
    cases h <;> rfl
  | stackControl h =>
    rw [ReferenceCheckedDecode.stack_control h v decoded] at action
    have pure : ReferencePureAction.action kind (ReferenceCheckedStackControlStep.instruction h v) v = some next := by
      cases h <;> cases action <;> assumption
    have wordsEq : words next = words v := by
      cases h <;> simpa [opcode,ReferenceCheckedStackControlStep.opcode,ReferenceCheckedStackControlStep.family,
        ReferencePureAction.opcode,ReferenceActionMemoryBounds.span,MachineState.M] using count
    have eventEq : event = .ordinary (ReferenceCheckedStackControlStep.charge h) := by
      cases h <;> simpa [ReferenceSystemReadingsTrace.SourcePrice,opcode,ReferenceCheckedStackControlStep.opcode,
        ReferenceCheckedStackControlStep.family,ReferencePureAction.opcode,
        ReferenceOrdinaryGas.ordinaryCost,ReferenceCheckedStackControlStep.charge,wordsEq] using price
    subst event
    have actual := ReferenceCheckedPureForward.stack_control context pure bound pcfit paid
    simp only [runHandler,actual]
    cases h <;> rfl
  | load =>
    rw [ReferenceCheckedDecode.nonpush v _ decoded rfl] at action
    cases action with
    | pure hp => simp [opcode,ReferenceCheckedMemoryStore.opcode,ReferenceCheckedCopyLogStep.opcode,ReferenceCheckedTerminalStep.opcode,ReferencePureAction.action,ReferencePureAction.classify] at hp
    | load shape =>
      have eventEq : event = .ordinary (if (sourceReading parent v warm).warm then 100 else 2100) := by
        simpa [ReferenceSystemReadingsTrace.SourcePrice,opcode,ReferenceOrdinaryGas.ordinaryCost,loadAction,words] using price
      subst event
      have actual := ReferenceCheckedStorageForward.load shape bound paid
      simp only [runHandler,actual,opcode]
  | store =>
    rw [ReferenceCheckedDecode.nonpush v _ decoded rfl] at action
    cases action with
    | pure hp => simp [opcode,ReferenceCheckedMemoryStore.opcode,ReferenceCheckedCopyLogStep.opcode,ReferenceCheckedTerminalStep.opcode,ReferencePureAction.action,ReferencePureAction.classify] at hp
    | store permission shape =>
      have eventEq : event = .store (sourceReading parent v warm).warm (sourceReading parent v warm).original
          (sourceReading parent v warm).current (sourceReading parent v warm).new := by
        simpa [ReferenceSystemReadingsTrace.SourcePrice,opcode,storeAction,words] using price
      subst event
      have actual := ReferenceCheckedStorageForward.store permission shape paid
      simp only [runHandler,actual,opcode]
  | memoryStore byte =>
    rw [ReferenceCheckedDecode.nonpush v _ decoded (by cases byte <;> rfl)] at action
    cases byte with
    | false =>
      cases action with
      | pure hp => simp [opcode,ReferenceCheckedMemoryStore.opcode,ReferenceCheckedCopyLogStep.opcode,ReferenceCheckedTerminalStep.opcode,ReferencePureAction.action,ReferencePureAction.classify] at hp
      | @word v off value rest shape =>
        have eventEq : event = .ordinary (3+(ReferenceMemoryCapacity.cost (words (memoryAction v off value.toByteArray rest))-ReferenceMemoryCapacity.cost (words v))) := by
          simpa [ReferenceSystemReadingsTrace.SourcePrice,opcode,ReferenceCheckedMemoryStore.opcode,
            ReferenceOrdinaryGas.ordinaryCost] using price
        subst event
        have actual := ReferenceCheckedMemoryForward.store (kind := kind) (parent := parent) (byte := false) shape aligned paid
        simp [runHandler,actual,opcode,ReferenceCheckedMemoryStore.opcode,ReferenceCheckedMemoryStore.data,warmAfter]
    | true =>
      cases action with
      | pure hp => simp [opcode,ReferenceCheckedMemoryStore.opcode,ReferenceCheckedCopyLogStep.opcode,ReferenceCheckedTerminalStep.opcode,ReferencePureAction.action,ReferencePureAction.classify] at hp
      | @byte v off value rest shape =>
        have eventEq : event = .ordinary (3+(ReferenceMemoryCapacity.cost (words (memoryAction v off ⟨#[UInt8.ofNat value.toNat]⟩ rest))-ReferenceMemoryCapacity.cost (words v))) := by
          simpa [ReferenceSystemReadingsTrace.SourcePrice,opcode,ReferenceCheckedMemoryStore.opcode,
            ReferenceOrdinaryGas.ordinaryCost] using price
        subst event
        have dataEq : ReferenceCheckedMemoryStore.data true value = ⟨#[UInt8.ofNat value.toNat]⟩ := by
          simp only [ReferenceCheckedMemoryStore.data,if_true,ByteArray.mk.injEq,Array.mk.injEq,List.cons.injEq,and_true]
          exact UInt8.ofNat_mod_size
        rw [←dataEq] at paid
        have actual := ReferenceCheckedMemoryForward.store (kind := kind) (parent := parent) (byte := true) shape aligned paid
        simp [runHandler,actual,dataEq,opcode,ReferenceCheckedMemoryStore.opcode,warmAfter]
  | copyLog h =>
    rw [ReferenceCheckedDecode.nonpush v _ decoded (by cases h <;> rfl)] at action
    cases h <;> cases action <;> rename_i hp <;>
      simp [opcode,ReferenceCheckedMemoryStore.opcode,ReferenceCheckedCopyLogStep.opcode,ReferenceCheckedTerminalStep.opcode,ReferencePureAction.action,ReferencePureAction.classify] at hp
  | terminal h =>
    rw [ReferenceCheckedDecode.nonpush v _ decoded (by cases h <;> rfl)] at action
    cases h <;> cases action <;> rename_i hp <;>
      simp [opcode,ReferenceCheckedMemoryStore.opcode,ReferenceCheckedCopyLogStep.opcode,ReferenceCheckedTerminalStep.opcode,ReferencePureAction.action,ReferencePureAction.classify] at hp

#print axioms handler
end Eip8282.Audit.Integrator.ReferenceCheckedSystemForward

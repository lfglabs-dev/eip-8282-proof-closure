import Eip8282.Audit.Integrator.ReferenceCheckedRuntimeTrace
import Eip8282.Audit.Integrator.Topics.ReferenceChecked2
import Eip8282.Audit.Integrator.Topics.ReferenceSource2

/-! Compose one checked running prefix and its literal terminal result into
actual pinned X evaluation, with the same storage/logs/stack/memory/output.
Synthetic gas/fuel are derived from paid work; the source meter is not equated
to the old interpreter gas. STOP advances only the source PC, so observations
exclude terminal PC. REVERT exposes internal observations, not committed state.
Actual source dispatcher/frame/world initialization and enclosing rollback are
separate producers. The explicit initial potential cap is a resource-context
interface, supplied for nested transactions by ReferenceResourceEntryBound. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedCompletion
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterPath
open ReferenceMeterRollback ReferenceMeterBoundary ReferenceExecutionLedger
open ReferenceCheckedTerminalStep
open ReferenceActionMemoryBounds (Aligned)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- Complete non-resource observations at the terminal, without claiming
source and replay PCs or gas meters coincide. -/
structure Observations (parent : ReferenceStorageView.Parent) (v : View) (post : EVM.State) : Prop where
  env : v.env = post.executionEnv
  stack : v.stack = post.stack
  memory : ReferenceMemoryOperations.Related post.toMachineState v.memory
  storage : ReferenceStorageView.Related parent v.storage post.toState
  logs : v.logs = ProtectedLogFrame.project post.executionEnv.codeOwner post.substate
  owner : SystemSpec.HasOwner post.toState

private theorem final_aligned {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v finish : View} {warm finalWarm : Warm} {events : List Event}
    (source : ReferenceSourceReplayTrace.Run kind parent v warm finish finalWarm events)
    (aligned : Aligned v) : Aligned finish := by
  induction source with
  | refl => exact aligned
  | cons action _ _ _ ih => exact ih (ReferenceActionMemoryBounds.preserves_alignment action aligned)

/-- Terminal cost is the actual ordered memory payment, and is included once
with the same running events. No independently supplied work bound. -/
theorem paid_bound {events : List Event} {pre middle final : Meter} {amount : Nat}
    (prefixPaid : runFull events pre = some middle)
    (terminal : runFull [.ordinary amount] middle = some final) :
    ReferenceExecutionPotential.potential final+work events+amount ≤ ReferenceExecutionPotential.potential pre := by
  have paid : runFull (events++[.ordinary amount]) pre = some final := by
    rw [ReferenceCheckedRuntimeTrace.runFull_append,prefixPaid,Option.bind_some,terminal]
  have bound := ReferenceExecutionLedger.bounded (.paid _ paid)
  simpa only [work,List.map_append,List.sum_append,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,eventWork,Nat.add_zero,Nat.add_assoc] using bound

private theorem observations_return {parent : ReferenceStorageView.Parent} {v : View}
    {off len : UInt256} {rest : Stack UInt256} {post : EVM.State}
    (aligned : Aligned v) (result : ReferenceReturnView.Result parent v off len rest post) :
    Observations parent (ReferenceCheckedCopyLogStep.expanded v off len rest) post := by
  refine ⟨result.env,result.stack.symm,?_,result.storage,result.logs,result.owner⟩
  have capacity := ReferenceCheckedCopyLogStep.expanded_capacity v off len aligned
  change ReferenceMemoryOperations.Related post.toMachineState
    (ReferenceMemoryOperations.extend v.memory (v.memory.size+(ReferenceMemoryExpansionSource.calculate v.memory.size off.toNat len.toNat).bytes))
  rw [capacity]
  exact result.memory

theorem stop {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    {pre middle : Meter} {result : End}
    (actual : ReferenceCheckedRuntimeTrace.Run kind parent (initial c tx) warm pre finish finalWarm middle events)
    (terminal : ReferenceCheckedTerminalStep.run .stop finish middle ByteArray.empty = .ok result)
    (decoded : ReferenceDecodeSites.referenceDecode finish.env.code finish.pc = some (.STOP,none))
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000) :
    result.halt = .stop ∧ result.meter = middle ∧
    ∃ post, X (events.length+2) (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩)
      (ReferenceSourceReplayEntry.call c events 0).entry = .ok (.success post result.output) ∧
      Observations parent result.view post := by
  rw [ReferenceCheckedTerminalStep.stop] at terminal
  cases terminal
  obtain ⟨source,paid,_⟩ := actual.extract (by simp [initial]) (ReferenceActionMemoryBounds.empty_aligned _ rfl)
  have payment := ReferenceExecutionLedger.bounded (.paid _ paid)
  have bound : work events ≤ 30000000 := by omega
  have halt : ReferenceSourceReplayTrace.instruction finish = (.STOP,none) := by
    simp only [ReferenceSourceReplayTrace.instruction,decoded,Option.getD_some]
  obtain ⟨_,post,_,_,_,execution,related⟩ := ReferenceSourceReplayCompletion.stop c source slots owner warmRelated bound halt
  exact ⟨rfl,rfl,post,execution,related.env,related.stack,related.memory,related.storage,related.logs,related.owner⟩

/-- RETURN and REVERT preserve the same complete terminal observations. The
reverted X result carries only gas/output; post is its internal witness. -/
theorem slice {kind : Kind} (c : XiCall kind) {parent : ReferenceStorageView.Parent}
    {tx : ReferenceStorageView.Tx} {warm finalWarm : Warm} {finish : View} {events : List Event}
    {pre middle : Meter} {result : End} {h : Halt}
    (notStop : h ≠ .stop)
    (actual : ReferenceCheckedRuntimeTrace.Run kind parent (initial c tx) warm pre finish finalWarm middle events)
    (terminal : ReferenceCheckedTerminalStep.run h finish middle ByteArray.empty = .ok result)
    (decoded : ReferenceDecodeSites.referenceDecode finish.env.code finish.pc = some (opcode h,none))
    (slots : ReferenceStorageView.Related parent tx c.entry.toState)
    (owner : SystemSpec.HasOwner c.entry.toState) (warmRelated : WarmRelated warm c.entry)
    (grant : ReferenceExecutionPotential.potential pre ≤ 30000000) :
    result.halt = h ∧ ∃ amount post,
      runFull (events++[.ordinary amount]) pre = some result.meter ∧
      X (events.length+2) (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩)
        (ReferenceSourceReplayEntry.call c events amount).entry =
          (if h = .returned then .ok (.success post result.output) else .ok (.revert post.gasAvailable result.output)) ∧
      Observations parent result.view post := by
  obtain ⟨source,paid,_⟩ := actual.extract (by simp [initial]) (ReferenceActionMemoryBounds.empty_aligned _ rfl)
  have aligned := final_aligned source (ReferenceActionMemoryBounds.empty_aligned _ rfl)
  obtain ⟨off,len,rest,shape,halt,view,output,terminalPaid⟩ := ReferenceCheckedTerminalStep.slice notStop aligned terminal
  have budget := paid_bound paid terminalPaid
  have bound : work events+ReferenceTerminalReplay.charge finish off len ≤ 30000000 := by omega
  have decode : ReferenceSourceReplayTrace.instruction finish = (opcode h,none) := by
    simp only [ReferenceSourceReplayTrace.instruction,decoded,Option.getD_some]
  have payment : runFull (events++[.ordinary (ReferenceTerminalReplay.charge finish off len)]) pre = some result.meter := by
    rw [ReferenceCheckedRuntimeTrace.runFull_append,paid,Option.bind_some,terminalPaid]
  refine ⟨halt,ReferenceTerminalReplay.charge finish off len,?_⟩
  cases h with
  | stop => exact False.elim (notStop rfl)
  | returned =>
    obtain ⟨_,post,_,_,execution,observed⟩ := ReferenceSourceReplayCompletion.returned c source slots owner warmRelated shape bound decode
    refine ⟨post,payment,?_,?_⟩
    · simpa only [output,if_true] using execution
    · rw [view]; exact observations_return aligned observed
  | reverted =>
    obtain ⟨_,post,_,_,execution,observed⟩ := ReferenceSourceReplayCompletion.reverted c source slots owner warmRelated shape bound decode
    refine ⟨post,payment,?_,?_⟩
    · simpa only [output,reduceCtorEq,if_false] using execution
    · rw [view]; exact observations_return aligned observed

#print axioms paid_bound
#print axioms stop
#print axioms slice
end Eip8282.Audit.Integrator.ReferenceCheckedCompletion

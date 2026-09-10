import Eip8282.Audit.Integrator.JournalCommittedLogs
import Eip8282.Audit.Integrator.JournalRetainedWork

/-! Cardinality counts retained actual invocation paths, never distinct payloads.
The occurrence list must map to the canonical retained list; its existence is
supplied by the actual traversal. No log equality or per-call domain is assumed. -/
namespace Eip8282.Audit.Integrator.JournalCommittedCardinality
open EvmYul EvmYul.EVM
open NestedEvents JournalWorldPaths JournalRetainedCalls JournalCommittedLogs
open ReachableCalls (Contract)
open JournalInvariant (modelKind)
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem submitted_iff {kind : Contract} {root : Request} {rr : root.Outcome} {rt : EventTree}
    (o : Occurrence kind root rr rt) (retained : Retained kind root rr rt o.path) :
    JournalRetainedWork.Submitted kind root rr rt o.path ↔
      o.transition.success = true ∧ o.transition.call.caller ≠ Eip8282.Audit.EvmRunner.sysAddr ∧
        o.transition.call.calldata.size ≠ 0 := by
  constructor
  · rintro ⟨f,a,cr,w,g,ss,out,survives,hu,hn⟩
    obtain ⟨hf,ha,hr⟩ := o.located.identity survives.actual
    have hz : o.transition.success = true :=
      congrArg (fun t => t.2.2.2.2.1) (Except.ok.inj hr)
    refine ⟨hz,?_,?_⟩
    · simpa only [o.context,ha,ThetaArgs.context] using hu
    · simpa only [o.context,ha,ThetaArgs.context] using hn
  · rintro ⟨hz,hu,hn⟩
    obtain ⟨f,a,r,survives⟩ := retained
    obtain ⟨hf,ha,hr⟩ := o.located.identity survives.actual
    have hs : Survives kind root rr rt o.path o.fuel o.args
        (.ok (o.transition.created,o.after,o.transition.gas,o.transition.substate,true,o.transition.output)) := by
      rw [←hf,←ha,←hr] at survives
      simpa only [hz] using survives
    exact ⟨o.fuel,o.args,o.transition.created,o.after,o.transition.gas,o.transition.substate,
      o.transition.output,hs,by simpa only [o.context,ThetaArgs.context] using hu,by simpa only [o.context,ThetaArgs.context] using hn⟩

theorem contribution_length {kind : Contract} {root : Request} {rr : root.Outcome} {rt : EventTree}
    (o : Occurrence kind root rr rt) (retained : Retained kind root rr rt o.path) :
    (contribution o).length = if JournalRetainedWork.Submitted kind root rr rt o.path then 1 else 0 := by
  classical
  rw [submitted_iff o retained]
  simp only [contribution,ProtectedCallLogSeries.contribution]
  split <;> rename_i hz
  · split <;> rename_i hu
    · simp [hz,hu]
    · split <;> rename_i hn
      · simp [hz,hu,hn]
      · simp [hz,hu,hn]
  · simp [hz]

private theorem list_length {kind : Contract} {root : Request} {rr : root.Outcome} {rt : EventTree}
    (os : List (Occurrence kind root rr rt))
    (valid : ∀ o ∈ os, Retained kind root rr rt o.path) :
    (os.flatMap contribution).length =
      ((os.map (·.path)).filter (fun p => decide (JournalRetainedWork.Submitted kind root rr rt p))).length := by
  classical
  induction os with
  | nil => rfl
  | cons o rest ih =>
    have ho := contribution_length o (valid o (by simp))
    have ht := ih (fun a ha => valid a (by simp [ha]))
    simp only [List.flatMap_cons,List.length_append,List.map_cons,List.filter_cons]
    rw [ho,ht]
    split <;> simp_all [Nat.add_comm]

theorem emitted_length {kind : Contract} {root : Request} {rr : root.Outcome} {rt : EventTree}
    (os : List (Occurrence kind root rr rt))
    (paths : os.map (·.path) = retainedList kind root rr rt) :
    (emitted kind root rr rt [] root rr rt).length = JournalRetainedWork.count kind root rr rt := by
  classical
  have he := emitted_replay (basePath := []) os (by simpa using paths)
  rw [he,list_length os]
  · rw [paths]
    rfl
  · intro o ho
    apply retainedList_mem_iff.mp
    rw [←paths]
    exact List.mem_map.mpr ⟨o,ho,rfl⟩

#print axioms submitted_iff
#print axioms contribution_length
#print axioms emitted_length
end Eip8282.Audit.Integrator.JournalCommittedCardinality

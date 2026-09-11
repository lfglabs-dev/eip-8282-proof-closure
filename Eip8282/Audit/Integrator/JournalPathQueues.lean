import Eip8282.Audit.Integrator.JournalWorldPaths
import Eip8282.Audit.Integrator.JournalProvenanceInterface

/-! Interpret actual retained protected-call world paths over a chosen queue.
Every protected edge is tied to an actual root ThetaAt occurrence. Its local
domain is derived from the original execution checkpoint, not supplied with
the edge. Frames preserve the chosen queue; actual rollback paths restore the
checkpoint queue. This interpreter alone does not establish completeness or
uniqueness of the retained occurrence list, nor committed-log survival. -/
namespace Eip8282.Audit.Integrator.JournalPathQueues
open EvmYul EvmYul.EVM
open NestedEvents JournalWorldPaths JournalExecution
open ReachableCalls (Contract address runtime)
open JournalInvariant (modelKind)
open QueueInvariant SystemSpec
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

abbrev Queue (kind : Contract) := List (Record (modelKind kind))

def replay {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree} :
    List (Occurrence kind root result tree) → Queue kind → Queue kind
  | [], queue => queue
  | o::rest, queue => replay rest
      (JournalProvenanceInterface.after (modelKind kind) o.transition.call o.transition.success queue)

theorem replay_append {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree}
    (first second : List (Occurrence kind root result tree)) (queue : Queue kind) :
    replay (first++second) queue = replay second (replay first queue) := by
  induction first generalizing queue with
  | nil => rfl
  | cons o rest ih => exact ih _

/-- The actual original checkpoint supplies the domain for whichever chosen
physical queue the preceding path has produced. -/
theorem occurrence_domain {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree}
    (cert : Cert root result tree) (adequate : FuelAdequacy.Adequate root)
    (budget : Nat) (hb : budget+tree.count < 2^128) (ready : Ready kind budget root)
    (inputs : NestedProtectedJournal.Inputs root result tree)
    (o : Occurrence kind root result tree) (queue : Queue kind)
    (represented : Represents (modelKind kind) (worldSlot o.before (address kind)) queue) :
    DirectDrain.Domain (modelKind kind) o.transition.call queue
      (budget+NestedJournalBudget.before tree o.path) := by
  have callReady := (JournalCheckpoints.from_resources cert adequate budget hb ready inputs).2
    o.path o.fuel o.args _ o.located
  have hw : o.args.world = o.before := by
    have h := o.transition.pre
    rw [o.context] at h
    exact h
  have hi : JournalInvariant.Invariant kind (budget+NestedJournalBudget.before tree o.path) o.before := by
    rw [←hw]
    exact callReady.1.1
  obtain ⟨inner,hcert,hinterval⟩ := NestedJournalBudget.call_interval o.located
  have hfit : o.transition.call.calldata.size < UInt256.size := by
    rw [o.context]
    exact (inputs o.path o.fuel o.args _ o.located).1
  exact JournalProvenanceInterface.transition_domain o.transition ⟨hi,represented⟩ (by omega) hfit

/-- The final represented queue is precisely the replay of retained actual
calls, including capped FIFO drops and failed/getter no-ops. -/
theorem represented_replay {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree}
    (cert : Cert root result tree) (adequate : FuelAdequacy.Adequate root)
    (budget : Nat) (hb : budget+tree.count < 2^128) (ready : Ready kind budget root)
    (inputs : NestedProtectedJournal.Inputs root result tree)
    {occurrences : List (Occurrence kind root result tree)} {before after : World}
    (path : Path kind root result tree occurrences before after) (queue : Queue kind)
    (represented : Represents (modelKind kind) (worldSlot before (address kind)) queue) :
    Represents (modelKind kind) (worldSlot after (address kind)) (replay occurrences queue) := by
  induction path generalizing queue with
  | frame hf =>
    have he := funext hf.storage
    rw [he]
    exact represented
  | call o =>
    have hd := occurrence_domain cert adequate budget hb ready inputs o queue represented
    have hc : o.transition.call.code = Eip8282.Audit.Correspondence.runtimeCode (modelKind kind) := by
      cases kind <;> exact o.transition.pinned.code
    have hq := JournalProvenanceInterface.completed_queue (modelKind kind) o.transition.call hc queue
      (budget+NestedJournalBudget.before tree o.path) hd o.transition.executed
    rw [o.transition.pinned.target] at hq
    exact hq
  | trans first second ih₁ ih₂ =>
    rw [replay_append]
    exact ih₂ _ (ih₁ queue represented)

/-- Uniqueness connects any independently chosen final physical queue to the
same replay; equal byte records are still not submission occurrence IDs. -/
theorem final_queue_eq {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree}
    (cert : Cert root result tree) (adequate : FuelAdequacy.Adequate root)
    (budget : Nat) (hb : budget+tree.count < 2^128) (ready : Ready kind budget root)
    (inputs : NestedProtectedJournal.Inputs root result tree)
    {occurrences : List (Occurrence kind root result tree)} {before after : World}
    (path : Path kind root result tree occurrences before after) (queue finalQueue : Queue kind)
    (pre : Represents (modelKind kind) (worldSlot before (address kind)) queue)
    (post : Represents (modelKind kind) (worldSlot after (address kind)) finalQueue) :
    finalQueue = replay occurrences queue :=
  JournalProvenanceInterface.represents_unique post
    (represented_replay cert adequate budget hb ready inputs path queue pre)

/-- A retained successful nonempty user call identifies source bytes. This is
an actual call occurrence, not a unique ID inferred from record contents. -/
def Submitted {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree}
    (o : Occurrence kind root result tree) (record : Record (modelKind kind)) : Prop :=
  o.transition.success = true ∧
    o.transition.call.caller ≠ Eip8282.Audit.EvmRunner.sysAddr ∧
    o.transition.call.calldata.size ≠ 0 ∧
    record = DirectDrain.inputRecord (modelKind kind) o.transition.call

private theorem after_origin {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree}
    (o : Occurrence kind root result tree) (queue : Queue kind) (record : Record (modelKind kind))
    (hm : record ∈ JournalProvenanceInterface.after (modelKind kind)
      o.transition.call o.transition.success queue) : record ∈ queue ∨ Submitted o record := by
  cases hs : o.transition.success with
  | false =>
    exact Or.inl (by simpa [JournalProvenanceInterface.after,hs] using hm)
  | true =>
    by_cases hc : o.transition.call.caller = Eip8282.Audit.EvmRunner.sysAddr
    · have hd : record ∈ queue.drop (min queue.length (SystemDataSpec.cap (modelKind kind))) := by
        simpa [JournalProvenanceInterface.after,hs,hc] using hm
      exact Or.inl (List.drop_subset _ _ hd)
    · by_cases hn : o.transition.call.calldata.size = 0
      · exact Or.inl (by simpa [JournalProvenanceInterface.after,DirectDrain.userQueue,hs,hc,hn] using hm)
      · have ha : record ∈ queue ∨ record = DirectDrain.inputRecord (modelKind kind) o.transition.call := by
          simpa [JournalProvenanceInterface.after,DirectDrain.userQueue,hs,hc,hn] using hm
        rcases ha with hq | he
        · exact Or.inl hq
        · exact Or.inr ⟨hs,hc,hn,he⟩

/-- Every final record comes from the initial queue or a retained actual
successful user submission. FIFO drops cannot manufacture source records. -/
theorem replay_origin {kind : Contract} {root : Request} {result : root.Outcome} {tree : EventTree}
    (occurrences : List (Occurrence kind root result tree)) (queue : Queue kind)
    (record : Record (modelKind kind)) (hm : record ∈ replay occurrences queue) :
    record ∈ queue ∨ ∃ o ∈ occurrences, Submitted o record := by
  induction occurrences generalizing queue with
  | nil => exact Or.inl hm
  | cons o rest ih =>
    rcases ih _ hm with hfirst | ⟨other,ho,hs⟩
    · rcases after_origin o queue record hfirst with hq | hs
      · exact Or.inl hq
      · exact Or.inr ⟨o,by simp,hs⟩
    · exact Or.inr ⟨other,List.mem_cons_of_mem _ ho,hs⟩

#print axioms occurrence_domain
#print axioms represented_replay
#print axioms final_queue_eq
#print axioms replay_origin
end Eip8282.Audit.Integrator.JournalPathQueues

import Eip8282.Audit.Integrator.ReferenceCheckedRuntimeTrace
import Eip8282.Audit.Integrator.Topics.Reference4
import Eip8282.Audit.Integrator.Topics.ReferenceChecked

/-! Finite, owner-local, typed storage support produced by the actual protected
handler trace. The support list is only a dictionary-enumeration witness: it is
not a count of appends, persisted records or call-tree occurrences. Consumer:
SYSTEM receipt incorporation into the source block tracker and ordered pair.
No property of arbitrary byte-array storage keys is assumed. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemBlockFootprint
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceStorageView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

structure Support (owner : AccountAddress) (tx : Tx) (keys : List UInt256) : Prop where
  writes : ∀ a k value, tx.writes a k = some value →
    a = owner ∧ ∃ q ∈ keys, k = q.toByteArray
  reads : ∀ a k, (a,k) ∈ tx.reads →
    a = owner ∧ ∃ q ∈ keys, k = q.toByteArray
  created : tx.created = ∅

theorem empty (owner : AccountAddress) :
    Support owner ⟨fun _ _ => none,∅,∅⟩ [] := by
  refine ⟨?_,?_,rfl⟩
  · intro a k value hw; contradiction
  · intro a k hr; exact False.elim hr

private theorem weaken {owner : AccountAddress} {tx : Tx} {keys : List UInt256}
    (h : Support owner tx keys) (q : UInt256) : Support owner tx (q::keys) := by
  refine ⟨?_,?_,h.created⟩
  · intro a k value hw
    obtain ⟨ha,r,hr,hk⟩ := h.writes a k value hw
    exact ⟨ha,r,List.mem_cons_of_mem q hr,hk⟩
  · intro a k hr
    obtain ⟨ha,r,hr,hk⟩ := h.reads a k hr
    exact ⟨ha,r,List.mem_cons_of_mem q hr,hk⟩

private theorem read {owner : AccountAddress} {tx : Tx} {keys : List UInt256}
    (h : Support owner tx keys) (q : UInt256) :
    Support owner (readTracked tx owner q.toByteArray) (q::keys) := by
  refine ⟨(weaken h q).writes,?_,h.created⟩
  intro a k hr
  change (a,k) ∈ insert (owner,q.toByteArray) tx.reads at hr
  rcases Set.mem_insert_iff.mp hr with he | hr
  · cases he
    exact ⟨rfl,q,by simp,rfl⟩
  · exact (weaken h q).reads a k hr

private theorem write_support {owner : AccountAddress} {tx : Tx} {keys : List UInt256}
    (h : Support owner tx keys) (q value : UInt256) (member : q ∈ keys) :
    Support owner (write tx owner q.toByteArray value) keys := by
  classical
  refine ⟨?_,h.reads,h.created⟩
  intro a k stored hw
  change (if a = owner ∧ k = q.toByteArray then some value else tx.writes a k) = some stored at hw
  by_cases he : a = owner ∧ k = q.toByteArray
  · exact ⟨he.1,q,member,he.2⟩
  · rw [if_neg he] at hw
    exact h.writes a k stored hw

private theorem pure_env {kind : Kind} {instr : Instruction} {v next : View}
    (h : ReferencePureAction.action kind instr v = some next) : next.env = v.env := by
  unfold ReferencePureAction.action at h
  cases hc : ReferencePureAction.classify instr.1 with
  | none => simp only [hc,Option.bind_none] at h; cases h
  | some p =>
    simp only [hc,Option.bind_some] at h
    unfold ReferencePureAction.familyAction at h
    repeat' first | split at h | (cases h <;> rfl)

/-- A successful nonterminal action supplies its typed support, including BAL
reads that remain meaningful even if a later enclosing frame rolls back. -/
theorem action {kind : Kind} {parent : Parent} {instr : Instruction}
    {v next : View} {keys : List UInt256}
    (effect : ReferenceRuntimeAction.Action kind parent instr v next)
    (support : Support v.env.codeOwner v.storage keys) :
    next.env = v.env ∧ ∃ more, Support next.env.codeOwner next.storage (more++keys) := by
  cases effect with
  | base effect =>
    cases effect with
    | pure hp =>
      have he := pure_env hp
      refine ⟨he,[],?_⟩
      simpa only [List.nil_append,he,ReferenceActionMetadata.pure_storage hp] using support
    | load => exact ⟨rfl,[_],read support _⟩
    | store =>
      exact ⟨rfl,[_],write_support (read support _) _ _ (by simp)⟩
    | word => exact ⟨rfl,[],support⟩
    | byte => exact ⟨rfl,[],support⟩
  | copy => exact ⟨rfl,[],support⟩
  | log => exact ⟨rfl,[],support⟩

/-- Arbitrary finite traces produce a finite journal; no final footprint or
fixed iteration bound is a premise. -/
theorem trace {kind : Kind} {parent : Parent} {v finish : View}
    {warm finalWarm : ReferenceSourceReadings.Warm} {events : List ReferenceMeterPath.Event}
    (run : ReferenceSourceReplayTrace.Run kind parent v warm finish finalWarm events)
    {keys : List UInt256} (support : Support v.env.codeOwner v.storage keys) :
    finish.env = v.env ∧ ∃ more, Support finish.env.codeOwner finish.storage (more++keys) := by
  induction run generalizing keys with
  | refl => exact ⟨rfl,[],support⟩
  | cons effect price stack tail ih =>
    obtain ⟨he,more,hs⟩ := action effect support
    obtain ⟨he',later,hs'⟩ := ih hs
    exact ⟨he'.trans he,later++more,by simpa only [List.append_assoc] using hs'⟩

theorem checked {kind : Kind} {parent : Parent} {v finish : View}
    {warm finalWarm : ReferenceSourceReadings.Warm}
    {meter final : ReferenceMeterRollback.Meter} {events : List ReferenceMeterPath.Event}
    (run : ReferenceCheckedRuntimeTrace.Run kind parent v warm meter finish finalWarm final events)
    (stack : v.stack.length ≤ 1024) (aligned : ReferenceActionMemoryBounds.Aligned v)
    {keys : List UInt256} (support : Support v.env.codeOwner v.storage keys) :
    finish.env = v.env ∧ ∃ more, Support finish.env.codeOwner finish.storage (more++keys) :=
  trace (run.extract stack aligned).1 support

private theorem terminal_fields {halt : ReferenceCheckedTerminalStep.Halt}
    {v : View} {meter : ReferenceMeterRollback.Meter} {output : ByteArray}
    {ended : ReferenceCheckedTerminalStep.End}
    (actual : ReferenceCheckedTerminalStep.run halt v meter output = .ok ended) :
    ended.view.env = v.env ∧ ended.view.storage = v.storage := by
  unfold ReferenceCheckedTerminalStep.run at actual
  repeat' first | split at actual | (cases actual <;> exact ⟨rfl,rfl⟩)

theorem terminal {destinations : List Nat} {ownerExists : Bool} {parent : Parent}
    {v : View} {warm : ReferenceSourceReadings.Warm} {meter : ReferenceMeterRollback.Meter}
    {output : ByteArray} {ended : ReferenceCheckedTerminalStep.End} {keys : List UInt256}
    (actual : ReferenceCheckedDispatch.run destinations ownerExists parent v warm meter output = .terminal ended)
    (support : Support v.env.codeOwner v.storage keys) :
    ended.view.env = v.env ∧ Support ended.view.env.codeOwner ended.view.storage keys := by
  obtain ⟨_,run,_⟩ := ReferenceCheckedDispatchTerminal.terminal actual
  have fields := terminal_fields run
  exact ⟨fields.1,by simpa only [fields.1,fields.2] using support⟩

/-- Every key enumerated by the actual journal passes the source BAL's
32-byte storage-key gate. This says nothing about the whole block's BAL cap. -/
theorem keys_fit {owner : AccountAddress} {tx : Tx} {keys : List UInt256}
    (support : Support owner tx keys) :
    (∀ a k value, tx.writes a k = some value → k.size = 32) ∧
    (∀ a k, (a,k) ∈ tx.reads → k.size = 32) := by
  constructor
  · intro a k value hw
    obtain ⟨_,q,_,rfl⟩ := support.writes a k value hw
    exact UInt256.size_toByteArray q
  · intro a k hr
    obtain ⟨_,q,_,rfl⟩ := support.reads a k hr
    exact UInt256.size_toByteArray q

theorem foreign_commit {owner : AccountAddress} {tx : Tx} {keys : List UInt256}
    (support : Support owner tx keys) (parent : Parent) (a : AccountAddress)
    (foreign : a ≠ owner) (k : ByteArray) :
    parentRead (commit parent tx) a k = parentRead parent a k := by
  rw [commit_read]
  have empty : tx.writes a k = none := by
    cases hw : tx.writes a k with
    | none => rfl
    | some value => exact False.elim (foreign (support.writes a k value hw).1)
  simp only [current,empty,Option.getD_none]

#print axioms action
#print axioms empty
#print axioms trace
#print axioms checked
#print axioms terminal
#print axioms keys_fit
#print axioms foreign_commit
end Eip8282.Audit.Integrator.ReferenceSystemBlockFootprint

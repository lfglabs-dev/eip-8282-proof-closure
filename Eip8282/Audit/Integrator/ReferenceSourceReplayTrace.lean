import Eip8282.Audit.Integrator.ReferenceRuntimeReplay
import Eip8282.Audit.Integrator.ReferenceActionMemoryBounds
import Eip8282.Audit.Integrator.ReferenceAllDecode

/-! Reconstruct an arbitrary finite protected trace from ordered source-shaped
Actions and Prices. No old trace, old success, per-step memory cap or fee-loop
iteration limit is supplied. Source execution extraction, checked stack-history
production and terminal completion remain separate obligations. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceReplayTrace
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceRuntimeAction ReferenceRuntimeReadings
open ReferenceSourceReadings ReferenceMeterPath ReferenceExecutionLedger
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def instruction (v : View) : Instruction :=
  (ReferenceDecodeSites.referenceDecode v.env.code v.pc).getD (.STOP,none)

/-- One event per actual source-shaped action, including free actions; no old
states occur in this relation. The source interpreter must produce its evidence. -/
inductive Run (kind : Kind) (parent : ReferenceStorageView.Parent) :
    View → Warm → View → Warm → List Event → Prop where
  | refl (v : View) (warm : Warm) : Run kind parent v warm v warm []
  | cons {v next finish : View} {warm finalWarm : Warm} {event : Event} {events : List Event}
      (effect : Action kind parent (instruction v) v next)
      (price : Price parent v warm next (instruction v).1 event)
      (stack : next.stack.length ≤ 1024)
      (tail : Run kind parent next (warmAfter (instruction v).1 v warm) finish finalWarm events) :
      Run kind parent v warm finish finalWarm (event::events)

theorem Run.memory_le {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v finish : View} {warm finalWarm : Warm} {events : List Event}
    (source : Run kind parent v warm finish finalWarm events) :
    ReferenceMemoryCapacity.cost (words finish) ≤ ReferenceMemoryCapacity.cost (words v)+work events := by
  induction source with
  | refl => simp [work]
  | cons effect price stack tail ih =>
    have growth := ReferenceReplayMemoryCost.memory_component price
    simp only [work,List.map_cons,List.sum_cons] at ih ⊢
    omega

theorem Run.stack_bound {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v finish : View} {warm finalWarm : Warm} {events : List Event}
    (source : Run kind parent v warm finish finalWarm events)
    (initial : v.stack.length ≤ 1024) : finish.stack.length ≤ 1024 := by
  induction source with
  | refl => exact initial
  | cons effect price stack tail ih => exact ih stack

private theorem nonhalting {kind : Kind} {parent : ReferenceStorageView.Parent}
    {v next : View} {instr : Instruction}
    (effect : Action kind parent instr v next) (machine : MachineState) : H machine instr.1 = none := by
  cases effect with
  | base base =>
    cases base with
    | pure effect =>
      unfold ReferencePureAction.action at effect
      cases selected : ReferencePureAction.classify instr.1 with
      | none => simp only [selected,Option.bind_none] at effect; contradiction
      | some p =>
        rw [←ReferencePureAction.classify_sound selected]
        cases p <;> try rfl
        rename_i b
        cases b <;> rfl
    | load => rfl
    | store => rfl
    | word => rfl
    | byte => rfl
  | copy => rfl
  | log => rfl

private theorem aligned {parent : ReferenceStorageView.Parent} {v : View} {pre : EVM.State}
    (related : Related parent v pre) : ReferenceActionMemoryBounds.Aligned v := by
  change v.memory.size = 32*words v
  rw [words_related related,related.memory.size]

private theorem span_related {parent : ReferenceStorageView.Parent} {v : View} {pre : EVM.State}
    (related : Related parent v pre) (op : Operation .EVM) :
    ReferenceActionMemoryBounds.span v op = RuntimeMemoryMonotone.span pre op := by
  unfold ReferenceActionMemoryBounds.span RuntimeMemoryMonotone.span
  split <;> simp only [related.stack]

/-- A literal source memory cost below the largest selected frame grant fits
both supported hosts. This is a derived numerical bound, not an assumed cap. -/
theorem host_of_cost {words : Nat} (bound : ReferenceMemoryCapacity.cost words ≤ 30000000) :
    32*words < 2^System.Platform.numBits := by
  unfold ReferenceMemoryCapacity.cost at bound
  rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega

/-- Construct the same event-annotated actual trace, preserving warmth, created
metadata and final source view. The final gas reserve remains available for a
separately composed terminal. Fuel depends on the actual finite trace length. -/
theorem replay {kind : Kind} {parent : ReferenceStorageView.Parent} {initialCreated : Set AccountAddress}
    {v finish : View} {warm finalWarm : Warm} {events : List Event}
    (source : Run kind parent v warm finish finalWarm events) (fuel : Nat)
    {pre : EVM.State} (related : Related parent v pre)
    (site : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (warmRelated : WarmRelated warm pre) (created : v.storage.created = initialCreated)
    (domain : ReferenceMemoryCapacity.cost (words v)+work events ≤ 30000000)
    (budget : 222*work events+2301 ≤ pre.gasAvailable.toNat) :
    ∃ post trace,
      Coupled kind parent initialCreated (events.length+fuel+1) pre v warm trace (fuel+1) post finish finalWarm events ∧
      Related parent finish post ∧ RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) post ∧
      WarmRelated finalWarm post ∧ finish.storage.created = initialCreated ∧
      2301 ≤ post.gasAvailable.toNat ∧ pre.gasAvailable.toNat ≤ post.gasAvailable.toNat+222*work events := by
  induction source generalizing pre with
  | refl v warm =>
    refine ⟨pre,[],?_,related,site,warmRelated,created,budget,by simp [work]⟩
    simpa using (Coupled.refl (kind := kind) (parent := parent)
      (initialCreated := initialCreated) (fuel+1) pre v warm)
  | @cons v next finish warm finalWarm event events effect price stack tail ih =>
    have decoded : decodeAt pre = instruction v := by
      unfold instruction
      rw [related.env,related.pc,site.1,ReferenceRuntimeSites.code_eq]
      exact ReferenceAllDecode.decode_matches site
    have actualEffect : Action kind parent (decodeAt pre) v next := by simpa only [decoded] using effect
    have actualPrice : Price parent v warm next (decodeAt pre).1 event := by simpa only [decoded] using price
    have growth := ReferenceReplayMemoryCost.memory_component price
    have memoryNext : ReferenceMemoryCapacity.cost (words next)+work events ≤ 30000000 := by
      simp only [work,List.map_cons,List.sum_cons] at domain
      unfold work
      omega
    have capacity := (ReferenceActionMemoryBounds.computed effect (aligned related)).2
    have host : 32*MachineState.M (words v) (RuntimeMemoryMonotone.span pre (decodeAt pre).1).1
        (RuntimeMemoryMonotone.span pre (decodeAt pre).1).2 < 2^System.Platform.numBits := by
      rw [decoded,←span_related related,←capacity]
      exact host_of_cost (by omega)
    have edgeBudget : 222*eventWork event+2301 ≤ pre.gasAvailable.toNat := by
      simp only [work,List.map_cons,List.sum_cons] at budget
      omega
    obtain ⟨middle,hz,hs,nextRelated,debit,cost⟩ := ReferenceRuntimeReplay.priced_step
      (events.length+fuel) related site actualEffect stack host actualPrice edgeBudget
    have hh := nonhalting actualEffect middle.toMachineState
    have nextSite := RuntimeExecutionScope.accepted_next site hz hs hh
    have nextWarm := ReferenceStorageWarmth.accepted_warm site hz hs related warmRelated
    have nextCreated := (ReferenceRuntimeReadings.created actualEffect).trans created
    have tailBudget : 222*work events+2301 ≤ middle.gasAvailable.toNat := by
      simp only [work,List.map_cons,List.sum_cons] at budget
      unfold work
      omega
    obtain ⟨post,trace,coupled,finalRelated,finalSite,finalWarmRelated,finalCreated,reserve,total⟩ :=
      ih nextRelated nextSite (by simpa only [decoded] using nextWarm) nextCreated memoryNext tailBudget
    have actual : XStepAt (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩)
        (events.length+fuel+1) (C' pre (decodeAt pre).1) pre middle := ⟨_,hz,hs,hh⟩
    refine ⟨post,((events.length+fuel+1,C' pre (decodeAt pre).1,decodeAt pre)::trace),?_,
      finalRelated,finalSite,finalWarmRelated,finalCreated,reserve,?_⟩
    · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,decoded] using
        Coupled.cons actual decoded related nextRelated warmRelated created actualEffect
          (ReferenceSourceReadings.reading_eq related warmRelated created) actualPrice
          (by simpa only [decoded] using coupled)
    · simp only [work,List.map_cons,List.sum_cons]
      unfold work at total
      omega

#print axioms host_of_cost
#print axioms Run.memory_le
#print axioms Run.stack_bound
#print axioms replay
end Eip8282.Audit.Integrator.ReferenceSourceReplayTrace

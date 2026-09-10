import Eip8282.Audit.Integrator.ReferenceRuntimeTrace
import Eip8282.Audit.Integrator.ReferenceActionMetadata
import Eip8282.Audit.Integrator.ReferenceStorageWarmth
import Eip8282.Audit.Integrator.ReferenceCopyLogGas
import Eip8282.Audit.Integrator.RuntimeMemoryCharges

/-! Exact source readings and literal prices on the same viewed runtime trace,
including user COPY and LOG0. The input trace is already derived from execution;
this annotation does not choose a second trace or arbitrary storage readings.
Initial source parent/created/warm bindings and source execution remain distinct. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeReadings
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceRuntimeAction ReferenceRuntimeTrace
open ReferenceSourceReadings ReferenceMeterPath
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

theorem created {kind : Kind} {parent : ReferenceStorageView.Parent}
    {instr : Instruction} {v next : View} (h : Action kind parent instr v next) :
    next.storage.created = v.storage.created := by
  cases h with
  | base h => exact ReferenceActionMetadata.created h
  | copy => rfl
  | log => rfl

noncomputable def Price (parent : ReferenceStorageView.Parent) (v : View) (w : Warm)
    (next : View) (op : Operation .EVM) (event : Event) : Prop :=
  let reading := sourceReading parent v w
  let memoryCost := ReferenceMemoryCapacity.cost (words next)-ReferenceMemoryCapacity.cost (words v)
  if op = .SSTORE then memoryCost = 0 ∧
    event = .store reading.warm reading.original reading.current reading.new
  else ∃ n, ReferenceCopyLogGas.ordinaryCost op reading.warm v.stack = some n ∧
    event = .ordinary (n+memoryCost)

inductive Coupled (kind : Kind) (parent : ReferenceStorageView.Parent) (initialCreated : Set AccountAddress) :
    Nat → EVM.State → View → Warm → List Labelled → Nat → EVM.State → View → Warm → List Event → Prop where
  | refl (fuel : Nat) (pre : EVM.State) (v : View) (w : Warm) :
      Coupled kind parent initialCreated fuel pre v w [] fuel pre v w []
  | cons {fuel gasCost rem : Nat} {pre mid post : EVM.State} {v next finish : View}
      {w finalWarm : Warm} {trace : List Labelled} {event : Event} {events : List Event}
      (actual : XStepAt (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel gasCost pre mid)
      (decoded : decodeAt pre = (ReferenceDecodeSites.referenceDecode v.env.code v.pc).getD (.STOP,none))
      (related : Related parent v pre) (nextRelated : Related parent next mid)
      (warm : WarmRelated w pre) (created_eq : v.storage.created = initialCreated)
      (action : Action kind parent (decodeAt pre) v next)
      (readings : ReferenceSourceReadings.inputs parent initialCreated pre = sourceReading parent v w)
      (price : Price parent v w next (decodeAt pre).1 event)
      (tail : Coupled kind parent initialCreated fuel mid next (warmAfter (decodeAt pre).1 v w)
        trace rem post finish finalWarm events) :
      Coupled kind parent initialCreated (fuel+1) pre v w ((fuel,gasCost,decodeAt pre)::trace)
        rem post finish finalWarm (event::events)

theorem Coupled.viewed {kind : Kind} {parent : ReferenceStorageView.Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind parent initialCreated fuel pre v w trace rem post finish finalWarm events) :
    Viewed kind parent fuel pre v trace rem post finish := by
  induction h with
  | refl => exact .refl _ _ _
  | cons actual decoded related nextRelated _ _ action _ _ _ ih =>
    exact .cons actual decoded related nextRelated action ih

/-- Produce the event sequence and evolving warmth on exactly the supplied
viewed trace, retaining its final source view. No per-edge payment is assumed. -/
theorem from_viewed {kind : Kind} {parent : ReferenceStorageView.Parent} {initialCreated : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {trace : List Labelled}
    (viewed : Viewed kind parent fuel pre v trace rem post finish)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (w : Warm) (warm : WarmRelated w pre) (created_eq : v.storage.created = initialCreated) :
    ∃ finalWarm events,
      Coupled kind parent initialCreated fuel pre v w trace rem post finish finalWarm events ∧
      WarmRelated finalWarm post ∧ finish.storage.created = initialCreated := by
  revert hat w
  induction viewed with
  | refl => intro _ w warm; exact ⟨w,[],.refl _ _ _ _,warm,created_eq⟩
  | @cons edgeFuel gasCost rem pre mid post v next finish trace actual decoded related nextRelated action tail ih =>
    intro hat w warm
    obtain ⟨charged,hz,hs,hh⟩ := actual
    have hatNext := RuntimeExecutionScope.accepted_next hat hz hs hh
    have warmNext : WarmRelated (warmAfter (decodeAt pre).1 v w) mid := by
      cases edgeFuel with
      | zero => cases hs
      | succ f => exact ReferenceStorageWarmth.accepted_warm hat hz hs related warm
    have createdNext := (created action).trans created_eq
    obtain ⟨finalWarm,events,hcoupled,hfinalWarm,hfinalCreated⟩ :=
      ih createdNext hatNext (warmAfter (decodeAt pre).1 v w) warmNext
    have readings := ReferenceSourceReadings.reading_eq related warm created_eq
    have priced : ∃ event, Price parent v w next (decodeAt pre).1 event := by
      by_cases hop : (decodeAt pre).1 = .SSTORE
      · refine ⟨.store (sourceReading parent v w).warm (sourceReading parent v w).original
          (sourceReading parent v w).current (sourceReading parent v w).new,?_⟩
        simp only [Price,if_pos hop]
        refine ⟨?_,True.intro⟩
        rw [words_related related,words_related nextRelated]
        have hm := RuntimeMemoryCharges.accepted_expansion hat hz hs
        rw [hop] at hm
        simp only [RuntimeMemoryMonotone.span,MachineState.M] at hm
        rw [hm,Nat.sub_self]
      · obtain ⟨n,hn⟩ := ReferenceCopyLogGas.defined (sourceReading parent v w).warm v.stack
          (RuntimeExecutionScope.opcode_allowed hat) hop
        exact ⟨.ordinary (n+(ReferenceMemoryCapacity.cost (words next)-ReferenceMemoryCapacity.cost (words v))),
          by simp only [Price,if_neg hop]; exact ⟨n,hn,rfl⟩⟩
    obtain ⟨event,hprice⟩ := priced
    exact ⟨finalWarm,event::events,
      .cons ⟨charged,hz,hs,hh⟩ decoded related nextRelated warm created_eq action readings hprice hcoupled,
      hfinalWarm,hfinalCreated⟩

#print axioms created
#print axioms Coupled.viewed
#print axioms from_viewed
end Eip8282.Audit.Integrator.ReferenceRuntimeReadings

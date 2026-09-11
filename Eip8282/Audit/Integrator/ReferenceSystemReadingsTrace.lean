import Eip8282.Audit.Integrator.ReferenceStorageWarmth
import Eip8282.Audit.Integrator.ReferenceActionMetadata
import Eip8282.Audit.Integrator.ReferenceSystemTrace

/-! Storage-meter readings and memory charges are attached to evolving source
views on the very same actual priced trace. Source warmth is independent of
BAL reads; the source transaction's created set remains fixed through SYSTEM.
Initial source-world/access-set binding and executable interpretation remain
external. No arbitrary reading oracle is an input to the construction below. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemReadingsTrace
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.EntryReach
open ReferenceRuntimeView ReferenceSourceReadings ReferenceSystemAction
open SystemTraceAnnotations SystemExecutionResources SystemMeterResources ReferenceMeterPath
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

noncomputable def SourcePrice (parent : ReferenceStorageView.Parent)
    (v : View) (w : Warm) (next : View) (op : Operation .EVM) (event : Event) : Prop :=
  let reading := sourceReading parent v w
  let memoryCost := ReferenceMemoryCapacity.cost (words next)-ReferenceMemoryCapacity.cost (words v)
  if op = .SSTORE then memoryCost = 0 ∧
    event = .store reading.warm reading.original reading.current reading.new
  else ∃ n, ReferenceOrdinaryGas.ordinaryCost op reading.warm = some n ∧
    event = .ordinary (n+memoryCost)

theorem source_price {parent : ReferenceStorageView.Parent} {created : Set AccountAddress}
    {v next : View} {w : Warm} {pre post : EVM.State} {op : Operation .EVM} {event : Event}
    (related : Related parent v pre) (nextRelated : Related parent next post)
    (warm : WarmRelated w pre) (created_eq : v.storage.created = created)
    (price : EdgePrice (ReferenceSourceReadings.inputs parent created) pre post op event) :
    SourcePrice parent v w next op event := by
  have readings := reading_eq related warm created_eq
  unfold EdgePrice at price
  rw [readings] at price
  simpa only [SourcePrice,delta,words_related related,words_related nextRelated] using price

theorem priced_runs {inputs : Inputs} {vj : Array UInt256} {fuel rem : Nat}
    {pre post : EVM.State} {trace : List Labelled} {events : List Event}
    (h : PricedTrace inputs vj fuel pre trace rem post events) :
    XRuns vj fuel pre trace rem post := by
  induction h with
  | refl => exact .refl _ _
  | cons hs _ _ ih => exact .cons hs ih

/-- Both actual and source-formula prices describe the same event. Every
intermediate source view has its actual state and warm-set relation recorded. -/
inductive Coupled (kind : Kind) (parent : ReferenceStorageView.Parent) (created : Set AccountAddress) :
    Nat → EVM.State → View → Warm → List Labelled → Nat → EVM.State → View → Warm → List Event → Prop where
  | refl (fuel : Nat) (pre : EVM.State) (v : View) (w : Warm) :
      Coupled kind parent created fuel pre v w [] fuel pre v w []
  | cons {fuel gasCost rem : Nat} {pre mid post : EVM.State} {v next finish : View}
      {w finalWarm : Warm} {trace : List Labelled} {event : Event} {events : List Event}
      (actual : XStepAt (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel gasCost pre mid)
      (decoded : decodeAt pre = (ReferenceDecodeSites.referenceDecode v.env.code v.pc).getD (.STOP,none))
      (related : Related parent v pre) (nextRelated : Related parent next mid)
      (warm : WarmRelated w pre) (created_eq : v.storage.created = created)
      (action : Action kind parent (decodeAt pre) v next)
      (readings : ReferenceSourceReadings.inputs parent created pre = sourceReading parent v w)
      (actual_price : EdgePrice (ReferenceSourceReadings.inputs parent created) pre mid (decodeAt pre).1 event)
      (source_price : SourcePrice parent v w next (decodeAt pre).1 event)
      (tail : Coupled kind parent created fuel mid next (warmAfter (decodeAt pre).1 v w)
        trace rem post finish finalWarm events) :
      Coupled kind parent created (fuel+1) pre v w ((fuel,gasCost,decodeAt pre)::trace)
        rem post finish finalWarm (event::events)

theorem Coupled.priced {kind : Kind} {parent : ReferenceStorageView.Parent} {created : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind parent created fuel pre v w trace rem post finish finalWarm events) :
    PricedTrace (ReferenceSourceReadings.inputs parent created)
      (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre trace rem post events := by
  induction h with
  | refl => exact .refl _ _
  | cons actual _ _ _ _ _ _ _ hp _ _ ih => exact .cons actual hp ih

theorem Coupled.viewed {kind : Kind} {parent : ReferenceStorageView.Parent} {created : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v finish : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind parent created fuel pre v w trace rem post finish finalWarm events) :
    ReferenceSystemTrace.Viewed kind parent fuel pre v trace rem post finish := by
  induction h with
  | refl => exact .refl _ _ _
  | cons actual decoded _ _ _ _ action _ _ _ _ ih => exact .cons actual decoded action ih

theorem from_priced {kind : Kind} {parent : ReferenceStorageView.Parent} {created : Set AccountAddress}
    {fuel rem cap : Nat} {pre post : EVM.State} {trace : List Labelled} {events : List Event}
    (hp : PricedTrace (ReferenceSourceReadings.inputs parent created)
      (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre trace rem post events)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (v : View) (w : Warm) (related : Related parent v pre) (warm : WarmRelated w pre)
    (created_eq : v.storage.created = created)
    (ha : ∀ op ∈ operations trace, SystemPathBudget.Allowed op)
    (permission : v.env.perm = true) (cdfit : v.env.calldata.size < UInt256.size)
    (capacity : post.activeWords.toNat ≤ cap) (host : 32*cap < 2^System.Platform.numBits) :
    ∃ finish finalWarm,
      Coupled kind parent created fuel pre v w trace rem post finish finalWarm events ∧
      Related parent finish post ∧ WarmRelated finalWarm post ∧ finish.storage.created = created := by
  revert hat v w ha
  induction hp with
  | refl =>
    intro hat v w related warm created_eq ha permission cdfit
    exact ⟨v,w,.refl _ _ _ _,related,warm,created_eq⟩
  | @cons edgeFuel gasCost rem pre middle post trace event events actual price tail ih =>
    intro hat v w related warm created_eq ha permission cdfit
    obtain ⟨charged,hz,hs,hh⟩ := actual
    have hatnext := RuntimeExecutionScope.accepted_next hat hz hs hh
    have hc := (RuntimeMemoryMonotone.runs hatnext (priced_runs tail)).2.trans capacity
    have hd : decodeAt pre = (ReferenceDecodeSites.referenceDecode v.env.code v.pc).getD (.STOP,none) := by
      rw [related.env,related.pc,hat.1,ReferenceRuntimeSites.code_eq]
      exact ReferenceRuntimeSites.decode_matches hat hh
    cases edgeFuel with
    | zero => cases hs
    | succ f =>
      obtain ⟨next,hact,hrel⟩ := ReferenceSystemAction.step hat hz hs hh related
        (ha _ (by simp [operations])) permission cdfit hc host
      have hw := ReferenceStorageWarmth.accepted_warm hat hz hs related warm
      have hcreated := (ReferenceActionMetadata.created hact).trans created_eq
      have henv : next.env = v.env :=
        hrel.env.trans ((RuntimeExecutionScope.accepted_environment hat hz hs).trans related.env.symm)
      obtain ⟨finish,finalWarm,hcoupled,hfinish,hwarm,hcreatedfinish⟩ := ih capacity hatnext next
        (warmAfter (decodeAt pre).1 v w) hrel hw hcreated
        (fun op hop => ha op (by simp [operations] at hop ⊢; exact Or.inr hop))
        (by rw [henv]; exact permission) (by rw [henv]; exact cdfit)
      exact ⟨finish,finalWarm,
        .cons ⟨charged,hz,hs,hh⟩ hd related hrel warm created_eq hact
          (reading_eq related warm created_eq) price (source_price related hrel warm created_eq price) hcoupled,
        hfinish,hwarm,hcreatedfinish⟩

#print axioms source_price
#print axioms priced_runs
#print axioms Coupled.priced
#print axioms Coupled.viewed
#print axioms from_priced
end Eip8282.Audit.Integrator.ReferenceSystemReadingsTrace

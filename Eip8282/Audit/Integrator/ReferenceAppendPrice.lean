import Eip8282.Audit.Integrator.ReferenceAppendOccurrences
import Eip8282.Audit.Integrator.ReferenceCoupledPrefix
import Eip8282.Audit.Integrator.ReferenceExecutionLedger

/-! Price actual selected append instructions on the same Coupled execution.
All store classes cost at least100 execution gas, even if slots alias or a write
is a no-op. LOG length comes from the actual stack. Selection is ordered and
nonoverlapping, including the tail store after LOG. -/
namespace Eip8282.Audit.Integrator.ReferenceAppendPrice
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings ReferenceMeterPath
open ReferenceAppendOccurrences ReferenceExecutionLedger ReferenceCoupledPrefix
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def markerWork : Marker → Nat
  | .store => 100
  | .log len => 375+8*len.toNat

def selectedWork (markers : List Marker) : Nat := (markers.map markerWork).sum

theorem marker_price {p : Parent} {pre : EVM.State} {v next : View} {w : Warm}
    {marker : Marker} {event : Event} (mark : Matches marker pre)
    (related : Related p v pre) (price : Price p v w next (decodeAt pre).1 event) :
    markerWork marker ≤ eventWork event := by
  cases marker with
  | store =>
    change decodeAt pre = (.SSTORE,none) at mark
    simp only [Price,mark,↓reduceIte] at price
    rw [price.2]
    simp only [markerWork,eventWork,ReferenceStorageGas.classify]
    split <;> omega
  | log len =>
    obtain ⟨decoded,off,rest,hstack⟩ := mark
    simp only [Price,decoded,show (Operation.LOG0 : Operation .EVM) ≠ .SSTORE by decide,↓reduceIte] at price
    obtain ⟨n,hcost,rfl⟩ := price
    rw [related.stack,hstack] at hcost
    have hn : 375+8*len.toNat = n := Option.some.inj hcost
    simp only [markerWork,eventWork]
    omega

/-- The actual earlier split threads source views, warmth and prices at the
same intermediate state. It introduces no arbitrary second event sequence. -/
theorem selected_cost {kind : Kind} {p : Parent} {created : Set AccountAddress}
    {fuel rem : Nat} {pre post : EVM.State} {v last : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event} {markers : List Marker}
    (marked : Marked (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre rem post markers)
    (priced : Coupled kind p created fuel pre v w trace rem post last finalWarm events) :
    selectedWork markers ≤ work events := by
  induction marked generalizing v last w finalWarm trace events with
  | skip run => exact Nat.zero_le _
  | single actual mark =>
    cases priced with
    | cons other decoded related nextRelated warm created_eq action readings price tail =>
      have empty := same_fuel tail
      have hm := marker_price mark related price
      simp only [work,List.map_cons,List.sum_cons,empty.2,List.map_nil,List.sum_nil,Nat.add_zero]
      simpa only [selectedWork,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using hm
  | trans first second ih1 ih2 =>
    obtain ⟨earlier,hprefix,_⟩ := first.erase
    obtain ⟨suffix,hsuffix,_⟩ := second.erase
    obtain ⟨middleView,middleWarm,remaining,firstEvents,restEvents,ht,he,hfirst,hrest⟩ :=
      split_at hprefix priced hsuffix.rem_le
    have h1 := ih1 hfirst
    have h2 := ih2 hrest
    simp only [selectedWork,List.map_append,List.sum_append] at h1 h2 ⊢
    rw [he]
    simp only [work,List.map_append,List.sum_append] at h1 h2 ⊢
    omega

theorem exact_marker_costs : selectedWork exitMarkers = 1419 ∧ selectedWork depositMarkers = 2647 := by
  decide +kernel

#print axioms marker_price
#print axioms selected_cost
#print axioms exact_marker_costs
end Eip8282.Audit.Integrator.ReferenceAppendPrice

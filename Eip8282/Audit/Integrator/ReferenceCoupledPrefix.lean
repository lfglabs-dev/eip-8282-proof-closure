import Eip8282.Audit.Integrator.ReferenceRuntimeReadings

/-! Split the same source-priced actual trace at an actual earlier endpoint.
The earlier length is not guessed: exact instruction determinism identifies its
steps, and remaining fuel proves it is contained in the supplied whole trace. -/
namespace Eip8282.Audit.Integrator.ReferenceCoupledPrefix
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings ReferenceMeterPath
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

theorem same_fuel {kind : Kind} {p : Parent} {created : Set AccountAddress}
    {fuel : Nat} {pre post : EVM.State} {v last : View} {w finalWarm : Warm}
    {trace : List Labelled} {events : List Event}
    (h : Coupled kind p created fuel pre v w trace fuel post last finalWarm events) :
    trace = [] ∧ events = [] := by
  cases h with
  | refl => exact ⟨rfl,rfl⟩
  | cons actual decoded related nextRelated warm created_eq action readings price tail =>
    have bound := tail.viewed.erase.rem_le
    omega

theorem split_at {kind : Kind} {p : Parent} {created : Set AccountAddress}
    {fuel middleFuel rem : Nat} {pre middle post : EVM.State} {v last : View} {w finalWarm : Warm}
    {earlier trace : List Labelled} {events : List Event}
    (head : XRuns (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre earlier middleFuel middle)
    (whole : Coupled kind p created fuel pre v w trace rem post last finalWarm events)
    (fits : rem ≤ middleFuel) :
    ∃ middleView middleWarm tail firstEvents restEvents,
      trace = earlier++tail ∧ events = firstEvents++restEvents ∧
      Coupled kind p created fuel pre v w earlier middleFuel middle middleView middleWarm firstEvents ∧
      Coupled kind p created middleFuel middle middleView middleWarm tail rem post last finalWarm restEvents := by
  induction head generalizing v w trace events with
  | refl => exact ⟨v,w,trace,[],events,rfl,rfl,.refl _ _ _ _,whole⟩
  | @cons fuel gasCost middleFuel pre mid middle earlier actual tail ih =>
    cases whole with
    | refl => have bound := tail.rem_le; omega
    | @cons _ _ _ _ _ _ _ _ _ _ _ _ event _ other decoded related nextRelated warm created_eq action readings price rest =>
      obtain ⟨rfl,rfl⟩ := XStepAt.deterministic actual other
      obtain ⟨middleView,middleWarm,remaining,firstEvents,restEvents,ht,he,hfirst,hrest⟩ := ih rest fits
      refine ⟨middleView,middleWarm,remaining,event::firstEvents,restEvents,?_,?_,?_,hrest⟩
      · simp only [List.cons_append,ht]
      · simp only [List.cons_append,he]
      · exact .cons actual decoded related nextRelated warm created_eq action readings price hfirst

#print axioms same_fuel
#print axioms split_at
end Eip8282.Audit.Integrator.ReferenceCoupledPrefix

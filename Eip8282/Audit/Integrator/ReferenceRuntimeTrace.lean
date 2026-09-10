import Eip8282.Audit.Integrator.ReferenceRuntimeAction
import Eip8282.Audit.Integrator.SystemTraceAnnotations

/-! Source-shaped views along arbitrary finite actual runtime traces, including
user COPY/LOG0. No global permission or source-state sequence is supplied.
Endpoint capacity is still a local resource premise; initial-call resource
producers and complete halting/failure observations remain separate consumers. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeTrace
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceRuntimeAction SystemTraceAnnotations
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

inductive Viewed (kind : Kind) (parent : ReferenceStorageView.Parent) :
    Nat → EVM.State → View → List Labelled → Nat → EVM.State → View → Prop where
  | refl (fuel : Nat) (pre : EVM.State) (v : View) : Viewed kind parent fuel pre v [] fuel pre v
  | cons {fuel gasCost rem : Nat} {pre mid post : EVM.State} {v next finish : View} {trace : List Labelled}
      (actual : XStepAt (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel gasCost pre mid)
      (decoded : decodeAt pre = (ReferenceDecodeSites.referenceDecode v.env.code v.pc).getD (.STOP,none))
      (related : Related parent v pre) (nextRelated : Related parent next mid)
      (action : Action kind parent (decodeAt pre) v next)
      (tail : Viewed kind parent fuel mid next trace rem post finish) :
      Viewed kind parent (fuel+1) pre v ((fuel,gasCost,decodeAt pre)::trace) rem post finish

theorem Viewed.erase {kind : Kind} {parent : ReferenceStorageView.Parent} {fuel rem : Nat}
    {pre post : EVM.State} {v finish : View} {trace : List Labelled}
    (h : Viewed kind parent fuel pre v trace rem post finish) :
    XRuns (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre trace rem post := by
  induction h with
  | refl => exact .refl _ _
  | cons hs _ _ _ _ _ ih => exact .cons hs ih

theorem from_runs {kind : Kind} {parent : ReferenceStorageView.Parent} {fuel rem cap : Nat}
    {pre post : EVM.State} {trace : List Labelled}
    (hr : XRuns (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre trace rem post)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (v : View) (related : Related parent v pre)
    (cdfit : v.env.calldata.size < UInt256.size)
    (capacity : post.activeWords.toNat ≤ cap) (host : 32*cap < 2^System.Platform.numBits) :
    ∃ finish, Viewed kind parent fuel pre v trace rem post finish ∧ Related parent finish post := by
  revert hat v
  induction hr with
  | refl => intro hat v related cdfit; exact ⟨v,.refl _ _ _,related⟩
  | @cons edgeFuel gasCost rem pre middle post trace actual tail ih =>
    intro hat v related cdfit
    obtain ⟨charged,hz,hs,hh⟩ := actual
    have hatnext := RuntimeExecutionScope.accepted_next hat hz hs hh
    have hc := (RuntimeMemoryMonotone.runs hatnext tail).2.trans capacity
    have hd : decodeAt pre = (ReferenceDecodeSites.referenceDecode v.env.code v.pc).getD (.STOP,none) := by
      rw [related.env,related.pc,hat.1,ReferenceRuntimeSites.code_eq]
      exact ReferenceRuntimeSites.decode_matches hat hh
    cases edgeFuel with
    | zero => cases hs
    | succ f =>
      obtain ⟨next,hact,hrel⟩ := ReferenceRuntimeAction.step hat hz hs hh related cdfit hc host
      have henv : next.env = v.env :=
        hrel.env.trans ((RuntimeExecutionScope.accepted_environment hat hz hs).trans related.env.symm)
      obtain ⟨finish,hview,hfinish⟩ := ih capacity hatnext next hrel (by rw [henv]; exact cdfit)
      exact ⟨finish,.cons ⟨charged,hz,hs,hh⟩ hd related hrel hact hview,hfinish⟩

#print axioms Viewed.erase
#print axioms from_runs
end Eip8282.Audit.Integrator.ReferenceRuntimeTrace

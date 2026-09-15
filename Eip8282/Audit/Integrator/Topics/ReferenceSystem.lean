import Eip8282.Audit.Integrator.Topics.Reference
import Eip8282.Audit.Integrator.ReferenceMemoryViewAction
import Eip8282.Audit.Integrator.Topics.ReferencePure
import Eip8282.Audit.Integrator.ReferenceReturnSlice
import Eip8282.Audit.Integrator.Topics.ReferenceStorage
import Eip8282.Audit.Integrator.SystemMeterResources
import Eip8282.Audit.Integrator.SystemPathBudget

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceSystemAction -/

/-! Literal source-shaped nonhalting SYSTEM actions. Each case constructs its
post-view from inputs; the actual accepted step derives the corresponding case.
Reference gas payment is handled by the same-trace meter layer, not assumed by
this local effect relation. This does not interpret executable Python. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemAction
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

inductive Action (kind : Kind) (parent : ReferenceStorageView.Parent) : Instruction → View → View → Prop where
  | pure {instr : Instruction} {pre post : View} :
      ReferencePureAction.action kind instr pre = some post → Action kind parent instr pre post
  | load {v : View} {key : UInt256} {rest : Stack UInt256} :
      v.stack = key::rest → Action kind parent (.SLOAD,none) v (loadAction parent v key rest)
  | store {v : View} {key value : UInt256} {rest : Stack UInt256} :
      v.env.perm = true → v.stack = key::value::rest →
      Action kind parent (.SSTORE,none) v (storeAction v key value rest)
  | word {v : View} {off value : UInt256} {rest : Stack UInt256} :
      v.stack = off::value::rest →
      Action kind parent (.MSTORE,none) v (memoryAction v off value.toByteArray rest)
  | byte {v : View} {off value : UInt256} {rest : Stack UInt256} :
      v.stack = off::value::rest →
      Action kind parent (.MSTORE8,none) v (memoryAction v off ⟨#[UInt8.ofNat value.toNat]⟩ rest)

theorem cases_of_nonhalting {pre post : EVM.State}
    (ha : SystemPathBudget.Allowed (decodeAt pre).1)
    (hh : H post.toMachineState (decodeAt pre).1 = none) :
    ReferencePureAction.Supported (decodeAt pre).1 ∨
      (decodeAt pre).1 = .SLOAD ∨ (decodeAt pre).1 = .SSTORE ∨
      (decodeAt pre).1 = .MSTORE ∨ (decodeAt pre).1 = .MSTORE8 := by
  have hc : ∀ op ∈ RuntimeOpcodeScope.allowedOps, op ≠ .LOG0 → op ≠ .CALLDATACOPY →
      (ReferencePureAction.classify op).isSome = true ∨
      op = .SLOAD ∨ op = .SSTORE ∨ op = .MSTORE ∨ op = .MSTORE8 ∨
      op = .STOP ∨ op = .RETURN ∨ op = .REVERT := by decide +kernel
  rcases hc _ ha.1 ha.2.1 ha.2.2 with h | h | h | h | h | h | h | h
  · cases he : ReferencePureAction.classify (decodeAt pre).1 with
    | none => simp [he] at h
    | some p => exact Or.inl ⟨p,ReferencePureAction.classify_sound he⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  all_goals simp [h,H] at hh

/-- Actual pre/post capacity and typed host bounds suffice for memory effects;
operand shapes, source decoder position and natural PC fit are derived. -/
theorem step {kind : Kind} {parent : ReferenceStorageView.Parent} {v : View}
    {pre mid post : EVM.State} {fuel gasCost cap : Nat}
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (hz : Z (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk (fuel+1) gasCost (decodeAt pre) mid post)
    (hh : H post.toMachineState (decodeAt pre).1 = none)
    (related : Related parent v pre) (ha : SystemPathBudget.Allowed (decodeAt pre).1)
    (permission : v.env.perm = true) (cdfit : v.env.calldata.size < UInt256.size)
    (capacity : post.activeWords.toNat ≤ cap) (host : 32*cap < 2^System.Platform.numBits) :
    ∃ next, Action kind parent (decodeAt pre) v next ∧ Related parent next post := by
  rcases cases_of_nonhalting ha hh with hp | hp | hp | hp | hp
  · obtain ⟨next,ha,hr⟩ := ReferencePureComplete.accepted related hat hp hz hs cdfit
    exact ⟨next,.pure ha,hr⟩
  · have hd := ReferenceDecodeShape.fixed pre .SLOAD hp rfl
    obtain ⟨key,rest,_,hstack,hr⟩ := ReferenceStorageViewAction.sload hat hd hz hs related
    exact ⟨_,by rw [hd]; exact .load hstack,hr⟩
  · have hd := ReferenceDecodeShape.fixed pre .SSTORE hp rfl
    obtain ⟨key,value,rest,_,hstack,hr⟩ := ReferenceStorageViewAction.sstore hat hd hz hs related
    exact ⟨_,by rw [hd]; exact .store permission hstack,hr⟩
  · have hd := ReferenceDecodeShape.fixed pre .MSTORE hp rfl
    obtain ⟨off,value,rest,hstack,hr⟩ := ReferenceMemoryViewAction.mstore hat hd hz hs related capacity host
    exact ⟨_,by rw [hd]; exact .word hstack,hr⟩
  · have hd := ReferenceDecodeShape.fixed pre .MSTORE8 hp rfl
    obtain ⟨off,value,rest,hstack,hr⟩ := ReferenceMemoryViewAction.mstore8 hat hd hz hs related capacity host
    exact ⟨_,by rw [hd]; exact .byte hstack,hr⟩

#print axioms cases_of_nonhalting
#print axioms step
end Eip8282.Audit.Integrator.ReferenceSystemAction

end

section

/-! ## ReferenceSystemTrace -/

/-! A complete source-shaped SYSTEM path is constructed along the same actual
XRuns. Source decoder bindings and intermediate views are retained at each edge.
Only initial slot/owner bindings remain; internal operand/PC/memory-capacity
premises are derived. Executable-Python and canonical context are not assumed
or asserted by this view-level trace construction. -/
namespace Eip8282.Audit.Integrator.ReferenceSystemTrace
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall)
open ReferenceRuntimeView ReferenceSystemAction
open SystemTraceAnnotations SystemExecutionResources
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

inductive Viewed (kind : Kind) (parent : ReferenceStorageView.Parent) :
    Nat → EVM.State → View → List Labelled → Nat → EVM.State → View → Prop where
  | refl (fuel : Nat) (pre : EVM.State) (v : View) : Viewed kind parent fuel pre v [] fuel pre v
  | cons {fuel gasCost rem : Nat} {pre mid post : EVM.State} {v next finish : View} {trace : List Labelled}
      (actual : XStepAt (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel gasCost pre mid)
      (decoded : decodeAt pre = (ReferenceDecodeSites.referenceDecode v.env.code v.pc).getD (.STOP,none))
      (action : Action kind parent (decodeAt pre) v next)
      (tail : Viewed kind parent fuel mid next trace rem post finish) :
      Viewed kind parent (fuel+1) pre v ((fuel,gasCost,decodeAt pre)::trace) rem post finish

theorem Viewed.erase {kind : Kind} {parent : ReferenceStorageView.Parent} {fuel rem : Nat}
    {pre post : EVM.State} {v finish : View} {trace : List Labelled}
    (h : Viewed kind parent fuel pre v trace rem post finish) :
    XRuns (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre trace rem post := by
  induction h with
  | refl => exact .refl _ _
  | cons hs _ _ _ ih => exact .cons hs ih

/-- All per-edge host spans come from the actual final capacity. -/
theorem from_runs {kind : Kind} {parent : ReferenceStorageView.Parent} {fuel rem cap : Nat}
    {pre post : EVM.State} {trace : List Labelled}
    (hr : XRuns (D_J (ReferenceRuntimeSites.runtime kind).code ⟨0⟩) fuel pre trace rem post)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (v : View) (related : Related parent v pre)
    (ha : ∀ op ∈ operations trace, SystemPathBudget.Allowed op)
    (permission : v.env.perm = true) (cdfit : v.env.calldata.size < UInt256.size)
    (capacity : post.activeWords.toNat ≤ cap) (host : 32*cap < 2^System.Platform.numBits) :
    ∃ finish, Viewed kind parent fuel pre v trace rem post finish ∧ Related parent finish post := by
  revert hat v ha
  induction hr with
  | refl => intro hat v related ha permission cdfit; exact ⟨v,.refl _ _ _,related⟩
  | @cons edgeFuel gasCost rem pre middle post trace actual tail ih =>
    intro hat v related ha permission cdfit
    obtain ⟨charged,hz,hs,hh⟩ := actual
    have hatnext := RuntimeExecutionScope.accepted_next hat hz hs hh
    have hc := (RuntimeMemoryMonotone.runs hatnext tail).2.trans capacity
    have hd : decodeAt pre = (ReferenceDecodeSites.referenceDecode v.env.code v.pc).getD (.STOP,none) := by
      rw [related.env,related.pc,hat.1,ReferenceRuntimeSites.code_eq]
      exact ReferenceRuntimeSites.decode_matches hat hh
    cases edgeFuel with
    | zero => cases hs
    | succ f =>
      obtain ⟨next,hact,hrel⟩ := ReferenceSystemAction.step hat hz hs hh related
        (ha _ (by simp [operations])) permission cdfit hc host
      have henv : next.env = v.env :=
        hrel.env.trans ((RuntimeExecutionScope.accepted_environment hat hz hs).trans related.env.symm)
      obtain ⟨finish,hview,hfinish⟩ := ih capacity hatnext next hrel
        (fun op hop => ha op (by simp [operations] at hop ⊢; exact Or.inr hop))
        (by rw [henv]; exact permission) (by rw [henv]; exact cdfit)
      exact ⟨finish,.cons ⟨charged,hz,hs,hh⟩ hd hact hview,hfinish⟩

/-- A source-shaped observation of the same completed execution, including its
actual terminal instruction. Storage and logs belong to its actual final state. -/
def Observed {kind : Kind} {parent : ReferenceStorageView.Parent}
    {steps cap outputBytes fuel : Nat} {pre : EVM.State}
    (h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes fuel pre)
    (initial : View) : Prop :=
  ∃ v off len rest,
    Viewed kind parent fuel pre initial h.trace (h.rem+2) h.exitState v ∧
    Related parent v h.exitState ∧
    ReferenceDecodeSites.referenceDecode v.env.code v.pc = some (.RETURN,none) ∧
    v.stack = off::len::rest ∧
    ReferenceReturnView.Result parent v off len rest h.finalState ∧
    h.output = (ReferenceReturnView.returnMemory v off len).extract off.toNat (off.toNat+len.toNat)

/-- Intermediate operands, views, capacities and the terminal output equation
are constructed from this actual completed path. -/
theorem attach {kind : Kind} {parent : ReferenceStorageView.Parent}
    {steps cap outputBytes fuel : Nat} {pre : EVM.State}
    (h : Completed (ReferenceRuntimeSites.runtime kind) steps cap outputBytes fuel pre)
    (hat : RuntimeExecutionScope.At (ReferenceRuntimeSites.runtime kind) pre)
    (v : View) (related : Related parent v pre)
    (permission : v.env.perm = true) (cdfit : v.env.calldata.size < UInt256.size)
    (output_fit : outputBytes ≤ 32*cap) (host : 32*cap < 2^System.Platform.numBits) :
    Observed (parent := parent) h v := by
  obtain ⟨finish,hview,hrel⟩ := from_runs h.run hat v related
    (fun op hop => h.allowed op (List.mem_append_left _ hop)) permission cdfit h.exit_capacity host
  obtain ⟨_,_,_,hcap,_⟩ := SystemMemoryResources.attach h hat output_fit
  obtain ⟨off,len,rest,_,hshape,hr,hout⟩ :=
    ReferenceReturnView.halted h.halt.charge h.terminal hrel hcap host h.returned
  refine ⟨finish,off,len,rest,hview,hrel,?_,hshape,hr,?_⟩
  · rw [hrel.env,hrel.pc,h.at_exit.1,ReferenceRuntimeSites.code_eq]
    exact ReferenceTerminalDecode.return_decode h.at_exit (congrArg Prod.fst h.halt.decode)
  · exact hout.trans (ReferenceReturnSlice.output_eq_extract hrel off len)

#print axioms Viewed.erase
#print axioms from_runs
#print axioms attach
end Eip8282.Audit.Integrator.ReferenceSystemTrace

end

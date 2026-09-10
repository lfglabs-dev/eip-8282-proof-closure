import Eip8282.Audit.Integrator.ReferencePureComplete
import Eip8282.Audit.Integrator.ReferenceStorageViewAction
import Eip8282.Audit.Integrator.ReferenceMemoryViewAction
import Eip8282.Audit.Integrator.ReferenceDecodeShape
import Eip8282.Audit.Integrator.SystemPathBudget

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

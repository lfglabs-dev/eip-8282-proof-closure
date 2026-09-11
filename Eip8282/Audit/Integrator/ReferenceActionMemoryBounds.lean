import Eip8282.Audit.Integrator.ReferenceRuntimeAction

/-! Source-shaped action memory metadata without old execution or Related.
Literal eager splice/buffer arithmetic gives exact computed expansion, preserves
alignment from empty frame memory, and bounds positive access endpoints. No
host-size bound is assumed here; the source paid-cost telescope must derive it.
This remains the audited action transcription, not executable Python refinement.
Zero-length COPY keeps the input memory, including arbitrary operand offsets. -/
namespace Eip8282.Audit.Integrator.ReferenceActionMemoryBounds
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferencePureAction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- Natural operand span computed entirely from the source view. -/
def span (v : View) (op : Operation .EVM) : Nat × Nat :=
  match op with
  | .CALLDATACOPY => (v.stack[0]!.toNat,v.stack[2]!.toNat)
  | .MSTORE => (v.stack[0]!.toNat,32)
  | .MSTORE8 => (v.stack[0]!.toNat,1)
  | .LOG0 | .RETURN | .REVERT => (v.stack[0]!.toNat,v.stack[1]!.toNat)
  | _ => (0,0)

def Aligned (v : View) : Prop := v.memory.size = 32*words v

private theorem splice_size (memory data : ByteArray) (off capacity : Nat)
    (fits : off+data.size ≤ capacity) :
    (ReferenceMemoryOperations.splice memory off data capacity).size = capacity := by
  simp only [ReferenceMemoryOperations.splice,ReferenceMemoryOperations.extend,
    ByteArray.size,Array.size_append,Array.size_extract]
  have hs := ReferenceMemoryView.buffer_size memory 0 capacity
  change (ReferenceMemoryView.buffer memory 0 capacity).data.size = capacity at hs
  rw [hs]
  change off+data.data.size ≤ capacity at fits
  omega

private theorem family_memory {kind : Kind} {v next : View} {arg : Option (UInt256 × Nat)}
    (p : Pure) (effect : familyAction kind p arg v = some next) : next.memory = v.memory := by
  cases p <;> simp only [familyAction] at effect
  all_goals repeat' first | split at effect | cases effect
  all_goals rfl

private theorem pure_memory {kind : Kind} {instr : Instruction} {v next : View}
    (effect : action kind instr v = some next) : next.memory = v.memory ∧ span v instr.1 = (0,0) := by
  unfold action at effect
  cases selected : classify instr.1 with
  | none => simp only [selected,Option.bind_none] at effect; contradiction
  | some p =>
    simp only [selected,Option.bind_some] at effect
    refine ⟨family_memory p effect,?_⟩
    rw [←classify_sound selected]
    cases p <;> try rfl
    rename_i b
    cases b <;> rfl

private theorem store_size (v : View) (off : UInt256) (data : ByteArray) (rest : Stack UInt256)
    (positive : 0 < data.size) :
    (memoryAction v off data rest).memory.size =
      32*MachineState.M (words v) off.toNat data.size := by
  apply splice_size
  exact (ReferenceMemoryCapacity.expansion_bounds (words v) off.toNat data.size).2 positive

/-- Both post size and words are computed from input operands. The alignment
premise is an initial representation invariant, not a post-capacity oracle. -/
theorem computed {kind : Kind} {parent : ReferenceStorageView.Parent} {instr : Instruction} {v next : View}
    (effect : ReferenceRuntimeAction.Action kind parent instr v next) (aligned : Aligned v) :
    next.memory.size = 32*MachineState.M (words v) (span v instr.1).1 (span v instr.1).2 ∧
    words next = MachineState.M (words v) (span v instr.1).1 (span v instr.1).2 := by
  have size : next.memory.size = 32*MachineState.M (words v) (span v instr.1).1 (span v instr.1).2 := by
    cases effect with
    | base base =>
      cases base with
      | pure pure =>
        obtain ⟨hm,hs⟩ := pure_memory pure
        rw [hm,hs]
        exact aligned
      | load shape => exact aligned
      | store permission shape => exact aligned
      | @word v off value rest shape =>
        have hs := store_size v off value.toByteArray rest (by rw [UInt256.size_toByteArray]; decide)
        simpa only [span,shape,List.getElem!_cons_zero,UInt256.size_toByteArray] using hs
      | @byte v off value rest shape =>
        have hs := store_size v off (⟨#[UInt8.ofNat value.toNat]⟩ : ByteArray) rest (by change 0 < 1; omega)
        change (memoryAction v off (⟨#[UInt8.ofNat value.toNat]⟩ : ByteArray) rest).memory.size = 32*MachineState.M (words v) off.toNat 1 at hs
        simpa only [span,shape,List.getElem!_cons_zero] using hs
    | copy shape =>
      simp only [span,shape,List.getElem!_cons_zero,List.getElem!_cons_succ]
      change (ReferenceCopyMemory.copyMemory _ _ _ _ _ _).size = _
      unfold ReferenceCopyMemory.copyMemory
      split
      · rename_i zero
        simpa only [Aligned,zero,MachineState.M] using aligned
      · rename_i positive
        apply splice_size
        rw [ReferenceMemoryView.buffer_size]
        exact (ReferenceMemoryCapacity.expansion_bounds _ _ _).2 (by omega)
    | log permission shape =>
      simp only [span,shape,List.getElem!_cons_zero,List.getElem!_cons_succ,
        ReferenceLogView.logAction,ReferenceReturnView.returnMemory,
        ReferenceMemoryOperations.extend,ReferenceMemoryView.buffer_size]
  refine ⟨size,?_⟩
  change next.memory.size/32 = _
  rw [size]
  omega

theorem preserves_alignment {kind : Kind} {parent : ReferenceStorageView.Parent} {instr : Instruction} {v next : View}
    (effect : ReferenceRuntimeAction.Action kind parent instr v next) (aligned : Aligned v) : Aligned next := by
  have h := computed effect aligned
  change next.memory.size = 32*words next
  rw [h.1,h.2]

theorem monotone {kind : Kind} {parent : ReferenceStorageView.Parent} {instr : Instruction} {v next : View}
    (effect : ReferenceRuntimeAction.Action kind parent instr v next) (aligned : Aligned v) :
    words v ≤ words next ∧ v.memory.size ≤ next.memory.size := by
  have h := computed effect aligned
  have lower := (ReferenceMemoryCapacity.expansion_bounds (words v) (span v instr.1).1 (span v instr.1).2).1
  change v.memory.size = 32*words v at aligned
  omega

theorem positive_endpoint {kind : Kind} {parent : ReferenceStorageView.Parent} {instr : Instruction} {v next : View}
    (effect : ReferenceRuntimeAction.Action kind parent instr v next) (aligned : Aligned v)
    (positive : 0 < (span v instr.1).2) :
    (span v instr.1).1+(span v instr.1).2 ≤ next.memory.size := by
  rw [(computed effect aligned).1]
  exact (ReferenceMemoryCapacity.expansion_bounds _ _ _).2 positive

theorem empty_aligned (v : View) (empty : v.memory = ByteArray.empty) : Aligned v := by
  simp [Aligned,words,empty]

#print axioms computed
#print axioms preserves_alignment
#print axioms monotone
#print axioms positive_endpoint
#print axioms empty_aligned
end Eip8282.Audit.Integrator.ReferenceActionMemoryBounds

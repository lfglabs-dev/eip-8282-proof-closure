import Eip8282.Audit.Integrator.ReferenceReturnView

/-! Literal RETURN output slice after eager memory extension. The cached
Amsterdam `return_` extends memory and then uses `memory_read_bytes`, an
unpadded natural-end slice (EL 0cc100eb, instructions/system.py 314-344 and
vm/memory.py 39-60). This is an output equation for the existing Lean view,
not a Python execution or gas-refinement theorem. -/
namespace Eip8282.Audit.Integrator.ReferenceReturnSlice
open EvmYul
open ReferenceRuntimeView ReferenceReturnView ReferenceMemoryView
set_option autoImplicit false

private theorem buffer_eq_extract (b : ByteArray) (off len : Nat)
    (fits : len = 0 ∨ off+len ≤ b.size) :
    buffer b off len = b.extract off (off+len) := by
  have hpad : len - (min (off+len) b.size - off) = 0 := by
    rcases fits with h | h <;> omega
  apply ByteArray.ext
  simp only [buffer,ByteArray.data_extract,hpad,Array.replicate_zero,Array.append_empty]

/-- All offsets and lengths are allowed. Zero length does not require the
offset to lie inside the extended memory. No post-memory premise is used. -/
theorem output_eq_extract {parent : ReferenceStorageView.Parent} {v : View}
    {pre : EVM.State} (related : Related parent v pre) (off len : UInt256) :
    output v off len = (returnMemory v off len).extract off.toNat (off.toNat+len.toNat) := by
  have hb := ReferenceMemoryCapacity.expansion_bounds (words v) off.toNat len.toNat
  have hsize : v.memory.size ≤ 32*MachineState.M (words v) off.toNat len.toNat := by
    have hs : v.memory.size = 32*words v := by
      rw [words_related related]
      exact related.memory.size
    rw [hs]
    omega
  have same := ReferenceMemoryOperations.extend_same v.memory
    (32*MachineState.M (words v) off.toNat len.toNat) hsize
  change buffer v.memory off.toNat len.toNat = _
  rw [buffer_congr v.memory (returnMemory v off len) same off.toNat len.toNat]
  apply buffer_eq_extract
  by_cases hz : len.toNat = 0
  · exact Or.inl hz
  · right
    have hspan := hb.2 (by omega)
    simpa only [returnMemory,ReferenceMemoryOperations.extend,buffer_size] using hspan

#print axioms output_eq_extract
end Eip8282.Audit.Integrator.ReferenceReturnSlice

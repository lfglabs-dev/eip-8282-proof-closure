import Eip8282.Audit.Integrator.ReferenceMemoryOperations
import Eip8282.Audit.Integrator.RuntimeMemoryMonotone

/-! Shifted calldata writes versus source padded-buffer copies. Arbitrary source
positions and zero-length destinations are retained. Pinned sparse memory need
not physically grow to the eager source capacity; only coherence and byte views
are equated. These are byte-array/primitive-memory proofs, not Python execution.
-/
namespace Eip8282.Audit.Integrator.ReferenceCopyMemory
open EvmYul Eip8282.Audit.EntryReach
open ReferenceMemoryView ReferenceMemoryOperations
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

/-- copySlice may clamp both source and destination. Only an upper bound holds
without assumptions about source length or destination gaps. -/
theorem copySlice_size_le (src dst : ByteArray) (so dest len : Nat) :
    (src.copySlice so dst dest len).size ≤ max dst.size (dest+len) := by
  simp only [ByteArray.copySlice,ByteArray.size,Array.size_append,Array.size_extract]
  omega

/-- All branches of the actual sparse write, including exhausted calldata. -/
theorem write_size_le (src dst : ByteArray) (so dest len : Nat)
    (bounds : ReferenceMemoryWrite.Bounds src dst so dest len) :
    (ByteArray.write src so dst dest len).size ≤ max dst.size (dest+len) := by
  by_cases hz : len = 0
  · simp only [ByteArray.write,hz,↓reduceIte]
    omega
  · obtain ⟨hlen,hgap⟩ := bounds.resolve_left hz
    unfold ByteArray.write
    rw [if_neg hz]
    split
    · exact (copySlice_size_le _ _ _ _ _).trans (by omega)
    · rename_i hin
      have hg : dest-dst.size < 2^System.Platform.numBits := hgap (by omega)
      have hp : (dst ++ ffi.ByteArray.zeroes ⟨(dest-dst.size : Nat)⟩).size = max dst.size dest := by
        simp only [ByteArray.size_append,ffi.ByteArray.size_zeroes]
        rw [ffi.ByteArray.toNat_natCast_of_lt _ hg]
        omega
      have hb := copySlice_size_le
        (src ++ ffi.ByteArray.zeroes ⟨(min dst.size (dest+len)-(dest+min len (src.size-so)) : Nat)⟩)
        (dst ++ ffi.ByteArray.zeroes ⟨(dest-dst.size : Nat)⟩) so dest
        (min len (src.size-so)+(min dst.size (dest+len)-(dest+min len (src.size-so))))
      rw [hp] at hb
      exact hb.trans (by omega)

/-- Compare a shifted actual source with the correctly shifted padded buffer,
not a false global Same relation between the two source arrays. -/
theorem padded_write (src dst : ByteArray) (so dest len : Nat)
    (bounds : len = 0 ∨ (len < 2^System.Platform.numBits ∧
      dest-dst.size < 2^System.Platform.numBits)) :
    Same (ByteArray.write src so dst dest len)
      (ByteArray.write (buffer src so len) 0 dst dest len) := by
  by_cases hz : len = 0
  · subst len
    intro i
    rfl
  · obtain ⟨hlen,hgap⟩ := bounds.resolve_left hz
    have h₁ : ReferenceMemoryWrite.Bounds src dst so dest len := Or.inr ⟨hlen,fun _ => hgap⟩
    have h₂ : ReferenceMemoryWrite.Bounds (buffer src so len) dst 0 dest len :=
      Or.inr ⟨hlen,fun _ => hgap⟩
    intro i
    rw [ReferenceMemoryWrite.write_byte _ _ _ _ _ _ h₁,
      ReferenceMemoryWrite.write_byte _ _ _ _ _ _ h₂]
    split
    · rename_i hi
      rw [Nat.zero_add,buffer_byte src so len (i-dest) (by omega)]
    · rfl

/-- Literal eager source copy. Zero length does not test either position. -/
def copyMemory (reference data : ByteArray) (dest source len capacity : Nat) : ByteArray :=
  if len = 0 then reference else splice reference dest (buffer data source len) capacity

/-- The exact primitive memory projection of SharedState.calldatacopy. -/
def copyMachine (μ : MachineState) (data : ByteArray) (dest source len : UInt256) : MachineState :=
  {μ with
    memory := ByteArray.write data source.toNat μ.memory dest.toNat len.toNat,
    activeWords := UInt256.ofNat (MachineState.M μ.activeWords.toNat dest.toNat len.toNat)}

/-- Actual M supplies capacity; all padding bounds follow from the final cap.
No bound on calldata's source offset appears. -/
theorem copy_related (μ : MachineState) (reference data : ByteArray) (dest source len : UInt256)
    (related : Related μ reference) (cap : Nat)
    (capacity : MachineState.M μ.activeWords.toNat dest.toNat len.toNat ≤ cap)
    (host : 32*cap < 2^System.Platform.numBits) :
    Related (copyMachine μ data dest source len)
      (copyMemory reference data dest.toNat source.toNat len.toNat
        (32*MachineState.M μ.activeWords.toNat dest.toNat len.toNat)) := by
  by_cases hz : len.toNat = 0
  · simpa only [copyMachine,copyMemory,hz,ByteArray.write,MachineState.M,↓reduceIte,ofNat_toNat'] using related
  · have hb := ReferenceMemoryCapacity.expansion_bounds μ.activeWords.toNat dest.toNat len.toNat
    have hspan := hb.2 (by omega)
    have hlen : len.toNat < 2^System.Platform.numBits := by omega
    have hgap : dest.toNat-μ.memory.size < 2^System.Platform.numBits := by omega
    have hbound : ReferenceMemoryWrite.Bounds data μ.memory source.toNat dest.toNat len.toNat :=
      Or.inr ⟨hlen,fun _ => hgap⟩
    have hpadded := padded_write data μ.memory source.toNat dest.toNat len.toNat (Or.inr ⟨hlen,hgap⟩)
    have hs := store_view μ.memory reference (buffer data source.toNat len.toNat) dest.toNat
      (32*MachineState.M μ.activeWords.toNat dest.toNat len.toNat) related.bytes
      (by rw [related.size]; omega)
      (by rw [buffer_size]; omega)
      (by rw [buffer_size]; exact hspan) (by omega)
    have hbytes : Same (ByteArray.write data source.toNat μ.memory dest.toNat len.toNat)
        (splice reference dest.toNat (buffer data source.toNat len.toNat)
          (32*MachineState.M μ.activeWords.toNat dest.toNat len.toNat)) := by
      intro i
      exact (hpadded i).trans (by simpa only [buffer_size] using hs.1 i)
    have hsize := write_size_le data μ.memory source.toNat dest.toNat len.toNat hbound
    have hn : (UInt256.ofNat (MachineState.M μ.activeWords.toNat dest.toNat len.toNat)).toNat =
        MachineState.M μ.activeWords.toNat dest.toNat len.toNat :=
      toNat_ofNat_lit _ (RuntimeMemoryMonotone.expansion_fit μ.activeWords dest len)
    refine ⟨?_,?_,?_⟩
    · change (ByteArray.write data source.toNat μ.memory dest.toNat len.toNat).size ≤
        32*(UInt256.ofNat (MachineState.M μ.activeWords.toNat dest.toNat len.toNat)).toNat
      rw [hn]
      have hc := related.coherent
      change μ.memory.size ≤ 32*μ.activeWords.toNat at hc
      omega
    · change (copyMemory reference data dest.toNat source.toNat len.toNat _).size =
        32*(UInt256.ofNat (MachineState.M μ.activeWords.toNat dest.toNat len.toNat)).toNat
      rw [copyMemory,if_neg hz,hn]
      exact hs.2
    · rw [copyMemory,if_neg hz]
      exact hbytes

#print axioms copySlice_size_le
#print axioms write_size_le
#print axioms padded_write
#print axioms copy_related
end Eip8282.Audit.Integrator.ReferenceCopyMemory

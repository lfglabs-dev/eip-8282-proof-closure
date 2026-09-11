import Eip8282.Audit.Integrator.ReferenceMemoryWrite
import Eip8282.Audit.Integrator.ReferenceMemoryCapacity

/-! Compose actual sparse stores with the source-shaped eager extension and
slice replacement. No equality of physical buffers is assumed or concluded.
The source's Python allocation/byte representation remains an audited boundary. -/
namespace Eip8282.Audit.Integrator.ReferenceMemoryOperations
open EvmYul ReferenceMemoryView
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def extend (b : ByteArray) (capacity : Nat) : ByteArray := buffer b 0 capacity

theorem extend_same (b : ByteArray) (capacity : Nat) (fits : b.size ≤ capacity) :
    Same b (extend b capacity) := by
  intro i
  by_cases hi : i < capacity
  · simpa [extend] using (buffer_byte b 0 capacity i hi).symm
  · unfold byte
    rw [Array.getElem?_eq_none (by change b.size ≤ i; omega),
      Array.getElem?_eq_none (by change (buffer b 0 capacity).size ≤ i; rw [buffer_size]; omega)]

def splice (b : ByteArray) (off : Nat) (data : ByteArray) (capacity : Nat) : ByteArray :=
  ⟨(extend b capacity).data.extract 0 off ++ data.data ++
    (extend b capacity).data.extract (off+data.size) capacity⟩

theorem splice_eq (b data : ByteArray) (off capacity : Nat)
    (positive : 0 < data.size) (span : off+data.size ≤ capacity) :
    splice b off data capacity = ByteArray.write data 0 (extend b capacity) off data.size := by
  rw [ByteArray.write_eq_of_fits data (extend b capacity) off data.size positive rfl
    (by simpa [extend,buffer_size] using span)]
  simp only [splice,extend,buffer_size]

/-- A single actual write agrees with eager extension followed by a full source
slice replacement. Every padding bound is derived from the announced capacity. -/
theorem store_view (pinned reference data : ByteArray) (off capacity : Nat)
    (same : Same pinned reference) (old : reference.size ≤ capacity)
    (positive : 0 < data.size) (span : off+data.size ≤ capacity)
    (host : capacity < 2^System.Platform.numBits) :
    Same (ByteArray.write data 0 pinned off data.size) (splice reference off data capacity) ∧
      (splice reference off data capacity).size = capacity := by
  rw [splice_eq reference data off capacity positive span]
  constructor
  · apply ReferenceMemoryWrite.congr
    · intro i; rfl
    · intro i
      exact (same i).trans (extend_same reference capacity old i)
    · right; exact ⟨by omega,fun _ => by omega⟩
    · right; exact ⟨by omega,fun _ => by omega⟩
  · rw [ByteArray.size_write_of_fits data (extend reference capacity) off data.size positive rfl
      (by simpa [extend,buffer_size] using span)]
    exact buffer_size reference 0 capacity

structure Related (μ : MachineState) (reference : ByteArray) : Prop where
  coherent : ReferenceMemoryCapacity.Coherent μ
  size : reference.size = 32*μ.activeWords.toNat
  bytes : Same μ.memory reference

/-- Actual MSTORE chooses its own new capacity; the post relation is derived
from the input relation and operand/resource bounds. -/
theorem mstore (μ : MachineState) (reference : ByteArray) (off value : UInt256) (cap : Nat)
    (related : Related μ reference) (active : μ.activeWords.toNat ≤ cap)
    (span : off.toNat+32 ≤ 32*cap)
    (word : cap < UInt256.size) (host : 32*cap < 2^System.Platform.numBits) :
    Related (μ.mstore off value)
      (splice reference off.toNat value.toByteArray (32*(μ.mstore off value).activeWords.toNat)) := by
  have hc := ReferenceMemoryCapacity.mstore μ off value cap related.coherent active span word host
  have hb := ReferenceMemoryCapacity.expansion_bounds μ.activeWords.toNat off.toNat 32
  have hbound := ReferenceMemoryCapacity.expansion_le μ.activeWords.toNat off.toNat 32 cap active (Or.inr span)
  have hn : (μ.mstore off value).activeWords.toNat = MachineState.M μ.activeWords.toNat off.toNat 32 :=
    Eip8282.Audit.EntryReach.toNat_ofNat_lit _ (hbound.trans_lt word)
  have hs := hb.2 (by decide)
  have hv := store_view μ.memory reference value.toByteArray off.toNat
    (32*(μ.mstore off value).activeWords.toNat) related.bytes
    (by rw [related.size,hn]; omega)
    (by rw [UInt256.size_toByteArray]; decide)
    (by rw [UInt256.size_toByteArray,hn]; exact hs)
    (by rw [hn]; omega)
  exact ⟨hc.1,hv.2,by
    simpa only [MachineState.mstore,MachineState.writeWord,writeBytes,UInt256.size_toByteArray] using hv.1⟩

theorem mstore8 (μ : MachineState) (reference : ByteArray) (off value : UInt256) (cap : Nat)
    (related : Related μ reference) (active : μ.activeWords.toNat ≤ cap)
    (span : off.toNat+1 ≤ 32*cap)
    (word : cap < UInt256.size) (host : 32*cap < 2^System.Platform.numBits) :
    Related (μ.mstore8 off value)
      (splice reference off.toNat ⟨#[UInt8.ofNat value.toNat]⟩
        (32*(μ.mstore8 off value).activeWords.toNat)) := by
  have hc := ReferenceMemoryCapacity.mstore8 μ off value cap related.coherent active span word host
  have hb := ReferenceMemoryCapacity.expansion_bounds μ.activeWords.toNat off.toNat 1
  have hbound := ReferenceMemoryCapacity.expansion_le μ.activeWords.toNat off.toNat 1 cap active (Or.inr span)
  have hn : (μ.mstore8 off value).activeWords.toNat = MachineState.M μ.activeWords.toNat off.toNat 1 :=
    Eip8282.Audit.EntryReach.toNat_ofNat_lit _ (hbound.trans_lt word)
  have hs := hb.2 (by decide)
  have hv := store_view μ.memory reference ⟨#[UInt8.ofNat value.toNat]⟩ off.toNat
    (32*(μ.mstore8 off value).activeWords.toNat) related.bytes
    (by rw [related.size,hn]; omega) (by change 0 < 1; decide)
    (by change off.toNat+1 ≤ _; rw [hn]; exact hs)
    (by rw [hn]; omega)
  exact ⟨hc.1,hv.2,hv.1⟩

/-- Terminal observable follows from the same memory relation. A host-sized
length satisfies the pinned64-bit panic guard on either supported platform. -/
theorem return_output (μ : MachineState) (reference : ByteArray) (off len : UInt256)
    (related : Related μ reference) (host : len.toNat < 2^System.Platform.numBits) :
    (μ.evmReturn off len).H_return = buffer reference off.toNat len.toNat := by
  have h64 : len.toNat < 2^64 := by
    rcases System.Platform.numBits_eq with h | h <;> rw [h] at host <;> omega
  exact ReferenceMemoryView.return_output μ reference related.bytes off len h64 host

#print axioms extend_same
#print axioms splice_eq
#print axioms store_view
#print axioms mstore
#print axioms mstore8
#print axioms return_output
end Eip8282.Audit.Integrator.ReferenceMemoryOperations

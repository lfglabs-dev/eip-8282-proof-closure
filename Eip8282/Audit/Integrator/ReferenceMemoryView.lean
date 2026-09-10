import EvmYul.EVM.Proof.Memory

/-! Zero-extended memory observations for source-shaped buffer_read and pinned
readWithPadding. Physical reference memory is rounded and eagerly extended;
pinned memory can be sparse. Host padding bounds are explicit, not inferred
from a gas-erased execution. This is not a Python buffer implementation proof. -/
namespace Eip8282.Audit.Integrator.ReferenceMemoryView
open EvmYul
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def byte (b : ByteArray) (i : Nat) : UInt8 := b.data[i]?.getD 0

def Same (a b : ByteArray) : Prop := ∀ i, byte a i = byte b i

/-- Natural-index source slice followed by right zero padding. -/
def buffer (b : ByteArray) (start len : Nat) : ByteArray :=
  ⟨b.data.extract start (start+len) ++
    Array.replicate (len - (min (start+len) b.size - start)) 0⟩

theorem buffer_size (b : ByteArray) (start len : Nat) :
    (buffer b start len).size = len := by
  simp only [buffer,ByteArray.size,Array.size_append,Array.size_extract,Array.size_replicate]
  omega

private theorem unpadded (b : ByteArray) (start len : Nat) :
    b.readWithoutPadding start len = b.extract start (start+len) := by
  unfold ByteArray.readWithoutPadding
  split
  · rename_i h
    apply ByteArray.ext
    simp only [ByteArray.data_extract,ByteArray.data_empty]
    symm
    apply Array.extract_eq_empty_of_le
    change min (start+len) b.size ≤ start
    omega
  · apply ByteArray.ext
    simp only [ByteArray.data_extract]
    apply Array.extract_eq_extract_right.mpr
    change min (start+min len b.size-start) (b.size-start) =
      min (start+len-start) (b.size-start)
    omega

/-- Includes zero length and arbitrary source offsets. Only the padding length
needs the host conversion bound; no small source-offset premise is introduced. -/
theorem read_eq_buffer (b : ByteArray) (start len : Nat)
    (length64 : len < 2^64) (host : len < 2^System.Platform.numBits) :
    b.readWithPadding start len = buffer b start len := by
  unfold ByteArray.readWithPadding
  rw [if_neg (by omega),unpadded]
  dsimp only
  have hs : (b.extract start (start+len)).size ≤ len := by simp; omega
  have hread : (b.extract start (start+len)).size < 2^System.Platform.numBits := by omega
  have hpad : ({toBitVec := (len : BitVec System.Platform.numBits) -
      ((b.extract start (start+len)).size : BitVec System.Platform.numBits)} : USize).toNat =
      len-(b.extract start (start+len)).size := by
    simp only [USize.toNat,BitVec.toNat_sub,BitVec.natCast_eq_ofNat,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt host,Nat.mod_eq_of_lt hread]
    rw [show 2^System.Platform.numBits-(b.extract start (start+len)).size+len =
      2^System.Platform.numBits+(len-(b.extract start (start+len)).size) from by omega,
      Nat.add_mod_left,Nat.mod_eq_of_lt (by omega)]
  apply ByteArray.ext
  simp only [ByteArray.size_extract] at hpad
  simp only [ByteArray.data_append,ffi.ByteArray.zeroes,ByteArray.data_extract,
    ByteArray.size_extract,buffer]
  rw [hpad]

theorem buffer_byte (b : ByteArray) (start len i : Nat) (hi : i < len) :
    byte (buffer b start len) i = byte b (start+i) := by
  unfold byte buffer
  simp only [Array.getElem?_append,Array.size_extract,Array.getElem?_extract,
    Array.getElem?_replicate]
  split
  · rfl
  · rename_i h
    have hout : b.data.size ≤ start+i := by omega
    rw [Array.getElem?_eq_none (by omega)]
    split <;> rfl

theorem buffer_congr (a b : ByteArray) (same : Same a b) (start len : Nat) :
    buffer a start len = buffer b start len := by
  apply ByteArray.ext
  apply Array.ext_getElem?
  intro i
  by_cases hi : i < len
  · have ha : i < (buffer a start len).data.size := by simpa [buffer_size] using hi
    have hb : i < (buffer b start len).data.size := by simpa [buffer_size] using hi
    have hv := (buffer_byte a start len i hi).trans ((same (start+i)).trans (buffer_byte b start len i hi).symm)
    unfold byte at hv
    rw [Array.getElem?_eq_getElem ha,Array.getElem?_eq_getElem hb] at hv ⊢
    exact congrArg some hv
  · rw [Array.getElem?_eq_none (by simpa [buffer_size] using Nat.le_of_not_gt hi),
      Array.getElem?_eq_none (by simpa [buffer_size] using Nat.le_of_not_gt hi)]

theorem read_congr (a b : ByteArray) (same : Same a b) (start len : Nat)
    (length64 : len < 2^64) (host : len < 2^System.Platform.numBits) :
    a.readWithPadding start len = b.readWithPadding start len := by
  rw [read_eq_buffer a start len length64 host,read_eq_buffer b start len length64 host]
  exact buffer_congr a b same start len

/-- RETURN observes the same zero-extended bytes, irrespective of unused
physical zero padding. It imposes no equality on the terminal internal PC. -/
theorem return_output (μ : MachineState) (referenceMemory : ByteArray)
    (same : Same μ.memory referenceMemory) (start len : UInt256)
    (length64 : len.toNat < 2^64) (host : len.toNat < 2^System.Platform.numBits) :
    (μ.evmReturn start len).H_return = buffer referenceMemory start.toNat len.toNat := by
  change μ.memory.readWithPadding start.toNat len.toNat = _
  rw [read_eq_buffer μ.memory start.toNat len.toNat length64 host]
  exact buffer_congr μ.memory referenceMemory same start.toNat len.toNat

#print axioms buffer_size
#print axioms read_eq_buffer
#print axioms buffer_byte
#print axioms buffer_congr
#print axioms read_congr
#print axioms return_output
end Eip8282.Audit.Integrator.ReferenceMemoryView

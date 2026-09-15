import Eip8282.Audit.Execution.Words
import EvmYul.EVM.Proof.Block
import EvmYul.EVM.Proof.Memory
import EvmYul.EVM.Proof.MemoryStep

/-! Related candidate proofs, grouped by topic. Original namespaces are preserved.
See audit/MODULE-LAYOUT.md for the source-module migration map. -/

section

/-! ## ReferenceMemoryView -/

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

end

section

/-! ## ReferenceMemoryCapacity -/

/-! Actual pinned memory expansion and the source's rounded-capacity cost.
Physical store endpoints, not RETURN lengths, determine the high-water mark.
Trace producers must establish the operand bounds consumed here. -/
namespace Eip8282.Audit.Integrator.ReferenceMemoryCapacity
open EvmYul Eip8282.Audit.EntryReach
set_option autoImplicit false

def Coherent (μ : MachineState) : Prop := μ.memory.size ≤ 32*μ.activeWords.toNat

theorem expansion_bounds (aw off len : Nat) :
    aw ≤ MachineState.M aw off len ∧
    (0 < len → off+len ≤ 32*MachineState.M aw off len) := by
  cases len with
  | zero => simp [MachineState.M]
  | succ len => simp only [MachineState.M]; omega

theorem expansion_le (aw off len cap : Nat)
    (active : aw ≤ cap) (span : len = 0 ∨ off+len ≤ 32*cap) :
    MachineState.M aw off len ≤ cap := by
  cases len with
  | zero => exact active
  | succ len => simp only [MachineState.M]; omega

theorem mstore (μ : MachineState) (off value : UInt256) (cap : Nat)
    (coherent : Coherent μ) (active : μ.activeWords.toNat ≤ cap)
    (span : off.toNat+32 ≤ 32*cap)
    (word : cap < UInt256.size) (host : 32*cap < 2^System.Platform.numBits) :
    Coherent (μ.mstore off value) ∧ (μ.mstore off value).activeWords.toNat ≤ cap := by
  have hb := expansion_bounds μ.activeWords.toNat off.toNat 32
  have hc := expansion_le μ.activeWords.toNat off.toNat 32 cap active (Or.inr span)
  have hn : (μ.mstore off value).activeWords.toNat =
      MachineState.M μ.activeWords.toNat off.toNat 32 :=
    toNat_ofNat_lit _ (hc.trans_lt word)
  have hm := MachineState.size_memory_mstore_of_pad μ off value (by omega)
  unfold Coherent at coherent ⊢
  rw [hm,hn]
  have hspan := hb.2 (by decide)
  constructor <;> omega

theorem mstore8 (μ : MachineState) (off value : UInt256) (cap : Nat)
    (coherent : Coherent μ) (active : μ.activeWords.toNat ≤ cap)
    (span : off.toNat+1 ≤ 32*cap)
    (word : cap < UInt256.size) (host : 32*cap < 2^System.Platform.numBits) :
    Coherent (μ.mstore8 off value) ∧ (μ.mstore8 off value).activeWords.toNat ≤ cap := by
  have hb := expansion_bounds μ.activeWords.toNat off.toNat 1
  have hc := expansion_le μ.activeWords.toNat off.toNat 1 cap active (Or.inr span)
  have hn : (μ.mstore8 off value).activeWords.toNat =
      MachineState.M μ.activeWords.toNat off.toNat 1 :=
    toNat_ofNat_lit _ (hc.trans_lt word)
  have hm := MachineState.size_memory_mstore8_of_pad μ off value (by omega)
  unfold Coherent at coherent ⊢
  rw [hm,hn]
  have hspan := hb.2 (by decide)
  constructor <;> omega

/-- Final full-word stores overhang the public RETURN buffers. -/
theorem deposit_item_span (i : Nat) (hi : i < 64) :
    184*i+160+32 ≤ 11784 ∧ 11784 ≤ 32*369 := by omega

theorem exit_item_span (i : Nat) (hi : i < 16) :
    68*i+52+32 ≤ 1104 ∧ 1104 ≤ 32*35 := by omega

/-- Source memory cost on rounded word capacity. -/
def cost (words : Nat) : Nat := 3*words + words*words/512

theorem cost_mono {a b : Nat} (h : a ≤ b) : cost a ≤ cost b := by
  have hm := Nat.mul_le_mul h h
  have hd := Nat.div_le_div_right hm (c := 512)
  unfold cost
  omega

/-- A finite monotone expansion history records each exact cost difference. -/
inductive Charges : Nat → Nat → Nat → Prop where
  | nil (a : Nat) : Charges a a 0
  | step {a b c total : Nat} : Charges a b total → b ≤ c →
      Charges a c (total+(cost c-cost b))

theorem telescopes {a b total : Nat} (h : Charges a b total) :
    a ≤ b ∧ total+cost a = cost b := by
  induction h with
  | nil => simp
  | step h order ih =>
    have hc := cost_mono order
    constructor <;> omega

theorem system_costs : cost 369 = 1372 ∧ cost 35 = 107 := by decide +kernel

#print axioms expansion_bounds
#print axioms expansion_le
#print axioms mstore
#print axioms mstore8
#print axioms deposit_item_span
#print axioms exit_item_span
#print axioms cost_mono
#print axioms telescopes
#print axioms system_costs
end Eip8282.Audit.Integrator.ReferenceMemoryCapacity

end

section

/-! ## ReferenceMemoryWrite -/

/-! Actual sparse ByteArray.write observations. Padding bounds concern the
branches that allocate zeros; no small source-offset or predicted post-memory
relation is assumed. This is a pinned byte-array theorem, not Python execution
or resource adequacy. -/
namespace Eip8282.Audit.Integrator.ReferenceMemoryWrite
open EvmYul ReferenceMemoryView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-- Zero-length and out-of-range-source branches need no destination-gap bound. -/
def Bounds (src dst : ByteArray) (so dest len : Nat) : Prop :=
  len = 0 ∨ (len < 2^System.Platform.numBits ∧
    (so < src.size → dest-dst.size < 2^System.Platform.numBits))

private theorem zeroes (n : Nat) (h : n < 2^System.Platform.numBits) :
    (ffi.ByteArray.zeroes ⟨n⟩).data = Array.replicate n 0 := by
  simp only [ffi.ByteArray.zeroes]
  rw [ffi.ByteArray.toNat_natCast_of_lt n h]

/-- Exact byte observation, including implicit zero suffixes of either buffer. -/
theorem write_byte (src dst : ByteArray) (so dest len i : Nat)
    (bounds : Bounds src dst so dest len) :
    byte (ByteArray.write src so dst dest len) i =
      if dest ≤ i ∧ i < dest+len then byte src (so+(i-dest)) else byte dst i := by
  by_cases hz : len=0
  · subst len
    simp [ByteArray.write]
  · obtain ⟨hlen,hgap⟩ := bounds.resolve_left hz
    unfold ByteArray.write
    rw [if_neg hz]
    split
    · rename_i hout
      dsimp only
      simp only [byte,ByteArray.copySlice]
      rw [zeroes _ (by omega)]
      simp only [Array.getElem?_append,Array.getElem?_extract,
        Array.getElem?_replicate,Array.size_append,Array.size_extract,Array.size_replicate]
      simp only [ByteArray.size] at *
      simp only [Nat.zero_add,Nat.sub_zero,Nat.min_self] at *
      repeat' first | omega | rfl | split
      all_goals try simp only [Option.getD_some,Option.getD_none]
      all_goals first | (rw [Array.getElem?_eq_none (by omega)]; rfl) | (congr 2; omega)
    · rename_i hin
      have hgap' := hgap (by omega)
      dsimp only
      simp only [byte,ByteArray.copySlice,ByteArray.data_append]
      rw [zeroes (dest-dst.size) hgap',zeroes (min dst.size (dest+len)-(dest+min len (src.size-so))) (by omega)]
      simp only [Array.getElem?_append,
        Array.getElem?_extract,Array.getElem?_replicate,Array.size_append,
        Array.size_extract,Array.size_replicate]
      simp only [ByteArray.size] at *
      simp only [Nat.zero_add,Nat.sub_zero,Nat.min_self] at *
      repeat' first | omega | rfl | split
      all_goals try simp only [Option.getD_some,Option.getD_none]
      all_goals first | (rw [Array.getElem?_eq_none (by omega)]; rfl) | (congr 2; omega)

/-- Pointwise input equality suffices even when physical zero suffixes differ. -/
theorem congr (src₁ src₂ dst₁ dst₂ : ByteArray) (so dest len : Nat)
    (sources : Same src₁ src₂) (destinations : Same dst₁ dst₂)
    (bound₁ : Bounds src₁ dst₁ so dest len) (bound₂ : Bounds src₂ dst₂ so dest len) :
    Same (ByteArray.write src₁ so dst₁ dest len) (ByteArray.write src₂ so dst₂ dest len) := by
  intro i
  rw [write_byte _ _ _ _ _ _ bound₁,write_byte _ _ _ _ _ _ bound₂]
  split
  · exact sources _
  · exact destinations _

#print axioms write_byte
#print axioms congr
end Eip8282.Audit.Integrator.ReferenceMemoryWrite

end

section

/-! ## ReferenceMemoryOperations -/

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

end

section

/-! ## ReferenceMemoryStep -/

/-! Memory relation along actual accepted EVM opcodes. Z and step gas updates
are retained, and the observed post-state is the actual supplied step result.
Source instruction interpretation and resource sufficiency remain separate. -/
namespace Eip8282.Audit.Integrator.ReferenceMemoryStep
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open ReferenceMemoryOperations
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem charged_relation (pre : EVM.State) (op : Operation .EVM) (cost : Nat)
    (reference : ByteArray) (h : Related pre.toMachineState reference) :
    Related (stepPre cost (zMid pre op)).toMachineState reference :=
  ⟨h.coherent,h.size,h.bytes⟩

theorem mstore {vj : Array UInt256} {pre mid post : EVM.State} {fuel cost : Nat}
    (accepted : Z vj .MSTORE pre = .ok (mid,cost))
    (executed : StepOk (fuel+1) cost (.MSTORE,none) mid post)
    (reference : ByteArray) (related : Related pre.toMachineState reference)
    (rest : Stack UInt256) (off value : UInt256)
    (operands : pre.stack.pop2 = some (rest,off,value)) (cap : Nat)
    (active : pre.activeWords.toNat ≤ cap) (span : off.toNat+32 ≤ 32*cap)
    (word : cap < UInt256.size) (host : 32*cap < 2^System.Platform.numBits) :
    Related post.toMachineState (splice reference off.toNat value.toByteArray (32*post.activeWords.toNat)) ∧
      post.stack = rest ∧ post.accountMap = pre.accountMap ∧ post.substate = pre.substate := by
  obtain rfl := Z_ok_state accepted
  have known := EvmYul.EVM.Proof.step_MSTORE fuel cost (zMid pre .MSTORE) rest off value operands
  have same := Except.ok.inj (executed.symm.trans known)
  subst post
  exact ⟨ReferenceMemoryOperations.mstore _ reference off value cap
    (charged_relation pre .MSTORE cost reference related) active span word host,rfl,rfl,rfl⟩

theorem mstore8 {vj : Array UInt256} {pre mid post : EVM.State} {fuel cost : Nat}
    (accepted : Z vj .MSTORE8 pre = .ok (mid,cost))
    (executed : StepOk (fuel+1) cost (.MSTORE8,none) mid post)
    (reference : ByteArray) (related : Related pre.toMachineState reference)
    (rest : Stack UInt256) (off value : UInt256)
    (operands : pre.stack.pop2 = some (rest,off,value)) (cap : Nat)
    (active : pre.activeWords.toNat ≤ cap) (span : off.toNat+1 ≤ 32*cap)
    (word : cap < UInt256.size) (host : 32*cap < 2^System.Platform.numBits) :
    Related post.toMachineState
      (splice reference off.toNat ⟨#[UInt8.ofNat value.toNat]⟩ (32*post.activeWords.toNat)) ∧
      post.stack = rest ∧ post.accountMap = pre.accountMap ∧ post.substate = pre.substate := by
  obtain rfl := Z_ok_state accepted
  have known := EvmYul.EVM.Proof.step_MSTORE8 fuel cost (zMid pre .MSTORE8) rest off value operands
  have same := Except.ok.inj (executed.symm.trans known)
  subst post
  exact ⟨ReferenceMemoryOperations.mstore8 _ reference off value cap
    (charged_relation pre .MSTORE8 cost reference related) active span word host,rfl,rfl,rfl⟩

theorem return_output {vj : Array UInt256} {pre mid post : EVM.State} {fuel cost : Nat}
    (accepted : Z vj .RETURN pre = .ok (mid,cost))
    (executed : StepOk (fuel+1) cost (.RETURN,none) mid post)
    (reference : ByteArray) (related : Related pre.toMachineState reference)
    (rest : Stack UInt256) (off len : UInt256)
    (operands : pre.stack.pop2 = some (rest,off,len))
    (host : len.toNat < 2^System.Platform.numBits) :
    post.H_return = ReferenceMemoryView.buffer reference off.toNat len.toNat ∧
      post.stack = rest ∧ post.accountMap = pre.accountMap ∧ post.substate = pre.substate := by
  obtain rfl := Z_ok_state accepted
  have known := EvmYul.EVM.Proof.step_RETURN fuel cost (zMid pre .RETURN) rest off len operands
  have same := Except.ok.inj (executed.symm.trans known)
  subst post
  exact ⟨ReferenceMemoryOperations.return_output _ reference off len
    (charged_relation pre .RETURN cost reference related) host,rfl,rfl,rfl⟩

#print axioms mstore
#print axioms mstore8
#print axioms return_output
end Eip8282.Audit.Integrator.ReferenceMemoryStep

end

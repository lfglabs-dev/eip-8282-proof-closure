import Eip8282.Audit.Integrator.ReferenceWordOps
import Eip8282.Audit.Integrator.Topics.ReferenceMemory
import Eip8282.Audit.Integrator.ReferenceControlOps

/-! Source-shaped environment operations for the pinned runtime opcode subset.
Archived Amsterdam EL0cc100eb190b64b23baba72dac0165652eaec252
vm/instructions/environment.py:113-205 SHA256
8c57bd699b99ff8b4d8e41e6a9c89cd1a03dda8160bf1d6dffe091932ec03657.
Actual raw steps change only stack/running PC. Source caller-byte encoding,
apparent-value context binding, Python numeric/byte interpretation and gas/error
admission are separate adapters. ADDRESS is absent from the runtime allowed set.
CALLDATALOAD retains arbitrary word offsets, including offsets above 2^64. -/
namespace Eip8282.Audit.Integrator.ReferenceEnvironmentOps
open EvmYul EvmYul.EVM
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open ReferenceMemoryView
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private theorem toList_loop (data : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop data i r = r.reverse ++ data.data.toList.drop i := by
  rw [ByteArray.toList.loop]
  split
  · rename_i hi
    rw [toList_loop data (i+1) (data.get! i::r),
      List.drop_eq_getElem_cons (i := i) (by simpa using hi)]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append,
      Array.getElem_toList]
    congr 2
    exact getElem!_pos data.data i hi
  · rename_i hi
    rw [List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_gt hi),List.append_nil]
termination_by data.size-i

theorem toList_eq (data : ByteArray) : data.toList = data.data.toList := by
  simpa only [ByteArray.toList,List.reverse_nil,List.nil_append,List.drop_zero] using
    toList_loop data 0 []

/-- Unlike readWithPadding, actual CALLDATALOAD uses readBytes, whose large
source-offset branch is a list slice. Both branches give the same natural
32-byte right-padded buffer; padding is small on either supported host. -/
theorem load_bytes (data : ByteArray) (off : Nat) :
    data.readBytes off 32 = buffer data off 32 := by
  have hread : (if off < 2^64 && (32 : Nat) < 2^64 then
      data.copySlice off ByteArray.empty 0 32
    else (⟨⟨data.toList.drop off |>.take 32⟩⟩ : ByteArray)) = data.extract off (off+32) := by
    split
    · unfold ByteArray.extract
      rw [Nat.add_sub_cancel_left]
    · apply ByteArray.ext
      apply Array.ext'
      simp [toList_eq,Array.toList_extract,List.extract]
  unfold ByteArray.readBytes
  rw [hread]
  have hs : (data.extract off (off+32)).size ≤ 32 := by simp; omega
  have hp : ((⟨32-(data.extract off (off+32)).size⟩ : USize)).toNat =
      32-(data.extract off (off+32)).size := ffi.ByteArray.toNat_usizeSub_of_le _ hs
  apply ByteArray.ext
  simp only [ByteArray.data_append,ffi.ByteArray.zeroes,ByteArray.data_extract,buffer]
  simp only [BitVec.natCast_eq_ofNat] at hp ⊢
  have h32 : BitVec.ofNat System.Platform.numBits 32 = (32 : BitVec System.Platform.numBits) := by
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> rfl
  rw [h32,hp]
  simp only [ByteArray.size_extract]

/-- Big-endian conversion of the exact source-shaped padded input word. -/
def load (data : ByteArray) (off : Nat) : UInt256 := uInt256OfByteArray (buffer data off 32)

theorem caller_value (s : EVM.State) :
    (UInt256.ofNat s.executionEnv.source.val).toNat = s.executionEnv.source.val := by
  apply toNat_ofNat_lit
  exact s.executionEnv.source.isLt.trans_le (by decide)

theorem caller_step (s : EVM.State) :
    EvmYul.step (τ := .EVM) .CALLER none s =
      .ok (s.replaceStackAndIncrPC (UInt256.ofNat s.executionEnv.source.val::s.stack)) :=
  pureStep_sound (by decide) rfl

theorem callvalue_step (s : EVM.State) :
    EvmYul.step (τ := .EVM) .CALLVALUE none s =
      .ok (s.replaceStackAndIncrPC (s.executionEnv.weiValue::s.stack)) :=
  pureStep_sound (by decide) rfl

/-- Raw pinned size conversion is modular; source checked U256 construction
is justified only when the actual input length fits. -/
theorem calldatasize_value (s : EVM.State) (fit : s.executionEnv.calldata.size < UInt256.size) :
    (UInt256.ofNat s.executionEnv.calldata.size).toNat = s.executionEnv.calldata.size :=
  toNat_ofNat_lit _ fit

theorem calldatasize_step (s : EVM.State) :
    EvmYul.step (τ := .EVM) .CALLDATASIZE none s =
      .ok (s.replaceStackAndIncrPC (UInt256.ofNat s.executionEnv.calldata.size::s.stack)) :=
  pureStep_sound (by decide) rfl

theorem calldataload_step (s : EVM.State) (off : UInt256) (rest : Stack UInt256)
    (stack : s.stack = off::rest) :
    EvmYul.step (τ := .EVM) .CALLDATALOAD none s =
      .ok (s.replaceStackAndIncrPC (load s.executionEnv.calldata off.toNat::rest)) := by
  apply pureStep_sound (by decide)
  simp only [pureStep,stack,EvmYul.State.calldataload,load,load_bytes]

/-- The whole-state step equations above retain every field besides stack/PC.
This companion supplies the source natural running-PC equation under its bound. -/
theorem running_pc (s : EVM.State) (stack : Stack UInt256)
    (fit : s.pc.toNat+1 < UInt256.size) :
    (s.replaceStackAndIncrPC stack).pc.toNat = s.pc.toNat+1 :=
  ReferenceControlOps.next_pc s stack 1 fit

/-- Source end-pop offset and end-push value match the actual head stack. -/
theorem python_load (data : ByteArray) (off : UInt256) (base : List UInt256) :
    ReferenceWordOps.fromPython (base++[off]) = off::ReferenceWordOps.fromPython base ∧
    ReferenceWordOps.fromPython (base++[load data off.toNat]) =
      load data off.toNat::ReferenceWordOps.fromPython base := by
  simp [ReferenceWordOps.fromPython,List.reverse_append]

#print axioms toList_eq
#print axioms load_bytes
#print axioms caller_value
#print axioms caller_step
#print axioms callvalue_step
#print axioms calldatasize_value
#print axioms calldatasize_step
#print axioms calldataload_step
#print axioms running_pc
#print axioms python_load
end Eip8282.Audit.Integrator.ReferenceEnvironmentOps

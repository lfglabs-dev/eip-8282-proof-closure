import Eip8282.Audit.Integrator.FactoryRuntimeReturn

/-! Exact bytes returned by the factory's MSTORE/RETURN tail. These are generic
word/address encodings, with no hash, creation-success or deployment premise. -/
namespace Eip8282.Audit.Integrator.FactoryReturnEncoding
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.EntryReach
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

theorem output_word (kind : Kind) (word : UInt256) :
    FactoryRuntimeReturn.output kind word = word.toByteArray.extract 12 32 := by
  have hfit : 0 + 32 ≤ (Initialization.initCode kind).size := by cases kind <;> decide
  unfold FactoryRuntimeReturn.output FactoryRuntimeReturn.returnedMemory mstoreMem
  change (ByteArray.write word.toByteArray 0 (Initialization.initCode kind) 0 32).readWithPadding 12 20 = _
  rw [ByteArray.readWithPadding_eq_extract _ 12 20 (by decide) (by decide)
    (by rw [ByteArray.size_write_of_fits _ _ _ _ (by decide) (UInt256.size_toByteArray word) hfit]; omega)]
  rw [ByteArray.write_eq_of_fits _ _ _ _ (by decide) (UInt256.size_toByteArray word) hfit]
  apply ByteArray.ext
  simp only [ByteArray.data_extract, Array.extract_zero, Array.empty_append]
  simpa using Array.extract_append_of_le word.toByteArray.data #[]
    ((Initialization.initCode kind).data.extract 32 (Initialization.initCode kind).size) 12 32
    (by rw [ByteArray.size_data, UInt256.size_toByteArray])

theorem address_bytes (address : AccountAddress) :
    address.toByteArray.data.toList = toBeBytesFixed address.val 20 := by
  have hb : (BE address.val).data.toList = toBytesBigEndian address.val := List.toList_data_toByteArray
  have hs : (BE address.val).size = (toBytesBigEndian address.val).length := List.size_toByteArray
  have hlen := congrArg List.length (toBeBytesFixed_eq_zeroPad address.val 20 address.isLt)
  have hl : (BE address.val).size ≤ 20 := by
    simp only [length_toBeBytesFixed, List.length_append, List.length_replicate] at hlen
    rw [hs]
    omega
  have hw : 20 < 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
  have hn : (BE address.val).size < 2 ^ System.Platform.numBits := by omega
  have h20 : (20 : BitVec System.Platform.numBits).toNat = 20 := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
  have hz : ∀ u : USize, (ffi.ByteArray.zeroes u).data.toList = List.replicate u.toNat 0 := by
    intro u; simp [ffi.ByteArray.zeroes]
  rw [toBeBytesFixed_eq_zeroPad address.val 20 address.isLt]
  unfold AccountAddress.toByteArray
  rw [ByteArray.toList_data_append, hz, hb]
  simp only [USize.toNat, BitVec.toNat_sub, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, h20]
  rw [show 2 ^ System.Platform.numBits - (BE address.val).size + 20 =
    2 ^ System.Platform.numBits + (20 - (BE address.val).size) by omega]
  rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt (by omega : 20 - (BE address.val).size < 2 ^ System.Platform.numBits), hs]

theorem address_word_bytes (address : AccountAddress) :
    (UInt256.ofNat address.val).toByteArray.extract 12 32 = address.toByteArray := by
  have hf : address.val < UInt256.size := by
    have := address.isLt
    unfold AccountAddress.size UInt256.size at *
    omega
  have hn : (UInt256.ofNat address.val).toNat = address.val := Nat.mod_eq_of_lt hf
  apply ByteArray.ext
  apply Array.ext'
  simp only [ByteArray.data_extract, Array.toList_extract, UInt256.toList_data_toByteArray,
    hn, address_bytes, List.extract_eq_take_drop]
  apply List.ext_getElem
  · simp
  · intro i hi _
    have hi20 : i < 20 := by simpa using hi
    rw [List.getElem_take, List.getElem_drop, getElem_toBeBytesFixed, getElem_toBeBytesFixed]
    rw [show 32 - 1 - (12 + i) = 20 - 1 - i by omega]

theorem output_address (kind : Kind) (address : AccountAddress) :
    FactoryRuntimeReturn.output kind (UInt256.ofNat address.val) = address.toByteArray := by
  rw [output_word, address_word_bytes]

theorem output_size (kind : Kind) (word : UInt256) :
    (FactoryRuntimeReturn.output kind word).size = 20 := by
  rw [output_word]
  simp [UInt256.size_toByteArray]

#print axioms output_word
#print axioms address_word_bytes
#print axioms output_address
#print axioms output_size
end Eip8282.Audit.Integrator.FactoryReturnEncoding

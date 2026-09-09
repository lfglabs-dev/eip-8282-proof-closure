import Eip8282.Audit.Integrator.AppendSpec

/-!
# Authentic exit receipts

An exit record is the immediate caller encoded as twenty big-endian bytes,
followed by the caller's forty-eight calldata bytes. The specification below
uses a fixed-width base-256 encoder, independently of the runtime's SHL/MSTORE
and CALLDATACOPY sequence. It makes no signature-validation claim.
-/

namespace Eip8282.Audit.Integrator.ExitRecord

open EvmYul EvmYul.EVM
open Eip8282.Audit.XiTransport
open Eip8282.Audit.EntryReach
open Eip8282.Audit.Integrator

set_option maxHeartbeats 1600000

def addressBytes (caller : AccountAddress) : ByteArray :=
  (toBeBytesFixed caller.val 20).toByteArray

def record (caller : AccountAddress) (pubkey : ByteArray) : ByteArray :=
  addressBytes caller ++ pubkey

theorem addressBytes_size (caller : AccountAddress) : (addressBytes caller).size = 20 := by
  simp [addressBytes, List.size_toByteArray]

theorem record_size (caller : AccountAddress) (pubkey : ByteArray) (h : pubkey.size = 48) :
    (record caller pubkey).size = 68 := by
  simp [record, addressBytes_size, h]

theorem shifted_caller_value (caller : AccountAddress) :
    (UInt256.shiftLeft (UInt256.ofNat caller.val) (UInt256.ofNat 96)).toNat =
      caller.val * 256 ^ 12 := by
  unfold UInt256.shiftLeft
  rw [if_neg (by decide)]
  change ((caller.val % UInt256.size) <<< 96) % UInt256.size = _
  have hcaller : caller.val < UInt256.size := by
    have := caller.isLt
    unfold AccountAddress.size UInt256.size at *
    omega
  rw [Nat.mod_eq_of_lt hcaller, Nat.shiftLeft_eq]
  change (caller.val * 256 ^ 12) % UInt256.size = caller.val * 256 ^ 12
  apply Nat.mod_eq_of_lt
  have := caller.isLt
  unfold AccountAddress.size UInt256.size at *
  omega

/-- The first twenty bytes of the left-aligned address word are its independent
twenty-byte big-endian encoding. The inherent 160-bit address bound prevents wrap. -/
theorem shifted_caller_prefix (caller : AccountAddress) :
    ((UInt256.shiftLeft (UInt256.ofNat caller.val) (UInt256.ofNat 96)).toByteArray.extract 0 20) = addressBytes caller := by
  apply ByteArray.ext
  apply Array.ext'
  simp only [ByteArray.data_extract, Array.toList_extract, UInt256.toList_data_toByteArray,
    shifted_caller_value, addressBytes, List.toList_data_toByteArray,
    List.extract_eq_take_drop, List.drop_zero]
  apply List.ext_getElem
  · simp
  · intro i hi _
    have hi20 : i < 20 := by simpa using hi
    rw [List.getElem_take, getElem_toBeBytesFixed, getElem_toBeBytesFixed]
    have hexp : 32 - 1 - i = (20 - 1 - i) + 12 := by omega
    rw [hexp, Nat.pow_add, Nat.mul_div_mul_right _ _ (by decide : 0 < 256 ^ 12)]

theorem mstore_empty (word : UInt256) :
    mstoreMem .empty (UInt256.ofNat 0) word = word.toByteArray := by
  unfold mstoreMem
  change ByteArray.write word.toByteArray 0 .empty 0 32 = _
  rw [ByteArray.write_eq_of_grows _ _ 0 32 (by decide) (UInt256.size_toByteArray word)
    (by decide) (by simp)]
  apply ByteArray.ext
  simp

/-- Copying the pubkey at byte 20 overwrites the trailing twelve zero bytes of
the address word and grows memory to exactly the independent 68-byte record. -/
theorem staging (caller : AccountAddress) (pubkey : ByteArray) (hsize : pubkey.size = 48) :
    ByteArray.write pubkey 0
      (UInt256.shiftLeft (UInt256.ofNat caller.val) (UInt256.ofNat 96)).toByteArray 20 48 =
      record caller pubkey := by
  rw [ByteArray.write_eq_of_grows _ _ 20 48 (by decide) hsize
    (by rw [UInt256.size_toByteArray]; decide)
    (by rw [UInt256.size_toByteArray]; simp)]
  rw [UInt256.size_toByteArray]
  simp only [show 20 - 32 = 0 by decide, Array.replicate_zero, Array.append_empty]
  rw [← ByteArray.data_extract, shifted_caller_prefix caller]
  unfold record
  apply ByteArray.ext
  exact ByteArray.data_append.symm

theorem staged_record (c : XiCall .exit) (hsize : c.env.calldata.size = 48) :
    (Exit.stagedMem c).readWithPadding 0 68 = record c.env.source c.env.calldata := by
  have hstage : Exit.stagedMem c = record c.env.source c.env.calldata := by
    unfold Exit.stagedMem cdcopyMem
    rw [AppendSpec.exit_item_environment]
    change ByteArray.write c.env.calldata 0
      (mstoreMem .empty (UInt256.ofNat 0)
        (UInt256.shiftLeft (UInt256.ofNat c.env.source.val) (UInt256.ofNat 96))) 20 48 = _
    rw [mstore_empty]
    exact staging _ _ hsize
  rw [hstage, ByteArray.readWithPadding_eq_extract _ 0 68 (by decide) (by decide)
    (by rw [record_size _ _ hsize])]
  apply ByteArray.ext
  simp only [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by rw [ByteArray.size_data, record_size _ _ hsize])

theorem authentic_log (c : XiCall .exit) (hsize : c.env.calldata.size = 48) :
    AppendSpec.AppendedLog c (record c.env.source c.env.calldata)
      (EndpointState.exitAppendState c).substate := by
  have h := AppendSpec.exit_append_log c
  rwa [staged_record c hsize] at h

theorem submission_receipt (c : XiCall .exit)
    (huser : Exit.callerWord c ≠ sysW) (hen : Exit.excessWord c ≠ INH)
    (hperm : c.env.perm = true) {n : Nat} {o i : UInt256}
    (hfee : Exit.FeeLoopEnds c n o i) (hsize : c.env.calldata.size = 48)
    (hpaid : ¬ Exit.valueWord c < Exit.feeWord o)
    (hg : 87 * n + 150000 ≤ c.gas.toNat) (hf : 24 * n + 122 ≤ c.fuel) :
    ∃ created world gas substate,
      c.result = .ok (.success (created, world, gas, substate) .empty) ∧
      AppendSpec.AppendedLog c (record c.env.source c.env.calldata) substate ∧
      AppendSpec.OtherAccountsUnchanged c world := by
  have hword : Exit.cdsizeWord c = UInt256.ofNat 48 := by
    change UInt256.ofNat c.env.calldata.size = _
    rw [hsize]
  obtain ⟨gas, hres⟩ := EndpointState.exit_append_result c huser hen hperm hfee hword hpaid hg hf
  exact ⟨_, _, gas, _, hres, authentic_log c hsize, AppendSpec.exit_other_accounts c⟩

#print axioms staged_record
#print axioms submission_receipt

end Eip8282.Audit.Integrator.ExitRecord

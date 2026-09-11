import Eip8282.Audit.Integrator.NestedEventArgs

/-!
The pinned CREATE address encoder is total on its typed inputs. This proves
Option nonfailure, not cryptographic address correctness. CREATE2's encoder
returns Some directly; no length property of the opaque KEC output is used.
-/
namespace Eip8282.Audit.Integrator.CreationPreimageTotal
open EvmYul EvmYul.EVM
open NestedEvents
open private s from EvmYul.Wheels
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

/-- A word's minimal big-endian representation fits the RLP short-string case. -/
theorem nonce_bytes_le (nonce : UInt256) : (BE nonce.toNat).size ≤ 32 := by
  simpa [BE] using EvmYul.length_toBytesBigEndian_le (n := nonce.toNat) nonce.val.isLt

/-- The actual address serializer has precisely its typed 160-bit width. -/
theorem sender_bytes_size (sender : AccountAddress) : sender.toByteArray.size = 20 := by
  have hfit : sender.val < 256^20 := sender.isLt
  have hlen := congrArg List.length (EvmYul.toBeBytesFixed_eq_zeroPad sender.val 20 hfit)
  simp only [EvmYul.length_toBeBytesFixed, List.length_append, List.length_replicate] at hlen
  have hb : (BE sender.val).size ≤ 20 := by
    simpa [BE] using (show (EvmYul.toBytesBigEndian sender.val).length ≤ 20 by omega)
  unfold AccountAddress.toByteArray
  rw [ByteArray.size_append, ffi.ByteArray.size_zeroes]
  have hw : 20 < 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega
  have hn : (BE sender.val).size < 2 ^ System.Platform.numBits := by omega
  have h20 : (20 : BitVec System.Platform.numBits).toNat = 20 := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
  simp only [USize.toNat, BitVec.toNat_sub, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, h20]
  rw [show 2 ^ System.Platform.numBits - (BE sender.val).size + 20 =
      2 ^ System.Platform.numBits + (20 - (BE sender.val).size) by omega,
    Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem rlp_bytes_short {bytes : ByteArray} (hb : bytes.size ≤ 32) :
    ∃ encoded, RLP (.𝔹 bytes) = some encoded ∧ encoded.size ≤ 33 := by
  unfold RLP
  change ∃ encoded, (if bytes.size = 1 ∧ bytes.get! 0 < 128 then some bytes
    else if bytes.size < 56 then some ([⟨128 + bytes.size⟩].toByteArray ++ bytes)
    else if bytes.size < 2^64 then
      some ([⟨183 + (BE bytes.size).size⟩].toByteArray ++ BE bytes.size ++ bytes)
    else none) = some encoded ∧ encoded.size ≤ 33
  split
  · exact ⟨bytes, rfl, by omega⟩
  · split
    · refine ⟨_, rfl, ?_⟩
      simp only [ByteArray.size_append, List.size_toByteArray, List.length_cons, List.length_nil]
      omega
    · omega

private theorem rlp_pair_total {left right : ByteArray} (hl : left.size ≤ 32)
    (hr : right.size ≤ 32) : ∃ encoded, RLP (.𝕃 [.𝔹 left, .𝔹 right]) = some encoded := by
  obtain ⟨l, hel, hll⟩ := rlp_bytes_short hl
  obtain ⟨r, her, hrl⟩ := rlp_bytes_short hr
  rw [RLP.eq_2, R_l.eq_1]
  simp only [s, hel, her]
  have hb : (l ++ (r ++ ByteArray.empty)).size < 2^64 := by
    simp only [ByteArray.size_append, ByteArray.size_empty]
    omega
  split
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩

/-- No nonce-admission premise is required: even a full 256-bit nonce encodes. -/
theorem create_total (sender : AccountAddress) (nonce : UInt256) (init : ByteArray) :
    ∃ bytes, Lambda.L_A sender nonce none init = some bytes := by
  exact rlp_pair_total (by rw [sender_bytes_size]; omega) (nonce_bytes_le nonce)

/-- Syntactic Option totality for CREATE2, without asserting that arbitrary
salt/hash bytes have the protocol widths. -/
theorem create2_total (sender : AccountAddress) (nonce : UInt256)
    (salt init : ByteArray) : ∃ bytes, Lambda.L_A sender nonce (some salt) init = some bytes :=
  ⟨_,rfl⟩

theorem context_total (c : CreationSettlement.Context) : ∃ bytes, c.preimage = some bytes := by
  unfold CreationSettlement.Context.preimage
  cases c.salt with
  | none => exact create_total _ _ _
  | some salt => exact create2_total _ _ _ _

theorem lambdaArgs_total (a : LambdaArgs) : ∃ bytes, a.preimage = some bytes :=
  context_total (a.context 0)

/-- The actual selected CREATE/CREATE2 request, with all nonce updates and gas
charging retained, has a successfully encoded address preimage. -/
theorem creationArgs_total (kind : CreationGas.Variant) (cost : Nat) (pre : EVM.State)
    (value off len salt : UInt256) :
    ∃ bytes, (creationArgs kind cost pre value off len salt).preimage = some bytes :=
  lambdaArgs_total _

/-- The actual CREATE2 salt adapter is exactly the 32-byte word encoding. This
is separate from the opaque init hash, whose width is not needed above. -/
theorem create2_salt_width (salt : UInt256) :
    ∃ bytes, CreationGas.saltBytes .create2 salt = some bytes ∧ bytes.size = 32 :=
  ⟨salt.toByteArray,rfl,UInt256.size_toByteArray salt⟩

#print axioms context_total
#print axioms lambdaArgs_total
#print axioms creationArgs_total
#print axioms create2_salt_width
end Eip8282.Audit.Integrator.CreationPreimageTotal

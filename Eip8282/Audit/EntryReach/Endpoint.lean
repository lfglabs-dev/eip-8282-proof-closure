import Eip8282.Audit.EntryReach.Operands
import Eip8282.Audit.XiTransport

/-!
# ENDPOINT — concrete return bytes at reached endpoints

This slice turns the named bytes at an ENTRY-REACH `RETURN` into the model's
byte encoding where the endpoint is a fee getter.  It is observation-only:
the committed state and the drain-record encoding remain separate endpoint
obligations.
-/

namespace Eip8282.Audit.EntryReach.Endpoint

open EvmYul EvmYul.EVM
open Eip8282.Audit.XiTransport
open Eip8282.Audit.Model

/-- A getter's real `MSTORE 0 fee; RETURN 0 32` publishes the model's
32-byte big-endian fee word. -/
theorem getter_mstore_bytes (mem : ByteArray) (fee : UInt256) :
    bytes ((mstoreMem mem (UInt256.ofNat 0) fee).readWithPadding 0 32) =
      toBeBytes fee.toNat 32 := by
  unfold mstoreMem
  change bytes ((ByteArray.write fee.toByteArray 0 mem 0 32).readWithPadding 0 32) = _
  rw [ByteArray.readWithPadding_write_self_of_pad _ _ _ _ (by norm_num) (by norm_num)
    (EvmYul.UInt256.size_toByteArray fee) (by simp)]
  exact bytes_toByteArray fee

end Eip8282.Audit.EntryReach.Endpoint

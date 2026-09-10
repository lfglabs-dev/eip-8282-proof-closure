import Eip8282.Audit.Integrator.ReferenceTerminalDecode

/-! Decoder agreement also includes STOP and the checked runtime EOF fallback.
This remains restricted to actual sites of the two pinned protected images;
generic foreign-code decoder agreement is not asserted. -/
namespace Eip8282.Audit.Integrator.ReferenceAllDecode
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeSites
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private theorem roundtrip (u : UInt256) : UInt256.ofNat u.toNat = u := by
  cases u with | mk u =>
    apply congrArg UInt256.mk
    apply Fin.ext
    exact Nat.mod_eq_of_lt u.isLt

theorem decode_matches {kind : Kind} {pre : EVM.State}
    (hat : RuntimeExecutionScope.At (runtime kind) pre) :
    decodeAt pre = (ReferenceDecodeSites.referenceDecode
      (ReferenceDecodeSites.code (reference kind)) pre.pc.toNat).getD (.STOP,none) := by
  have hd : decodeAt pre = (decode pre.executionEnv.code (UInt256.ofNat pre.pc.toNat)).getD (.STOP,none) := by
    rw [roundtrip]
    rfl
  rw [hd,hat.1,code_eq]
  rcases site_or_eof hat with hsite | heof
  · rw [ReferenceDecodeSites.decode_eq hsite]
  · rw [heof]
    have hf := (runtime kind).eof
    change decode (runtime kind).code (UInt256.ofNat (runtime kind).code.size) = none at hf
    rw [code_eq] at hf
    rw [hf]
    cases kind <;> decide +kernel

#print axioms decode_matches
end Eip8282.Audit.Integrator.ReferenceAllDecode

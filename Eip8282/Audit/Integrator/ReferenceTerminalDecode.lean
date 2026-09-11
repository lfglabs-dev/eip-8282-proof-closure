import Eip8282.Audit.Integrator.ReferenceRuntimeSites
import Eip8282.Audit.Integrator.ReferenceDecodeShape

/-! Actual non-STOP instructions cannot be the pinned EOF default. This gives
terminal RETURN the same exact checked source-decoder binding as running sites,
without an impossible nonhalting-H premise. No execution or source agreement
is assumed beyond the actual pinned site invariant and actual decoded opcode. -/
namespace Eip8282.Audit.Integrator.ReferenceTerminalDecode
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeSites
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem roundtrip (u : UInt256) : UInt256.ofNat u.toNat = u := by
  cases u with | mk u =>
    apply congrArg UInt256.mk
    apply Fin.ext
    exact Nat.mod_eq_of_lt u.isLt

private theorem decode_at (pre : EVM.State) :
    decodeAt pre = (decode pre.executionEnv.code (UInt256.ofNat pre.pc.toNat)).getD (.STOP,none) := by
  rw [roundtrip]
  rfl

theorem nonstop_site {kind : Kind} {pre : EVM.State}
    (hat : RuntimeExecutionScope.At (runtime kind) pre)
    (hn : (decodeAt pre).1 ≠ .STOP) :
    pre.pc.toNat ∈ ReferenceDecodeSites.sites (reference kind) := by
  rcases site_or_eof hat with hp | he
  · exact hp
  · apply False.elim
    apply hn
    rw [decode_at,hat.1,code_eq,he]
    have hf := (runtime kind).eof
    change decode (runtime kind).code (UInt256.ofNat (runtime kind).code.size) = none at hf
    rw [code_eq] at hf
    rw [hf]
    rfl

theorem decode_matches {kind : Kind} {pre : EVM.State}
    (hat : RuntimeExecutionScope.At (runtime kind) pre)
    (hn : (decodeAt pre).1 ≠ .STOP) :
    decodeAt pre = (ReferenceDecodeSites.referenceDecode
      (ReferenceDecodeSites.code (reference kind)) pre.pc.toNat).getD (.STOP,none) := by
  rw [decode_at,hat.1,code_eq,ReferenceDecodeSites.decode_eq (nonstop_site hat hn)]

/-- The source decoder really succeeds; its fallback is not being equated. -/
theorem decode_some {kind : Kind} {pre : EVM.State}
    (hat : RuntimeExecutionScope.At (runtime kind) pre)
    (hn : (decodeAt pre).1 ≠ .STOP) :
    ReferenceDecodeSites.referenceDecode
      (ReferenceDecodeSites.code (reference kind)) pre.pc.toNat = some (decodeAt pre) := by
  have hm := decode_matches hat hn
  cases hd : ReferenceDecodeSites.referenceDecode
      (ReferenceDecodeSites.code (reference kind)) pre.pc.toNat with
  | none =>
    simp only [hd,Option.getD_none] at hm
    exact False.elim (hn (congrArg Prod.fst hm))
  | some instr =>
    simp only [hd,Option.getD_some] at hm
    exact congrArg some hm.symm

/-- RETURN's null immediate and successful source decode are both derived. -/
theorem return_decode {kind : Kind} {pre : EVM.State}
    (hat : RuntimeExecutionScope.At (runtime kind) pre)
    (hr : (decodeAt pre).1 = .RETURN) :
    ReferenceDecodeSites.referenceDecode
      (ReferenceDecodeSites.code (reference kind)) pre.pc.toNat = some (.RETURN,none) := by
  have hn : (decodeAt pre).1 ≠ .STOP := by rw [hr]; decide
  rw [decode_some hat hn,ReferenceDecodeShape.fixed pre .RETURN hr rfl]

#print axioms nonstop_site
#print axioms decode_matches
#print axioms decode_some
#print axioms return_decode
end Eip8282.Audit.Integrator.ReferenceTerminalDecode

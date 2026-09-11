import Eip8282.Audit.Integrator.ReferenceDecodeSites
import Eip8282.Audit.Integrator.RuntimeExecutionScope

/-! Bridge actual protected-runtime sites to the checked source decoder tables.
Site and natural-PC fit obligations are derived; no caller-supplied matched
instruction or no-wrap predicate is needed. Only the two pinned runtimes occur. -/
namespace Eip8282.Audit.Integrator.ReferenceRuntimeSites
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach Eip8282.Audit.SymExec
open Eip8282.Audit.Model (Kind)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

def runtime : Kind → RuntimeExecutionScope.Image
  | .deposit => RuntimeExecutionScope.deposit
  | .exit => RuntimeExecutionScope.exit

def reference : Kind → ReferenceDecodeSites.Image
  | .deposit => .deposit
  | .exit => .exit

theorem code_eq (kind : Kind) : (runtime kind).code = ReferenceDecodeSites.code (reference kind) := by
  cases kind <;> rfl

theorem sites_eq (kind : Kind) : (runtime kind).sites = ReferenceDecodeSites.sites (reference kind) := by
  cases kind <;> decide +kernel

private theorem roundtrip (u : UInt256) : UInt256.ofNat u.toNat = u := by
  cases u with | mk u =>
    apply congrArg UInt256.mk
    apply Fin.ext
    exact Nat.mod_eq_of_lt u.isLt

private theorem decode_at (pre : EVM.State) :
    decodeAt pre = (decode pre.executionEnv.code (UInt256.ofNat pre.pc.toNat)).getD (.STOP,none) := by
  rw [roundtrip]
  rfl

theorem site_or_eof {kind : Kind} {pre : EVM.State} (hat : RuntimeExecutionScope.At (runtime kind) pre) :
    pre.pc.toNat ∈ ReferenceDecodeSites.sites (reference kind) ∨
      pre.pc.toNat = (ReferenceDecodeSites.code (reference kind)).size := by
  simpa only [sites_eq,code_eq] using hat.2

/-- EOF is the pinned STOP default and cannot occur on a nonhalting edge. -/
theorem nonhalting_site {kind : Kind} {pre post : EVM.State}
    (hat : RuntimeExecutionScope.At (runtime kind) pre)
    (hh : H post.toMachineState (decodeAt pre).1 = none) :
    pre.pc.toNat ∈ ReferenceDecodeSites.sites (reference kind) := by
  rcases site_or_eof hat with hp | he
  · exact hp
  · have hd : (decodeAt pre).1 = .STOP := by
      rw [decode_at,hat.1,code_eq,he]
      have hf := (runtime kind).eof
      change decode (runtime kind).code (UInt256.ofNat (runtime kind).code.size) = none at hf
      rw [code_eq] at hf
      rw [hf]
      rfl
    simp [hd,H] at hh

/-- Equality is applied at the actual state site, not at an assumed matching PC. -/
theorem decode_matches {kind : Kind} {pre post : EVM.State}
    (hat : RuntimeExecutionScope.At (runtime kind) pre)
    (hh : H post.toMachineState (decodeAt pre).1 = none) :
    decodeAt pre = (ReferenceDecodeSites.referenceDecode
      (ReferenceDecodeSites.code (reference kind)) pre.pc.toNat).getD (.STOP,none) := by
  rw [decode_at,hat.1,code_eq,ReferenceDecodeSites.decode_eq (nonhalting_site hat hh)]

theorem pc_fit {kind : Kind} {pre : EVM.State} (hat : RuntimeExecutionScope.At (runtime kind) pre) :
    pre.pc.toNat+1+argOnNBytesOfInstr (decodeAt pre).1 < UInt256.size := by
  have hc : (ReferenceDecodeSites.code (reference kind)).size ≤ 1024 := by cases kind <;> decide
  have hp : pre.pc.toNat ≤ 1024 := by
    rcases site_or_eof hat with hp | he
    · have := (ReferenceDecodeSites.site_facts hp).1; omega
    · omega
  have ho := RuntimeExecutionScope.opcode_allowed hat
  have hw : argOnNBytesOfInstr (decodeAt pre).1 ≤ 32 := by
    have h : ∀ op ∈ RuntimeOpcodeScope.allowedOps, argOnNBytesOfInstr op ≤ 32 := by decide +kernel
    exact h _ ho
  have hsize : 1057 < UInt256.size := by decide +kernel
  omega

theorem jumps_eq (kind : Kind) :
    D_J (runtime kind).code ⟨0⟩ =
      ((ReferenceDecodeSites.referenceJumps (reference kind)).map UInt256.ofNat).toArray := by
  rw [code_eq]
  exact ReferenceDecodeSites.jumps_eq _

/-- An actually admitted word destination is a natural reference destination. -/
theorem jump_member {kind : Kind} {dest : UInt256} (hd : dest ∈ D_J (runtime kind).code ⟨0⟩) :
    dest.toNat ∈ ReferenceDecodeSites.referenceJumps (reference kind) := by
  rw [jumps_eq] at hd
  simp only [List.mem_toArray,List.mem_map] at hd
  obtain ⟨pc,hp,he⟩ := hd
  have hsite : pc ∈ ReferenceDecodeSites.sites (reference kind) := (List.mem_filter.mp hp).1
  have hsize : (ReferenceDecodeSites.code (reference kind)).size < UInt256.size := by cases kind <;> decide
  have hfit := (ReferenceDecodeSites.site_facts hsite).1.trans hsize
  rw [← he,toNat_ofNat_lit pc hfit]
  exact hp

#print axioms sites_eq
#print axioms nonhalting_site
#print axioms decode_matches
#print axioms pc_fit
#print axioms jump_member
end Eip8282.Audit.Integrator.ReferenceRuntimeSites

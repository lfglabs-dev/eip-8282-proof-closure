import Eip8282.Audit.Integrator.ReferenceCheckedDispatch

/-! Reverse binding from decoded protected opcodes to actual source handler
selection. Only the fixed byte universe is finite; execution length is not.
Consumer: forward acceptance of the paid SYSTEM trace and its RETURN. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSourceSelection
open EvmYul EvmYul.EVM ReferenceRuntimeView ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem parsed (h : Handler) (tag : UInt8) (decoded : parseInstr tag = some (opcode h)) :
    select tag = some h := by
  have table : ∀ t : Fin 256, parseInstr (UInt8.ofNat t.val) = some (opcode h) →
      select (UInt8.ofNat t.val) = some h := by
    cases h with
    | binary b => cases b <;> decide +kernel
    | environment e => cases e <;> decide +kernel
    | stackControl s => cases s <;> decide +kernel
    | memoryStore b => cases b <;> decide +kernel
    | copyLog c => cases c <;> decide +kernel
    | load => decide +kernel
    | store => decide +kernel
    | terminal t => cases t <;> decide +kernel
  have check := table ⟨tag.toNat,tag.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at check
  exact check decoded

theorem read {bytes : ByteArray} {pc : Nat} {h : Handler} {arg : Option (UInt256 × Nat)}
    (decoded : ReferenceDecodeSites.referenceDecode bytes pc = some (opcode h,arg)) :
    ReferenceCheckedDispatch.read bytes pc = .handler h := by
  cases ht : bytes[pc]? with
  | none => simp [ReferenceDecodeSites.referenceDecode,ht] at decoded
  | some tag =>
    cases hp : parseInstr tag with
    | none => simp [ReferenceDecodeSites.referenceDecode,ht,hp] at decoded
    | some op =>
      have eq : some (op,if ReferenceDecodeSites.pushWidth tag = 0 then none else
          some (uInt256OfByteArray (ReferenceDecodeSites.paddedImmediate bytes pc (ReferenceDecodeSites.pushWidth tag)),ReferenceDecodeSites.pushWidth tag)) =
          some (opcode h,arg) := by simpa [ReferenceDecodeSites.referenceDecode,ht,hp] using decoded
      have opEq := congrArg (fun x => x.map Prod.fst) eq
      simp only [Option.map_some,Option.some.injEq] at opEq
      rw [opEq] at hp
      have selected := parsed h tag hp
      have valid := (select_facts tag selected).1
      simp only [ReferenceCheckedDispatch.read,ht,valid,if_true,selected]

#print axioms parsed
#print axioms read
end Eip8282.Audit.Integrator.ReferenceCheckedSourceSelection

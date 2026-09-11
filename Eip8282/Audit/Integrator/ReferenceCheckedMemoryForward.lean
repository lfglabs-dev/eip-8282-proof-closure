import Eip8282.Audit.Integrator.ReferenceCheckedPureForward

/-! Forward checked memory stores for the paid SYSTEM trace consumer. The
price is that of the same computed post-memory; alignment derives the literal
source expansion charge, without a new memory budget or execution hypothesis. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedMemoryForward
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceCheckedMemoryStore ReferenceMemoryExpansionSource
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

theorem store {kind : Kind} {parent : ReferenceStorageView.Parent} {byte : Bool}
    {v : View} {meter final : Meter} {off value : UInt256} {rest : List UInt256}
    (shape : v.stack = off::value::rest) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (paid : runFull [.ordinary (3+(ReferenceMemoryCapacity.cost (words (memoryAction v off (data byte value) rest))-
      ReferenceMemoryCapacity.cost (words v)))] meter = some final) :
    ReferenceCheckedMemoryStore.run byte v meter = .ok (memoryAction v off (data byte value) rest,final) := by
  have dataSize : (data byte value).size = length byte := by
    cases byte <;> simp [data,length,UInt256.size_toByteArray] <;> rfl
  have act : ReferenceRuntimeAction.Action kind parent (opcode byte,none) v
      (memoryAction v off (data byte value) rest) := by
    cases byte with
    | false => exact .base (.word shape)
    | true =>
      have byteEq : UInt8.ofNat (value.toNat%256) = UInt8.ofNat value.toNat := UInt8.ofNat_mod_size
      simpa [opcode,data,byteEq] using
        (ReferenceRuntimeAction.Action.base (ReferenceSystemAction.Action.byte shape) :
          ReferenceRuntimeAction.Action kind parent (.MSTORE8,none) v
            (memoryAction v off ⟨#[UInt8.ofNat value.toNat]⟩ rest))
  have computed := (ReferenceActionMemoryBounds.computed act aligned).2
  have span : ReferenceActionMemoryBounds.span v (opcode byte) = (off.toNat,length byte) := by
    cases byte <;> simp [ReferenceActionMemoryBounds.span,opcode,length,shape]
  rw [span] at computed
  dsimp only at computed
  have expansion := ReferenceMemoryExpansionSource.aligned (words v) off.toNat (length byte)
  rw [←aligned] at expansion
  have capacity : v.memory.size+(calculate v.memory.size off.toNat (length byte)).bytes =
      32*MachineState.M (words v) off.toNat (length byte) := by
    have lower := (ReferenceMemoryCapacity.expansion_bounds (words v) off.toNat (length byte)).1
    change v.memory.size = 32*words v at aligned
    omega
  rw [computed,←expansion.2] at paid
  obtain ⟨charged,hc,rfl⟩ := ReferenceCheckedPureForward.ordinary_paid paid
  simp only [ReferenceCheckedMemoryStore.run,shape,ReferenceSourceStackAdmission.pop,hc,capacity,
    memoryAction,dataSize]

#print axioms store
end Eip8282.Audit.Integrator.ReferenceCheckedMemoryForward

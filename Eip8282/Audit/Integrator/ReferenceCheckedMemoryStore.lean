import Eip8282.Audit.Integrator.ReferenceCheckedBinaryStep
import Eip8282.Audit.Integrator.ReferenceMemoryExpansionSource
import Eip8282.Audit.Integrator.ReferenceActionMemoryBounds

/-! Checked MSTORE/MSTORE8: two ordered pops, literal single-span memory charge,
then eager extension and slice write, then PC increment. Amsterdam EL0cc100eb,
vm/instructions/memory.py31-93, full body in the49-file source archive.
The existing audited splice implements extension followed by source memory_write.
Actual source frame/buffer extraction and outer failure restoration are separate.
Raw expansion uses source Uint/Nat operations; alignment is needed only by the
successful replay theorem and is derived along initialized handler histories. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedMemoryStore
open EvmYul EvmYul.EVM
open Eip8282.Audit.Model (Kind)
open ReferenceRuntimeView ReferenceMeterRollback ReferenceMeterBoundary
open ReferenceCheckedBinaryStep (Failure)
open ReferenceMemoryExpansionSource
open ReferenceActionMemoryBounds (Aligned)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def length (byte : Bool) : Nat := if byte then 1 else 32

def opcode (byte : Bool) : Operation .EVM := if byte then .MSTORE8 else .MSTORE

def data (byte : Bool) (value : UInt256) : ByteArray :=
  if byte then ⟨#[UInt8.ofNat (value.toNat%256)]⟩ else value.toByteArray

def run (byte : Bool) (v : View) (meter : Meter) :
    Except (Failure × View × Meter) (View × Meter) :=
  match ReferenceSourceStackAdmission.pop v.stack with
  | .error e => .error (.stack e,v,meter)
  | .ok (first,off) =>
    match ReferenceSourceStackAdmission.pop first with
    | .error e => .error (.stack e,{v with stack := first},meter)
    | .ok (rest,value) =>
      let expansion := calculate v.memory.size off.toNat (length byte)
      match ReferenceStorageGas.chargeExecution (core meter) (3+expansion.cost) with
      | none => .error (.outOfGas,{v with stack := rest},meter)
      | some charged => .ok ({v with stack := rest,pc := v.pc+1, memory := ReferenceMemoryOperations.splice v.memory off.toNat (data byte value) (v.memory.size+expansion.bytes)},update meter charged)

private theorem shape {byte : Bool} {v next : View} {meter final : Meter}
    (actual : run byte v meter = .ok (next,final)) :
    ∃ off value rest charged,
      v.stack = off::value::rest ∧
      ReferenceStorageGas.chargeExecution (core meter)
        (3+(calculate v.memory.size off.toNat (length byte)).cost) = some charged ∧
      next = {v with stack := rest,pc := v.pc+1, memory := ReferenceMemoryOperations.splice v.memory off.toNat (data byte value) (v.memory.size+(calculate v.memory.size off.toNat (length byte)).bytes)} ∧
      final = update meter charged := by
  unfold run at actual
  cases hs : v.stack with
  | nil => simp only [hs,ReferenceSourceStackAdmission.pop] at actual; contradiction
  | cons off first =>
    simp only [hs,ReferenceSourceStackAdmission.pop] at actual
    cases first with
    | nil => contradiction
    | cons value rest =>
      dsimp only [ReferenceSourceStackAdmission.pop] at actual
      split at actual
      · contradiction
      · rename_i charged hc
        cases actual
        exact ⟨off,value,rest,charged,rfl,hc,rfl,rfl⟩

/-- Exact same raw expansion pays the price computed from its actual result.
No output memory capacity, action, desired stack or paid event is supplied. -/
theorem success {byte : Bool} {v next : View} {meter final : Meter}
    (kind : Kind) (parent : ReferenceStorageView.Parent) (warm : ReferenceSourceReadings.Warm)
    (initial : v.stack.length ≤ 1024) (aligned : Aligned v)
    (actual : run byte v meter = .ok (next,final)) :
    ReferenceRuntimeAction.Action kind parent (opcode byte,none) v next ∧
    ReferenceRuntimeReadings.Price parent v warm next (opcode byte)
      (.ordinary (3+(ReferenceMemoryCapacity.cost (words next)-ReferenceMemoryCapacity.cost (words v)))) ∧
    runFull [.ordinary (3+(ReferenceMemoryCapacity.cost (words next)-ReferenceMemoryCapacity.cost (words v)))]
      meter = some final ∧ next.stack.length ≤ 1024 := by
  obtain ⟨off,value,rest,charged,hs,hc,rfl,rfl⟩ := shape actual
  have expansionFacts := ReferenceMemoryExpansionSource.aligned (words v) off.toNat (length byte)
  rw [←aligned] at expansionFacts
  have lower := (ReferenceMemoryCapacity.expansion_bounds (words v) off.toNat (length byte)).1
  have capacity : v.memory.size+(calculate v.memory.size off.toNat (length byte)).bytes =
      32*MachineState.M (words v) off.toNat (length byte) := by
    change v.memory.size = 32*words v at aligned
    omega
  rw [capacity]
  have action : ReferenceRuntimeAction.Action kind parent (opcode byte,none) v
      {v with stack := rest,pc := v.pc+1, memory := ReferenceMemoryOperations.splice v.memory off.toNat (data byte value) (32*MachineState.M (words v) off.toNat (length byte))} := by
    cases byte with
    | false =>
      have step : ReferenceRuntimeAction.Action kind parent (.MSTORE,none) v (memoryAction v off value.toByteArray rest) := .base (.word hs)
      simpa only [opcode,length,data,Bool.false_eq_true,if_false,memoryAction,UInt256.size_toByteArray] using step
    | true =>
      have byteEq : UInt8.ofNat (value.toNat%256) = UInt8.ofNat value.toNat := UInt8.ofNat_mod_size
      have sizeByte : (⟨#[UInt8.ofNat value.toNat]⟩ : ByteArray).size = 1 := rfl
      simpa [opcode,length,data,memoryAction,byteEq,sizeByte] using (ReferenceRuntimeAction.Action.base (ReferenceSystemAction.Action.byte hs) :
        ReferenceRuntimeAction.Action kind parent (.MSTORE8,none) v (memoryAction v off ⟨#[UInt8.ofNat value.toNat]⟩ rest))
  have computed := (ReferenceActionMemoryBounds.computed action aligned).2
  have span : ReferenceActionMemoryBounds.span v (opcode byte) = (off.toNat,length byte) := by
    cases byte <;> simp [ReferenceActionMemoryBounds.span,opcode,length,hs]
  rw [span] at computed
  dsimp only at computed
  refine ⟨action,?_,?_,?_⟩
  · cases byte <;> simp [ReferenceRuntimeReadings.Price,ReferenceCopyLogGas.ordinaryCost,
      ReferenceOrdinaryGas.ordinaryCost,opcode,computed]
  · have amount : 3+(ReferenceMemoryCapacity.cost (words
        {v with stack := rest,pc := v.pc+1, memory := ReferenceMemoryOperations.splice v.memory off.toNat (data byte value) (32*MachineState.M (words v) off.toNat (length byte))})-ReferenceMemoryCapacity.cost (words v)) =
        3+(calculate v.memory.size off.toNat (length byte)).cost := by
      rw [computed,expansionFacts.2]
    rw [amount]
    simp only [runFull,ReferenceMeterPath.run,ReferenceMeterPath.pay,hc,Option.bind_some,Option.map_some]
  · change rest.length ≤ 1024
    rw [hs] at initial
    simp only [List.length_cons] at initial
    omega

#print axioms success
end Eip8282.Audit.Integrator.ReferenceCheckedMemoryStore

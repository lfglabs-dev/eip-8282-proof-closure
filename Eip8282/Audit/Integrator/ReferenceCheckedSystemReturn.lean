import Eip8282.Audit.Integrator.ReferenceCheckedPureForward
import Eip8282.Audit.Integrator.ReferenceCheckedSourceSelection
import Eip8282.Audit.Integrator.ReferenceSystemSourcePayment
import Eip8282.Audit.Integrator.ReferenceCheckedEvaluator

/-! Accept the very RETURN paid by Whole, preserving its actual storage/logs,
full meter and exact extended output. Consumer: successful SYSTEM evaluation. -/
namespace Eip8282.Audit.Integrator.ReferenceCheckedSystemReturn
open EvmYul EvmYul.EVM ReferenceRuntimeView ReferenceSourceReadings
open ReferenceMeterRollback ReferenceMeterBoundary
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

def result (v : View) (off len : UInt256) (rest : List UInt256) (final : Meter) : ReferenceCheckedTerminalStep.End :=
  ⟨.returned,{v with stack := rest,memory := ReferenceReturnView.returnMemory v off len},final,
    (ReferenceReturnView.returnMemory v off len).extract off.toNat (off.toNat+len.toNat)⟩

theorem accepted {v : View} {off len : UInt256} {rest : List UInt256} {meter final : Meter}
    (shape : v.stack = off::len::rest) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (paid : runFull [.ordinary (ReferenceSystemSourcePayment.terminalCost v off len)] meter = some final)
    (previousOutput : ByteArray) :
    ReferenceCheckedTerminalStep.run .returned v meter previousOutput = .ok (result v off len rest final) := by
  have price := (ReferenceMemoryExpansionSource.aligned (words v) off.toNat len.toNat).2
  rw [←aligned] at price
  have amount : ReferenceSystemSourcePayment.terminalCost v off len =
      (ReferenceMemoryExpansionSource.calculate v.memory.size off.toNat len.toNat).cost := by
    unfold ReferenceSystemSourcePayment.terminalCost
    simp only [ReferenceReturnView.returnMemory,ReferenceMemoryOperations.extend,ReferenceMemoryView.buffer_size]
    simpa using price.symm
  rw [amount] at paid
  obtain ⟨charged,hc,rfl⟩ := ReferenceCheckedPureForward.ordinary_paid paid
  have capacity := ReferenceCheckedCopyLogStep.expanded_capacity v off len aligned
  simp only [ReferenceCheckedTerminalStep.run,show ReferenceCheckedTerminalStep.Halt.returned ≠ .stop by decide,
    if_false,shape,ReferenceSourceStackAdmission.pop,hc,ReferenceCheckedCopyLogStep.expanded,capacity,result,
    ReferenceReturnView.returnMemory]

theorem evaluated {v : View} {off len : UInt256} {rest : List UInt256} {meter final : Meter}
    {destinations : List Nat} {parent : ReferenceStorageView.Parent} {warm : Warm}
    (decoded : ReferenceDecodeSites.referenceDecode v.env.code v.pc = some (.RETURN,none))
    (shape : v.stack = off::len::rest) (aligned : ReferenceActionMemoryBounds.Aligned v)
    (paid : runFull [.ordinary (ReferenceSystemSourcePayment.terminalCost v off len)] meter = some final)
    (budget : Nat) (output : ByteArray) :
    ReferenceCheckedEvaluator.eval destinations true parent output (budget+1) v warm meter =
      some ([],.terminal (result v off len rest final)) := by
  have selected := ReferenceCheckedSourceSelection.read (h := .terminal .returned) decoded
  have actual := accepted shape aligned paid output
  simp only [ReferenceCheckedEvaluator.eval,ReferenceCheckedDispatch.run,selected,
    ReferenceCheckedDispatch.runHandler,actual]

#print axioms accepted
#print axioms evaluated
end Eip8282.Audit.Integrator.ReferenceCheckedSystemReturn

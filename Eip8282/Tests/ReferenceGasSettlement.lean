import Eip8282.Audit.Integrator.ReferenceOutcomeGas

/-! Injected original/current storage divergences, not fresh transactions or
canonical histories. They show why the transaction settlement theorem must
produce a fresh journal and follow linked writes. A local successful SSTORE
alone does not justify outer Uint subtractions or U256 refund conversion. -/
namespace Eip8282.Tests.ReferenceGasSettlement
open EvmYul EvmYul.EVM Eip8282.Audit.Integrator
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private def parent (original : UInt256) : ReferenceStorageView.Parent := ⟨fun _ _ => none,fun _ _ => original⟩
private def tx (current : UInt256) : ReferenceStorageView.Tx := ⟨fun _ _ => some current,∅,∅⟩
private def frame (current new : UInt256) : View :=
  ⟨{(default : ExecutionEnv .EVM) with code := ⟨#[0x55]⟩,perm := true},0,[⟨0⟩,new],.empty,tx current,[]⟩
private noncomputable def observations (original current new : UInt256) : Option (Nat × Int × Int) :=
  match ReferenceCheckedStorageStep.store true (parent original) (frame current new) ∅ (ReferenceChildMeter.init 3000 0) with
  | .error _ => none
  | .ok (_,_,meter) => some (meter.execution+meter.reservoir,meter.refund,netUsed 0 meter)

private theorem zero_original_credit : observations ⟨0⟩ ⟨1⟩ ⟨0⟩ = some (98820,10000,-97920) := by
  simp [observations,ReferenceCheckedStorageStep.store,ReferenceCheckedStorageStep.storeAfterPop,
    ReferenceSourceStackAdmission.pop,frame,parent,tx,ReferenceCheckedStorageStep.access,
    ReferenceStorageView.original,ReferenceStorageView.current,ReferenceStorageView.parentRead,
    ReferenceStorageGas.classify,ReferenceStorageGas.creditState,ReferenceStorageGas.chargeExecution,
    ReferenceStorageGas.chargeState,ReferenceChildMeter.init,ReferenceMeterBoundary.core,ReferenceMeterBoundary.update,netUsed,UInt256.size]

private theorem nonzero_original_debt : observations ⟨1⟩ ⟨0⟩ ⟨2⟩ = some (900,-11616,0) := by
  simp [observations,ReferenceCheckedStorageStep.store,ReferenceCheckedStorageStep.storeAfterPop,
    ReferenceSourceStackAdmission.pop,frame,parent,tx,ReferenceCheckedStorageStep.access,
    ReferenceStorageView.original,ReferenceStorageView.current,ReferenceStorageView.parentRead,
    ReferenceStorageGas.classify,ReferenceStorageGas.creditState,ReferenceStorageGas.chargeExecution,
    ReferenceStorageGas.chargeState,ReferenceChildMeter.init,ReferenceMeterBoundary.core,ReferenceMeterBoundary.update,netUsed,UInt256.size]

theorem unlinked_credit_exceeds_grant :
    observations ⟨0⟩ ⟨1⟩ ⟨0⟩ = some (98820,10000,-97920) ∧ ¬ (98820 ≤ 3000) := ⟨zero_original_credit,by decide⟩

theorem unlinked_negative_refund_rejected :
    observations ⟨1⟩ ⟨0⟩ ⟨2⟩ = some (900,-11616,0) ∧ ReferenceRefundCounter.checked (-11616) = none :=
  ⟨nonzero_original_debt,by simp [ReferenceRefundCounter.checked]⟩

#print axioms unlinked_credit_exceeds_grant
#print axioms unlinked_negative_refund_rejected
end Eip8282.Tests.ReferenceGasSettlement

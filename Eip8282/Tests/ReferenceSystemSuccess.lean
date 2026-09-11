import Eip8282.Audit.Integrator.ReferenceCheckedSystemDrainTotal

/-! Injected local opcode/resource mutations for the SYSTEM success bridge.
These distinguish nominal from ordered storage payment, a paid prefix from
paid RETURN, and a supplied event from the actual decoded operation. They are
not canonical histories; existing Deposit/Exit byte mutants remain retained. -/
namespace Eip8282.Tests.ReferenceSystemSuccess
open EvmYul EvmYul.EVM Eip8282.Audit.Integrator
open ReferenceRuntimeView ReferenceMeterRollback ReferenceMeterBoundary ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private def parent : ReferenceStorageView.Parent := ⟨fun _ _ => none,fun _ _ => ⟨0⟩⟩
private def frame (tag : UInt8) (stack : List UInt256) : View :=
  ⟨{(default : ExecutionEnv .EVM) with code := ⟨#[tag]⟩,perm := true},0,stack,.empty,
    ProtocolSystemDispatchExtraction.freshTx,[]⟩

/-- Merely paying a cold no-op SSTORE's2100 cost misses the2301 sentry. -/
theorem sentry_not_nominal_payment :
    runFull [.ordinary 2100] (ReferenceChildMeter.init 2300 0) = some (ReferenceChildMeter.init 200 0) ∧
    runFull [.store false ⟨0⟩ ⟨0⟩ ⟨0⟩] (ReferenceChildMeter.init 2300 0) = none ∧
    ReferenceCheckedStorageStep.store true parent (frame 0x55 [⟨0⟩,⟨0⟩]) ∅ (ReferenceChildMeter.init 2300 0) =
      .error (.checked .outOfGas,frame 0x55 [],∅,ReferenceChildMeter.init 2300 0) := by
  simp [runFull,ReferenceMeterPath.run,ReferenceMeterPath.pay,ReferenceStorageGas.storageCharge,
    ReferenceStorageGas.classify,ReferenceStorageGas.chargeExecution,core,update,ReferenceChildMeter.init,
    ReferenceCheckedStorageStep.store,ReferenceCheckedStorageStep.storeAfterPop,ReferenceCheckedStorageStep.access,
    frame,ReferenceSourceStackAdmission.pop]

/-- Prefix payment alone does not pay the final memory expansion. -/
theorem return_payment_required :
    ReferenceCheckedTerminalStep.run .returned (frame 0xf3 [⟨32⟩,⟨1⟩]) (ReferenceChildMeter.init 5 0) ByteArray.empty =
      .error (.outOfGas,frame 0xf3 [],ReferenceChildMeter.init 5 0,ByteArray.empty) := by
  exact ReferenceCheckedTerminalStep.out_of_gas .returned _ _ _ ⟨32⟩ ⟨1⟩ []
    (by decide) rfl (by decide +kernel)

/-- A three-unit supplied event cannot pay the decoded MUL, which costs five. -/
theorem decoded_payment_required :
    runFull [.ordinary 3] (ReferenceChildMeter.init 3 0) = some (ReferenceChildMeter.init 0 0) ∧
    ReferenceCheckedDispatch.run [] true parent (frame 0x02 [⟨7⟩,⟨9⟩]) ∅ (ReferenceChildMeter.init 3 0) ByteArray.empty =
      .failed (.binary .outOfGas) (frame 0x02 []) ∅ (ReferenceChildMeter.init 3 0) ByteArray.empty := by
  refine ⟨by rfl,?_⟩
  have selected : read (frame 0x02 [⟨7⟩,⟨9⟩]).env.code (frame 0x02 [⟨7⟩,⟨9⟩]).pc = .handler (.binary .mul) := by decide +kernel
  have failure := ReferenceCheckedBinaryStep.out_of_gas .mul (frame 0x02 [⟨7⟩,⟨9⟩])
    (ReferenceChildMeter.init 3 0) ⟨7⟩ ⟨9⟩ [] rfl (by decide)
  simp only [ReferenceCheckedDispatch.run,selected,runHandler,failure]
  rfl

#print axioms sentry_not_nominal_payment
#print axioms return_payment_required
#print axioms decoded_payment_required
end Eip8282.Tests.ReferenceSystemSuccess

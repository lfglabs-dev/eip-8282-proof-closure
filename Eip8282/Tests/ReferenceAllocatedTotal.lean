import Eip8282.Audit.Integrator.ReferenceAllocatedTotal

/-! Finite injected evaluator fixtures. A valid foreign opcode remains
unsupported outside the pinned-code domain. Zero execution gas still produces
a completed exceptional result, distinct from computational fuel exhaustion.
These are not initialized/canonical histories. -/
namespace Eip8282.Tests.ReferenceAllocatedTotal
open EvmYul EvmYul.EVM Eip8282.Audit.Integrator
open ReferenceRuntimeView ReferenceSourceReadings ReferenceMeterRollback ReferenceCheckedDispatch
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private def accountsParent : ReferenceAccountLookup.Parent Unit := ⟨fun _ => none,fun _ => none⟩
private def accounts : ReferenceAccountLookup.Tx Unit := ⟨fun _ => none,∅⟩
private def storageParent : ReferenceStorageView.Parent := ⟨fun _ _ => none,fun _ _ => ⟨0⟩⟩
private def storage : ReferenceStorageView.Tx := ⟨fun _ _ => none,∅,∅⟩
private def view (bytes : ByteArray) : View :=
  ⟨{(default : ExecutionEnv .EVM) with code := bytes},0,[],.empty,storage,[]⟩
private def meter : Meter := ReferenceChildMeter.init 0 0

/-- TIMESTAMP is a valid source opcode but is outside the 44 protected handlers. -/
theorem foreign_not_silently_stopped :
    ReferenceCheckedAccountEvaluator.eval accountsParent [] storageParent .empty 1 accounts (view ⟨#[0x42]⟩) ∅ meter =
      some (([],.unsupported 0x42 (view ⟨#[0x42]⟩) ∅ meter .empty),accounts) := by
  have fetched : read (view ⟨#[0x42]⟩).env.code (view ⟨#[0x42]⟩).pc = .unsupported 0x42 := by decide +kernel
  simp only [ReferenceCheckedAccountEvaluator.eval,ReferenceCheckedAccountDispatch.run,ReferenceCheckedDispatch.run,
    fetched,ReferenceCheckedAccountDispatch.assertionReached,Bool.false_eq_true,ite_false]

/-- The pinned initial CALLER fails exceptionally at zero gas, using one unit
of computational fuel; completion cannot be strengthened to EVM success. -/
theorem zero_gas_is_completed_failure (kind : ReachableCalls.Contract) :
    ReferenceCheckedAccountEvaluator.eval accountsParent [] storageParent .empty 1 accounts (view (ReachableCalls.runtime kind)) ∅ meter =
      some (([],.failed (.environment (.checked .outOfGas)) (view (ReachableCalls.runtime kind)) ∅ meter .empty),accounts) := by
  have fetched : read (view (ReachableCalls.runtime kind)).env.code (view (ReachableCalls.runtime kind)).pc = .handler (.environment .caller) := by
    cases kind <;> decide +kernel
  simp only [ReferenceCheckedAccountEvaluator.eval,ReferenceCheckedAccountDispatch.run,ReferenceCheckedDispatch.run,
    fetched,runHandler,ReferenceCheckedEnvironmentStep.run,ReferenceCheckedEnvironmentStep.finish,
    ReferenceMeterBoundary.core,meter,ReferenceChildMeter.init,ReferenceStorageGas.chargeExecution,
    Nat.reduceLeDiff,ite_false,ReferenceCheckedAccountDispatch.assertionReached,Bool.false_eq_true]

#print axioms foreign_not_silently_stopped
#print axioms zero_gas_is_completed_failure
end Eip8282.Tests.ReferenceAllocatedTotal

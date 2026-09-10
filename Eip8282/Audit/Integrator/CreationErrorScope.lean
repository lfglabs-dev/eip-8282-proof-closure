import Eip8282.Audit.Integrator.CreationPreimageTotal

/-!
After actual address-encoding totality, Lambda's only returned exception is
OutOfFuel. Ordinary init exceptions are returned failed creations. This is an
error classification, not evaluator-fuel adequacy or a rollback assertion for
CREATE's catch of a Lambda error.
-/
namespace Eip8282.Audit.Integrator.CreationErrorScope
open EvmYul EvmYul.EVM
open NestedEvents
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

theorem context_error (c : CreationSettlement.Context) {err : ExecutionException}
    (h : c.result = .error err) : err = .OutOfFuel := by
  obtain ⟨bytes,hp⟩ := CreationPreimageTotal.context_total c
  rw [CreationSettlement.result_eq_settle c hp] at h
  cases he : c.execution (CreationSettlement.address bytes) with
  | error childError =>
      simp only [CreationSettlement.Context.settle, he] at h
      split at h
      · cases h; rfl
      · cases h
  | ok result =>
      cases result with
      | revert gas out =>
          simp only [CreationSettlement.Context.settle, he] at h
          cases h
      | success state out =>
          obtain ⟨created,world,gas,substate⟩ := state
          simp only [CreationSettlement.Context.settle, he] at h
          cases h

/-- The same classification for the actual raw Lambda request, including its
zero-fuel branch. No success or per-child admission premise is needed. -/
theorem lambda_error {fuel : Nat} {a : LambdaArgs} {err : ExecutionException}
    (h : (Request.lambda fuel a).eval = .error err) : err = .OutOfFuel := by
  cases fuel with
  | zero => cases h; rfl
  | succ fuel => exact context_error (a.context fuel) h

#print axioms context_error
#print axioms lambda_error
end Eip8282.Audit.Integrator.CreationErrorScope

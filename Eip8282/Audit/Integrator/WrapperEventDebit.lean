import Eip8282.Audit.Integrator.RecursiveEventDebit
import Eip8282.Audit.Integrator.FrameEvents

/-!
# All-outcome residual transport through actual execution wrappers

Ξ preserves the X accounting residual. Code Θ and Λ settlement can only
reduce that residual, even on failures. These wrapper edges preserve an
independently proved child-event charge; they do not extract a call tree.
-/
namespace Eip8282.Audit.Integrator.WrapperEventDebit
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open RecursiveEventDebit
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

abbrev XiResult := Except ExecutionException
  (ExecutionResult (Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate))

def xiResidual : XiResult → Nat
  | .error _ => 0 | .ok result => (ReturnedGas.xiGas result).toNat

/-- Literal fresh machine used by Ξ, with the original-world snapshot retained. -/
def entry (created : Std.TreeSet AccountAddress compare) (genesis : BlockHeader)
    (blocks : ProcessedBlocks) (world original : AccountMap .EVM) (gas : UInt256)
    (substate : Substate) (env : ExecutionEnv .EVM) : EVM.State :=
  { (default : EVM.State) with
    accountMap := world, σ₀ := original, executionEnv := env, substate := substate,
    createdAccounts := created, gasAvailable := gas, blocks := blocks, genesisBlockHeader := genesis }

/-- Exact preservation for every X outcome, including both kinds of failure. -/
theorem xi_residual (fuel : Nat) (created : Std.TreeSet AccountAddress compare)
    (genesis : BlockHeader) (blocks : ProcessedBlocks) (world original : AccountMap .EVM)
    (gas : UInt256) (substate : Substate) (env : ExecutionEnv .EVM) :
    xiResidual (Ξ (fuel+1) created genesis blocks world original gas substate env) =
      FrameEvents.residual (X fuel (D_J env.code ⟨0⟩)
        (entry created genesis blocks world original gas substate env)) := by
  unfold Ξ
  change xiResidual (do
    let result ← X fuel (D_J env.code ⟨0⟩) (entry created genesis blocks world original gas substate env)
    match result with
    | .success state out => pure (.success (state.createdAccounts,state.accountMap,state.gasAvailable,state.substate) out)
    | .revert remaining out => pure (.revert remaining out)) = _
  cases he : X fuel (D_J env.code ⟨0⟩) (entry created genesis blocks world original gas substate env) with
  | error err => rfl
  | ok result => cases result <;> rfl

/-- Θ's exact rollback and empty-world fallback cannot increase the code
execution's residual, including propagated OutOfFuel. -/
theorem theta_residual (c : MessageCall.Context) :
    thetaResidual c.result ≤ xiResidual c.execution := by
  rw [MessageCall.result_eq_settle]
  cases he : c.execution with
  | error err =>
      simp only [MessageCall.Context.settle, he]
      split <;> exact Nat.le_refl _
  | ok result =>
      cases result with
      | revert gas out => exact Nat.le_refl _
      | success result out => obtain ⟨created,world,gas,substate⟩ := result; exact Nat.le_refl _

/-- For a successfully encoded address, every actual Λ settlement retains or
reduces the residual of the SAME selected init execution. -/
theorem lambda_residual (c : CreationSettlement.Context) {preimage : ByteArray}
    (hp : c.preimage = some preimage) :
    lambdaResidual c.result ≤ xiResidual (c.execution (CreationSettlement.address preimage)) := by
  rw [CreationSettlement.result_eq_settle c hp]
  cases he : c.execution (CreationSettlement.address preimage) with
  | error err =>
      simp only [CreationSettlement.Context.settle, he]
      split <;> exact Nat.le_refl _
  | ok result =>
      cases result with
      | revert gas out => exact Nat.le_refl _
      | success result code =>
          obtain ⟨created,world,gas,substate⟩ := result
          change (UInt256.ofNat (if c.depositFailure (CreationSettlement.address preimage) gas code
            then 0 else gas.toNat-GasConstants.Gcodedeposit*code.size)).toNat ≤ gas.toNat
          split
          · exact Nat.zero_le _
          · exact (Nat.mod_le _ _).trans (Nat.sub_le _ _)

/-- Failed address encoding does not execute init code. No init charge may be
invented for this branch. This statement concerns its actual residual only. -/
theorem lambda_no_preimage (c : CreationSettlement.Context) (hp : c.preimage = none) :
    lambdaResidual c.result = 0 := by
  unfold CreationSettlement.Context.result Lambda
  change Lambda.L_A c.sender ((c.world.get? c.sender |>.option ⟨0⟩ (·.nonce))-⟨1⟩) c.salt c.init = none at hp
  dsimp only
  rw [hp]
  rfl

/-- Wrapper induction edge, with the child charge bound stated explicitly. -/
theorem theta_charge (c : MessageCall.Context) (charge : Nat)
    (h : xiResidual c.execution + charge ≤ c.gas.toNat) :
    thetaResidual c.result + charge ≤ c.gas.toNat :=
  (Nat.add_le_add_right (theta_residual c) charge).trans h

theorem lambda_charge (c : CreationSettlement.Context) {preimage : ByteArray}
    (hp : c.preimage = some preimage) (charge : Nat)
    (h : xiResidual (c.execution (CreationSettlement.address preimage)) + charge ≤ c.gas.toNat) :
    lambdaResidual c.result + charge ≤ c.gas.toNat :=
  (Nat.add_le_add_right (lambda_residual c hp) charge).trans h

#print axioms xi_residual
#print axioms theta_residual
#print axioms lambda_residual
#print axioms lambda_no_preimage
#print axioms theta_charge
#print axioms lambda_charge
end Eip8282.Audit.Integrator.WrapperEventDebit

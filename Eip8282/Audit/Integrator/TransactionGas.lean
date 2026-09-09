import Eip8282.Audit.Integrator.ReturnedGas
import Eip8282.Audit.Integrator.RefundAccounting

/-!
# Actual transaction gas with the execution bound discharged

This follows the pinned Υ function, including its real provisional Θ/Lambda
selection. It does not assert protocol transaction admission or supply a count
of nested append events. Their aggregate charge remains a separate obligation.
-/
namespace Eip8282.Audit.Integrator.TransactionGas
open EvmYul EvmYul.EVM
open RefundAccounting
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

theorem provisional_remaining (c : Context) {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool}
    (h : c.provisional = .ok (world,gas,substate,success)) :
    gas.toNat ≤ c.entryGas.toNat := by
  unfold Context.provisional at h
  split at h
  · split at h
    · rename_i he
      have hb := ReturnedGas.lambda_remaining c.fuel he
      cases h
      exact hb
    · cases h
  · split at h
    · rename_i he
      have hb := ReturnedGas.theta_remaining c.fuel he
      cases h
      exact hb
    · cases h

/-- The actual transaction result has the capped natural refund formula.
No returned-gas inequality is supplied by the caller of this theorem. -/
theorem result_debit (c : Context) {world : AccountMap .EVM}
    {substate : Substate} {success : Bool} {used : UInt256}
    (h : c.result = .ok (world,substate,success,used)) :
    ∃ provisionalWorld remaining,
      c.provisional = .ok (provisionalWorld,remaining,substate,success) ∧
      remaining.toNat ≤ c.entryGas.toNat ∧
      used.toNat = (c.transaction.base.gasLimit.toNat - remaining.toNat) -
        min ((c.transaction.base.gasLimit.toNat - remaining.toNat)/5) substate.refundBalance.toNat ∧
      used.toNat ≤ c.transaction.base.gasLimit.toNat := by
  obtain ⟨pw,rem,hp,hg⟩ := result_inversion c world substate success used h
  have hr := provisional_remaining c hp
  have hl := hr.trans (entryGas_le_limit c)
  have hn := net_toNat c.transaction.base.gasLimit rem substate.refundBalance hl
  refine ⟨pw,rem,hp,hr,?_,?_⟩
  · rw [hg]
    exact hn
  · rw [hg,hn]
    exact (Nat.sub_le _ _).trans (Nat.sub_le _ _)

/-- The actual execution discharges remaining≤entry. The independently counted
aggregate append charge is still explicit, rather than manufactured here. -/
theorem count_le_used (c : Context) (count : Nat)
    (provisionalWorld world : AccountMap .EVM) (remaining used : UInt256)
    (substate finalSubstate : Substate) (success finalSuccess : Bool)
    (hp : c.provisional = .ok (provisionalWorld,remaining,substate,success))
    (hr : c.result = .ok (world,finalSubstate,finalSuccess,used))
    (hcharged : 919*count ≤ c.transaction.base.gasLimit.toNat - remaining.toNat) :
    count ≤ used.toNat :=
  count_le_transaction_gas_of_entry c count provisionalWorld world remaining used substate
    finalSubstate success finalSuccess hp hr (provisional_remaining c hp) hcharged

#print axioms provisional_remaining
#print axioms result_debit
#print axioms count_le_used
end Eip8282.Audit.Integrator.TransactionGas

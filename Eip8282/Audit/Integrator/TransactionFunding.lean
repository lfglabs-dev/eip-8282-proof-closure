import Eip8282.Audit.Integrator.ExecutionFunding
import Eip8282.Audit.Integrator.FinalizationFunding
import Eip8282.Audit.Integrator.Topics.Transaction3

/-!
# Funding at the actual transaction boundary

Admission is stated over independent pre-balances and actual fee inputs. It is
not claimed to have been extracted from consensus validation. Execution and
settlement use the pinned Υ function and its real checkpoint and child call.
-/
namespace Eip8282.Audit.Integrator.TransactionFunding
open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach
open RefundAccounting TransferFunding
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def upfront (c : Context) : Nat :=
  c.transaction.base.gasLimit.toNat * c.effectivePrice.toNat + calcBlobFee c.header c.transaction

/-- Sufficient natural prepayment and a valid nonce/priority relationship.
These are input conditions, not assumed child or transaction postconditions. -/
structure Admission (c : Context) (account : Account .EVM) : Prop where
  sender : c.world.get? c.sender = some account
  funded : upfront c + c.transaction.base.value.toNat ≤ account.balance.toNat
  nonce : account.nonce.toNat < 2^64-1
  priority : c.priorityFee.toNat ≤ c.effectivePrice.toNat

def debited (c : Context) (account : Account .EVM) : Account .EVM :=
  { account with
    balance := account.balance - c.transaction.base.gasLimit * c.effectivePrice -
      UInt256.ofNat (calcBlobFee c.header c.transaction),
    nonce := account.nonce + ⟨1⟩ }

theorem checkpoint_eq (c : Context) {account : Account .EVM} (ha : Admission c account) :
    c.checkpoint = c.world.insert c.sender (debited c account) := by
  unfold Context.checkpoint debited
  rw [ha.sender]
  rfl

theorem debited_balance (c : Context) {account : Account .EVM} (ha : Admission c account) :
    (debited c account).balance.toNat + upfront c = account.balance.toNat := by
  have hf := ha.funded
  unfold upfront at hf
  have hmulfit : c.transaction.base.gasLimit.toNat * c.effectivePrice.toNat < UInt256.size :=
    (by omega : c.transaction.base.gasLimit.toNat * c.effectivePrice.toNat ≤ account.balance.toNat).trans_lt
      (toNat_lt_size account.balance)
  have hmul : (c.transaction.base.gasLimit*c.effectivePrice).toNat =
      c.transaction.base.gasLimit.toNat*c.effectivePrice.toNat := Nat.mod_eq_of_lt hmulfit
  have hblobfit : calcBlobFee c.header c.transaction < UInt256.size :=
    (by omega : calcBlobFee c.header c.transaction ≤ account.balance.toNat).trans_lt
      (toNat_lt_size account.balance)
  have hblob := toNat_ofNat_lit (calcBlobFee c.header c.transaction) hblobfit
  have hs : (account.balance - c.transaction.base.gasLimit*c.effectivePrice).toNat =
      account.balance.toNat - c.transaction.base.gasLimit.toNat*c.effectivePrice.toNat := by
    rw [toNat_sub_of_le _ _ (by rw [hmul]; omega), hmul]
  change ((account.balance - c.transaction.base.gasLimit*c.effectivePrice) -
    UInt256.ofNat (calcBlobFee c.header c.transaction)).toNat + upfront c = _
  rw [toNat_sub_of_le _ _ (by rw [hs,hblob]; omega), hs,hblob]
  unfold upfront
  omega

theorem checkpoint_debit (c : Context) {account : Account .EVM} (ha : Admission c account) :
    worldFunds c.checkpoint + upfront c = worldFunds c.world := by
  have hf := funds_insert c.world c.sender (debited c account)
  have hb := debited_balance c ha
  simp only [worldBalance, ha.sender, Option.map_some, Option.getD_some] at hf
  rw [checkpoint_eq c ha]
  omega

theorem checkpoint_funded (c : Context) {account : Account .EVM} (ha : Admission c account) :
    c.transaction.base.value.toNat ≤ worldBalance c.checkpoint c.sender := by
  have hb := debited_balance c ha
  have hf := ha.funded
  unfold worldBalance
  rw [checkpoint_eq c ha]
  have hl : (c.world.insert c.sender (debited c account)).get? c.sender = some (debited c account) :=
    Std.TreeMap.getElem?_insert_self
  rw [hl]
  simp only [Option.map_some, Option.getD_some]
  omega

theorem checkpoint_nonce (c : Context) {account : Account .EVM} (ha : Admission c account) :
    ExecutionFunding.NonzeroNonce c.checkpoint c.sender := by
  rw [checkpoint_eq c ha]
  refine ⟨debited c account, Std.TreeMap.getElem?_insert_self, ?_⟩
  have hn := ha.nonce
  have hb : account.nonce.toNat+1 < UInt256.size := by unfold UInt256.size; omega
  intro he
  have he := congrArg UInt256.toNat he
  change (account.nonce.toNat+1) % UInt256.size = 0 at he
  rw [Nat.mod_eq_of_lt hb] at he
  omega

theorem provisional_funds (c : Context) {account : Account .EVM} (ha : Admission c account) {world : AccountMap .EVM}
    {gas : UInt256} {substate : Substate} {success : Bool}
    (h : c.provisional = .ok (world,gas,substate,success)) :
    worldFunds world ≤ worldFunds c.checkpoint := by
  unfold Context.provisional at h
  split at h
  · split at h
    · rename_i he
      have hb := ExecutionFunding.lambda_funds c.fuel (checkpoint_funded c ha) (checkpoint_nonce c ha) he
      cases h
      exact hb
    · cases h
  · split at h
    · rename_i he
      have hb := ExecutionFunding.theta_funds c.fuel (checkpoint_funded c ha) he
      cases h
      exact hb
    · cases h

def settledWorld (c : Context) (world : AccountMap .EVM) (remaining : UInt256)
    (substate : Substate) : AccountMap .EVM :=
  let refunded := world.increaseBalance .EVM c.sender
    (returnedGas c.transaction.base.gasLimit remaining substate.refundBalance * c.effectivePrice)
  let beneficiaryFee := netGas c.transaction.base.gasLimit remaining substate.refundBalance * c.priorityFee
  let paid := if beneficiaryFee != ⟨0⟩ then
    refunded.increaseBalance .EVM c.header.beneficiary beneficiaryFee else refunded
  FinalizationFunding.cleanup paid substate

theorem payout_le (c : Context) (remaining : UInt256) (substate : Substate)
    (hpriority : c.priorityFee.toNat ≤ c.effectivePrice.toNat)
    (hremaining : remaining.toNat ≤ c.transaction.base.gasLimit.toNat) :
    (returnedGas c.transaction.base.gasLimit remaining substate.refundBalance * c.effectivePrice).toNat +
      (netGas c.transaction.base.gasLimit remaining substate.refundBalance * c.priorityFee).toNat ≤
    c.transaction.base.gasLimit.toNat*c.effectivePrice.toNat := by
  let returned := returnedGas c.transaction.base.gasLimit remaining substate.refundBalance
  let used := netGas c.transaction.base.gasLimit remaining substate.refundBalance
  have hr : returned.toNat ≤ c.transaction.base.gasLimit.toNat :=
    (returned_toNat _ _ _ hremaining).2
  have hn : used.toNat = c.transaction.base.gasLimit.toNat-returned.toNat :=
    toNat_sub_of_le _ _ hr
  have hs : returned.toNat + used.toNat = c.transaction.base.gasLimit.toNat := by omega
  have hrefund : (returned*c.effectivePrice).toNat ≤ returned.toNat*c.effectivePrice.toNat := Nat.mod_le _ _
  have hbeneficiary : (used*c.priorityFee).toNat ≤ used.toNat*c.effectivePrice.toNat :=
    (Nat.mod_le _ _).trans (Nat.mul_le_mul_left used.toNat hpriority)
  change (returned*c.effectivePrice).toNat + (used*c.priorityFee).toNat ≤ _
  calc
    _ ≤ returned.toNat*c.effectivePrice.toNat + used.toNat*c.effectivePrice.toNat := Nat.add_le_add hrefund hbeneficiary
    _ = _ := by rw [← Nat.add_mul,hs]

theorem settled_funds_le (c : Context) (world : AccountMap .EVM) (remaining : UInt256) (substate : Substate)
    (hpriority : c.priorityFee.toNat ≤ c.effectivePrice.toNat)
    (hremaining : remaining.toNat ≤ c.transaction.base.gasLimit.toNat) :
    worldFunds (settledWorld c world remaining substate) ≤
      worldFunds world + c.transaction.base.gasLimit.toNat*c.effectivePrice.toNat := by
  let refundAmount := returnedGas c.transaction.base.gasLimit remaining substate.refundBalance*c.effectivePrice
  let refunded := world.increaseBalance .EVM c.sender refundAmount
  let beneficiaryFee := netGas c.transaction.base.gasLimit remaining substate.refundBalance*c.priorityFee
  let paid := if beneficiaryFee != ⟨0⟩ then
    refunded.increaseBalance .EVM c.header.beneficiary beneficiaryFee else refunded
  have hs : worldFunds refunded ≤ worldFunds world+refundAmount.toNat := FinalizationFunding.credit_le _ _ _
  have hb : worldFunds paid ≤ worldFunds refunded+beneficiaryFee.toNat := by
    unfold paid
    split
    · exact FinalizationFunding.credit_le _ _ _
    · exact Nat.le_add_right _ _
  have hc : worldFunds (settledWorld c world remaining substate) ≤ worldFunds paid :=
    FinalizationFunding.cleanup_le paid substate
  have hp : refundAmount.toNat+beneficiaryFee.toNat ≤ c.transaction.base.gasLimit.toNat*c.effectivePrice.toNat :=
    payout_le c remaining substate hpriority hremaining
  omega

/-- Exact Υ, including the actual final world and cleanup, not only gas. -/
theorem result_equation (c : Context) :
    c.result = (do
      let (world,remaining,substate,success) ← c.provisional
      pure (settledWorld c world remaining substate,substate,success,
        netGas c.transaction.base.gasLimit remaining substate.refundBalance)) := by
  unfold Context.result Υ Context.provisional Context.entryGas Context.entrySubstate
    Context.checkpoint settledWorld Context.effectivePrice Context.priorityFee
    FinalizationFunding.cleanup FinalizationFunding.clearTransient netGas returnedGas refund
  dsimp only
  unfold Υ.match_1 Context.priorityFee.match_1
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  cases hr : c.transaction.base.recipient <;> dsimp only
  all_goals
    split <;> rename_i h <;> simp_all

/-- Complete actual transaction conservation under the independent admission
conditions. No child or final-world funding bound is a premise. -/
theorem result_funds (c : Context) {account : Account .EVM} (ha : Admission c account)
    {world : AccountMap .EVM} {substate : Substate} {success : Bool} {used : UInt256}
    (h : c.result = .ok (world,substate,success,used)) : worldFunds world ≤ worldFunds c.world := by
  rw [result_equation] at h
  cases hp : c.provisional with
  | error err => simp only [hp, Bind.bind, Except.bind] at h; cases h
  | ok result =>
    obtain ⟨pw,remaining,ss,z⟩ := result
    have hf := provisional_funds c ha hp
    have hg := (TransactionGas.provisional_remaining c hp).trans (entryGas_le_limit c)
    have hs := settled_funds_le c pw remaining ss ha.priority hg
    have hd := checkpoint_debit c ha
    simp only [hp, Bind.bind, Except.bind, pure, Except.pure] at h
    cases h
    unfold upfront at hd
    omega

#print axioms debited_balance
#print axioms checkpoint_debit
#print axioms provisional_funds
#print axioms payout_le
#print axioms result_equation
#print axioms result_funds

end Eip8282.Audit.Integrator.TransactionFunding

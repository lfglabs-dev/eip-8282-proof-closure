import Eip8282.Audit.Integrator.ActualAppendGas

/-!
# Actual transaction refund arithmetic

The word expression below is exactly Υ's remaining-gas refund and reported
net gas. Its link to Υ is proved by unfolding the pinned function and retaining
its actual provisional Θ/Lambda result. Transaction validation and assignment
of distinct append events to gross gas remain explicit external obligations.
-/
namespace Eip8282.Audit.Integrator.RefundAccounting

open EvmYul EvmYul.EVM
open Eip8282.Audit.EntryReach

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def refund (limit remaining balance : UInt256) : UInt256 :=
  min ((limit-remaining) / ⟨5⟩) balance

def returnedGas (limit remaining balance : UInt256) : UInt256 :=
  remaining + refund limit remaining balance

def netGas (limit remaining balance : UInt256) : UInt256 :=
  limit - returnedGas limit remaining balance

private theorem min_toNat (a b : UInt256) : (min a b).toNat = min a.toNat b.toNat := by
  change (if a ≤ b then a else b).toNat = _
  by_cases h : a.toNat ≤ b.toNat
  · have hw : a ≤ b := h
    rw [if_pos hw, Nat.min_eq_left h]
  · have hw : ¬ a ≤ b := h
    rw [if_neg hw, Nat.min_eq_right (by omega)]

/-- Only the real remaining-gas bound is required. The refund balance may be
any word; the actual min imposes its cap. -/
theorem refund_toNat (limit remaining balance : UInt256)
    (h : remaining.toNat ≤ limit.toNat) :
    (refund limit remaining balance).toNat =
      min ((limit.toNat-remaining.toNat)/5) balance.toNat := by
  unfold refund
  rw [min_toNat, toNat_div, toNat_sub_of_le _ _ h]
  rfl

theorem refund_le (limit remaining balance : UInt256)
    (h : remaining.toNat ≤ limit.toNat) :
    (refund limit remaining balance).toNat ≤ (limit.toNat-remaining.toNat)/5 := by
  rw [refund_toNat _ _ _ h]
  exact Nat.min_le_left _ _

/-- The returned-gas addition cannot wrap: capped refund plus remaining gas
is at most the original gas limit, which itself is an EVM word. -/
theorem returned_toNat (limit remaining balance : UInt256)
    (h : remaining.toNat ≤ limit.toNat) :
    (returnedGas limit remaining balance).toNat =
      remaining.toNat + (refund limit remaining balance).toNat ∧
    (returnedGas limit remaining balance).toNat ≤ limit.toNat := by
  have hr := refund_le limit remaining balance h
  have hd := Nat.div_le_self (limit.toNat-remaining.toNat) 5
  have hs : remaining.toNat + (refund limit remaining balance).toNat ≤ limit.toNat := by omega
  have he : (returnedGas limit remaining balance).toNat =
      remaining.toNat + (refund limit remaining balance).toNat :=
    toNat_add_of_lt _ _ (hs.trans_lt (toNat_lt_size limit))
  exact ⟨he, he ▸ hs⟩

/-- Exact natural net gas, with the subtraction and addition fit proved from
remaining≤limit, not assumed as desired final-gas equations. -/
theorem net_toNat (limit remaining balance : UInt256)
    (h : remaining.toNat ≤ limit.toNat) :
    (netGas limit remaining balance).toNat =
      (limit.toNat-remaining.toNat) - min ((limit.toNat-remaining.toNat)/5) balance.toNat := by
  obtain ⟨he, hb⟩ := returned_toNat limit remaining balance h
  unfold netGas
  rw [toNat_sub_of_le _ _ hb, he, refund_toNat _ _ _ h]
  omega

/-- The 1/5 refund cap leaves enough net gas to charge one unit for every
append whose independently established gross cost is at least 919. -/
theorem count_le_net (count : Nat) (limit remaining balance : UInt256)
    (h : remaining.toNat ≤ limit.toNat)
    (hc : 919*count ≤ limit.toNat-remaining.toNat) :
    count ≤ (netGas limit remaining balance).toNat := by
  rw [net_toNat _ _ _ h]
  have hr := Nat.min_le_left ((limit.toNat-remaining.toNat)/5) balance.toNat
  omega

/-- Inputs of the pinned transaction function, without asserting validation. -/
structure Context where
  fuel : Nat
  world : AccountMap .EVM
  baseFee : Nat
  header : BlockHeader
  genesis : BlockHeader
  blocks : ProcessedBlocks
  transaction : Transaction
  sender : AccountAddress

def Context.result (c : Context) :=
  Υ c.fuel c.world c.baseFee c.header c.genesis c.blocks c.transaction c.sender

def Context.priorityFee (c : Context) : UInt256 :=
  match c.transaction with
  | .legacy t | .access t => t.gasPrice - .ofNat c.baseFee
  | .dynamic t | .blob t => min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat c.baseFee)

def Context.effectivePrice (c : Context) : UInt256 :=
  match c.transaction with
  | .legacy t | .access t => t.gasPrice
  | .dynamic _ | .blob _ => c.priorityFee + .ofNat c.baseFee

def Context.checkpoint (c : Context) : AccountMap .EVM :=
  let account := (c.world.get? c.sender).get!
  c.world.insert c.sender { account with
    balance := account.balance - c.transaction.base.gasLimit * c.effectivePrice -
      .ofNat (calcBlobFee c.header c.transaction), nonce := account.nonce + ⟨1⟩ }

def Context.entrySubstate (c : Context) : Substate :=
  let accessList := c.transaction.getAccessList
  let keys : List (AccountAddress × UInt256) := do
    let ⟨Eₐ, Eₛ⟩ ← accessList
    let eₛ ← Eₛ.toList
    pure (Eₐ, eₛ)
  let accessed := A0.accessedAccounts.insert c.sender |>.insert c.header.beneficiary
    |>.union (Std.TreeSet.ofList (accessList.map Prod.fst) compare)
  let accessed := match c.transaction.base.recipient with
    | some target => accessed.insert target
    | none => accessed
  { A0 with
    accessedAccounts := accessed
    accessedStorageKeys := Std.TreeSet.ofList keys Substate.storageKeysCmp }

def Context.entryGas (c : Context) : UInt256 :=
  .ofNat (c.transaction.base.gasLimit.toNat - intrinsicGas c.transaction)

/-- The actual provisional execution selected by Υ, including creation and
precompile selection, failure status, remaining gas, and interpreter errors. -/
def Context.provisional (c : Context) :
    Except EVM.Exception (AccountMap .EVM × UInt256 × Substate × Bool) :=
  match c.transaction.base.recipient with
  | none =>
      match Lambda c.fuel c.transaction.blobVersionedHashes .empty c.genesis c.blocks
        c.checkpoint c.checkpoint c.entrySubstate c.sender c.sender c.entryGas c.effectivePrice
        c.transaction.base.value c.transaction.base.data ⟨0⟩ none c.header true with
      | .ok (_, _, world, gas, substate, success, _) => .ok (world, gas, substate, success)
      | .error err => .error (.ExecutionException err)
  | some target =>
      match Θ c.fuel c.transaction.blobVersionedHashes .empty c.genesis c.blocks
        c.checkpoint c.checkpoint c.entrySubstate c.sender c.sender target
        (toExecute .EVM c.checkpoint target) c.entryGas c.effectivePrice
        c.transaction.base.value c.transaction.base.value c.transaction.base.data 0 c.header true with
      | .ok (_, world, gas, substate, success, _) => .ok (world, gas, substate, success)
      | .error err => .error (.ExecutionException err)

/-- Exact Υ observation after its real execution and finalization. World
cleanup is not discarded from Υ; this projection observes its gas/substate/status. -/
theorem result_observation (c : Context) :
    c.result.map (fun r => (r.2.1, r.2.2.1, r.2.2.2)) =
      c.provisional.map (fun r => (r.2.2.1, r.2.2.2,
        netGas c.transaction.base.gasLimit r.2.1 r.2.2.1.refundBalance)) := by
  unfold Context.result Υ Context.provisional Context.entryGas Context.entrySubstate
    Context.checkpoint Context.effectivePrice Context.priorityFee netGas returnedGas refund
  dsimp only
  unfold Υ.match_1 Context.priorityFee.match_1
  simp only [Except.map, Bind.bind, Except.bind, pure, Except.pure]
  cases hr : c.transaction.base.recipient <;> dsimp only
  all_goals
    split <;> rename_i h <;> split at h <;> simp_all
  all_goals subst_vars; rfl

/-- Inversion of the real transaction result, including status false. No
agreement with an assumed final world or assumed final gas is a premise. -/
theorem result_inversion (c : Context) (world : AccountMap .EVM)
    (substate : Substate) (success : Bool) (used : UInt256)
    (hr : c.result = .ok (world, substate, success, used)) :
    ∃ provisionalWorld remaining,
      c.provisional = .ok (provisionalWorld, remaining, substate, success) ∧
      used = netGas c.transaction.base.gasLimit remaining substate.refundBalance := by
  have ho := result_observation c
  rw [hr] at ho
  cases hp : c.provisional with
  | error err => simp [hp, Except.map] at ho
  | ok value =>
    obtain ⟨pw, remaining, a, z⟩ := value
    simp only [hp, Except.map, Except.ok.injEq, Prod.mk.injEq] at ho
    obtain ⟨ha, hz, hg⟩ := ho
    subst a; subst z
    exact ⟨pw, remaining, rfl, hg⟩

/-- The entry gas cast itself fits, even without asserting intrinsic-gas
validation. Validation still matters for interpreting an actual transaction. -/
theorem entryGas_toNat (c : Context) :
    c.entryGas.toNat = c.transaction.base.gasLimit.toNat - intrinsicGas c.transaction := by
  exact toNat_ofNat_lit _
    ((Nat.sub_le _ _).trans_lt (toNat_lt_size c.transaction.base.gasLimit))

theorem entryGas_le_limit (c : Context) :
    c.entryGas.toNat ≤ c.transaction.base.gasLimit.toNat := by
  rw [entryGas_toNat]
  exact Nat.sub_le _ _

/-- Actual Υ settlement converts an independently accounted gross append
charge to a bound by reported net gas. The remaining-gas bound is attached to
the actual provisional Θ/Lambda execution, not to a stipulated final state.
The theorem does not assign nested append events to distinct gross charges. -/
theorem count_le_transaction_gas (c : Context) (count : Nat)
    (provisionalWorld world : AccountMap .EVM) (remaining used : UInt256)
    (substate finalSubstate : Substate) (success finalSuccess : Bool)
    (hp : c.provisional = .ok (provisionalWorld, remaining, substate, success))
    (hr : c.result = .ok (world, finalSubstate, finalSuccess, used))
    (hremaining : remaining.toNat ≤ c.transaction.base.gasLimit.toNat)
    (hcharged : 919*count ≤ c.transaction.base.gasLimit.toNat - remaining.toNat) :
    count ≤ used.toNat := by
  obtain ⟨pw, rem, hx, hg⟩ := result_inversion c world finalSubstate finalSuccess used hr
  rw [hp] at hx
  have he := Except.ok.inj hx
  have hm : remaining = rem := congrArg (fun r => r.2.1) he
  have ha : substate = finalSubstate := congrArg (fun r => r.2.2.1) he
  subst rem; subst finalSubstate
  rw [hg]
  exact count_le_net count _ _ _ hremaining hcharged

/-- A bound by actual execution-entry gas is sufficient for the previous
remaining-gas premise; intrinsic gas needs no wrap assumption here. -/
theorem count_le_transaction_gas_of_entry (c : Context) (count : Nat)
    (provisionalWorld world : AccountMap .EVM) (remaining used : UInt256)
    (substate finalSubstate : Substate) (success finalSuccess : Bool)
    (hp : c.provisional = .ok (provisionalWorld, remaining, substate, success))
    (hr : c.result = .ok (world, finalSubstate, finalSuccess, used))
    (hremaining : remaining.toNat ≤ c.entryGas.toNat)
    (hcharged : 919*count ≤ c.transaction.base.gasLimit.toNat - remaining.toNat) :
    count ≤ used.toNat :=
  count_le_transaction_gas c count provisionalWorld world remaining used substate
    finalSubstate success finalSuccess hp hr (hremaining.trans (entryGas_le_limit c)) hcharged

#print axioms refund_toNat
#print axioms returned_toNat
#print axioms net_toNat
#print axioms count_le_net
#print axioms result_observation
#print axioms result_inversion
#print axioms entryGas_toNat
#print axioms count_le_transaction_gas
#print axioms count_le_transaction_gas_of_entry

end Eip8282.Audit.Integrator.RefundAccounting

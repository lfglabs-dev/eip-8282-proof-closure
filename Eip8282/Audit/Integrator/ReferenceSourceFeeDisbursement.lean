import Eip8282.Audit.Integrator.ReferenceSourceFeeCredit
import Eip8282.Audit.Integrator.ReferenceTransactionGas

/-! Pinned fork.py997-1006: calculate refund and priority, then convert/credit
payer, then convert/credit beneficiary. Errors retain completed reads/credits.
Zero payments are not skipped. Equal payer/beneficiary addresses are supported.
The budget theorem is consumed by same-frame finalization, with its budget
derived from the prepayment/history producer. No post-balance premise. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceFeeDisbursement
open EvmYul ReferenceSourceValueTransfer ReferenceSourceFeeCredit
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

inductive Error where
  | priorityUnderflow | refundAmountOverflow | refundCreditOverflow
  | tipAmountOverflow | tipCreditOverflow

noncomputable def run {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (payer beneficiary : AccountAddress)
    (price base : Nat) (gas : ReferenceTransactionGas.Settlement) : Except Error Unit × Tx Hash :=
  let refundAmount := gas.gasLeft * price
  if base ≤ price then
    let tipAmount := gas.gasUsed * (price-base)
    if refundAmount < UInt256.size then
      let refunded := credit emptyHash parent tx payer (UInt256.ofNat refundAmount)
      match refunded.1 with
      | .error _ => (.error .refundCreditOverflow,refunded.2)
      | .ok _ =>
        if tipAmount < UInt256.size then
          let tipped := credit emptyHash parent refunded.2 beneficiary (UInt256.ofNat tipAmount)
          match tipped.1 with
          | .error _ => (.error .tipCreditOverflow,tipped.2)
          | .ok _ => (.ok (),tipped.2)
        else (.error .tipAmountOverflow,refunded.2)
    else (.error .refundAmountOverflow,tx)
  else (.error .priorityUnderflow,tx)

theorem funded {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (payer beneficiary : AccountAddress)
    (price base budget : Nat) (gas : ReferenceTransactionGas.Settlement)
    (baseFits : base ≤ price)
    (balances : ∀ a, (account emptyHash parent tx a).balance.toNat ≤ budget)
    (funds : budget + gas.gasLeft*price + gas.gasUsed*(price-base) < UInt256.size) :
    (run emptyHash parent tx payer beneficiary price base gas).1 = .ok () ∧
    ∀ a, (account emptyHash parent (run emptyHash parent tx payer beneficiary price base gas).2 a).balance.toNat =
      (account emptyHash parent tx a).balance.toNat +
        (if a = payer then gas.gasLeft*price else 0) +
        (if a = beneficiary then gas.gasUsed*(price-base) else 0) := by
  have refundFit : gas.gasLeft*price < UInt256.size := by omega
  have tipFit : gas.gasUsed*(price-base) < UInt256.size := by omega
  have refundNat : (UInt256.ofNat (gas.gasLeft*price)).toNat = gas.gasLeft*price := Nat.mod_eq_of_lt refundFit
  have tipNat : (UInt256.ofNat (gas.gasUsed*(price-base))).toNat = gas.gasUsed*(price-base) := Nat.mod_eq_of_lt tipFit
  have first := successful emptyHash parent tx payer (UInt256.ofNat (gas.gasLeft*price)) (by rw [refundNat]; have h := balances payer; omega)
  have second := successful emptyHash parent (credit emptyHash parent tx payer (UInt256.ofNat (gas.gasLeft*price))).2 beneficiary
    (UInt256.ofNat (gas.gasUsed*(price-base))) (by
      rw [first.2 beneficiary,refundNat,tipNat]
      have h := balances beneficiary
      split <;> omega)
  unfold run
  dsimp only
  rw [if_pos baseFits,if_pos refundFit,first.1]
  dsimp only
  rw [if_pos tipFit,second.1]
  refine ⟨rfl,?_⟩
  intro a
  rw [second.2 a,first.2 a,refundNat,tipNat]

/-- Protected code storage survives zero-credit cleanup as well as all partial
errors. This property is available even outside the funded-success domain. -/
theorem protected_storage {Hash : Type} [DecidableEq Hash] (emptyHash : Hash)
    (parent : Parent Hash) (tx : Tx Hash) (payer beneficiary address : AccountAddress)
    (price base : Nat) (gas : ReferenceTransactionGas.Settlement)
    (nonempty : hashAt emptyHash parent tx address ≠ emptyHash)
    (storageParent : ReferenceStorageView.Parent) (slot : ByteArray) :
    ReferenceStorageView.current storageParent (run emptyHash parent tx payer beneficiary price base gas).2.storage address slot =
      ReferenceStorageView.current storageParent tx.storage address slot := by
  unfold run
  dsimp only
  split
  · split
    · split
      · exact ReferenceSourceFeeCredit.protected_storage emptyHash parent tx payer address _ nonempty storageParent slot
      · split
        · have next : hashAt emptyHash parent (credit emptyHash parent tx payer (UInt256.ofNat (gas.gasLeft*price))).2 address ≠ emptyHash := by rwa [ReferenceSourceFeeCredit.hash]
          split <;> rw [ReferenceSourceFeeCredit.protected_storage emptyHash parent _ beneficiary address _ next storageParent slot]
          all_goals exact ReferenceSourceFeeCredit.protected_storage emptyHash parent tx payer address _ nonempty storageParent slot
        · exact ReferenceSourceFeeCredit.protected_storage emptyHash parent tx payer address _ nonempty storageParent slot
    · rfl
  · rfl

#print axioms funded
#print axioms protected_storage
end Eip8282.Audit.Integrator.ReferenceSourceFeeDisbursement

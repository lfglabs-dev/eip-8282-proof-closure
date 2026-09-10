import Eip8282.Audit.Integrator.ReferenceTransactionSettlement

/-! Source fee subtraction and the exact refund/tip/burn partition. Source gas
settlement supplies the same gas-used/left pair; no old replay gas is used.
Admission supplies price/base ordering and the prepayment supplies its budget.
The burn is an accounting residual, not an extra balance credit. -/
namespace Eip8282.Audit.Integrator.ReferenceSourceFeeAmounts
open EvmYul EvmYul.EVM
open ReferenceAdmissionExtraction
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem dynamic_base (cap priority : UInt256) (base : Nat) (fits : base ≤ cap.toNat) :
    base ≤ (min priority (cap-UInt256.ofNat base)+UInt256.ofNat base).toNat := by
  have bn : (UInt256.ofNat base).toNat = base := Nat.mod_eq_of_lt (fits.trans_lt cap.val.isLt)
  have sn : (cap-UInt256.ofNat base).toNat = cap.toNat-base := by
    rw [Eip8282.Audit.EntryReach.toNat_sub_of_le _ _ (by rw [bn]; exact fits),bn]
  have mn : (min priority (cap-UInt256.ofNat base)).toNat ≤ cap.toNat-base := by
    change (if priority ≤ cap-UInt256.ofNat base then priority else cap-UInt256.ofNat base).toNat ≤ _
    split
    · rename_i h
      change priority.toNat ≤ (cap-UInt256.ofNat base).toNat at h
      rwa [sn] at h
    · exact sn.le
  have capFit : cap.toNat < UInt256.size := cap.val.isLt
  rw [Eip8282.Audit.EntryReach.toNat_add_of_lt _ _ (by rw [bn]; omega),bn]
  omega

theorem price_base (tx : RefundAccounting.Context) (base : tx.baseFee ≤ feeCap tx.transaction) :
    tx.baseFee ≤ tx.effectivePrice.toNat := by
  obtain ⟨fuel,world,baseFee,header,genesis,blocks,transaction,sender⟩ := tx
  cases transaction with
  | legacy t => exact base
  | access t => exact base
  | dynamic t => exact dynamic_base t.maxFeePerGas t.maxPriorityFeePerGas baseFee base
  | blob t => exact dynamic_base t.maxFeePerGas t.maxPriorityFeePerGas baseFee base

theorem partition (gas : ReferenceTransactionGas.Settlement) (limit price base : Nat)
    (conserved : gas.gasUsed+gas.gasLeft = limit) (ordered : base ≤ price) :
    gas.gasLeft*price + gas.gasUsed*(price-base) + gas.gasUsed*base = limit*price ∧
    gas.gasLeft*price + gas.gasUsed*(price-base) ≤ limit*price := by
  have eq : gas.gasLeft*price + gas.gasUsed*(price-base) + gas.gasUsed*base = limit*price := by
    rw [Nat.add_assoc,← Nat.mul_add,Nat.sub_add_cancel ordered,← Nat.add_mul,Nat.add_comm gas.gasLeft,conserved]
  exact ⟨eq,by omega⟩

theorem actual {txGas floor grant : Nat} {meter : ReferenceMeterRollback.Meter}
    (facts : ReferenceTransactionSettlement.Facts txGas floor grant meter)
    (price base : Nat) (ordered : base ≤ price) :
    let gas := ReferenceTransactionSettlement.calculation txGas floor grant meter
    gas.gasLeft*price + gas.gasUsed*(price-base) + gas.gasUsed*base = txGas*price ∧
    gas.gasLeft*price + gas.gasUsed*(price-base) ≤ txGas*price :=
  partition _ _ _ _ facts.sender_conservation ordered

#print axioms price_base
#print axioms partition
#print axioms actual
end Eip8282.Audit.Integrator.ReferenceSourceFeeAmounts

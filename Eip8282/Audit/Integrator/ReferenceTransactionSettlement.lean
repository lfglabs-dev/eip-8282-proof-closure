import Eip8282.Audit.Integrator.ReferenceOutcomeGas

/-! Apply the pinned source's ordered transaction gas formula to the exact
returned frame meter. Its checked conversions/subtractions are conclusions
from same-run validity, not alternate invented modulo/clamp arithmetic.
This calculates gas quantities; sender/beneficiary fee balance updates and
block/canonical admission are separate consumers. -/
namespace Eip8282.Audit.Integrator.ReferenceTransactionSettlement
open EvmYul ReferenceMeterRollback
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def calculation (txGas floor grant : Nat) (m : Meter) : ReferenceTransactionGas.Settlement :=
  ReferenceTransactionGas.settle txGas floor m.execution m.reservoir (UInt256.ofNat m.refund.toNat) (netUsed grant m)

structure Facts (txGas floor grant : Nat) (m : Meter) : Prop where
  net_checked : checkedNetUsed grant m = some (netUsed grant m)
  refund_checked : ReferenceRefundCounter.checked m.refund = some (UInt256.ofNat m.refund.toNat)
  refund_exact : ((UInt256.ofNat m.refund.toNat).toNat : Int) = m.refund
  execution_returned : m.execution ≤ txGas
  state_returned : m.reservoir ≤ txGas-m.execution
  state_subtraction : ReferenceTransactionGas.settledState (netUsed grant m) ≤ txGas-m.execution-m.reservoir
  refund_subtraction : min ((txGas-m.execution-m.reservoir)/5) (UInt256.ofNat m.refund.toNat).toNat ≤ txGas-m.execution-m.reservoir
  sender_charge_bound : (calculation txGas floor grant m).gasUsed ≤ txGas
  sender_conservation : (calculation txGas floor grant m).gasUsed+(calculation txGas floor grant m).gasLeft = txGas
  execution_floor : floor ≤ (calculation txGas floor grant m).executionUsed

theorem settled {txGas floor grant : Nat} {m : Meter}
    (valid : ReferenceOutcomeGas.Valid txGas grant m) (floorFits : floor ≤ txGas) : Facts txGas floor grant m := by
  have result := ReferenceTransactionGas.settlement txGas floor m.execution m.reservoir
    (UInt256.ofNat m.refund.toNat) (netUsed grant m) valid.returned floorFits valid.state
  have exactRefund : ((UInt256.ofNat m.refund.toNat).toNat : Int) = m.refund := by
    have fit : m.refund.toNat < UInt256.size := by have h := valid.refund_fits; have hn := valid.refund_nonnegative; omega
    change ((m.refund.toNat % UInt256.size : Nat) : Int) = m.refund
    rw [Nat.mod_eq_of_lt fit]
    exact Int.toNat_of_nonneg valid.refund_nonnegative
  exact ⟨if_pos valid.baseline,if_pos ⟨valid.refund_nonnegative,valid.refund_fits⟩,exactRefund,
    result.1,result.2.1,result.2.2.2.1,result.2.2.1,result.2.2.2.2.1,result.2.2.2.2.2.1,result.2.2.2.2.2.2⟩

#print axioms settled
end Eip8282.Audit.Integrator.ReferenceTransactionSettlement

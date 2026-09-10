import Eip8282.Audit.Integrator.ReferenceTransactionGas
import Eip8282.Audit.Integrator.ReferenceSharedPayment

/-! Concrete source allocation consumes the same event list's two budgets.
The inequalities are sufficient resource requirements, not consequences of
transaction validity alone. In particular a valid transaction may run out of
gas. State payment can spill, including when the initial reservoir is zero. -/
namespace Eip8282.Audit.Integrator.ReferenceTransactionPayment
open EvmYul ReferenceStorageGas ReferenceMeterPath ReferenceTransactionGas
set_option autoImplicit false

def initialMeter (txGas intrinsic : Nat) : Meter :=
  {execution := (allocate txGas intrinsic).execution,
   reservoir := (allocate txGas intrinsic).reservoir,
   spill := 0, refund := 0}

theorem payment (events : List Event) (txGas intrinsic : Nat)
    (executionFits : intrinsic+sumExec events ≤ 16777216)
    (totalFits : intrinsic+sumExec events+sumState events ≤ txGas) :
    ∃ post, run events (initialMeter txGas intrinsic) = some post := by
  have alloc := allocation txGas intrinsic (by omega) (by omega)
  apply ReferenceSharedPayment.payment
  · change sumExec events ≤ min (16777216-intrinsic) (txGas-intrinsic)
    omega
  · change sumExec events+sumState events ≤ (allocate txGas intrinsic).execution+(allocate txGas intrinsic).reservoir
    omega

/-- A zero reservoir is supported by the same literal allocation and payment,
without changing either source rule or inventing additional state gas. -/
theorem below_cap (events : List Event) (txGas intrinsic : Nat)
    (cap : txGas ≤ 16777216)
    (totalFits : intrinsic+sumExec events+sumState events ≤ txGas) :
    (initialMeter txGas intrinsic).reservoir = 0 ∧
    ∃ post, run events (initialMeter txGas intrinsic) = some post := by
  constructor
  · simp only [initialMeter,allocate]
    omega
  · exact payment events txGas intrinsic (by omega) totalFits

#print axioms payment
#print axioms below_cap
end Eip8282.Audit.Integrator.ReferenceTransactionPayment

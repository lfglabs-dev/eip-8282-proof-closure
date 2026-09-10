import Eip8282.Audit.Integrator.ReferenceExecutionLedger
import Eip8282.Audit.Integrator.ReferenceTransactionGas
import Eip8282.Audit.Integrator.ResourceBounds

/-! Source execution allocation and calldata floor consume the finite nested
resource ledger. No nonnegative net-state premise is needed for the comparison
with block execution charge. Actual source transaction/frame/block extraction
and the completed-append instruction-cost producer remain explicit inputs.
The arithmetic does not manufacture a completed append count from LOG0 alone. -/
namespace Eip8282.Audit.Integrator.ReferenceTransactionWork
open EvmYul ReferenceMeterRollback ReferenceExecutionPotential ReferenceExecutionLedger
open ReferenceTransactionGas
set_option autoImplicit false

def initial (txGas intrinsic : Nat) : Meter :=
  ReferenceChildMeter.init (allocate txGas intrinsic).execution (allocate txGas intrinsic).reservoir

theorem allocated_work {txGas intrinsic executed : Nat} {post : Meter}
    (h : Run (initial txGas intrinsic) post executed)
    (affords : intrinsic ≤ txGas) (maximum : intrinsic ≤ 16777216) :
    intrinsic+executed ≤ 16777216 := by
  have hrun := bounded h
  have halloc := allocation txGas intrinsic affords maximum
  simp only [initial,ReferenceChildMeter.init,potential,Nat.add_zero] at hrun
  omega

/-- The 1419 premise is a structural completed-append cost certificate, to be
produced on actual disjoint completed protected frames. It is never an
admission condition or a count bound assumed about a canonical history. -/
theorem appends_le_execution_charge {txGas intrinsic executed appends : Nat} {post : Meter}
    (h : Run (initial txGas intrinsic) post executed)
    (affords : intrinsic ≤ txGas) (maximum : intrinsic ≤ 16777216)
    (completedCost : 1419*appends ≤ executed)
    (dataBytes recipientExecution accessTokens gasLeft stateLeft : Nat)
    (refund : UInt256) (netState : Int) :
    appends ≤ 11823 ∧
    appends ≤ (settle txGas (ReferenceCalldataAdmission.floor dataBytes recipientExecution accessTokens)
      gasLeft stateLeft refund netState).executionUsed := by
  have hw := allocated_work h affords maximum
  have hf : 12000 ≤ ReferenceCalldataAdmission.floor dataBytes recipientExecution accessTokens := by
    simp only [ReferenceCalldataAdmission.floor]
    omega
  have he : ReferenceCalldataAdmission.floor dataBytes recipientExecution accessTokens ≤
      (settle txGas (ReferenceCalldataAdmission.floor dataBytes recipientExecution accessTokens)
        gasLeft stateLeft refund netState).executionUsed := Nat.le_max_right _ _
  omega

/-- The sender refund and signed state usage may vary arbitrarily here; the
same literal source execution settlement is always at least its calldata floor.
Checked Uint subtraction validity is still required by the source adapter. -/
theorem floor_execution (txGas dataBytes recipientExecution accessTokens gasLeft stateLeft : Nat)
    (refund : UInt256) (netState : Int) :
    12000 ≤ (settle txGas (ReferenceCalldataAdmission.floor dataBytes recipientExecution accessTokens)
      gasLeft stateLeft refund netState).executionUsed := by
  have h : 12000 ≤ ReferenceCalldataAdmission.floor dataBytes recipientExecution accessTokens := by
    simp only [ReferenceCalldataAdmission.floor]
    omega
  exact h.trans (Nat.le_max_right _ _)

#print axioms allocated_work
#print axioms appends_le_execution_charge
#print axioms floor_execution
end Eip8282.Audit.Integrator.ReferenceTransactionWork

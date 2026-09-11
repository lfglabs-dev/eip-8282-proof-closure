import Eip8282.Audit.Integrator.ReferenceCalldataAdmission

/-! Literal Nat transcription of Amsterdam allocation and settlement.
EL0cc100eb190b64b23baba72dac0165652eaec252 vm/gas.py:1116-1150,1177-1250,
SHA41d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c,
full body audit/receipts/direct-reference-admission-sources-20260910.json.
Explicit source guards justify checked subtraction. This proves arithmetic of
these definitions, not Python execution or that a validator/frame supplied
the inputs. In particular source execution and state pools are not oldYul gas.
-/
namespace Eip8282.Audit.Integrator.ReferenceTransactionGas
open EvmYul
set_option autoImplicit false

structure Allocation where
  execution : Nat
  reservoir : Nat

def allocate (txGas intrinsic : Nat) : Allocation :=
  let evmGas := txGas-intrinsic
  let executionBudget := 16777216-intrinsic
  let execution := min executionBudget evmGas
  {execution := execution, reservoir := evmGas-execution}

/-- Every checked subtraction in allocation is funded by the two admission
checks; remaining-pool conservation is a conclusion. -/
theorem allocation (txGas intrinsic : Nat)
    (affords : intrinsic ≤ txGas) (maximum : intrinsic ≤ 16777216) :
    (allocate txGas intrinsic).execution+(allocate txGas intrinsic).reservoir = txGas-intrinsic ∧
    intrinsic+(allocate txGas intrinsic).execution+(allocate txGas intrinsic).reservoir = txGas ∧
    (allocate txGas intrinsic).execution ≤ 16777216-intrinsic ∧
    (allocate txGas intrinsic).execution ≤ txGas-intrinsic ∧
    intrinsic+(allocate txGas intrinsic).execution ≤ 16777216 := by
  simp only [allocate]
  omega

structure Settlement where
  gasUsed : Nat
  gasLeft : Nat
  executionUsed : Nat
  stateUsed : Nat

/-- Uint(max(0,netState)) has value Int.toNat netState. -/
def settledState (netState : Int) : Nat := (max 0 netState).toNat

def settle (txGas calldataFloor gasLeft stateLeft : Nat) (refund : UInt256) (netState : Int) : Settlement :=
  let beforeRefund := txGas-gasLeft-stateLeft
  let gasRefund := min (beforeRefund/5) refund.toNat
  let afterRefund := beforeRefund-gasRefund
  let gasUsed := max afterRefund calldataFloor
  let stateUsed := settledState netState
  let executionUsed := max (beforeRefund-stateUsed) calldataFloor
  {gasUsed := gasUsed, gasLeft := txGas-gasUsed,
   executionUsed := executionUsed, stateUsed := stateUsed}

/-- The source sender-facing charge never drops below its calldata floor. -/
theorem floor_paid (txGas calldataFloor gasLeft stateLeft : Nat) (refund : UInt256) (netState : Int) :
    calldataFloor ≤ (settle txGas calldataFloor gasLeft stateLeft refund netState).gasUsed := by
  exact Nat.le_max_right _ _

/-- Source checked subtraction guards, final sender conservation and bounds.
Returned pools and net state usage are frame inputs, not assumed conclusions
about this allocation or a claimed source interpreter execution. -/
theorem settlement (txGas calldataFloor gasLeft stateLeft : Nat) (refund : UInt256) (netState : Int)
    (returned : gasLeft+stateLeft ≤ txGas) (floorFits : calldataFloor ≤ txGas)
    (stateFits : settledState netState ≤ txGas-gasLeft-stateLeft) :
    gasLeft ≤ txGas ∧ stateLeft ≤ txGas-gasLeft ∧
    min ((txGas-gasLeft-stateLeft)/5) refund.toNat ≤ txGas-gasLeft-stateLeft ∧
    settledState netState ≤ txGas-gasLeft-stateLeft ∧
    (settle txGas calldataFloor gasLeft stateLeft refund netState).gasUsed ≤ txGas ∧
    (settle txGas calldataFloor gasLeft stateLeft refund netState).gasUsed+
      (settle txGas calldataFloor gasLeft stateLeft refund netState).gasLeft = txGas ∧
    calldataFloor ≤ (settle txGas calldataFloor gasLeft stateLeft refund netState).executionUsed := by
  simp only [settle]
  omega

#print axioms allocation
#print axioms floor_paid
#print axioms settlement
end Eip8282.Audit.Integrator.ReferenceTransactionGas

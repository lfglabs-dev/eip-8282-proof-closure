import Eip8282.Audit.Guarantees.PSubmit1

/-!
# P-SUBMIT-1 kill-line

The mutation is applied to the **bytecode**, not to any model function. A single
byte of the pinned builder_deposits runtime is changed and the *same*
`PSubmit1.submitFacts` the parent is registered against is re-evaluated. It
must come out `false`.

This is what makes `PSubmit1.psubmit1_bytecode_parent` load-bearing: were the
parent a tautology, or were it phrased over an abstract `Model.userCall`, no
edit to these bytes could refute it.
-/

namespace Eip8282.Tests.PSubmit1Mutant

open Eip8282.Audit.Bytecode
open Eip8282.Audit.EvmRunner
open Eip8282.Audit.Guarantees.PSubmit1

/-- Offset of the `RETURN` (`0xf3`) that ends the fee-getter path
`...5f5260205ff35b` in builder_deposits' runtime. -/
def feeReturnIdx : Nat := 158

/-- Sanity: the pinned byte really is `RETURN`, and the runtime is 628 bytes. -/
theorem pinned_fee_return_is_f3 :
    depositRuntime.size = 628 ∧ depositRuntime.get! feeReturnIdx = 0xf3 := by
  native_decide

/-- `RETURN` → `REVERT`. One byte. Nothing else in the world changes. -/
def mutatedDepositRuntime : ByteArray := depositRuntime.set! feeReturnIdx 0xfd

theorem mutant_differs_in_one_byte :
    mutatedDepositRuntime.size = depositRuntime.size ∧
      mutatedDepositRuntime.get! feeReturnIdx = 0xfd := by
  native_decide

/--
**Kill-line.** The mutated runtime refutes the parent's own conjunction, and
refutes the getter conjunct the parent states separately. The exit runtime is
left pinned, so the failure is attributable to the deposit bytes.
-/
theorem mutant_refutes_parent :
    submitFacts mutatedDepositRuntime exitRuntime = false ∧
      isSuccess (runDeposit FUEL submitter 0 ByteArray.empty
        (code := mutatedDepositRuntime) (storage := liveStorage)) = false ∧
      isRevert (runDeposit FUEL submitter 0 ByteArray.empty
        (code := mutatedDepositRuntime) (storage := liveStorage)) = true := by
  native_decide

/-- The mutation is not vacuous in the other direction: the pinned bytes
satisfy exactly what the mutant breaks. -/
theorem pinned_satisfies_what_mutant_breaks :
    depositFeeGetterFact depositRuntime = true ∧
      depositFeeGetterFact mutatedDepositRuntime = false := by
  native_decide

end Eip8282.Tests.PSubmit1Mutant

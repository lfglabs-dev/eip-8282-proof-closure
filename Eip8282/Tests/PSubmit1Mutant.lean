import Eip8282.Audit.Guarantees.PSubmit1
import Eip8282.Audit.Guarantees.PDrain1
import Eip8282.Audit.Guarantees.PControl1

/-!
# P-SUBMIT-1 kill-line

The mutations are applied to the **bytecode**, not to any model function.
Single bytes of the pinned builder_deposits runtime are changed and the
*same* `PSubmit1.submitFacts` the parent is registered against is
re-evaluated. It must come out `false`.

Three user-path bytes are cut:

* **the fee-getter `RETURN`** — offset 158, `0xf3` → `0xfd`. Wave 1.
  The empty-calldata quote reverts instead of returning 32 bytes.
* **the write-path `LOG0` data size** — offset 274, the `PUSH1 0xb8`
  (`RECORD_SIZE = 184`) that sizes the anonymous log on a paid deposit.
  Flipping it to `PUSH1 0x00` leaves the six-word SSTORE append intact
  and still emits one topic-free log, but the data is empty, so
  `depositPaidLogFact` fails. Wave 4.
* **the write-path fee `CALLVALUE`** — offset 161, `0x34` → `GAS` (`0x5a`).
  Wave 6. This is the `callvalue` the handle_input fee check compares
  against the quoted fee (`dup1; callvalue; lt; jumpi @revert`). Replacing
  it with remaining gas makes `gas < fee` false at 30M gas, so a
  well-formed 184-byte deposit whose `msg.value` is strictly below the
  quote succeeds and writes, and `depositUnderpayFact` /
  `altDepositUnderpayFact` fail. Wave-1 RETURN@158 and Wave-4 LOG size@274
  are left alone. The getter-path `CALLVALUE` at 148, the stake-check
  `CALLVALUE` at 198, and the exit fee-check `CALLVALUE` at 159 are left
  alone.

`underpay_mutant_leaves_siblings_intact` proves the new cut leaves
`PDrain1.drainFacts` and `PControl1.controlFacts` true. So the underpay
conjunct is not a restatement of a sibling guarantee.
-/

namespace Eip8282.Tests.PSubmit1Mutant

open Eip8282.Audit.Bytecode
open Eip8282.Audit.EvmRunner
open Eip8282.Audit.Guarantees.PSubmit1

/-- Offset of the `RETURN` (`0xf3`) that ends the fee-getter path
`...5f5260205ff35b` in builder_deposits' runtime. -/
def feeReturnIdx : Nat := 158

/-- Offset of the `PUSH1 0xb8` immediate that sizes the user-path
`LOG0` (`60b85fa0`) on a paid deposit. Distinct from the calldatacopy
size at offset 269 and from every drain-only byte. -/
def depositLogSizeIdx : Nat := 274

/-- Offset of the handle_input `CALLVALUE` (`0x34`) that the fee check
compares against the quote. Distinct from the getter-path `CALLVALUE`
at 148 and from the stake-check `CALLVALUE` at 198. -/
def depositFeeCallvalueIdx : Nat := 161

/-- Sanity: the pinned bytes really are what the mutations claim to cut. -/
theorem pinned_submit_bytes :
    depositRuntime.size = 628
    ∧ depositRuntime.get! feeReturnIdx = 0xf3
    ∧ depositRuntime.get! depositLogSizeIdx = 0xb8
    ∧ depositRuntime.get! depositFeeCallvalueIdx = 0x34
    ∧ depositRuntime.get! 148 = 0x34
    ∧ depositRuntime.get! 162 = 0x10
    ∧ depositRuntime.get! 198 = 0x34
    ∧ depositRuntime.get! 269 = 0xb8
    ∧ depositRuntime.get! 276 = 0xa0
    ∧ exitRuntime.size = 458
    ∧ exitRuntime.get! 159 = 0x34
    ∧ exitRuntime.get! 215 = 0x44
    ∧ exitRuntime.get! 217 = 0xa0 := by
  native_decide

/-- `RETURN` → `REVERT`. One byte. Nothing else in the world changes. -/
def mutatedDepositRuntime : ByteArray := depositRuntime.set! feeReturnIdx 0xfd

/-- `PUSH1 184` → `PUSH1 0` on the user-path `LOG0` size only. -/
def logSizeMutatedDeposit : ByteArray := depositRuntime.set! depositLogSizeIdx 0x00

/-- `CALLVALUE` → `GAS` on the handle_input fee check only. -/
def underpayMutatedDeposit : ByteArray :=
  depositRuntime.set! depositFeeCallvalueIdx 0x5a

theorem mutants_differ_in_one_byte :
    mutatedDepositRuntime.size = depositRuntime.size
    ∧ mutatedDepositRuntime.get! feeReturnIdx = 0xfd
    ∧ mutatedDepositRuntime.get! depositLogSizeIdx = 0xb8
    ∧ mutatedDepositRuntime.get! depositFeeCallvalueIdx = 0x34
    ∧ logSizeMutatedDeposit.size = depositRuntime.size
    ∧ logSizeMutatedDeposit.get! depositLogSizeIdx = 0x00
    ∧ logSizeMutatedDeposit.get! feeReturnIdx = 0xf3
    ∧ logSizeMutatedDeposit.get! depositFeeCallvalueIdx = 0x34
    ∧ logSizeMutatedDeposit.get! 269 = 0xb8
    ∧ logSizeMutatedDeposit.get! 276 = 0xa0
    ∧ underpayMutatedDeposit.size = depositRuntime.size
    ∧ underpayMutatedDeposit.get! depositFeeCallvalueIdx = 0x5a
    ∧ underpayMutatedDeposit.get! feeReturnIdx = 0xf3
    ∧ underpayMutatedDeposit.get! depositLogSizeIdx = 0xb8
    ∧ underpayMutatedDeposit.get! 148 = 0x34
    ∧ underpayMutatedDeposit.get! 198 = 0x34 := by
  native_decide

/--
**Kill-line.** Each mutant refutes `submitFacts`, the exact conjunction
`psubmit1_bytecode_parent` is registered against. The exit runtime is
left pinned, so the failure is attributable to the deposit bytes.
-/
theorem mutant_refutes_parent :
    submitFacts mutatedDepositRuntime exitRuntime = false
    ∧ isSuccess (runDeposit FUEL submitter 0 ByteArray.empty
        (code := mutatedDepositRuntime) (storage := liveStorage)) = false
    ∧ isRevert (runDeposit FUEL submitter 0 ByteArray.empty
        (code := mutatedDepositRuntime) (storage := liveStorage)) = true
    ∧ submitFacts logSizeMutatedDeposit exitRuntime = false
    ∧ submitFacts underpayMutatedDeposit exitRuntime = false := by
  native_decide

/-- The Wave-1 mutation is not vacuous in the other direction: the pinned
bytes satisfy exactly what the getter mutant breaks. -/
theorem pinned_satisfies_what_mutant_breaks :
    depositFeeGetterFact depositRuntime = true
    ∧ depositFeeGetterFact mutatedDepositRuntime = false := by
  native_decide

/--
The log-size mutant's mechanism, spelled out against the parent's own
conjuncts. The paid deposit still succeeds and still appends the six
calldata words; only the receipt changes: `LOG0` is still anonymous,
but its data is 0 bytes instead of the 184-byte record.
-/
theorem log_size_mutant_empties_the_log :
    (let r := runDeposit FUEL submitter payment depositInput
        (code := logSizeMutatedDeposit) (storage := liveStorage);
      isSuccess r = true
        ∧ successLogCount r = 1
        ∧ successLogTopicsLen r 0 = some 0
        ∧ successLogDataSize r 0 = some 0
        ∧ successLog0Is r 0 depositInput = false)
    ∧ depositPaidLogFact logSizeMutatedDeposit = false
    ∧ depositPaidAppendFact logSizeMutatedDeposit = true
    ∧ depositFeeGetterFact logSizeMutatedDeposit = true
    ∧ depositValueRejectedFact logSizeMutatedDeposit = true
    ∧ depositInhibitedFact logSizeMutatedDeposit = true
    ∧ depositUnderpayFact logSizeMutatedDeposit = true
    ∧ exitPaidLogFact exitRuntime = true := by
  native_decide

/-- The pinned bytes satisfy exactly what the log-size mutant breaks. -/
theorem pinned_satisfies_what_log_mutant_breaks :
    depositPaidLogFact depositRuntime = true
    ∧ depositPaidLogFact logSizeMutatedDeposit = false
    ∧ exitPaidLogFact exitRuntime = true := by
  native_decide

/--
**The Wave-4 conjunct is not a sibling.** The write-path `LOG0` size is
invisible to P-DRAIN-1 (system `RETURN` uses exit offset 450) and to
P-CONTROL-1 (no receipt observation). Both sibling parents stay true.
-/
theorem log_mutant_leaves_siblings_intact :
    Eip8282.Audit.Guarantees.PDrain1.drainFacts logSizeMutatedDeposit exitRuntime = true
    ∧ Eip8282.Audit.Guarantees.PControl1.controlFacts logSizeMutatedDeposit exitRuntime = true := by
  native_decide

/--
The underpay mutant's mechanism, spelled out against the new conjuncts.
A 184-byte deposit whose `msg.value` is `liveDepositFee - 1` now
*succeeds* and writes `SLOT_COUNT`/`SLOT_TAIL`, so the freeze fails on
both storage images. The getter, the paid-enough append, and the LOG0
stay true: only the fee-check `CALLVALUE` moved.
-/
theorem underpay_mutant_accepts_the_underpay :
    (let r := runDeposit FUEL submitter (liveDepositFee - 1) depositInput
        (code := underpayMutatedDeposit) (storage := liveStorage);
      isRevert r = false
        ∧ isSuccess r = true
        ∧ slots0to3Are r depositAddr 100 6 7 10 = true)
    ∧ depositUnderpayFact underpayMutatedDeposit = false
    ∧ altDepositUnderpayFact underpayMutatedDeposit = false
    ∧ depositFeeGetterFact underpayMutatedDeposit = true
    ∧ depositPaidAppendFact underpayMutatedDeposit = true
    ∧ depositPaidLogFact underpayMutatedDeposit = true
    ∧ depositInhibitedFact underpayMutatedDeposit = true
    ∧ depositValueRejectedFact underpayMutatedDeposit = true
    ∧ exitUnderpayFact exitRuntime = true
    ∧ altExitUnderpayFact exitRuntime = true := by
  native_decide

/-- The pinned bytes satisfy exactly what the underpay mutant breaks. -/
theorem pinned_satisfies_what_underpay_mutant_breaks :
    depositUnderpayFact depositRuntime = true
    ∧ altDepositUnderpayFact depositRuntime = true
    ∧ depositUnderpayFact underpayMutatedDeposit = false
    ∧ altDepositUnderpayFact underpayMutatedDeposit = false
    ∧ exitUnderpayFact exitRuntime = true := by
  native_decide

/--
**The new conjunct is not a sibling.** The handle_input fee `CALLVALUE`
is on the user write path. P-DRAIN-1 only calls from `SYSTEM_ADDR`.
P-CONTROL-1's paid submissions use `payment` strictly above the quote,
so swapping that `CALLVALUE` for `GAS` does not change the control
traces. Both sibling parents stay true.
-/
theorem underpay_mutant_leaves_siblings_intact :
    Eip8282.Audit.Guarantees.PDrain1.drainFacts underpayMutatedDeposit exitRuntime = true
    ∧ Eip8282.Audit.Guarantees.PControl1.controlFacts underpayMutatedDeposit exitRuntime = true := by
  native_decide

end Eip8282.Tests.PSubmit1Mutant

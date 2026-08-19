import Eip8282.Audit.Guarantees.PControl1
import Eip8282.Audit.Guarantees.PSubmit1

/-!
# P-CONTROL-1 kill-line

The mutations are applied to the **bytecode**, not to any model function. Single
bytes of the pinned runtimes are changed and the *same* `PControl1.controlFacts`
the parent is registered against is re-evaluated. It must come out `false`.

Two independent bytes are cut, one per half of the control plane:

* **the caller gate** — the `EQ` at offset 22 that compares `CALLER` against
  `SYSTEM_ADDR` and decides whether the call enters the system subroutine;
* **the system-side `TARGET_PER_BLOCK`** — the `8` at offset 571, inside the
  `compute_excess` block that the system subroutine alone reaches.

Both are control-plane bytes in the strict sense: neither is touched by any user
submission trace. `control_mutants_leave_psubmit1_intact` proves that directly —
P-SUBMIT-1's parent still holds of both mutants. So
`PControl1.pcontrol1_bytecode_parent` is not a re-statement of a sibling
guarantee; it is load-bearing on bytes nothing else in this repository
constrains.
-/

namespace Eip8282.Tests.PControl1Mutant

open Eip8282.Audit.Bytecode
open Eip8282.Audit.EvmRunner
open Eip8282.Audit.Guarantees.PControl1

/-- Offset of the `EQ` in `CALLER; PUSH20 SYSTEM_ADDR; EQ; JUMPI @read_requests`,
the first four instructions of both runtimes. -/
def gateEqIdx : Nat := 22

/-- Offset of the `TARGET_PER_BLOCK` operand of `PUSH1 8` in builder_deposits'
`compute_excess` block (`ADD; PUSH1 8; SWAP1; SUB`), reachable only from the
system subroutine. -/
def sysTargetIdx : Nat := 571

/-- Sanity: the pinned bytes really are what the mutations claim to cut. -/
theorem pinned_control_bytes :
    depositRuntime.size = 628
    ∧ exitRuntime.size = 458
    ∧ depositRuntime.get! gateEqIdx = 0x14
    ∧ exitRuntime.get! gateEqIdx = 0x14
    ∧ depositRuntime.get! sysTargetIdx = 0x08 := by
  native_decide

/-- `EQ` → `LT`. `SYSTEM_ADDR < SYSTEM_ADDR` is false, so the system address no
longer opens the gate and every caller falls through to the user subroutine. -/
def gateMutatedDeposit : ByteArray := depositRuntime.set! gateEqIdx 0x10

/-- The same cut in builder_exits. -/
def gateMutatedExit : ByteArray := exitRuntime.set! gateEqIdx 0x10

/-- `PUSH1 8` → `PUSH1 9` in the system-side excess recurrence only. -/
def targetMutatedDeposit : ByteArray := depositRuntime.set! sysTargetIdx 0x09

theorem mutants_differ_in_one_byte :
    gateMutatedDeposit.size = depositRuntime.size
    ∧ gateMutatedDeposit.get! gateEqIdx = 0x10
    ∧ gateMutatedExit.size = exitRuntime.size
    ∧ gateMutatedExit.get! gateEqIdx = 0x10
    ∧ targetMutatedDeposit.size = depositRuntime.size
    ∧ targetMutatedDeposit.get! sysTargetIdx = 0x09 := by
  native_decide

/--
**Kill-line.** Each mutant refutes `controlFacts`, the exact conjunction
`pcontrol1_bytecode_parent` is registered against. The other runtime is left
pinned in each case, so the failure is attributable to the cut bytes.
-/
theorem mutant_refutes_parent :
    controlFacts gateMutatedDeposit exitRuntime = false
    ∧ controlFacts depositRuntime gateMutatedExit = false
    ∧ controlFacts targetMutatedDeposit exitRuntime = false := by
  native_decide

/--
The gate mutant's mechanism, spelled out against the parent's own conjuncts.
With the gate cut, a call from `SYSTEM_ADDR` is answered as a *user* call: it
returns a 32-byte fee quote instead of draining, `SLOT_COUNT` keeps its old
value 5 instead of being reset, `SLOT_EXCESS` stays 100 instead of becoming 97 —
and, worst, from the inhibited image the system call now reverts, so the drain
and the re-enable path are lost exactly when the kill switch is down.
-/
theorem gate_mutant_loses_the_system_subroutine :
    successOutSize (runDepositSystem FUEL ByteArray.empty
        (code := gateMutatedDeposit) (storage := ctlStorage 100 5)) = 32
    ∧ slots0to3Are (runDepositSystem FUEL ByteArray.empty
        (code := gateMutatedDeposit) (storage := ctlStorage 100 5)) depositAddr 100 5 0 0 = true
    ∧ isRevert (runDepositSystem FUEL ByteArray.empty
        (code := gateMutatedDeposit) (storage := inhibitedStorage 5)) = true
    ∧ depositGateFact gateMutatedDeposit = false
    ∧ depositCountResetFact gateMutatedDeposit = false
    ∧ depositInhibitedGatingFact gateMutatedDeposit = false := by
  native_decide

/--
The target mutant's mechanism. It is surgical: the user-facing quote is
untouched (the `bump_excess` copy of the target lives at a different offset), but
the system-side recurrence now subtracts 9, so `(100, 5)` folds to 96 instead of
97 and `(0, 9)` folds to 0 instead of 1.
-/
theorem target_mutant_shifts_only_the_system_recurrence :
    storageSlotIs (runDepositSystem FUEL ByteArray.empty
        (code := targetMutatedDeposit) (storage := ctlStorage 100 5))
        depositAddr (u256 0) (u256 96) = true
    ∧ storageSlotIs (runDepositSystem FUEL ByteArray.empty
        (code := targetMutatedDeposit) (storage := ctlStorage 0 9))
        depositAddr (u256 0) (u256 0) = true
    ∧ depositExcessFact targetMutatedDeposit = false
    ∧ depositFeeCountFact targetMutatedDeposit = true
    ∧ depositFeeDiscriminatesFact targetMutatedDeposit = true := by
  native_decide

/-- The mutations are not vacuous in the other direction: the pinned bytes
satisfy exactly what each mutant breaks. -/
theorem pinned_satisfies_what_mutants_break :
    depositGateFact depositRuntime = true
    ∧ depositGateFact gateMutatedDeposit = false
    ∧ exitGateFact exitRuntime = true
    ∧ exitGateFact gateMutatedExit = false
    ∧ depositExcessFact depositRuntime = true
    ∧ depositExcessFact targetMutatedDeposit = false := by
  native_decide

/--
**The parent is not a sibling.** Both control mutants leave
`PSubmit1.submitFacts` — the conjunction P-SUBMIT-1's own bytecode parent is
registered against — fully satisfied. P-SUBMIT-1 never calls from `SYSTEM_ADDR`
and never reaches `compute_excess`, so these bytes are invisible to it.
Whatever `pcontrol1_bytecode_parent` is carrying, it is not carried anywhere
else in this repository.
-/
theorem control_mutants_leave_psubmit1_intact :
    Eip8282.Audit.Guarantees.PSubmit1.submitFacts gateMutatedDeposit exitRuntime = true
    ∧ Eip8282.Audit.Guarantees.PSubmit1.submitFacts targetMutatedDeposit exitRuntime = true := by
  native_decide

end Eip8282.Tests.PControl1Mutant

import Eip8282.Audit.Guarantees.PControl1
import Eip8282.Audit.Guarantees.PSubmit1

/-!
# P-CONTROL-1 kill-line

The mutations are applied to the **bytecode**, not to any model function. Single
bytes of the pinned runtimes are changed and the *same* `PControl1.controlFacts`
the parent is registered against is re-evaluated. It must come out `false`.
`pcontrol1_forall_parent` keeps those traces as conjuncts, so the same
cuts also make the registered `∀` parent false of the mutant bytecode.

Two independent bytes are cut, one per half of the control plane:

* **the caller gate** — the `EQ` at offset 22 that compares `CALLER` against
  `SYSTEM_ADDR` and decides whether the call enters the system subroutine;
* **the system-side `TARGET_PER_BLOCK`** — the `8` at offset 571, inside the
  `compute_excess` block that the system subroutine alone reaches.

Both are control-plane bytes in the strict sense: neither is touched by any user
submission trace. `control_mutants_leave_psubmit1_intact` proves that directly —
P-SUBMIT-1's parent still holds of both mutants. So
`PControl1.pcontrol1_bytecode_parent` (and the `∀` parent that contains
it) is not a re-statement of a sibling guarantee; it is load-bearing on
bytes nothing else in this repository constrains.
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

/-! ## Wave 5: nonempty-queue excess fold kill-line

The Wave-5 parent `nonemptyControlFacts` is false if the queue is empty:
`depositQueue 2` returns `368` bytes and `HEAD=0 TAIL=0` after a full drain,
while an empty image returns `0` bytes and leaves `HEAD=TAIL=0` from the
start. The same `TARGET_PER_BLOCK` byte that the Wave-1 parent is pinned on
(`deposit 571`) therefore also refutes the nonempty extension — but the new
observation is that the excess fold is *independent* of how many records were
drained. A second cut on the exit side (`exit` system `TARGET` at `400`,
`2 → 3`) shows the same for the other predeploy. Both are control-plane
bytes: the `compute_excess` block is reached only from the system subroutine,
never from a user submission.

`wave5_mutants_leave_siblings_intact` proves the nonempty kill-line is not a
restatement of a sibling: the two system-target cuts leave `P-SUBMIT-1`
(which never calls as `SYSTEM_ADDR` and never reaches `compute_excess`)
fully satisfied. `PDrain1.drainFacts` is intentionally *not* claimed intact
for the deposit cut — it also checks `excess 97` — but the `exit` cut leaves
the deposit side of `drainFacts` untouched, and the gate cut leaves the
deposit log size (P-SUBMIT-1 Wave-4) untouched. The load-bearing content of
Wave 5 is therefore the *nonempty* excess fold, not the drain.
-/

/-- Offset of the `TARGET_PER_BLOCK` operand of `PUSH1 2` in builder_exits'
`compute_excess` block. Distinct from the user-side `bump_excess` at `82`. -/
def exitSysTargetIdx : Nat := 401

def wave5TargetMutatedDeposit : ByteArray := depositRuntime.set! sysTargetIdx 0x09
def wave5TargetMutatedExit : ByteArray := exitRuntime.set! exitSysTargetIdx 0x03

theorem wave5_pinned_bytes :
    exitRuntime.get! exitSysTargetIdx = 0x02
    ∧ wave5TargetMutatedExit.get! exitSysTargetIdx = 0x03 := by
  native_decide

theorem wave5_mutant_refutes_nonempty_parent :
    nonemptyControlFacts wave5TargetMutatedDeposit exitRuntime = false
    ∧ nonemptyControlFacts depositRuntime wave5TargetMutatedExit = false
    ∧ nonemptyControlFacts gateMutatedDeposit exitRuntime = false := by
  native_decide

theorem wave5_target_shifts_nonempty_excess :
    storageSlotIs (runDepositSystem FUEL ByteArray.empty
        (code := wave5TargetMutatedDeposit) (storage := depositQueue 2))
        depositAddr (u256 0) (u256 96) = true
    ∧ storageSlotIs (runExitSystem FUEL ByteArray.empty
        (code := wave5TargetMutatedExit) (storage := exitQueue 2))
        exitAddr (u256 0) (u256 102) = true
    ∧ depositNonemptyUnderCapFact wave5TargetMutatedDeposit = false
    ∧ exitNonemptyUnderCapFact wave5TargetMutatedExit = false := by
  native_decide

theorem wave5_mutants_leave_psubmit1_intact :
    Eip8282.Audit.Guarantees.PSubmit1.submitFacts wave5TargetMutatedDeposit exitRuntime = true
    ∧ Eip8282.Audit.Guarantees.PSubmit1.submitFacts depositRuntime wave5TargetMutatedExit = true
    ∧ Eip8282.Audit.Guarantees.PSubmit1.submitFacts gateMutatedDeposit exitRuntime = true := by
  native_decide

theorem nonempty_is_not_empty :
    depositNonemptyUnderCapFact depositRuntime = true
    ∧ (let r := runDepositSystem FUEL ByteArray.empty
          (code := depositRuntime) (storage := ctlStorage 100 5);
        successOutSize r == 0 && slots0to3Are r depositAddr 97 0 0 0) = true
    ∧ depositNonemptyUnderCapFact depositRuntime !=
        (let r := runDepositSystem FUEL ByteArray.empty
            (code := depositRuntime) (storage := ctlStorage 100 5);
          isSuccess r && successOutSize r == 368) := by
  native_decide

end Eip8282.Tests.PControl1Mutant

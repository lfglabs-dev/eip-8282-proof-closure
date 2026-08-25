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

/-! ## Fold-equating mutants

The user-path `bump_excess` and system-path `update_excess` use
separate copies of `TARGET`. Changing the system copy to equal `count`
at the test image merges the two folds:

* **deposit 571: 8→5** — at `(100, 5)`, `update_excess` gives
  `max(0, 105−5) = 100`, matching `bump_excess(100, 5, 8) = 100`.
* **exit 401: 2→1** — at `(100, 1)`, `update_excess` gives
  `max(0, 101−1) = 100`, matching `bump_excess(100, 1, 2) = 100`.

These are NOT the same cuts as the standard kill-line (571: 8→9,
401: 2→3). The equating cuts make `depositFoldDiscriminateFact` and
`exitFoldDiscriminateFact` `false` because the system now stores the
bump_excess value, not a distinct one. The existing kill-line targets
the same byte, so both classes of mutants refute the strengthened
parent.
-/

def foldEquatingDeposit : ByteArray := depositRuntime.set! sysTargetIdx 0x05
def foldEquatingExit : ByteArray := exitRuntime.set! exitSysTargetIdx 0x01

theorem fold_equating_mutants_differ_in_one_byte :
    foldEquatingDeposit.size = depositRuntime.size
    ∧ foldEquatingDeposit.get! sysTargetIdx = 0x05
    ∧ foldEquatingExit.size = exitRuntime.size
    ∧ foldEquatingExit.get! exitSysTargetIdx = 0x01 := by
  native_decide

/-- The equating mutant stores the bump_excess value (100) instead of the
update_excess value (97 / 99), directly merging the two folds. -/
theorem fold_equating_mutant_stores_bump_excess_value :
    storageSlotIs (runDepositSystem FUEL ByteArray.empty
        (code := foldEquatingDeposit) (storage := ctlStorage 100 5))
        depositAddr (u256 0) (u256 100) = true
    ∧ storageSlotIs (runExitSystem FUEL ByteArray.empty
        (code := foldEquatingExit) (storage := ctlStorage 100 1))
        exitAddr (u256 0) (u256 100) = true := by
  native_decide

/-- The fold discrimination facts are `false` on the equating mutants. -/
theorem fold_equating_mutant_refutes_discrimination :
    depositFoldDiscriminateFact foldEquatingDeposit = false
    ∧ exitFoldDiscriminateFact foldEquatingExit = false := by
  native_decide

/-- The existing kill-line also refutes the fold discrimination facts:
changing TARGET shifts the system excess away from 97 / 99. -/
theorem existing_kill_line_refutes_fold_discrimination :
    depositFoldDiscriminateFact targetMutatedDeposit = false
    ∧ exitFoldDiscriminateFact wave5TargetMutatedExit = false := by
  native_decide

/-- The fold-equating mutants leave P-SUBMIT-1 intact: byte 571 / 401
are in `compute_excess`, which the user path never reaches. -/
theorem fold_equating_mutants_leave_psubmit1_intact :
    Eip8282.Audit.Guarantees.PSubmit1.submitFacts foldEquatingDeposit exitRuntime = true
    ∧ Eip8282.Audit.Guarantees.PSubmit1.submitFacts depositRuntime foldEquatingExit = true := by
  native_decide

/-! ## Kill-line for the C4 code-deposit conjunct

`CtorXi.ctorXiFacts` is cut on the **init** images, one byte each. These
are bytes no runtime trace can reach: the init code is not the deployed
code, so neither `controlFacts` nor `submitFacts` nor `drainFacts`
constrains them. Before `pcontrol1_ctor_xi_parent` nothing in this
repository did.
-/

open Eip8282.Audit.Guarantees.PControl1.CtorXi

/-- Source offset of the runtime copy in the deposit ctor
(`PUSH2 0x0274; DUP1; PUSH1 0x0a; PUSH0; CODECOPY`): the `0x0a` operand. -/
def depositCtorSrcIdx : Nat := 5

/-- The `SSTORE` of the exit ctor's `PUSH32 INHIBITOR; PUSH0; SSTORE`. -/
def exitCtorSstoreIdx : Nat := 34

/-- Sanity: the pinned init bytes really are what the mutations claim to cut. -/
theorem pinned_ctor_bytes :
    depositInit.size = 638
    ∧ exitInit.size = 503
    ∧ depositInit.get! depositCtorSrcIdx = 0x0a
    ∧ exitInit.get! exitCtorSstoreIdx = 0x55 := by
  native_decide

/-- `CODECOPY` source `10` → `11`. The ctor still returns 628 bytes and
still succeeds, but the buffer is the runtime shifted one byte, so the
code deposited is not the code every other guarantee is proved about. -/
def ctorSrcMutatedDeposit : ByteArray := depositInit.set! depositCtorSrcIdx 0x0b

/-- `SSTORE` → `POP`. The exit ctor still deploys the right runtime, but
slot 0 is left at 0 instead of `INHIBITOR`, so the exit contract starts
un-inhibited — the exact failure C4 exists to exclude. -/
def sstoreMutatedExit : ByteArray := exitInit.set! exitCtorSstoreIdx 0x50

theorem ctor_mutants_differ_in_one_byte :
    ctorSrcMutatedDeposit.size = depositInit.size
    ∧ ctorSrcMutatedDeposit.get! depositCtorSrcIdx = 0x0b
    ∧ sstoreMutatedExit.size = exitInit.size
    ∧ sstoreMutatedExit.get! exitCtorSstoreIdx = 0x50 := by
  native_decide

/-- **The C4 code-deposit kill-line.** `ctorXiFacts` is the conjunct
`pcontrol1_c4_ctor_forall` carries, so each cut also makes the registered
`pcontrol1_forall_parent` false of the mutated init image. -/
theorem ctor_mutant_refutes_parent :
    ctorXiFacts ctorSrcMutatedDeposit exitInit = false
    ∧ ctorXiFacts depositInit sstoreMutatedExit = false := by
  native_decide

/-- The two cuts are independent: the shifted-copy mutant leaves the exit
ctor alone and the lost-`SSTORE` mutant leaves the deposit ctor alone. -/
theorem ctor_mutants_are_independent :
    depositCtorFact ctorSrcMutatedDeposit = false
    ∧ exitCtorFact exitInit = true
    ∧ depositCtorFact depositInit = true
    ∧ exitCtorFact sstoreMutatedExit = false := by
  native_decide

/-- The init cuts leave every runtime guarantee intact: the deployed code
is a different byte string from the init code, so no runtime trace can
see these bytes. This is what makes the C4 code-deposit conjunct
load-bearing rather than a restatement. -/
theorem ctor_mutants_leave_runtime_guarantees_intact :
    controlFacts depositRuntime exitRuntime = true
    ∧ Eip8282.Audit.Guarantees.PSubmit1.submitFacts depositRuntime exitRuntime = true := by
  native_decide

end Eip8282.Tests.PControl1Mutant

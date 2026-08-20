import Eip8282.Audit.Guarantees.PDrain1
import Eip8282.Audit.Guarantees.PSubmit1
import Eip8282.Audit.Guarantees.PControl1

/-!
# P-DRAIN-1 kill-line

The mutations are applied to the **bytecode**, not to any model function.
Single bytes of the pinned runtimes are changed and the *same*
`PDrain1.drainFacts` the parent is registered against is re-evaluated. It
must come out `false`.

Three drain-only bytes are cut. None is on a path P-SUBMIT-1 or
P-CONTROL-1 observe:

* **the per-block exit cap** — the `16` at offset 244, the `PUSH1 MAX_PER_BLOCK`
  that replaces the live queue length once `tail - head` is no longer
  strictly below the cap. The comparison immediate at offset 237 is left
  alone, so an under-cap drain still uses the real length.
* **the drained exit record size** — the `68` at offset 450, the `PUSH1 RECORD_SIZE`
  that sizes the system `RETURN`. The user-path `LOG0` copy of `RECORD_SIZE`
  (offset 215) is not touched.
* **the per-block deposit cap** — the `64` at offset 304, the `PUSH1 MAX_PER_BLOCK`
  that *clamps* the deposit drain once `MAX > count` is not taken. The
  comparison immediate at offset 296 is left alone, so an under-cap deposit
  drain (empty / 1 / 2 records) still uses the real length. This is the
  Wave-2 kill-line: it refutes the new `depositOverCapFact` conjunct.

`drain_mutants_leave_siblings_intact` proves all three mutants leave
`PSubmit1.submitFacts` and `PControl1.controlFacts` true. So
`PDrain1.pdrain1_bytecode_parent` is not a re-statement of a sibling
guarantee; it is load-bearing on bytes nothing else in this repository
constrains.
-/

namespace Eip8282.Tests.PDrain1Mutant

open Eip8282.Audit.Bytecode
open Eip8282.Audit.EvmRunner
open Eip8282.Audit.Guarantees.PDrain1

/-- Offset of the second `PUSH1 0x10` (`MAX_PER_BLOCK`) in builder_exits'
system subroutine: the immediate that *clamps* the drain once the
`MAX > count` jump is not taken. -/
def exitCapIdx : Nat := 244

/-- Offset of the `PUSH1 0x44` (`RECORD_SIZE = 68`) that multiplies the
drained count to produce the system `RETURN` size. -/
def exitRecordSizeIdx : Nat := 450

/-- Offset of the second `PUSH1 0x40` (`MAX_PER_BLOCK = 64`) in
builder_deposits' system subroutine: the immediate that *clamps* the
drain once the `MAX > count` jump is not taken. The comparison
immediate at offset 296 is the first `PUSH1 0x40` of that pair. -/
def depositCapIdx : Nat := 304

/-- Sanity: the pinned bytes really are what the mutations claim to cut. -/
theorem pinned_drain_bytes :
    exitRuntime.size = 458
    ∧ exitRuntime.get! exitCapIdx = 0x10
    ∧ exitRuntime.get! exitRecordSizeIdx = 0x44
    ∧ depositRuntime.size = 628
    ∧ depositRuntime.get! depositCapIdx = 0x40
    ∧ depositRuntime.get! 296 = 0x40 := by
  native_decide

/-- `PUSH1 16` → `PUSH1 8` on the over-cap clamp only. -/
def capMutatedExit : ByteArray := exitRuntime.set! exitCapIdx 0x08

/-- `PUSH1 68` → `PUSH1 64` on the system return-size multiplier only. -/
def recSizeMutatedExit : ByteArray := exitRuntime.set! exitRecordSizeIdx 0x40

/-- `PUSH1 64` → `PUSH1 32` on the deposit over-cap clamp only. -/
def capMutatedDeposit : ByteArray := depositRuntime.set! depositCapIdx 0x20

theorem mutants_differ_in_one_byte :
    capMutatedExit.size = exitRuntime.size
    ∧ capMutatedExit.get! exitCapIdx = 0x08
    ∧ recSizeMutatedExit.size = exitRuntime.size
    ∧ recSizeMutatedExit.get! exitRecordSizeIdx = 0x40
    ∧ capMutatedDeposit.size = depositRuntime.size
    ∧ capMutatedDeposit.get! depositCapIdx = 0x20
    ∧ capMutatedDeposit.get! 296 = 0x40 := by
  native_decide

/--
**Kill-line.** Each mutant refutes `drainFacts`, the exact conjunction
`pdrain1_bytecode_parent` is registered against. The other runtime is
left pinned in each case, so the failure is attributable to the cut
byte.
-/
theorem mutant_refutes_parent :
    drainFacts depositRuntime capMutatedExit = false
    ∧ drainFacts depositRuntime recSizeMutatedExit = false
    ∧ drainFacts capMutatedDeposit exitRuntime = false := by
  native_decide

/--
The cap mutant's mechanism, spelled out against the parent's own conjuncts.
Seventeen queued exits now return `8 * 68 = 544` bytes and advance the head
by 8, not 16. The under-cap two-record drain is untouched, because that
path never loads the clamp immediate.
-/
theorem cap_mutant_halves_the_over_cap_drain :
    successOutSize (runExitSystem FUEL ByteArray.empty
        (code := capMutatedExit) (storage := exitQueue 17)) = 544
    ∧ storageSlotIs (runExitSystem FUEL ByteArray.empty
        (code := capMutatedExit) (storage := exitQueue 17))
        exitAddr (u256 2) (u256 8) = true
    ∧ storageSlotIs (runExitSystem FUEL ByteArray.empty
        (code := capMutatedExit) (storage := exitQueue 17))
        exitAddr (u256 3) (u256 17) = true
    ∧ exitOverCapFact capMutatedExit = false
    ∧ exitUnderCapFifoFact capMutatedExit = true := by
  native_decide

/--
The record-size mutant's mechanism. The drain loop still walks 16 / 2
records, but the system `RETURN` now reports `n * 64` bytes, so the
two-record drain is 128 bytes instead of 136 and the over-cap drain is
1024 instead of 1088.
-/
theorem rec_size_mutant_shrinks_the_return :
    successOutSize (runExitSystem FUEL ByteArray.empty
        (code := recSizeMutatedExit) (storage := exitQueue 2)) = 128
    ∧ successOutSize (runExitSystem FUEL ByteArray.empty
        (code := recSizeMutatedExit) (storage := exitQueue 17)) = 1024
    ∧ exitUnderCapFifoFact recSizeMutatedExit = false
    ∧ exitOverCapFact recSizeMutatedExit = false := by
  native_decide

/--
The deposit-cap mutant's mechanism. Sixty-five queued deposits now
return `32 * 184 = 5888` bytes and advance the head by 32, not 64.
`QUEUE_TAIL` stays 65. The empty-queue and under-cap (1- and 2-record)
deposit drains are untouched, because those paths never load the clamp
immediate.
-/
theorem deposit_cap_mutant_halves_the_over_cap_drain :
    (let r := runDepositSystem DEPOSIT_CAP_FUEL ByteArray.empty
        (code := capMutatedDeposit) (storage := depositQueue65);
      successOutSize r = 5888
        ∧ storageSlotIs r depositAddr (u256 2) (u256 32) = true
        ∧ storageSlotIs r depositAddr (u256 3) (u256 65) = true)
    ∧ depositOverCapFact capMutatedDeposit = false
    ∧ depositEmptyDrainFact capMutatedDeposit = true
    ∧ depositFifoFact capMutatedDeposit = true := by
  native_decide

/-- The mutations are not vacuous in the other direction: the pinned bytes
satisfy exactly what each mutant breaks. -/
theorem pinned_satisfies_what_mutants_break :
    exitOverCapFact exitRuntime = true
    ∧ exitOverCapFact capMutatedExit = false
    ∧ exitUnderCapFifoFact exitRuntime = true
    ∧ exitUnderCapFifoFact recSizeMutatedExit = false
    ∧ depositOverCapFact depositRuntime = true
    ∧ depositOverCapFact capMutatedDeposit = false
    ∧ depositEmptyDrainFact depositRuntime = true := by
  native_decide

/--
**The parent is not a sibling.** All three drain mutants leave
`PSubmit1.submitFacts` and `PControl1.controlFacts` — the conjunctions
those parents are registered against — fully satisfied. P-SUBMIT-1 never
calls from `SYSTEM_ADDR`. P-CONTROL-1 does, but holds an empty queue, so
the cap clamp is never taken and `0 * RECORD_SIZE` is still 0.
Whatever `pdrain1_bytecode_parent` is carrying, it is not carried anywhere
else in this repository.
-/
theorem drain_mutants_leave_siblings_intact :
    Eip8282.Audit.Guarantees.PSubmit1.submitFacts depositRuntime capMutatedExit = true
    ∧ Eip8282.Audit.Guarantees.PSubmit1.submitFacts depositRuntime recSizeMutatedExit = true
    ∧ Eip8282.Audit.Guarantees.PSubmit1.submitFacts capMutatedDeposit exitRuntime = true
    ∧ Eip8282.Audit.Guarantees.PControl1.controlFacts depositRuntime capMutatedExit = true
    ∧ Eip8282.Audit.Guarantees.PControl1.controlFacts depositRuntime recSizeMutatedExit = true
    ∧ Eip8282.Audit.Guarantees.PControl1.controlFacts capMutatedDeposit exitRuntime = true := by
  native_decide

end Eip8282.Tests.PDrain1Mutant

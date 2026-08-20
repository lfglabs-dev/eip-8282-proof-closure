import Eip8282.Audit.Guarantees.PDrain1
import Eip8282.Audit.Guarantees.PSubmit1
import Eip8282.Audit.Guarantees.PControl1

/-!
# P-DRAIN-1 kill-line

The mutations are applied to the **bytecode**, not to any model function.
Single bytes of the pinned runtimes are changed and the *same*
`PDrain1.drainFacts` the parent is registered against is re-evaluated. It
must come out `false`.

Six drain-only bytes are cut. None is on a path P-SUBMIT-1 or
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
  drain (empty / 1 / 2 records) still uses the real length.
* **the partial-drain `QUEUE_HEAD` store (Wave 3)** — the `2` at deposit offset 483,
  the `PUSH1 QUEUE_HEAD` of `SSTORE` that writes the advanced head after
  an *incomplete* drain. Flipping it to `9` (`QUEUE_OFFSET + 5`, the last
  remaining word of drained item 0) makes that `SSTORE` overwrite a
  drained remaining word with the new head value `64`, so
  `staleDepositRestIs 0` fails. The empty-queue reset writes
  `PUSH0; PUSH1 QUEUE_HEAD; SSTORE` at a different offset and is not
  touched; under-cap full drains take that reset path, so they stay true.
* **the partial-drain `QUEUE_HEAD` store (Wave 6 deposit)** — the same `2` at
  deposit offset 483 retargeted to `196` (`QUEUE_OFFSET + 6*32`, the first
  word of drained deposit item 32). Flipping it to `196` overwrites the
  distinctive first word of item 32 with `64`, so `staleDepositPk1Is 32`
  fails; the empty-queue and under-cap full drains are still untouched.
* **the partial-drain `QUEUE_HEAD` store (Wave 6 exit)** — the `2` at exit offset 313,
  the `PUSH1 QUEUE_HEAD` of the *exit* partial-drain `SSTORE`. Flipping it
  to `25` (`QUEUE_OFFSET + 3*7`, the src word of drained exit item 7)
  overwrites that word with `16`, so `staleExitSrcIs 7` fails; the empty-queue
  and under-cap exits are still untouched.

`drain_mutants_leave_siblings_intact` proves all six mutants leave
`PSubmit1.submitFacts` and `PControl1.controlFacts` true. So
`PDrain1.pdrain1_forall_parent` (via the kept `pdrain1_bytecode_parent`
/`drainFacts` traces) is not a re-statement of a sibling guarantee; it
is load-bearing on bytes nothing else in this repository constrains.
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

/-- Offset of the `PUSH1 QUEUE_HEAD` (`0x02`) that the *partial* deposit
drain uses to `SSTORE` the advanced head. The empty-queue / full-drain
reset is a different `PUSH0; PUSH1 2; SSTORE` whose operand sits at
offset 494 and is left alone. Slot `9` is `QUEUE_OFFSET + 5`, the last
remaining word of drained deposit item 0. -/
def depositHeadSlotIdx : Nat := 483

/-- Storage slot the Wave-3 mutant writes the new head into: last word
of drained item 0. -/
def depositItem0LastSlot : UInt8 := 9

/-- Offset of the `PUSH1 QUEUE_HEAD` (`0x02`) that the *partial* exit
drain uses to `SSTORE` the advanced head. The empty-queue / full-drain
reset is a different `PUSH0; PUSH1 2; SSTORE` whose operand sits at
offset 324 and is left alone. Slot `25` is `QUEUE_OFFSET + 3*7`, the src
word of drained exit item 7. -/
def exitHeadSlotIdx : Nat := 313

/-- Storage slot the Wave-6 deposit mutant writes the new head into: first
word of drained deposit item 32. -/
def depositItem32FirstSlot : UInt8 := 196

/-- Storage slot the Wave-6 exit mutant writes the new head into: src word
of drained exit item 7. -/
def exitItem7SrcSlot : UInt8 := 25

/-- Sanity: the pinned bytes really are what the mutations claim to cut. -/
theorem pinned_drain_bytes :
    exitRuntime.size = 458
    ∧ exitRuntime.get! exitCapIdx = 0x10
    ∧ exitRuntime.get! exitRecordSizeIdx = 0x44
    ∧ exitRuntime.get! exitHeadSlotIdx = 0x02
    ∧ exitRuntime.get! 324 = 0x02
    ∧ depositRuntime.size = 628
    ∧ depositRuntime.get! depositCapIdx = 0x40
    ∧ depositRuntime.get! 296 = 0x40
    ∧ depositRuntime.get! depositHeadSlotIdx = 0x02
    ∧ depositRuntime.get! 494 = 0x02 := by
  native_decide

/-- `PUSH1 16` → `PUSH1 8` on the over-cap clamp only. -/
def capMutatedExit : ByteArray := exitRuntime.set! exitCapIdx 0x08

/-- `PUSH1 68` → `PUSH1 64` on the system return-size multiplier only. -/
def recSizeMutatedExit : ByteArray := exitRuntime.set! exitRecordSizeIdx 0x40

/-- `PUSH1 64` → `PUSH1 32` on the deposit over-cap clamp only. -/
def capMutatedDeposit : ByteArray := depositRuntime.set! depositCapIdx 0x20

/-- `PUSH1 QUEUE_HEAD` → `PUSH1 9` on the partial-drain head store only.
The new head value `64` is written into slot 9 (last remaining word of
drained item 0) instead of slot 2. -/
def headSlotMutatedDeposit : ByteArray :=
  depositRuntime.set! depositHeadSlotIdx depositItem0LastSlot

/-- `PUSH1 QUEUE_HEAD` → `PUSH1 196` on the same deposit partial-drain head
store, retargeted onto the first word of drained deposit item 32. -/
def headSlotMutatedDepositItem32 : ByteArray :=
  depositRuntime.set! depositHeadSlotIdx depositItem32FirstSlot

/-- `PUSH1 QUEUE_HEAD` → `PUSH1 25` on the exit partial-drain head store only.
The new head value `16` is written into slot 25 (src word of drained exit
item 7) instead of slot 2. -/
def headSlotMutatedExitItem7 : ByteArray :=
  exitRuntime.set! exitHeadSlotIdx exitItem7SrcSlot

theorem mutants_differ_in_one_byte :
    capMutatedExit.size = exitRuntime.size
    ∧ capMutatedExit.get! exitCapIdx = 0x08
    ∧ recSizeMutatedExit.size = exitRuntime.size
    ∧ recSizeMutatedExit.get! exitRecordSizeIdx = 0x40
    ∧ capMutatedDeposit.size = depositRuntime.size
    ∧ capMutatedDeposit.get! depositCapIdx = 0x20
    ∧ capMutatedDeposit.get! 296 = 0x40
    ∧ headSlotMutatedDeposit.size = depositRuntime.size
    ∧ headSlotMutatedDeposit.get! depositHeadSlotIdx = depositItem0LastSlot
    ∧ headSlotMutatedDeposit.get! 494 = 0x02
    ∧ headSlotMutatedDepositItem32.size = depositRuntime.size
    ∧ headSlotMutatedDepositItem32.get! depositHeadSlotIdx = depositItem32FirstSlot
    ∧ headSlotMutatedDepositItem32.get! 494 = 0x02
    ∧ headSlotMutatedExitItem7.size = exitRuntime.size
    ∧ headSlotMutatedExitItem7.get! exitHeadSlotIdx = exitItem7SrcSlot
    ∧ headSlotMutatedExitItem7.get! 324 = 0x02 := by
  native_decide

/--
**Kill-line.** Each mutant refutes `drainFacts`, the exact conjunction
`pdrain1_bytecode_parent` (and therefore `pdrain1_forall_parent`) is
registered against. The other runtime is left pinned in each case, so
the failure is attributable to the cut byte.
-/
theorem mutant_refutes_parent :
    drainFacts depositRuntime capMutatedExit = false
    ∧ drainFacts depositRuntime recSizeMutatedExit = false
    ∧ drainFacts capMutatedDeposit exitRuntime = false
    ∧ drainFacts headSlotMutatedDeposit exitRuntime = false
    ∧ drainFacts headSlotMutatedDepositItem32 exitRuntime = false
    ∧ drainFacts depositRuntime headSlotMutatedExitItem7 = false := by
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

/--
The Wave-3 head-slot mutant's mechanism. Sixty-five queued deposits
still return 64 records and still *intend* to advance the head by 64,
but the `SSTORE` writes that `64` into slot 9 — the last remaining word
of drained item 0 — instead of into `QUEUE_HEAD`. Slot 2 therefore
stays 0, slot 9 becomes 64 instead of the distinctive leftover word,
and `staleDepositRestIs 0` is false. The empty-queue and under-cap
full drains take the reset path (`PUSH0; PUSH1 2; SSTORE` at a
different offset) and stay true.
-/
theorem head_slot_mutant_overwrites_a_drained_word :
    (let r := runDepositSystem DEPOSIT_CAP_FUEL ByteArray.empty
        (code := headSlotMutatedDeposit) (storage := depositQueue65);
      successOutSize r = 11776
        ∧ storageSlotIs r depositAddr (u256 2) (u256 0) = true
        ∧ storageSlotIs r depositAddr (u256 3) (u256 65) = true
        ∧ storageSlotIs r depositAddr (u256 depositItem0LastSlot.toNat) (u256 64) = true
        ∧ staleDepositPk1Is r 0 0x1100 = true
        ∧ staleDepositRestIs r 0 = false
        ∧ staleDepositPk1Is r 63 0x113F = true
        ∧ staleDepositPk1Is r 64 0x1140 = true)
    ∧ depositOverCapFact headSlotMutatedDeposit = false
    ∧ depositEmptyDrainFact headSlotMutatedDeposit = true
    ∧ depositFifoFact headSlotMutatedDeposit = true := by
  native_decide

/--
The Wave-6 deposit head-slot mutant's mechanism. Sixty-five queued deposits
still return 64 records, but the `SSTORE` writes the new head `64` into
slot 196 (first word of drained deposit item 32) instead of `QUEUE_HEAD`.
Slot 2 stays 0, slot 196 becomes 64, and `staleDepositPk1Is 32` is false.
`staleDepositRestIs 0`, `staleDepositRestIs 1` and `staleDepositRestIs 63`
are still true because those slots are not overwritten; the empty-queue
and under-cap full drains still take the reset path.
-/
theorem head_slot_mutant_item32_overwrites_item32_first_word :
    (let r := runDepositSystem DEPOSIT_CAP_FUEL ByteArray.empty
        (code := headSlotMutatedDepositItem32) (storage := depositQueue65);
      successOutSize r = 11776
        ∧ storageSlotIs r depositAddr (u256 2) (u256 0) = true
        ∧ storageSlotIs r depositAddr (u256 3) (u256 65) = true
        ∧ storageSlotIs r depositAddr (u256 depositItem32FirstSlot.toNat) (u256 64) = true
        ∧ staleDepositPk1Is r 0 0x1100 = true
        ∧ staleDepositRestIs r 0 = true
        ∧ staleDepositRestIs r 1 = true
        ∧ staleDepositPk1Is r 32 0x1120 = false
        ∧ staleDepositPk1Is r 63 0x113F = true
        ∧ staleDepositRestIs r 63 = true
        ∧ staleDepositPk1Is r 64 0x1140 = true)
    ∧ depositOverCapFact headSlotMutatedDepositItem32 = false
    ∧ depositEmptyDrainFact headSlotMutatedDepositItem32 = true
    ∧ depositFifoFact headSlotMutatedDepositItem32 = true := by
  native_decide

/--
The Wave-6 exit head-slot mutant's mechanism. Seventeen queued exits still
return 16 records, but the `SSTORE` writes the new head `16` into slot 25
(src word of drained exit item 7) instead of `QUEUE_HEAD`. Slot 2 stays 0,
slot 25 becomes 16, and `staleExitSrcIs 7` is false. The other stale
slots (item 0 all three words, item 15 all three words) are not
overwritten, and the empty-queue and under-cap exits still take the
reset path.
-/
theorem head_slot_mutant_item7_overwrites_item7_src :
    (let r := runExitSystem FUEL ByteArray.empty
        (code := headSlotMutatedExitItem7) (storage := exitQueue 17);
      successOutSize r = 1088
        ∧ storageSlotIs r exitAddr (u256 2) (u256 0) = true
        ∧ storageSlotIs r exitAddr (u256 3) (u256 17) = true
        ∧ storageSlotIs r exitAddr (u256 exitItem7SrcSlot.toNat) (u256 16) = true
        ∧ staleExitSrcIs r 0 = true
        ∧ staleExitPk1Is r 0 = true
        ∧ staleExitPk2Is r 0 = true
        ∧ staleExitSrcIs r 15 = true
        ∧ staleExitPk1Is r 15 = true
        ∧ staleExitPk2Is r 15 = true
        ∧ staleExitSrcIs r 7 = false
        ∧ staleExitPk1Is r 7 = true
        ∧ staleExitPk2Is r 7 = true)
    ∧ exitOverCapFact headSlotMutatedExitItem7 = false
    ∧ exitEmptyDrainFact headSlotMutatedExitItem7 = true
    ∧ exitUnderCapFifoFact headSlotMutatedExitItem7 = true := by
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
    ∧ depositOverCapFact headSlotMutatedDeposit = false
    ∧ depositOverCapFact headSlotMutatedDepositItem32 = false
    ∧ exitOverCapFact headSlotMutatedExitItem7 = false
    ∧ depositEmptyDrainFact depositRuntime = true
    ∧ depositEmptyDrainFact headSlotMutatedDeposit = true
    ∧ depositEmptyDrainFact headSlotMutatedDepositItem32 = true
    ∧ exitEmptyDrainFact exitRuntime = true
    ∧ exitEmptyDrainFact headSlotMutatedExitItem7 = true := by
  native_decide

/--
**The parent is not a sibling.** All six drain mutants leave
`PSubmit1.submitFacts` and `PControl1.controlFacts` — the conjunctions
those parents are registered against on the empty-queue / user-write
paths — fully satisfied. P-SUBMIT-1 never calls from `SYSTEM_ADDR`.
P-CONTROL-1's empty-queue `controlFacts` hold `QUEUE_HEAD = QUEUE_TAIL = 0`,
so the cap clamp is never taken, the partial-drain head stores are never
taken, and `0 * RECORD_SIZE` is still 0.
Whatever `pdrain1_bytecode_parent` is carrying, it is not carried anywhere
else in this repository.
-/
theorem drain_mutants_leave_siblings_intact :
    Eip8282.Audit.Guarantees.PSubmit1.submitFacts depositRuntime capMutatedExit = true
    ∧ Eip8282.Audit.Guarantees.PSubmit1.submitFacts depositRuntime recSizeMutatedExit = true
    ∧ Eip8282.Audit.Guarantees.PSubmit1.submitFacts capMutatedDeposit exitRuntime = true
    ∧ Eip8282.Audit.Guarantees.PSubmit1.submitFacts headSlotMutatedDeposit exitRuntime = true
    ∧ Eip8282.Audit.Guarantees.PSubmit1.submitFacts headSlotMutatedDepositItem32 exitRuntime = true
    ∧ Eip8282.Audit.Guarantees.PSubmit1.submitFacts depositRuntime headSlotMutatedExitItem7 = true
    ∧ Eip8282.Audit.Guarantees.PControl1.controlFacts depositRuntime capMutatedExit = true
    ∧ Eip8282.Audit.Guarantees.PControl1.controlFacts depositRuntime recSizeMutatedExit = true
    ∧ Eip8282.Audit.Guarantees.PControl1.controlFacts capMutatedDeposit exitRuntime = true
    ∧ Eip8282.Audit.Guarantees.PControl1.controlFacts headSlotMutatedDeposit exitRuntime = true
    ∧ Eip8282.Audit.Guarantees.PControl1.controlFacts headSlotMutatedDepositItem32 exitRuntime = true
    ∧ Eip8282.Audit.Guarantees.PControl1.controlFacts depositRuntime headSlotMutatedExitItem7 = true := by
  native_decide

end Eip8282.Tests.PDrain1Mutant

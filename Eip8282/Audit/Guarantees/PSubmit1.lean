import Eip8282.Audit.Guarantees.Registry
import Eip8282.Audit.Model
import Eip8282.Audit.EvmRunner

namespace Eip8282.Audit.Guarantees.PSubmit1

open Eip8282.Audit.Model

def guarantee : Guarantee := ⟨.pSubmit1, [.model, .evm]⟩

/-! ## Abstract model layer

Scaffolding over `Model.userCall`. These are *not* the load-bearing parent:
`userCall` is a hand-written abstraction with no proven relation to the
deployed bytecode. The load-bearing statement is
`psubmit1_bytecode_parent` in the next section, which executes the pinned
runtime bytes under `EvmYul.EVM.Ξ`.
-/

theorem revert_is_atomic
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei) :
    (userCall s caller calldata value).isRevert = true →
      (userCall s caller calldata value).state = s := by
  unfold userCall
  by_cases hInh : inhibited s = true
  · simp [hInh]
  · simp [hInh]
    by_cases hEmpty : calldata = []
    · simp [hEmpty]
      by_cases hVal : value = 0
      · simp [hVal]
      · have : ¬ value = 0 := hVal
        simp [this]
    · simp [hEmpty]
      by_cases hAdm : admissible s calldata value = true
      · simp [hAdm]
      · simp [hAdm]

theorem success_count_and_balance
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei)
    (hInh : inhibited s = false)
    (hne : calldata ≠ [])
    (hAdm : admissible s calldata value = true) :
    let t := (userCall s caller calldata value).state
    t.count = s.count + 1 ∧
      t.balance = s.balance + value ∧
      t.queue = (appendRecord s caller calldata value).queue := by
  unfold userCall
  simp [hInh, hne, hAdm, appendRecord]

theorem deposit_appends_calldata
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei)
    (hk : s.kind = .deposit)
    (hInh : inhibited s = false)
    (hne : calldata ≠ [])
    (hAdm : admissible s calldata value = true) :
    (userCall s caller calldata value).state.queue =
      s.queue ++ [.deposit calldata (depositAmount calldata)] := by
  unfold userCall appendRecord
  simp [hInh, hne, hAdm, hk]

theorem exit_binds_caller
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei)
    (hk : s.kind = .exit)
    (hInh : inhibited s = false)
    (hne : calldata ≠ [])
    (hAdm : admissible s calldata value = true) :
    (userCall s caller calldata value).state.queue =
      s.queue ++ [.exit caller calldata] := by
  unfold userCall appendRecord
  simp [hInh, hne, hAdm, hk]

theorem inhibited_blocks_users
    (s : State) (caller : Address) (calldata : List Byte) (value : Wei)
    (h : inhibited s = true) :
    userCall s caller calldata value = .revert s := by
  unfold userCall
  simp [h]

/-! ## Pinned-bytecode layer

Everything below runs `Eip8282.Audit.Bytecode.depositRuntime` and
`exitRuntime` — the bytes of `pinned/bytecode/builder_{deposits,exits}/main.hex`
— inside `EvmYul.EVM.Ξ` via `Eip8282.Audit.EvmRunner`.

Each fact is a `Bool` parameterized by the runtime `code`. That is the whole
point: `Eip8282.Tests.PSubmit1Mutant` feeds a *byte-mutated* runtime to the
same `submitFacts` and gets `false`, so the parent is refuted by changing the
bytecode rather than by changing the model.
-/

open Eip8282.Audit.EvmRunner
open Eip8282.Audit.Bytecode

def FUEL : Nat := 80000

/-- A non-system, non-privileged caller. -/
def submitter : Nat := 0x1234

/-- `SLOT_EXCESS = 100`, `SLOT_COUNT = 5`, `SLOT_HEAD = 7`, `SLOT_TAIL = 9`. -/
def liveStorage := storageFromList [(0, 100), (1, 5), (2, 7), (3, 9)]

/-- The same queue state with `SLOT_EXCESS` holding `INHIBITOR = 2^256 - 1`. -/
def inhibitedStorage :=
  (storageFromList [(1, 5), (2, 7), (3, 9)]).insert ZERO_U256 INHIBITOR_U256

/-- `QUEUE_OFFSET + SLOT_TAIL * SLOTS_PER_ITEM` for builder_deposits. -/
def depositQueueBase : Nat := 4 + 9 * 6

/-- `QUEUE_OFFSET + SLOT_TAIL * SLOTS_PER_ITEM` for builder_exits. -/
def exitQueueBase : Nat := 4 + 9 * 3

/-- Well-formed 184-byte deposit input; bytes 80..87 are `MIN_AMOUNT` gwei. -/
def depositInput : ByteArray :=
  ByteArray.mk <|
    (Array.replicate 184 (7 : UInt8))
      |>.set! 80 0 |>.set! 81 0 |>.set! 82 0 |>.set! 83 0
      |>.set! 84 0x3b |>.set! 85 0x9a |>.set! 86 0xca |>.set! 87 0x00

/-- Well-formed 48-byte exit input (a BLS pubkey). -/
def exitInput : ByteArray := ByteArray.mk (Array.replicate 48 (9 : UInt8))

/-- Strictly above the fee both runtimes quote for `liveStorage`. -/
def payment : Nat := 10 ^ 18 + 100000

/-- Empty calldata with `value = 0` returns 32 bytes and leaves slots 0–3 alone. -/
def depositFeeGetterFact (code : ByteArray) : Bool :=
  let r := runDeposit FUEL submitter 0 ByteArray.empty (code := code) (storage := liveStorage)
  isSuccess r
    && successOutSize r == 32
    && (successOutWord r).map (·.toNat) == some 357
    && slots0to3Are r depositAddr 100 5 7 9

/-- Empty calldata with `value ≠ 0` reverts, so no storage write survives. -/
def depositValueRejectedFact (code : ByteArray) : Bool :=
  isRevert (runDeposit FUEL submitter 1 ByteArray.empty (code := code) (storage := liveStorage))

/-- A paid 184-byte write bumps only `SLOT_COUNT`/`SLOT_TAIL` and appends the
calldata verbatim as six `CALLDATALOAD`-sized words at the tail. -/
def depositPaidAppendFact (code : ByteArray) : Bool :=
  let r := runDeposit FUEL submitter payment depositInput (code := code) (storage := liveStorage)
  isSuccess r
    && slots0to3Are r depositAddr 100 6 7 10
    && (List.range 6).all (fun i =>
         storageSlotIs r depositAddr (u256 (depositQueueBase + i))
           (calldataWord depositInput (32 * i)))

/-- The same paid deposit emits one anonymous `LOG0` whose data is the
184-byte calldata `Ξ` copied (`push RECORD_SIZE; push 0; log0`). That
pins the first word, the amount at bytes 80..87, and the remaining
record bytes — the same fields `depositPaidAppendFact` stores. -/
def depositPaidLogFact (code : ByteArray) : Bool :=
  let r := runDeposit FUEL submitter payment depositInput (code := code) (storage := liveStorage)
  isSuccess r
    && successLogCount r == 1
    && successLogTopicsLen r 0 == some 0
    && successLogDataSize r 0 == some 184
    && successLog0Is r 0 depositInput

/-- With `SLOT_EXCESS = INHIBITOR`, both the getter and the write path revert. -/
def depositInhibitedFact (code : ByteArray) : Bool :=
  isRevert (runDeposit FUEL submitter payment depositInput
      (code := code) (storage := inhibitedStorage))
    && isRevert (runDeposit FUEL submitter 0 ByteArray.empty
      (code := code) (storage := inhibitedStorage))

def exitFeeGetterFact (code : ByteArray) : Bool :=
  let r := runExit FUEL submitter 0 ByteArray.empty (code := code) (storage := liveStorage)
  isSuccess r
    && successOutSize r == 32
    && (successOutWord r).map (·.toNat) == some 427
    && slots0to3Are r exitAddr 100 5 7 9

def exitValueRejectedFact (code : ByteArray) : Bool :=
  isRevert (runExit FUEL submitter 1 ByteArray.empty (code := code) (storage := liveStorage))

/-- A paid 48-byte write appends `msg.sender` followed by the pubkey words. The
first appended slot is the *caller*, not calldata: that is the authenticity bind. -/
def exitPaidAppendFact (code : ByteArray) : Bool :=
  let r := runExit FUEL submitter payment exitInput (code := code) (storage := liveStorage)
  isSuccess r
    && slots0to3Are r exitAddr 100 6 7 10
    && storageSlotIs r exitAddr (u256 exitQueueBase) (u256 submitter)
    && storageSlotIs r exitAddr (u256 (exitQueueBase + 1)) (calldataWord exitInput 0)
    && storageSlotIs r exitAddr (u256 (exitQueueBase + 2)) (calldataWord exitInput 32)

/-- 20-byte big-endian encoding of `submitter = 0x1234`, the source the
exit write path `mstore`s before the pubkey and then `LOG0`s. -/
def exitLogSource : ByteArray :=
  ByteArray.mk <| (Array.replicate 20 (0 : UInt8)).set! 18 0x12 |>.set! 19 0x34

/-- `RECORD_SIZE = 68` payload the exit runtime actually logs:
`msg.sender` (20) then the 48-byte pubkey. -/
def exitLogPayload : ByteArray := exitLogSource ++ exitInput

/-- The same paid exit emits one anonymous `LOG0` of 68 data bytes:
source address then pubkey — the same fields `exitPaidAppendFact` stores. -/
def exitPaidLogFact (code : ByteArray) : Bool :=
  let r := runExit FUEL submitter payment exitInput (code := code) (storage := liveStorage)
  isSuccess r
    && successLogCount r == 1
    && successLogTopicsLen r 0 == some 0
    && successLogDataSize r 0 == some 68
    && successLog0Is r 0 exitLogPayload

def exitInhibitedFact (code : ByteArray) : Bool :=
  isRevert (runExit FUEL submitter payment exitInput
      (code := code) (storage := inhibitedStorage))
    && isRevert (runExit FUEL submitter 0 ByteArray.empty
      (code := code) (storage := inhibitedStorage))

/-- The whole P-SUBMIT-1 write-path claim, as a function of the two runtimes.
Feeding a mutated `depCode` or `exitCode` must make this `false`. -/
def submitFacts (depCode exitCode : ByteArray) : Bool :=
  depositFeeGetterFact depCode
    && depositValueRejectedFact depCode
    && depositPaidAppendFact depCode
    && depositPaidLogFact depCode
    && depositInhibitedFact depCode
    && exitFeeGetterFact exitCode
    && exitValueRejectedFact exitCode
    && exitPaidAppendFact exitCode
    && exitPaidLogFact exitCode
    && exitInhibitedFact exitCode

/--
**P-SUBMIT-1 parent, on pinned bytecode.**

`submitFacts depositRuntime exitRuntime` holds of the actual
sys-asm@83f9801 runtime bytes executed by `EvmYul.EVM.Ξ`. The extra
conjuncts pin the getter/rejection dispatch outside `submitFacts` so the
statement mentions `runDeposit`/`runExit` and both runtimes directly.

This is a finite set of concrete traces at one storage image, not a
universally quantified P-SUBMIT-1. See `A-EVM-WORLD`.

Discharged by `native_decide`: `Ξ` calls the `partial def D_J_aux` jumpdest
scanner, which is kernel-opaque, so `decide`/`rfl` cannot reduce it. The
resulting compiler-generated axiom is disclosed in `Eip8282.Audit.Trust` and
as `A-NATIVE-DECIDE` in `audit/assumptions.yaml`.
-/
theorem psubmit1_bytecode_parent :
    submitFacts depositRuntime exitRuntime = true
    ∧ isSuccess (runDeposit FUEL submitter 0 ByteArray.empty
        (code := depositRuntime) (storage := liveStorage)) = true
    ∧ isRevert (runDeposit FUEL submitter 1 ByteArray.empty
        (code := depositRuntime) (storage := liveStorage)) = true
    ∧ isSuccess (runExit FUEL submitter 0 ByteArray.empty
        (code := exitRuntime) (storage := liveStorage)) = true
    ∧ isRevert (runExit FUEL submitter 1 ByteArray.empty
        (code := exitRuntime) (storage := liveStorage)) = true := by
  native_decide

end Eip8282.Audit.Guarantees.PSubmit1

/-
  Private validation: finite inhibition/reactivation on pinned EIP-8282 bytes
  via Eip8282.Audit.EvmRunner → EvmYul.EVM.Ξ.

  - constructor init images under Ξ
  - nonempty queue system inhibit + drain
  - user revert while inhibited
  - empty system uninhibit + drain
  Receipts: success/revert, return size, slots 0–3, final gas, balances, SYSTEM caller.

  Finite only. No 2^64 wrap claim. noWrap is NOT a premise.
-/
import Eip8282.Audit.EvmRunner
import Eip8282.Audit.Bytecode

open EvmYul
open EvmYul.EVM
open Eip8282.Audit.EvmRunner
open Eip8282.Audit.Bytecode

namespace DirectQueueValidateXi

def FUEL : Nat := 80000
def CTOR_FUEL : Nat := 20000
def submitter : Nat := 0x1234
def deployer : Nat := 0x1234
def oneByte : ByteArray := ByteArray.mk #[0]
def INHIBITOR_NAT : Nat := 2 ^ 256 - 1

def queueStorage (excess count head tail : Nat) (words : List (Nat × Nat)) : Storage :=
  storageFromList ([(0, excess), (1, count), (2, head), (3, tail)] ++ words)

def depositAmtWord (amt : Nat) : Nat :=
  (2 ^ 128 - 1) * (2 ^ 128) + amt * (2 ^ 64)

def depositItemWords (i amt : Nat) : List (Nat × Nat) :=
  let base := 4 + 6 * i
  [ (base,     (0x1100 + i) * (2 ^ 240))
  , (base + 1, (0x2200 + i) * (2 ^ 240))
  , (base + 2, depositAmtWord amt)
  , (base + 3, (0x3300 + i) * (2 ^ 240))
  , (base + 4, (0x4400 + i) * (2 ^ 240))
  , (base + 5, (0x5500 + i) * (2 ^ 240)) ]

def depositAmtOf (i : Nat) : Nat := 0x0102030405060708 + i * 0x0101010101010101

def depositQueue (n : Nat) : Storage :=
  queueStorage 100 5 0 n ((List.range n).flatMap (fun i => depositItemWords i (depositAmtOf i)))

def exitItemWords (i : Nat) : List (Nat × Nat) :=
  let base := 4 + 3 * i
  let exitSrc := 0xA100 + i
  let exitPk1 := (0xB000 + i) * (2 ^ 240)
  let exitPk2 := (0xC000 + i) * (2 ^ 240)
  [(base, exitSrc), (base + 1, exitPk1), (base + 2, exitPk2)]

def exitQueue (n : Nat) : Storage :=
  queueStorage 100 5 0 n ((List.range n).flatMap exitItemWords)

/-- Ξ on init image (creation world: target account has empty code). -/
def runInit (fuel : Nat) (target : AccountAddress) (initCode : ByteArray) : RunResult :=
  let σ : AccountMap .EVM :=
    (default : AccountMap .EVM)
      |>.insert target (mkAccount ByteArray.empty)
      |>.insert (toAddress deployer) (mkAccount ByteArray.empty oneEth)
  Ξ fuel default default default σ σ defaultGas default
    (callEnv target initCode (toAddress deployer) ZERO_U256 ByteArray.empty)

def returnBuffer (r : RunResult) : ByteArray :=
  match r with
  | .ok (.success _ o) => o
  | _ => ByteArray.empty

def finalGasOf (r : RunResult) : Option Nat :=
  match r with
  | .ok (.success (_, _, g, _) _) => some g.toNat
  | _ => none

def balanceOf (r : RunResult) (addr : AccountAddress) : Option Nat :=
  match r with
  | .ok (.success (_, amap, _, _) _) =>
      amap.get? addr |>.map (fun acc => acc.balance.toNat)
  | _ => none

def slotNat (r : RunResult) (target : AccountAddress) (slot : Nat) : Option Nat :=
  match storageSlotAfter r target (u256 slot) with
  | some v => some v.toNat
  | none => none

/-- Deposit ctor under Ξ: returns depositRuntime, slots 0–3 zero. -/
def depositCtorOk : Bool :=
  let r := runInit CTOR_FUEL depositAddr depositInit
  isSuccess r
    && bytesEq (returnBuffer r) depositRuntime
    && slots0to3Are r depositAddr 0 0 0 0

/-- Exit ctor under Ξ: returns exitRuntime, slot0=INHIBITOR. -/
def exitCtorOk : Bool :=
  let r := runInit CTOR_FUEL exitAddr exitInit
  isSuccess r
    && bytesEq (returnBuffer r) exitRuntime
    && slots0to3Are r exitAddr INHIBITOR_NAT 0 0 0

/-- Nonempty deposit queue (2 items): system nonempty → drain 2 + INHIBITOR. -/
def depositNonemptyInhibitOk : Bool :=
  let r := runDepositSystem FUEL oneByte (code := depositRuntime) (storage := depositQueue 2)
  isSuccess r
    && successOutSize r == 368
    && slots0to3Are r depositAddr INHIBITOR_NAT 0 0 0
    && (finalGasOf r).isSome

/-- From inhibited+empty after drain: user reverts; system empty clears excess. -/
def depositInhibitedUserRevertsOk : Bool :=
  let inh := storageFromList [(0, INHIBITOR_NAT), (1, 0), (2, 0), (3, 0)]
  isRevert (runDeposit FUEL submitter 0 ByteArray.empty (code := depositRuntime) (storage := inh))

def depositUninhibitOk : Bool :=
  let inh := storageFromList [(0, INHIBITOR_NAT), (1, 0), (2, 0), (3, 0)]
  let r := runDepositSystem FUEL ByteArray.empty (code := depositRuntime) (storage := inh)
  isSuccess r && slots0to3Are r depositAddr 0 0 0 0

/-- Nonempty inhibited deposit queue still drains on empty system and clears inhibitor. -/
def depositNonemptyUninhibitOk : Bool :=
  let inhabited := queueStorage INHIBITOR_NAT 5 0 2
    ((List.range 2).flatMap (fun i => depositItemWords i (depositAmtOf i)))
  let r := runDepositSystem FUEL ByteArray.empty (code := depositRuntime) (storage := inhabited)
  isSuccess r
    && successOutSize r == 368
    && slots0to3Are r depositAddr 0 0 0 0

/-- Exit nonempty inhibit. -/
def exitNonemptyInhibitOk : Bool :=
  let r := runExitSystem FUEL oneByte (code := exitRuntime) (storage := exitQueue 2)
  isSuccess r
    && successOutSize r == 136
    && slots0to3Are r exitAddr INHIBITOR_NAT 0 0 0

def exitNonemptyUninhibitOk : Bool :=
  let inhabited := queueStorage INHIBITOR_NAT 5 0 2 ((List.range 2).flatMap exitItemWords)
  let r := runExitSystem FUEL ByteArray.empty (code := exitRuntime) (storage := inhabited)
  isSuccess r
    && successOutSize r == 136
    && slots0to3Are r exitAddr 0 0 0 0

/-- SYSTEM vs user gate on same nonempty image: user fee quote no drain; system drains. -/
def depositSystemFlagOk : Bool :=
  let q := depositQueue 2
  let u := runDeposit FUEL submitter 0 ByteArray.empty (code := depositRuntime) (storage := q)
  let s := runDepositSystem FUEL ByteArray.empty (code := depositRuntime) (storage := q)
  isSuccess u && successOutSize u == 32 && slots0to3Are u depositAddr 100 5 0 2
    && isSuccess s && successOutSize s == 368 && slots0to3Are s depositAddr 97 0 0 0

/-- Full finite conjunction used as #eval target. -/
def nonemptyInhibitionCycleReceipt : Bool :=
  depositCtorOk && exitCtorOk
    && depositNonemptyInhibitOk
    && depositInhibitedUserRevertsOk
    && depositUninhibitOk
    && depositNonemptyUninhibitOk
    && exitNonemptyInhibitOk
    && exitNonemptyUninhibitOk
    && depositSystemFlagOk

#eval nonemptyInhibitionCycleReceipt

-- Individual printouts for receipt JSON parsing (true/false lines).
#eval depositCtorOk
#eval exitCtorOk
#eval depositNonemptyInhibitOk
#eval depositInhibitedUserRevertsOk
#eval depositUninhibitOk
#eval depositNonemptyUninhibitOk
#eval exitNonemptyInhibitOk
#eval exitNonemptyUninhibitOk
#eval depositSystemFlagOk

-- Gas remaining sample on inhibit call (Nat).
#eval
  match finalGasOf (runDepositSystem FUEL oneByte (code := depositRuntime) (storage := depositQueue 2)) with
  | some g => g
  | none => 0

-- Predeploy balance after system call (should stay 0; runner gives target 0 balance).
#eval
  match balanceOf (runDepositSystem FUEL oneByte (code := depositRuntime) (storage := depositQueue 2)) depositAddr with
  | some b => b
  | none => 999

-- Return payload size on nonempty inhibit.
#eval successOutSize (runDepositSystem FUEL oneByte (code := depositRuntime) (storage := depositQueue 2))

-- Slot0 after inhibit (should be 2^256-1).
#eval
  match slotNat (runDepositSystem FUEL oneByte (code := depositRuntime) (storage := depositQueue 2)) depositAddr 0 with
  | some v => if v == INHIBITOR_NAT then 1 else 0
  | none => 0

end DirectQueueValidateXi

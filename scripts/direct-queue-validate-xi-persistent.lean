/-
  Finite EvmRunner/Ξ multi-step receipt: nonempty-after-drain *persistent*
  inhibition (HEAD/TAIL remain live under INHIBITOR).

  Deposit cap = 64. Queue of 70 + system nonempty calldata:
    drains 64, leaves head=64 tail=70, EXCESS=INHIBITOR, COUNT=0.
  That is NOT a two-item full drain that resets (0,0).

  Labels: #eval facts are testé (finite traces), NOT prouvé ∀.
  No 2^64 wrap claim. noWrap is NOT a premise. No TAIL<2^64 guard added.
-/
import Eip8282.Audit.EvmRunner
import Eip8282.Audit.Bytecode

open EvmYul
open EvmYul.EVM
open Eip8282.Audit.EvmRunner
open Eip8282.Audit.Bytecode

namespace DirectQueueValidatePersistent

def FUEL : Nat := 300000  -- enough for 64-record deposit drain
def FUEL_SMALL : Nat := 80000
def submitter : Nat := 0x1234
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

-- 70 queued deposits: first system drain is partial (cap 64).
def depositQueue70 : Storage :=
  queueStorage 100 5 0 70 ((List.range 70).flatMap (fun i => depositItemWords i (depositAmtOf i)))

def exitItemWords (i : Nat) : List (Nat × Nat) :=
  let base := 4 + 3 * i
  [(base, 0xA100 + i), (base + 1, (0xB000 + i) * (2 ^ 240)), (base + 2, (0xC000 + i) * (2 ^ 240))]

-- 20 queued exits: first system drain partial (cap 16) → head=16 tail=20.
def exitQueue20 : Storage :=
  queueStorage 100 5 0 20 ((List.range 20).flatMap exitItemWords)

def slotNat (r : RunResult) (target : AccountAddress) (slot : Nat) : Nat :=
  match storageSlotAfter r target (u256 slot) with
  | some v => v.toNat
  | none => 999999  -- sentinel: call did not succeed / missing

def finalGas (r : RunResult) : Nat :=
  match r with
  | .ok (.success (_, _, g, _) _) => g.toNat
  | .ok (.revert g _) => g.toNat
  | _ => 0

def outSize (r : RunResult) : Nat := successOutSize r

def okSucc (r : RunResult) : Nat := if isSuccess r then 1 else 0
def okRev (r : RunResult) : Nat := if isRevert r then 1 else 0

-- Encode a step snapshot as a Nat list printed via #eval for JSON harvest:   [okSucc, okRev, outSize, slot0, count, head, tail, gas]   slot0 is 1 if INHIBITOR else the natural value when small, or 2 for "other large".
def slot0Tag (r : RunResult) (target : AccountAddress) : Nat :=
  let v := slotNat r target 0
  if v == INHIBITOR_NAT then 1  -- INHIBITOR
  else if v == 999999 then 9    -- missing
  else if v < 1000 then v       -- small excess
  else 2                        -- other

def snap (r : RunResult) (target : AccountAddress) : List Nat :=
  [ okSucc r
  , okRev r
  , outSize r
  , slot0Tag r target
  , slotNat r target 1  -- count
  , slotNat r target 2  -- head
  , slotNat r target 3  -- tail
  , finalGas r
  ]

def snapOk (r : RunResult) (target : AccountAddress)
    (succ rev out s0 c h t : Nat) : Bool :=
  let s := snap r target
  s == [succ, rev, out, s0, c, h, t, s.getD 7 0]
    && (s.getD 7 0 > 0)  -- gas observed

-- For equality we check structural fields except gas (gas just must be positive).
def fieldsOk (r : RunResult) (target : AccountAddress)
    (succ rev out s0 c h t : Nat) : Bool :=
  okSucc r == succ
    && okRev r == rev
    && outSize r == out
    && slot0Tag r target == s0
    && slotNat r target 1 == c
    && slotNat r target 2 == h
    && slotNat r target 3 == t
    && finalGas r > 0

-- ## Deposit persistent path

-- Step D0 initial image is depositQueue70 — not executed; documented in JSON.

-- D1: system nonempty on 70-queue → partial drain + INHIBITOR, head=64 tail=70.
def d1 : RunResult :=
  runDepositSystem FUEL oneByte (code := depositRuntime) (storage := depositQueue70)

def d1Ok : Bool :=
  fieldsOk d1 depositAddr 1 0 (64 * 184) 1 0 64 70

-- Storage after D1: inhibited, nonempty pointers.
def storageAfterD1 : Storage :=
  queueStorage INHIBITOR_NAT 0 64 70
    ((List.range 70).flatMap (fun i => depositItemWords i (depositAmtOf i)))

-- D2: user append while inhibited + nonempty queue → revert; no storage read on fail     so we only check isRevert + gas.
def d2 : RunResult :=
  runDeposit FUEL_SMALL submitter 0 ByteArray.empty (code := depositRuntime) (storage := storageAfterD1)

def d2Ok : Bool := isRevert d2 && finalGas d2 > 0

-- D3: empty system while inhibited + nonempty → drain remaining 6, clear excess, reset 0,0.
def d3 : RunResult :=
  runDepositSystem FUEL ByteArray.empty (code := depositRuntime) (storage := storageAfterD1)

def d3Ok : Bool :=
  fieldsOk d3 depositAddr 1 0 (6 * 184) 0 0 0 0

-- D4: after clear, empty system on zero queue is idle success.
def storageAfterD3 : Storage := queueStorage 0 0 0 0 []

def d4 : RunResult :=
  runDepositSystem FUEL_SMALL ByteArray.empty (code := depositRuntime) (storage := storageAfterD3)

def d4Ok : Bool := fieldsOk d4 depositAddr 1 0 0 0 0 0 0

-- Contrast: two-item full drain+inhibit resets (0,0) — NOT the persistent cycle.
def depositQueue2 : Storage :=
  queueStorage 100 5 0 2 ((List.range 2).flatMap (fun i => depositItemWords i (depositAmtOf i)))

def twoItemFullDrain : RunResult :=
  runDepositSystem FUEL_SMALL oneByte (code := depositRuntime) (storage := depositQueue2)

def twoItemIsFullReset : Bool :=
  fieldsOk twoItemFullDrain depositAddr 1 0 (2 * 184) 1 0 0 0

def twoItemIsNotPersistent : Bool :=
  twoItemIsFullReset
    && !(slotNat twoItemFullDrain depositAddr 2 == 64)  -- head not 64
    && slotNat twoItemFullDrain depositAddr 2 == 0
    && slotNat twoItemFullDrain depositAddr 3 == 0

-- ## Exit persistent path (cap 16, queue 20)

def e1 : RunResult :=
  runExitSystem FUEL_SMALL oneByte (code := exitRuntime) (storage := exitQueue20)

def e1Ok : Bool :=
  fieldsOk e1 exitAddr 1 0 (16 * 68) 1 0 16 20

def storageAfterE1 : Storage :=
  queueStorage INHIBITOR_NAT 0 16 20 ((List.range 20).flatMap exitItemWords)

def e2 : RunResult :=
  runExit FUEL_SMALL submitter 0 ByteArray.empty (code := exitRuntime) (storage := storageAfterE1)

def e2Ok : Bool := isRevert e2 && finalGas e2 > 0

def e3 : RunResult :=
  runExitSystem FUEL_SMALL ByteArray.empty (code := exitRuntime) (storage := storageAfterE1)

def e3Ok : Bool :=
  fieldsOk e3 exitAddr 1 0 (4 * 68) 0 0 0 0

-- Conjunction: persistent nonempty-after-drain inhibition cycle (finite, testé).
def persistentInhibitionCycleOk : Bool :=
  d1Ok && d2Ok && d3Ok && d4Ok
    && e1Ok && e2Ok && e3Ok
    && twoItemIsNotPersistent

#eval persistentInhibitionCycleOk

-- Per-step field dumps for receipt harvest (8 nats each, then booleans).
-- D1 snap fields:
#eval okSucc d1
#eval okRev d1
#eval outSize d1
#eval slot0Tag d1 depositAddr
#eval slotNat d1 depositAddr 1
#eval slotNat d1 depositAddr 2
#eval slotNat d1 depositAddr 3
#eval finalGas d1
#eval (d1Ok)

-- D2 (revert): succ, rev, gas only meaningful
#eval okSucc d2
#eval okRev d2
#eval finalGas d2
#eval (d2Ok)

-- D3
#eval okSucc d3
#eval okRev d3
#eval outSize d3
#eval slot0Tag d3 depositAddr
#eval slotNat d3 depositAddr 1
#eval slotNat d3 depositAddr 2
#eval slotNat d3 depositAddr 3
#eval finalGas d3
#eval (d3Ok)

-- D4
#eval okSucc d4
#eval okRev d4
#eval outSize d4
#eval slot0Tag d4 depositAddr
#eval slotNat d4 depositAddr 1
#eval slotNat d4 depositAddr 2
#eval slotNat d4 depositAddr 3
#eval finalGas d4
#eval (d4Ok)

-- E1
#eval okSucc e1
#eval okRev e1
#eval outSize e1
#eval slot0Tag e1 exitAddr
#eval slotNat e1 exitAddr 1
#eval slotNat e1 exitAddr 2
#eval slotNat e1 exitAddr 3
#eval finalGas e1
#eval (e1Ok)

-- E2
#eval okSucc e2
#eval okRev e2
#eval finalGas e2
#eval (e2Ok)

-- E3
#eval okSucc e3
#eval okRev e3
#eval outSize e3
#eval slot0Tag e3 exitAddr
#eval slotNat e3 exitAddr 1
#eval slotNat e3 exitAddr 2
#eval slotNat e3 exitAddr 3
#eval finalGas e3
#eval (e3Ok)

-- two-item contrast
#eval okSucc twoItemFullDrain
#eval outSize twoItemFullDrain
#eval slot0Tag twoItemFullDrain depositAddr
#eval slotNat twoItemFullDrain depositAddr 2
#eval slotNat twoItemFullDrain depositAddr 3
#eval (twoItemIsNotPersistent)

end DirectQueueValidatePersistent

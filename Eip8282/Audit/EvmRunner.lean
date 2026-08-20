import EvmYul.EVM.Semantics
import EvmYul.EVM.State
import EvmYul.State.Account
import EvmYul.State.ExecutionEnv
import EvmYul.Maps.AccountMap
import Eip8282.Audit.Bytecode

/-!
Minimal EVMYulLean driver for the pinned EIP-8282 runtimes.

`run` is `EvmYul.EVM.Ξ` on a world that contains only the target predeploy
(with a caller-supplied storage image) and the caller, who holds `value`
plus a 1 ETH stipend. This is the execution plane the guarantees must use.
It is not itself a guarantee.

The runtime code is an explicit parameter of every runner, defaulting to the
pinned bytes of `Eip8282.Audit.Bytecode`. That is what lets a bytecode mutant
be fed to exactly the same statement a guarantee is registered against.
-/

namespace Eip8282.Audit.EvmRunner

open EvmYul
open EvmYul.EVM
open Eip8282.Audit.Bytecode

def toAddress (n : Nat) : AccountAddress := AccountAddress.ofNat n

/-- `UInt256.ofNat`, re-exported so callers need not `open EvmYul` (which would
make `Storage` and `State` ambiguous against `Eip8282.Audit.Model`). -/
def u256 (n : Nat) : UInt256 := UInt256.ofNat n

def depositAddr : AccountAddress := toAddress depositAddress
def exitAddr : AccountAddress := toAddress exitAddress

/-- `SYSTEM_ADDR` of the pinned runtimes. The first four instructions of both
runtimes are `CALLER; PUSH20 SYSTEM_ADDR; EQ; JUMPI @read_requests`, so this
address is the sole key to the system subroutine. -/
def sysAddr : AccountAddress := toAddress systemAddress

def ZERO_U256 : UInt256 := UInt256.ofNat 0
def INHIBITOR_U256 : UInt256 := UInt256.ofNat ((2 ^ 256) - 1)
def defaultGas : UInt256 := UInt256.ofNat 30000000
def oneEth : UInt256 := UInt256.ofNat (10 ^ 18)

def mkAccount (code : ByteArray) (balance : UInt256 := ZERO_U256)
    (storage : Storage := default) : Account .EVM :=
  { nonce := ZERO_U256
    balance := balance
    storage := storage
    tstorage := default
    code := code }

def storageFromList (pairs : List (Nat × Nat)) : Storage :=
  pairs.foldl (fun acc (k, v) => acc.insert (UInt256.ofNat k) (UInt256.ofNat v)) default

def worldWith
    (target : AccountAddress) (code : ByteArray)
    (caller : AccountAddress) (callerBalance : UInt256)
    (storage : Storage := default) : AccountMap .EVM :=
  let empty : AccountMap .EVM := default
  empty.insert target (mkAccount code ZERO_U256 storage)
    |>.insert caller (mkAccount ByteArray.empty callerBalance)

def callEnv
    (target : AccountAddress) (code : ByteArray)
    (caller : AccountAddress) (value : UInt256) (calldata : ByteArray)
    : ExecutionEnv .EVM :=
  { codeOwner := target
    sender := caller
    source := caller
    weiValue := value
    calldata := calldata
    code := code
    gasPrice := 0
    header := default
    depth := 0
    perm := true
    blobVersionedHashes := [] }

abbrev RunResult :=
  Except EVM.ExecutionException
    (ExecutionResult
      (Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate))

/-- Execute `code` at `target` as a message call from `caller`, via `EVM.Ξ`. -/
def run
    (fuel : Nat)
    (target : AccountAddress) (code : ByteArray)
    (caller : AccountAddress) (value : UInt256) (calldata : ByteArray)
    (gas : UInt256 := defaultGas)
    (storage : Storage := default)
    : RunResult :=
  let σ := worldWith target code caller (value + oneEth) storage
  Ξ fuel default default default σ σ gas default
    (callEnv target code caller value calldata)

/-- Non-system call on the builder-deposits runtime. `code` defaults to the pin. -/
def runDeposit (fuel : Nat) (caller : Nat) (value : Nat) (calldata : ByteArray)
    (code : ByteArray := depositRuntime) (storage : Storage := default) : RunResult :=
  run fuel depositAddr code (toAddress caller) (UInt256.ofNat value) calldata
    (storage := storage)

/-- Non-system call on the builder-exits runtime. `code` defaults to the pin. -/
def runExit (fuel : Nat) (caller : Nat) (value : Nat) (calldata : ByteArray)
    (code : ByteArray := exitRuntime) (storage : Storage := default) : RunResult :=
  run fuel exitAddr code (toAddress caller) (UInt256.ofNat value) calldata
    (storage := storage)

/-- System call on the builder-deposits runtime: same `run`, caller `sysAddr`,
zero value. Only the caller distinguishes it from `runDeposit`. -/
def runDepositSystem (fuel : Nat) (calldata : ByteArray)
    (code : ByteArray := depositRuntime) (storage : Storage := default) : RunResult :=
  run fuel depositAddr code sysAddr ZERO_U256 calldata (storage := storage)

/-- System call on the builder-exits runtime. -/
def runExitSystem (fuel : Nat) (calldata : ByteArray)
    (code : ByteArray := exitRuntime) (storage : Storage := default) : RunResult :=
  run fuel exitAddr code sysAddr ZERO_U256 calldata (storage := storage)

def isRevert (res : RunResult) : Bool :=
  match res with
  | .ok (.revert _ _) => true
  | _ => false

def isSuccess (res : RunResult) : Bool :=
  match res with
  | .ok (.success _ _) => true
  | _ => false

def successOutSize (res : RunResult) : Nat :=
  match res with
  | .ok (.success _ o) => o.size
  | _ => 0

/-- Byte `i` of a successful return buffer equals `b`. False on revert or OOB. -/
def successOutByteIs (res : RunResult) (i : Nat) (b : Nat) : Bool :=
  match res with
  | .ok (.success _ o) => i < o.size && (o.get! i).toNat == b
  | _ => false

/-- Big-endian value of a successful 32-byte return buffer. -/
def successOutWord (res : RunResult) : Option UInt256 :=
  match res with
  | .ok (.success _ o) =>
      if o.size = 32 then
        some (UInt256.ofNat (o.foldl (fun acc b => acc * 256 + b.toNat) 0))
      else none
  | _ => none

/-- Post-state storage slot of `target`; `none` unless the call succeeded. -/
def storageSlotAfter (res : RunResult) (target : AccountAddress) (slot : UInt256) :
    Option UInt256 :=
  match res with
  | .ok (.success (_, amap, _, _) _) =>
      amap.get? target |>.map (fun acc => acc.storage.getD slot ZERO_U256)
  | _ => none

def storageSlotIs (res : RunResult) (target : AccountAddress) (slot : UInt256)
    (expected : UInt256) : Bool :=
  match storageSlotAfter res target slot with
  | some v => v == expected
  | none => false

/-- `CALLDATALOAD` semantics: 32-byte big-endian read of `b` at `off`, zero padded. -/
def calldataWord (b : ByteArray) (off : Nat) : UInt256 :=
  UInt256.ofNat <|
    (List.range 32).foldl
      (fun acc i => acc * 256 + (if off + i < b.size then (b.get! (off + i)).toNat else 0)) 0

/-- Slots 0–3 of `target` after `res` equal the four given values. -/
def slots0to3Are (res : RunResult) (target : AccountAddress) (s0 s1 s2 s3 : Nat) : Bool :=
  storageSlotIs res target (UInt256.ofNat 0) (UInt256.ofNat s0) &&
  storageSlotIs res target (UInt256.ofNat 1) (UInt256.ofNat s1) &&
  storageSlotIs res target (UInt256.ofNat 2) (UInt256.ofNat s2) &&
  storageSlotIs res target (UInt256.ofNat 3) (UInt256.ofNat s3)

end Eip8282.Audit.EvmRunner

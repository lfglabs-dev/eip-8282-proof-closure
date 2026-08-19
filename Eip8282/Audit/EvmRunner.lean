/-!
Minimal EVMYulLean driver for the pinned EIP-8282 runtimes.

`run` is `EVM.Ξ` on a world that contains only the target predeploy, with
the caller's account holding `value` wei. This is the execution plane the
three guarantees must use. It is not itself a guarantee.
-/

import EvmYul.EVM.Semantics
import EvmYul.EVM.State
import EvmYul.State.Account
import EvmYul.State.ExecutionEnv
import EvmYul.Maps.AccountMap
import Eip8282.Audit.Bytecode

namespace Eip8282.Audit.EvmRunner

open EvmYul
open EvmYul.EVM
open Eip8282.Audit.Bytecode

def toAddress (n : Nat) : AccountAddress := AccountAddress.ofUInt256 ⟨n⟩

def depositAddr : AccountAddress := toAddress depositAddress
def exitAddr : AccountAddress := toAddress exitAddress
def systemAddr : AccountAddress := toAddress systemAddress

def mkAccount (code : ByteArray) (balance : UInt256 := ⟨0⟩) : Account .EVM :=
  { nonce := ⟨0⟩
    balance := balance
    storage := default
    tstorage := default
    code := code }

def worldWith
    (target : AccountAddress) (code : ByteArray)
    (caller : AccountAddress) (callerBalance : UInt256) : AccountMap .EVM :=
  let empty : AccountMap .EVM := default
  empty.insert target (mkAccount code)
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

/-- Execute `code` at `target` as a message call from `caller`. -/
def run
    (fuel : Nat)
    (target : AccountAddress) (code : ByteArray)
    (caller : AccountAddress) (value : UInt256) (calldata : ByteArray)
    (gas : UInt256 := ⟨30000000⟩)
    : Except EVM.ExecutionException
        (ExecutionResult
          (Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate)) :=
  let σ := worldWith target code caller (value + ⟨10 ^ 18⟩)
  Ξ fuel default default default σ σ gas default
    (callEnv target code caller value calldata)

def runDeposit (fuel : Nat) (caller : Nat) (value : Nat) (calldata : ByteArray) :=
  run fuel depositAddr depositRuntime (toAddress caller) ⟨value⟩ calldata

def runExit (fuel : Nat) (caller : Nat) (value : Nat) (calldata : ByteArray) :=
  run fuel exitAddr exitRuntime (toAddress caller) ⟨value⟩ calldata

def runDepositSystem (fuel : Nat) (calldata : ByteArray) :=
  run fuel depositAddr depositRuntime systemAddr ⟨0⟩ calldata

def runExitSystem (fuel : Nat) (calldata : ByteArray) :=
  run fuel exitAddr exitRuntime systemAddr ⟨0⟩ calldata

end Eip8282.Audit.EvmRunner

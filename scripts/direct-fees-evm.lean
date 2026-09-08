import Eip8282.Audit.EvmRunner

open EvmYul EvmYul.EVM Eip8282.Audit Eip8282.Audit.Bytecode Eip8282.Audit.EvmRunner

def gasLeft : RunResult → Option Nat
  | .ok (.success (_, _, g, _) _) => some g.toNat
  | .ok (.revert g _) => some g.toNat
  | _ => none

def status : RunResult → String
  | .ok (.success _ _) => "success"
  | .ok (.revert _ _) => "revert"
  | .error _ => "exception"

def outputWordNat (r : RunResult) : Option Nat := (successOutWord r).map UInt256.toNat

def outputEquals (r : RunResult) (expected : ByteArray) : Bool :=
  match r with
  | .ok (.success _ output) => bytesEq output expected
  | _ => false

def runCtor (kind : String) (fuel gas : Nat) : IO Unit := do
  let init := if kind = "deposit" then depositInit else exitInit
  let runtime := if kind = "deposit" then depositRuntime else exitRuntime
  let target := if kind = "deposit" then depositAddr else exitAddr
  let r := run fuel target init (toAddress 0x1234) ZERO_U256 ByteArray.empty (u256 gas)
  let used := (gasLeft r).map (fun left => gas - left)
  IO.println s!"kind={kind}-ctor calldata=0 value=0 fuel={fuel} gas={gas} status={status r} gas_left={repr (gasLeft r)} gas_used={repr used} output_size={successOutSize r} output_equals_runtime={outputEquals r runtime} slot0={repr (storageSlotAfter r target (u256 0) |>.map UInt256.toNat)}"

def runCase (kind : String) (excess count value calldataSize fuel gas : Nat) : IO Unit := do
  let storage := storageFromList [(0, excess), (1, count), (2, 0), (3, 0)]
  let calldata := ByteArray.mk (Array.replicate calldataSize 0)
  let r := if kind = "deposit" then
      run fuel depositAddr depositRuntime (toAddress 0x1234) (u256 value) calldata (u256 gas) storage
    else
      run fuel exitAddr exitRuntime (toAddress 0x1234) (u256 value) calldata (u256 gas) storage
  let used := (gasLeft r).map (fun left => gas - left)
  IO.println s!"kind={kind} excess={excess} count={count} value={value} calldata={calldataSize} fuel={fuel} gas={gas} status={status r} gas_left={repr (gasLeft r)} gas_used={repr used} output_word={repr (outputWordNat r)}"

def main : IO Unit := do
  -- Init-code execution is diagnostic: `run` does not model the CREATE envelope.
  runCtor "deposit" 200000 30000000
  runCtor "exit" 200000 30000000
  -- Getter calls isolate fee calculation. Exit submission calls test the 1-wei boundary.
  runCase "exit" 1608 0 0 0 200000 30000000
  runCase "exit" 1620 0 0 0 200000 30000000
  runCase "exit" 1620 0 243056981773394081136356734028591621772928 48 200000 30000000
  runCase "exit" 1620 0 243056981773394081136356734028591621772929 48 200000 30000000
  runCase "exit" 2893 0 0 0 300000 30000000
  runCase "deposit" 2893 0 0 0 300000 30000000

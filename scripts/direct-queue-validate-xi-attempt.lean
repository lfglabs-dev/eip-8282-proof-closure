/-
  Private validation attempt: one finite inhibition cycle on pinned deposit
  runtime via Eip8282.Audit.EvmRunner (EvmYul.EVM.Ξ).

  NOT a Model/AdmissibleCall/Trust/YAML edit. Private artifact only.
  Finite traces only; no 2^64 wrap claim.
-/
import Eip8282.Audit.EvmRunner
import Eip8282.Audit.Bytecode

open Eip8282.Audit.EvmRunner
open Eip8282.Audit.Bytecode

namespace DirectQueueValidate

def FUEL : Nat := 80000
def oneByte : ByteArray := ByteArray.mk #[1]
def submitter : Nat := 0xabc

/-- Empty queue, excess=0,count=0: nonempty system calldata latches INHIBITOR. -/
def inhibitEmpty : Bool :=
  let r := runDepositSystem FUEL oneByte (code := depositRuntime) (storage := default)
  isSuccess r
    && storageSlotIs r depositAddr (u256 0) INHIBITOR_U256
    && storageSlotIs r depositAddr (u256 1) (u256 0)

/-- From inhibited empty image, user reverts; empty system clears excess to 0. -/
def uninhibitAndGate : Bool :=
  let inh := storageFromList [(0, (2 ^ 256) - 1)]
  let user := runDeposit FUEL submitter 0 ByteArray.empty (code := depositRuntime) (storage := inh)
  let sys := runDepositSystem FUEL ByteArray.empty (code := depositRuntime) (storage := inh)
  isRevert user
    && isSuccess sys
    && storageSlotIs sys depositAddr (u256 0) (u256 0)

/-- Combined finite inhibition cycle receipt (empty-queue plane). -/
def inhibitionCycleReceipt : Bool :=
  inhibitEmpty && uninhibitAndGate

/-- #eval target for lake env lean — prints true only if Ξ receipts hold. -/
#eval inhibitionCycleReceipt

end DirectQueueValidate

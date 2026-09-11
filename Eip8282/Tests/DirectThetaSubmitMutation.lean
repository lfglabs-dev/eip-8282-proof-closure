import Eip8282.Tests.PSubmit1Mutant
import Eip8282.Audit.Integrator.DirectGuarantees
import Eip8282.Audit.Integrator.TransferFunding

/-!
# Funded LOG0 mutation witness at the actual Theta boundary

This is finite corroboration of the same parameter-code submission predicate,
not a substitute for its universal proof. Unlike the old untransferred Xi
fixture, the call here executes the real value transfer from funded pre-balances.
The zero-excess witness uses 158 individually checked decode/charge/step
certificates. Candidate snapshots were generated offline by evaluation; every
transition and their composition are checked by the Lean kernel. No evaluator
result is accepted as an axiom.
-/
namespace Eip8282.Tests.DirectThetaSubmitMutation

open EvmYul EvmYul.EVM
open Eip8282.Audit.EvmRunner
open Eip8282.Audit.Integrator
open MessageCall SystemSpec

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option autoImplicit false

def fixture (code : ByteArray) : Context :=
  { fuel := 512, created := default, genesis := default, blocks := default,
    world := worldWith depositAddr code (toAddress 0x1234) (u256 (2 * 10^18)),
    originalWorld := worldWith depositAddr code (toAddress 0x1234) (u256 (2 * 10^18)),
    substate := default, caller := toAddress 0x1234, origin := toAddress 0x1234,
    target := depositAddr, code := code, gas := defaultGas, gasPrice := ZERO_U256,
    value := u256 (10^18 + 1), apparentValue := u256 (10^18 + 1),
    calldata := Eip8282.Audit.Guarantees.PSubmit1.depositInput,
    depth := 0, header := default, permission := true, blobHashes := [] }

def hasEmptyLog (c : Context) : Bool :=
  match c.result with
  | .ok (_, _, _, substate, true, _) =>
      substate.logSeries.size == 1 && (substate.logSeries[0]?.map (fun l => l.data.size)) == some 0
  | _ => false

/-- Exact fresh state made by Ξ after the actual Theta transfer. -/
def initial : EVM.State :=
  let c := fixture PSubmit1Mutant.logSizeMutatedDeposit
  { (default : EVM.State) with
    accountMap := c.entryWorld, σ₀ := c.originalWorld,
    executionEnv := c.environment, substate := c.substate, createdAccounts := c.created,
    gasAvailable := c.gas, blocks := c.blocks, genesisBlockHeader := c.genesis }


open EvmYul.EVM.Proof

/-- The mutant has the same jump sites; this checks its actual bytes. -/
def validJumps : Array UInt256 := #[(u256 82), (u256 88), (u256 100), (u256 127), (u256 159), (u256 284), (u256 305), (u256 307), (u256 471), (u256 489), (u256 500), (u256 560), (u256 568), (u256 578), (u256 612), (u256 624)]
theorem validJumps_eq : D_J initial.executionEnv.code ⟨0⟩ = validJumps := by decide +kernel

theorem zeroes_sub32 (n : Nat) (hn : n ≤ 32) :
    ffi.ByteArray.zeroes ⟨((32 : Nat) : BitVec System.Platform.numBits) - (n : BitVec System.Platform.numBits)⟩ =
      (⟨Array.replicate (32-n) 0⟩ : ByteArray) := by
  unfold ffi.ByteArray.zeroes
  apply congrArg ByteArray.mk
  apply congrArg (fun k : Nat => Array.replicate k (0 : UInt8))
  change ((BitVec.ofNat System.Platform.numBits 32) - BitVec.ofNat System.Platform.numBits n).toNat = 32-n
  rcases System.Platform.numBits_eq with h | h
  all_goals rw [h]
  all_goals simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  all_goals have hn' : n < 2^32 := by omega
  all_goals omega

/-! Snapshots below are candidate data. Shared storage/access-list effects retain
the actual State.sload/sstore operations; machine fields are materialized to
keep every kernel reduction bounded to one instruction. -/
def shared0 : EvmYul.State .EVM := initial.toState
def memory0 : ByteArray := ⟨#[]⟩
def state0 : EVM.State :=
  { initial with
    toState := shared0, pc := (u256 0), stack := [],
    gasAvailable := (u256 30000000), activeWords := (u256 0), execLength := 0, memory := memory0 }

def state1 : EVM.State :=
  { initial with
    toState := shared0, pc := (u256 1), stack := [(u256 4660)],
    gasAvailable := (u256 29999998), activeWords := (u256 0), execLength := 1, memory := memory0 }

def state2 : EVM.State :=
  { initial with
    toState := shared0, pc := (u256 22), stack := [(u256 1461501637330902918203684832716283019655932542974), (u256 4660)],
    gasAvailable := (u256 29999995), activeWords := (u256 0), execLength := 2, memory := memory0 }

def state3 : EVM.State :=
  { initial with
    toState := shared0, pc := (u256 23), stack := [(u256 0)],
    gasAvailable := (u256 29999992), activeWords := (u256 0), execLength := 3, memory := memory0 }

def state4 : EVM.State :=
  { initial with
    toState := shared0, pc := (u256 26), stack := [(u256 284), (u256 0)],
    gasAvailable := (u256 29999989), activeWords := (u256 0), execLength := 4, memory := memory0 }

def state5 : EVM.State :=
  { initial with
    toState := shared0, pc := (u256 27), stack := [],
    gasAvailable := (u256 29999979), activeWords := (u256 0), execLength := 5, memory := memory0 }

def state6 : EVM.State :=
  { initial with
    toState := shared0, pc := (u256 28), stack := [(u256 0)],
    gasAvailable := (u256 29999977), activeWords := (u256 0), execLength := 6, memory := memory0 }

def shared1 : EvmYul.State .EVM := (shared0.sload (u256 0)).1
def state7 : EVM.State :=
  { initial with
    toState := shared1, pc := (u256 29), stack := [(u256 0)],
    gasAvailable := (u256 29997877), activeWords := (u256 0), execLength := 7, memory := memory0 }

def state8 : EVM.State :=
  { initial with
    toState := shared1, pc := (u256 30), stack := [(u256 0), (u256 0)],
    gasAvailable := (u256 29997874), activeWords := (u256 0), execLength := 8, memory := memory0 }

def state9 : EVM.State :=
  { initial with
    toState := shared1, pc := (u256 63), stack := [(u256 115792089237316195423570985008687907853269984665640564039457584007913129639935), (u256 0), (u256 0)],
    gasAvailable := (u256 29997871), activeWords := (u256 0), execLength := 9, memory := memory0 }

def state10 : EVM.State :=
  { initial with
    toState := shared1, pc := (u256 64), stack := [(u256 0), (u256 0)],
    gasAvailable := (u256 29997868), activeWords := (u256 0), execLength := 10, memory := memory0 }

def state11 : EVM.State :=
  { initial with
    toState := shared1, pc := (u256 67), stack := [(u256 624), (u256 0), (u256 0)],
    gasAvailable := (u256 29997865), activeWords := (u256 0), execLength := 11, memory := memory0 }

def state12 : EVM.State :=
  { initial with
    toState := shared1, pc := (u256 68), stack := [(u256 0)],
    gasAvailable := (u256 29997855), activeWords := (u256 0), execLength := 12, memory := memory0 }

def state13 : EVM.State :=
  { initial with
    toState := shared1, pc := (u256 70), stack := [(u256 1), (u256 0)],
    gasAvailable := (u256 29997852), activeWords := (u256 0), execLength := 13, memory := memory0 }

def shared2 : EvmYul.State .EVM := (shared1.sload (u256 1)).1
def state14 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 71), stack := [(u256 0), (u256 0)],
    gasAvailable := (u256 29995752), activeWords := (u256 0), execLength := 14, memory := memory0 }

def state15 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 73), stack := [(u256 8), (u256 0), (u256 0)],
    gasAvailable := (u256 29995749), activeWords := (u256 0), execLength := 15, memory := memory0 }

def state16 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 74), stack := [(u256 0), (u256 8), (u256 0), (u256 0)],
    gasAvailable := (u256 29995746), activeWords := (u256 0), execLength := 16, memory := memory0 }

def state17 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 75), stack := [(u256 0), (u256 0), (u256 0)],
    gasAvailable := (u256 29995743), activeWords := (u256 0), execLength := 17, memory := memory0 }

def state18 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 77), stack := [(u256 82), (u256 0), (u256 0), (u256 0)],
    gasAvailable := (u256 29995740), activeWords := (u256 0), execLength := 18, memory := memory0 }

def state19 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 78), stack := [(u256 0), (u256 0)],
    gasAvailable := (u256 29995730), activeWords := (u256 0), execLength := 19, memory := memory0 }

def state20 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 79), stack := [(u256 0)],
    gasAvailable := (u256 29995728), activeWords := (u256 0), execLength := 20, memory := memory0 }

def state21 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 81), stack := [(u256 88), (u256 0)],
    gasAvailable := (u256 29995725), activeWords := (u256 0), execLength := 21, memory := memory0 }

def state22 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 88), stack := [(u256 0)],
    gasAvailable := (u256 29995717), activeWords := (u256 0), execLength := 22, memory := memory0 }

def state23 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 89), stack := [(u256 0)],
    gasAvailable := (u256 29995716), activeWords := (u256 0), execLength := 23, memory := memory0 }

def state24 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 91), stack := [(u256 17), (u256 0)],
    gasAvailable := (u256 29995713), activeWords := (u256 0), execLength := 24, memory := memory0 }

def state25 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 92), stack := [(u256 0), (u256 17)],
    gasAvailable := (u256 29995710), activeWords := (u256 0), execLength := 25, memory := memory0 }

def state26 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 94), stack := [(u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995707), activeWords := (u256 0), execLength := 26, memory := memory0 }

def state27 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 95), stack := [(u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995704), activeWords := (u256 0), execLength := 27, memory := memory0 }

def state28 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 96), stack := [(u256 17), (u256 0), (u256 17)],
    gasAvailable := (u256 29995699), activeWords := (u256 0), execLength := 28, memory := memory0 }

def state29 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 98), stack := [(u256 1), (u256 17), (u256 0), (u256 17)],
    gasAvailable := (u256 29995696), activeWords := (u256 0), execLength := 29, memory := memory0 }

def state30 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 99), stack := [(u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995693), activeWords := (u256 0), execLength := 30, memory := memory0 }

def state31 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 100), stack := [(u256 0), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995691), activeWords := (u256 0), execLength := 31, memory := memory0 }

def state32 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 101), stack := [(u256 0), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995690), activeWords := (u256 0), execLength := 32, memory := memory0 }

def state33 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 102), stack := [(u256 0), (u256 0), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995688), activeWords := (u256 0), execLength := 33, memory := memory0 }

def state34 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 103), stack := [(u256 17), (u256 0), (u256 0), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995685), activeWords := (u256 0), execLength := 34, memory := memory0 }

def state35 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 104), stack := [(u256 1), (u256 0), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995682), activeWords := (u256 0), execLength := 35, memory := memory0 }

def state36 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 105), stack := [(u256 0), (u256 0), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995679), activeWords := (u256 0), execLength := 36, memory := memory0 }

def state37 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 107), stack := [(u256 127), (u256 0), (u256 0), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995676), activeWords := (u256 0), execLength := 37, memory := memory0 }

def state38 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 108), stack := [(u256 0), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995666), activeWords := (u256 0), execLength := 38, memory := memory0 }

def state39 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 109), stack := [(u256 17), (u256 0), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995663), activeWords := (u256 0), execLength := 39, memory := memory0 }

def state40 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 110), stack := [(u256 17), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995660), activeWords := (u256 0), execLength := 40, memory := memory0 }

def state41 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 111), stack := [(u256 17), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995657), activeWords := (u256 0), execLength := 41, memory := memory0 }

def state42 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 112), stack := [(u256 0), (u256 17), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995654), activeWords := (u256 0), execLength := 42, memory := memory0 }

def state43 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 113), stack := [(u256 0), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995649), activeWords := (u256 0), execLength := 43, memory := memory0 }

def state44 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 114), stack := [(u256 17), (u256 0), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995646), activeWords := (u256 0), execLength := 44, memory := memory0 }

def state45 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 115), stack := [(u256 1), (u256 17), (u256 0), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995643), activeWords := (u256 0), execLength := 45, memory := memory0 }

def state46 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 116), stack := [(u256 17), (u256 0), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995638), activeWords := (u256 0), execLength := 46, memory := memory0 }

def state47 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 117), stack := [(u256 0), (u256 17), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995635), activeWords := (u256 0), execLength := 47, memory := memory0 }

def state48 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 118), stack := [(u256 0), (u256 17), (u256 1), (u256 0), (u256 17)],
    gasAvailable := (u256 29995630), activeWords := (u256 0), execLength := 48, memory := memory0 }

def state49 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 119), stack := [(u256 1), (u256 17), (u256 0), (u256 0), (u256 17)],
    gasAvailable := (u256 29995627), activeWords := (u256 0), execLength := 49, memory := memory0 }

def state50 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 121), stack := [(u256 1), (u256 1), (u256 17), (u256 0), (u256 0), (u256 17)],
    gasAvailable := (u256 29995624), activeWords := (u256 0), execLength := 50, memory := memory0 }

def state51 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 122), stack := [(u256 2), (u256 17), (u256 0), (u256 0), (u256 17)],
    gasAvailable := (u256 29995621), activeWords := (u256 0), execLength := 51, memory := memory0 }

def state52 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 123), stack := [(u256 0), (u256 17), (u256 2), (u256 0), (u256 17)],
    gasAvailable := (u256 29995618), activeWords := (u256 0), execLength := 52, memory := memory0 }

def state53 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 124), stack := [(u256 17), (u256 0), (u256 2), (u256 0), (u256 17)],
    gasAvailable := (u256 29995615), activeWords := (u256 0), execLength := 53, memory := memory0 }

def state54 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 126), stack := [(u256 100), (u256 17), (u256 0), (u256 2), (u256 0), (u256 17)],
    gasAvailable := (u256 29995612), activeWords := (u256 0), execLength := 54, memory := memory0 }

def state55 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 100), stack := [(u256 17), (u256 0), (u256 2), (u256 0), (u256 17)],
    gasAvailable := (u256 29995604), activeWords := (u256 0), execLength := 55, memory := memory0 }

def state56 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 101), stack := [(u256 17), (u256 0), (u256 2), (u256 0), (u256 17)],
    gasAvailable := (u256 29995603), activeWords := (u256 0), execLength := 56, memory := memory0 }

def state57 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 102), stack := [(u256 0), (u256 17), (u256 0), (u256 2), (u256 0), (u256 17)],
    gasAvailable := (u256 29995601), activeWords := (u256 0), execLength := 57, memory := memory0 }

def state58 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 103), stack := [(u256 0), (u256 0), (u256 17), (u256 0), (u256 2), (u256 0), (u256 17)],
    gasAvailable := (u256 29995598), activeWords := (u256 0), execLength := 58, memory := memory0 }

def state59 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 104), stack := [(u256 0), (u256 17), (u256 0), (u256 2), (u256 0), (u256 17)],
    gasAvailable := (u256 29995595), activeWords := (u256 0), execLength := 59, memory := memory0 }

def state60 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 105), stack := [(u256 1), (u256 17), (u256 0), (u256 2), (u256 0), (u256 17)],
    gasAvailable := (u256 29995592), activeWords := (u256 0), execLength := 60, memory := memory0 }

def state61 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 107), stack := [(u256 127), (u256 1), (u256 17), (u256 0), (u256 2), (u256 0), (u256 17)],
    gasAvailable := (u256 29995589), activeWords := (u256 0), execLength := 61, memory := memory0 }

def state62 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 127), stack := [(u256 17), (u256 0), (u256 2), (u256 0), (u256 17)],
    gasAvailable := (u256 29995579), activeWords := (u256 0), execLength := 62, memory := memory0 }

def state63 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 128), stack := [(u256 17), (u256 0), (u256 2), (u256 0), (u256 17)],
    gasAvailable := (u256 29995578), activeWords := (u256 0), execLength := 63, memory := memory0 }

def state64 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 129), stack := [(u256 0), (u256 17), (u256 2), (u256 0), (u256 17)],
    gasAvailable := (u256 29995575), activeWords := (u256 0), execLength := 64, memory := memory0 }

def state65 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 130), stack := [(u256 17), (u256 17), (u256 2), (u256 0), (u256 0)],
    gasAvailable := (u256 29995572), activeWords := (u256 0), execLength := 65, memory := memory0 }

def state66 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 131), stack := [(u256 17), (u256 17), (u256 2), (u256 0), (u256 0)],
    gasAvailable := (u256 29995569), activeWords := (u256 0), execLength := 66, memory := memory0 }

def state67 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 132), stack := [(u256 1), (u256 2), (u256 0), (u256 0)],
    gasAvailable := (u256 29995564), activeWords := (u256 0), execLength := 67, memory := memory0 }

def state68 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 133), stack := [(u256 0), (u256 2), (u256 0), (u256 1)],
    gasAvailable := (u256 29995561), activeWords := (u256 0), execLength := 68, memory := memory0 }

def state69 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 134), stack := [(u256 2), (u256 0), (u256 1)],
    gasAvailable := (u256 29995559), activeWords := (u256 0), execLength := 69, memory := memory0 }

def state70 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 135), stack := [(u256 0), (u256 1)],
    gasAvailable := (u256 29995557), activeWords := (u256 0), execLength := 70, memory := memory0 }

def state71 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 136), stack := [(u256 1)],
    gasAvailable := (u256 29995555), activeWords := (u256 0), execLength := 71, memory := memory0 }

def state72 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 137), stack := [(u256 184), (u256 1)],
    gasAvailable := (u256 29995553), activeWords := (u256 0), execLength := 72, memory := memory0 }

def state73 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 139), stack := [(u256 184), (u256 184), (u256 1)],
    gasAvailable := (u256 29995550), activeWords := (u256 0), execLength := 73, memory := memory0 }

def state74 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 140), stack := [(u256 1), (u256 1)],
    gasAvailable := (u256 29995547), activeWords := (u256 0), execLength := 74, memory := memory0 }

def state75 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 142), stack := [(u256 159), (u256 1), (u256 1)],
    gasAvailable := (u256 29995544), activeWords := (u256 0), execLength := 75, memory := memory0 }

def state76 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 159), stack := [(u256 1)],
    gasAvailable := (u256 29995534), activeWords := (u256 0), execLength := 76, memory := memory0 }

def state77 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 160), stack := [(u256 1)],
    gasAvailable := (u256 29995533), activeWords := (u256 0), execLength := 77, memory := memory0 }

def state78 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 161), stack := [(u256 1), (u256 1)],
    gasAvailable := (u256 29995530), activeWords := (u256 0), execLength := 78, memory := memory0 }

def state79 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 162), stack := [(u256 1000000000000000001), (u256 1), (u256 1)],
    gasAvailable := (u256 29995528), activeWords := (u256 0), execLength := 79, memory := memory0 }

def state80 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 163), stack := [(u256 0), (u256 1)],
    gasAvailable := (u256 29995525), activeWords := (u256 0), execLength := 80, memory := memory0 }

def state81 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 166), stack := [(u256 624), (u256 0), (u256 1)],
    gasAvailable := (u256 29995522), activeWords := (u256 0), execLength := 81, memory := memory0 }

def state82 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 167), stack := [(u256 1)],
    gasAvailable := (u256 29995512), activeWords := (u256 0), execLength := 82, memory := memory0 }

def state83 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 169), stack := [(u256 56), (u256 1)],
    gasAvailable := (u256 29995509), activeWords := (u256 0), execLength := 83, memory := memory0 }

def state84 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 170), stack := [(u256 3178606371220444580254889784552217078325058402586211561866956709204435061248), (u256 1)],
    gasAvailable := (u256 29995506), activeWords := (u256 0), execLength := 84, memory := memory0 }

def state85 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 179), stack := [(u256 18446744073709551615), (u256 3178606371220444580254889784552217078325058402586211561866956709204435061248), (u256 1)],
    gasAvailable := (u256 29995503), activeWords := (u256 0), execLength := 85, memory := memory0 }

def state86 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 180), stack := [(u256 1000000000), (u256 1)],
    gasAvailable := (u256 29995500), activeWords := (u256 0), execLength := 86, memory := memory0 }

def state87 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 181), stack := [(u256 1000000000), (u256 1000000000), (u256 1)],
    gasAvailable := (u256 29995497), activeWords := (u256 0), execLength := 87, memory := memory0 }

def state88 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 186), stack := [(u256 1000000000), (u256 1000000000), (u256 1000000000), (u256 1)],
    gasAvailable := (u256 29995494), activeWords := (u256 0), execLength := 88, memory := memory0 }

def state89 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 187), stack := [(u256 0), (u256 1000000000), (u256 1)],
    gasAvailable := (u256 29995491), activeWords := (u256 0), execLength := 89, memory := memory0 }

def state90 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 190), stack := [(u256 624), (u256 0), (u256 1000000000), (u256 1)],
    gasAvailable := (u256 29995488), activeWords := (u256 0), execLength := 90, memory := memory0 }

def state91 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 191), stack := [(u256 1000000000), (u256 1)],
    gasAvailable := (u256 29995478), activeWords := (u256 0), execLength := 91, memory := memory0 }

def state92 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 196), stack := [(u256 1000000000), (u256 1000000000), (u256 1)],
    gasAvailable := (u256 29995475), activeWords := (u256 0), execLength := 92, memory := memory0 }

def state93 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 197), stack := [(u256 1000000000000000000), (u256 1)],
    gasAvailable := (u256 29995470), activeWords := (u256 0), execLength := 93, memory := memory0 }

def state94 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 198), stack := [(u256 1), (u256 1000000000000000000)],
    gasAvailable := (u256 29995467), activeWords := (u256 0), execLength := 94, memory := memory0 }

def state95 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 199), stack := [(u256 1000000000000000001), (u256 1), (u256 1000000000000000000)],
    gasAvailable := (u256 29995465), activeWords := (u256 0), execLength := 95, memory := memory0 }

def state96 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 200), stack := [(u256 1000000000000000000), (u256 1000000000000000000)],
    gasAvailable := (u256 29995462), activeWords := (u256 0), execLength := 96, memory := memory0 }

def state97 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 201), stack := [(u256 0)],
    gasAvailable := (u256 29995459), activeWords := (u256 0), execLength := 97, memory := memory0 }

def state98 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 204), stack := [(u256 624), (u256 0)],
    gasAvailable := (u256 29995456), activeWords := (u256 0), execLength := 98, memory := memory0 }

def state99 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 205), stack := [],
    gasAvailable := (u256 29995446), activeWords := (u256 0), execLength := 99, memory := memory0 }

def state100 : EVM.State :=
  { initial with
    toState := shared2, pc := (u256 207), stack := [(u256 1)],
    gasAvailable := (u256 29995443), activeWords := (u256 0), execLength := 100, memory := memory0 }

def shared3 : EvmYul.State .EVM := (shared2.sload (u256 1)).1
def state101 : EVM.State :=
  { initial with
    toState := shared3, pc := (u256 208), stack := [(u256 0)],
    gasAvailable := (u256 29995343), activeWords := (u256 0), execLength := 101, memory := memory0 }

def state102 : EVM.State :=
  { initial with
    toState := shared3, pc := (u256 210), stack := [(u256 1), (u256 0)],
    gasAvailable := (u256 29995340), activeWords := (u256 0), execLength := 102, memory := memory0 }

def state103 : EVM.State :=
  { initial with
    toState := shared3, pc := (u256 211), stack := [(u256 1)],
    gasAvailable := (u256 29995337), activeWords := (u256 0), execLength := 103, memory := memory0 }

def state104 : EVM.State :=
  { initial with
    toState := shared3, pc := (u256 213), stack := [(u256 1), (u256 1)],
    gasAvailable := (u256 29995334), activeWords := (u256 0), execLength := 104, memory := memory0 }

def shared4 : EvmYul.State .EVM := shared3.sstore (u256 1) (u256 1)
def state105 : EVM.State :=
  { initial with
    toState := shared4, pc := (u256 214), stack := [],
    gasAvailable := (u256 29975334), activeWords := (u256 0), execLength := 105, memory := memory0 }

def state106 : EVM.State :=
  { initial with
    toState := shared4, pc := (u256 216), stack := [(u256 3)],
    gasAvailable := (u256 29975331), activeWords := (u256 0), execLength := 106, memory := memory0 }

def shared5 : EvmYul.State .EVM := (shared4.sload (u256 3)).1
def state107 : EVM.State :=
  { initial with
    toState := shared5, pc := (u256 217), stack := [(u256 0)],
    gasAvailable := (u256 29973231), activeWords := (u256 0), execLength := 107, memory := memory0 }

def state108 : EVM.State :=
  { initial with
    toState := shared5, pc := (u256 218), stack := [(u256 0), (u256 0)],
    gasAvailable := (u256 29973228), activeWords := (u256 0), execLength := 108, memory := memory0 }

def state109 : EVM.State :=
  { initial with
    toState := shared5, pc := (u256 220), stack := [(u256 6), (u256 0), (u256 0)],
    gasAvailable := (u256 29973225), activeWords := (u256 0), execLength := 109, memory := memory0 }

def state110 : EVM.State :=
  { initial with
    toState := shared5, pc := (u256 221), stack := [(u256 0), (u256 0)],
    gasAvailable := (u256 29973220), activeWords := (u256 0), execLength := 110, memory := memory0 }

def state111 : EVM.State :=
  { initial with
    toState := shared5, pc := (u256 223), stack := [(u256 4), (u256 0), (u256 0)],
    gasAvailable := (u256 29973217), activeWords := (u256 0), execLength := 111, memory := memory0 }

def state112 : EVM.State :=
  { initial with
    toState := shared5, pc := (u256 224), stack := [(u256 4), (u256 0)],
    gasAvailable := (u256 29973214), activeWords := (u256 0), execLength := 112, memory := memory0 }

def state113 : EVM.State :=
  { initial with
    toState := shared5, pc := (u256 225), stack := [(u256 0), (u256 4), (u256 0)],
    gasAvailable := (u256 29973212), activeWords := (u256 0), execLength := 113, memory := memory0 }

def state114 : EVM.State :=
  { initial with
    toState := shared5, pc := (u256 226), stack := [(u256 3178606371220444580254889784552217078325058402586211561867463090413301597959), (u256 4), (u256 0)],
    gasAvailable := (u256 29973209), activeWords := (u256 0), execLength := 114, memory := memory0 }

def state115 : EVM.State :=
  { initial with
    toState := shared5, pc := (u256 227), stack := [(u256 4), (u256 3178606371220444580254889784552217078325058402586211561867463090413301597959), (u256 4), (u256 0)],
    gasAvailable := (u256 29973206), activeWords := (u256 0), execLength := 115, memory := memory0 }

def shared6 : EvmYul.State .EVM := shared5.sstore (u256 4) (u256 3178606371220444580254889784552217078325058402586211561867463090413301597959)
def state116 : EVM.State :=
  { initial with
    toState := shared6, pc := (u256 228), stack := [(u256 4), (u256 0)],
    gasAvailable := (u256 29951106), activeWords := (u256 0), execLength := 116, memory := memory0 }

def state117 : EVM.State :=
  { initial with
    toState := shared6, pc := (u256 230), stack := [(u256 1), (u256 4), (u256 0)],
    gasAvailable := (u256 29951103), activeWords := (u256 0), execLength := 117, memory := memory0 }

def state118 : EVM.State :=
  { initial with
    toState := shared6, pc := (u256 231), stack := [(u256 5), (u256 0)],
    gasAvailable := (u256 29951100), activeWords := (u256 0), execLength := 118, memory := memory0 }

def state119 : EVM.State :=
  { initial with
    toState := shared6, pc := (u256 233), stack := [(u256 32), (u256 5), (u256 0)],
    gasAvailable := (u256 29951097), activeWords := (u256 0), execLength := 119, memory := memory0 }

def state120 : EVM.State :=
  { initial with
    toState := shared6, pc := (u256 234), stack := [(u256 3178606371220444580254889784552217078325058402586211561867463090413301597959), (u256 5), (u256 0)],
    gasAvailable := (u256 29951094), activeWords := (u256 0), execLength := 120, memory := memory0 }

def state121 : EVM.State :=
  { initial with
    toState := shared6, pc := (u256 235), stack := [(u256 5), (u256 3178606371220444580254889784552217078325058402586211561867463090413301597959), (u256 5), (u256 0)],
    gasAvailable := (u256 29951091), activeWords := (u256 0), execLength := 121, memory := memory0 }

def shared7 : EvmYul.State .EVM := shared6.sstore (u256 5) (u256 3178606371220444580254889784552217078325058402586211561867463090413301597959)
def state122 : EVM.State :=
  { initial with
    toState := shared7, pc := (u256 236), stack := [(u256 5), (u256 0)],
    gasAvailable := (u256 29928991), activeWords := (u256 0), execLength := 122, memory := memory0 }

def state123 : EVM.State :=
  { initial with
    toState := shared7, pc := (u256 238), stack := [(u256 1), (u256 5), (u256 0)],
    gasAvailable := (u256 29928988), activeWords := (u256 0), execLength := 123, memory := memory0 }

def state124 : EVM.State :=
  { initial with
    toState := shared7, pc := (u256 239), stack := [(u256 6), (u256 0)],
    gasAvailable := (u256 29928985), activeWords := (u256 0), execLength := 124, memory := memory0 }

def state125 : EVM.State :=
  { initial with
    toState := shared7, pc := (u256 241), stack := [(u256 64), (u256 6), (u256 0)],
    gasAvailable := (u256 29928982), activeWords := (u256 0), execLength := 125, memory := memory0 }

def state126 : EVM.State :=
  { initial with
    toState := shared7, pc := (u256 242), stack := [(u256 3178606371220444580254889784552217078315717318022514897140723641858688222983), (u256 6), (u256 0)],
    gasAvailable := (u256 29928979), activeWords := (u256 0), execLength := 126, memory := memory0 }

def state127 : EVM.State :=
  { initial with
    toState := shared7, pc := (u256 243), stack := [(u256 6), (u256 3178606371220444580254889784552217078315717318022514897140723641858688222983), (u256 6), (u256 0)],
    gasAvailable := (u256 29928976), activeWords := (u256 0), execLength := 127, memory := memory0 }

def shared8 : EvmYul.State .EVM := shared7.sstore (u256 6) (u256 3178606371220444580254889784552217078315717318022514897140723641858688222983)
def state128 : EVM.State :=
  { initial with
    toState := shared8, pc := (u256 244), stack := [(u256 6), (u256 0)],
    gasAvailable := (u256 29906876), activeWords := (u256 0), execLength := 128, memory := memory0 }

def state129 : EVM.State :=
  { initial with
    toState := shared8, pc := (u256 246), stack := [(u256 1), (u256 6), (u256 0)],
    gasAvailable := (u256 29906873), activeWords := (u256 0), execLength := 129, memory := memory0 }

def state130 : EVM.State :=
  { initial with
    toState := shared8, pc := (u256 247), stack := [(u256 7), (u256 0)],
    gasAvailable := (u256 29906870), activeWords := (u256 0), execLength := 130, memory := memory0 }

def state131 : EVM.State :=
  { initial with
    toState := shared8, pc := (u256 249), stack := [(u256 96), (u256 7), (u256 0)],
    gasAvailable := (u256 29906867), activeWords := (u256 0), execLength := 131, memory := memory0 }

def state132 : EVM.State :=
  { initial with
    toState := shared8, pc := (u256 250), stack := [(u256 3178606371220444580254889784552217078325058402586211561867463090413301597959), (u256 7), (u256 0)],
    gasAvailable := (u256 29906864), activeWords := (u256 0), execLength := 132, memory := memory0 }

def state133 : EVM.State :=
  { initial with
    toState := shared8, pc := (u256 251), stack := [(u256 7), (u256 3178606371220444580254889784552217078325058402586211561867463090413301597959), (u256 7), (u256 0)],
    gasAvailable := (u256 29906861), activeWords := (u256 0), execLength := 133, memory := memory0 }

def shared9 : EvmYul.State .EVM := shared8.sstore (u256 7) (u256 3178606371220444580254889784552217078325058402586211561867463090413301597959)
def state134 : EVM.State :=
  { initial with
    toState := shared9, pc := (u256 252), stack := [(u256 7), (u256 0)],
    gasAvailable := (u256 29884761), activeWords := (u256 0), execLength := 134, memory := memory0 }

def state135 : EVM.State :=
  { initial with
    toState := shared9, pc := (u256 254), stack := [(u256 1), (u256 7), (u256 0)],
    gasAvailable := (u256 29884758), activeWords := (u256 0), execLength := 135, memory := memory0 }

def state136 : EVM.State :=
  { initial with
    toState := shared9, pc := (u256 255), stack := [(u256 8), (u256 0)],
    gasAvailable := (u256 29884755), activeWords := (u256 0), execLength := 136, memory := memory0 }

def state137 : EVM.State :=
  { initial with
    toState := shared9, pc := (u256 257), stack := [(u256 128), (u256 8), (u256 0)],
    gasAvailable := (u256 29884752), activeWords := (u256 0), execLength := 137, memory := memory0 }

def state138 : EVM.State :=
  { initial with
    toState := shared9, pc := (u256 258), stack := [(u256 3178606371220444580254889784552217078325058402586211561867463090413301597959), (u256 8), (u256 0)],
    gasAvailable := (u256 29884749), activeWords := (u256 0), execLength := 138, memory := memory0 }

def state139 : EVM.State :=
  { initial with
    toState := shared9, pc := (u256 259), stack := [(u256 8), (u256 3178606371220444580254889784552217078325058402586211561867463090413301597959), (u256 8), (u256 0)],
    gasAvailable := (u256 29884746), activeWords := (u256 0), execLength := 139, memory := memory0 }

def shared10 : EvmYul.State .EVM := shared9.sstore (u256 8) (u256 3178606371220444580254889784552217078325058402586211561867463090413301597959)
def state140 : EVM.State :=
  { initial with
    toState := shared10, pc := (u256 260), stack := [(u256 8), (u256 0)],
    gasAvailable := (u256 29862646), activeWords := (u256 0), execLength := 140, memory := memory0 }

def state141 : EVM.State :=
  { initial with
    toState := shared10, pc := (u256 262), stack := [(u256 1), (u256 8), (u256 0)],
    gasAvailable := (u256 29862643), activeWords := (u256 0), execLength := 141, memory := memory0 }

def state142 : EVM.State :=
  { initial with
    toState := shared10, pc := (u256 263), stack := [(u256 9), (u256 0)],
    gasAvailable := (u256 29862640), activeWords := (u256 0), execLength := 142, memory := memory0 }

def state143 : EVM.State :=
  { initial with
    toState := shared10, pc := (u256 265), stack := [(u256 160), (u256 9), (u256 0)],
    gasAvailable := (u256 29862637), activeWords := (u256 0), execLength := 143, memory := memory0 }

def state144 : EVM.State :=
  { initial with
    toState := shared10, pc := (u256 266), stack := [(u256 3178606371220444580254889784552217078325058402586211561866956709203435061248), (u256 9), (u256 0)],
    gasAvailable := (u256 29862634), activeWords := (u256 0), execLength := 144, memory := memory0 }

def state145 : EVM.State :=
  { initial with
    toState := shared10, pc := (u256 267), stack := [(u256 9), (u256 3178606371220444580254889784552217078325058402586211561866956709203435061248), (u256 0)],
    gasAvailable := (u256 29862631), activeWords := (u256 0), execLength := 145, memory := memory0 }

def shared11 : EvmYul.State .EVM := shared10.sstore (u256 9) (u256 3178606371220444580254889784552217078325058402586211561866956709203435061248)
def state146 : EVM.State :=
  { initial with
    toState := shared11, pc := (u256 268), stack := [(u256 0)],
    gasAvailable := (u256 29840531), activeWords := (u256 0), execLength := 146, memory := memory0 }

def state147 : EVM.State :=
  { initial with
    toState := shared11, pc := (u256 270), stack := [(u256 184), (u256 0)],
    gasAvailable := (u256 29840528), activeWords := (u256 0), execLength := 147, memory := memory0 }

def state148 : EVM.State :=
  { initial with
    toState := shared11, pc := (u256 271), stack := [(u256 0), (u256 184), (u256 0)],
    gasAvailable := (u256 29840526), activeWords := (u256 0), execLength := 148, memory := memory0 }

def state149 : EVM.State :=
  { initial with
    toState := shared11, pc := (u256 272), stack := [(u256 0), (u256 0), (u256 184), (u256 0)],
    gasAvailable := (u256 29840524), activeWords := (u256 0), execLength := 149, memory := memory0 }

def memory1 : ByteArray := ⟨#[7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 0, 0, 0, 0, 59, 154, 202, 0, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7]⟩
def state150 : EVM.State :=
  { initial with
    toState := shared11, pc := (u256 273), stack := [(u256 0)],
    gasAvailable := (u256 29840485), activeWords := (u256 6), execLength := 150, memory := memory1 }

def state151 : EVM.State :=
  { initial with
    toState := shared11, pc := (u256 275), stack := [(u256 0), (u256 0)],
    gasAvailable := (u256 29840482), activeWords := (u256 6), execLength := 151, memory := memory1 }

def state152 : EVM.State :=
  { initial with
    toState := shared11, pc := (u256 276), stack := [(u256 0), (u256 0), (u256 0)],
    gasAvailable := (u256 29840480), activeWords := (u256 6), execLength := 152, memory := memory1 }

def shared12 : EvmYul.State .EVM :=
  { shared11 with substate.logSeries := shared11.substate.logSeries.push ⟨depositAddr, #[], .empty⟩ }
def state153 : EVM.State :=
  { initial with
    toState := shared12, pc := (u256 277), stack := [(u256 0)],
    gasAvailable := (u256 29840105), activeWords := (u256 6), execLength := 153, memory := memory1 }

def state154 : EVM.State :=
  { initial with
    toState := shared12, pc := (u256 279), stack := [(u256 1), (u256 0)],
    gasAvailable := (u256 29840102), activeWords := (u256 6), execLength := 154, memory := memory1 }

def state155 : EVM.State :=
  { initial with
    toState := shared12, pc := (u256 280), stack := [(u256 1)],
    gasAvailable := (u256 29840099), activeWords := (u256 6), execLength := 155, memory := memory1 }

def state156 : EVM.State :=
  { initial with
    toState := shared12, pc := (u256 282), stack := [(u256 3), (u256 1)],
    gasAvailable := (u256 29840096), activeWords := (u256 6), execLength := 156, memory := memory1 }

def shared13 : EvmYul.State .EVM := shared12.sstore (u256 3) (u256 1)
def state157 : EVM.State :=
  { initial with
    toState := shared13, pc := (u256 283), stack := [],
    gasAvailable := (u256 29820096), activeWords := (u256 6), execLength := 157, memory := memory1 }

def state158 : EVM.State :=
  { initial with
    toState := shared13, pc := (u256 283), stack := [],
    gasAvailable := (u256 29820096), activeWords := (u256 6), execLength := 158, memory := memory1 }

/-! Each edge checks the actual decoder, Z gas/admission check, and EVM.step. -/
theorem decode0 : decodeAt state0 = (.CALLER, none) := by rfl
def middle0 : EVM.State := { state0 with gasAvailable := (u256 30000000) }
theorem charge0 : Z validJumps .CALLER state0 = .ok (middle0, 2) := by rfl
theorem step0 : StepOk 510 2 (.CALLER, none) middle0 state1 := by rfl
theorem edge0 : X 511 validJumps state0 = X 510 validJumps state1 :=
  X_succ_of_continue decode0 charge0 step0 rfl

theorem decode1 : decodeAt state1 = (.PUSH20, some ((u256 1461501637330902918203684832716283019655932542974), 20)) := by rfl
def middle1 : EVM.State := { state1 with gasAvailable := (u256 29999998) }
theorem charge1 : Z validJumps .PUSH20 state1 = .ok (middle1, 3) := by rfl
theorem step1 : StepOk 509 3 (.PUSH20, some ((u256 1461501637330902918203684832716283019655932542974), 20)) middle1 state2 := by rfl
theorem edge1 : X 510 validJumps state1 = X 509 validJumps state2 :=
  X_succ_of_continue decode1 charge1 step1 rfl

theorem decode2 : decodeAt state2 = (.EQ, none) := by rfl
def middle2 : EVM.State := { state2 with gasAvailable := (u256 29999995) }
theorem charge2 : Z validJumps .EQ state2 = .ok (middle2, 3) := by rfl
theorem step2 : StepOk 508 3 (.EQ, none) middle2 state3 := by rfl
theorem edge2 : X 509 validJumps state2 = X 508 validJumps state3 :=
  X_succ_of_continue decode2 charge2 step2 rfl

theorem decode3 : decodeAt state3 = (.PUSH2, some ((u256 284), 2)) := by rfl
def middle3 : EVM.State := { state3 with gasAvailable := (u256 29999992) }
theorem charge3 : Z validJumps .PUSH2 state3 = .ok (middle3, 3) := by rfl
theorem step3 : StepOk 507 3 (.PUSH2, some ((u256 284), 2)) middle3 state4 := by rfl
theorem edge3 : X 508 validJumps state3 = X 507 validJumps state4 :=
  X_succ_of_continue decode3 charge3 step3 rfl

theorem decode4 : decodeAt state4 = (.JUMPI, none) := by rfl
def middle4 : EVM.State := { state4 with gasAvailable := (u256 29999989) }
theorem jump4 : X.notIn state4.stack[0]? validJumps = false := by decide +kernel
theorem charge4 : Z validJumps .JUMPI state4 = .ok (middle4, 10) := by
  simp only [Z, jump4]
  rfl
theorem step4 : StepOk 506 10 (.JUMPI, none) middle4 state5 := by rfl
theorem edge4 : X 507 validJumps state4 = X 506 validJumps state5 :=
  X_succ_of_continue decode4 charge4 step4 rfl

theorem decode5 : decodeAt state5 = (.PUSH0, none) := by rfl
def middle5 : EVM.State := { state5 with gasAvailable := (u256 29999979) }
theorem charge5 : Z validJumps .PUSH0 state5 = .ok (middle5, 2) := by rfl
theorem step5 : StepOk 505 2 (.PUSH0, none) middle5 state6 := by rfl
theorem edge5 : X 506 validJumps state5 = X 505 validJumps state6 :=
  X_succ_of_continue decode5 charge5 step5 rfl

theorem decode6 : decodeAt state6 = (.SLOAD, none) := by rfl
def middle6 : EVM.State := { state6 with gasAvailable := (u256 29999977) }
theorem charge6 : Z validJumps .SLOAD state6 = .ok (middle6, 2100) := by rfl
theorem step6 : StepOk 504 2100 (.SLOAD, none) middle6 state7 := by rfl
theorem edge6 : X 505 validJumps state6 = X 504 validJumps state7 :=
  X_succ_of_continue decode6 charge6 step6 rfl

theorem decode7 : decodeAt state7 = (.DUP1, none) := by rfl
def middle7 : EVM.State := { state7 with gasAvailable := (u256 29997877) }
theorem charge7 : Z validJumps .DUP1 state7 = .ok (middle7, 3) := by rfl
theorem step7 : StepOk 503 3 (.DUP1, none) middle7 state8 := by rfl
theorem edge7 : X 504 validJumps state7 = X 503 validJumps state8 :=
  X_succ_of_continue decode7 charge7 step7 rfl

theorem decode8 : decodeAt state8 = (.PUSH32, some ((u256 115792089237316195423570985008687907853269984665640564039457584007913129639935), 32)) := by rfl
def middle8 : EVM.State := { state8 with gasAvailable := (u256 29997874) }
theorem charge8 : Z validJumps .PUSH32 state8 = .ok (middle8, 3) := by rfl
theorem step8 : StepOk 502 3 (.PUSH32, some ((u256 115792089237316195423570985008687907853269984665640564039457584007913129639935), 32)) middle8 state9 := by rfl
theorem edge8 : X 503 validJumps state8 = X 502 validJumps state9 :=
  X_succ_of_continue decode8 charge8 step8 rfl

theorem decode9 : decodeAt state9 = (.EQ, none) := by rfl
def middle9 : EVM.State := { state9 with gasAvailable := (u256 29997871) }
theorem charge9 : Z validJumps .EQ state9 = .ok (middle9, 3) := by rfl
theorem step9 : StepOk 501 3 (.EQ, none) middle9 state10 := by rfl
theorem edge9 : X 502 validJumps state9 = X 501 validJumps state10 :=
  X_succ_of_continue decode9 charge9 step9 rfl

theorem decode10 : decodeAt state10 = (.PUSH2, some ((u256 624), 2)) := by rfl
def middle10 : EVM.State := { state10 with gasAvailable := (u256 29997868) }
theorem charge10 : Z validJumps .PUSH2 state10 = .ok (middle10, 3) := by rfl
theorem step10 : StepOk 500 3 (.PUSH2, some ((u256 624), 2)) middle10 state11 := by rfl
theorem edge10 : X 501 validJumps state10 = X 500 validJumps state11 :=
  X_succ_of_continue decode10 charge10 step10 rfl

theorem decode11 : decodeAt state11 = (.JUMPI, none) := by rfl
def middle11 : EVM.State := { state11 with gasAvailable := (u256 29997865) }
theorem jump11 : X.notIn state11.stack[0]? validJumps = false := by decide +kernel
theorem charge11 : Z validJumps .JUMPI state11 = .ok (middle11, 10) := by
  simp only [Z, jump11]
  rfl
theorem step11 : StepOk 499 10 (.JUMPI, none) middle11 state12 := by rfl
theorem edge11 : X 500 validJumps state11 = X 499 validJumps state12 :=
  X_succ_of_continue decode11 charge11 step11 rfl

theorem decode12 : decodeAt state12 = (.PUSH1, some ((u256 1), 1)) := by rfl
def middle12 : EVM.State := { state12 with gasAvailable := (u256 29997855) }
theorem charge12 : Z validJumps .PUSH1 state12 = .ok (middle12, 3) := by rfl
theorem step12 : StepOk 498 3 (.PUSH1, some ((u256 1), 1)) middle12 state13 := by rfl
theorem edge12 : X 499 validJumps state12 = X 498 validJumps state13 :=
  X_succ_of_continue decode12 charge12 step12 rfl

theorem decode13 : decodeAt state13 = (.SLOAD, none) := by rfl
def middle13 : EVM.State := { state13 with gasAvailable := (u256 29997852) }
theorem charge13 : Z validJumps .SLOAD state13 = .ok (middle13, 2100) := by rfl
theorem step13 : StepOk 497 2100 (.SLOAD, none) middle13 state14 := by rfl
theorem edge13 : X 498 validJumps state13 = X 497 validJumps state14 :=
  X_succ_of_continue decode13 charge13 step13 rfl

theorem decode14 : decodeAt state14 = (.PUSH1, some ((u256 8), 1)) := by rfl
def middle14 : EVM.State := { state14 with gasAvailable := (u256 29995752) }
theorem charge14 : Z validJumps .PUSH1 state14 = .ok (middle14, 3) := by rfl
theorem step14 : StepOk 496 3 (.PUSH1, some ((u256 8), 1)) middle14 state15 := by rfl
theorem edge14 : X 497 validJumps state14 = X 496 validJumps state15 :=
  X_succ_of_continue decode14 charge14 step14 rfl

theorem decode15 : decodeAt state15 = (.DUP2, none) := by rfl
def middle15 : EVM.State := { state15 with gasAvailable := (u256 29995749) }
theorem charge15 : Z validJumps .DUP2 state15 = .ok (middle15, 3) := by rfl
theorem step15 : StepOk 495 3 (.DUP2, none) middle15 state16 := by rfl
theorem edge15 : X 496 validJumps state15 = X 495 validJumps state16 :=
  X_succ_of_continue decode15 charge15 step15 rfl

theorem decode16 : decodeAt state16 = (.GT, none) := by rfl
def middle16 : EVM.State := { state16 with gasAvailable := (u256 29995746) }
theorem charge16 : Z validJumps .GT state16 = .ok (middle16, 3) := by rfl
theorem step16 : StepOk 494 3 (.GT, none) middle16 state17 := by rfl
theorem edge16 : X 495 validJumps state16 = X 494 validJumps state17 :=
  X_succ_of_continue decode16 charge16 step16 rfl

theorem decode17 : decodeAt state17 = (.PUSH1, some ((u256 82), 1)) := by rfl
def middle17 : EVM.State := { state17 with gasAvailable := (u256 29995743) }
theorem charge17 : Z validJumps .PUSH1 state17 = .ok (middle17, 3) := by rfl
theorem step17 : StepOk 493 3 (.PUSH1, some ((u256 82), 1)) middle17 state18 := by rfl
theorem edge17 : X 494 validJumps state17 = X 493 validJumps state18 :=
  X_succ_of_continue decode17 charge17 step17 rfl

theorem decode18 : decodeAt state18 = (.JUMPI, none) := by rfl
def middle18 : EVM.State := { state18 with gasAvailable := (u256 29995740) }
theorem jump18 : X.notIn state18.stack[0]? validJumps = false := by decide +kernel
theorem charge18 : Z validJumps .JUMPI state18 = .ok (middle18, 10) := by
  simp only [Z, jump18]
  rfl
theorem step18 : StepOk 492 10 (.JUMPI, none) middle18 state19 := by rfl
theorem edge18 : X 493 validJumps state18 = X 492 validJumps state19 :=
  X_succ_of_continue decode18 charge18 step18 rfl

theorem decode19 : decodeAt state19 = (.POP, none) := by rfl
def middle19 : EVM.State := { state19 with gasAvailable := (u256 29995730) }
theorem charge19 : Z validJumps .POP state19 = .ok (middle19, 2) := by rfl
theorem step19 : StepOk 491 2 (.POP, none) middle19 state20 := by rfl
theorem edge19 : X 492 validJumps state19 = X 491 validJumps state20 :=
  X_succ_of_continue decode19 charge19 step19 rfl

theorem decode20 : decodeAt state20 = (.PUSH1, some ((u256 88), 1)) := by rfl
def middle20 : EVM.State := { state20 with gasAvailable := (u256 29995728) }
theorem charge20 : Z validJumps .PUSH1 state20 = .ok (middle20, 3) := by rfl
theorem step20 : StepOk 490 3 (.PUSH1, some ((u256 88), 1)) middle20 state21 := by rfl
theorem edge20 : X 491 validJumps state20 = X 490 validJumps state21 :=
  X_succ_of_continue decode20 charge20 step20 rfl

theorem decode21 : decodeAt state21 = (.JUMP, none) := by rfl
def middle21 : EVM.State := { state21 with gasAvailable := (u256 29995725) }
theorem jump21 : X.notIn state21.stack[0]? validJumps = false := by decide +kernel
theorem charge21 : Z validJumps .JUMP state21 = .ok (middle21, 8) := by
  simp only [Z, jump21]
  rfl
theorem step21 : StepOk 489 8 (.JUMP, none) middle21 state22 := by rfl
theorem edge21 : X 490 validJumps state21 = X 489 validJumps state22 :=
  X_succ_of_continue decode21 charge21 step21 rfl

theorem decode22 : decodeAt state22 = (.JUMPDEST, none) := by rfl
def middle22 : EVM.State := { state22 with gasAvailable := (u256 29995717) }
theorem charge22 : Z validJumps .JUMPDEST state22 = .ok (middle22, 1) := by rfl
theorem step22 : StepOk 488 1 (.JUMPDEST, none) middle22 state23 := by rfl
theorem edge22 : X 489 validJumps state22 = X 488 validJumps state23 :=
  X_succ_of_continue decode22 charge22 step22 rfl

theorem decode23 : decodeAt state23 = (.PUSH1, some ((u256 17), 1)) := by rfl
def middle23 : EVM.State := { state23 with gasAvailable := (u256 29995716) }
theorem charge23 : Z validJumps .PUSH1 state23 = .ok (middle23, 3) := by rfl
theorem step23 : StepOk 487 3 (.PUSH1, some ((u256 17), 1)) middle23 state24 := by rfl
theorem edge23 : X 488 validJumps state23 = X 487 validJumps state24 :=
  X_succ_of_continue decode23 charge23 step23 rfl

theorem decode24 : decodeAt state24 = (.SWAP1, none) := by rfl
def middle24 : EVM.State := { state24 with gasAvailable := (u256 29995713) }
theorem charge24 : Z validJumps .SWAP1 state24 = .ok (middle24, 3) := by rfl
theorem step24 : StepOk 486 3 (.SWAP1, none) middle24 state25 := by rfl
theorem edge24 : X 487 validJumps state24 = X 486 validJumps state25 :=
  X_succ_of_continue decode24 charge24 step24 rfl

theorem decode25 : decodeAt state25 = (.PUSH1, some ((u256 1), 1)) := by rfl
def middle25 : EVM.State := { state25 with gasAvailable := (u256 29995710) }
theorem charge25 : Z validJumps .PUSH1 state25 = .ok (middle25, 3) := by rfl
theorem step25 : StepOk 485 3 (.PUSH1, some ((u256 1), 1)) middle25 state26 := by rfl
theorem edge25 : X 486 validJumps state25 = X 485 validJumps state26 :=
  X_succ_of_continue decode25 charge25 step25 rfl

theorem decode26 : decodeAt state26 = (.DUP3, none) := by rfl
def middle26 : EVM.State := { state26 with gasAvailable := (u256 29995707) }
theorem charge26 : Z validJumps .DUP3 state26 = .ok (middle26, 3) := by rfl
theorem step26 : StepOk 484 3 (.DUP3, none) middle26 state27 := by rfl
theorem edge26 : X 485 validJumps state26 = X 484 validJumps state27 :=
  X_succ_of_continue decode26 charge26 step26 rfl

theorem decode27 : decodeAt state27 = (.MUL, none) := by rfl
def middle27 : EVM.State := { state27 with gasAvailable := (u256 29995704) }
theorem charge27 : Z validJumps .MUL state27 = .ok (middle27, 5) := by rfl
theorem step27 : StepOk 483 5 (.MUL, none) middle27 state28 := by rfl
theorem edge27 : X 484 validJumps state27 = X 483 validJumps state28 :=
  X_succ_of_continue decode27 charge27 step27 rfl

theorem decode28 : decodeAt state28 = (.PUSH1, some ((u256 1), 1)) := by rfl
def middle28 : EVM.State := { state28 with gasAvailable := (u256 29995699) }
theorem charge28 : Z validJumps .PUSH1 state28 = .ok (middle28, 3) := by rfl
theorem step28 : StepOk 482 3 (.PUSH1, some ((u256 1), 1)) middle28 state29 := by rfl
theorem edge28 : X 483 validJumps state28 = X 482 validJumps state29 :=
  X_succ_of_continue decode28 charge28 step28 rfl

theorem decode29 : decodeAt state29 = (.SWAP1, none) := by rfl
def middle29 : EVM.State := { state29 with gasAvailable := (u256 29995696) }
theorem charge29 : Z validJumps .SWAP1 state29 = .ok (middle29, 3) := by rfl
theorem step29 : StepOk 481 3 (.SWAP1, none) middle29 state30 := by rfl
theorem edge29 : X 482 validJumps state29 = X 481 validJumps state30 :=
  X_succ_of_continue decode29 charge29 step29 rfl

theorem decode30 : decodeAt state30 = (.PUSH0, none) := by rfl
def middle30 : EVM.State := { state30 with gasAvailable := (u256 29995693) }
theorem charge30 : Z validJumps .PUSH0 state30 = .ok (middle30, 2) := by rfl
theorem step30 : StepOk 480 2 (.PUSH0, none) middle30 state31 := by rfl
theorem edge30 : X 481 validJumps state30 = X 480 validJumps state31 :=
  X_succ_of_continue decode30 charge30 step30 rfl

theorem decode31 : decodeAt state31 = (.JUMPDEST, none) := by rfl
def middle31 : EVM.State := { state31 with gasAvailable := (u256 29995691) }
theorem charge31 : Z validJumps .JUMPDEST state31 = .ok (middle31, 1) := by rfl
theorem step31 : StepOk 479 1 (.JUMPDEST, none) middle31 state32 := by rfl
theorem edge31 : X 480 validJumps state31 = X 479 validJumps state32 :=
  X_succ_of_continue decode31 charge31 step31 rfl

theorem decode32 : decodeAt state32 = (.PUSH0, none) := by rfl
def middle32 : EVM.State := { state32 with gasAvailable := (u256 29995690) }
theorem charge32 : Z validJumps .PUSH0 state32 = .ok (middle32, 2) := by rfl
theorem step32 : StepOk 478 2 (.PUSH0, none) middle32 state33 := by rfl
theorem edge32 : X 479 validJumps state32 = X 478 validJumps state33 :=
  X_succ_of_continue decode32 charge32 step32 rfl

theorem decode33 : decodeAt state33 = (.DUP3, none) := by rfl
def middle33 : EVM.State := { state33 with gasAvailable := (u256 29995688) }
theorem charge33 : Z validJumps .DUP3 state33 = .ok (middle33, 3) := by rfl
theorem step33 : StepOk 477 3 (.DUP3, none) middle33 state34 := by rfl
theorem edge33 : X 478 validJumps state33 = X 477 validJumps state34 :=
  X_succ_of_continue decode33 charge33 step33 rfl

theorem decode34 : decodeAt state34 = (.GT, none) := by rfl
def middle34 : EVM.State := { state34 with gasAvailable := (u256 29995685) }
theorem charge34 : Z validJumps .GT state34 = .ok (middle34, 3) := by rfl
theorem step34 : StepOk 476 3 (.GT, none) middle34 state35 := by rfl
theorem edge34 : X 477 validJumps state34 = X 476 validJumps state35 :=
  X_succ_of_continue decode34 charge34 step34 rfl

theorem decode35 : decodeAt state35 = (.ISZERO, none) := by rfl
def middle35 : EVM.State := { state35 with gasAvailable := (u256 29995682) }
theorem charge35 : Z validJumps .ISZERO state35 = .ok (middle35, 3) := by rfl
theorem step35 : StepOk 475 3 (.ISZERO, none) middle35 state36 := by rfl
theorem edge35 : X 476 validJumps state35 = X 475 validJumps state36 :=
  X_succ_of_continue decode35 charge35 step35 rfl

theorem decode36 : decodeAt state36 = (.PUSH1, some ((u256 127), 1)) := by rfl
def middle36 : EVM.State := { state36 with gasAvailable := (u256 29995679) }
theorem charge36 : Z validJumps .PUSH1 state36 = .ok (middle36, 3) := by rfl
theorem step36 : StepOk 474 3 (.PUSH1, some ((u256 127), 1)) middle36 state37 := by rfl
theorem edge36 : X 475 validJumps state36 = X 474 validJumps state37 :=
  X_succ_of_continue decode36 charge36 step36 rfl

theorem decode37 : decodeAt state37 = (.JUMPI, none) := by rfl
def middle37 : EVM.State := { state37 with gasAvailable := (u256 29995676) }
theorem jump37 : X.notIn state37.stack[0]? validJumps = false := by decide +kernel
theorem charge37 : Z validJumps .JUMPI state37 = .ok (middle37, 10) := by
  simp only [Z, jump37]
  rfl
theorem step37 : StepOk 473 10 (.JUMPI, none) middle37 state38 := by rfl
theorem edge37 : X 474 validJumps state37 = X 473 validJumps state38 :=
  X_succ_of_continue decode37 charge37 step37 rfl

theorem decode38 : decodeAt state38 = (.DUP2, none) := by rfl
def middle38 : EVM.State := { state38 with gasAvailable := (u256 29995666) }
theorem charge38 : Z validJumps .DUP2 state38 = .ok (middle38, 3) := by rfl
theorem step38 : StepOk 472 3 (.DUP2, none) middle38 state39 := by rfl
theorem edge38 : X 473 validJumps state38 = X 472 validJumps state39 :=
  X_succ_of_continue decode38 charge38 step38 rfl

theorem decode39 : decodeAt state39 = (.ADD, none) := by rfl
def middle39 : EVM.State := { state39 with gasAvailable := (u256 29995663) }
theorem charge39 : Z validJumps .ADD state39 = .ok (middle39, 3) := by rfl
theorem step39 : StepOk 471 3 (.ADD, none) middle39 state40 := by rfl
theorem edge39 : X 472 validJumps state39 = X 471 validJumps state40 :=
  X_succ_of_continue decode39 charge39 step39 rfl

theorem decode40 : decodeAt state40 = (.SWAP1, none) := by rfl
def middle40 : EVM.State := { state40 with gasAvailable := (u256 29995660) }
theorem charge40 : Z validJumps .SWAP1 state40 = .ok (middle40, 3) := by rfl
theorem step40 : StepOk 470 3 (.SWAP1, none) middle40 state41 := by rfl
theorem edge40 : X 471 validJumps state40 = X 470 validJumps state41 :=
  X_succ_of_continue decode40 charge40 step40 rfl

theorem decode41 : decodeAt state41 = (.DUP4, none) := by rfl
def middle41 : EVM.State := { state41 with gasAvailable := (u256 29995657) }
theorem charge41 : Z validJumps .DUP4 state41 = .ok (middle41, 3) := by rfl
theorem step41 : StepOk 469 3 (.DUP4, none) middle41 state42 := by rfl
theorem edge41 : X 470 validJumps state41 = X 469 validJumps state42 :=
  X_succ_of_continue decode41 charge41 step41 rfl

theorem decode42 : decodeAt state42 = (.MUL, none) := by rfl
def middle42 : EVM.State := { state42 with gasAvailable := (u256 29995654) }
theorem charge42 : Z validJumps .MUL state42 = .ok (middle42, 5) := by rfl
theorem step42 : StepOk 468 5 (.MUL, none) middle42 state43 := by rfl
theorem edge42 : X 469 validJumps state42 = X 468 validJumps state43 :=
  X_succ_of_continue decode42 charge42 step42 rfl

theorem decode43 : decodeAt state43 = (.DUP5, none) := by rfl
def middle43 : EVM.State := { state43 with gasAvailable := (u256 29995649) }
theorem charge43 : Z validJumps .DUP5 state43 = .ok (middle43, 3) := by rfl
theorem step43 : StepOk 467 3 (.DUP5, none) middle43 state44 := by rfl
theorem edge43 : X 468 validJumps state43 = X 467 validJumps state44 :=
  X_succ_of_continue decode43 charge43 step43 rfl

theorem decode44 : decodeAt state44 = (.DUP4, none) := by rfl
def middle44 : EVM.State := { state44 with gasAvailable := (u256 29995646) }
theorem charge44 : Z validJumps .DUP4 state44 = .ok (middle44, 3) := by rfl
theorem step44 : StepOk 466 3 (.DUP4, none) middle44 state45 := by rfl
theorem edge44 : X 467 validJumps state44 = X 466 validJumps state45 :=
  X_succ_of_continue decode44 charge44 step44 rfl

theorem decode45 : decodeAt state45 = (.MUL, none) := by rfl
def middle45 : EVM.State := { state45 with gasAvailable := (u256 29995643) }
theorem charge45 : Z validJumps .MUL state45 = .ok (middle45, 5) := by rfl
theorem step45 : StepOk 465 5 (.MUL, none) middle45 state46 := by rfl
theorem edge45 : X 466 validJumps state45 = X 465 validJumps state46 :=
  X_succ_of_continue decode45 charge45 step45 rfl

theorem decode46 : decodeAt state46 = (.SWAP1, none) := by rfl
def middle46 : EVM.State := { state46 with gasAvailable := (u256 29995638) }
theorem charge46 : Z validJumps .SWAP1 state46 = .ok (middle46, 3) := by rfl
theorem step46 : StepOk 464 3 (.SWAP1, none) middle46 state47 := by rfl
theorem edge46 : X 465 validJumps state46 = X 464 validJumps state47 :=
  X_succ_of_continue decode46 charge46 step46 rfl

theorem decode47 : decodeAt state47 = (.DIV, none) := by rfl
def middle47 : EVM.State := { state47 with gasAvailable := (u256 29995635) }
theorem charge47 : Z validJumps .DIV state47 = .ok (middle47, 5) := by rfl
theorem step47 : StepOk 463 5 (.DIV, none) middle47 state48 := by rfl
theorem edge47 : X 464 validJumps state47 = X 463 validJumps state48 :=
  X_succ_of_continue decode47 charge47 step47 rfl

theorem decode48 : decodeAt state48 = (.SWAP2, none) := by rfl
def middle48 : EVM.State := { state48 with gasAvailable := (u256 29995630) }
theorem charge48 : Z validJumps .SWAP2 state48 = .ok (middle48, 3) := by rfl
theorem step48 : StepOk 462 3 (.SWAP2, none) middle48 state49 := by rfl
theorem edge48 : X 463 validJumps state48 = X 462 validJumps state49 :=
  X_succ_of_continue decode48 charge48 step48 rfl

theorem decode49 : decodeAt state49 = (.PUSH1, some ((u256 1), 1)) := by rfl
def middle49 : EVM.State := { state49 with gasAvailable := (u256 29995627) }
theorem charge49 : Z validJumps .PUSH1 state49 = .ok (middle49, 3) := by rfl
theorem step49 : StepOk 461 3 (.PUSH1, some ((u256 1), 1)) middle49 state50 := by rfl
theorem edge49 : X 462 validJumps state49 = X 461 validJumps state50 :=
  X_succ_of_continue decode49 charge49 step49 rfl

theorem decode50 : decodeAt state50 = (.ADD, none) := by rfl
def middle50 : EVM.State := { state50 with gasAvailable := (u256 29995624) }
theorem charge50 : Z validJumps .ADD state50 = .ok (middle50, 3) := by rfl
theorem step50 : StepOk 460 3 (.ADD, none) middle50 state51 := by rfl
theorem edge50 : X 461 validJumps state50 = X 460 validJumps state51 :=
  X_succ_of_continue decode50 charge50 step50 rfl

theorem decode51 : decodeAt state51 = (.SWAP2, none) := by rfl
def middle51 : EVM.State := { state51 with gasAvailable := (u256 29995621) }
theorem charge51 : Z validJumps .SWAP2 state51 = .ok (middle51, 3) := by rfl
theorem step51 : StepOk 459 3 (.SWAP2, none) middle51 state52 := by rfl
theorem edge51 : X 460 validJumps state51 = X 459 validJumps state52 :=
  X_succ_of_continue decode51 charge51 step51 rfl

theorem decode52 : decodeAt state52 = (.SWAP1, none) := by rfl
def middle52 : EVM.State := { state52 with gasAvailable := (u256 29995618) }
theorem charge52 : Z validJumps .SWAP1 state52 = .ok (middle52, 3) := by rfl
theorem step52 : StepOk 458 3 (.SWAP1, none) middle52 state53 := by rfl
theorem edge52 : X 459 validJumps state52 = X 458 validJumps state53 :=
  X_succ_of_continue decode52 charge52 step52 rfl

theorem decode53 : decodeAt state53 = (.PUSH1, some ((u256 100), 1)) := by rfl
def middle53 : EVM.State := { state53 with gasAvailable := (u256 29995615) }
theorem charge53 : Z validJumps .PUSH1 state53 = .ok (middle53, 3) := by rfl
theorem step53 : StepOk 457 3 (.PUSH1, some ((u256 100), 1)) middle53 state54 := by rfl
theorem edge53 : X 458 validJumps state53 = X 457 validJumps state54 :=
  X_succ_of_continue decode53 charge53 step53 rfl

theorem decode54 : decodeAt state54 = (.JUMP, none) := by rfl
def middle54 : EVM.State := { state54 with gasAvailable := (u256 29995612) }
theorem jump54 : X.notIn state54.stack[0]? validJumps = false := by decide +kernel
theorem charge54 : Z validJumps .JUMP state54 = .ok (middle54, 8) := by
  simp only [Z, jump54]
  rfl
theorem step54 : StepOk 456 8 (.JUMP, none) middle54 state55 := by rfl
theorem edge54 : X 457 validJumps state54 = X 456 validJumps state55 :=
  X_succ_of_continue decode54 charge54 step54 rfl

theorem decode55 : decodeAt state55 = (.JUMPDEST, none) := by rfl
def middle55 : EVM.State := { state55 with gasAvailable := (u256 29995604) }
theorem charge55 : Z validJumps .JUMPDEST state55 = .ok (middle55, 1) := by rfl
theorem step55 : StepOk 455 1 (.JUMPDEST, none) middle55 state56 := by rfl
theorem edge55 : X 456 validJumps state55 = X 455 validJumps state56 :=
  X_succ_of_continue decode55 charge55 step55 rfl

theorem decode56 : decodeAt state56 = (.PUSH0, none) := by rfl
def middle56 : EVM.State := { state56 with gasAvailable := (u256 29995603) }
theorem charge56 : Z validJumps .PUSH0 state56 = .ok (middle56, 2) := by rfl
theorem step56 : StepOk 454 2 (.PUSH0, none) middle56 state57 := by rfl
theorem edge56 : X 455 validJumps state56 = X 454 validJumps state57 :=
  X_succ_of_continue decode56 charge56 step56 rfl

theorem decode57 : decodeAt state57 = (.DUP3, none) := by rfl
def middle57 : EVM.State := { state57 with gasAvailable := (u256 29995601) }
theorem charge57 : Z validJumps .DUP3 state57 = .ok (middle57, 3) := by rfl
theorem step57 : StepOk 453 3 (.DUP3, none) middle57 state58 := by rfl
theorem edge57 : X 454 validJumps state57 = X 453 validJumps state58 :=
  X_succ_of_continue decode57 charge57 step57 rfl

theorem decode58 : decodeAt state58 = (.GT, none) := by rfl
def middle58 : EVM.State := { state58 with gasAvailable := (u256 29995598) }
theorem charge58 : Z validJumps .GT state58 = .ok (middle58, 3) := by rfl
theorem step58 : StepOk 452 3 (.GT, none) middle58 state59 := by rfl
theorem edge58 : X 453 validJumps state58 = X 452 validJumps state59 :=
  X_succ_of_continue decode58 charge58 step58 rfl

theorem decode59 : decodeAt state59 = (.ISZERO, none) := by rfl
def middle59 : EVM.State := { state59 with gasAvailable := (u256 29995595) }
theorem charge59 : Z validJumps .ISZERO state59 = .ok (middle59, 3) := by rfl
theorem step59 : StepOk 451 3 (.ISZERO, none) middle59 state60 := by rfl
theorem edge59 : X 452 validJumps state59 = X 451 validJumps state60 :=
  X_succ_of_continue decode59 charge59 step59 rfl

theorem decode60 : decodeAt state60 = (.PUSH1, some ((u256 127), 1)) := by rfl
def middle60 : EVM.State := { state60 with gasAvailable := (u256 29995592) }
theorem charge60 : Z validJumps .PUSH1 state60 = .ok (middle60, 3) := by rfl
theorem step60 : StepOk 450 3 (.PUSH1, some ((u256 127), 1)) middle60 state61 := by rfl
theorem edge60 : X 451 validJumps state60 = X 450 validJumps state61 :=
  X_succ_of_continue decode60 charge60 step60 rfl

theorem decode61 : decodeAt state61 = (.JUMPI, none) := by rfl
def middle61 : EVM.State := { state61 with gasAvailable := (u256 29995589) }
theorem jump61 : X.notIn state61.stack[0]? validJumps = false := by decide +kernel
theorem charge61 : Z validJumps .JUMPI state61 = .ok (middle61, 10) := by
  simp only [Z, jump61]
  rfl
theorem step61 : StepOk 449 10 (.JUMPI, none) middle61 state62 := by rfl
theorem edge61 : X 450 validJumps state61 = X 449 validJumps state62 :=
  X_succ_of_continue decode61 charge61 step61 rfl

theorem decode62 : decodeAt state62 = (.JUMPDEST, none) := by rfl
def middle62 : EVM.State := { state62 with gasAvailable := (u256 29995579) }
theorem charge62 : Z validJumps .JUMPDEST state62 = .ok (middle62, 1) := by rfl
theorem step62 : StepOk 448 1 (.JUMPDEST, none) middle62 state63 := by rfl
theorem edge62 : X 449 validJumps state62 = X 448 validJumps state63 :=
  X_succ_of_continue decode62 charge62 step62 rfl

theorem decode63 : decodeAt state63 = (.SWAP1, none) := by rfl
def middle63 : EVM.State := { state63 with gasAvailable := (u256 29995578) }
theorem charge63 : Z validJumps .SWAP1 state63 = .ok (middle63, 3) := by rfl
theorem step63 : StepOk 447 3 (.SWAP1, none) middle63 state64 := by rfl
theorem edge63 : X 448 validJumps state63 = X 447 validJumps state64 :=
  X_succ_of_continue decode63 charge63 step63 rfl

theorem decode64 : decodeAt state64 = (.SWAP4, none) := by rfl
def middle64 : EVM.State := { state64 with gasAvailable := (u256 29995575) }
theorem charge64 : Z validJumps .SWAP4 state64 = .ok (middle64, 3) := by rfl
theorem step64 : StepOk 446 3 (.SWAP4, none) middle64 state65 := by rfl
theorem edge64 : X 447 validJumps state64 = X 446 validJumps state65 :=
  X_succ_of_continue decode64 charge64 step64 rfl

theorem decode65 : decodeAt state65 = (.SWAP1, none) := by rfl
def middle65 : EVM.State := { state65 with gasAvailable := (u256 29995572) }
theorem charge65 : Z validJumps .SWAP1 state65 = .ok (middle65, 3) := by rfl
theorem step65 : StepOk 445 3 (.SWAP1, none) middle65 state66 := by rfl
theorem edge65 : X 446 validJumps state65 = X 445 validJumps state66 :=
  X_succ_of_continue decode65 charge65 step65 rfl

theorem decode66 : decodeAt state66 = (.DIV, none) := by rfl
def middle66 : EVM.State := { state66 with gasAvailable := (u256 29995569) }
theorem charge66 : Z validJumps .DIV state66 = .ok (middle66, 5) := by rfl
theorem step66 : StepOk 444 5 (.DIV, none) middle66 state67 := by rfl
theorem edge66 : X 445 validJumps state66 = X 444 validJumps state67 :=
  X_succ_of_continue decode66 charge66 step66 rfl

theorem decode67 : decodeAt state67 = (.SWAP3, none) := by rfl
def middle67 : EVM.State := { state67 with gasAvailable := (u256 29995564) }
theorem charge67 : Z validJumps .SWAP3 state67 = .ok (middle67, 3) := by rfl
theorem step67 : StepOk 443 3 (.SWAP3, none) middle67 state68 := by rfl
theorem edge67 : X 444 validJumps state67 = X 443 validJumps state68 :=
  X_succ_of_continue decode67 charge67 step67 rfl

theorem decode68 : decodeAt state68 = (.POP, none) := by rfl
def middle68 : EVM.State := { state68 with gasAvailable := (u256 29995561) }
theorem charge68 : Z validJumps .POP state68 = .ok (middle68, 2) := by rfl
theorem step68 : StepOk 442 2 (.POP, none) middle68 state69 := by rfl
theorem edge68 : X 443 validJumps state68 = X 442 validJumps state69 :=
  X_succ_of_continue decode68 charge68 step68 rfl

theorem decode69 : decodeAt state69 = (.POP, none) := by rfl
def middle69 : EVM.State := { state69 with gasAvailable := (u256 29995559) }
theorem charge69 : Z validJumps .POP state69 = .ok (middle69, 2) := by rfl
theorem step69 : StepOk 441 2 (.POP, none) middle69 state70 := by rfl
theorem edge69 : X 442 validJumps state69 = X 441 validJumps state70 :=
  X_succ_of_continue decode69 charge69 step69 rfl

theorem decode70 : decodeAt state70 = (.POP, none) := by rfl
def middle70 : EVM.State := { state70 with gasAvailable := (u256 29995557) }
theorem charge70 : Z validJumps .POP state70 = .ok (middle70, 2) := by rfl
theorem step70 : StepOk 440 2 (.POP, none) middle70 state71 := by rfl
theorem edge70 : X 441 validJumps state70 = X 440 validJumps state71 :=
  X_succ_of_continue decode70 charge70 step70 rfl

theorem decode71 : decodeAt state71 = (.CALLDATASIZE, none) := by rfl
def middle71 : EVM.State := { state71 with gasAvailable := (u256 29995555) }
theorem charge71 : Z validJumps .CALLDATASIZE state71 = .ok (middle71, 2) := by rfl
theorem step71 : StepOk 439 2 (.CALLDATASIZE, none) middle71 state72 := by rfl
theorem edge71 : X 440 validJumps state71 = X 439 validJumps state72 :=
  X_succ_of_continue decode71 charge71 step71 rfl

theorem decode72 : decodeAt state72 = (.PUSH1, some ((u256 184), 1)) := by rfl
def middle72 : EVM.State := { state72 with gasAvailable := (u256 29995553) }
theorem charge72 : Z validJumps .PUSH1 state72 = .ok (middle72, 3) := by rfl
theorem step72 : StepOk 438 3 (.PUSH1, some ((u256 184), 1)) middle72 state73 := by rfl
theorem edge72 : X 439 validJumps state72 = X 438 validJumps state73 :=
  X_succ_of_continue decode72 charge72 step72 rfl

theorem decode73 : decodeAt state73 = (.EQ, none) := by rfl
def middle73 : EVM.State := { state73 with gasAvailable := (u256 29995550) }
theorem charge73 : Z validJumps .EQ state73 = .ok (middle73, 3) := by rfl
theorem step73 : StepOk 437 3 (.EQ, none) middle73 state74 := by rfl
theorem edge73 : X 438 validJumps state73 = X 437 validJumps state74 :=
  X_succ_of_continue decode73 charge73 step73 rfl

theorem decode74 : decodeAt state74 = (.PUSH1, some ((u256 159), 1)) := by rfl
def middle74 : EVM.State := { state74 with gasAvailable := (u256 29995547) }
theorem charge74 : Z validJumps .PUSH1 state74 = .ok (middle74, 3) := by rfl
theorem step74 : StepOk 436 3 (.PUSH1, some ((u256 159), 1)) middle74 state75 := by rfl
theorem edge74 : X 437 validJumps state74 = X 436 validJumps state75 :=
  X_succ_of_continue decode74 charge74 step74 rfl

theorem decode75 : decodeAt state75 = (.JUMPI, none) := by rfl
def middle75 : EVM.State := { state75 with gasAvailable := (u256 29995544) }
theorem jump75 : X.notIn state75.stack[0]? validJumps = false := by decide +kernel
theorem charge75 : Z validJumps .JUMPI state75 = .ok (middle75, 10) := by
  simp only [Z, jump75]
  rfl
theorem step75 : StepOk 435 10 (.JUMPI, none) middle75 state76 := by rfl
theorem edge75 : X 436 validJumps state75 = X 435 validJumps state76 :=
  X_succ_of_continue decode75 charge75 step75 rfl

theorem decode76 : decodeAt state76 = (.JUMPDEST, none) := by rfl
def middle76 : EVM.State := { state76 with gasAvailable := (u256 29995534) }
theorem charge76 : Z validJumps .JUMPDEST state76 = .ok (middle76, 1) := by rfl
theorem step76 : StepOk 434 1 (.JUMPDEST, none) middle76 state77 := by rfl
theorem edge76 : X 435 validJumps state76 = X 434 validJumps state77 :=
  X_succ_of_continue decode76 charge76 step76 rfl

theorem decode77 : decodeAt state77 = (.DUP1, none) := by rfl
def middle77 : EVM.State := { state77 with gasAvailable := (u256 29995533) }
theorem charge77 : Z validJumps .DUP1 state77 = .ok (middle77, 3) := by rfl
theorem step77 : StepOk 433 3 (.DUP1, none) middle77 state78 := by rfl
theorem edge77 : X 434 validJumps state77 = X 433 validJumps state78 :=
  X_succ_of_continue decode77 charge77 step77 rfl

theorem decode78 : decodeAt state78 = (.CALLVALUE, none) := by rfl
def middle78 : EVM.State := { state78 with gasAvailable := (u256 29995530) }
theorem charge78 : Z validJumps .CALLVALUE state78 = .ok (middle78, 2) := by rfl
theorem step78 : StepOk 432 2 (.CALLVALUE, none) middle78 state79 := by rfl
theorem edge78 : X 433 validJumps state78 = X 432 validJumps state79 :=
  X_succ_of_continue decode78 charge78 step78 rfl

theorem decode79 : decodeAt state79 = (.LT, none) := by rfl
def middle79 : EVM.State := { state79 with gasAvailable := (u256 29995528) }
theorem charge79 : Z validJumps .LT state79 = .ok (middle79, 3) := by rfl
theorem step79 : StepOk 431 3 (.LT, none) middle79 state80 := by rfl
theorem edge79 : X 432 validJumps state79 = X 431 validJumps state80 :=
  X_succ_of_continue decode79 charge79 step79 rfl

theorem decode80 : decodeAt state80 = (.PUSH2, some ((u256 624), 2)) := by rfl
def middle80 : EVM.State := { state80 with gasAvailable := (u256 29995525) }
theorem charge80 : Z validJumps .PUSH2 state80 = .ok (middle80, 3) := by rfl
theorem step80 : StepOk 430 3 (.PUSH2, some ((u256 624), 2)) middle80 state81 := by rfl
theorem edge80 : X 431 validJumps state80 = X 430 validJumps state81 :=
  X_succ_of_continue decode80 charge80 step80 rfl

theorem decode81 : decodeAt state81 = (.JUMPI, none) := by rfl
def middle81 : EVM.State := { state81 with gasAvailable := (u256 29995522) }
theorem jump81 : X.notIn state81.stack[0]? validJumps = false := by decide +kernel
theorem charge81 : Z validJumps .JUMPI state81 = .ok (middle81, 10) := by
  simp only [Z, jump81]
  rfl
theorem step81 : StepOk 429 10 (.JUMPI, none) middle81 state82 := by rfl
theorem edge81 : X 430 validJumps state81 = X 429 validJumps state82 :=
  X_succ_of_continue decode81 charge81 step81 rfl

theorem decode82 : decodeAt state82 = (.PUSH1, some ((u256 56), 1)) := by rfl
def middle82 : EVM.State := { state82 with gasAvailable := (u256 29995512) }
theorem charge82 : Z validJumps .PUSH1 state82 = .ok (middle82, 3) := by rfl
theorem step82 : StepOk 428 3 (.PUSH1, some ((u256 56), 1)) middle82 state83 := by rfl
theorem edge82 : X 429 validJumps state82 = X 428 validJumps state83 :=
  X_succ_of_continue decode82 charge82 step82 rfl

theorem decode83 : decodeAt state83 = (.CALLDATALOAD, none) := by rfl
def middle83 : EVM.State := { state83 with gasAvailable := (u256 29995509) }
theorem charge83 : Z validJumps .CALLDATALOAD state83 = .ok (middle83, 3) := by rfl
theorem load83 : middle83.toState.calldataload (u256 56) = (u256 3178606371220444580254889784552217078325058402586211561866956709204435061248) := by
  unfold EvmYul.State.calldataload ByteArray.readBytes
  dsimp only []
  rw [zeroes_sub32 _ (by decide +kernel)]
  decide +kernel
theorem step83 : StepOk 427 3 (.CALLDATALOAD, none) middle83 state84 := by
  change Except.ok (Eip8282.Audit.SymExec.bump 3 middle83 (middle83.replaceStackAndIncrPC (middle83.toState.calldataload (u256 56) :: [(u256 1)]))) = .ok state84
  rw [load83]
  rfl
theorem edge83 : X 428 validJumps state83 = X 427 validJumps state84 :=
  X_succ_of_continue decode83 charge83 step83 rfl

theorem decode84 : decodeAt state84 = (.PUSH8, some ((u256 18446744073709551615), 8)) := by rfl
def middle84 : EVM.State := { state84 with gasAvailable := (u256 29995506) }
theorem charge84 : Z validJumps .PUSH8 state84 = .ok (middle84, 3) := by rfl
theorem step84 : StepOk 426 3 (.PUSH8, some ((u256 18446744073709551615), 8)) middle84 state85 := by rfl
theorem edge84 : X 427 validJumps state84 = X 426 validJumps state85 :=
  X_succ_of_continue decode84 charge84 step84 rfl

theorem decode85 : decodeAt state85 = (.AND, none) := by rfl
def middle85 : EVM.State := { state85 with gasAvailable := (u256 29995503) }
theorem charge85 : Z validJumps .AND state85 = .ok (middle85, 3) := by rfl
theorem step85 : StepOk 425 3 (.AND, none) middle85 state86 := by rfl
theorem edge85 : X 426 validJumps state85 = X 425 validJumps state86 :=
  X_succ_of_continue decode85 charge85 step85 rfl

theorem decode86 : decodeAt state86 = (.DUP1, none) := by rfl
def middle86 : EVM.State := { state86 with gasAvailable := (u256 29995500) }
theorem charge86 : Z validJumps .DUP1 state86 = .ok (middle86, 3) := by rfl
theorem step86 : StepOk 424 3 (.DUP1, none) middle86 state87 := by rfl
theorem edge86 : X 425 validJumps state86 = X 424 validJumps state87 :=
  X_succ_of_continue decode86 charge86 step86 rfl

theorem decode87 : decodeAt state87 = (.PUSH4, some ((u256 1000000000), 4)) := by rfl
def middle87 : EVM.State := { state87 with gasAvailable := (u256 29995497) }
theorem charge87 : Z validJumps .PUSH4 state87 = .ok (middle87, 3) := by rfl
theorem step87 : StepOk 423 3 (.PUSH4, some ((u256 1000000000), 4)) middle87 state88 := by rfl
theorem edge87 : X 424 validJumps state87 = X 423 validJumps state88 :=
  X_succ_of_continue decode87 charge87 step87 rfl

theorem decode88 : decodeAt state88 = (.GT, none) := by rfl
def middle88 : EVM.State := { state88 with gasAvailable := (u256 29995494) }
theorem charge88 : Z validJumps .GT state88 = .ok (middle88, 3) := by rfl
theorem step88 : StepOk 422 3 (.GT, none) middle88 state89 := by rfl
theorem edge88 : X 423 validJumps state88 = X 422 validJumps state89 :=
  X_succ_of_continue decode88 charge88 step88 rfl

theorem decode89 : decodeAt state89 = (.PUSH2, some ((u256 624), 2)) := by rfl
def middle89 : EVM.State := { state89 with gasAvailable := (u256 29995491) }
theorem charge89 : Z validJumps .PUSH2 state89 = .ok (middle89, 3) := by rfl
theorem step89 : StepOk 421 3 (.PUSH2, some ((u256 624), 2)) middle89 state90 := by rfl
theorem edge89 : X 422 validJumps state89 = X 421 validJumps state90 :=
  X_succ_of_continue decode89 charge89 step89 rfl

theorem decode90 : decodeAt state90 = (.JUMPI, none) := by rfl
def middle90 : EVM.State := { state90 with gasAvailable := (u256 29995488) }
theorem jump90 : X.notIn state90.stack[0]? validJumps = false := by decide +kernel
theorem charge90 : Z validJumps .JUMPI state90 = .ok (middle90, 10) := by
  simp only [Z, jump90]
  rfl
theorem step90 : StepOk 420 10 (.JUMPI, none) middle90 state91 := by rfl
theorem edge90 : X 421 validJumps state90 = X 420 validJumps state91 :=
  X_succ_of_continue decode90 charge90 step90 rfl

theorem decode91 : decodeAt state91 = (.PUSH4, some ((u256 1000000000), 4)) := by rfl
def middle91 : EVM.State := { state91 with gasAvailable := (u256 29995478) }
theorem charge91 : Z validJumps .PUSH4 state91 = .ok (middle91, 3) := by rfl
theorem step91 : StepOk 419 3 (.PUSH4, some ((u256 1000000000), 4)) middle91 state92 := by rfl
theorem edge91 : X 420 validJumps state91 = X 419 validJumps state92 :=
  X_succ_of_continue decode91 charge91 step91 rfl

theorem decode92 : decodeAt state92 = (.MUL, none) := by rfl
def middle92 : EVM.State := { state92 with gasAvailable := (u256 29995475) }
theorem charge92 : Z validJumps .MUL state92 = .ok (middle92, 5) := by rfl
theorem step92 : StepOk 418 5 (.MUL, none) middle92 state93 := by rfl
theorem edge92 : X 419 validJumps state92 = X 418 validJumps state93 :=
  X_succ_of_continue decode92 charge92 step92 rfl

theorem decode93 : decodeAt state93 = (.SWAP1, none) := by rfl
def middle93 : EVM.State := { state93 with gasAvailable := (u256 29995470) }
theorem charge93 : Z validJumps .SWAP1 state93 = .ok (middle93, 3) := by rfl
theorem step93 : StepOk 417 3 (.SWAP1, none) middle93 state94 := by rfl
theorem edge93 : X 418 validJumps state93 = X 417 validJumps state94 :=
  X_succ_of_continue decode93 charge93 step93 rfl

theorem decode94 : decodeAt state94 = (.CALLVALUE, none) := by rfl
def middle94 : EVM.State := { state94 with gasAvailable := (u256 29995467) }
theorem charge94 : Z validJumps .CALLVALUE state94 = .ok (middle94, 2) := by rfl
theorem step94 : StepOk 416 2 (.CALLVALUE, none) middle94 state95 := by rfl
theorem edge94 : X 417 validJumps state94 = X 416 validJumps state95 :=
  X_succ_of_continue decode94 charge94 step94 rfl

theorem decode95 : decodeAt state95 = (.SUB, none) := by rfl
def middle95 : EVM.State := { state95 with gasAvailable := (u256 29995465) }
theorem charge95 : Z validJumps .SUB state95 = .ok (middle95, 3) := by rfl
theorem step95 : StepOk 415 3 (.SUB, none) middle95 state96 := by rfl
theorem edge95 : X 416 validJumps state95 = X 415 validJumps state96 :=
  X_succ_of_continue decode95 charge95 step95 rfl

theorem decode96 : decodeAt state96 = (.LT, none) := by rfl
def middle96 : EVM.State := { state96 with gasAvailable := (u256 29995462) }
theorem charge96 : Z validJumps .LT state96 = .ok (middle96, 3) := by rfl
theorem step96 : StepOk 414 3 (.LT, none) middle96 state97 := by rfl
theorem edge96 : X 415 validJumps state96 = X 414 validJumps state97 :=
  X_succ_of_continue decode96 charge96 step96 rfl

theorem decode97 : decodeAt state97 = (.PUSH2, some ((u256 624), 2)) := by rfl
def middle97 : EVM.State := { state97 with gasAvailable := (u256 29995459) }
theorem charge97 : Z validJumps .PUSH2 state97 = .ok (middle97, 3) := by rfl
theorem step97 : StepOk 413 3 (.PUSH2, some ((u256 624), 2)) middle97 state98 := by rfl
theorem edge97 : X 414 validJumps state97 = X 413 validJumps state98 :=
  X_succ_of_continue decode97 charge97 step97 rfl

theorem decode98 : decodeAt state98 = (.JUMPI, none) := by rfl
def middle98 : EVM.State := { state98 with gasAvailable := (u256 29995456) }
theorem jump98 : X.notIn state98.stack[0]? validJumps = false := by decide +kernel
theorem charge98 : Z validJumps .JUMPI state98 = .ok (middle98, 10) := by
  simp only [Z, jump98]
  rfl
theorem step98 : StepOk 412 10 (.JUMPI, none) middle98 state99 := by rfl
theorem edge98 : X 413 validJumps state98 = X 412 validJumps state99 :=
  X_succ_of_continue decode98 charge98 step98 rfl

theorem decode99 : decodeAt state99 = (.PUSH1, some ((u256 1), 1)) := by rfl
def middle99 : EVM.State := { state99 with gasAvailable := (u256 29995446) }
theorem charge99 : Z validJumps .PUSH1 state99 = .ok (middle99, 3) := by rfl
theorem step99 : StepOk 411 3 (.PUSH1, some ((u256 1), 1)) middle99 state100 := by rfl
theorem edge99 : X 412 validJumps state99 = X 411 validJumps state100 :=
  X_succ_of_continue decode99 charge99 step99 rfl

theorem decode100 : decodeAt state100 = (.SLOAD, none) := by rfl
def middle100 : EVM.State := { state100 with gasAvailable := (u256 29995443) }
theorem charge100 : Z validJumps .SLOAD state100 = .ok (middle100, 100) := by rfl
theorem step100 : StepOk 410 100 (.SLOAD, none) middle100 state101 := by rfl
theorem edge100 : X 411 validJumps state100 = X 410 validJumps state101 :=
  X_succ_of_continue decode100 charge100 step100 rfl

theorem decode101 : decodeAt state101 = (.PUSH1, some ((u256 1), 1)) := by rfl
def middle101 : EVM.State := { state101 with gasAvailable := (u256 29995343) }
theorem charge101 : Z validJumps .PUSH1 state101 = .ok (middle101, 3) := by rfl
theorem step101 : StepOk 409 3 (.PUSH1, some ((u256 1), 1)) middle101 state102 := by rfl
theorem edge101 : X 410 validJumps state101 = X 409 validJumps state102 :=
  X_succ_of_continue decode101 charge101 step101 rfl

theorem decode102 : decodeAt state102 = (.ADD, none) := by rfl
def middle102 : EVM.State := { state102 with gasAvailable := (u256 29995340) }
theorem charge102 : Z validJumps .ADD state102 = .ok (middle102, 3) := by rfl
theorem step102 : StepOk 408 3 (.ADD, none) middle102 state103 := by rfl
theorem edge102 : X 409 validJumps state102 = X 408 validJumps state103 :=
  X_succ_of_continue decode102 charge102 step102 rfl

theorem decode103 : decodeAt state103 = (.PUSH1, some ((u256 1), 1)) := by rfl
def middle103 : EVM.State := { state103 with gasAvailable := (u256 29995337) }
theorem charge103 : Z validJumps .PUSH1 state103 = .ok (middle103, 3) := by rfl
theorem step103 : StepOk 407 3 (.PUSH1, some ((u256 1), 1)) middle103 state104 := by rfl
theorem edge103 : X 408 validJumps state103 = X 407 validJumps state104 :=
  X_succ_of_continue decode103 charge103 step103 rfl

theorem decode104 : decodeAt state104 = (.SSTORE, none) := by rfl
def middle104 : EVM.State := { state104 with gasAvailable := (u256 29995334) }
theorem charge104 : Z validJumps .SSTORE state104 = .ok (middle104, 20000) := by rfl
theorem step104 : StepOk 406 20000 (.SSTORE, none) middle104 state105 := by rfl
theorem edge104 : X 407 validJumps state104 = X 406 validJumps state105 :=
  X_succ_of_continue decode104 charge104 step104 rfl

theorem decode105 : decodeAt state105 = (.PUSH1, some ((u256 3), 1)) := by rfl
def middle105 : EVM.State := { state105 with gasAvailable := (u256 29975334) }
theorem charge105 : Z validJumps .PUSH1 state105 = .ok (middle105, 3) := by rfl
theorem step105 : StepOk 405 3 (.PUSH1, some ((u256 3), 1)) middle105 state106 := by rfl
theorem edge105 : X 406 validJumps state105 = X 405 validJumps state106 :=
  X_succ_of_continue decode105 charge105 step105 rfl

theorem decode106 : decodeAt state106 = (.SLOAD, none) := by rfl
def middle106 : EVM.State := { state106 with gasAvailable := (u256 29975331) }
theorem charge106 : Z validJumps .SLOAD state106 = .ok (middle106, 2100) := by rfl
theorem step106 : StepOk 404 2100 (.SLOAD, none) middle106 state107 := by rfl
theorem edge106 : X 405 validJumps state106 = X 404 validJumps state107 :=
  X_succ_of_continue decode106 charge106 step106 rfl

theorem decode107 : decodeAt state107 = (.DUP1, none) := by rfl
def middle107 : EVM.State := { state107 with gasAvailable := (u256 29973231) }
theorem charge107 : Z validJumps .DUP1 state107 = .ok (middle107, 3) := by rfl
theorem step107 : StepOk 403 3 (.DUP1, none) middle107 state108 := by rfl
theorem edge107 : X 404 validJumps state107 = X 403 validJumps state108 :=
  X_succ_of_continue decode107 charge107 step107 rfl

theorem decode108 : decodeAt state108 = (.PUSH1, some ((u256 6), 1)) := by rfl
def middle108 : EVM.State := { state108 with gasAvailable := (u256 29973228) }
theorem charge108 : Z validJumps .PUSH1 state108 = .ok (middle108, 3) := by rfl
theorem step108 : StepOk 402 3 (.PUSH1, some ((u256 6), 1)) middle108 state109 := by rfl
theorem edge108 : X 403 validJumps state108 = X 402 validJumps state109 :=
  X_succ_of_continue decode108 charge108 step108 rfl

theorem decode109 : decodeAt state109 = (.MUL, none) := by rfl
def middle109 : EVM.State := { state109 with gasAvailable := (u256 29973225) }
theorem charge109 : Z validJumps .MUL state109 = .ok (middle109, 5) := by rfl
theorem step109 : StepOk 401 5 (.MUL, none) middle109 state110 := by rfl
theorem edge109 : X 402 validJumps state109 = X 401 validJumps state110 :=
  X_succ_of_continue decode109 charge109 step109 rfl

theorem decode110 : decodeAt state110 = (.PUSH1, some ((u256 4), 1)) := by rfl
def middle110 : EVM.State := { state110 with gasAvailable := (u256 29973220) }
theorem charge110 : Z validJumps .PUSH1 state110 = .ok (middle110, 3) := by rfl
theorem step110 : StepOk 400 3 (.PUSH1, some ((u256 4), 1)) middle110 state111 := by rfl
theorem edge110 : X 401 validJumps state110 = X 400 validJumps state111 :=
  X_succ_of_continue decode110 charge110 step110 rfl

theorem decode111 : decodeAt state111 = (.ADD, none) := by rfl
def middle111 : EVM.State := { state111 with gasAvailable := (u256 29973217) }
theorem charge111 : Z validJumps .ADD state111 = .ok (middle111, 3) := by rfl
theorem step111 : StepOk 399 3 (.ADD, none) middle111 state112 := by rfl
theorem edge111 : X 400 validJumps state111 = X 399 validJumps state112 :=
  X_succ_of_continue decode111 charge111 step111 rfl

theorem decode112 : decodeAt state112 = (.PUSH0, none) := by rfl
def middle112 : EVM.State := { state112 with gasAvailable := (u256 29973214) }
theorem charge112 : Z validJumps .PUSH0 state112 = .ok (middle112, 2) := by rfl
theorem step112 : StepOk 398 2 (.PUSH0, none) middle112 state113 := by rfl
theorem edge112 : X 399 validJumps state112 = X 398 validJumps state113 :=
  X_succ_of_continue decode112 charge112 step112 rfl

theorem decode113 : decodeAt state113 = (.CALLDATALOAD, none) := by rfl
def middle113 : EVM.State := { state113 with gasAvailable := (u256 29973212) }
theorem charge113 : Z validJumps .CALLDATALOAD state113 = .ok (middle113, 3) := by rfl
theorem load113 : middle113.toState.calldataload (u256 0) = (u256 3178606371220444580254889784552217078325058402586211561867463090413301597959) := by
  unfold EvmYul.State.calldataload ByteArray.readBytes
  dsimp only []
  rw [zeroes_sub32 _ (by decide +kernel)]
  decide +kernel
theorem step113 : StepOk 397 3 (.CALLDATALOAD, none) middle113 state114 := by
  change Except.ok (Eip8282.Audit.SymExec.bump 3 middle113 (middle113.replaceStackAndIncrPC (middle113.toState.calldataload (u256 0) :: [(u256 4), (u256 0)]))) = .ok state114
  rw [load113]
  rfl
theorem edge113 : X 398 validJumps state113 = X 397 validJumps state114 :=
  X_succ_of_continue decode113 charge113 step113 rfl

theorem decode114 : decodeAt state114 = (.DUP2, none) := by rfl
def middle114 : EVM.State := { state114 with gasAvailable := (u256 29973209) }
theorem charge114 : Z validJumps .DUP2 state114 = .ok (middle114, 3) := by rfl
theorem step114 : StepOk 396 3 (.DUP2, none) middle114 state115 := by rfl
theorem edge114 : X 397 validJumps state114 = X 396 validJumps state115 :=
  X_succ_of_continue decode114 charge114 step114 rfl

theorem decode115 : decodeAt state115 = (.SSTORE, none) := by rfl
def middle115 : EVM.State := { state115 with gasAvailable := (u256 29973206) }
theorem charge115 : Z validJumps .SSTORE state115 = .ok (middle115, 22100) := by rfl
theorem step115 : StepOk 395 22100 (.SSTORE, none) middle115 state116 := by rfl
theorem edge115 : X 396 validJumps state115 = X 395 validJumps state116 :=
  X_succ_of_continue decode115 charge115 step115 rfl

theorem decode116 : decodeAt state116 = (.PUSH1, some ((u256 1), 1)) := by rfl
def middle116 : EVM.State := { state116 with gasAvailable := (u256 29951106) }
theorem charge116 : Z validJumps .PUSH1 state116 = .ok (middle116, 3) := by rfl
theorem step116 : StepOk 394 3 (.PUSH1, some ((u256 1), 1)) middle116 state117 := by rfl
theorem edge116 : X 395 validJumps state116 = X 394 validJumps state117 :=
  X_succ_of_continue decode116 charge116 step116 rfl

theorem decode117 : decodeAt state117 = (.ADD, none) := by rfl
def middle117 : EVM.State := { state117 with gasAvailable := (u256 29951103) }
theorem charge117 : Z validJumps .ADD state117 = .ok (middle117, 3) := by rfl
theorem step117 : StepOk 393 3 (.ADD, none) middle117 state118 := by rfl
theorem edge117 : X 394 validJumps state117 = X 393 validJumps state118 :=
  X_succ_of_continue decode117 charge117 step117 rfl

theorem decode118 : decodeAt state118 = (.PUSH1, some ((u256 32), 1)) := by rfl
def middle118 : EVM.State := { state118 with gasAvailable := (u256 29951100) }
theorem charge118 : Z validJumps .PUSH1 state118 = .ok (middle118, 3) := by rfl
theorem step118 : StepOk 392 3 (.PUSH1, some ((u256 32), 1)) middle118 state119 := by rfl
theorem edge118 : X 393 validJumps state118 = X 392 validJumps state119 :=
  X_succ_of_continue decode118 charge118 step118 rfl

theorem decode119 : decodeAt state119 = (.CALLDATALOAD, none) := by rfl
def middle119 : EVM.State := { state119 with gasAvailable := (u256 29951097) }
theorem charge119 : Z validJumps .CALLDATALOAD state119 = .ok (middle119, 3) := by rfl
theorem load119 : middle119.toState.calldataload (u256 32) = (u256 3178606371220444580254889784552217078325058402586211561867463090413301597959) := by
  unfold EvmYul.State.calldataload ByteArray.readBytes
  dsimp only []
  rw [zeroes_sub32 _ (by decide +kernel)]
  decide +kernel
theorem step119 : StepOk 391 3 (.CALLDATALOAD, none) middle119 state120 := by
  change Except.ok (Eip8282.Audit.SymExec.bump 3 middle119 (middle119.replaceStackAndIncrPC (middle119.toState.calldataload (u256 32) :: [(u256 5), (u256 0)]))) = .ok state120
  rw [load119]
  rfl
theorem edge119 : X 392 validJumps state119 = X 391 validJumps state120 :=
  X_succ_of_continue decode119 charge119 step119 rfl

theorem decode120 : decodeAt state120 = (.DUP2, none) := by rfl
def middle120 : EVM.State := { state120 with gasAvailable := (u256 29951094) }
theorem charge120 : Z validJumps .DUP2 state120 = .ok (middle120, 3) := by rfl
theorem step120 : StepOk 390 3 (.DUP2, none) middle120 state121 := by rfl
theorem edge120 : X 391 validJumps state120 = X 390 validJumps state121 :=
  X_succ_of_continue decode120 charge120 step120 rfl

theorem decode121 : decodeAt state121 = (.SSTORE, none) := by rfl
def middle121 : EVM.State := { state121 with gasAvailable := (u256 29951091) }
theorem charge121 : Z validJumps .SSTORE state121 = .ok (middle121, 22100) := by rfl
theorem step121 : StepOk 389 22100 (.SSTORE, none) middle121 state122 := by rfl
theorem edge121 : X 390 validJumps state121 = X 389 validJumps state122 :=
  X_succ_of_continue decode121 charge121 step121 rfl

theorem decode122 : decodeAt state122 = (.PUSH1, some ((u256 1), 1)) := by rfl
def middle122 : EVM.State := { state122 with gasAvailable := (u256 29928991) }
theorem charge122 : Z validJumps .PUSH1 state122 = .ok (middle122, 3) := by rfl
theorem step122 : StepOk 388 3 (.PUSH1, some ((u256 1), 1)) middle122 state123 := by rfl
theorem edge122 : X 389 validJumps state122 = X 388 validJumps state123 :=
  X_succ_of_continue decode122 charge122 step122 rfl

theorem decode123 : decodeAt state123 = (.ADD, none) := by rfl
def middle123 : EVM.State := { state123 with gasAvailable := (u256 29928988) }
theorem charge123 : Z validJumps .ADD state123 = .ok (middle123, 3) := by rfl
theorem step123 : StepOk 387 3 (.ADD, none) middle123 state124 := by rfl
theorem edge123 : X 388 validJumps state123 = X 387 validJumps state124 :=
  X_succ_of_continue decode123 charge123 step123 rfl

theorem decode124 : decodeAt state124 = (.PUSH1, some ((u256 64), 1)) := by rfl
def middle124 : EVM.State := { state124 with gasAvailable := (u256 29928985) }
theorem charge124 : Z validJumps .PUSH1 state124 = .ok (middle124, 3) := by rfl
theorem step124 : StepOk 386 3 (.PUSH1, some ((u256 64), 1)) middle124 state125 := by rfl
theorem edge124 : X 387 validJumps state124 = X 386 validJumps state125 :=
  X_succ_of_continue decode124 charge124 step124 rfl

theorem decode125 : decodeAt state125 = (.CALLDATALOAD, none) := by rfl
def middle125 : EVM.State := { state125 with gasAvailable := (u256 29928982) }
theorem charge125 : Z validJumps .CALLDATALOAD state125 = .ok (middle125, 3) := by rfl
theorem load125 : middle125.toState.calldataload (u256 64) = (u256 3178606371220444580254889784552217078315717318022514897140723641858688222983) := by
  unfold EvmYul.State.calldataload ByteArray.readBytes
  dsimp only []
  rw [zeroes_sub32 _ (by decide +kernel)]
  decide +kernel
theorem step125 : StepOk 385 3 (.CALLDATALOAD, none) middle125 state126 := by
  change Except.ok (Eip8282.Audit.SymExec.bump 3 middle125 (middle125.replaceStackAndIncrPC (middle125.toState.calldataload (u256 64) :: [(u256 6), (u256 0)]))) = .ok state126
  rw [load125]
  rfl
theorem edge125 : X 386 validJumps state125 = X 385 validJumps state126 :=
  X_succ_of_continue decode125 charge125 step125 rfl

theorem decode126 : decodeAt state126 = (.DUP2, none) := by rfl
def middle126 : EVM.State := { state126 with gasAvailable := (u256 29928979) }
theorem charge126 : Z validJumps .DUP2 state126 = .ok (middle126, 3) := by rfl
theorem step126 : StepOk 384 3 (.DUP2, none) middle126 state127 := by rfl
theorem edge126 : X 385 validJumps state126 = X 384 validJumps state127 :=
  X_succ_of_continue decode126 charge126 step126 rfl

theorem decode127 : decodeAt state127 = (.SSTORE, none) := by rfl
def middle127 : EVM.State := { state127 with gasAvailable := (u256 29928976) }
theorem charge127 : Z validJumps .SSTORE state127 = .ok (middle127, 22100) := by rfl
theorem step127 : StepOk 383 22100 (.SSTORE, none) middle127 state128 := by rfl
theorem edge127 : X 384 validJumps state127 = X 383 validJumps state128 :=
  X_succ_of_continue decode127 charge127 step127 rfl

theorem decode128 : decodeAt state128 = (.PUSH1, some ((u256 1), 1)) := by rfl
def middle128 : EVM.State := { state128 with gasAvailable := (u256 29906876) }
theorem charge128 : Z validJumps .PUSH1 state128 = .ok (middle128, 3) := by rfl
theorem step128 : StepOk 382 3 (.PUSH1, some ((u256 1), 1)) middle128 state129 := by rfl
theorem edge128 : X 383 validJumps state128 = X 382 validJumps state129 :=
  X_succ_of_continue decode128 charge128 step128 rfl

theorem decode129 : decodeAt state129 = (.ADD, none) := by rfl
def middle129 : EVM.State := { state129 with gasAvailable := (u256 29906873) }
theorem charge129 : Z validJumps .ADD state129 = .ok (middle129, 3) := by rfl
theorem step129 : StepOk 381 3 (.ADD, none) middle129 state130 := by rfl
theorem edge129 : X 382 validJumps state129 = X 381 validJumps state130 :=
  X_succ_of_continue decode129 charge129 step129 rfl

theorem decode130 : decodeAt state130 = (.PUSH1, some ((u256 96), 1)) := by rfl
def middle130 : EVM.State := { state130 with gasAvailable := (u256 29906870) }
theorem charge130 : Z validJumps .PUSH1 state130 = .ok (middle130, 3) := by rfl
theorem step130 : StepOk 380 3 (.PUSH1, some ((u256 96), 1)) middle130 state131 := by rfl
theorem edge130 : X 381 validJumps state130 = X 380 validJumps state131 :=
  X_succ_of_continue decode130 charge130 step130 rfl

theorem decode131 : decodeAt state131 = (.CALLDATALOAD, none) := by rfl
def middle131 : EVM.State := { state131 with gasAvailable := (u256 29906867) }
theorem charge131 : Z validJumps .CALLDATALOAD state131 = .ok (middle131, 3) := by rfl
theorem load131 : middle131.toState.calldataload (u256 96) = (u256 3178606371220444580254889784552217078325058402586211561867463090413301597959) := by
  unfold EvmYul.State.calldataload ByteArray.readBytes
  dsimp only []
  rw [zeroes_sub32 _ (by decide +kernel)]
  decide +kernel
theorem step131 : StepOk 379 3 (.CALLDATALOAD, none) middle131 state132 := by
  change Except.ok (Eip8282.Audit.SymExec.bump 3 middle131 (middle131.replaceStackAndIncrPC (middle131.toState.calldataload (u256 96) :: [(u256 7), (u256 0)]))) = .ok state132
  rw [load131]
  rfl
theorem edge131 : X 380 validJumps state131 = X 379 validJumps state132 :=
  X_succ_of_continue decode131 charge131 step131 rfl

theorem decode132 : decodeAt state132 = (.DUP2, none) := by rfl
def middle132 : EVM.State := { state132 with gasAvailable := (u256 29906864) }
theorem charge132 : Z validJumps .DUP2 state132 = .ok (middle132, 3) := by rfl
theorem step132 : StepOk 378 3 (.DUP2, none) middle132 state133 := by rfl
theorem edge132 : X 379 validJumps state132 = X 378 validJumps state133 :=
  X_succ_of_continue decode132 charge132 step132 rfl

theorem decode133 : decodeAt state133 = (.SSTORE, none) := by rfl
def middle133 : EVM.State := { state133 with gasAvailable := (u256 29906861) }
theorem charge133 : Z validJumps .SSTORE state133 = .ok (middle133, 22100) := by rfl
theorem step133 : StepOk 377 22100 (.SSTORE, none) middle133 state134 := by rfl
theorem edge133 : X 378 validJumps state133 = X 377 validJumps state134 :=
  X_succ_of_continue decode133 charge133 step133 rfl

theorem decode134 : decodeAt state134 = (.PUSH1, some ((u256 1), 1)) := by rfl
def middle134 : EVM.State := { state134 with gasAvailable := (u256 29884761) }
theorem charge134 : Z validJumps .PUSH1 state134 = .ok (middle134, 3) := by rfl
theorem step134 : StepOk 376 3 (.PUSH1, some ((u256 1), 1)) middle134 state135 := by rfl
theorem edge134 : X 377 validJumps state134 = X 376 validJumps state135 :=
  X_succ_of_continue decode134 charge134 step134 rfl

theorem decode135 : decodeAt state135 = (.ADD, none) := by rfl
def middle135 : EVM.State := { state135 with gasAvailable := (u256 29884758) }
theorem charge135 : Z validJumps .ADD state135 = .ok (middle135, 3) := by rfl
theorem step135 : StepOk 375 3 (.ADD, none) middle135 state136 := by rfl
theorem edge135 : X 376 validJumps state135 = X 375 validJumps state136 :=
  X_succ_of_continue decode135 charge135 step135 rfl

theorem decode136 : decodeAt state136 = (.PUSH1, some ((u256 128), 1)) := by rfl
def middle136 : EVM.State := { state136 with gasAvailable := (u256 29884755) }
theorem charge136 : Z validJumps .PUSH1 state136 = .ok (middle136, 3) := by rfl
theorem step136 : StepOk 374 3 (.PUSH1, some ((u256 128), 1)) middle136 state137 := by rfl
theorem edge136 : X 375 validJumps state136 = X 374 validJumps state137 :=
  X_succ_of_continue decode136 charge136 step136 rfl

theorem decode137 : decodeAt state137 = (.CALLDATALOAD, none) := by rfl
def middle137 : EVM.State := { state137 with gasAvailable := (u256 29884752) }
theorem charge137 : Z validJumps .CALLDATALOAD state137 = .ok (middle137, 3) := by rfl
theorem load137 : middle137.toState.calldataload (u256 128) = (u256 3178606371220444580254889784552217078325058402586211561867463090413301597959) := by
  unfold EvmYul.State.calldataload ByteArray.readBytes
  dsimp only []
  rw [zeroes_sub32 _ (by decide +kernel)]
  decide +kernel
theorem step137 : StepOk 373 3 (.CALLDATALOAD, none) middle137 state138 := by
  change Except.ok (Eip8282.Audit.SymExec.bump 3 middle137 (middle137.replaceStackAndIncrPC (middle137.toState.calldataload (u256 128) :: [(u256 8), (u256 0)]))) = .ok state138
  rw [load137]
  rfl
theorem edge137 : X 374 validJumps state137 = X 373 validJumps state138 :=
  X_succ_of_continue decode137 charge137 step137 rfl

theorem decode138 : decodeAt state138 = (.DUP2, none) := by rfl
def middle138 : EVM.State := { state138 with gasAvailable := (u256 29884749) }
theorem charge138 : Z validJumps .DUP2 state138 = .ok (middle138, 3) := by rfl
theorem step138 : StepOk 372 3 (.DUP2, none) middle138 state139 := by rfl
theorem edge138 : X 373 validJumps state138 = X 372 validJumps state139 :=
  X_succ_of_continue decode138 charge138 step138 rfl

theorem decode139 : decodeAt state139 = (.SSTORE, none) := by rfl
def middle139 : EVM.State := { state139 with gasAvailable := (u256 29884746) }
theorem charge139 : Z validJumps .SSTORE state139 = .ok (middle139, 22100) := by rfl
theorem step139 : StepOk 371 22100 (.SSTORE, none) middle139 state140 := by rfl
theorem edge139 : X 372 validJumps state139 = X 371 validJumps state140 :=
  X_succ_of_continue decode139 charge139 step139 rfl

theorem decode140 : decodeAt state140 = (.PUSH1, some ((u256 1), 1)) := by rfl
def middle140 : EVM.State := { state140 with gasAvailable := (u256 29862646) }
theorem charge140 : Z validJumps .PUSH1 state140 = .ok (middle140, 3) := by rfl
theorem step140 : StepOk 370 3 (.PUSH1, some ((u256 1), 1)) middle140 state141 := by rfl
theorem edge140 : X 371 validJumps state140 = X 370 validJumps state141 :=
  X_succ_of_continue decode140 charge140 step140 rfl

theorem decode141 : decodeAt state141 = (.ADD, none) := by rfl
def middle141 : EVM.State := { state141 with gasAvailable := (u256 29862643) }
theorem charge141 : Z validJumps .ADD state141 = .ok (middle141, 3) := by rfl
theorem step141 : StepOk 369 3 (.ADD, none) middle141 state142 := by rfl
theorem edge141 : X 370 validJumps state141 = X 369 validJumps state142 :=
  X_succ_of_continue decode141 charge141 step141 rfl

theorem decode142 : decodeAt state142 = (.PUSH1, some ((u256 160), 1)) := by rfl
def middle142 : EVM.State := { state142 with gasAvailable := (u256 29862640) }
theorem charge142 : Z validJumps .PUSH1 state142 = .ok (middle142, 3) := by rfl
theorem step142 : StepOk 368 3 (.PUSH1, some ((u256 160), 1)) middle142 state143 := by rfl
theorem edge142 : X 369 validJumps state142 = X 368 validJumps state143 :=
  X_succ_of_continue decode142 charge142 step142 rfl

theorem decode143 : decodeAt state143 = (.CALLDATALOAD, none) := by rfl
def middle143 : EVM.State := { state143 with gasAvailable := (u256 29862637) }
theorem charge143 : Z validJumps .CALLDATALOAD state143 = .ok (middle143, 3) := by rfl
theorem load143 : middle143.toState.calldataload (u256 160) = (u256 3178606371220444580254889784552217078325058402586211561866956709203435061248) := by
  unfold EvmYul.State.calldataload ByteArray.readBytes
  dsimp only []
  rw [zeroes_sub32 _ (by decide +kernel)]
  decide +kernel
theorem step143 : StepOk 367 3 (.CALLDATALOAD, none) middle143 state144 := by
  change Except.ok (Eip8282.Audit.SymExec.bump 3 middle143 (middle143.replaceStackAndIncrPC (middle143.toState.calldataload (u256 160) :: [(u256 9), (u256 0)]))) = .ok state144
  rw [load143]
  rfl
theorem edge143 : X 368 validJumps state143 = X 367 validJumps state144 :=
  X_succ_of_continue decode143 charge143 step143 rfl

theorem decode144 : decodeAt state144 = (.SWAP1, none) := by rfl
def middle144 : EVM.State := { state144 with gasAvailable := (u256 29862634) }
theorem charge144 : Z validJumps .SWAP1 state144 = .ok (middle144, 3) := by rfl
theorem step144 : StepOk 366 3 (.SWAP1, none) middle144 state145 := by rfl
theorem edge144 : X 367 validJumps state144 = X 366 validJumps state145 :=
  X_succ_of_continue decode144 charge144 step144 rfl

theorem decode145 : decodeAt state145 = (.SSTORE, none) := by rfl
def middle145 : EVM.State := { state145 with gasAvailable := (u256 29862631) }
theorem charge145 : Z validJumps .SSTORE state145 = .ok (middle145, 22100) := by rfl
theorem step145 : StepOk 365 22100 (.SSTORE, none) middle145 state146 := by rfl
theorem edge145 : X 366 validJumps state145 = X 365 validJumps state146 :=
  X_succ_of_continue decode145 charge145 step145 rfl

theorem decode146 : decodeAt state146 = (.PUSH1, some ((u256 184), 1)) := by rfl
def middle146 : EVM.State := { state146 with gasAvailable := (u256 29840531) }
theorem charge146 : Z validJumps .PUSH1 state146 = .ok (middle146, 3) := by rfl
theorem step146 : StepOk 364 3 (.PUSH1, some ((u256 184), 1)) middle146 state147 := by rfl
theorem edge146 : X 365 validJumps state146 = X 364 validJumps state147 :=
  X_succ_of_continue decode146 charge146 step146 rfl

theorem decode147 : decodeAt state147 = (.PUSH0, none) := by rfl
def middle147 : EVM.State := { state147 with gasAvailable := (u256 29840528) }
theorem charge147 : Z validJumps .PUSH0 state147 = .ok (middle147, 2) := by rfl
theorem step147 : StepOk 363 2 (.PUSH0, none) middle147 state148 := by rfl
theorem edge147 : X 364 validJumps state147 = X 363 validJumps state148 :=
  X_succ_of_continue decode147 charge147 step147 rfl

theorem decode148 : decodeAt state148 = (.PUSH0, none) := by rfl
def middle148 : EVM.State := { state148 with gasAvailable := (u256 29840526) }
theorem charge148 : Z validJumps .PUSH0 state148 = .ok (middle148, 2) := by rfl
theorem step148 : StepOk 362 2 (.PUSH0, none) middle148 state149 := by rfl
theorem edge148 : X 363 validJumps state148 = X 362 validJumps state149 :=
  X_succ_of_continue decode148 charge148 step148 rfl

theorem decode149 : decodeAt state149 = (.CALLDATACOPY, none) := by rfl
def middle149 : EVM.State := { state149 with gasAvailable := (u256 29840506) }
theorem charge149 : Z validJumps .CALLDATACOPY state149 = .ok (middle149, 21) := by rfl
theorem step149 : StepOk 361 21 (.CALLDATACOPY, none) middle149 state150 := by rfl
theorem edge149 : X 362 validJumps state149 = X 361 validJumps state150 :=
  X_succ_of_continue decode149 charge149 step149 rfl

theorem decode150 : decodeAt state150 = (.PUSH1, some ((u256 0), 1)) := by rfl
def middle150 : EVM.State := { state150 with gasAvailable := (u256 29840485) }
theorem charge150 : Z validJumps .PUSH1 state150 = .ok (middle150, 3) := by rfl
theorem step150 : StepOk 360 3 (.PUSH1, some ((u256 0), 1)) middle150 state151 := by rfl
theorem edge150 : X 361 validJumps state150 = X 360 validJumps state151 :=
  X_succ_of_continue decode150 charge150 step150 rfl

theorem decode151 : decodeAt state151 = (.PUSH0, none) := by rfl
def middle151 : EVM.State := { state151 with gasAvailable := (u256 29840482) }
theorem charge151 : Z validJumps .PUSH0 state151 = .ok (middle151, 2) := by rfl
theorem step151 : StepOk 359 2 (.PUSH0, none) middle151 state152 := by rfl
theorem edge151 : X 360 validJumps state151 = X 359 validJumps state152 :=
  X_succ_of_continue decode151 charge151 step151 rfl

theorem decode152 : decodeAt state152 = (.LOG0, none) := by rfl
def middle152 : EVM.State := { state152 with gasAvailable := (u256 29840480) }
theorem charge152 : Z validJumps .LOG0 state152 = .ok (middle152, 375) := by rfl
theorem logdata152 : middle152.memory.readWithPadding 0 0 = .empty := by
  apply ByteArray.ext
  exact Array.eq_empty_of_size_eq_zero (Eip8282.Audit.XiTransport.readWithPadding_size_zero _ _)
theorem step152 : StepOk 358 375 (.LOG0, none) middle152 state153 := by
  change Except.ok (Eip8282.Audit.SymExec.bump 375 middle152 (({ middle152 with toSharedState := SharedState.logOp (u256 0) (u256 0) #[] middle152.toSharedState } : EVM.State).replaceStackAndIncrPC [(u256 0)])) = .ok state153
  unfold SharedState.logOp
  dsimp only []
  simp only [show (u256 0).toNat = 0 from rfl, logdata152]
  rfl
theorem edge152 : X 359 validJumps state152 = X 358 validJumps state153 :=
  X_succ_of_continue decode152 charge152 step152 rfl

theorem decode153 : decodeAt state153 = (.PUSH1, some ((u256 1), 1)) := by rfl
def middle153 : EVM.State := { state153 with gasAvailable := (u256 29840105) }
theorem charge153 : Z validJumps .PUSH1 state153 = .ok (middle153, 3) := by rfl
theorem step153 : StepOk 357 3 (.PUSH1, some ((u256 1), 1)) middle153 state154 := by rfl
theorem edge153 : X 358 validJumps state153 = X 357 validJumps state154 :=
  X_succ_of_continue decode153 charge153 step153 rfl

theorem decode154 : decodeAt state154 = (.ADD, none) := by rfl
def middle154 : EVM.State := { state154 with gasAvailable := (u256 29840102) }
theorem charge154 : Z validJumps .ADD state154 = .ok (middle154, 3) := by rfl
theorem step154 : StepOk 356 3 (.ADD, none) middle154 state155 := by rfl
theorem edge154 : X 357 validJumps state154 = X 356 validJumps state155 :=
  X_succ_of_continue decode154 charge154 step154 rfl

theorem decode155 : decodeAt state155 = (.PUSH1, some ((u256 3), 1)) := by rfl
def middle155 : EVM.State := { state155 with gasAvailable := (u256 29840099) }
theorem charge155 : Z validJumps .PUSH1 state155 = .ok (middle155, 3) := by rfl
theorem step155 : StepOk 355 3 (.PUSH1, some ((u256 3), 1)) middle155 state156 := by rfl
theorem edge155 : X 356 validJumps state155 = X 355 validJumps state156 :=
  X_succ_of_continue decode155 charge155 step155 rfl

theorem decode156 : decodeAt state156 = (.SSTORE, none) := by rfl
def middle156 : EVM.State := { state156 with gasAvailable := (u256 29840096) }
theorem charge156 : Z validJumps .SSTORE state156 = .ok (middle156, 20000) := by rfl
theorem step156 : StepOk 354 20000 (.SSTORE, none) middle156 state157 := by rfl
theorem edge156 : X 355 validJumps state156 = X 354 validJumps state157 :=
  X_succ_of_continue decode156 charge156 step156 rfl

theorem decode157 : decodeAt state157 = (.STOP, none) := by rfl
def middle157 : EVM.State := { state157 with gasAvailable := (u256 29820096) }
theorem charge157 : Z validJumps .STOP state157 = .ok (middle157, 0) := by rfl
theorem step157 : StepOk 353 0 (.STOP, none) middle157 state158 := by rfl
theorem halt : X 354 validJumps state157 = .ok (.success state158 .empty) :=
  X_succ_of_halt decode157 charge157 step157 rfl (by decide)

/- Keep elaboration from recomputing X while composing its proved edges.
This local transparency setting changes no definition or theorem premise. -/
attribute [local irreducible] EvmYul.EVM.X

theorem kernel_run : X 511 validJumps initial = .ok (.success state158 .empty) := by
  change X 511 validJumps state0 = _
  exact edge0.trans (edge1.trans (edge2.trans (edge3.trans (edge4.trans (edge5.trans (edge6.trans (edge7.trans (edge8.trans (edge9.trans (edge10.trans (edge11.trans (edge12.trans (edge13.trans (edge14.trans (edge15.trans (edge16.trans (edge17.trans (edge18.trans (edge19.trans (edge20.trans (edge21.trans (edge22.trans (edge23.trans (edge24.trans (edge25.trans (edge26.trans (edge27.trans (edge28.trans (edge29.trans (edge30.trans (edge31.trans (edge32.trans (edge33.trans (edge34.trans (edge35.trans (edge36.trans (edge37.trans (edge38.trans (edge39.trans (edge40.trans (edge41.trans (edge42.trans (edge43.trans (edge44.trans (edge45.trans (edge46.trans (edge47.trans (edge48.trans (edge49.trans (edge50.trans (edge51.trans (edge52.trans (edge53.trans (edge54.trans (edge55.trans (edge56.trans (edge57.trans (edge58.trans (edge59.trans (edge60.trans (edge61.trans (edge62.trans (edge63.trans (edge64.trans (edge65.trans (edge66.trans (edge67.trans (edge68.trans (edge69.trans (edge70.trans (edge71.trans (edge72.trans (edge73.trans (edge74.trans (edge75.trans (edge76.trans (edge77.trans (edge78.trans (edge79.trans (edge80.trans (edge81.trans (edge82.trans (edge83.trans (edge84.trans (edge85.trans (edge86.trans (edge87.trans (edge88.trans (edge89.trans (edge90.trans (edge91.trans (edge92.trans (edge93.trans (edge94.trans (edge95.trans (edge96.trans (edge97.trans (edge98.trans (edge99.trans (edge100.trans (edge101.trans (edge102.trans (edge103.trans (edge104.trans (edge105.trans (edge106.trans (edge107.trans (edge108.trans (edge109.trans (edge110.trans (edge111.trans (edge112.trans (edge113.trans (edge114.trans (edge115.trans (edge116.trans (edge117.trans (edge118.trans (edge119.trans (edge120.trans (edge121.trans (edge122.trans (edge123.trans (edge124.trans (edge125.trans (edge126.trans (edge127.trans (edge128.trans (edge129.trans (edge130.trans (edge131.trans (edge132.trans (edge133.trans (edge134.trans (edge135.trans (edge136.trans (edge137.trans (edge138.trans (edge139.trans (edge140.trans (edge141.trans (edge142.trans (edge143.trans (edge144.trans (edge145.trans (edge146.trans (edge147.trans (edge148.trans (edge149.trans (edge150.trans (edge151.trans (edge152.trans (edge153.trans (edge154.trans (edge155.trans (edge156.trans (halt)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem execution_result :
    (fixture PSubmit1Mutant.logSizeMutatedDeposit).execution =
      .ok (.success (state158.createdAccounts, state158.accountMap,
        state158.gasAvailable, state158.substate) .empty) := by
  change (do
    let r ← X 511 (D_J initial.executionEnv.code ⟨0⟩) initial
    match r with
    | .success st out => Except.ok (ExecutionResult.success (st.createdAccounts, st.accountMap, st.gasAvailable, st.substate) out)
    | .revert gas out => Except.ok (ExecutionResult.revert gas out) : Eip8282.Audit.EvmRunner.RunResult) = _
  rw [validJumps_eq, kernel_run]
  rfl

theorem actual_empty_log : hasEmptyLog (fixture PSubmit1Mutant.logSizeMutatedDeposit) = true := by
  unfold hasEmptyLog
  rw [MessageCall.result_eq_settle, execution_result]
  rfl

#print axioms kernel_run
#print axioms execution_result
#print axioms actual_empty_log
end Eip8282.Tests.DirectThetaSubmitMutation


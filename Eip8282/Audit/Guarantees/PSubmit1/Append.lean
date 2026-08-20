/-
CFG-direct `∀` append for P-SUBMIT-1 (`handle_input`).

F4 left `A-ABSTRACT-TX` open, so this module does not reduce `EvmYul.EVM.Ξ`.
It steps the pinned `handle_input` opcode sequence (F1: deposit PC 159,
exit PC 158) on symbolic calldata and storage under `WellFormed` / `CallHyp`.

Fee is a stack parameter (S4 fake-exponential is not used). Paying means
the three (deposit) / one (exit) `JUMPI @revert` guards fall through.
-/

import Eip8282.Audit.Correspondence

namespace Eip8282.Audit.Guarantees.PSubmit1.Append

open EvmYul
open EvmYul.Operation
open Eip8282.Audit.Bytecode
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Correspondence
open Eip8282.Audit.EvmRunner (calldataWord)
open Eip8282.Audit.Step (isUserCaller campaignGasBound)

set_option maxRecDepth 20000
set_option linter.unusedVariables false

/-! ## Pinned `handle_input` fragments

Copied from `depositRuntimeHex` / `exitRuntimeHex` at the F1 PCs through
the write-path `STOP`. The fragments are `ByteArray.mk` of those bytes
(so `opcodeAt` is `rfl` without unfolding `fromHex`).
-/

/-- Bytes 159..283 of `depositRuntime` (`JUMPDEST handle_input` .. `STOP`). -/
def depositHandleInputHex : String :=
  "5b8034106102705760383567ffffffffffffffff1680633b9aca00116102705763" ++
    "3b9aca0002903403106102705760015460010160015560035480600602600401" ++
    "5f35815560010160203581556001016040358155600101606035815560010160" ++
    "8035815560010160a035905560b85f5f3760b85fa060010160035500"

def depositHandleInput : ByteArray :=
  ByteArray.mk #[0x5b, 0x80, 0x34, 0x10, 0x61, 0x02, 0x70, 0x57, 0x60, 0x38, 0x35, 0x67, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x16, 0x80, 0x63, 0x3b, 0x9a, 0xca, 0x00, 0x11, 0x61, 0x02, 0x70, 0x57, 0x63, 0x3b, 0x9a, 0xca, 0x00, 0x02, 0x90, 0x34, 0x03, 0x10, 0x61, 0x02, 0x70, 0x57, 0x60, 0x01, 0x54, 0x60, 0x01, 0x01, 0x60, 0x01, 0x55, 0x60, 0x03, 0x54, 0x80, 0x60, 0x06, 0x02, 0x60, 0x04, 0x01, 0x5f, 0x35, 0x81, 0x55, 0x60, 0x01, 0x01, 0x60, 0x20, 0x35, 0x81, 0x55, 0x60, 0x01, 0x01, 0x60, 0x40, 0x35, 0x81, 0x55, 0x60, 0x01, 0x01, 0x60, 0x60, 0x35, 0x81, 0x55, 0x60, 0x01, 0x01, 0x60, 0x80, 0x35, 0x81, 0x55, 0x60, 0x01, 0x01, 0x60, 0xa0, 0x35, 0x90, 0x55, 0x60, 0xb8, 0x5f, 0x5f, 0x37, 0x60, 0xb8, 0x5f, 0xa0, 0x60, 0x01, 0x01, 0x60, 0x03, 0x55, 0x00]

/-- Bytes 158..224 of `exitRuntime` (`JUMPDEST handle_input` .. `STOP`). -/
def exitHandleInputHex : String :=
  "5b34106101c657600154600101600155600354806003026004013381556001015f35" ++
    "815560010160203590553360601b5f5260305f60143760445fa060010160035500"

def exitHandleInput : ByteArray :=
  ByteArray.mk #[0x5b, 0x34, 0x10, 0x61, 0x01, 0xc6, 0x57, 0x60, 0x01, 0x54, 0x60, 0x01, 0x01, 0x60, 0x01, 0x55, 0x60, 0x03, 0x54, 0x80, 0x60, 0x03, 0x02, 0x60, 0x04, 0x01, 0x33, 0x81, 0x55, 0x60, 0x01, 0x01, 0x5f, 0x35, 0x81, 0x55, 0x60, 0x01, 0x01, 0x60, 0x20, 0x35, 0x90, 0x55, 0x33, 0x60, 0x60, 0x1b, 0x5f, 0x52, 0x60, 0x30, 0x5f, 0x60, 0x14, 0x37, 0x60, 0x44, 0x5f, 0xa0, 0x60, 0x01, 0x01, 0x60, 0x03, 0x55, 0x00]

theorem depositHandleInput_size : depositHandleInput.size = 125 := rfl
theorem exitHandleInput_size : exitHandleInput.size = 67 := rfl

theorem deposit_handle_input_pc : Deposit.handle_input = 159 := rfl
theorem exit_handle_input_pc : Exit.handle_input = 158 := rfl

theorem deposit_handle_input_len :
    Deposit.read_requests - Deposit.handle_input = 125 := by
  decide

theorem exit_handle_input_len :
    Exit.read_requests - Exit.handle_input = 67 := by
  decide

/-! ## Opcode-at-PC (`rfl` on the fragments) -/

theorem dOp_0 :
    opcodeAt depositHandleInput 0 =
      some (.JUMPDEST, none) :=
  rfl

theorem dOp_1 :
    opcodeAt depositHandleInput 1 =
      some (.DUP1, none) :=
  rfl

theorem dOp_2 :
    opcodeAt depositHandleInput 2 =
      some (.CALLVALUE, none) :=
  rfl

theorem dOp_3 :
    opcodeAt depositHandleInput 3 =
      some (.LT, none) :=
  rfl

theorem dOp_4 :
    opcodeAt depositHandleInput 4 =
      some (.PUSH2, some (UInt256.ofNat 624, 2)) :=
  rfl

theorem dOp_7 :
    opcodeAt depositHandleInput 7 =
      some (.JUMPI, none) :=
  rfl

theorem dOp_8 :
    opcodeAt depositHandleInput 8 =
      some (.PUSH1, some (UInt256.ofNat 56, 1)) :=
  rfl

theorem dOp_10 :
    opcodeAt depositHandleInput 10 =
      some (.CALLDATALOAD, none) :=
  rfl

theorem dOp_11 :
    opcodeAt depositHandleInput 11 =
      some (.PUSH8, some (UInt256.ofNat 18446744073709551615, 8)) :=
  rfl

theorem dOp_20 :
    opcodeAt depositHandleInput 20 =
      some (.AND, none) :=
  rfl

theorem dOp_21 :
    opcodeAt depositHandleInput 21 =
      some (.DUP1, none) :=
  rfl

theorem dOp_22 :
    opcodeAt depositHandleInput 22 =
      some (.PUSH4, some (UInt256.ofNat 1000000000, 4)) :=
  rfl

theorem dOp_27 :
    opcodeAt depositHandleInput 27 =
      some (.GT, none) :=
  rfl

theorem dOp_28 :
    opcodeAt depositHandleInput 28 =
      some (.PUSH2, some (UInt256.ofNat 624, 2)) :=
  rfl

theorem dOp_31 :
    opcodeAt depositHandleInput 31 =
      some (.JUMPI, none) :=
  rfl

theorem dOp_32 :
    opcodeAt depositHandleInput 32 =
      some (.PUSH4, some (UInt256.ofNat 1000000000, 4)) :=
  rfl

theorem dOp_37 :
    opcodeAt depositHandleInput 37 =
      some (.MUL, none) :=
  rfl

theorem dOp_38 :
    opcodeAt depositHandleInput 38 =
      some (.SWAP1, none) :=
  rfl

theorem dOp_39 :
    opcodeAt depositHandleInput 39 =
      some (.CALLVALUE, none) :=
  rfl

theorem dOp_40 :
    opcodeAt depositHandleInput 40 =
      some (.SUB, none) :=
  rfl

theorem dOp_41 :
    opcodeAt depositHandleInput 41 =
      some (.LT, none) :=
  rfl

theorem dOp_42 :
    opcodeAt depositHandleInput 42 =
      some (.PUSH2, some (UInt256.ofNat 624, 2)) :=
  rfl

theorem dOp_45 :
    opcodeAt depositHandleInput 45 =
      some (.JUMPI, none) :=
  rfl

theorem dOp_46 :
    opcodeAt depositHandleInput 46 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem dOp_48 :
    opcodeAt depositHandleInput 48 =
      some (.SLOAD, none) :=
  rfl

theorem dOp_49 :
    opcodeAt depositHandleInput 49 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem dOp_51 :
    opcodeAt depositHandleInput 51 =
      some (.ADD, none) :=
  rfl

theorem dOp_52 :
    opcodeAt depositHandleInput 52 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem dOp_54 :
    opcodeAt depositHandleInput 54 =
      some (.SSTORE, none) :=
  rfl

theorem dOp_55 :
    opcodeAt depositHandleInput 55 =
      some (.PUSH1, some (UInt256.ofNat 3, 1)) :=
  rfl

theorem dOp_57 :
    opcodeAt depositHandleInput 57 =
      some (.SLOAD, none) :=
  rfl

theorem dOp_58 :
    opcodeAt depositHandleInput 58 =
      some (.DUP1, none) :=
  rfl

theorem dOp_59 :
    opcodeAt depositHandleInput 59 =
      some (.PUSH1, some (UInt256.ofNat 6, 1)) :=
  rfl

theorem dOp_61 :
    opcodeAt depositHandleInput 61 =
      some (.MUL, none) :=
  rfl

theorem dOp_62 :
    opcodeAt depositHandleInput 62 =
      some (.PUSH1, some (UInt256.ofNat 4, 1)) :=
  rfl

theorem dOp_64 :
    opcodeAt depositHandleInput 64 =
      some (.ADD, none) :=
  rfl

theorem dOp_65 :
    opcodeAt depositHandleInput 65 =
      some (.PUSH0, none) :=
  rfl

theorem dOp_66 :
    opcodeAt depositHandleInput 66 =
      some (.CALLDATALOAD, none) :=
  rfl

theorem dOp_67 :
    opcodeAt depositHandleInput 67 =
      some (.DUP2, none) :=
  rfl

theorem dOp_68 :
    opcodeAt depositHandleInput 68 =
      some (.SSTORE, none) :=
  rfl

theorem dOp_69 :
    opcodeAt depositHandleInput 69 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem dOp_71 :
    opcodeAt depositHandleInput 71 =
      some (.ADD, none) :=
  rfl

theorem dOp_72 :
    opcodeAt depositHandleInput 72 =
      some (.PUSH1, some (UInt256.ofNat 32, 1)) :=
  rfl

theorem dOp_74 :
    opcodeAt depositHandleInput 74 =
      some (.CALLDATALOAD, none) :=
  rfl

theorem dOp_75 :
    opcodeAt depositHandleInput 75 =
      some (.DUP2, none) :=
  rfl

theorem dOp_76 :
    opcodeAt depositHandleInput 76 =
      some (.SSTORE, none) :=
  rfl

theorem dOp_77 :
    opcodeAt depositHandleInput 77 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem dOp_79 :
    opcodeAt depositHandleInput 79 =
      some (.ADD, none) :=
  rfl

theorem dOp_80 :
    opcodeAt depositHandleInput 80 =
      some (.PUSH1, some (UInt256.ofNat 64, 1)) :=
  rfl

theorem dOp_82 :
    opcodeAt depositHandleInput 82 =
      some (.CALLDATALOAD, none) :=
  rfl

theorem dOp_83 :
    opcodeAt depositHandleInput 83 =
      some (.DUP2, none) :=
  rfl

theorem dOp_84 :
    opcodeAt depositHandleInput 84 =
      some (.SSTORE, none) :=
  rfl

theorem dOp_85 :
    opcodeAt depositHandleInput 85 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem dOp_87 :
    opcodeAt depositHandleInput 87 =
      some (.ADD, none) :=
  rfl

theorem dOp_88 :
    opcodeAt depositHandleInput 88 =
      some (.PUSH1, some (UInt256.ofNat 96, 1)) :=
  rfl

theorem dOp_90 :
    opcodeAt depositHandleInput 90 =
      some (.CALLDATALOAD, none) :=
  rfl

theorem dOp_91 :
    opcodeAt depositHandleInput 91 =
      some (.DUP2, none) :=
  rfl

theorem dOp_92 :
    opcodeAt depositHandleInput 92 =
      some (.SSTORE, none) :=
  rfl

theorem dOp_93 :
    opcodeAt depositHandleInput 93 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem dOp_95 :
    opcodeAt depositHandleInput 95 =
      some (.ADD, none) :=
  rfl

theorem dOp_96 :
    opcodeAt depositHandleInput 96 =
      some (.PUSH1, some (UInt256.ofNat 128, 1)) :=
  rfl

theorem dOp_98 :
    opcodeAt depositHandleInput 98 =
      some (.CALLDATALOAD, none) :=
  rfl

theorem dOp_99 :
    opcodeAt depositHandleInput 99 =
      some (.DUP2, none) :=
  rfl

theorem dOp_100 :
    opcodeAt depositHandleInput 100 =
      some (.SSTORE, none) :=
  rfl

theorem dOp_101 :
    opcodeAt depositHandleInput 101 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem dOp_103 :
    opcodeAt depositHandleInput 103 =
      some (.ADD, none) :=
  rfl

theorem dOp_104 :
    opcodeAt depositHandleInput 104 =
      some (.PUSH1, some (UInt256.ofNat 160, 1)) :=
  rfl

theorem dOp_106 :
    opcodeAt depositHandleInput 106 =
      some (.CALLDATALOAD, none) :=
  rfl

theorem dOp_107 :
    opcodeAt depositHandleInput 107 =
      some (.SWAP1, none) :=
  rfl

theorem dOp_108 :
    opcodeAt depositHandleInput 108 =
      some (.SSTORE, none) :=
  rfl

theorem dOp_109 :
    opcodeAt depositHandleInput 109 =
      some (.PUSH1, some (UInt256.ofNat 184, 1)) :=
  rfl

theorem dOp_111 :
    opcodeAt depositHandleInput 111 =
      some (.PUSH0, none) :=
  rfl

theorem dOp_112 :
    opcodeAt depositHandleInput 112 =
      some (.PUSH0, none) :=
  rfl

theorem dOp_113 :
    opcodeAt depositHandleInput 113 =
      some (.CALLDATACOPY, none) :=
  rfl

theorem dOp_114 :
    opcodeAt depositHandleInput 114 =
      some (.PUSH1, some (UInt256.ofNat 184, 1)) :=
  rfl

theorem dOp_116 :
    opcodeAt depositHandleInput 116 =
      some (.PUSH0, none) :=
  rfl

theorem dOp_117 :
    opcodeAt depositHandleInput 117 =
      some (.LOG0, none) :=
  rfl

theorem dOp_118 :
    opcodeAt depositHandleInput 118 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem dOp_120 :
    opcodeAt depositHandleInput 120 =
      some (.ADD, none) :=
  rfl

theorem dOp_121 :
    opcodeAt depositHandleInput 121 =
      some (.PUSH1, some (UInt256.ofNat 3, 1)) :=
  rfl

theorem dOp_123 :
    opcodeAt depositHandleInput 123 =
      some (.SSTORE, none) :=
  rfl

theorem dOp_124 :
    opcodeAt depositHandleInput 124 =
      some (.STOP, none) :=
  rfl

theorem eOp_0 :
    opcodeAt exitHandleInput 0 =
      some (.JUMPDEST, none) :=
  rfl

theorem eOp_1 :
    opcodeAt exitHandleInput 1 =
      some (.CALLVALUE, none) :=
  rfl

theorem eOp_2 :
    opcodeAt exitHandleInput 2 =
      some (.LT, none) :=
  rfl

theorem eOp_3 :
    opcodeAt exitHandleInput 3 =
      some (.PUSH2, some (UInt256.ofNat 454, 2)) :=
  rfl

theorem eOp_6 :
    opcodeAt exitHandleInput 6 =
      some (.JUMPI, none) :=
  rfl

theorem eOp_7 :
    opcodeAt exitHandleInput 7 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem eOp_9 :
    opcodeAt exitHandleInput 9 =
      some (.SLOAD, none) :=
  rfl

theorem eOp_10 :
    opcodeAt exitHandleInput 10 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem eOp_12 :
    opcodeAt exitHandleInput 12 =
      some (.ADD, none) :=
  rfl

theorem eOp_13 :
    opcodeAt exitHandleInput 13 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem eOp_15 :
    opcodeAt exitHandleInput 15 =
      some (.SSTORE, none) :=
  rfl

theorem eOp_16 :
    opcodeAt exitHandleInput 16 =
      some (.PUSH1, some (UInt256.ofNat 3, 1)) :=
  rfl

theorem eOp_18 :
    opcodeAt exitHandleInput 18 =
      some (.SLOAD, none) :=
  rfl

theorem eOp_19 :
    opcodeAt exitHandleInput 19 =
      some (.DUP1, none) :=
  rfl

theorem eOp_20 :
    opcodeAt exitHandleInput 20 =
      some (.PUSH1, some (UInt256.ofNat 3, 1)) :=
  rfl

theorem eOp_22 :
    opcodeAt exitHandleInput 22 =
      some (.MUL, none) :=
  rfl

theorem eOp_23 :
    opcodeAt exitHandleInput 23 =
      some (.PUSH1, some (UInt256.ofNat 4, 1)) :=
  rfl

theorem eOp_25 :
    opcodeAt exitHandleInput 25 =
      some (.ADD, none) :=
  rfl

theorem eOp_26 :
    opcodeAt exitHandleInput 26 =
      some (.CALLER, none) :=
  rfl

theorem eOp_27 :
    opcodeAt exitHandleInput 27 =
      some (.DUP2, none) :=
  rfl

theorem eOp_28 :
    opcodeAt exitHandleInput 28 =
      some (.SSTORE, none) :=
  rfl

theorem eOp_29 :
    opcodeAt exitHandleInput 29 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem eOp_31 :
    opcodeAt exitHandleInput 31 =
      some (.ADD, none) :=
  rfl

theorem eOp_32 :
    opcodeAt exitHandleInput 32 =
      some (.PUSH0, none) :=
  rfl

theorem eOp_33 :
    opcodeAt exitHandleInput 33 =
      some (.CALLDATALOAD, none) :=
  rfl

theorem eOp_34 :
    opcodeAt exitHandleInput 34 =
      some (.DUP2, none) :=
  rfl

theorem eOp_35 :
    opcodeAt exitHandleInput 35 =
      some (.SSTORE, none) :=
  rfl

theorem eOp_36 :
    opcodeAt exitHandleInput 36 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem eOp_38 :
    opcodeAt exitHandleInput 38 =
      some (.ADD, none) :=
  rfl

theorem eOp_39 :
    opcodeAt exitHandleInput 39 =
      some (.PUSH1, some (UInt256.ofNat 32, 1)) :=
  rfl

theorem eOp_41 :
    opcodeAt exitHandleInput 41 =
      some (.CALLDATALOAD, none) :=
  rfl

theorem eOp_42 :
    opcodeAt exitHandleInput 42 =
      some (.SWAP1, none) :=
  rfl

theorem eOp_43 :
    opcodeAt exitHandleInput 43 =
      some (.SSTORE, none) :=
  rfl

theorem eOp_44 :
    opcodeAt exitHandleInput 44 =
      some (.CALLER, none) :=
  rfl

theorem eOp_45 :
    opcodeAt exitHandleInput 45 =
      some (.PUSH1, some (UInt256.ofNat 96, 1)) :=
  rfl

theorem eOp_47 :
    opcodeAt exitHandleInput 47 =
      some (.SHL, none) :=
  rfl

theorem eOp_48 :
    opcodeAt exitHandleInput 48 =
      some (.PUSH0, none) :=
  rfl

theorem eOp_49 :
    opcodeAt exitHandleInput 49 =
      some (.MSTORE, none) :=
  rfl

theorem eOp_50 :
    opcodeAt exitHandleInput 50 =
      some (.PUSH1, some (UInt256.ofNat 48, 1)) :=
  rfl

theorem eOp_52 :
    opcodeAt exitHandleInput 52 =
      some (.PUSH0, none) :=
  rfl

theorem eOp_53 :
    opcodeAt exitHandleInput 53 =
      some (.PUSH1, some (UInt256.ofNat 20, 1)) :=
  rfl

theorem eOp_55 :
    opcodeAt exitHandleInput 55 =
      some (.CALLDATACOPY, none) :=
  rfl

theorem eOp_56 :
    opcodeAt exitHandleInput 56 =
      some (.PUSH1, some (UInt256.ofNat 68, 1)) :=
  rfl

theorem eOp_58 :
    opcodeAt exitHandleInput 58 =
      some (.PUSH0, none) :=
  rfl

theorem eOp_59 :
    opcodeAt exitHandleInput 59 =
      some (.LOG0, none) :=
  rfl

theorem eOp_60 :
    opcodeAt exitHandleInput 60 =
      some (.PUSH1, some (UInt256.ofNat 1, 1)) :=
  rfl

theorem eOp_62 :
    opcodeAt exitHandleInput 62 =
      some (.ADD, none) :=
  rfl

theorem eOp_63 :
    opcodeAt exitHandleInput 63 =
      some (.PUSH1, some (UInt256.ofNat 3, 1)) :=
  rfl

theorem eOp_65 :
    opcodeAt exitHandleInput 65 =
      some (.SSTORE, none) :=
  rfl

theorem eOp_66 :
    opcodeAt exitHandleInput 66 =
      some (.STOP, none) :=
  rfl


open Eip8282.Audit.Model (inhibitor)

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

/-! ## Call environment, memory, CFG state -/

structure CallEnv where
  caller : UInt256
  value : UInt256
  calldata : ByteArray

def Memory := Nat → UInt8

def memEmpty : Memory := fun _ => 0

def memWriteBytes (m : Memory) (dest : Nat) (bs : List UInt8) : Memory :=
  fun j =>
    if j < dest then
      m j
    else
      bs.getD (j - dest) (m j)

def calldataByte (cd : ByteArray) (i : Nat) : UInt8 :=
  if i < cd.size then cd.get! i else 0

def calldatacopyMem (m : Memory) (cd : ByteArray) (dest ost size : Nat) : Memory :=
  memWriteBytes m dest ((List.range size).map (fun i => calldataByte cd (ost + i)))

def wordByteBE (w : UInt256) (i : Nat) : UInt8 :=
  UInt8.ofNat ((w.toNat / 256 ^ (31 - i)) % 256)

def wordBytesBE (w : UInt256) : List UInt8 :=
  (List.range 32).map (fun i => wordByteBE w i)

def mstoreMem (m : Memory) (off : Nat) (w : UInt256) : Memory :=
  memWriteBytes m off (wordBytesBE w)

def memSlice (m : Memory) (off size : Nat) : List UInt8 :=
  (List.range size).map (fun i => m (off + i))

def addressByteBE (caller : UInt256) (i : Nat) : UInt8 :=
  UInt8.ofNat ((caller.toNat / 256 ^ (19 - i)) % 256)

def addressBytes20 (caller : UInt256) : List UInt8 :=
  (List.range 20).map (fun i => addressByteBE caller i)

def calldataBytes (cd : ByteArray) : List UInt8 :=
  (List.range cd.size).map (fun i => cd.get! i)

inductive AppendError where
  | stackUnderflow
  | unexpectedOpcode
  | reverted
  deriving DecidableEq, Repr

def loadAfter (σ : Storage) (ws : List (UInt256 × UInt256)) (k : UInt256) :
    UInt256 :=
  match ws.findRev? (fun p => decide (p.1 = k)) with
  | some (_, v) => v
  | none => σ.getD k (UInt256.ofNat 0)

structure AppendState where
  pc : Nat
  stack : List UInt256
  storage : Storage
  memory : Memory
  logs : List (List UInt8)
  halted : Bool
  writes : List (UInt256 × UInt256)

def raw (pc : Nat) (stack : List UInt256) (σ : Storage)
    (writes : List (UInt256 × UInt256)) (mem : Memory) (logs : List (List UInt8)) :
    AppendState :=
  { pc := pc, stack := stack, storage := σ, memory := mem, logs := logs,
    halted := false, writes := writes }

def done (pc : Nat) (stack : List UInt256) (σ : Storage)
    (writes : List (UInt256 × UInt256)) (mem : Memory) (logs : List (List UInt8)) :
    AppendState :=
  { pc := pc, stack := stack, storage := σ, memory := mem, logs := logs,
    halted := true, writes := writes }

def loadSlot (σ : Storage) (k : UInt256) : UInt256 :=
  σ.getD k (UInt256.ofNat 0)

def loadState (m : AppendState) (k : UInt256) : UInt256 :=
  loadAfter m.storage m.writes k

def appendBase (slotsPerItem tail : UInt256) : UInt256 :=
  UInt256.ofNat QUEUE_OFFSET + slotsPerItem * tail

/-! ## CFG stepper for `handle_input` -/

def cfgStep (code : ByteArray) (env : CallEnv) (m : AppendState) :
    Except AppendError AppendState :=
  match m.halted with
  | true => .ok m
  | false =>
    match opcodeAt code m.pc with
    | some (.JUMPDEST, none) =>
        .ok { m with pc := m.pc + 1 }
    | some (.STOP, none) =>
        .ok { m with pc := m.pc + 1, halted := true }
    | some (.PUSH0, none) =>
        .ok { m with pc := m.pc + 1, stack := (UInt256.ofNat 0 :: m.stack) }
    | some (.Push _, some (imm, width)) =>
        .ok { m with pc := m.pc + 1 + width, stack := (imm :: m.stack) }
    | some (.DUP1, none) =>
        match m.stack with
        | a :: rest =>
            .ok { m with pc := m.pc + 1, stack := (a :: a :: rest) }
        | _ => .error .stackUnderflow
    | some (.DUP2, none) =>
        match m.stack with
        | a :: b :: rest =>
            .ok { m with pc := m.pc + 1, stack := (b :: a :: b :: rest) }
        | _ => .error .stackUnderflow
    | some (.SWAP1, none) =>
        match m.stack with
        | a :: b :: rest =>
            .ok { m with pc := m.pc + 1, stack := (b :: a :: rest) }
        | _ => .error .stackUnderflow
    | some (.ADD, none) =>
        match m.stack with
        | a :: b :: rest =>
            .ok { m with pc := m.pc + 1, stack := ((a + b) :: rest) }
        | _ => .error .stackUnderflow
    | some (.MUL, none) =>
        match m.stack with
        | a :: b :: rest =>
            .ok { m with pc := m.pc + 1, stack := ((a * b) :: rest) }
        | _ => .error .stackUnderflow
    | some (.SUB, none) =>
        match m.stack with
        | a :: b :: rest =>
            .ok { m with pc := m.pc + 1, stack := ((a - b) :: rest) }
        | _ => .error .stackUnderflow
    | some (.LT, none) =>
        match m.stack with
        | a :: b :: rest =>
            .ok { m with pc := m.pc + 1, stack := (UInt256.lt a b :: rest) }
        | _ => .error .stackUnderflow
    | some (.GT, none) =>
        match m.stack with
        | a :: b :: rest =>
            .ok { m with pc := m.pc + 1, stack := (UInt256.gt a b :: rest) }
        | _ => .error .stackUnderflow
    | some (.AND, none) =>
        match m.stack with
        | a :: b :: rest =>
            .ok { m with pc := m.pc + 1, stack := (UInt256.land a b :: rest) }
        | _ => .error .stackUnderflow
    | some (.SHL, none) =>
        match m.stack with
        | sh :: v :: rest =>
            .ok { m with pc := m.pc + 1, stack := (UInt256.shiftLeft v sh :: rest) }
        | _ => .error .stackUnderflow
    | some (.CALLVALUE, none) =>
        .ok { m with pc := m.pc + 1, stack := (env.value :: m.stack) }
    | some (.CALLER, none) =>
        .ok { m with pc := m.pc + 1, stack := (env.caller :: m.stack) }
    | some (.CALLDATALOAD, none) =>
        match m.stack with
        | off :: rest =>
            .ok { m with pc := m.pc + 1, stack := (calldataWord env.calldata off.toNat :: rest) }
        | _ => .error .stackUnderflow
    | some (.CALLDATACOPY, none) =>
        match m.stack with
        | dest :: ost :: size :: rest =>
            .ok { m with pc := m.pc + 1, stack := rest, memory := (calldatacopyMem m.memory env.calldata dest.toNat ost.toNat size.toNat) }
        | _ => .error .stackUnderflow
    | some (.SLOAD, none) =>
        match m.stack with
        | key :: rest =>
            .ok { m with pc := m.pc + 1, stack := (loadAfter m.storage m.writes key :: rest) }
        | _ => .error .stackUnderflow
    | some (.SSTORE, none) =>
        match m.stack with
        | key :: val :: rest =>
            .ok { m with pc := m.pc + 1, stack := rest, writes := m.writes ++ [(key, val)] }
        | _ => .error .stackUnderflow
    | some (.MSTORE, none) =>
        match m.stack with
        | off :: val :: rest =>
            .ok { m with pc := m.pc + 1, stack := rest, memory := mstoreMem m.memory off.toNat val }
        | _ => .error .stackUnderflow
    | some (.JUMPI, none) =>
        match m.stack with
        | dest :: cond :: rest =>
            match (cond != UInt256.ofNat 0) with
            | true => .error .reverted
            | false => .ok { m with pc := m.pc + 1, stack := rest }
        | _ => .error .stackUnderflow
    | some (.LOG0, none) =>
        match m.stack with
        | off :: size :: rest =>
            .ok { m with pc := m.pc + 1, stack := rest, logs := m.logs ++ [memSlice m.memory off.toNat size.toNat] }
        | _ => .error .stackUnderflow
    | _ => .error .unexpectedOpcode

def runFuel (code : ByteArray) (env : CallEnv) :
    Nat → AppendState → Except AppendError AppendState
  | 0, m => .ok m
  | n + 1, m =>
    match m.halted with
    | true => .ok m
    | false =>
      match cfgStep code env m with
      | .error e => .error e
      | .ok m' => runFuel code env n m'

theorem runFuel_zero (code : ByteArray) (env : CallEnv) (m : AppendState) :
    runFuel code env 0 m = .ok m :=
  rfl

@[simp] theorem raw_pc (pc : Nat) (stack : List UInt256) (σ : Storage)
    (w : List (UInt256 × UInt256)) (mem : Memory) (logs : List (List UInt8)) :
    (raw pc stack σ w mem logs).pc = pc := rfl
@[simp] theorem raw_stack (pc : Nat) (stack : List UInt256) (σ : Storage)
    (w : List (UInt256 × UInt256)) (mem : Memory) (logs : List (List UInt8)) :
    (raw pc stack σ w mem logs).stack = stack := rfl
@[simp] theorem raw_storage (pc : Nat) (stack : List UInt256) (σ : Storage)
    (w : List (UInt256 × UInt256)) (mem : Memory) (logs : List (List UInt8)) :
    (raw pc stack σ w mem logs).storage = σ := rfl
@[simp] theorem raw_writes (pc : Nat) (stack : List UInt256) (σ : Storage)
    (w : List (UInt256 × UInt256)) (mem : Memory) (logs : List (List UInt8)) :
    (raw pc stack σ w mem logs).writes = w := rfl
@[simp] theorem raw_memory (pc : Nat) (stack : List UInt256) (σ : Storage)
    (w : List (UInt256 × UInt256)) (mem : Memory) (logs : List (List UInt8)) :
    (raw pc stack σ w mem logs).memory = mem := rfl
@[simp] theorem raw_logs (pc : Nat) (stack : List UInt256) (σ : Storage)
    (w : List (UInt256 × UInt256)) (mem : Memory) (logs : List (List UInt8)) :
    (raw pc stack σ w mem logs).logs = logs := rfl
@[simp] theorem raw_halted (pc : Nat) (stack : List UInt256) (σ : Storage)
    (w : List (UInt256 × UInt256)) (mem : Memory) (logs : List (List UInt8)) :
    (raw pc stack σ w mem logs).halted = false := rfl

theorem runFuel_succ (code : ByteArray) (env : CallEnv) (n : Nat)
    (m m' : AppendState) (hh : m.halted = false)
    (hs : cfgStep code env m = .ok m') :
    runFuel code env (n + 1) m = runFuel code env n m' := by
  change (match m.halted with
      | true => Except.ok m
      | false =>
        match cfgStep code env m with
        | Except.error e => Except.error e
        | Except.ok m2 => runFuel code env n m2) =
    runFuel code env n m'
  rw [hh, hs]

theorem runFuel_halted (code : ByteArray) (env : CallEnv) (n : Nat)
    (m : AppendState) (h : m.halted = true) :
    runFuel code env n m = .ok m := by
  induction n with
  | zero => rfl
  | succ n _ =>
      change (match m.halted with
          | true => Except.ok m
          | false =>
            match cfgStep code env m with
            | Except.error e => Except.error e
            | Except.ok m2 => runFuel code env n m2) =
        Except.ok m
      rw [h]

theorem runFuel_trans {code : ByteArray} {env : CallEnv} {n k : Nat}
    {s t u : AppendState}
    (h1 : runFuel code env n s = .ok t)
    (h2 : runFuel code env k t = .ok u) :
    runFuel code env (n + k) s = .ok u := by
  induction n generalizing s with
  | zero =>
      rw [runFuel_zero] at h1
      injection h1 with heq
      subst heq
      simpa using h2
  | succ n ih =>
      cases hhalt : s.halted
      · have hsum : n + 1 + k = (n + k) + 1 := by omega
        rw [hsum]
        have h1' :
            (match cfgStep code env s with
              | Except.error e => Except.error e
              | Except.ok m2 => runFuel code env n m2) = Except.ok t := by
          change (match s.halted with
              | true => Except.ok s
              | false =>
                match cfgStep code env s with
                | Except.error e => Except.error e
                | Except.ok m2 => runFuel code env n m2) = Except.ok t at h1
          rw [hhalt] at h1
          exact h1
        have hgoal :
            runFuel code env ((n + k) + 1) s =
              match cfgStep code env s with
              | Except.error e => Except.error e
              | Except.ok m2 => runFuel code env (n + k) m2 := by
          change (match s.halted with
              | true => Except.ok s
              | false =>
                match cfgStep code env s with
                | Except.error e => Except.error e
                | Except.ok m2 => runFuel code env (n + k) m2) =
            match cfgStep code env s with
            | Except.error e => Except.error e
            | Except.ok m2 => runFuel code env (n + k) m2
          rw [hhalt]
        rw [hgoal]
        split at h1'
        · cases h1'
        · next m2 hm =>
            have h1n : runFuel code env n m2 = Except.ok t := by
              simpa [hm] using h1'
            have ih' := ih h1n
            simpa [hm] using ih'
      · rw [runFuel_halted (h := hhalt)] at h1
        injection h1 with heq
        subst heq
        rw [runFuel_halted (h := hhalt)] at h2
        injection h2 with heq
        subst heq
        exact runFuel_halted _ _ _ _ hhalt

/-! ## Overlay lookup after `SSTORE` -/

theorem findRev?_snoc_eq (ws : List (UInt256 × UInt256)) (k v : UInt256) :
    (ws ++ [(k, v)]).findRev? (fun p => decide (p.1 = k)) = some (k, v) := by
  simp [List.findRev?_eq_find?_reverse]

theorem findRev?_snoc_ne (ws : List (UInt256 × UInt256)) (k v k' : UInt256)
    (h : k ≠ k') :
    (ws ++ [(k, v)]).findRev? (fun p => decide (p.1 = k')) =
      ws.findRev? (fun p => decide (p.1 = k')) := by
  have : decide (k = k') = false := decide_eq_false h
  simp [List.findRev?_eq_find?_reverse, this]

theorem loadAfter_nil (σ : Storage) (k : UInt256) :
    loadAfter σ [] k = σ.getD k (UInt256.ofNat 0) :=
  rfl

theorem loadAfter_snoc_eq (σ : Storage) (ws : List (UInt256 × UInt256))
    (k v : UInt256) :
    loadAfter σ (ws ++ [(k, v)]) k = v := by
  unfold loadAfter
  rw [findRev?_snoc_eq]

theorem loadAfter_snoc_ne (σ : Storage) (ws : List (UInt256 × UInt256))
    (k v k' : UInt256) (h : k ≠ k') :
    loadAfter σ (ws ++ [(k, v)]) k' = loadAfter σ ws k' := by
  unfold loadAfter
  rw [findRev?_snoc_ne _ _ _ _ h]

theorem ofNat_toNat (n : Nat) :
    (UInt256.ofNat n).toNat = n % UInt256.size :=
  rfl

theorem ofNat_toNat_lt {n : Nat} (h : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := by
  rw [ofNat_toNat]
  exact Nat.mod_eq_of_lt h

theorem toNat_small (n : Nat) (h : n < 2 ^ 16 := by decide) :
    (UInt256.ofNat n).toNat = n :=
  ofNat_toNat_lt (Nat.lt_trans h (by decide : 2 ^ 16 < UInt256.size))

theorem ofNat_one_ne_three :
    UInt256.ofNat 1 ≠ UInt256.ofNat 3 := by
  intro h
  have := congrArg UInt256.toNat h
  simp [toNat_small] at this

theorem ofNat_zero_ne_one :
    UInt256.ofNat 0 ≠ UInt256.ofNat 1 := by
  intro h
  have := congrArg UInt256.toNat h
  simp [toNat_small] at this

def depositStart (σ : Storage) (fee : UInt256) : AppendState :=
  raw 0 [fee] σ [] memEmpty []

def exitStart (σ : Storage) (fee : UInt256) : AppendState :=
  raw 0 [fee] σ [] memEmpty []

/-- Assembly `AND` of the PUSH8 mask with `CALLDATALOAD 56`. `abbrev` so
paying hypotheses are definitionally the stack `UInt256.gt`/`UInt256.lt`
terms. -/
abbrev amountAsm (cd : ByteArray) : UInt256 :=
  UInt256.land (UInt256.ofNat 18446744073709551615)
    (calldataWord cd (UInt256.ofNat 56).toNat)

private theorem bne_zero_zero :
    (UInt256.ofNat 0 != UInt256.ofNat 0) = false := by
  decide

theorem bne_of_eq_zero {c : UInt256} (h : c = UInt256.ofNat 0) :
    (c != UInt256.ofNat 0) = false := by
  rw [h]; exact bne_zero_zero

def PaidFee (env : CallEnv) (fee : UInt256) : Prop :=
  UInt256.lt env.value fee = UInt256.ofNat 0

def PaidMinAmount (cd : ByteArray) : Prop :=
  UInt256.gt (UInt256.ofNat 1000000000) (amountAsm cd) = UInt256.ofNat 0

def PaidStake (env : CallEnv) (fee : UInt256) : Prop :=
  UInt256.lt (env.value - fee) (UInt256.ofNat 1000000000 * amountAsm env.calldata) =
    UInt256.ofNat 0

def PaidDeposit (env : CallEnv) (fee : UInt256) : Prop :=
  PaidFee env fee ∧ PaidMinAmount env.calldata ∧ PaidStake env fee

def PaidExit (env : CallEnv) (fee : UInt256) : Prop :=
  PaidFee env fee

def uSLOT_EXCESS : UInt256 := UInt256.ofNat SLOT_EXCESS
def uSLOT_COUNT : UInt256 := UInt256.ofNat SLOT_COUNT
def uQUEUE_HEAD : UInt256 := UInt256.ofNat QUEUE_HEAD
def uQUEUE_TAIL : UInt256 := UInt256.ofNat QUEUE_TAIL

def depositAppendBase (σ : Storage) : UInt256 :=
  appendBase (UInt256.ofNat 6) (loadSlot σ uQUEUE_TAIL)

def exitAppendBase (σ : Storage) : UInt256 :=
  appendBase (UInt256.ofNat 3) (loadSlot σ uQUEUE_TAIL)

theorem getD_eq_get {α} (l : List α) (i : Nat) (d : α) (h : i < l.length) :
    l.getD i d = l.get ⟨i, h⟩ := by
  induction l generalizing i with
  | nil => cases h
  | cons a as ih =>
      cases i with
      | zero => rfl
      | succ i =>
          exact ih i (Nat.lt_of_succ_lt_succ h)

theorem getD_map_range (f : Nat → UInt8) (n i : Nat) (h : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  have hlen : i < ((List.range n).map f).length := by
    simpa [List.length_map, List.length_range]
  rw [getD_eq_get _ _ _ hlen]
  have : ((List.range n).map f).get ⟨i, hlen⟩ = f i := by
    simp [List.get_eq_getElem, List.getElem_map, List.getElem_range]
  exact this

theorem memSlice_calldatacopy (cd : ByteArray) (size : Nat) :
    memSlice (calldatacopyMem memEmpty cd 0 0 size) 0 size =
      (List.range size).map (fun i => calldataByte cd i) := by
  unfold memSlice
  apply List.map_congr_left
  intro i hi
  have hi' : i < size := List.mem_range.mp hi
  unfold calldatacopyMem memWriteBytes memEmpty
  have hnlt : ¬ (0 + i) < 0 := Nat.not_lt.mpr (Nat.zero_le _)
  rw [if_neg hnlt]
  have hlen : i < ((List.range size).map (fun j => calldataByte cd (0 + j))).length := by
    simpa [List.length_map, List.length_range]
  have hidx : 0 + i - 0 = i := by omega
  rw [hidx, getD_eq_get _ _ _ hlen]
  simp [List.get_eq_getElem, List.getElem_map, List.getElem_range]

theorem calldataBytes_of_exact (cd : ByteArray) (n : Nat) (hsz : cd.size = n) :
    (List.range n).map (fun i => calldataByte cd i) =
      (List.range n).map (fun i => cd.get! i) := by
  apply List.map_congr_left
  intro i hi
  have : i < n := List.mem_range.mp hi
  unfold calldataByte
  simp [hsz, this]

theorem toNat_0 : (UInt256.ofNat 0).toNat = 0 := rfl
theorem toNat_20 : (UInt256.ofNat 20).toNat = 20 := rfl
theorem toNat_32 : (UInt256.ofNat 32).toNat = 32 := rfl
theorem toNat_48 : (UInt256.ofNat 48).toNat = 48 := rfl
theorem toNat_56 : (UInt256.ofNat 56).toNat = 56 := rfl
theorem toNat_64 : (UInt256.ofNat 64).toNat = 64 := rfl
theorem toNat_68 : (UInt256.ofNat 68).toNat = 68 := rfl
theorem toNat_96 : (UInt256.ofNat 96).toNat = 96 := rfl
theorem toNat_128 : (UInt256.ofNat 128).toNat = 128 := rfl
theorem toNat_160 : (UInt256.ofNat 160).toNat = 160 := rfl
theorem toNat_184 : (UInt256.ofNat 184).toNat = 184 := rfl

theorem memWriteBytes_lt (m : Memory) (dest : Nat) (bs : List UInt8) (j : Nat)
    (h : j < dest) :
    memWriteBytes m dest bs j = m j := by
  unfold memWriteBytes
  rw [if_pos h]

theorem memWriteBytes_hit (m : Memory) (dest : Nat) (bs : List UInt8) (j : Nat)
    (h1 : dest ≤ j) (h2 : j - dest < bs.length) :
    memWriteBytes m dest bs j = bs.getD (j - dest) (m j) := by
  unfold memWriteBytes
  have : ¬ j < dest := Nat.not_lt.mpr h1
  rw [if_neg this]

theorem memSlice_mstore_20 (w : UInt256) :
    memSlice (mstoreMem memEmpty 0 w) 0 20 =
      (List.range 20).map (fun i => wordByteBE w i) := by
  unfold memSlice
  apply List.map_congr_left
  intro i hi
  have hi20 : i < 20 := List.mem_range.mp hi
  unfold mstoreMem memWriteBytes wordBytesBE memEmpty
  have hlen : i < ((List.range 32).map (fun j => wordByteBE w j)).length := by
    simpa [List.length_map, List.length_range] using
      (Nat.lt_trans hi20 (by decide : 20 < 32))
  have hnlt : ¬ (0 + i) < 0 := Nat.not_lt.mpr (Nat.zero_le _)
  rw [if_neg hnlt]
  have hidx : 0 + i - 0 = i := by omega
  rw [hidx, getD_eq_get _ _ _ hlen]
  simp [List.get_eq_getElem, List.getElem_map, List.getElem_range]

theorem memSlice_copy_from (pre : Memory) (cd : ByteArray) (dest size : Nat) :
    memSlice (calldatacopyMem pre cd dest 0 size) dest size =
      (List.range size).map (fun i => calldataByte cd i) := by
  unfold memSlice
  apply List.map_congr_left
  intro i hi
  have hi' : i < size := List.mem_range.mp hi
  unfold calldatacopyMem memWriteBytes
  have hnlt : ¬ (dest + i) < dest := Nat.not_lt.mpr (Nat.le_add_right _ _)
  rw [if_neg hnlt]
  have hlen : i < ((List.range size).map (fun j => calldataByte cd (0 + j))).length := by
    simpa [List.length_map, List.length_range]
  have hidx : dest + i - dest = i := Nat.add_sub_cancel_left dest i
  rw [hidx, getD_eq_get _ _ _ hlen]
  simp [List.get_eq_getElem, List.getElem_map, List.getElem_range]

theorem memSlice_copy_prefix (pre : Memory) (cd : ByteArray)
    (dest size n : Nat) (hn : n ≤ dest) :
    memSlice (calldatacopyMem pre cd dest 0 size) 0 n = memSlice pre 0 n := by
  unfold memSlice calldatacopyMem
  apply List.map_congr_left
  intro i hi
  have hi' : i < n := List.mem_range.mp hi
  have hlt : 0 + i < dest := Nat.lt_of_lt_of_le (by omega) hn
  exact memWriteBytes_lt pre dest _ (0 + i) hlt

theorem range_add' (n k : Nat) :
    List.range (n + k) = List.range n ++ (List.range k).map (fun i => n + i) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, List.range_succ, List.range_succ, ih]
      simp [List.append_assoc]

theorem memSlice_add (m : Memory) (n k : Nat) :
    memSlice m 0 (n + k) = memSlice m 0 n ++ memSlice m n k := by
  unfold memSlice
  rw [range_add']
  simp [List.map_append, List.map_map]

theorem memSlice_copy_68 (pre : Memory) (cd : ByteArray) :
    memSlice (calldatacopyMem pre cd 20 0 48) 0 68 =
      memSlice pre 0 20 ++ (List.range 48).map (fun i => calldataByte cd i) := by
  have hsplit : 68 = 20 + 48 := rfl
  rw [hsplit, memSlice_add]
  rw [memSlice_copy_prefix pre cd 20 48 20 (Nat.le_refl _)]
  rw [memSlice_copy_from]

/-! Generated CFG ticks follow. -/

/-! ## Deposit CFG ticks -/

theorem d_cfg_0
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 0 [fee] σ [] memEmpty []) =
      .ok (raw 1 [fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_0]
  rfl

theorem d_cfg_1
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 1 [fee] σ [] memEmpty []) =
      .ok (raw 2 [fee, fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_1]
  rfl

theorem d_cfg_2
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 2 [fee, fee] σ [] memEmpty []) =
      .ok (raw 3 [env.value, fee, fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_2]
  rfl

theorem d_cfg_3
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 3 [env.value, fee, fee] σ [] memEmpty []) =
      .ok (raw 4 [(UInt256.lt env.value fee), fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_3]
  rfl

theorem d_cfg_4
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 4 [(UInt256.lt env.value fee), fee] σ [] memEmpty []) =
      .ok (raw 7 [(UInt256.ofNat 624), (UInt256.lt env.value fee), fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_4]
  rfl

theorem d_cfg_7
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 7 [(UInt256.ofNat 624), (UInt256.lt env.value fee), fee] σ [] memEmpty []) =
      .ok (raw 8 [fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_7]
  have hx := hpay.1
  rw [bne_of_eq_zero hx]
  rfl

theorem d_cfg_8
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 8 [fee] σ [] memEmpty []) =
      .ok (raw 10 [(UInt256.ofNat 56), fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_8]
  rfl

theorem d_cfg_10
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 10 [(UInt256.ofNat 56), fee] σ [] memEmpty []) =
      .ok (raw 11 [(calldataWord env.calldata ((UInt256.ofNat 56)).toNat), fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_10]
  rfl

theorem d_cfg_11
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 11 [(calldataWord env.calldata ((UInt256.ofNat 56)).toNat), fee] σ [] memEmpty []) =
      .ok (raw 20 [(UInt256.ofNat 18446744073709551615), (calldataWord env.calldata ((UInt256.ofNat 56)).toNat), fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_11]
  rfl

theorem d_cfg_20
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 20 [(UInt256.ofNat 18446744073709551615), (calldataWord env.calldata ((UInt256.ofNat 56)).toNat), fee] σ [] memEmpty []) =
      .ok (raw 21 [(UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_20]
  rfl

theorem d_cfg_21
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 21 [(UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), fee] σ [] memEmpty []) =
      .ok (raw 22 [(UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_21]
  rfl

theorem d_cfg_22
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 22 [(UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), fee] σ [] memEmpty []) =
      .ok (raw 27 [(UInt256.ofNat 1000000000), (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_22]
  rfl

theorem d_cfg_27
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 27 [(UInt256.ofNat 1000000000), (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), fee] σ [] memEmpty []) =
      .ok (raw 28 [(UInt256.gt (UInt256.ofNat 1000000000) (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat))), (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_27]
  rfl

theorem d_cfg_28
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 28 [(UInt256.gt (UInt256.ofNat 1000000000) (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat))), (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), fee] σ [] memEmpty []) =
      .ok (raw 31 [(UInt256.ofNat 624), (UInt256.gt (UInt256.ofNat 1000000000) (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat))), (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_28]
  rfl

theorem d_cfg_31
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 31 [(UInt256.ofNat 624), (UInt256.gt (UInt256.ofNat 1000000000) (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat))), (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), fee] σ [] memEmpty []) =
      .ok (raw 32 [(UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_31]
  have hx := hpay.2.1
  rw [bne_of_eq_zero hx]
  rfl

theorem d_cfg_32
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 32 [(UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), fee] σ [] memEmpty []) =
      .ok (raw 37 [(UInt256.ofNat 1000000000), (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_32]
  rfl

theorem d_cfg_37
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 37 [(UInt256.ofNat 1000000000), (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), fee] σ [] memEmpty []) =
      .ok (raw 38 [((UInt256.ofNat 1000000000) * (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat))), fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_37]
  rfl

theorem d_cfg_38
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 38 [((UInt256.ofNat 1000000000) * (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat))), fee] σ [] memEmpty []) =
      .ok (raw 39 [fee, ((UInt256.ofNat 1000000000) * (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)))] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_38]
  rfl

theorem d_cfg_39
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 39 [fee, ((UInt256.ofNat 1000000000) * (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)))] σ [] memEmpty []) =
      .ok (raw 40 [env.value, fee, ((UInt256.ofNat 1000000000) * (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)))] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_39]
  rfl

theorem d_cfg_40
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 40 [env.value, fee, ((UInt256.ofNat 1000000000) * (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)))] σ [] memEmpty []) =
      .ok (raw 41 [(env.value - fee), ((UInt256.ofNat 1000000000) * (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)))] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_40]
  rfl

theorem d_cfg_41
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 41 [(env.value - fee), ((UInt256.ofNat 1000000000) * (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)))] σ [] memEmpty []) =
      .ok (raw 42 [(UInt256.lt (env.value - fee) ((UInt256.ofNat 1000000000) * (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat))))] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_41]
  rfl

theorem d_cfg_42
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 42 [(UInt256.lt (env.value - fee) ((UInt256.ofNat 1000000000) * (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat))))] σ [] memEmpty []) =
      .ok (raw 45 [(UInt256.ofNat 624), (UInt256.lt (env.value - fee) ((UInt256.ofNat 1000000000) * (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat))))] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_42]
  rfl

theorem d_cfg_45
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 45 [(UInt256.ofNat 624), (UInt256.lt (env.value - fee) ((UInt256.ofNat 1000000000) * (UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat))))] σ [] memEmpty []) =
      .ok (raw 46 [] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_45]
  have hx := hpay.2.2
  rw [bne_of_eq_zero hx]
  rfl

theorem d_cfg_46
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 46 [] σ [] memEmpty []) =
      .ok (raw 48 [(UInt256.ofNat 1)] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_46]
  rfl

theorem d_cfg_48
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 48 [(UInt256.ofNat 1)] σ [] memEmpty []) =
      .ok (raw 49 [(loadAfter σ [] (UInt256.ofNat 1))] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_48]
  rfl

theorem d_cfg_49
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 49 [(loadAfter σ [] (UInt256.ofNat 1))] σ [] memEmpty []) =
      .ok (raw 51 [(UInt256.ofNat 1), (loadAfter σ [] (UInt256.ofNat 1))] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_49]
  rfl

theorem d_cfg_51
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 51 [(UInt256.ofNat 1), (loadAfter σ [] (UInt256.ofNat 1))] σ [] memEmpty []) =
      .ok (raw 52 [((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_51]
  rfl

theorem d_cfg_52
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 52 [((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))] σ [] memEmpty []) =
      .ok (raw 54 [(UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_52]
  rfl

theorem d_cfg_54
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 54 [(UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))] σ [] memEmpty []) =
      .ok (raw 55 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_54]
  rfl

theorem d_cfg_55
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 55 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 57 [(UInt256.ofNat 3)] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_55]
  rfl

theorem d_cfg_57
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 57 [(UInt256.ofNat 3)] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 58 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_57]
  rfl

theorem d_cfg_58
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 58 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 59 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_58]
  rfl

theorem d_cfg_59
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 59 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 61 [(UInt256.ofNat 6), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_59]
  rfl

theorem d_cfg_61
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 61 [(UInt256.ofNat 6), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 62 [((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_61]
  rfl

theorem d_cfg_62
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 62 [((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 64 [(UInt256.ofNat 4), ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_62]
  rfl

theorem d_cfg_64
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 64 [(UInt256.ofNat 4), ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 65 [((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_64]
  rfl

theorem d_cfg_65
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 65 [((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 66 [(UInt256.ofNat 0), ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_65]
  rfl

theorem d_cfg_66
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 66 [(UInt256.ofNat 0), ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 67 [(calldataWord env.calldata ((UInt256.ofNat 0)).toNat), ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_66]
  rfl

theorem d_cfg_67
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 67 [(calldataWord env.calldata ((UInt256.ofNat 0)).toNat), ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 68 [((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat), ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_67]
  rfl

theorem d_cfg_68
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 68 [((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat), ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 69 [((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_68]
  rfl

theorem d_cfg_69
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 69 [((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) =
      .ok (raw 71 [(UInt256.ofNat 1), ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_69]
  rfl

theorem d_cfg_71
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 71 [(UInt256.ofNat 1), ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) =
      .ok (raw 72 [((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_71]
  rfl

theorem d_cfg_72
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 72 [((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) =
      .ok (raw 74 [(UInt256.ofNat 32), ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_72]
  rfl

theorem d_cfg_74
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 74 [(UInt256.ofNat 32), ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) =
      .ok (raw 75 [(calldataWord env.calldata ((UInt256.ofNat 32)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_74]
  rfl

theorem d_cfg_75
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 75 [(calldataWord env.calldata ((UInt256.ofNat 32)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) =
      .ok (raw 76 [((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_75]
  rfl

theorem d_cfg_76
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 76 [((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) =
      .ok (raw 77 [((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_76]
  rfl

theorem d_cfg_77
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 77 [((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) =
      .ok (raw 79 [(UInt256.ofNat 1), ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_77]
  rfl

theorem d_cfg_79
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 79 [(UInt256.ofNat 1), ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) =
      .ok (raw 80 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_79]
  rfl

theorem d_cfg_80
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 80 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) =
      .ok (raw 82 [(UInt256.ofNat 64), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_80]
  rfl

theorem d_cfg_82
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 82 [(UInt256.ofNat 64), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) =
      .ok (raw 83 [(calldataWord env.calldata ((UInt256.ofNat 64)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_82]
  rfl

theorem d_cfg_83
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 83 [(calldataWord env.calldata ((UInt256.ofNat 64)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) =
      .ok (raw 84 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_83]
  rfl

theorem d_cfg_84
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 84 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) =
      .ok (raw 85 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_84]
  rfl

theorem d_cfg_85
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 85 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat))] memEmpty []) =
      .ok (raw 87 [(UInt256.ofNat 1), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_85]
  rfl

theorem d_cfg_87
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 87 [(UInt256.ofNat 1), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat))] memEmpty []) =
      .ok (raw 88 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_87]
  rfl

theorem d_cfg_88
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 88 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat))] memEmpty []) =
      .ok (raw 90 [(UInt256.ofNat 96), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_88]
  rfl

theorem d_cfg_90
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 90 [(UInt256.ofNat 96), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat))] memEmpty []) =
      .ok (raw 91 [(calldataWord env.calldata ((UInt256.ofNat 96)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_90]
  rfl

theorem d_cfg_91
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 91 [(calldataWord env.calldata ((UInt256.ofNat 96)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat))] memEmpty []) =
      .ok (raw 92 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_91]
  rfl

theorem d_cfg_92
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 92 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat))] memEmpty []) =
      .ok (raw 93 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_92]
  rfl

theorem d_cfg_93
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 93 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat))] memEmpty []) =
      .ok (raw 95 [(UInt256.ofNat 1), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_93]
  rfl

theorem d_cfg_95
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 95 [(UInt256.ofNat 1), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat))] memEmpty []) =
      .ok (raw 96 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_95]
  rfl

theorem d_cfg_96
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 96 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat))] memEmpty []) =
      .ok (raw 98 [(UInt256.ofNat 128), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_96]
  rfl

theorem d_cfg_98
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 98 [(UInt256.ofNat 128), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat))] memEmpty []) =
      .ok (raw 99 [(calldataWord env.calldata ((UInt256.ofNat 128)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_98]
  rfl

theorem d_cfg_99
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 99 [(calldataWord env.calldata ((UInt256.ofNat 128)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat))] memEmpty []) =
      .ok (raw 100 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_99]
  rfl

theorem d_cfg_100
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 100 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat))] memEmpty []) =
      .ok (raw 101 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_100]
  rfl

theorem d_cfg_101
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 101 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat))] memEmpty []) =
      .ok (raw 103 [(UInt256.ofNat 1), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_101]
  rfl

theorem d_cfg_103
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 103 [(UInt256.ofNat 1), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat))] memEmpty []) =
      .ok (raw 104 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_103]
  rfl

theorem d_cfg_104
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 104 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat))] memEmpty []) =
      .ok (raw 106 [(UInt256.ofNat 160), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_104]
  rfl

theorem d_cfg_106
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 106 [(UInt256.ofNat 160), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat))] memEmpty []) =
      .ok (raw 107 [(calldataWord env.calldata ((UInt256.ofNat 160)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_106]
  rfl

theorem d_cfg_107
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 107 [(calldataWord env.calldata ((UInt256.ofNat 160)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat))] memEmpty []) =
      .ok (raw 108 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_107]
  rfl

theorem d_cfg_108
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 108 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat))] memEmpty []) =
      .ok (raw 109 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_108]
  rfl

theorem d_cfg_109
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 109 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] memEmpty []) =
      .ok (raw 111 [(UInt256.ofNat 184), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_109]
  rfl

theorem d_cfg_111
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 111 [(UInt256.ofNat 184), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] memEmpty []) =
      .ok (raw 112 [(UInt256.ofNat 0), (UInt256.ofNat 184), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_111]
  rfl

theorem d_cfg_112
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 112 [(UInt256.ofNat 0), (UInt256.ofNat 184), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] memEmpty []) =
      .ok (raw 113 [(UInt256.ofNat 0), (UInt256.ofNat 0), (UInt256.ofNat 184), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_112]
  rfl

theorem d_cfg_113
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 113 [(UInt256.ofNat 0), (UInt256.ofNat 0), (UInt256.ofNat 184), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] memEmpty []) =
      .ok (raw 114 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_113]
  rfl

theorem d_cfg_114
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 114 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) []) =
      .ok (raw 116 [(UInt256.ofNat 184), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_114]
  rfl

theorem d_cfg_116
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 116 [(UInt256.ofNat 184), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) []) =
      .ok (raw 117 [(UInt256.ofNat 0), (UInt256.ofNat 184), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_116]
  rfl

theorem d_cfg_117
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 117 [(UInt256.ofNat 0), (UInt256.ofNat 184), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) []) =
      .ok (raw 118 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) [(memSlice (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat)]) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_117]
  rfl

theorem d_cfg_118
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 118 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) [(memSlice (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat)]) =
      .ok (raw 120 [(UInt256.ofNat 1), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) [(memSlice (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat)]) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_118]
  rfl

theorem d_cfg_120
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 120 [(UInt256.ofNat 1), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) [(memSlice (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat)]) =
      .ok (raw 121 [((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) [(memSlice (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat)]) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_120]
  rfl

theorem d_cfg_121
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 121 [((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) [(memSlice (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat)]) =
      .ok (raw 123 [(UInt256.ofNat 3), ((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) [(memSlice (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat)]) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_121]
  rfl

theorem d_cfg_123
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 123 [(UInt256.ofNat 3), ((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) [(memSlice (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat)]) =
      .ok (raw 124 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat)), ((UInt256.ofNat 3), ((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) [(memSlice (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat)]) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_123]
  rfl

theorem d_cfg_124
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    cfgStep depositHandleInput env (raw 124 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat)), ((UInt256.ofNat 3), ((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) [(memSlice (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat)]) =
      .ok (done 125 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat)), ((UInt256.ofNat 3), ((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) [(memSlice (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat)]) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [dOp_124]
  rfl

/-! ### Deposit checkpoints -/

theorem d_run_fee
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    runFuel depositHandleInput env 6 (raw 0 [fee] σ [] memEmpty []) =
      .ok (raw 8 [fee] σ [] memEmpty []) := by
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_0 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_1 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_2 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_3 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_4 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_7 env σ fee hpay)]
  rfl

theorem d_run_minAmt
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    runFuel depositHandleInput env 9 (raw 8 [fee] σ [] memEmpty []) =
      .ok (raw 32 [(UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), fee] σ [] memEmpty []) := by
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_8 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_10 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_11 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_20 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_21 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_22 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_27 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_28 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_31 env σ fee hpay)]
  rfl

theorem d_run_stake
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    runFuel depositHandleInput env 8 (raw 32 [(UInt256.land (UInt256.ofNat 18446744073709551615) (calldataWord env.calldata ((UInt256.ofNat 56)).toNat)), fee] σ [] memEmpty []) =
      .ok (raw 46 [] σ [] memEmpty []) := by
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_32 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_37 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_38 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_39 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_40 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_41 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_42 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_45 env σ fee hpay)]
  rfl

theorem d_run_count
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    runFuel depositHandleInput env 6 (raw 46 [] σ [] memEmpty []) =
      .ok (raw 55 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_46 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_48 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_49 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_51 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_52 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_54 env σ fee hpay)]
  rfl

theorem d_run_base
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    runFuel depositHandleInput env 7 (raw 55 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 65 [((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_55 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_57 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_58 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_59 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_61 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_62 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_64 env σ fee hpay)]
  rfl

theorem d_run_word0
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    runFuel depositHandleInput env 6 (raw 65 [((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 72 [((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) := by
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_65 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_66 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_67 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_68 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_69 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_71 env σ fee hpay)]
  rfl

theorem d_run_word1
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    runFuel depositHandleInput env 6 (raw 72 [((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) =
      .ok (raw 80 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) := by
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_72 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_74 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_75 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_76 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_77 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_79 env σ fee hpay)]
  rfl

theorem d_run_word2
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    runFuel depositHandleInput env 6 (raw 80 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) =
      .ok (raw 88 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat))] memEmpty []) := by
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_80 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_82 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_83 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_84 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_85 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_87 env σ fee hpay)]
  rfl

theorem d_run_word3
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    runFuel depositHandleInput env 6 (raw 88 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat))] memEmpty []) =
      .ok (raw 96 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat))] memEmpty []) := by
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_88 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_90 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_91 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_92 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_93 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_95 env σ fee hpay)]
  rfl

theorem d_run_word4
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    runFuel depositHandleInput env 6 (raw 96 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat))] memEmpty []) =
      .ok (raw 104 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat))] memEmpty []) := by
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_96 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_98 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_99 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_100 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_101 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_103 env σ fee hpay)]
  rfl

theorem d_run_word5
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    runFuel depositHandleInput env 4 (raw 104 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat))] memEmpty []) =
      .ok (raw 109 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] memEmpty []) := by
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_104 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_106 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_107 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_108 env σ fee hpay)]
  rfl

theorem d_run_log
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    runFuel depositHandleInput env 7 (raw 109 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] memEmpty []) =
      .ok (raw 118 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) [(memSlice (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat)]) := by
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_109 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_111 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_112 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_113 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_114 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_116 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_117 env σ fee hpay)]
  rfl

theorem d_run_tail
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    runFuel depositHandleInput env 5 (raw 118 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) [(memSlice (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat)]) =
      .ok (done 125 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat)), ((UInt256.ofNat 3), ((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) [(memSlice (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat)]) := by
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_118 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_120 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_121 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_123 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := d_cfg_124 env σ fee hpay)]
  rfl

theorem deposit_handle_input_run
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidDeposit env fee) :

    runFuel depositHandleInput env 82 (raw 0 [fee] σ [] memEmpty []) =
      .ok (done 125 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 64)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))), (calldataWord env.calldata ((UInt256.ofNat 96)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))), (calldataWord env.calldata ((UInt256.ofNat 128)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))), (calldataWord env.calldata ((UInt256.ofNat 160)).toNat)), ((UInt256.ofNat 3), ((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))] (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) [(memSlice (calldatacopyMem memEmpty env.calldata ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 184)).toNat)]) := by
  have h0 := d_run_fee env σ fee hpay
  have h1 := d_run_minAmt env σ fee hpay
  have h2 := d_run_stake env σ fee hpay
  have h3 := d_run_count env σ fee hpay
  have h4 := d_run_base env σ fee hpay
  have h5 := d_run_word0 env σ fee hpay
  have h6 := d_run_word1 env σ fee hpay
  have h7 := d_run_word2 env σ fee hpay
  have h8 := d_run_word3 env σ fee hpay
  have h9 := d_run_word4 env σ fee hpay
  have h10 := d_run_word5 env σ fee hpay
  have h11 := d_run_log env σ fee hpay
  have h12 := d_run_tail env σ fee hpay
  have t0 := h0
  have t1 := runFuel_trans t0 h1
  have t2 := runFuel_trans t1 h2
  have t3 := runFuel_trans t2 h3
  have t4 := runFuel_trans t3 h4
  have t5 := runFuel_trans t4 h5
  have t6 := runFuel_trans t5 h6
  have t7 := runFuel_trans t6 h7
  have t8 := runFuel_trans t7 h8
  have t9 := runFuel_trans t8 h9
  have t10 := runFuel_trans t9 h10
  have t11 := runFuel_trans t10 h11
  have t12 := runFuel_trans t11 h12
  simpa using t12

/-! ## Exit CFG ticks -/

theorem e_cfg_0
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 0 [fee] σ [] memEmpty []) =
      .ok (raw 1 [fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_0]
  rfl

theorem e_cfg_1
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 1 [fee] σ [] memEmpty []) =
      .ok (raw 2 [env.value, fee] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_1]
  rfl

theorem e_cfg_2
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 2 [env.value, fee] σ [] memEmpty []) =
      .ok (raw 3 [(UInt256.lt env.value fee)] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_2]
  rfl

theorem e_cfg_3
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 3 [(UInt256.lt env.value fee)] σ [] memEmpty []) =
      .ok (raw 6 [(UInt256.ofNat 454), (UInt256.lt env.value fee)] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_3]
  rfl

theorem e_cfg_6
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 6 [(UInt256.ofNat 454), (UInt256.lt env.value fee)] σ [] memEmpty []) =
      .ok (raw 7 [] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_6]
  have hx := hpay
  rw [bne_of_eq_zero hx]
  rfl

theorem e_cfg_7
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 7 [] σ [] memEmpty []) =
      .ok (raw 9 [(UInt256.ofNat 1)] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_7]
  rfl

theorem e_cfg_9
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 9 [(UInt256.ofNat 1)] σ [] memEmpty []) =
      .ok (raw 10 [(loadAfter σ [] (UInt256.ofNat 1))] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_9]
  rfl

theorem e_cfg_10
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 10 [(loadAfter σ [] (UInt256.ofNat 1))] σ [] memEmpty []) =
      .ok (raw 12 [(UInt256.ofNat 1), (loadAfter σ [] (UInt256.ofNat 1))] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_10]
  rfl

theorem e_cfg_12
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 12 [(UInt256.ofNat 1), (loadAfter σ [] (UInt256.ofNat 1))] σ [] memEmpty []) =
      .ok (raw 13 [((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_12]
  rfl

theorem e_cfg_13
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 13 [((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))] σ [] memEmpty []) =
      .ok (raw 15 [(UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))] σ [] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_13]
  rfl

theorem e_cfg_15
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 15 [(UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))] σ [] memEmpty []) =
      .ok (raw 16 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_15]
  rfl

theorem e_cfg_16
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 16 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 18 [(UInt256.ofNat 3)] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_16]
  rfl

theorem e_cfg_18
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 18 [(UInt256.ofNat 3)] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 19 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_18]
  rfl

theorem e_cfg_19
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 19 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 20 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_19]
  rfl

theorem e_cfg_20
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 20 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 22 [(UInt256.ofNat 3), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_20]
  rfl

theorem e_cfg_22
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 22 [(UInt256.ofNat 3), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 23 [((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_22]
  rfl

theorem e_cfg_23
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 23 [((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 25 [(UInt256.ofNat 4), ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_23]
  rfl

theorem e_cfg_25
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 25 [(UInt256.ofNat 4), ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 26 [((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_25]
  rfl

theorem e_cfg_26
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 26 [((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 27 [env.caller, ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_26]
  rfl

theorem e_cfg_27
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 27 [env.caller, ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 28 [((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller, ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_27]
  rfl

theorem e_cfg_28
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 28 [((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller, ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 29 [((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller)] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_28]
  rfl

theorem e_cfg_29
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 29 [((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller)] memEmpty []) =
      .ok (raw 31 [(UInt256.ofNat 1), ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller)] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_29]
  rfl

theorem e_cfg_31
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 31 [(UInt256.ofNat 1), ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller)] memEmpty []) =
      .ok (raw 32 [((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller)] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_31]
  rfl

theorem e_cfg_32
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 32 [((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller)] memEmpty []) =
      .ok (raw 33 [(UInt256.ofNat 0), ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller)] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_32]
  rfl

theorem e_cfg_33
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 33 [(UInt256.ofNat 0), ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller)] memEmpty []) =
      .ok (raw 34 [(calldataWord env.calldata ((UInt256.ofNat 0)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller)] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_33]
  rfl

theorem e_cfg_34
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 34 [(calldataWord env.calldata ((UInt256.ofNat 0)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller)] memEmpty []) =
      .ok (raw 35 [((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller)] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_34]
  rfl

theorem e_cfg_35
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 35 [((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller)] memEmpty []) =
      .ok (raw 36 [((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_35]
  rfl

theorem e_cfg_36
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 36 [((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) =
      .ok (raw 38 [(UInt256.ofNat 1), ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_36]
  rfl

theorem e_cfg_38
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 38 [(UInt256.ofNat 1), ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) =
      .ok (raw 39 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_38]
  rfl

theorem e_cfg_39
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 39 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) =
      .ok (raw 41 [(UInt256.ofNat 32), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_39]
  rfl

theorem e_cfg_41
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 41 [(UInt256.ofNat 32), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) =
      .ok (raw 42 [(calldataWord env.calldata ((UInt256.ofNat 32)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_41]
  rfl

theorem e_cfg_42
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 42 [(calldataWord env.calldata ((UInt256.ofNat 32)).toNat), ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) =
      .ok (raw 43 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_42]
  rfl

theorem e_cfg_43
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 43 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) =
      .ok (raw 44 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_43]
  rfl

theorem e_cfg_44
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 44 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) =
      .ok (raw 45 [env.caller, (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_44]
  rfl

theorem e_cfg_45
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 45 [env.caller, (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) =
      .ok (raw 47 [(UInt256.ofNat 96), env.caller, (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_45]
  rfl

theorem e_cfg_47
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 47 [(UInt256.ofNat 96), env.caller, (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) =
      .ok (raw 48 [(UInt256.shiftLeft env.caller (UInt256.ofNat 96)), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_47]
  rfl

theorem e_cfg_48
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 48 [(UInt256.shiftLeft env.caller (UInt256.ofNat 96)), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) =
      .ok (raw 49 [(UInt256.ofNat 0), (UInt256.shiftLeft env.caller (UInt256.ofNat 96)), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_48]
  rfl

theorem e_cfg_49
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 49 [(UInt256.ofNat 0), (UInt256.shiftLeft env.caller (UInt256.ofNat 96)), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) =
      .ok (raw 50 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_49]
  rfl

theorem e_cfg_50
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 50 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) []) =
      .ok (raw 52 [(UInt256.ofNat 48), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_50]
  rfl

theorem e_cfg_52
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 52 [(UInt256.ofNat 48), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) []) =
      .ok (raw 53 [(UInt256.ofNat 0), (UInt256.ofNat 48), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_52]
  rfl

theorem e_cfg_53
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 53 [(UInt256.ofNat 0), (UInt256.ofNat 48), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) []) =
      .ok (raw 55 [(UInt256.ofNat 20), (UInt256.ofNat 0), (UInt256.ofNat 48), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_53]
  rfl

theorem e_cfg_55
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 55 [(UInt256.ofNat 20), (UInt256.ofNat 0), (UInt256.ofNat 48), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) []) =
      .ok (raw 56 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_55]
  rfl

theorem e_cfg_56
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 56 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) []) =
      .ok (raw 58 [(UInt256.ofNat 68), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_56]
  rfl

theorem e_cfg_58
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 58 [(UInt256.ofNat 68), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) []) =
      .ok (raw 59 [(UInt256.ofNat 0), (UInt256.ofNat 68), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) []) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_58]
  rfl

theorem e_cfg_59
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 59 [(UInt256.ofNat 0), (UInt256.ofNat 68), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) []) =
      .ok (raw 60 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) [(memSlice (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 68)).toNat)]) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_59]
  rfl

theorem e_cfg_60
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 60 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) [(memSlice (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 68)).toNat)]) =
      .ok (raw 62 [(UInt256.ofNat 1), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) [(memSlice (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 68)).toNat)]) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_60]
  rfl

theorem e_cfg_62
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 62 [(UInt256.ofNat 1), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) [(memSlice (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 68)).toNat)]) =
      .ok (raw 63 [((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) [(memSlice (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 68)).toNat)]) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_62]
  rfl

theorem e_cfg_63
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 63 [((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) [(memSlice (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 68)).toNat)]) =
      .ok (raw 65 [(UInt256.ofNat 3), ((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) [(memSlice (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 68)).toNat)]) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_63]
  rfl

theorem e_cfg_65
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 65 [(UInt256.ofNat 3), ((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) [(memSlice (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 68)).toNat)]) =
      .ok (raw 66 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), ((UInt256.ofNat 3), ((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) [(memSlice (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 68)).toNat)]) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_65]
  rfl

theorem e_cfg_66
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    cfgStep exitHandleInput env (raw 66 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), ((UInt256.ofNat 3), ((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) [(memSlice (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 68)).toNat)]) =
      .ok (done 67 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), ((UInt256.ofNat 3), ((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) [(memSlice (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 68)).toNat)]) := by
  unfold cfgStep
  rw [raw_halted, raw_pc, raw_stack, raw_storage, raw_writes, raw_memory, raw_logs]
  simp only [eOp_66]
  rfl

/-! ### Exit checkpoints -/

theorem e_run_fee
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    runFuel exitHandleInput env 5 (raw 0 [fee] σ [] memEmpty []) =
      .ok (raw 7 [] σ [] memEmpty []) := by
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_0 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_1 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_2 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_3 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_6 env σ fee hpay)]
  rfl

theorem e_run_count
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    runFuel exitHandleInput env 6 (raw 7 [] σ [] memEmpty []) =
      .ok (raw 16 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_7 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_9 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_10 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_12 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_13 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_15 env σ fee hpay)]
  rfl

theorem e_run_base
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    runFuel exitHandleInput env 7 (raw 16 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 26 [((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) := by
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_16 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_18 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_19 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_20 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_22 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_23 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_25 env σ fee hpay)]
  rfl

theorem e_run_word0
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    runFuel exitHandleInput env 5 (raw 26 [((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] memEmpty []) =
      .ok (raw 32 [((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller)] memEmpty []) := by
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_26 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_27 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_28 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_29 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_31 env σ fee hpay)]
  rfl

theorem e_run_word1
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    runFuel exitHandleInput env 6 (raw 32 [((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller)] memEmpty []) =
      .ok (raw 39 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) := by
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_32 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_33 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_34 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_35 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_36 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_38 env σ fee hpay)]
  rfl

theorem e_run_word2
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    runFuel exitHandleInput env 4 (raw 39 [((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat))] memEmpty []) =
      .ok (raw 44 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) := by
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_39 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_41 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_42 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_43 env σ fee hpay)]
  rfl

theorem e_run_log
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    runFuel exitHandleInput env 12 (raw 44 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] memEmpty []) =
      .ok (raw 60 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) [(memSlice (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 68)).toNat)]) := by
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_44 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_45 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_47 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_48 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_49 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_50 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_52 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_53 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_55 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_56 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_58 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_59 env σ fee hpay)]
  rfl

theorem e_run_tail
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    runFuel exitHandleInput env 5 (raw 60 [(loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) [(memSlice (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 68)).toNat)]) =
      .ok (done 67 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), ((UInt256.ofNat 3), ((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) [(memSlice (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 68)).toNat)]) := by
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_60 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_62 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_63 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_65 env σ fee hpay)]
  rw [runFuel_succ (hh := rfl) (hs := e_cfg_66 env σ fee hpay)]
  rfl

theorem exit_handle_input_run
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (hpay : PaidExit env fee) :

    runFuel exitHandleInput env 50 (raw 0 [fee] σ [] memEmpty []) =
      .ok (done 67 [] σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))), (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))), env.caller), (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))), (calldataWord env.calldata ((UInt256.ofNat 0)).toNat)), (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))), (calldataWord env.calldata ((UInt256.ofNat 32)).toNat)), ((UInt256.ofNat 3), ((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))] (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) [(memSlice (calldatacopyMem (mstoreMem memEmpty ((UInt256.ofNat 0)).toNat (UInt256.shiftLeft env.caller (UInt256.ofNat 96))) env.calldata ((UInt256.ofNat 20)).toNat ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 48)).toNat) ((UInt256.ofNat 0)).toNat ((UInt256.ofNat 68)).toNat)]) := by
  have h0 := e_run_fee env σ fee hpay
  have h1 := e_run_count env σ fee hpay
  have h2 := e_run_base env σ fee hpay
  have h3 := e_run_word0 env σ fee hpay
  have h4 := e_run_word1 env σ fee hpay
  have h5 := e_run_word2 env σ fee hpay
  have h6 := e_run_log env σ fee hpay
  have h7 := e_run_tail env σ fee hpay
  have t0 := h0
  have t1 := runFuel_trans t0 h1
  have t2 := runFuel_trans t1 h2
  have t3 := runFuel_trans t2 h3
  have t4 := runFuel_trans t3 h4
  have t5 := runFuel_trans t4 h5
  have t6 := runFuel_trans t5 h6
  have t7 := runFuel_trans t6 h7
  simpa using t7

/-! ## Parent theorems (CFG-level, not `Ξ`) -/

theorem depositStart_eq (σ : Storage) (fee : UInt256) :
    depositStart σ fee = raw 0 [fee] σ [] memEmpty [] :=
  rfl

theorem exitStart_eq (σ : Storage) (fee : UInt256) :
    exitStart σ fee = raw 0 [fee] σ [] memEmpty [] :=
  rfl

theorem loadAfter_nil_slot (σ : Storage) (k : UInt256) :
    loadAfter σ [] k = loadSlot σ k :=
  rfl

theorem loadAfter_count_then_tail (σ : Storage) (v : UInt256) :
    loadAfter σ [(UInt256.ofNat 1, v)] (UInt256.ofNat 3) =
      loadSlot σ uQUEUE_TAIL := by
  have h := loadAfter_snoc_ne σ [] (UInt256.ofNat 1) v (UInt256.ofNat 3)
    ofNat_one_ne_three
  simpa [loadAfter_nil_slot, uQUEUE_TAIL, QUEUE_TAIL] using h

theorem deposit_log0_calldata (env : CallEnv) (hsize : env.calldata.size = 184) :
    memSlice
        (calldatacopyMem memEmpty env.calldata
          (UInt256.ofNat 0).toNat (UInt256.ofNat 0).toNat (UInt256.ofNat 184).toNat)
        (UInt256.ofNat 0).toNat (UInt256.ofNat 184).toNat =
      (List.range 184).map (fun i => env.calldata.get! i) := by
  simp [toNat_0, toNat_184]
  rw [memSlice_calldatacopy, calldataBytes_of_exact _ _ hsize]

theorem exit_log0_sender_pubkey (env : CallEnv)
    (hsize : env.calldata.size = 48) :
    memSlice
        (calldatacopyMem
          (mstoreMem memEmpty (UInt256.ofNat 0).toNat
            (UInt256.shiftLeft env.caller (UInt256.ofNat 96)))
          env.calldata
          (UInt256.ofNat 20).toNat (UInt256.ofNat 0).toNat (UInt256.ofNat 48).toNat)
        (UInt256.ofNat 0).toNat (UInt256.ofNat 68).toNat =
      (List.range 20).map
          (fun i => wordByteBE (UInt256.shiftLeft env.caller (UInt256.ofNat 96)) i) ++
        (List.range 48).map (fun i => env.calldata.get! i) := by
  simp [toNat_0, toNat_20, toNat_48, toNat_68]
  rw [memSlice_copy_68, memSlice_mstore_20, calldataBytes_of_exact _ _ hsize]

/--
**P-SUBMIT-1 deposit append, CFG-level.** Relative PC 0 is F1
`Deposit.handle_input = 159`. Paying means the three `JUMPI @revert`
guards fall through (`PaidDeposit`). `CallHyp` records well-formed
storage, user caller, gas ≥ 30M, fuel ≥ 80000. Fee is a stack parameter.
SSTORE/LOG0 are the CFG stepper, not `Ξ`.
-/
theorem deposit_handle_input_append
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (_h : CallHyp .deposit σ)
    (huser : _h.isUser = true)
    (hinh : slotExcess σ ≠ inhibitor)
    (hsize : env.calldata.size = 184)
    (hpay : PaidDeposit env fee) :
    runFuel depositHandleInput env 82 (depositStart σ fee) =
      .ok (done 125 [] σ
        [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))),
         (((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))),
           (calldataWord env.calldata (UInt256.ofNat 0).toNat)),
         (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))),
           (calldataWord env.calldata (UInt256.ofNat 32).toNat)),
         (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))),
           (calldataWord env.calldata (UInt256.ofNat 64).toNat)),
         (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))),
           (calldataWord env.calldata (UInt256.ofNat 96).toNat)),
         (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))))),
           (calldataWord env.calldata (UInt256.ofNat 128).toNat)),
         (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 6) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))))))),
           (calldataWord env.calldata (UInt256.ofNat 160).toNat)),
         ((UInt256.ofNat 3), ((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))]
        (calldatacopyMem memEmpty env.calldata
          (UInt256.ofNat 0).toNat (UInt256.ofNat 0).toNat (UInt256.ofNat 184).toNat)
        [memSlice
          (calldatacopyMem memEmpty env.calldata
            (UInt256.ofNat 0).toNat (UInt256.ofNat 0).toNat (UInt256.ofNat 184).toNat)
          (UInt256.ofNat 0).toNat (UInt256.ofNat 184).toNat]) ∧
      memSlice
          (calldatacopyMem memEmpty env.calldata
            (UInt256.ofNat 0).toNat (UInt256.ofNat 0).toNat (UInt256.ofNat 184).toNat)
          (UInt256.ofNat 0).toNat (UInt256.ofNat 184).toNat =
        (List.range 184).map (fun i => env.calldata.get! i) ∧
      _h.isUser = true ∧
      slotExcess σ ≠ inhibitor ∧
      env.calldata.size = 184 :=
  ⟨by simpa [depositStart] using deposit_handle_input_run env σ fee hpay,
    deposit_log0_calldata env hsize, huser, hinh, hsize⟩

/--
**P-SUBMIT-1 exit append, CFG-level.** Relative PC 0 is F1
`Exit.handle_input = 158`. Paying means the fee `JUMPI @revert` falls
through. First queued word is `CALLER`. LOG0 is 68 bytes = sender‖pubkey.
-/
theorem exit_handle_input_append
    (env : CallEnv) (σ : Storage) (fee : UInt256)
    (_h : CallHyp .exit σ)
    (huser : _h.isUser = true)
    (hinh : slotExcess σ ≠ inhibitor)
    (hsize : env.calldata.size = 48)
    (hpay : PaidExit env fee) :
    runFuel exitHandleInput env 50 (exitStart σ fee) =
      .ok (done 67 [] σ
        [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1)))),
         (((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))),
           env.caller),
         (((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))),
           (calldataWord env.calldata (UInt256.ofNat 0).toNat)),
         (((UInt256.ofNat 1) + ((UInt256.ofNat 1) + ((UInt256.ofNat 4) + ((UInt256.ofNat 3) * (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3)))))),
           (calldataWord env.calldata (UInt256.ofNat 32).toNat)),
         ((UInt256.ofNat 3), ((UInt256.ofNat 1) + (loadAfter σ [((UInt256.ofNat 1), ((UInt256.ofNat 1) + (loadAfter σ [] (UInt256.ofNat 1))))] (UInt256.ofNat 3))))]
        (calldatacopyMem
          (mstoreMem memEmpty (UInt256.ofNat 0).toNat
            (UInt256.shiftLeft env.caller (UInt256.ofNat 96)))
          env.calldata
          (UInt256.ofNat 20).toNat (UInt256.ofNat 0).toNat (UInt256.ofNat 48).toNat)
        [memSlice
          (calldatacopyMem
            (mstoreMem memEmpty (UInt256.ofNat 0).toNat
              (UInt256.shiftLeft env.caller (UInt256.ofNat 96)))
            env.calldata
            (UInt256.ofNat 20).toNat (UInt256.ofNat 0).toNat (UInt256.ofNat 48).toNat)
          (UInt256.ofNat 0).toNat (UInt256.ofNat 68).toNat]) ∧
      memSlice
          (calldatacopyMem
            (mstoreMem memEmpty (UInt256.ofNat 0).toNat
              (UInt256.shiftLeft env.caller (UInt256.ofNat 96)))
            env.calldata
            (UInt256.ofNat 20).toNat (UInt256.ofNat 0).toNat (UInt256.ofNat 48).toNat)
          (UInt256.ofNat 0).toNat (UInt256.ofNat 68).toNat =
        (List.range 20).map
            (fun i => wordByteBE (UInt256.shiftLeft env.caller (UInt256.ofNat 96)) i) ++
          (List.range 48).map (fun i => env.calldata.get! i) ∧
      _h.isUser = true ∧
      slotExcess σ ≠ inhibitor ∧
      env.calldata.size = 48 := by
  refine ⟨?run, ?log, huser, hinh, hsize⟩
  · simpa [exitStart] using exit_handle_input_run env σ fee hpay
  · exact exit_log0_sender_pubkey env hsize

end Eip8282.Audit.Guarantees.PSubmit1.Append

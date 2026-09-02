import Eip8282.Audit.EntryReach.Machine

/-!
# The straight-line blocks of the two pinned runtimes

Generated from `pinned/bytecode/builder_{deposits,exits}/main.hex` by
`scripts/gen_blocks.py` (reproducible; do not edit by hand). Every block is a
maximal straight-line run of `SymExec.blockOps` between the effectful sites and
the jump targets. For each block:

* `<name>` lists its sites — offsets and decoded instructions;
* `<name>_ok` kernel-checks, over the pinned byte-array literal, that the image
  really decodes those instructions at those offsets, consecutively;
* `<name>_shape` computes, by `rfl`, what the block does to the program counter,
  the stack and the storage-access state, on a machine whose stack is the
  concrete shape the program has at that offset.

Nothing here is an assumption: the shape lemmas are definitional unfoldings of
`SymExec.symBlock`, whose agreement with EVMYulLean's `EvmYul.step` is
`SymExec.pureStep_sound`.
-/

namespace Eip8282.Audit.EntryReach

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall)
open Eip8282.Audit.Model (Kind)

set_option maxRecDepth 4000

/-! ### `deposit` blocks -/

/-- `0`: CALLER PUSH20 EQ PUSH2(284). -/
def deposit_b0 : List Site :=
  [(0, (.CALLER, none)), (1, (.PUSH20, some (UInt256.ofNat 1461501637330902918203684832716283019655932542974, 20))), (22, (.EQ, none)), (23, (.PUSH2, some (UInt256.ofNat 284, 2)))]

theorem deposit_b0_ok : sitesOk depositRuntime deposit_b0 = true := by decide +kernel

theorem deposit_b0_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b0.map Prod.snd) (at_ c st mem aw g 0 (r) e)
      = some (at_ c st mem aw g 26 (UInt256.ofNat 284 :: UInt256.eq (UInt256.ofNat 1461501637330902918203684832716283019655932542974) (callerW st) :: r) e) := rfl

/-- `27`: PUSH0 SLOAD DUP1 PUSH32 EQ PUSH2(624). -/
def deposit_b27 : List Site :=
  [(27, (.PUSH0, none)), (28, (.SLOAD, none)), (29, (.DUP1, none)), (30, (.PUSH32, some (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935, 32))), (63, (.EQ, none)), (64, (.PUSH2, some (UInt256.ofNat 624, 2)))]

theorem deposit_b27_ok : sitesOk depositRuntime deposit_b27 = true := by decide +kernel

theorem deposit_b27_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b27.map Prod.snd) (at_ c st mem aw g 27 (r) e)
      = some (at_ c (touch st (UInt256.ofNat 0)) mem aw g 67 (UInt256.ofNat 624 :: UInt256.eq (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (slotW st (UInt256.ofNat 0)) :: slotW st (UInt256.ofNat 0) :: r) e) := rfl

/-- `68`: PUSH1(1) SLOAD PUSH1(8) DUP2 GT PUSH1(82). -/
def deposit_b68 : List Site :=
  [(68, (.PUSH1, some (UInt256.ofNat 1, 1))), (70, (.SLOAD, none)), (71, (.PUSH1, some (UInt256.ofNat 8, 1))), (73, (.DUP2, none)), (74, (.GT, none)), (75, (.PUSH1, some (UInt256.ofNat 82, 1)))]

theorem deposit_b68_ok : sitesOk depositRuntime deposit_b68 = true := by decide +kernel

theorem deposit_b68_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b68.map Prod.snd) (at_ c st mem aw g 68 (r) e)
      = some (at_ c (touch st (UInt256.ofNat 1)) mem aw g 77 (UInt256.ofNat 82 :: UInt256.gt (slotW st (UInt256.ofNat 1)) (UInt256.ofNat 8) :: slotW st (UInt256.ofNat 1) :: r) e) := rfl

/-- `78`: POP PUSH1(88) JUMP. -/
def deposit_b78 : List Site :=
  [(78, (.POP, none)), (79, (.PUSH1, some (UInt256.ofNat 88, 1))), (81, (.JUMP, none))]

theorem deposit_b78_ok : sitesOk depositRuntime deposit_b78 = true := by decide +kernel

theorem deposit_b78_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b78.map Prod.snd) (at_ c st mem aw g 78 (a0 :: r) e)
      = some (at_ c st mem aw g 88 (r) e) := rfl

/-- `82`: JUMPDEST PUSH1(8) SWAP1 SUB ADD. -/
def deposit_b82 : List Site :=
  [(82, (.JUMPDEST, none)), (83, (.PUSH1, some (UInt256.ofNat 8, 1))), (85, (.SWAP1, none)), (86, (.SUB, none)), (87, (.ADD, none))]

theorem deposit_b82_ok : sitesOk depositRuntime deposit_b82 = true := by decide +kernel

theorem deposit_b82_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b82.map Prod.snd) (at_ c st mem aw g 82 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 88 (((a0 - UInt256.ofNat 8) + a1) :: r) e) := rfl

/-- `88`: JUMPDEST PUSH1(17) SWAP1 PUSH1(1) DUP3 MUL PUSH1(1) SWAP1 PUSH0. -/
def deposit_b88 : List Site :=
  [(88, (.JUMPDEST, none)), (89, (.PUSH1, some (UInt256.ofNat 17, 1))), (91, (.SWAP1, none)), (92, (.PUSH1, some (UInt256.ofNat 1, 1))), (94, (.DUP3, none)), (95, (.MUL, none)), (96, (.PUSH1, some (UInt256.ofNat 1, 1))), (98, (.SWAP1, none)), (99, (.PUSH0, none))]

theorem deposit_b88_ok : sitesOk depositRuntime deposit_b88 = true := by decide +kernel

theorem deposit_b88_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b88.map Prod.snd) (at_ c st mem aw g 88 (a0 :: r) e)
      = some (at_ c st mem aw g 100 (UInt256.ofNat 0 :: (UInt256.ofNat 17 * UInt256.ofNat 1) :: UInt256.ofNat 1 :: a0 :: UInt256.ofNat 17 :: r) e) := rfl

/-- `100`: JUMPDEST PUSH0 DUP3 GT ISZERO PUSH1(127). -/
def deposit_b100 : List Site :=
  [(100, (.JUMPDEST, none)), (101, (.PUSH0, none)), (102, (.DUP3, none)), (103, (.GT, none)), (104, (.ISZERO, none)), (105, (.PUSH1, some (UInt256.ofNat 127, 1)))]

theorem deposit_b100_ok : sitesOk depositRuntime deposit_b100 = true := by decide +kernel

theorem deposit_b100_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b100.map Prod.snd) (at_ c st mem aw g 100 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 107 (UInt256.ofNat 127 :: UInt256.isZero (UInt256.gt (a1) (UInt256.ofNat 0)) :: a0 :: a1 :: r) e) := rfl

/-- `108`: DUP2 ADD SWAP1 DUP4 MUL DUP5 DUP4 MUL SWAP1 DIV SWAP2 PUSH1(1) ADD SWAP2 SWAP1 PUSH1(100) JUMP. -/
def deposit_b108 : List Site :=
  [(108, (.DUP2, none)), (109, (.ADD, none)), (110, (.SWAP1, none)), (111, (.DUP4, none)), (112, (.MUL, none)), (113, (.DUP5, none)), (114, (.DUP4, none)), (115, (.MUL, none)), (116, (.SWAP1, none)), (117, (.DIV, none)), (118, (.SWAP2, none)), (119, (.PUSH1, some (UInt256.ofNat 1, 1))), (121, (.ADD, none)), (122, (.SWAP2, none)), (123, (.SWAP1, none)), (124, (.PUSH1, some (UInt256.ofNat 100, 1))), (126, (.JUMP, none))]

theorem deposit_b108_ok : sitesOk depositRuntime deposit_b108 = true := by decide +kernel

theorem deposit_b108_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 a2 a3 a4 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b108.map Prod.snd) (at_ c st mem aw g 108 (a0 :: a1 :: a2 :: a3 :: a4 :: r) e)
      = some (at_ c st mem aw g 100 ((a1 + a0) :: ((a3 * a1) / (a2 * a4)) :: (UInt256.ofNat 1 + a2) :: a3 :: a4 :: r) e) := rfl

/-- `127`: JUMPDEST SWAP1 SWAP4 SWAP1 DIV SWAP3 POP POP POP CALLDATASIZE PUSH1(184) EQ PUSH1(159). -/
def deposit_b127 : List Site :=
  [(127, (.JUMPDEST, none)), (128, (.SWAP1, none)), (129, (.SWAP4, none)), (130, (.SWAP1, none)), (131, (.DIV, none)), (132, (.SWAP3, none)), (133, (.POP, none)), (134, (.POP, none)), (135, (.POP, none)), (136, (.CALLDATASIZE, none)), (137, (.PUSH1, some (UInt256.ofNat 184, 1))), (139, (.EQ, none)), (140, (.PUSH1, some (UInt256.ofNat 159, 1)))]

theorem deposit_b127_ok : sitesOk depositRuntime deposit_b127 = true := by decide +kernel

theorem deposit_b127_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 a2 a3 a4 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b127.map Prod.snd) (at_ c st mem aw g 127 (a0 :: a1 :: a2 :: a3 :: a4 :: r) e)
      = some (at_ c st mem aw g 142 (UInt256.ofNat 159 :: UInt256.eq (UInt256.ofNat 184) (cdsizeW st) :: (a0 / a4) :: r) e) := rfl

/-- `143`: CALLDATASIZE PUSH2(624). -/
def deposit_b143 : List Site :=
  [(143, (.CALLDATASIZE, none)), (144, (.PUSH2, some (UInt256.ofNat 624, 2)))]

theorem deposit_b143_ok : sitesOk depositRuntime deposit_b143 = true := by decide +kernel

theorem deposit_b143_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b143.map Prod.snd) (at_ c st mem aw g 143 (r) e)
      = some (at_ c st mem aw g 147 (UInt256.ofNat 624 :: cdsizeW st :: r) e) := rfl

/-- `148`: CALLVALUE PUSH2(624). -/
def deposit_b148 : List Site :=
  [(148, (.CALLVALUE, none)), (149, (.PUSH2, some (UInt256.ofNat 624, 2)))]

theorem deposit_b148_ok : sitesOk depositRuntime deposit_b148 = true := by decide +kernel

theorem deposit_b148_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b148.map Prod.snd) (at_ c st mem aw g 148 (r) e)
      = some (at_ c st mem aw g 152 (UInt256.ofNat 624 :: valueW st :: r) e) := rfl

/-- `153`: PUSH0. -/
def deposit_b153 : List Site :=
  [(153, (.PUSH0, none))]

theorem deposit_b153_ok : sitesOk depositRuntime deposit_b153 = true := by decide +kernel

theorem deposit_b153_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b153.map Prod.snd) (at_ c st mem aw g 153 (r) e)
      = some (at_ c st mem aw g 154 (UInt256.ofNat 0 :: r) e) := rfl

/-- `155`: PUSH1(32) PUSH0. -/
def deposit_b155 : List Site :=
  [(155, (.PUSH1, some (UInt256.ofNat 32, 1))), (157, (.PUSH0, none))]

theorem deposit_b155_ok : sitesOk depositRuntime deposit_b155 = true := by decide +kernel

theorem deposit_b155_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b155.map Prod.snd) (at_ c st mem aw g 155 (r) e)
      = some (at_ c st mem aw g 158 (UInt256.ofNat 0 :: UInt256.ofNat 32 :: r) e) := rfl

/-- `159`: JUMPDEST DUP1 CALLVALUE LT PUSH2(624). -/
def deposit_b159 : List Site :=
  [(159, (.JUMPDEST, none)), (160, (.DUP1, none)), (161, (.CALLVALUE, none)), (162, (.LT, none)), (163, (.PUSH2, some (UInt256.ofNat 624, 2)))]

theorem deposit_b159_ok : sitesOk depositRuntime deposit_b159 = true := by decide +kernel

theorem deposit_b159_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b159.map Prod.snd) (at_ c st mem aw g 159 (a0 :: r) e)
      = some (at_ c st mem aw g 166 (UInt256.ofNat 624 :: UInt256.lt (valueW st) (a0) :: a0 :: r) e) := rfl

/-- `167`: PUSH1(56) CALLDATALOAD PUSH8(18446744073709551615) AND DUP1 PUSH4(1000000000) GT PUSH2(624). -/
def deposit_b167 : List Site :=
  [(167, (.PUSH1, some (UInt256.ofNat 56, 1))), (169, (.CALLDATALOAD, none)), (170, (.PUSH8, some (UInt256.ofNat 18446744073709551615, 8))), (179, (.AND, none)), (180, (.DUP1, none)), (181, (.PUSH4, some (UInt256.ofNat 1000000000, 4))), (186, (.GT, none)), (187, (.PUSH2, some (UInt256.ofNat 624, 2)))]

theorem deposit_b167_ok : sitesOk depositRuntime deposit_b167 = true := by decide +kernel

theorem deposit_b167_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b167.map Prod.snd) (at_ c st mem aw g 167 (r) e)
      = some (at_ c st mem aw g 190 (UInt256.ofNat 624 :: UInt256.gt (UInt256.ofNat 1000000000) (UInt256.land (UInt256.ofNat 18446744073709551615) (cdW st (UInt256.ofNat 56))) :: UInt256.land (UInt256.ofNat 18446744073709551615) (cdW st (UInt256.ofNat 56)) :: r) e) := rfl

/-- `191`: PUSH4(1000000000) MUL SWAP1 CALLVALUE SUB LT PUSH2(624). -/
def deposit_b191 : List Site :=
  [(191, (.PUSH4, some (UInt256.ofNat 1000000000, 4))), (196, (.MUL, none)), (197, (.SWAP1, none)), (198, (.CALLVALUE, none)), (199, (.SUB, none)), (200, (.LT, none)), (201, (.PUSH2, some (UInt256.ofNat 624, 2)))]

theorem deposit_b191_ok : sitesOk depositRuntime deposit_b191 = true := by decide +kernel

theorem deposit_b191_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b191.map Prod.snd) (at_ c st mem aw g 191 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 204 (UInt256.ofNat 624 :: UInt256.lt ((valueW st - a1)) ((UInt256.ofNat 1000000000 * a0)) :: r) e) := rfl

/-- `205`: PUSH1(1) SLOAD PUSH1(1) ADD PUSH1(1). -/
def deposit_b205 : List Site :=
  [(205, (.PUSH1, some (UInt256.ofNat 1, 1))), (207, (.SLOAD, none)), (208, (.PUSH1, some (UInt256.ofNat 1, 1))), (210, (.ADD, none)), (211, (.PUSH1, some (UInt256.ofNat 1, 1)))]

theorem deposit_b205_ok : sitesOk depositRuntime deposit_b205 = true := by decide +kernel

theorem deposit_b205_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b205.map Prod.snd) (at_ c st mem aw g 205 (r) e)
      = some (at_ c (touch st (UInt256.ofNat 1)) mem aw g 213 (UInt256.ofNat 1 :: (UInt256.ofNat 1 + slotW st (UInt256.ofNat 1)) :: r) e) := rfl

/-- `214`: PUSH1(3) SLOAD DUP1 PUSH1(6) MUL PUSH1(4) ADD PUSH0 CALLDATALOAD DUP2. -/
def deposit_b214 : List Site :=
  [(214, (.PUSH1, some (UInt256.ofNat 3, 1))), (216, (.SLOAD, none)), (217, (.DUP1, none)), (218, (.PUSH1, some (UInt256.ofNat 6, 1))), (220, (.MUL, none)), (221, (.PUSH1, some (UInt256.ofNat 4, 1))), (223, (.ADD, none)), (224, (.PUSH0, none)), (225, (.CALLDATALOAD, none)), (226, (.DUP2, none))]

theorem deposit_b214_ok : sitesOk depositRuntime deposit_b214 = true := by decide +kernel

theorem deposit_b214_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b214.map Prod.snd) (at_ c st mem aw g 214 (r) e)
      = some (at_ c (touch st (UInt256.ofNat 3)) mem aw g 227 ((UInt256.ofNat 4 + (UInt256.ofNat 6 * slotW st (UInt256.ofNat 3))) :: cdW (touch st (UInt256.ofNat 3)) (UInt256.ofNat 0) :: (UInt256.ofNat 4 + (UInt256.ofNat 6 * slotW st (UInt256.ofNat 3))) :: slotW st (UInt256.ofNat 3) :: r) e) := rfl

/-- `228`: PUSH1(1) ADD PUSH1(32) CALLDATALOAD DUP2. -/
def deposit_b228 : List Site :=
  [(228, (.PUSH1, some (UInt256.ofNat 1, 1))), (230, (.ADD, none)), (231, (.PUSH1, some (UInt256.ofNat 32, 1))), (233, (.CALLDATALOAD, none)), (234, (.DUP2, none))]

theorem deposit_b228_ok : sitesOk depositRuntime deposit_b228 = true := by decide +kernel

theorem deposit_b228_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b228.map Prod.snd) (at_ c st mem aw g 228 (a0 :: r) e)
      = some (at_ c st mem aw g 235 ((UInt256.ofNat 1 + a0) :: cdW st (UInt256.ofNat 32) :: (UInt256.ofNat 1 + a0) :: r) e) := rfl

/-- `236`: PUSH1(1) ADD PUSH1(64) CALLDATALOAD DUP2. -/
def deposit_b236 : List Site :=
  [(236, (.PUSH1, some (UInt256.ofNat 1, 1))), (238, (.ADD, none)), (239, (.PUSH1, some (UInt256.ofNat 64, 1))), (241, (.CALLDATALOAD, none)), (242, (.DUP2, none))]

theorem deposit_b236_ok : sitesOk depositRuntime deposit_b236 = true := by decide +kernel

theorem deposit_b236_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b236.map Prod.snd) (at_ c st mem aw g 236 (a0 :: r) e)
      = some (at_ c st mem aw g 243 ((UInt256.ofNat 1 + a0) :: cdW st (UInt256.ofNat 64) :: (UInt256.ofNat 1 + a0) :: r) e) := rfl

/-- `244`: PUSH1(1) ADD PUSH1(96) CALLDATALOAD DUP2. -/
def deposit_b244 : List Site :=
  [(244, (.PUSH1, some (UInt256.ofNat 1, 1))), (246, (.ADD, none)), (247, (.PUSH1, some (UInt256.ofNat 96, 1))), (249, (.CALLDATALOAD, none)), (250, (.DUP2, none))]

theorem deposit_b244_ok : sitesOk depositRuntime deposit_b244 = true := by decide +kernel

theorem deposit_b244_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b244.map Prod.snd) (at_ c st mem aw g 244 (a0 :: r) e)
      = some (at_ c st mem aw g 251 ((UInt256.ofNat 1 + a0) :: cdW st (UInt256.ofNat 96) :: (UInt256.ofNat 1 + a0) :: r) e) := rfl

/-- `252`: PUSH1(1) ADD PUSH1(128) CALLDATALOAD DUP2. -/
def deposit_b252 : List Site :=
  [(252, (.PUSH1, some (UInt256.ofNat 1, 1))), (254, (.ADD, none)), (255, (.PUSH1, some (UInt256.ofNat 128, 1))), (257, (.CALLDATALOAD, none)), (258, (.DUP2, none))]

theorem deposit_b252_ok : sitesOk depositRuntime deposit_b252 = true := by decide +kernel

theorem deposit_b252_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b252.map Prod.snd) (at_ c st mem aw g 252 (a0 :: r) e)
      = some (at_ c st mem aw g 259 ((UInt256.ofNat 1 + a0) :: cdW st (UInt256.ofNat 128) :: (UInt256.ofNat 1 + a0) :: r) e) := rfl

/-- `260`: PUSH1(1) ADD PUSH1(160) CALLDATALOAD SWAP1. -/
def deposit_b260 : List Site :=
  [(260, (.PUSH1, some (UInt256.ofNat 1, 1))), (262, (.ADD, none)), (263, (.PUSH1, some (UInt256.ofNat 160, 1))), (265, (.CALLDATALOAD, none)), (266, (.SWAP1, none))]

theorem deposit_b260_ok : sitesOk depositRuntime deposit_b260 = true := by decide +kernel

theorem deposit_b260_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b260.map Prod.snd) (at_ c st mem aw g 260 (a0 :: r) e)
      = some (at_ c st mem aw g 267 ((UInt256.ofNat 1 + a0) :: cdW st (UInt256.ofNat 160) :: r) e) := rfl

/-- `268`: PUSH1(184) PUSH0 PUSH0. -/
def deposit_b268 : List Site :=
  [(268, (.PUSH1, some (UInt256.ofNat 184, 1))), (270, (.PUSH0, none)), (271, (.PUSH0, none))]

theorem deposit_b268_ok : sitesOk depositRuntime deposit_b268 = true := by decide +kernel

theorem deposit_b268_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b268.map Prod.snd) (at_ c st mem aw g 268 (r) e)
      = some (at_ c st mem aw g 272 (UInt256.ofNat 0 :: UInt256.ofNat 0 :: UInt256.ofNat 184 :: r) e) := rfl

/-- `273`: PUSH1(184) PUSH0. -/
def deposit_b273 : List Site :=
  [(273, (.PUSH1, some (UInt256.ofNat 184, 1))), (275, (.PUSH0, none))]

theorem deposit_b273_ok : sitesOk depositRuntime deposit_b273 = true := by decide +kernel

theorem deposit_b273_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b273.map Prod.snd) (at_ c st mem aw g 273 (r) e)
      = some (at_ c st mem aw g 276 (UInt256.ofNat 0 :: UInt256.ofNat 184 :: r) e) := rfl

/-- `277`: PUSH1(1) ADD PUSH1(3). -/
def deposit_b277 : List Site :=
  [(277, (.PUSH1, some (UInt256.ofNat 1, 1))), (279, (.ADD, none)), (280, (.PUSH1, some (UInt256.ofNat 3, 1)))]

theorem deposit_b277_ok : sitesOk depositRuntime deposit_b277 = true := by decide +kernel

theorem deposit_b277_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b277.map Prod.snd) (at_ c st mem aw g 277 (a0 :: r) e)
      = some (at_ c st mem aw g 282 (UInt256.ofNat 3 :: (UInt256.ofNat 1 + a0) :: r) e) := rfl

/-- `284`: JUMPDEST PUSH1(3) SLOAD PUSH1(2) SLOAD DUP1 DUP3 SUB DUP1 PUSH1(64) GT PUSH2(305). -/
def deposit_b284 : List Site :=
  [(284, (.JUMPDEST, none)), (285, (.PUSH1, some (UInt256.ofNat 3, 1))), (287, (.SLOAD, none)), (288, (.PUSH1, some (UInt256.ofNat 2, 1))), (290, (.SLOAD, none)), (291, (.DUP1, none)), (292, (.DUP3, none)), (293, (.SUB, none)), (294, (.DUP1, none)), (295, (.PUSH1, some (UInt256.ofNat 64, 1))), (297, (.GT, none)), (298, (.PUSH2, some (UInt256.ofNat 305, 2)))]

theorem deposit_b284_ok : sitesOk depositRuntime deposit_b284 = true := by decide +kernel

theorem deposit_b284_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b284.map Prod.snd) (at_ c st mem aw g 284 (r) e)
      = some (at_ c (touch (touch st (UInt256.ofNat 3)) (UInt256.ofNat 2)) mem aw g 301 (UInt256.ofNat 305 :: UInt256.gt (UInt256.ofNat 64) ((slotW st (UInt256.ofNat 3) - slotW (touch st (UInt256.ofNat 3)) (UInt256.ofNat 2))) :: (slotW st (UInt256.ofNat 3) - slotW (touch st (UInt256.ofNat 3)) (UInt256.ofNat 2)) :: slotW (touch st (UInt256.ofNat 3)) (UInt256.ofNat 2) :: slotW st (UInt256.ofNat 3) :: r) e) := rfl

/-- `302`: POP PUSH1(64). -/
def deposit_b302 : List Site :=
  [(302, (.POP, none)), (303, (.PUSH1, some (UInt256.ofNat 64, 1)))]

theorem deposit_b302_ok : sitesOk depositRuntime deposit_b302 = true := by decide +kernel

theorem deposit_b302_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b302.map Prod.snd) (at_ c st mem aw g 302 (a0 :: r) e)
      = some (at_ c st mem aw g 305 (UInt256.ofNat 64 :: r) e) := rfl

/-- `305`: JUMPDEST PUSH0. -/
def deposit_b305 : List Site :=
  [(305, (.JUMPDEST, none)), (306, (.PUSH0, none))]

theorem deposit_b305_ok : sitesOk depositRuntime deposit_b305 = true := by decide +kernel

theorem deposit_b305_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b305.map Prod.snd) (at_ c st mem aw g 305 (r) e)
      = some (at_ c st mem aw g 307 (UInt256.ofNat 0 :: r) e) := rfl

/-- `307`: JUMPDEST DUP2 DUP2 EQ PUSH2(471). -/
def deposit_b307 : List Site :=
  [(307, (.JUMPDEST, none)), (308, (.DUP2, none)), (309, (.DUP2, none)), (310, (.EQ, none)), (311, (.PUSH2, some (UInt256.ofNat 471, 2)))]

theorem deposit_b307_ok : sitesOk depositRuntime deposit_b307 = true := by decide +kernel

theorem deposit_b307_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b307.map Prod.snd) (at_ c st mem aw g 307 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 314 (UInt256.ofNat 471 :: UInt256.eq (a0) (a1) :: a0 :: a1 :: r) e) := rfl

/-- `315`: DUP3 DUP2 ADD PUSH1(6) MUL PUSH1(4) ADD DUP2 PUSH1(184) MUL DUP2 SLOAD DUP2. -/
def deposit_b315 : List Site :=
  [(315, (.DUP3, none)), (316, (.DUP2, none)), (317, (.ADD, none)), (318, (.PUSH1, some (UInt256.ofNat 6, 1))), (320, (.MUL, none)), (321, (.PUSH1, some (UInt256.ofNat 4, 1))), (323, (.ADD, none)), (324, (.DUP2, none)), (325, (.PUSH1, some (UInt256.ofNat 184, 1))), (327, (.MUL, none)), (328, (.DUP2, none)), (329, (.SLOAD, none)), (330, (.DUP2, none))]

theorem deposit_b315_ok : sitesOk depositRuntime deposit_b315 = true := by decide +kernel

theorem deposit_b315_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 a2 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b315.map Prod.snd) (at_ c st mem aw g 315 (a0 :: a1 :: a2 :: r) e)
      = some (at_ c (touch st ((UInt256.ofNat 4 + (UInt256.ofNat 6 * (a0 + a2))))) mem aw g 331 ((UInt256.ofNat 184 * a0) :: slotW st ((UInt256.ofNat 4 + (UInt256.ofNat 6 * (a0 + a2)))) :: (UInt256.ofNat 184 * a0) :: (UInt256.ofNat 4 + (UInt256.ofNat 6 * (a0 + a2))) :: a0 :: a1 :: a2 :: r) e) := rfl

/-- `332`: PUSH1(32) ADD DUP2 PUSH1(1) ADD SLOAD DUP2. -/
def deposit_b332 : List Site :=
  [(332, (.PUSH1, some (UInt256.ofNat 32, 1))), (334, (.ADD, none)), (335, (.DUP2, none)), (336, (.PUSH1, some (UInt256.ofNat 1, 1))), (338, (.ADD, none)), (339, (.SLOAD, none)), (340, (.DUP2, none))]

theorem deposit_b332_ok : sitesOk depositRuntime deposit_b332 = true := by decide +kernel

theorem deposit_b332_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b332.map Prod.snd) (at_ c st mem aw g 332 (a0 :: a1 :: r) e)
      = some (at_ c (touch st ((UInt256.ofNat 1 + a1))) mem aw g 341 ((UInt256.ofNat 32 + a0) :: slotW st ((UInt256.ofNat 1 + a1)) :: (UInt256.ofNat 32 + a0) :: a1 :: r) e) := rfl

/-- `342`: PUSH1(32) ADD DUP2 PUSH1(2) ADD SLOAD DUP1 DUP3. -/
def deposit_b342 : List Site :=
  [(342, (.PUSH1, some (UInt256.ofNat 32, 1))), (344, (.ADD, none)), (345, (.DUP2, none)), (346, (.PUSH1, some (UInt256.ofNat 2, 1))), (348, (.ADD, none)), (349, (.SLOAD, none)), (350, (.DUP1, none)), (351, (.DUP3, none))]

theorem deposit_b342_ok : sitesOk depositRuntime deposit_b342 = true := by decide +kernel

theorem deposit_b342_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b342.map Prod.snd) (at_ c st mem aw g 342 (a0 :: a1 :: r) e)
      = some (at_ c (touch st ((UInt256.ofNat 2 + a1))) mem aw g 352 ((UInt256.ofNat 32 + a0) :: slotW st ((UInt256.ofNat 2 + a1)) :: slotW st ((UInt256.ofNat 2 + a1)) :: (UInt256.ofNat 32 + a0) :: a1 :: r) e) := rfl

/-- `353`: PUSH1(64) SHR PUSH8(18446744073709551615) AND DUP2 PUSH1(16) ADD DUP2 PUSH1(56) SHR DUP2 PUSH1(7) ADD. -/
def deposit_b353 : List Site :=
  [(353, (.PUSH1, some (UInt256.ofNat 64, 1))), (355, (.SHR, none)), (356, (.PUSH8, some (UInt256.ofNat 18446744073709551615, 8))), (365, (.AND, none)), (366, (.DUP2, none)), (367, (.PUSH1, some (UInt256.ofNat 16, 1))), (369, (.ADD, none)), (370, (.DUP2, none)), (371, (.PUSH1, some (UInt256.ofNat 56, 1))), (373, (.SHR, none)), (374, (.DUP2, none)), (375, (.PUSH1, some (UInt256.ofNat 7, 1))), (377, (.ADD, none))]

theorem deposit_b353_ok : sitesOk depositRuntime deposit_b353 = true := by decide +kernel

theorem deposit_b353_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b353.map Prod.snd) (at_ c st mem aw g 353 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 378 ((UInt256.ofNat 7 + (UInt256.ofNat 16 + a1)) :: UInt256.shiftRight (UInt256.land (UInt256.ofNat 18446744073709551615) (UInt256.shiftRight (a0) (UInt256.ofNat 64))) (UInt256.ofNat 56) :: (UInt256.ofNat 16 + a1) :: UInt256.land (UInt256.ofNat 18446744073709551615) (UInt256.shiftRight (a0) (UInt256.ofNat 64)) :: a1 :: r) e) := rfl

/-- `379`: DUP2 PUSH1(48) SHR DUP2 PUSH1(6) ADD. -/
def deposit_b379 : List Site :=
  [(379, (.DUP2, none)), (380, (.PUSH1, some (UInt256.ofNat 48, 1))), (382, (.SHR, none)), (383, (.DUP2, none)), (384, (.PUSH1, some (UInt256.ofNat 6, 1))), (386, (.ADD, none))]

theorem deposit_b379_ok : sitesOk depositRuntime deposit_b379 = true := by decide +kernel

theorem deposit_b379_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b379.map Prod.snd) (at_ c st mem aw g 379 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 387 ((UInt256.ofNat 6 + a0) :: UInt256.shiftRight (a1) (UInt256.ofNat 48) :: a0 :: a1 :: r) e) := rfl

/-- `388`: DUP2 PUSH1(40) SHR DUP2 PUSH1(5) ADD. -/
def deposit_b388 : List Site :=
  [(388, (.DUP2, none)), (389, (.PUSH1, some (UInt256.ofNat 40, 1))), (391, (.SHR, none)), (392, (.DUP2, none)), (393, (.PUSH1, some (UInt256.ofNat 5, 1))), (395, (.ADD, none))]

theorem deposit_b388_ok : sitesOk depositRuntime deposit_b388 = true := by decide +kernel

theorem deposit_b388_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b388.map Prod.snd) (at_ c st mem aw g 388 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 396 ((UInt256.ofNat 5 + a0) :: UInt256.shiftRight (a1) (UInt256.ofNat 40) :: a0 :: a1 :: r) e) := rfl

/-- `397`: DUP2 PUSH1(32) SHR DUP2 PUSH1(4) ADD. -/
def deposit_b397 : List Site :=
  [(397, (.DUP2, none)), (398, (.PUSH1, some (UInt256.ofNat 32, 1))), (400, (.SHR, none)), (401, (.DUP2, none)), (402, (.PUSH1, some (UInt256.ofNat 4, 1))), (404, (.ADD, none))]

theorem deposit_b397_ok : sitesOk depositRuntime deposit_b397 = true := by decide +kernel

theorem deposit_b397_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b397.map Prod.snd) (at_ c st mem aw g 397 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 405 ((UInt256.ofNat 4 + a0) :: UInt256.shiftRight (a1) (UInt256.ofNat 32) :: a0 :: a1 :: r) e) := rfl

/-- `406`: DUP2 PUSH1(24) SHR DUP2 PUSH1(3) ADD. -/
def deposit_b406 : List Site :=
  [(406, (.DUP2, none)), (407, (.PUSH1, some (UInt256.ofNat 24, 1))), (409, (.SHR, none)), (410, (.DUP2, none)), (411, (.PUSH1, some (UInt256.ofNat 3, 1))), (413, (.ADD, none))]

theorem deposit_b406_ok : sitesOk depositRuntime deposit_b406 = true := by decide +kernel

theorem deposit_b406_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b406.map Prod.snd) (at_ c st mem aw g 406 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 414 ((UInt256.ofNat 3 + a0) :: UInt256.shiftRight (a1) (UInt256.ofNat 24) :: a0 :: a1 :: r) e) := rfl

/-- `415`: DUP2 PUSH1(16) SHR DUP2 PUSH1(2) ADD. -/
def deposit_b415 : List Site :=
  [(415, (.DUP2, none)), (416, (.PUSH1, some (UInt256.ofNat 16, 1))), (418, (.SHR, none)), (419, (.DUP2, none)), (420, (.PUSH1, some (UInt256.ofNat 2, 1))), (422, (.ADD, none))]

theorem deposit_b415_ok : sitesOk depositRuntime deposit_b415 = true := by decide +kernel

theorem deposit_b415_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b415.map Prod.snd) (at_ c st mem aw g 415 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 423 ((UInt256.ofNat 2 + a0) :: UInt256.shiftRight (a1) (UInt256.ofNat 16) :: a0 :: a1 :: r) e) := rfl

/-- `424`: DUP2 PUSH1(8) SHR DUP2 PUSH1(1) ADD. -/
def deposit_b424 : List Site :=
  [(424, (.DUP2, none)), (425, (.PUSH1, some (UInt256.ofNat 8, 1))), (427, (.SHR, none)), (428, (.DUP2, none)), (429, (.PUSH1, some (UInt256.ofNat 1, 1))), (431, (.ADD, none))]

theorem deposit_b424_ok : sitesOk depositRuntime deposit_b424 = true := by decide +kernel

theorem deposit_b424_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b424.map Prod.snd) (at_ c st mem aw g 424 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 432 ((UInt256.ofNat 1 + a0) :: UInt256.shiftRight (a1) (UInt256.ofNat 8) :: a0 :: a1 :: r) e) := rfl

/-- `434`: PUSH1(32) ADD DUP2 PUSH1(3) ADD SLOAD DUP2. -/
def deposit_b434 : List Site :=
  [(434, (.PUSH1, some (UInt256.ofNat 32, 1))), (436, (.ADD, none)), (437, (.DUP2, none)), (438, (.PUSH1, some (UInt256.ofNat 3, 1))), (440, (.ADD, none)), (441, (.SLOAD, none)), (442, (.DUP2, none))]

theorem deposit_b434_ok : sitesOk depositRuntime deposit_b434 = true := by decide +kernel

theorem deposit_b434_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b434.map Prod.snd) (at_ c st mem aw g 434 (a0 :: a1 :: r) e)
      = some (at_ c (touch st ((UInt256.ofNat 3 + a1))) mem aw g 443 ((UInt256.ofNat 32 + a0) :: slotW st ((UInt256.ofNat 3 + a1)) :: (UInt256.ofNat 32 + a0) :: a1 :: r) e) := rfl

/-- `444`: PUSH1(32) ADD DUP2 PUSH1(4) ADD SLOAD DUP2. -/
def deposit_b444 : List Site :=
  [(444, (.PUSH1, some (UInt256.ofNat 32, 1))), (446, (.ADD, none)), (447, (.DUP2, none)), (448, (.PUSH1, some (UInt256.ofNat 4, 1))), (450, (.ADD, none)), (451, (.SLOAD, none)), (452, (.DUP2, none))]

theorem deposit_b444_ok : sitesOk depositRuntime deposit_b444 = true := by decide +kernel

theorem deposit_b444_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b444.map Prod.snd) (at_ c st mem aw g 444 (a0 :: a1 :: r) e)
      = some (at_ c (touch st ((UInt256.ofNat 4 + a1))) mem aw g 453 ((UInt256.ofNat 32 + a0) :: slotW st ((UInt256.ofNat 4 + a1)) :: (UInt256.ofNat 32 + a0) :: a1 :: r) e) := rfl

/-- `454`: PUSH1(32) ADD SWAP1 PUSH1(5) ADD SLOAD SWAP1. -/
def deposit_b454 : List Site :=
  [(454, (.PUSH1, some (UInt256.ofNat 32, 1))), (456, (.ADD, none)), (457, (.SWAP1, none)), (458, (.PUSH1, some (UInt256.ofNat 5, 1))), (460, (.ADD, none)), (461, (.SLOAD, none)), (462, (.SWAP1, none))]

theorem deposit_b454_ok : sitesOk depositRuntime deposit_b454 = true := by decide +kernel

theorem deposit_b454_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b454.map Prod.snd) (at_ c st mem aw g 454 (a0 :: a1 :: r) e)
      = some (at_ c (touch st ((UInt256.ofNat 5 + a1))) mem aw g 463 ((UInt256.ofNat 32 + a0) :: slotW st ((UInt256.ofNat 5 + a1)) :: r) e) := rfl

/-- `464`: PUSH1(1) ADD PUSH2(307) JUMP. -/
def deposit_b464 : List Site :=
  [(464, (.PUSH1, some (UInt256.ofNat 1, 1))), (466, (.ADD, none)), (467, (.PUSH2, some (UInt256.ofNat 307, 2))), (470, (.JUMP, none))]

theorem deposit_b464_ok : sitesOk depositRuntime deposit_b464 = true := by decide +kernel

theorem deposit_b464_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b464.map Prod.snd) (at_ c st mem aw g 464 (a0 :: r) e)
      = some (at_ c st mem aw g 307 ((UInt256.ofNat 1 + a0) :: r) e) := rfl

/-- `471`: JUMPDEST SWAP2 ADD DUP1 SWAP3 EQ PUSH2(489). -/
def deposit_b471 : List Site :=
  [(471, (.JUMPDEST, none)), (472, (.SWAP2, none)), (473, (.ADD, none)), (474, (.DUP1, none)), (475, (.SWAP3, none)), (476, (.EQ, none)), (477, (.PUSH2, some (UInt256.ofNat 489, 2)))]

theorem deposit_b471_ok : sitesOk depositRuntime deposit_b471 = true := by decide +kernel

theorem deposit_b471_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 a2 a3 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b471.map Prod.snd) (at_ c st mem aw g 471 (a0 :: a1 :: a2 :: a3 :: r) e)
      = some (at_ c st mem aw g 480 (UInt256.ofNat 489 :: UInt256.eq (a3) ((a2 + a1)) :: a0 :: (a2 + a1) :: r) e) := rfl

/-- `481`: SWAP1 PUSH1(2). -/
def deposit_b481 : List Site :=
  [(481, (.SWAP1, none)), (482, (.PUSH1, some (UInt256.ofNat 2, 1)))]

theorem deposit_b481_ok : sitesOk depositRuntime deposit_b481 = true := by decide +kernel

theorem deposit_b481_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b481.map Prod.snd) (at_ c st mem aw g 481 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 484 (UInt256.ofNat 2 :: a1 :: a0 :: r) e) := rfl

/-- `485`: PUSH2(500) JUMP. -/
def deposit_b485 : List Site :=
  [(485, (.PUSH2, some (UInt256.ofNat 500, 2))), (488, (.JUMP, none))]

theorem deposit_b485_ok : sitesOk depositRuntime deposit_b485 = true := by decide +kernel

theorem deposit_b485_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b485.map Prod.snd) (at_ c st mem aw g 485 (r) e)
      = some (at_ c st mem aw g 500 (r) e) := rfl

/-- `489`: JUMPDEST SWAP1 POP PUSH0 PUSH1(2). -/
def deposit_b489 : List Site :=
  [(489, (.JUMPDEST, none)), (490, (.SWAP1, none)), (491, (.POP, none)), (492, (.PUSH0, none)), (493, (.PUSH1, some (UInt256.ofNat 2, 1)))]

theorem deposit_b489_ok : sitesOk depositRuntime deposit_b489 = true := by decide +kernel

theorem deposit_b489_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b489.map Prod.snd) (at_ c st mem aw g 489 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 495 (UInt256.ofNat 2 :: UInt256.ofNat 0 :: a0 :: r) e) := rfl

/-- `496`: PUSH0 PUSH1(3). -/
def deposit_b496 : List Site :=
  [(496, (.PUSH0, none)), (497, (.PUSH1, some (UInt256.ofNat 3, 1)))]

theorem deposit_b496_ok : sitesOk depositRuntime deposit_b496 = true := by decide +kernel

theorem deposit_b496_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b496.map Prod.snd) (at_ c st mem aw g 496 (r) e)
      = some (at_ c st mem aw g 499 (UInt256.ofNat 3 :: UInt256.ofNat 0 :: r) e) := rfl

/-- `500`: JUMPDEST CALLDATASIZE PUSH2(578). -/
def deposit_b500 : List Site :=
  [(500, (.JUMPDEST, none)), (501, (.CALLDATASIZE, none)), (502, (.PUSH2, some (UInt256.ofNat 578, 2)))]

theorem deposit_b500_ok : sitesOk depositRuntime deposit_b500 = true := by decide +kernel

theorem deposit_b500_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b500.map Prod.snd) (at_ c st mem aw g 500 (r) e)
      = some (at_ c st mem aw g 505 (UInt256.ofNat 578 :: cdsizeW st :: r) e) := rfl

/-- `506`: PUSH0 SLOAD PUSH1(1) SLOAD DUP2 PUSH32 EQ PUSH2(560). -/
def deposit_b506 : List Site :=
  [(506, (.PUSH0, none)), (507, (.SLOAD, none)), (508, (.PUSH1, some (UInt256.ofNat 1, 1))), (510, (.SLOAD, none)), (511, (.DUP2, none)), (512, (.PUSH32, some (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935, 32))), (545, (.EQ, none)), (546, (.PUSH2, some (UInt256.ofNat 560, 2)))]

theorem deposit_b506_ok : sitesOk depositRuntime deposit_b506 = true := by decide +kernel

theorem deposit_b506_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b506.map Prod.snd) (at_ c st mem aw g 506 (r) e)
      = some (at_ c (touch (touch st (UInt256.ofNat 0)) (UInt256.ofNat 1)) mem aw g 549 (UInt256.ofNat 560 :: UInt256.eq (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (slotW st (UInt256.ofNat 0)) :: slotW (touch st (UInt256.ofNat 0)) (UInt256.ofNat 1) :: slotW st (UInt256.ofNat 0) :: r) e) := rfl

/-- `550`: PUSH1(8) DUP3 DUP3 ADD GT PUSH2(568). -/
def deposit_b550 : List Site :=
  [(550, (.PUSH1, some (UInt256.ofNat 8, 1))), (552, (.DUP3, none)), (553, (.DUP3, none)), (554, (.ADD, none)), (555, (.GT, none)), (556, (.PUSH2, some (UInt256.ofNat 568, 2)))]

theorem deposit_b550_ok : sitesOk depositRuntime deposit_b550 = true := by decide +kernel

theorem deposit_b550_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b550.map Prod.snd) (at_ c st mem aw g 550 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 559 (UInt256.ofNat 568 :: UInt256.gt ((a0 + a1)) (UInt256.ofNat 8) :: a0 :: a1 :: r) e) := rfl

/-- `560`: JUMPDEST POP POP PUSH0 PUSH2(612) JUMP. -/
def deposit_b560 : List Site :=
  [(560, (.JUMPDEST, none)), (561, (.POP, none)), (562, (.POP, none)), (563, (.PUSH0, none)), (564, (.PUSH2, some (UInt256.ofNat 612, 2))), (567, (.JUMP, none))]

theorem deposit_b560_ok : sitesOk depositRuntime deposit_b560 = true := by decide +kernel

theorem deposit_b560_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b560.map Prod.snd) (at_ c st mem aw g 560 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 612 (UInt256.ofNat 0 :: r) e) := rfl

/-- `568`: JUMPDEST ADD PUSH1(8) SWAP1 SUB PUSH2(612) JUMP. -/
def deposit_b568 : List Site :=
  [(568, (.JUMPDEST, none)), (569, (.ADD, none)), (570, (.PUSH1, some (UInt256.ofNat 8, 1))), (572, (.SWAP1, none)), (573, (.SUB, none)), (574, (.PUSH2, some (UInt256.ofNat 612, 2))), (577, (.JUMP, none))]

theorem deposit_b568_ok : sitesOk depositRuntime deposit_b568 = true := by decide +kernel

theorem deposit_b568_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b568.map Prod.snd) (at_ c st mem aw g 568 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 612 (((a0 + a1) - UInt256.ofNat 8) :: r) e) := rfl

/-- `578`: JUMPDEST PUSH32. -/
def deposit_b578 : List Site :=
  [(578, (.JUMPDEST, none)), (579, (.PUSH32, some (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935, 32)))]

theorem deposit_b578_ok : sitesOk depositRuntime deposit_b578 = true := by decide +kernel

theorem deposit_b578_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b578.map Prod.snd) (at_ c st mem aw g 578 (r) e)
      = some (at_ c st mem aw g 612 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 :: r) e) := rfl

/-- `612`: JUMPDEST PUSH0. -/
def deposit_b612 : List Site :=
  [(612, (.JUMPDEST, none)), (613, (.PUSH0, none))]

theorem deposit_b612_ok : sitesOk depositRuntime deposit_b612 = true := by decide +kernel

theorem deposit_b612_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b612.map Prod.snd) (at_ c st mem aw g 612 (r) e)
      = some (at_ c st mem aw g 614 (UInt256.ofNat 0 :: r) e) := rfl

/-- `615`: PUSH0 PUSH1(1). -/
def deposit_b615 : List Site :=
  [(615, (.PUSH0, none)), (616, (.PUSH1, some (UInt256.ofNat 1, 1)))]

theorem deposit_b615_ok : sitesOk depositRuntime deposit_b615 = true := by decide +kernel

theorem deposit_b615_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b615.map Prod.snd) (at_ c st mem aw g 615 (r) e)
      = some (at_ c st mem aw g 618 (UInt256.ofNat 1 :: UInt256.ofNat 0 :: r) e) := rfl

/-- `619`: PUSH1(184) MUL PUSH0. -/
def deposit_b619 : List Site :=
  [(619, (.PUSH1, some (UInt256.ofNat 184, 1))), (621, (.MUL, none)), (622, (.PUSH0, none))]

theorem deposit_b619_ok : sitesOk depositRuntime deposit_b619 = true := by decide +kernel

theorem deposit_b619_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b619.map Prod.snd) (at_ c st mem aw g 619 (a0 :: r) e)
      = some (at_ c st mem aw g 623 (UInt256.ofNat 0 :: (UInt256.ofNat 184 * a0) :: r) e) := rfl

/-- `624`: JUMPDEST PUSH0 PUSH0. -/
def deposit_b624 : List Site :=
  [(624, (.JUMPDEST, none)), (625, (.PUSH0, none)), (626, (.PUSH0, none))]

theorem deposit_b624_ok : sitesOk depositRuntime deposit_b624 = true := by decide +kernel

theorem deposit_b624_shape (c : XiCall .deposit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock depositJumpdestNats (deposit_b624.map Prod.snd) (at_ c st mem aw g 624 (r) e)
      = some (at_ c st mem aw g 627 (UInt256.ofNat 0 :: UInt256.ofNat 0 :: r) e) := rfl

/-! ### `exit` blocks -/

/-- `0`: CALLER PUSH20 EQ PUSH1(225). -/
def exit_b0 : List Site :=
  [(0, (.CALLER, none)), (1, (.PUSH20, some (UInt256.ofNat 1461501637330902918203684832716283019655932542974, 20))), (22, (.EQ, none)), (23, (.PUSH1, some (UInt256.ofNat 225, 1)))]

theorem exit_b0_ok : sitesOk exitRuntime exit_b0 = true := by decide +kernel

theorem exit_b0_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b0.map Prod.snd) (at_ c st mem aw g 0 (r) e)
      = some (at_ c st mem aw g 25 (UInt256.ofNat 225 :: UInt256.eq (UInt256.ofNat 1461501637330902918203684832716283019655932542974) (callerW st) :: r) e) := rfl

/-- `26`: PUSH0 SLOAD DUP1 PUSH32 EQ PUSH2(454). -/
def exit_b26 : List Site :=
  [(26, (.PUSH0, none)), (27, (.SLOAD, none)), (28, (.DUP1, none)), (29, (.PUSH32, some (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935, 32))), (62, (.EQ, none)), (63, (.PUSH2, some (UInt256.ofNat 454, 2)))]

theorem exit_b26_ok : sitesOk exitRuntime exit_b26 = true := by decide +kernel

theorem exit_b26_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b26.map Prod.snd) (at_ c st mem aw g 26 (r) e)
      = some (at_ c (touch st (UInt256.ofNat 0)) mem aw g 66 (UInt256.ofNat 454 :: UInt256.eq (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (slotW st (UInt256.ofNat 0)) :: slotW st (UInt256.ofNat 0) :: r) e) := rfl

/-- `67`: PUSH1(1) SLOAD PUSH1(2) DUP2 GT PUSH1(81). -/
def exit_b67 : List Site :=
  [(67, (.PUSH1, some (UInt256.ofNat 1, 1))), (69, (.SLOAD, none)), (70, (.PUSH1, some (UInt256.ofNat 2, 1))), (72, (.DUP2, none)), (73, (.GT, none)), (74, (.PUSH1, some (UInt256.ofNat 81, 1)))]

theorem exit_b67_ok : sitesOk exitRuntime exit_b67 = true := by decide +kernel

theorem exit_b67_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b67.map Prod.snd) (at_ c st mem aw g 67 (r) e)
      = some (at_ c (touch st (UInt256.ofNat 1)) mem aw g 76 (UInt256.ofNat 81 :: UInt256.gt (slotW st (UInt256.ofNat 1)) (UInt256.ofNat 2) :: slotW st (UInt256.ofNat 1) :: r) e) := rfl

/-- `77`: POP PUSH1(87) JUMP. -/
def exit_b77 : List Site :=
  [(77, (.POP, none)), (78, (.PUSH1, some (UInt256.ofNat 87, 1))), (80, (.JUMP, none))]

theorem exit_b77_ok : sitesOk exitRuntime exit_b77 = true := by decide +kernel

theorem exit_b77_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b77.map Prod.snd) (at_ c st mem aw g 77 (a0 :: r) e)
      = some (at_ c st mem aw g 87 (r) e) := rfl

/-- `81`: JUMPDEST PUSH1(2) SWAP1 SUB ADD. -/
def exit_b81 : List Site :=
  [(81, (.JUMPDEST, none)), (82, (.PUSH1, some (UInt256.ofNat 2, 1))), (84, (.SWAP1, none)), (85, (.SUB, none)), (86, (.ADD, none))]

theorem exit_b81_ok : sitesOk exitRuntime exit_b81 = true := by decide +kernel

theorem exit_b81_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b81.map Prod.snd) (at_ c st mem aw g 81 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 87 (((a0 - UInt256.ofNat 2) + a1) :: r) e) := rfl

/-- `87`: JUMPDEST PUSH1(17) SWAP1 PUSH1(1) DUP3 MUL PUSH1(1) SWAP1 PUSH0. -/
def exit_b87 : List Site :=
  [(87, (.JUMPDEST, none)), (88, (.PUSH1, some (UInt256.ofNat 17, 1))), (90, (.SWAP1, none)), (91, (.PUSH1, some (UInt256.ofNat 1, 1))), (93, (.DUP3, none)), (94, (.MUL, none)), (95, (.PUSH1, some (UInt256.ofNat 1, 1))), (97, (.SWAP1, none)), (98, (.PUSH0, none))]

theorem exit_b87_ok : sitesOk exitRuntime exit_b87 = true := by decide +kernel

theorem exit_b87_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b87.map Prod.snd) (at_ c st mem aw g 87 (a0 :: r) e)
      = some (at_ c st mem aw g 99 (UInt256.ofNat 0 :: (UInt256.ofNat 17 * UInt256.ofNat 1) :: UInt256.ofNat 1 :: a0 :: UInt256.ofNat 17 :: r) e) := rfl

/-- `99`: JUMPDEST PUSH0 DUP3 GT ISZERO PUSH1(126). -/
def exit_b99 : List Site :=
  [(99, (.JUMPDEST, none)), (100, (.PUSH0, none)), (101, (.DUP3, none)), (102, (.GT, none)), (103, (.ISZERO, none)), (104, (.PUSH1, some (UInt256.ofNat 126, 1)))]

theorem exit_b99_ok : sitesOk exitRuntime exit_b99 = true := by decide +kernel

theorem exit_b99_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b99.map Prod.snd) (at_ c st mem aw g 99 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 106 (UInt256.ofNat 126 :: UInt256.isZero (UInt256.gt (a1) (UInt256.ofNat 0)) :: a0 :: a1 :: r) e) := rfl

/-- `107`: DUP2 ADD SWAP1 DUP4 MUL DUP5 DUP4 MUL SWAP1 DIV SWAP2 PUSH1(1) ADD SWAP2 SWAP1 PUSH1(99) JUMP. -/
def exit_b107 : List Site :=
  [(107, (.DUP2, none)), (108, (.ADD, none)), (109, (.SWAP1, none)), (110, (.DUP4, none)), (111, (.MUL, none)), (112, (.DUP5, none)), (113, (.DUP4, none)), (114, (.MUL, none)), (115, (.SWAP1, none)), (116, (.DIV, none)), (117, (.SWAP2, none)), (118, (.PUSH1, some (UInt256.ofNat 1, 1))), (120, (.ADD, none)), (121, (.SWAP2, none)), (122, (.SWAP1, none)), (123, (.PUSH1, some (UInt256.ofNat 99, 1))), (125, (.JUMP, none))]

theorem exit_b107_ok : sitesOk exitRuntime exit_b107 = true := by decide +kernel

theorem exit_b107_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 a2 a3 a4 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b107.map Prod.snd) (at_ c st mem aw g 107 (a0 :: a1 :: a2 :: a3 :: a4 :: r) e)
      = some (at_ c st mem aw g 99 ((a1 + a0) :: ((a3 * a1) / (a2 * a4)) :: (UInt256.ofNat 1 + a2) :: a3 :: a4 :: r) e) := rfl

/-- `126`: JUMPDEST SWAP1 SWAP4 SWAP1 DIV SWAP3 POP POP POP CALLDATASIZE PUSH1(48) EQ PUSH1(158). -/
def exit_b126 : List Site :=
  [(126, (.JUMPDEST, none)), (127, (.SWAP1, none)), (128, (.SWAP4, none)), (129, (.SWAP1, none)), (130, (.DIV, none)), (131, (.SWAP3, none)), (132, (.POP, none)), (133, (.POP, none)), (134, (.POP, none)), (135, (.CALLDATASIZE, none)), (136, (.PUSH1, some (UInt256.ofNat 48, 1))), (138, (.EQ, none)), (139, (.PUSH1, some (UInt256.ofNat 158, 1)))]

theorem exit_b126_ok : sitesOk exitRuntime exit_b126 = true := by decide +kernel

theorem exit_b126_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 a2 a3 a4 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b126.map Prod.snd) (at_ c st mem aw g 126 (a0 :: a1 :: a2 :: a3 :: a4 :: r) e)
      = some (at_ c st mem aw g 141 (UInt256.ofNat 158 :: UInt256.eq (UInt256.ofNat 48) (cdsizeW st) :: (a0 / a4) :: r) e) := rfl

/-- `142`: CALLDATASIZE PUSH2(454). -/
def exit_b142 : List Site :=
  [(142, (.CALLDATASIZE, none)), (143, (.PUSH2, some (UInt256.ofNat 454, 2)))]

theorem exit_b142_ok : sitesOk exitRuntime exit_b142 = true := by decide +kernel

theorem exit_b142_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b142.map Prod.snd) (at_ c st mem aw g 142 (r) e)
      = some (at_ c st mem aw g 146 (UInt256.ofNat 454 :: cdsizeW st :: r) e) := rfl

/-- `147`: CALLVALUE PUSH2(454). -/
def exit_b147 : List Site :=
  [(147, (.CALLVALUE, none)), (148, (.PUSH2, some (UInt256.ofNat 454, 2)))]

theorem exit_b147_ok : sitesOk exitRuntime exit_b147 = true := by decide +kernel

theorem exit_b147_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b147.map Prod.snd) (at_ c st mem aw g 147 (r) e)
      = some (at_ c st mem aw g 151 (UInt256.ofNat 454 :: valueW st :: r) e) := rfl

/-- `152`: PUSH0. -/
def exit_b152 : List Site :=
  [(152, (.PUSH0, none))]

theorem exit_b152_ok : sitesOk exitRuntime exit_b152 = true := by decide +kernel

theorem exit_b152_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b152.map Prod.snd) (at_ c st mem aw g 152 (r) e)
      = some (at_ c st mem aw g 153 (UInt256.ofNat 0 :: r) e) := rfl

/-- `154`: PUSH1(32) PUSH0. -/
def exit_b154 : List Site :=
  [(154, (.PUSH1, some (UInt256.ofNat 32, 1))), (156, (.PUSH0, none))]

theorem exit_b154_ok : sitesOk exitRuntime exit_b154 = true := by decide +kernel

theorem exit_b154_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b154.map Prod.snd) (at_ c st mem aw g 154 (r) e)
      = some (at_ c st mem aw g 157 (UInt256.ofNat 0 :: UInt256.ofNat 32 :: r) e) := rfl

/-- `158`: JUMPDEST CALLVALUE LT PUSH2(454). -/
def exit_b158 : List Site :=
  [(158, (.JUMPDEST, none)), (159, (.CALLVALUE, none)), (160, (.LT, none)), (161, (.PUSH2, some (UInt256.ofNat 454, 2)))]

theorem exit_b158_ok : sitesOk exitRuntime exit_b158 = true := by decide +kernel

theorem exit_b158_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b158.map Prod.snd) (at_ c st mem aw g 158 (a0 :: r) e)
      = some (at_ c st mem aw g 164 (UInt256.ofNat 454 :: UInt256.lt (valueW st) (a0) :: r) e) := rfl

/-- `165`: PUSH1(1) SLOAD PUSH1(1) ADD PUSH1(1). -/
def exit_b165 : List Site :=
  [(165, (.PUSH1, some (UInt256.ofNat 1, 1))), (167, (.SLOAD, none)), (168, (.PUSH1, some (UInt256.ofNat 1, 1))), (170, (.ADD, none)), (171, (.PUSH1, some (UInt256.ofNat 1, 1)))]

theorem exit_b165_ok : sitesOk exitRuntime exit_b165 = true := by decide +kernel

theorem exit_b165_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b165.map Prod.snd) (at_ c st mem aw g 165 (r) e)
      = some (at_ c (touch st (UInt256.ofNat 1)) mem aw g 173 (UInt256.ofNat 1 :: (UInt256.ofNat 1 + slotW st (UInt256.ofNat 1)) :: r) e) := rfl

/-- `174`: PUSH1(3) SLOAD DUP1 PUSH1(3) MUL PUSH1(4) ADD CALLER DUP2. -/
def exit_b174 : List Site :=
  [(174, (.PUSH1, some (UInt256.ofNat 3, 1))), (176, (.SLOAD, none)), (177, (.DUP1, none)), (178, (.PUSH1, some (UInt256.ofNat 3, 1))), (180, (.MUL, none)), (181, (.PUSH1, some (UInt256.ofNat 4, 1))), (183, (.ADD, none)), (184, (.CALLER, none)), (185, (.DUP2, none))]

theorem exit_b174_ok : sitesOk exitRuntime exit_b174 = true := by decide +kernel

theorem exit_b174_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b174.map Prod.snd) (at_ c st mem aw g 174 (r) e)
      = some (at_ c (touch st (UInt256.ofNat 3)) mem aw g 186 ((UInt256.ofNat 4 + (UInt256.ofNat 3 * slotW st (UInt256.ofNat 3))) :: callerW (touch st (UInt256.ofNat 3)) :: (UInt256.ofNat 4 + (UInt256.ofNat 3 * slotW st (UInt256.ofNat 3))) :: slotW st (UInt256.ofNat 3) :: r) e) := rfl

/-- `187`: PUSH1(1) ADD PUSH0 CALLDATALOAD DUP2. -/
def exit_b187 : List Site :=
  [(187, (.PUSH1, some (UInt256.ofNat 1, 1))), (189, (.ADD, none)), (190, (.PUSH0, none)), (191, (.CALLDATALOAD, none)), (192, (.DUP2, none))]

theorem exit_b187_ok : sitesOk exitRuntime exit_b187 = true := by decide +kernel

theorem exit_b187_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b187.map Prod.snd) (at_ c st mem aw g 187 (a0 :: r) e)
      = some (at_ c st mem aw g 193 ((UInt256.ofNat 1 + a0) :: cdW st (UInt256.ofNat 0) :: (UInt256.ofNat 1 + a0) :: r) e) := rfl

/-- `194`: PUSH1(1) ADD PUSH1(32) CALLDATALOAD SWAP1. -/
def exit_b194 : List Site :=
  [(194, (.PUSH1, some (UInt256.ofNat 1, 1))), (196, (.ADD, none)), (197, (.PUSH1, some (UInt256.ofNat 32, 1))), (199, (.CALLDATALOAD, none)), (200, (.SWAP1, none))]

theorem exit_b194_ok : sitesOk exitRuntime exit_b194 = true := by decide +kernel

theorem exit_b194_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b194.map Prod.snd) (at_ c st mem aw g 194 (a0 :: r) e)
      = some (at_ c st mem aw g 201 ((UInt256.ofNat 1 + a0) :: cdW st (UInt256.ofNat 32) :: r) e) := rfl

/-- `202`: CALLER PUSH1(96) SHL PUSH0. -/
def exit_b202 : List Site :=
  [(202, (.CALLER, none)), (203, (.PUSH1, some (UInt256.ofNat 96, 1))), (205, (.SHL, none)), (206, (.PUSH0, none))]

theorem exit_b202_ok : sitesOk exitRuntime exit_b202 = true := by decide +kernel

theorem exit_b202_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b202.map Prod.snd) (at_ c st mem aw g 202 (r) e)
      = some (at_ c st mem aw g 207 (UInt256.ofNat 0 :: UInt256.shiftLeft (callerW st) (UInt256.ofNat 96) :: r) e) := rfl

/-- `208`: PUSH1(48) PUSH0 PUSH1(20). -/
def exit_b208 : List Site :=
  [(208, (.PUSH1, some (UInt256.ofNat 48, 1))), (210, (.PUSH0, none)), (211, (.PUSH1, some (UInt256.ofNat 20, 1)))]

theorem exit_b208_ok : sitesOk exitRuntime exit_b208 = true := by decide +kernel

theorem exit_b208_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b208.map Prod.snd) (at_ c st mem aw g 208 (r) e)
      = some (at_ c st mem aw g 213 (UInt256.ofNat 20 :: UInt256.ofNat 0 :: UInt256.ofNat 48 :: r) e) := rfl

/-- `214`: PUSH1(68) PUSH0. -/
def exit_b214 : List Site :=
  [(214, (.PUSH1, some (UInt256.ofNat 68, 1))), (216, (.PUSH0, none))]

theorem exit_b214_ok : sitesOk exitRuntime exit_b214 = true := by decide +kernel

theorem exit_b214_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b214.map Prod.snd) (at_ c st mem aw g 214 (r) e)
      = some (at_ c st mem aw g 217 (UInt256.ofNat 0 :: UInt256.ofNat 68 :: r) e) := rfl

/-- `218`: PUSH1(1) ADD PUSH1(3). -/
def exit_b218 : List Site :=
  [(218, (.PUSH1, some (UInt256.ofNat 1, 1))), (220, (.ADD, none)), (221, (.PUSH1, some (UInt256.ofNat 3, 1)))]

theorem exit_b218_ok : sitesOk exitRuntime exit_b218 = true := by decide +kernel

theorem exit_b218_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b218.map Prod.snd) (at_ c st mem aw g 218 (a0 :: r) e)
      = some (at_ c st mem aw g 223 (UInt256.ofNat 3 :: (UInt256.ofNat 1 + a0) :: r) e) := rfl

/-- `225`: JUMPDEST PUSH1(3) SLOAD PUSH1(2) SLOAD DUP1 DUP3 SUB DUP1 PUSH1(16) GT PUSH1(245). -/
def exit_b225 : List Site :=
  [(225, (.JUMPDEST, none)), (226, (.PUSH1, some (UInt256.ofNat 3, 1))), (228, (.SLOAD, none)), (229, (.PUSH1, some (UInt256.ofNat 2, 1))), (231, (.SLOAD, none)), (232, (.DUP1, none)), (233, (.DUP3, none)), (234, (.SUB, none)), (235, (.DUP1, none)), (236, (.PUSH1, some (UInt256.ofNat 16, 1))), (238, (.GT, none)), (239, (.PUSH1, some (UInt256.ofNat 245, 1)))]

theorem exit_b225_ok : sitesOk exitRuntime exit_b225 = true := by decide +kernel

theorem exit_b225_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b225.map Prod.snd) (at_ c st mem aw g 225 (r) e)
      = some (at_ c (touch (touch st (UInt256.ofNat 3)) (UInt256.ofNat 2)) mem aw g 241 (UInt256.ofNat 245 :: UInt256.gt (UInt256.ofNat 16) ((slotW st (UInt256.ofNat 3) - slotW (touch st (UInt256.ofNat 3)) (UInt256.ofNat 2))) :: (slotW st (UInt256.ofNat 3) - slotW (touch st (UInt256.ofNat 3)) (UInt256.ofNat 2)) :: slotW (touch st (UInt256.ofNat 3)) (UInt256.ofNat 2) :: slotW st (UInt256.ofNat 3) :: r) e) := rfl

/-- `242`: POP PUSH1(16). -/
def exit_b242 : List Site :=
  [(242, (.POP, none)), (243, (.PUSH1, some (UInt256.ofNat 16, 1)))]

theorem exit_b242_ok : sitesOk exitRuntime exit_b242 = true := by decide +kernel

theorem exit_b242_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b242.map Prod.snd) (at_ c st mem aw g 242 (a0 :: r) e)
      = some (at_ c st mem aw g 245 (UInt256.ofNat 16 :: r) e) := rfl

/-- `245`: JUMPDEST PUSH0. -/
def exit_b245 : List Site :=
  [(245, (.JUMPDEST, none)), (246, (.PUSH0, none))]

theorem exit_b245_ok : sitesOk exitRuntime exit_b245 = true := by decide +kernel

theorem exit_b245_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b245.map Prod.snd) (at_ c st mem aw g 245 (r) e)
      = some (at_ c st mem aw g 247 (UInt256.ofNat 0 :: r) e) := rfl

/-- `247`: JUMPDEST DUP2 DUP2 EQ PUSH2(301). -/
def exit_b247 : List Site :=
  [(247, (.JUMPDEST, none)), (248, (.DUP2, none)), (249, (.DUP2, none)), (250, (.EQ, none)), (251, (.PUSH2, some (UInt256.ofNat 301, 2)))]

theorem exit_b247_ok : sitesOk exitRuntime exit_b247 = true := by decide +kernel

theorem exit_b247_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b247.map Prod.snd) (at_ c st mem aw g 247 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 254 (UInt256.ofNat 301 :: UInt256.eq (a0) (a1) :: a0 :: a1 :: r) e) := rfl

/-- `255`: DUP3 DUP2 ADD PUSH1(3) MUL PUSH1(4) ADD DUP2 PUSH1(68) MUL DUP2 SLOAD PUSH1(96) SHL DUP2. -/
def exit_b255 : List Site :=
  [(255, (.DUP3, none)), (256, (.DUP2, none)), (257, (.ADD, none)), (258, (.PUSH1, some (UInt256.ofNat 3, 1))), (260, (.MUL, none)), (261, (.PUSH1, some (UInt256.ofNat 4, 1))), (263, (.ADD, none)), (264, (.DUP2, none)), (265, (.PUSH1, some (UInt256.ofNat 68, 1))), (267, (.MUL, none)), (268, (.DUP2, none)), (269, (.SLOAD, none)), (270, (.PUSH1, some (UInt256.ofNat 96, 1))), (272, (.SHL, none)), (273, (.DUP2, none))]

theorem exit_b255_ok : sitesOk exitRuntime exit_b255 = true := by decide +kernel

theorem exit_b255_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 a2 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b255.map Prod.snd) (at_ c st mem aw g 255 (a0 :: a1 :: a2 :: r) e)
      = some (at_ c (touch st ((UInt256.ofNat 4 + (UInt256.ofNat 3 * (a0 + a2))))) mem aw g 274 ((UInt256.ofNat 68 * a0) :: UInt256.shiftLeft (slotW st ((UInt256.ofNat 4 + (UInt256.ofNat 3 * (a0 + a2))))) (UInt256.ofNat 96) :: (UInt256.ofNat 68 * a0) :: (UInt256.ofNat 4 + (UInt256.ofNat 3 * (a0 + a2))) :: a0 :: a1 :: a2 :: r) e) := rfl

/-- `275`: PUSH1(20) ADD DUP2 PUSH1(1) ADD SLOAD DUP2. -/
def exit_b275 : List Site :=
  [(275, (.PUSH1, some (UInt256.ofNat 20, 1))), (277, (.ADD, none)), (278, (.DUP2, none)), (279, (.PUSH1, some (UInt256.ofNat 1, 1))), (281, (.ADD, none)), (282, (.SLOAD, none)), (283, (.DUP2, none))]

theorem exit_b275_ok : sitesOk exitRuntime exit_b275 = true := by decide +kernel

theorem exit_b275_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b275.map Prod.snd) (at_ c st mem aw g 275 (a0 :: a1 :: r) e)
      = some (at_ c (touch st ((UInt256.ofNat 1 + a1))) mem aw g 284 ((UInt256.ofNat 20 + a0) :: slotW st ((UInt256.ofNat 1 + a1)) :: (UInt256.ofNat 20 + a0) :: a1 :: r) e) := rfl

/-- `285`: PUSH1(32) ADD SWAP1 PUSH1(2) ADD SLOAD SWAP1. -/
def exit_b285 : List Site :=
  [(285, (.PUSH1, some (UInt256.ofNat 32, 1))), (287, (.ADD, none)), (288, (.SWAP1, none)), (289, (.PUSH1, some (UInt256.ofNat 2, 1))), (291, (.ADD, none)), (292, (.SLOAD, none)), (293, (.SWAP1, none))]

theorem exit_b285_ok : sitesOk exitRuntime exit_b285 = true := by decide +kernel

theorem exit_b285_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b285.map Prod.snd) (at_ c st mem aw g 285 (a0 :: a1 :: r) e)
      = some (at_ c (touch st ((UInt256.ofNat 2 + a1))) mem aw g 294 ((UInt256.ofNat 32 + a0) :: slotW st ((UInt256.ofNat 2 + a1)) :: r) e) := rfl

/-- `295`: PUSH1(1) ADD PUSH1(247) JUMP. -/
def exit_b295 : List Site :=
  [(295, (.PUSH1, some (UInt256.ofNat 1, 1))), (297, (.ADD, none)), (298, (.PUSH1, some (UInt256.ofNat 247, 1))), (300, (.JUMP, none))]

theorem exit_b295_ok : sitesOk exitRuntime exit_b295 = true := by decide +kernel

theorem exit_b295_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b295.map Prod.snd) (at_ c st mem aw g 295 (a0 :: r) e)
      = some (at_ c st mem aw g 247 ((UInt256.ofNat 1 + a0) :: r) e) := rfl

/-- `301`: JUMPDEST SWAP2 ADD DUP1 SWAP3 EQ PUSH2(319). -/
def exit_b301 : List Site :=
  [(301, (.JUMPDEST, none)), (302, (.SWAP2, none)), (303, (.ADD, none)), (304, (.DUP1, none)), (305, (.SWAP3, none)), (306, (.EQ, none)), (307, (.PUSH2, some (UInt256.ofNat 319, 2)))]

theorem exit_b301_ok : sitesOk exitRuntime exit_b301 = true := by decide +kernel

theorem exit_b301_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 a2 a3 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b301.map Prod.snd) (at_ c st mem aw g 301 (a0 :: a1 :: a2 :: a3 :: r) e)
      = some (at_ c st mem aw g 310 (UInt256.ofNat 319 :: UInt256.eq (a3) ((a2 + a1)) :: a0 :: (a2 + a1) :: r) e) := rfl

/-- `311`: SWAP1 PUSH1(2). -/
def exit_b311 : List Site :=
  [(311, (.SWAP1, none)), (312, (.PUSH1, some (UInt256.ofNat 2, 1)))]

theorem exit_b311_ok : sitesOk exitRuntime exit_b311 = true := by decide +kernel

theorem exit_b311_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b311.map Prod.snd) (at_ c st mem aw g 311 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 314 (UInt256.ofNat 2 :: a1 :: a0 :: r) e) := rfl

/-- `315`: PUSH2(330) JUMP. -/
def exit_b315 : List Site :=
  [(315, (.PUSH2, some (UInt256.ofNat 330, 2))), (318, (.JUMP, none))]

theorem exit_b315_ok : sitesOk exitRuntime exit_b315 = true := by decide +kernel

theorem exit_b315_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b315.map Prod.snd) (at_ c st mem aw g 315 (r) e)
      = some (at_ c st mem aw g 330 (r) e) := rfl

/-- `319`: JUMPDEST SWAP1 POP PUSH0 PUSH1(2). -/
def exit_b319 : List Site :=
  [(319, (.JUMPDEST, none)), (320, (.SWAP1, none)), (321, (.POP, none)), (322, (.PUSH0, none)), (323, (.PUSH1, some (UInt256.ofNat 2, 1)))]

theorem exit_b319_ok : sitesOk exitRuntime exit_b319 = true := by decide +kernel

theorem exit_b319_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b319.map Prod.snd) (at_ c st mem aw g 319 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 325 (UInt256.ofNat 2 :: UInt256.ofNat 0 :: a0 :: r) e) := rfl

/-- `326`: PUSH0 PUSH1(3). -/
def exit_b326 : List Site :=
  [(326, (.PUSH0, none)), (327, (.PUSH1, some (UInt256.ofNat 3, 1)))]

theorem exit_b326_ok : sitesOk exitRuntime exit_b326 = true := by decide +kernel

theorem exit_b326_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b326.map Prod.snd) (at_ c st mem aw g 326 (r) e)
      = some (at_ c st mem aw g 329 (UInt256.ofNat 3 :: UInt256.ofNat 0 :: r) e) := rfl

/-- `330`: JUMPDEST CALLDATASIZE PUSH2(408). -/
def exit_b330 : List Site :=
  [(330, (.JUMPDEST, none)), (331, (.CALLDATASIZE, none)), (332, (.PUSH2, some (UInt256.ofNat 408, 2)))]

theorem exit_b330_ok : sitesOk exitRuntime exit_b330 = true := by decide +kernel

theorem exit_b330_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b330.map Prod.snd) (at_ c st mem aw g 330 (r) e)
      = some (at_ c st mem aw g 335 (UInt256.ofNat 408 :: cdsizeW st :: r) e) := rfl

/-- `336`: PUSH0 SLOAD PUSH1(1) SLOAD DUP2 PUSH32 EQ PUSH2(390). -/
def exit_b336 : List Site :=
  [(336, (.PUSH0, none)), (337, (.SLOAD, none)), (338, (.PUSH1, some (UInt256.ofNat 1, 1))), (340, (.SLOAD, none)), (341, (.DUP2, none)), (342, (.PUSH32, some (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935, 32))), (375, (.EQ, none)), (376, (.PUSH2, some (UInt256.ofNat 390, 2)))]

theorem exit_b336_ok : sitesOk exitRuntime exit_b336 = true := by decide +kernel

theorem exit_b336_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b336.map Prod.snd) (at_ c st mem aw g 336 (r) e)
      = some (at_ c (touch (touch st (UInt256.ofNat 0)) (UInt256.ofNat 1)) mem aw g 379 (UInt256.ofNat 390 :: UInt256.eq (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935) (slotW st (UInt256.ofNat 0)) :: slotW (touch st (UInt256.ofNat 0)) (UInt256.ofNat 1) :: slotW st (UInt256.ofNat 0) :: r) e) := rfl

/-- `380`: PUSH1(2) DUP3 DUP3 ADD GT PUSH2(398). -/
def exit_b380 : List Site :=
  [(380, (.PUSH1, some (UInt256.ofNat 2, 1))), (382, (.DUP3, none)), (383, (.DUP3, none)), (384, (.ADD, none)), (385, (.GT, none)), (386, (.PUSH2, some (UInt256.ofNat 398, 2)))]

theorem exit_b380_ok : sitesOk exitRuntime exit_b380 = true := by decide +kernel

theorem exit_b380_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b380.map Prod.snd) (at_ c st mem aw g 380 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 389 (UInt256.ofNat 398 :: UInt256.gt ((a0 + a1)) (UInt256.ofNat 2) :: a0 :: a1 :: r) e) := rfl

/-- `390`: JUMPDEST POP POP PUSH0 PUSH2(442) JUMP. -/
def exit_b390 : List Site :=
  [(390, (.JUMPDEST, none)), (391, (.POP, none)), (392, (.POP, none)), (393, (.PUSH0, none)), (394, (.PUSH2, some (UInt256.ofNat 442, 2))), (397, (.JUMP, none))]

theorem exit_b390_ok : sitesOk exitRuntime exit_b390 = true := by decide +kernel

theorem exit_b390_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b390.map Prod.snd) (at_ c st mem aw g 390 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 442 (UInt256.ofNat 0 :: r) e) := rfl

/-- `398`: JUMPDEST ADD PUSH1(2) SWAP1 SUB PUSH2(442) JUMP. -/
def exit_b398 : List Site :=
  [(398, (.JUMPDEST, none)), (399, (.ADD, none)), (400, (.PUSH1, some (UInt256.ofNat 2, 1))), (402, (.SWAP1, none)), (403, (.SUB, none)), (404, (.PUSH2, some (UInt256.ofNat 442, 2))), (407, (.JUMP, none))]

theorem exit_b398_ok : sitesOk exitRuntime exit_b398 = true := by decide +kernel

theorem exit_b398_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 a1 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b398.map Prod.snd) (at_ c st mem aw g 398 (a0 :: a1 :: r) e)
      = some (at_ c st mem aw g 442 (((a0 + a1) - UInt256.ofNat 2) :: r) e) := rfl

/-- `408`: JUMPDEST PUSH32. -/
def exit_b408 : List Site :=
  [(408, (.JUMPDEST, none)), (409, (.PUSH32, some (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935, 32)))]

theorem exit_b408_ok : sitesOk exitRuntime exit_b408 = true := by decide +kernel

theorem exit_b408_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b408.map Prod.snd) (at_ c st mem aw g 408 (r) e)
      = some (at_ c st mem aw g 442 (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935 :: r) e) := rfl

/-- `442`: JUMPDEST PUSH0. -/
def exit_b442 : List Site :=
  [(442, (.JUMPDEST, none)), (443, (.PUSH0, none))]

theorem exit_b442_ok : sitesOk exitRuntime exit_b442 = true := by decide +kernel

theorem exit_b442_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b442.map Prod.snd) (at_ c st mem aw g 442 (r) e)
      = some (at_ c st mem aw g 444 (UInt256.ofNat 0 :: r) e) := rfl

/-- `445`: PUSH0 PUSH1(1). -/
def exit_b445 : List Site :=
  [(445, (.PUSH0, none)), (446, (.PUSH1, some (UInt256.ofNat 1, 1)))]

theorem exit_b445_ok : sitesOk exitRuntime exit_b445 = true := by decide +kernel

theorem exit_b445_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b445.map Prod.snd) (at_ c st mem aw g 445 (r) e)
      = some (at_ c st mem aw g 448 (UInt256.ofNat 1 :: UInt256.ofNat 0 :: r) e) := rfl

/-- `449`: PUSH1(68) MUL PUSH0. -/
def exit_b449 : List Site :=
  [(449, (.PUSH1, some (UInt256.ofNat 68, 1))), (451, (.MUL, none)), (452, (.PUSH0, none))]

theorem exit_b449_ok : sitesOk exitRuntime exit_b449 = true := by decide +kernel

theorem exit_b449_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (a0 : UInt256) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b449.map Prod.snd) (at_ c st mem aw g 449 (a0 :: r) e)
      = some (at_ c st mem aw g 453 (UInt256.ofNat 0 :: (UInt256.ofNat 68 * a0) :: r) e) := rfl

/-- `454`: JUMPDEST PUSH0 PUSH0. -/
def exit_b454 : List Site :=
  [(454, (.JUMPDEST, none)), (455, (.PUSH0, none)), (456, (.PUSH0, none))]

theorem exit_b454_ok : sitesOk exitRuntime exit_b454 = true := by decide +kernel

theorem exit_b454_shape (c : XiCall .exit) (st : EvmYul.State .EVM) (mem : ByteArray)
    (aw g : UInt256) (e : Nat) (r : Stack UInt256) :
    symBlock exitJumpdestNats (exit_b454.map Prod.snd) (at_ c st mem aw g 454 (r) e)
      = some (at_ c st mem aw g 457 (UInt256.ofNat 0 :: UInt256.ofNat 0 :: r) e) := rfl

end Eip8282.Audit.EntryReach

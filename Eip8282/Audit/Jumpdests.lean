import EvmYul.EVM.Semantics
import Eip8282.Audit.Bytecode

/-!
Concrete `D_J` tables for the pinned EIP-8282 runtimes.

`EvmYul.EVM.D_J` is implemented by the `partial def D_J_aux`, so the kernel
cannot reduce a ground `D_J` application. This module closes those two
runtime scans once (`native_decide`) and exposes the resulting finite
JUMPDEST sets plus the CFG labels the F3 stepper needs. Later lemmas must
rewrite with `deposit_D_J` / `exit_D_J` rather than re-entering `D_J_aux`.

PCs are byte offsets into the **runtime** image (`depositRuntime` /
`exitRuntime`). They match `JUMPDEST` labels in
`pinned/sys-asm/builder_{deposits,exits}/main.eas` after the `#include` of
`fake_expo`. Both programs start
`CALLER; PUSH20 SYSTEM_ADDR; EQ; JUMPI @read_requests`; the `EQ` sits at
offset 22 (`0x14`).
-/

namespace Eip8282.Audit.Jumpdests

open EvmYul
open EvmYul.EVM
open Eip8282.Audit.Bytecode

/-! ## Opcode-at-PC (thin decode wrapper for F3) -/

/-- Instruction at `pc`, if the byte is a known opcode. `none` at EOF or an
invalid byte. Push immediates are returned in the optional pair. -/
def opcodeAt (code : ByteArray) (pc : Nat) :
    Option (Operation .EVM × Option (UInt256 × Nat)) :=
  decode code (UInt256.ofNat pc)

/-- The `EQ` of `CALLER; PUSH20 SYSTEM_ADDR; EQ; JUMPI @read_requests`.
Not a JUMPDEST; named so F3 can talk about the caller gate without a magic
number. Same offset in both runtimes. -/
def gate_eq : Nat := 22

/-! ## Deposit runtime

Verified against `D_J depositRuntime ⟨0⟩` and against the assembly:

* `JUMPI @read_requests` pushes `0x011c` = 284.
* `JUMPI @revert` / the trailing `JUMPDEST; PUSH0; PUSH0; REVERT` is 624.
* `begin_loop` / `accum_loop` are consecutive JUMPDESTs around `PUSH0`
  (305 / 307); the `MAX_PER_BLOCK` clamp immediate is the byte at 304.
* `compute_excess` is 568; the system `TARGET_PER_BLOCK` immediate is 571.
-/

def depositJumpdestNats : List Nat :=
  [82, 88, 100, 127, 159, 284, 305, 307, 471, 489, 500, 560, 568, 578, 612, 624]

def depositJumpdests : Array UInt256 :=
  (depositJumpdestNats.map UInt256.ofNat).toArray

namespace Deposit

/-- `bump_excess:` — add `count - TARGET` into excess when `count > 8`. -/
def bump_excess : Nat := 82

/-- `compute_user_fee:` — fake-exponential entry (then the getter / write). -/
def compute_user_fee : Nat := 88

/-- Inner `fake_expo` loop JUMPDEST (from the shared include, not a
`main.eas` label). Candidate PC: 100. -/
def fake_expo_loop : Nat := 100

/-- Fall-through after the `fake_expo` loop. Candidate PC: 127. -/
def fake_expo_done : Nat := 127

/-- `handle_input:` — 184-byte paid append. -/
def handle_input : Nat := 159

/-- `read_requests:` — first system-path JUMPDEST. `PUSH2 0x011c` at the
gate. Confirmed. -/
def read_requests : Nat := 284

/-- `begin_loop:` — after the `MAX_PER_BLOCK` (64) clamp. -/
def begin_loop : Nat := 305

/-- `accum_loop:` — FIFO drain iteration. Immediately after `PUSH0`. -/
def accum_loop : Nat := 307

/-- `update_head:` — exit the drain loop, advance `QUEUE_HEAD`. -/
def update_head : Nat := 471

/-- `reset_queue:` — full drain zeroes HEAD and TAIL. -/
def reset_queue : Nat := 489

/-- `update_excess:` — system fee-accumulator / inhibitor dispatch. -/
def update_excess : Nat := 500

/-- `zero_excess:` — inhibited+empty and under-target fold to 0. -/
def zero_excess : Nat := 560

/-- `compute_excess:` — `max(0, excess+count-TARGET)` taken-branch. -/
def compute_excess : Nat := 568

/-- `set_inhibitor:` — nonempty system calldata stores `INHIBITOR`. -/
def set_inhibitor : Nat := 578

/-- `store_excess:` — `SSTORE` slot 0, clear count, `RETURN` records. -/
def store_excess : Nat := 612

/-- `revert:` — last JUMPDEST; `JUMPDEST; PUSH0; PUSH0; REVERT`. -/
def revert : Nat := 624

end Deposit

theorem deposit_D_J : D_J depositRuntime ⟨0⟩ = depositJumpdests := by
  native_decide

theorem depositJumpdests_toList :
    depositJumpdests.toList = depositJumpdestNats.map UInt256.ofNat :=
  List.toList_toArray

theorem mem_deposit_D_J_iff {pc : UInt256} :
    pc ∈ D_J depositRuntime ⟨0⟩ ↔ pc ∈ depositJumpdests := by
  rw [deposit_D_J]

theorem mem_depositJumpdests_iff {n : Nat} :
    UInt256.ofNat n ∈ depositJumpdests ↔
      ∃ k, k ∈ depositJumpdestNats ∧ UInt256.ofNat k = UInt256.ofNat n := by
  simp [depositJumpdests, List.mem_toArray, List.mem_map]

theorem mem_depositJumpdests_of_mem_nats {n : Nat}
    (h : n ∈ depositJumpdestNats) :
    UInt256.ofNat n ∈ depositJumpdests :=
  mem_depositJumpdests_iff.mpr ⟨n, h, rfl⟩

theorem mem_deposit_D_J_of_mem_nats {n : Nat}
    (h : n ∈ depositJumpdestNats) :
    UInt256.ofNat n ∈ D_J depositRuntime ⟨0⟩ :=
  mem_deposit_D_J_iff.mpr (mem_depositJumpdests_of_mem_nats h)

theorem deposit_named_in_nats :
    Deposit.bump_excess ∈ depositJumpdestNats ∧
    Deposit.compute_user_fee ∈ depositJumpdestNats ∧
    Deposit.fake_expo_loop ∈ depositJumpdestNats ∧
    Deposit.fake_expo_done ∈ depositJumpdestNats ∧
    Deposit.handle_input ∈ depositJumpdestNats ∧
    Deposit.read_requests ∈ depositJumpdestNats ∧
    Deposit.begin_loop ∈ depositJumpdestNats ∧
    Deposit.accum_loop ∈ depositJumpdestNats ∧
    Deposit.update_head ∈ depositJumpdestNats ∧
    Deposit.reset_queue ∈ depositJumpdestNats ∧
    Deposit.update_excess ∈ depositJumpdestNats ∧
    Deposit.zero_excess ∈ depositJumpdestNats ∧
    Deposit.compute_excess ∈ depositJumpdestNats ∧
    Deposit.set_inhibitor ∈ depositJumpdestNats ∧
    Deposit.store_excess ∈ depositJumpdestNats ∧
    Deposit.revert ∈ depositJumpdestNats := by
  decide

theorem deposit_bump_excess_mem :
    UInt256.ofNat Deposit.bump_excess ∈ D_J depositRuntime ⟨0⟩ :=
  mem_deposit_D_J_of_mem_nats (by decide)

theorem deposit_compute_user_fee_mem :
    UInt256.ofNat Deposit.compute_user_fee ∈ D_J depositRuntime ⟨0⟩ :=
  mem_deposit_D_J_of_mem_nats (by decide)

theorem deposit_fake_expo_loop_mem :
    UInt256.ofNat Deposit.fake_expo_loop ∈ D_J depositRuntime ⟨0⟩ :=
  mem_deposit_D_J_of_mem_nats (by decide)

theorem deposit_fake_expo_done_mem :
    UInt256.ofNat Deposit.fake_expo_done ∈ D_J depositRuntime ⟨0⟩ :=
  mem_deposit_D_J_of_mem_nats (by decide)

theorem deposit_handle_input_mem :
    UInt256.ofNat Deposit.handle_input ∈ D_J depositRuntime ⟨0⟩ :=
  mem_deposit_D_J_of_mem_nats (by decide)

theorem deposit_read_requests_mem :
    UInt256.ofNat Deposit.read_requests ∈ D_J depositRuntime ⟨0⟩ :=
  mem_deposit_D_J_of_mem_nats (by decide)

theorem deposit_begin_loop_mem :
    UInt256.ofNat Deposit.begin_loop ∈ D_J depositRuntime ⟨0⟩ :=
  mem_deposit_D_J_of_mem_nats (by decide)

theorem deposit_accum_loop_mem :
    UInt256.ofNat Deposit.accum_loop ∈ D_J depositRuntime ⟨0⟩ :=
  mem_deposit_D_J_of_mem_nats (by decide)

theorem deposit_update_head_mem :
    UInt256.ofNat Deposit.update_head ∈ D_J depositRuntime ⟨0⟩ :=
  mem_deposit_D_J_of_mem_nats (by decide)

theorem deposit_reset_queue_mem :
    UInt256.ofNat Deposit.reset_queue ∈ D_J depositRuntime ⟨0⟩ :=
  mem_deposit_D_J_of_mem_nats (by decide)

theorem deposit_update_excess_mem :
    UInt256.ofNat Deposit.update_excess ∈ D_J depositRuntime ⟨0⟩ :=
  mem_deposit_D_J_of_mem_nats (by decide)

theorem deposit_zero_excess_mem :
    UInt256.ofNat Deposit.zero_excess ∈ D_J depositRuntime ⟨0⟩ :=
  mem_deposit_D_J_of_mem_nats (by decide)

theorem deposit_compute_excess_mem :
    UInt256.ofNat Deposit.compute_excess ∈ D_J depositRuntime ⟨0⟩ :=
  mem_deposit_D_J_of_mem_nats (by decide)

theorem deposit_set_inhibitor_mem :
    UInt256.ofNat Deposit.set_inhibitor ∈ D_J depositRuntime ⟨0⟩ :=
  mem_deposit_D_J_of_mem_nats (by decide)

theorem deposit_store_excess_mem :
    UInt256.ofNat Deposit.store_excess ∈ D_J depositRuntime ⟨0⟩ :=
  mem_deposit_D_J_of_mem_nats (by decide)

theorem deposit_revert_mem :
    UInt256.ofNat Deposit.revert ∈ D_J depositRuntime ⟨0⟩ :=
  mem_deposit_D_J_of_mem_nats (by decide)

/-! ## Exit runtime

Verified against `D_J exitRuntime ⟨0⟩` and against the assembly:

* `JUMPI @read_requests` pushes `0xe1` = 225.
* Trailing `revert` JUMPDEST is 454.
* `begin_loop` / `accum_loop` are 245 / 247; `MAX_PER_BLOCK` immediate at 244.
* `compute_excess` is 398; the system `TARGET_PER_BLOCK` immediate is 401.
-/

def exitJumpdestNats : List Nat :=
  [81, 87, 99, 126, 158, 225, 245, 247, 301, 319, 330, 390, 398, 408, 442, 454]

def exitJumpdests : Array UInt256 :=
  (exitJumpdestNats.map UInt256.ofNat).toArray

namespace Exit

def bump_excess : Nat := 81
def compute_user_fee : Nat := 87

/-- Inner `fake_expo` loop JUMPDEST. Candidate PC: 99. -/
def fake_expo_loop : Nat := 99

/-- Fall-through after the `fake_expo` loop. Candidate PC: 126. -/
def fake_expo_done : Nat := 126

def handle_input : Nat := 158

/-- First system-path JUMPDEST. `PUSH1 0xe1` at the gate. Confirmed. -/
def read_requests : Nat := 225

def begin_loop : Nat := 245
def accum_loop : Nat := 247
def update_head : Nat := 301
def reset_queue : Nat := 319
def update_excess : Nat := 330
def zero_excess : Nat := 390
def compute_excess : Nat := 398
def set_inhibitor : Nat := 408
def store_excess : Nat := 442

/-- Last JUMPDEST; `JUMPDEST; PUSH0; PUSH0; REVERT`. -/
def revert : Nat := 454

end Exit

theorem exit_D_J : D_J exitRuntime ⟨0⟩ = exitJumpdests := by
  native_decide

theorem exitJumpdests_toList :
    exitJumpdests.toList = exitJumpdestNats.map UInt256.ofNat :=
  List.toList_toArray

theorem mem_exit_D_J_iff {pc : UInt256} :
    pc ∈ D_J exitRuntime ⟨0⟩ ↔ pc ∈ exitJumpdests := by
  rw [exit_D_J]

theorem mem_exitJumpdests_iff {n : Nat} :
    UInt256.ofNat n ∈ exitJumpdests ↔
      ∃ k, k ∈ exitJumpdestNats ∧ UInt256.ofNat k = UInt256.ofNat n := by
  simp [exitJumpdests, List.mem_toArray, List.mem_map]

theorem mem_exitJumpdests_of_mem_nats {n : Nat}
    (h : n ∈ exitJumpdestNats) :
    UInt256.ofNat n ∈ exitJumpdests :=
  mem_exitJumpdests_iff.mpr ⟨n, h, rfl⟩

theorem mem_exit_D_J_of_mem_nats {n : Nat}
    (h : n ∈ exitJumpdestNats) :
    UInt256.ofNat n ∈ D_J exitRuntime ⟨0⟩ :=
  mem_exit_D_J_iff.mpr (mem_exitJumpdests_of_mem_nats h)

theorem exit_named_in_nats :
    Exit.bump_excess ∈ exitJumpdestNats ∧
    Exit.compute_user_fee ∈ exitJumpdestNats ∧
    Exit.fake_expo_loop ∈ exitJumpdestNats ∧
    Exit.fake_expo_done ∈ exitJumpdestNats ∧
    Exit.handle_input ∈ exitJumpdestNats ∧
    Exit.read_requests ∈ exitJumpdestNats ∧
    Exit.begin_loop ∈ exitJumpdestNats ∧
    Exit.accum_loop ∈ exitJumpdestNats ∧
    Exit.update_head ∈ exitJumpdestNats ∧
    Exit.reset_queue ∈ exitJumpdestNats ∧
    Exit.update_excess ∈ exitJumpdestNats ∧
    Exit.zero_excess ∈ exitJumpdestNats ∧
    Exit.compute_excess ∈ exitJumpdestNats ∧
    Exit.set_inhibitor ∈ exitJumpdestNats ∧
    Exit.store_excess ∈ exitJumpdestNats ∧
    Exit.revert ∈ exitJumpdestNats := by
  decide

theorem exit_bump_excess_mem :
    UInt256.ofNat Exit.bump_excess ∈ D_J exitRuntime ⟨0⟩ :=
  mem_exit_D_J_of_mem_nats (by decide)

theorem exit_compute_user_fee_mem :
    UInt256.ofNat Exit.compute_user_fee ∈ D_J exitRuntime ⟨0⟩ :=
  mem_exit_D_J_of_mem_nats (by decide)

theorem exit_fake_expo_loop_mem :
    UInt256.ofNat Exit.fake_expo_loop ∈ D_J exitRuntime ⟨0⟩ :=
  mem_exit_D_J_of_mem_nats (by decide)

theorem exit_fake_expo_done_mem :
    UInt256.ofNat Exit.fake_expo_done ∈ D_J exitRuntime ⟨0⟩ :=
  mem_exit_D_J_of_mem_nats (by decide)

theorem exit_handle_input_mem :
    UInt256.ofNat Exit.handle_input ∈ D_J exitRuntime ⟨0⟩ :=
  mem_exit_D_J_of_mem_nats (by decide)

theorem exit_read_requests_mem :
    UInt256.ofNat Exit.read_requests ∈ D_J exitRuntime ⟨0⟩ :=
  mem_exit_D_J_of_mem_nats (by decide)

theorem exit_begin_loop_mem :
    UInt256.ofNat Exit.begin_loop ∈ D_J exitRuntime ⟨0⟩ :=
  mem_exit_D_J_of_mem_nats (by decide)

theorem exit_accum_loop_mem :
    UInt256.ofNat Exit.accum_loop ∈ D_J exitRuntime ⟨0⟩ :=
  mem_exit_D_J_of_mem_nats (by decide)

theorem exit_update_head_mem :
    UInt256.ofNat Exit.update_head ∈ D_J exitRuntime ⟨0⟩ :=
  mem_exit_D_J_of_mem_nats (by decide)

theorem exit_reset_queue_mem :
    UInt256.ofNat Exit.reset_queue ∈ D_J exitRuntime ⟨0⟩ :=
  mem_exit_D_J_of_mem_nats (by decide)

theorem exit_update_excess_mem :
    UInt256.ofNat Exit.update_excess ∈ D_J exitRuntime ⟨0⟩ :=
  mem_exit_D_J_of_mem_nats (by decide)

theorem exit_zero_excess_mem :
    UInt256.ofNat Exit.zero_excess ∈ D_J exitRuntime ⟨0⟩ :=
  mem_exit_D_J_of_mem_nats (by decide)

theorem exit_compute_excess_mem :
    UInt256.ofNat Exit.compute_excess ∈ D_J exitRuntime ⟨0⟩ :=
  mem_exit_D_J_of_mem_nats (by decide)

theorem exit_set_inhibitor_mem :
    UInt256.ofNat Exit.set_inhibitor ∈ D_J exitRuntime ⟨0⟩ :=
  mem_exit_D_J_of_mem_nats (by decide)

theorem exit_store_excess_mem :
    UInt256.ofNat Exit.store_excess ∈ D_J exitRuntime ⟨0⟩ :=
  mem_exit_D_J_of_mem_nats (by decide)

theorem exit_revert_mem :
    UInt256.ofNat Exit.revert ∈ D_J exitRuntime ⟨0⟩ :=
  mem_exit_D_J_of_mem_nats (by decide)

/-! ## Init bytecode

Constructor preambles contain no JUMPDEST. `D_J` still walks the copied
runtime, so every runtime JUMPDEST appears shifted by the preamble length
(`PUSH2 size; DUP1; PUSH1 offset; PUSH0; CODECOPY; PUSH0; RETURN` = 10
bytes for deposits; exit stores `INHIBITOR` first, 45 bytes).
-/

def depositInitPreamble : Nat := 10
def exitInitPreamble : Nat := 45

def depositInitJumpdestNats : List Nat :=
  depositJumpdestNats.map (· + depositInitPreamble)

def exitInitJumpdestNats : List Nat :=
  exitJumpdestNats.map (· + exitInitPreamble)

def depositInitJumpdests : Array UInt256 :=
  (depositInitJumpdestNats.map UInt256.ofNat).toArray

def exitInitJumpdests : Array UInt256 :=
  (exitInitJumpdestNats.map UInt256.ofNat).toArray

theorem depositInit_D_J : D_J depositInit ⟨0⟩ = depositInitJumpdests := by
  native_decide

theorem exitInit_D_J : D_J exitInit ⟨0⟩ = exitInitJumpdests := by
  native_decide

end Eip8282.Audit.Jumpdests

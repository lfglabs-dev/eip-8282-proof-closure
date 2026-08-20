/-!
Concrete `D_J` tables for the pinned EIP-8282 runtimes (and init, as a
finite bonus for later ctor work).

`EvmYul.EVM.D_J_aux` is `partial`, so the kernel cannot reduce a jumpdest
scan. This module discharges the four ground equalities with
`native_decide` (the campaign exception) and then exposes **kernel**
membership lemmas over the resulting `List Nat` tables.

**Later modules must rewrite with `deposit_D_J` / `exit_D_J` (and the
init variants) instead of unfolding `D_J` or `D_J_aux`.** Reducing the
scanner again is not a proof; it re-enters the `partial` function.
-/

import EvmYul.EVM.Semantics
import Eip8282.Audit.Bytecode

namespace Eip8282.Audit.Jumpdests

open EvmYul
open EvmYul.EVM
open Eip8282.Audit.Bytecode

/-! ## Tables

PCs are collected by `D_J` (JUMPDEST = `0x5b`; PUSH1..PUSH32 skip their
immediates). The lists below are the expected images; the theorems
`deposit_D_J` etc. are what make them equal to `EvmYul.EVM.D_J`.
-/

/-- JUMPDEST PCs of `depositRuntime` (628 bytes). -/
def depositJumpdestNats : List Nat :=
  [82, 88, 100, 127, 159, 284, 305, 307, 471, 489, 500, 560, 568, 578, 612, 624]

/-- JUMPDEST PCs of `exitRuntime` (458 bytes). -/
def exitJumpdestNats : List Nat :=
  [81, 87, 99, 126, 158, 225, 245, 247, 301, 319, 330, 390, 398, 408, 442, 454]

/-- JUMPDEST PCs of `depositInit` (638 bytes). Runtime PCs plus the 10-byte
codecopy wrapper. -/
def depositInitJumpdestNats : List Nat :=
  [92, 98, 110, 137, 169, 294, 315, 317, 481, 499, 510, 570, 578, 588, 622, 634]

/-- JUMPDEST PCs of `exitInit` (503 bytes). Runtime PCs plus the 45-byte
inhibitor-store + codecopy wrapper. -/
def exitInitJumpdestNats : List Nat :=
  [126, 132, 144, 171, 203, 270, 290, 292, 346, 364, 375, 435, 443, 453, 487, 499]

/-- `Array UInt256` form matching `D_J`'s return type. -/
def jumpdestsOf (ns : List Nat) : Array UInt256 :=
  (ns.map UInt256.ofNat).toArray

def depositJumpdests : Array UInt256 := jumpdestsOf depositJumpdestNats
def exitJumpdests : Array UInt256 := jumpdestsOf exitJumpdestNats
def depositInitJumpdests : Array UInt256 := jumpdestsOf depositInitJumpdestNats
def exitInitJumpdests : Array UInt256 := jumpdestsOf exitInitJumpdestNats

@[simp] theorem toList_jumpdestsOf (ns : List Nat) :
    (jumpdestsOf ns).toList = ns.map UInt256.ofNat :=
  Array.toList_toArray

/-! ## `D_J` equalities (`native_decide` — campaign exception)

These are the only `native_decide` uses in this file. Do not add `Ξ`
traces here.
-/

/--
`D_J depositRuntime ⟨0⟩` is the finite table `depositJumpdests`.

Later modules: `rw [deposit_D_J]` or `simp [deposit_D_J]`. Do not reduce
`D_J_aux`.
-/
theorem deposit_D_J : D_J depositRuntime ⟨0⟩ = depositJumpdests := by
  native_decide

/--
`D_J exitRuntime ⟨0⟩` is the finite table `exitJumpdests`.

Later modules: `rw [exit_D_J]` or `simp [exit_D_J]`. Do not reduce
`D_J_aux`.
-/
theorem exit_D_J : D_J exitRuntime ⟨0⟩ = exitJumpdests := by
  native_decide

theorem depositInit_D_J : D_J depositInit ⟨0⟩ = depositInitJumpdests := by
  native_decide

theorem exitInit_D_J : D_J exitInit ⟨0⟩ = exitInitJumpdests := by
  native_decide

/-! ## Kernel lemmas over the `List Nat` tables

None of these re-reduce `D_J_aux`. They reason about `UInt256.ofNat` and
the concrete PC lists.
-/

private theorem toNat_ofNat (n : Nat) :
    (UInt256.ofNat n).toNat = n % UInt256.size :=
  rfl

private theorem uint256_ext {a b : UInt256} (h : a.toNat = b.toNat) : a = b := by
  cases a
  cases b
  simp [UInt256.toNat] at h
  exact congrArg UInt256.mk (Fin.ext h)

private theorem ofNat_eq_iff (a b : Nat) :
    UInt256.ofNat a = UInt256.ofNat b ↔ a % UInt256.size = b % UInt256.size := by
  constructor
  · intro h
    simpa [toNat_ofNat] using congrArg UInt256.toNat h
  · intro h
    exact uint256_ext (by simpa [toNat_ofNat] using h)

private theorem ofNat_mod (n : Nat) :
    UInt256.ofNat (n % UInt256.size) = UInt256.ofNat n :=
  (ofNat_eq_iff _ _).2 (Nat.mod_mod n UInt256.size)

private theorem mem_map_ofNat {ns : List Nat}
    (hbound : ∀ n ∈ ns, n < UInt256.size) (pc : Nat) :
    UInt256.ofNat pc ∈ ns.map UInt256.ofNat ↔ pc % UInt256.size ∈ ns := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨n, hn, heq⟩
    have hmod : pc % UInt256.size = n % UInt256.size := (ofNat_eq_iff _ _).1 heq
    have : n % UInt256.size = n := Nat.mod_eq_of_lt (hbound n hn)
    rwa [this] at hmod
  · intro h
    exact ⟨pc % UInt256.size, h, ofNat_mod pc⟩

private theorem mem_jumpdestsOf {ns : List Nat}
    (hbound : ∀ n ∈ ns, n < UInt256.size) (pc : Nat) :
    UInt256.ofNat pc ∈ jumpdestsOf ns ↔ pc % UInt256.size ∈ ns := by
  rw [Array.mem_def, toList_jumpdestsOf]
  exact mem_map_ofNat hbound pc

private theorem mem_jumpdestsOf_of_lt {ns : List Nat}
    (hbound : ∀ n ∈ ns, n < UInt256.size) {pc : Nat} (hpc : pc < UInt256.size) :
    UInt256.ofNat pc ∈ jumpdestsOf ns ↔ pc ∈ ns := by
  rw [mem_jumpdestsOf hbound, Nat.mod_eq_of_lt hpc]

private theorem depositJumpdestNats_lt :
    ∀ n ∈ depositJumpdestNats, n < UInt256.size := by
  decide

private theorem exitJumpdestNats_lt :
    ∀ n ∈ exitJumpdestNats, n < UInt256.size := by
  decide

private theorem depositInitJumpdestNats_lt :
    ∀ n ∈ depositInitJumpdestNats, n < UInt256.size := by
  decide

private theorem exitInitJumpdestNats_lt :
    ∀ n ∈ exitInitJumpdestNats, n < UInt256.size := by
  decide

/--
Membership in the deposit `D_J` table, as a statement about the `List Nat`
PCs. The optional bound is discharged by `decide` at concrete PCs; it is
needed because `UInt256.ofNat` is modulo `2^256`.
-/
theorem deposit_jumpdest_mem (pc : Nat) (hpc : pc < UInt256.size := by decide) :
    (UInt256.ofNat pc ∈ depositJumpdests) ↔ pc ∈ depositJumpdestNats :=
  mem_jumpdestsOf_of_lt depositJumpdestNats_lt hpc

theorem exit_jumpdest_mem (pc : Nat) (hpc : pc < UInt256.size := by decide) :
    (UInt256.ofNat pc ∈ exitJumpdests) ↔ pc ∈ exitJumpdestNats :=
  mem_jumpdestsOf_of_lt exitJumpdestNats_lt hpc

theorem depositInit_jumpdest_mem (pc : Nat) (hpc : pc < UInt256.size := by decide) :
    (UInt256.ofNat pc ∈ depositInitJumpdests) ↔ pc ∈ depositInitJumpdestNats :=
  mem_jumpdestsOf_of_lt depositInitJumpdestNats_lt hpc

theorem exitInit_jumpdest_mem (pc : Nat) (hpc : pc < UInt256.size := by decide) :
    (UInt256.ofNat pc ∈ exitInitJumpdests) ↔ pc ∈ exitInitJumpdestNats :=
  mem_jumpdestsOf_of_lt exitInitJumpdestNats_lt hpc

/-- Unbounded form: `ofNat` wraps, so membership is `pc % 2^256`. -/
theorem deposit_jumpdest_mem_mod (pc : Nat) :
    (UInt256.ofNat pc ∈ depositJumpdests) ↔
      pc % UInt256.size ∈ depositJumpdestNats :=
  mem_jumpdestsOf depositJumpdestNats_lt pc

theorem exit_jumpdest_mem_mod (pc : Nat) :
    (UInt256.ofNat pc ∈ exitJumpdests) ↔
      pc % UInt256.size ∈ exitJumpdestNats :=
  mem_jumpdestsOf exitJumpdestNats_lt pc

/-- Rewrite `D_J` then consult the Nat table. Does not reduce `D_J_aux`. -/
theorem deposit_D_J_mem (pc : Nat) (hpc : pc < UInt256.size := by decide) :
    (UInt256.ofNat pc ∈ D_J depositRuntime ⟨0⟩) ↔ pc ∈ depositJumpdestNats := by
  rw [deposit_D_J]
  exact deposit_jumpdest_mem pc hpc

theorem exit_D_J_mem (pc : Nat) (hpc : pc < UInt256.size := by decide) :
    (UInt256.ofNat pc ∈ D_J exitRuntime ⟨0⟩) ↔ pc ∈ exitJumpdestNats := by
  rw [exit_D_J]
  exact exit_jumpdest_mem pc hpc

/-! ## CFG site PCs

Labels from `pinned/sys-asm/builder_{deposits,exits}/main.eas`. The two
`fake_expo_*` sites are JUMPDESTs inside the included fake-exponential
loop (not labelled in `main.eas`).
-/

def deposit_bump_excess : Nat := 82
def deposit_compute_user_fee : Nat := 88
def deposit_fake_expo_loop : Nat := 100
def deposit_fake_expo_done : Nat := 127
def deposit_handle_input : Nat := 159
def deposit_read_requests : Nat := 284
def deposit_begin_loop : Nat := 305
def deposit_accum_loop : Nat := 307
def deposit_update_head : Nat := 471
def deposit_reset_queue : Nat := 489
def deposit_update_excess : Nat := 500
def deposit_zero_excess : Nat := 560
def deposit_compute_excess : Nat := 568
def deposit_set_inhibitor : Nat := 578
def deposit_store_excess : Nat := 612
def deposit_revert : Nat := 624

def exit_bump_excess : Nat := 81
def exit_compute_user_fee : Nat := 87
def exit_fake_expo_loop : Nat := 99
def exit_fake_expo_done : Nat := 126
def exit_handle_input : Nat := 158
def exit_read_requests : Nat := 225
def exit_begin_loop : Nat := 245
def exit_accum_loop : Nat := 247
def exit_update_head : Nat := 301
def exit_reset_queue : Nat := 319
def exit_update_excess : Nat := 330
def exit_zero_excess : Nat := 390
def exit_compute_excess : Nat := 398
def exit_set_inhibitor : Nat := 408
def exit_store_excess : Nat := 442
def exit_revert : Nat := 454

/-- Init = runtime PC + constructor prefix (`depositInit` 10 bytes, `exitInit` 45). -/
def depositInitOffset : Nat := 10
def exitInitOffset : Nat := 45

theorem depositInitJumpdestNats_shift :
    depositInitJumpdestNats =
      depositJumpdestNats.map (· + depositInitOffset) := rfl

theorem exitInitJumpdestNats_shift :
    exitInitJumpdestNats =
      exitJumpdestNats.map (· + exitInitOffset) := rfl

theorem deposit_bump_excess_mem : deposit_bump_excess ∈ depositJumpdestNats := by decide
theorem deposit_compute_user_fee_mem : deposit_compute_user_fee ∈ depositJumpdestNats := by decide
theorem deposit_fake_expo_loop_mem : deposit_fake_expo_loop ∈ depositJumpdestNats := by decide
theorem deposit_fake_expo_done_mem : deposit_fake_expo_done ∈ depositJumpdestNats := by decide
theorem deposit_handle_input_mem : deposit_handle_input ∈ depositJumpdestNats := by decide
theorem deposit_read_requests_mem : deposit_read_requests ∈ depositJumpdestNats := by decide
theorem deposit_begin_loop_mem : deposit_begin_loop ∈ depositJumpdestNats := by decide
theorem deposit_accum_loop_mem : deposit_accum_loop ∈ depositJumpdestNats := by decide
theorem deposit_update_head_mem : deposit_update_head ∈ depositJumpdestNats := by decide
theorem deposit_reset_queue_mem : deposit_reset_queue ∈ depositJumpdestNats := by decide
theorem deposit_update_excess_mem : deposit_update_excess ∈ depositJumpdestNats := by decide
theorem deposit_zero_excess_mem : deposit_zero_excess ∈ depositJumpdestNats := by decide
theorem deposit_compute_excess_mem : deposit_compute_excess ∈ depositJumpdestNats := by decide
theorem deposit_set_inhibitor_mem : deposit_set_inhibitor ∈ depositJumpdestNats := by decide
theorem deposit_store_excess_mem : deposit_store_excess ∈ depositJumpdestNats := by decide
theorem deposit_revert_mem : deposit_revert ∈ depositJumpdestNats := by decide

theorem exit_bump_excess_mem : exit_bump_excess ∈ exitJumpdestNats := by decide
theorem exit_compute_user_fee_mem : exit_compute_user_fee ∈ exitJumpdestNats := by decide
theorem exit_fake_expo_loop_mem : exit_fake_expo_loop ∈ exitJumpdestNats := by decide
theorem exit_fake_expo_done_mem : exit_fake_expo_done ∈ exitJumpdestNats := by decide
theorem exit_handle_input_mem : exit_handle_input ∈ exitJumpdestNats := by decide
theorem exit_read_requests_mem : exit_read_requests ∈ exitJumpdestNats := by decide
theorem exit_begin_loop_mem : exit_begin_loop ∈ exitJumpdestNats := by decide
theorem exit_accum_loop_mem : exit_accum_loop ∈ exitJumpdestNats := by decide
theorem exit_update_head_mem : exit_update_head ∈ exitJumpdestNats := by decide
theorem exit_reset_queue_mem : exit_reset_queue ∈ exitJumpdestNats := by decide
theorem exit_update_excess_mem : exit_update_excess ∈ exitJumpdestNats := by decide
theorem exit_zero_excess_mem : exit_zero_excess ∈ exitJumpdestNats := by decide
theorem exit_compute_excess_mem : exit_compute_excess ∈ exitJumpdestNats := by decide
theorem exit_set_inhibitor_mem : exit_set_inhibitor ∈ exitJumpdestNats := by decide
theorem exit_store_excess_mem : exit_store_excess ∈ exitJumpdestNats := by decide
theorem exit_revert_mem : exit_revert ∈ exitJumpdestNats := by decide

/-- Array-level membership for a CFG site, via the Nat table (no `D_J_aux`). -/
theorem deposit_read_requests_in_table :
    UInt256.ofNat deposit_read_requests ∈ depositJumpdests :=
  (deposit_jumpdest_mem _).2 deposit_read_requests_mem

theorem deposit_revert_in_table :
    UInt256.ofNat deposit_revert ∈ depositJumpdests :=
  (deposit_jumpdest_mem _).2 deposit_revert_mem

theorem deposit_accum_loop_in_table :
    UInt256.ofNat deposit_accum_loop ∈ depositJumpdests :=
  (deposit_jumpdest_mem _).2 deposit_accum_loop_mem

theorem exit_read_requests_in_table :
    UInt256.ofNat exit_read_requests ∈ exitJumpdests :=
  (exit_jumpdest_mem _).2 exit_read_requests_mem

theorem exit_revert_in_table :
    UInt256.ofNat exit_revert ∈ exitJumpdests :=
  (exit_jumpdest_mem _).2 exit_revert_mem

theorem exit_accum_loop_in_table :
    UInt256.ofNat exit_accum_loop ∈ exitJumpdests :=
  (exit_jumpdest_mem _).2 exit_accum_loop_mem

end Eip8282.Audit.Jumpdests

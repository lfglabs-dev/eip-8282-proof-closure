import EvmYul.EVM.Semantics
import Eip8282.Audit.Bytecode

/-!
Concrete `D_J` tables for the pinned EIP-8282 hexes.

`EvmYul.EVM.D_J_aux` is `partial`, so it is kernel-opaque. This module
defines a structurally recursive fuelled replica `scanJumpdests` (not
`partial`) and discharges `scanJumpdests c = D_J c ⟨0⟩` by `native_decide`
on the two runtime images (and the init images). Later modules should
rewrite with `deposit_D_J` / `exit_D_J` and use the `List Nat` membership
lemmas; they must not unfold `D_J_aux`.
-/

namespace Eip8282.Audit.Jumpdests

open EvmYul
open EvmYul.EVM
open Eip8282.Audit.Bytecode

/--
Fuelled replica of `D_J_aux`. Fuel is a remaining-byte bound (`c.size` at
the start). Each instruction consumes one unit of fuel and advances the
PC with `N`, the same `parseInstr` / `N` / `.JUMPDEST` step as `D_J_aux`.
Structurally recursive on `fuel`; kernel-reducible.
-/
def scanJumpdests.go (c : ByteArray) :
    Nat → UInt256 → Array UInt256 → Array UInt256
  | 0, _, result => result
  | fuel + 1, i, result =>
    match c.get? i.toNat >>= parseInstr with
    | none => result
    | some cᵢ =>
      scanJumpdests.go c fuel (N i cᵢ)
        (if cᵢ = .JUMPDEST then result.push i else result)

/-- JUMPDEST PCs of `c`, scanning from offset 0 with fuel `c.size`. -/
def scanJumpdests (c : ByteArray) : Array UInt256 :=
  scanJumpdests.go c c.size ⟨0⟩ #[]

/-! ## Pinned tables (PUSH-aware `0x5b` scan; equal to `D_J`) -/

def depositJumpdestNats : List Nat :=
  [82, 88, 100, 127, 159, 284, 305, 307, 471, 489, 500, 560, 568, 578, 612, 624]

def depositJumpdests : Array UInt256 :=
  (depositJumpdestNats.map UInt256.ofNat).toArray

def exitJumpdestNats : List Nat :=
  [81, 87, 99, 126, 158, 225, 245, 247, 301, 319, 330, 390, 398, 408, 442, 454]

def exitJumpdests : Array UInt256 :=
  (exitJumpdestNats.map UInt256.ofNat).toArray

def depositInitJumpdestNats : List Nat :=
  [92, 98, 110, 137, 169, 294, 315, 317, 481, 499, 510, 570, 578, 588, 622, 634]

def depositInitJumpdests : Array UInt256 :=
  (depositInitJumpdestNats.map UInt256.ofNat).toArray

def exitInitJumpdestNats : List Nat :=
  [126, 132, 144, 171, 203, 270, 290, 292, 346, 364, 375, 435, 443, 453, 487, 499]

def exitInitJumpdests : Array UInt256 :=
  (exitInitJumpdestNats.map UInt256.ofNat).toArray

theorem depositJumpdests_toList :
    depositJumpdests.toList = depositJumpdestNats.map UInt256.ofNat :=
  rfl

theorem exitJumpdests_toList :
    exitJumpdests.toList = exitJumpdestNats.map UInt256.ofNat :=
  rfl

theorem depositInitJumpdests_toList :
    depositInitJumpdests.toList = depositInitJumpdestNats.map UInt256.ofNat :=
  rfl

theorem exitInitJumpdests_toList :
    exitInitJumpdests.toList = exitInitJumpdestNats.map UInt256.ofNat :=
  rfl

theorem mem_depositJumpdests_of_mem_nats {pc : Nat}
    (h : pc ∈ depositJumpdestNats) :
    UInt256.ofNat pc ∈ depositJumpdests := by
  simpa [depositJumpdests] using List.mem_map_of_mem (f := UInt256.ofNat) h

theorem mem_exitJumpdests_of_mem_nats {pc : Nat}
    (h : pc ∈ exitJumpdestNats) :
    UInt256.ofNat pc ∈ exitJumpdests := by
  simpa [exitJumpdests] using List.mem_map_of_mem (f := UInt256.ofNat) h

theorem mem_depositInitJumpdests_of_mem_nats {pc : Nat}
    (h : pc ∈ depositInitJumpdestNats) :
    UInt256.ofNat pc ∈ depositInitJumpdests := by
  simpa [depositInitJumpdests] using List.mem_map_of_mem (f := UInt256.ofNat) h

theorem mem_exitInitJumpdests_of_mem_nats {pc : Nat}
    (h : pc ∈ exitInitJumpdestNats) :
    UInt256.ofNat pc ∈ exitInitJumpdests := by
  simpa [exitInitJumpdests] using List.mem_map_of_mem (f := UInt256.ofNat) h

/-! ## `scanJumpdests` agrees with `D_J` on the pinned hexes.

`D_J_aux` is `partial`, so this equality is discharged by `native_decide`
(allowed for F1 finite tables). The fuelled scanner itself is a `def`.
-/

theorem scan_eq_D_J_deposit :
    scanJumpdests depositRuntime = D_J depositRuntime ⟨0⟩ := by
  native_decide

theorem scan_eq_D_J_exit :
    scanJumpdests exitRuntime = D_J exitRuntime ⟨0⟩ := by
  native_decide

theorem scan_eq_D_J_depositInit :
    scanJumpdests depositInit = D_J depositInit ⟨0⟩ := by
  native_decide

theorem scan_eq_D_J_exitInit :
    scanJumpdests exitInit = D_J exitInit ⟨0⟩ := by
  native_decide

theorem scan_eq_depositJumpdests :
    scanJumpdests depositRuntime = depositJumpdests := by
  native_decide

theorem scan_eq_exitJumpdests :
    scanJumpdests exitRuntime = exitJumpdests := by
  native_decide

theorem scan_eq_depositInitJumpdests :
    scanJumpdests depositInit = depositInitJumpdests := by
  native_decide

theorem scan_eq_exitInitJumpdests :
    scanJumpdests exitInit = exitInitJumpdests := by
  native_decide

@[simp] theorem deposit_D_J :
    D_J depositRuntime ⟨0⟩ = depositJumpdests :=
  scan_eq_D_J_deposit.symm.trans scan_eq_depositJumpdests

@[simp] theorem exit_D_J :
    D_J exitRuntime ⟨0⟩ = exitJumpdests :=
  scan_eq_D_J_exit.symm.trans scan_eq_exitJumpdests

@[simp] theorem depositInit_D_J :
    D_J depositInit ⟨0⟩ = depositInitJumpdests :=
  scan_eq_D_J_depositInit.symm.trans scan_eq_depositInitJumpdests

@[simp] theorem exitInit_D_J :
    D_J exitInit ⟨0⟩ = exitInitJumpdests :=
  scan_eq_D_J_exitInit.symm.trans scan_eq_exitInitJumpdests

/-- Later modules: a Nat from the pinned table is a `D_J` member. -/
theorem mem_D_J_deposit {pc : Nat} (h : pc ∈ depositJumpdestNats) :
    UInt256.ofNat pc ∈ D_J depositRuntime ⟨0⟩ := by
  rw [deposit_D_J]
  exact mem_depositJumpdests_of_mem_nats h

theorem mem_D_J_exit {pc : Nat} (h : pc ∈ exitJumpdestNats) :
    UInt256.ofNat pc ∈ D_J exitRuntime ⟨0⟩ := by
  rw [exit_D_J]
  exact mem_exitJumpdests_of_mem_nats h

theorem mem_D_J_depositInit {pc : Nat} (h : pc ∈ depositInitJumpdestNats) :
    UInt256.ofNat pc ∈ D_J depositInit ⟨0⟩ := by
  rw [depositInit_D_J]
  exact mem_depositInitJumpdests_of_mem_nats h

theorem mem_D_J_exitInit {pc : Nat} (h : pc ∈ exitInitJumpdestNats) :
    UInt256.ofNat pc ∈ D_J exitInit ⟨0⟩ := by
  rw [exitInit_D_J]
  exact mem_exitInitJumpdests_of_mem_nats h

/-! ## Concrete `List Nat` membership, so CFG lemmas need not mention `D_J`. -/

@[simp] theorem mem_depositJumpdestNats_82 : 82 ∈ depositJumpdestNats := by decide
@[simp] theorem mem_depositJumpdestNats_88 : 88 ∈ depositJumpdestNats := by decide
@[simp] theorem mem_depositJumpdestNats_100 : 100 ∈ depositJumpdestNats := by decide
@[simp] theorem mem_depositJumpdestNats_127 : 127 ∈ depositJumpdestNats := by decide
@[simp] theorem mem_depositJumpdestNats_159 : 159 ∈ depositJumpdestNats := by decide
@[simp] theorem mem_depositJumpdestNats_284 : 284 ∈ depositJumpdestNats := by decide
@[simp] theorem mem_depositJumpdestNats_305 : 305 ∈ depositJumpdestNats := by decide
@[simp] theorem mem_depositJumpdestNats_307 : 307 ∈ depositJumpdestNats := by decide
@[simp] theorem mem_depositJumpdestNats_471 : 471 ∈ depositJumpdestNats := by decide
@[simp] theorem mem_depositJumpdestNats_489 : 489 ∈ depositJumpdestNats := by decide
@[simp] theorem mem_depositJumpdestNats_500 : 500 ∈ depositJumpdestNats := by decide
@[simp] theorem mem_depositJumpdestNats_560 : 560 ∈ depositJumpdestNats := by decide
@[simp] theorem mem_depositJumpdestNats_568 : 568 ∈ depositJumpdestNats := by decide
@[simp] theorem mem_depositJumpdestNats_578 : 578 ∈ depositJumpdestNats := by decide
@[simp] theorem mem_depositJumpdestNats_612 : 612 ∈ depositJumpdestNats := by decide
@[simp] theorem mem_depositJumpdestNats_624 : 624 ∈ depositJumpdestNats := by decide

@[simp] theorem mem_exitJumpdestNats_81 : 81 ∈ exitJumpdestNats := by decide
@[simp] theorem mem_exitJumpdestNats_87 : 87 ∈ exitJumpdestNats := by decide
@[simp] theorem mem_exitJumpdestNats_99 : 99 ∈ exitJumpdestNats := by decide
@[simp] theorem mem_exitJumpdestNats_126 : 126 ∈ exitJumpdestNats := by decide
@[simp] theorem mem_exitJumpdestNats_158 : 158 ∈ exitJumpdestNats := by decide
@[simp] theorem mem_exitJumpdestNats_225 : 225 ∈ exitJumpdestNats := by decide
@[simp] theorem mem_exitJumpdestNats_245 : 245 ∈ exitJumpdestNats := by decide
@[simp] theorem mem_exitJumpdestNats_247 : 247 ∈ exitJumpdestNats := by decide
@[simp] theorem mem_exitJumpdestNats_301 : 301 ∈ exitJumpdestNats := by decide
@[simp] theorem mem_exitJumpdestNats_319 : 319 ∈ exitJumpdestNats := by decide
@[simp] theorem mem_exitJumpdestNats_330 : 330 ∈ exitJumpdestNats := by decide
@[simp] theorem mem_exitJumpdestNats_390 : 390 ∈ exitJumpdestNats := by decide
@[simp] theorem mem_exitJumpdestNats_398 : 398 ∈ exitJumpdestNats := by decide
@[simp] theorem mem_exitJumpdestNats_408 : 408 ∈ exitJumpdestNats := by decide
@[simp] theorem mem_exitJumpdestNats_442 : 442 ∈ exitJumpdestNats := by decide
@[simp] theorem mem_exitJumpdestNats_454 : 454 ∈ exitJumpdestNats := by decide

end Eip8282.Audit.Jumpdests

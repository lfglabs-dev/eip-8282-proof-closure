import Eip8282.Audit.Integrator.ReferenceMemoryView
import Eip8282.Audit.EntryReach.Words

/-! Actual pinned memory expansion and the source's rounded-capacity cost.
Physical store endpoints, not RETURN lengths, determine the high-water mark.
Trace producers must establish the operand bounds consumed here. -/
namespace Eip8282.Audit.Integrator.ReferenceMemoryCapacity
open EvmYul Eip8282.Audit.EntryReach
set_option autoImplicit false

def Coherent (μ : MachineState) : Prop := μ.memory.size ≤ 32*μ.activeWords.toNat

theorem expansion_bounds (aw off len : Nat) :
    aw ≤ MachineState.M aw off len ∧
    (0 < len → off+len ≤ 32*MachineState.M aw off len) := by
  cases len with
  | zero => simp [MachineState.M]
  | succ len => simp only [MachineState.M]; omega

theorem expansion_le (aw off len cap : Nat)
    (active : aw ≤ cap) (span : len = 0 ∨ off+len ≤ 32*cap) :
    MachineState.M aw off len ≤ cap := by
  cases len with
  | zero => exact active
  | succ len => simp only [MachineState.M]; omega

theorem mstore (μ : MachineState) (off value : UInt256) (cap : Nat)
    (coherent : Coherent μ) (active : μ.activeWords.toNat ≤ cap)
    (span : off.toNat+32 ≤ 32*cap)
    (word : cap < UInt256.size) (host : 32*cap < 2^System.Platform.numBits) :
    Coherent (μ.mstore off value) ∧ (μ.mstore off value).activeWords.toNat ≤ cap := by
  have hb := expansion_bounds μ.activeWords.toNat off.toNat 32
  have hc := expansion_le μ.activeWords.toNat off.toNat 32 cap active (Or.inr span)
  have hn : (μ.mstore off value).activeWords.toNat =
      MachineState.M μ.activeWords.toNat off.toNat 32 :=
    toNat_ofNat_lit _ (hc.trans_lt word)
  have hm := MachineState.size_memory_mstore_of_pad μ off value (by omega)
  unfold Coherent at coherent ⊢
  rw [hm,hn]
  have hspan := hb.2 (by decide)
  constructor <;> omega

theorem mstore8 (μ : MachineState) (off value : UInt256) (cap : Nat)
    (coherent : Coherent μ) (active : μ.activeWords.toNat ≤ cap)
    (span : off.toNat+1 ≤ 32*cap)
    (word : cap < UInt256.size) (host : 32*cap < 2^System.Platform.numBits) :
    Coherent (μ.mstore8 off value) ∧ (μ.mstore8 off value).activeWords.toNat ≤ cap := by
  have hb := expansion_bounds μ.activeWords.toNat off.toNat 1
  have hc := expansion_le μ.activeWords.toNat off.toNat 1 cap active (Or.inr span)
  have hn : (μ.mstore8 off value).activeWords.toNat =
      MachineState.M μ.activeWords.toNat off.toNat 1 :=
    toNat_ofNat_lit _ (hc.trans_lt word)
  have hm := MachineState.size_memory_mstore8_of_pad μ off value (by omega)
  unfold Coherent at coherent ⊢
  rw [hm,hn]
  have hspan := hb.2 (by decide)
  constructor <;> omega

/-- Final full-word stores overhang the public RETURN buffers. -/
theorem deposit_item_span (i : Nat) (hi : i < 64) :
    184*i+160+32 ≤ 11784 ∧ 11784 ≤ 32*369 := by omega

theorem exit_item_span (i : Nat) (hi : i < 16) :
    68*i+52+32 ≤ 1104 ∧ 1104 ≤ 32*35 := by omega

/-- Source memory cost on rounded word capacity. -/
def cost (words : Nat) : Nat := 3*words + words*words/512

theorem cost_mono {a b : Nat} (h : a ≤ b) : cost a ≤ cost b := by
  have hm := Nat.mul_le_mul h h
  have hd := Nat.div_le_div_right hm (c := 512)
  unfold cost
  omega

/-- A finite monotone expansion history records each exact cost difference. -/
inductive Charges : Nat → Nat → Nat → Prop where
  | nil (a : Nat) : Charges a a 0
  | step {a b c total : Nat} : Charges a b total → b ≤ c →
      Charges a c (total+(cost c-cost b))

theorem telescopes {a b total : Nat} (h : Charges a b total) :
    a ≤ b ∧ total+cost a = cost b := by
  induction h with
  | nil => simp
  | step h order ih =>
    have hc := cost_mono order
    constructor <;> omega

theorem system_costs : cost 369 = 1372 ∧ cost 35 = 107 := by decide +kernel

#print axioms expansion_bounds
#print axioms expansion_le
#print axioms mstore
#print axioms mstore8
#print axioms deposit_item_span
#print axioms exit_item_span
#print axioms cost_mono
#print axioms telescopes
#print axioms system_costs
end Eip8282.Audit.Integrator.ReferenceMemoryCapacity

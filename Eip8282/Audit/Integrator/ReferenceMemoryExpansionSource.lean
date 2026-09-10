import Eip8282.Audit.Integrator.ReferenceCopyLogGas

/-! Literal single-span calculate_gas_extend_memory from EL0cc100eb190b64b23baba72dac0165652eaec252,
gas.py747-818 SHA25641d97e32f68585f99276f164b828b9091c112a05df31002594276d8e1feacc0c,
archived in direct-reference-amsterdam-gas-sources-20260910.json.
The source skips zero lengths, rounds before/after sizes, skips covered spans,
and subtracts costs only after the growth comparison. Byte indices and costs
are unbounded source Uint/Nat, not silently truncated UInt256 intermediates.
Alignment is a derived invariant of initialized handler histories; the raw
calculator is defined also on injected unaligned memory sizes. Python buffer
allocation and actual frame initialization remain audited boundaries. -/
namespace Eip8282.Audit.Integrator.ReferenceMemoryExpansionSource
open EvmYul
open ReferenceCopyLogGas (sourceCeil32)
set_option autoImplicit false
set_option maxHeartbeats 1600000

structure Expansion where
  cost : Nat
  bytes : Nat
  deriving DecidableEq, Repr

def memoryCost (size : Nat) : Nat :=
  let words := sourceCeil32 size/32
  words*3+words^2/512

def calculate (size off len : Nat) : Expansion :=
  if len = 0 then ⟨0,0⟩ else
    let before := sourceCeil32 size
    let after := sourceCeil32 (off+len)
    if after ≤ before then ⟨0,0⟩
    else ⟨memoryCost after-memoryCost before,after-before⟩

theorem ceil_eq (n : Nat) : sourceCeil32 n = 32*((n+31)/32) := by
  unfold sourceCeil32
  split <;> omega

private theorem rounded (words : Nat) : sourceCeil32 (32*words) = 32*words := by
  simp [sourceCeil32]

private theorem cost_rounded (words : Nat) : memoryCost (32*words) = ReferenceMemoryCapacity.cost words := by
  unfold memoryCost
  rw [rounded]
  simp [ReferenceMemoryCapacity.cost,Nat.mul_comm,pow_two]

/-- Exact source growth bytes and price match the action calculator on rounded
memory. Both output fields refer to the same expansion, including zero size. -/
theorem aligned (words off len : Nat) :
    (calculate (32*words) off len).bytes = 32*MachineState.M words off len-32*words ∧
    (calculate (32*words) off len).cost =
      ReferenceMemoryCapacity.cost (MachineState.M words off len)-ReferenceMemoryCapacity.cost words := by
  by_cases hz : len = 0
  · subst len
    simp [calculate,MachineState.M]
  · unfold calculate
    rw [if_neg hz,rounded,ceil_eq (off+len)]
    dsimp only
    by_cases covered : 32*((off+len+31)/32) ≤ 32*words
    · rw [if_pos covered]
      have cap : (off+len+31)/32 ≤ words := by omega
      have hm : MachineState.M words off len = words := by simp [MachineState.M,Nat.max_eq_left cap]
      simp [hm]
    · rw [if_neg covered]
      have cap : words ≤ (off+len+31)/32 := by omega
      have hm : MachineState.M words off len = (off+len+31)/32 := by simp [MachineState.M,Nat.max_eq_right cap]
      simp [hm,cost_rounded]

/-- A zero-length access neither allocates nor charges, at arbitrary offsets
and even on injected unaligned inputs. -/
theorem zero (size off : Nat) : calculate size off 0 = ⟨0,0⟩ := by simp [calculate]

#print axioms ceil_eq
#print axioms aligned
#print axioms zero
end Eip8282.Audit.Integrator.ReferenceMemoryExpansionSource

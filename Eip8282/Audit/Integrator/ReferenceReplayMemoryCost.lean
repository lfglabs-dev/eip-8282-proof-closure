import Eip8282.Audit.Integrator.ReferenceReplayCost
import Eip8282.Audit.Integrator.RuntimeMemoryCharges

/-! Synthetic total replay budget from the same raw effects and literal source
prices. Memory correspondence is derived from raw metadata, before Z admission.
The source resource ledger remains separate; 222 is a conservative proof budget.
No bound on the number of fee-loop iterations is imposed. -/
namespace Eip8282.Audit.Integrator.ReferenceReplayMemoryCost
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open RuntimeOpcodeScope RuntimeMemoryMonotone
open ReferenceStorageView ReferenceRuntimeView ReferenceSourceReadings ReferenceRuntimeReadings ReferenceMeterPath
open ReferenceExecutionLedger
open ReferenceMemoryCapacity (cost)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

private theorem predicted (pre : EVM.State) (op : Operation .EVM) (hop : op ∈ allowedOps) :
    (memoryExpansionCost.μᵢ' pre op).toNat =
      MachineState.M pre.activeWords.toNat (span pre op).1 (span pre op).2 := by
  simp only [allowedOps,List.mem_cons,List.not_mem_nil,or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl
    | exact toNat_ofNat_lit _ (expansion_fit pre.activeWords pre.stack[0]! pre.stack[1]!)
    | exact toNat_ofNat_lit _ (expansion_fit pre.activeWords pre.stack[0]! pre.stack[2]!)
    | exact toNat_ofNat_lit _ (expansion_fit_nat _ _ 32 pre.activeWords.val.isLt pre.stack[0]!.val.isLt (by decide +kernel))
    | exact toNat_ofNat_lit _ (expansion_fit_nat _ _ 1 pre.activeWords.val.isLt pre.stack[0]!.val.isLt (by decide +kernel))

/-- Both memory potentials concern this actual raw step, not a post-state
chosen independently to satisfy a desired charge. -/
theorem raw_memory {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {pre post : EVM.State} {parent : Parent} {v next : View}
    (allowed : op ∈ allowedOps) (related : Related parent v pre)
    (nextRelated : Related parent next post)
    (raw : EvmYul.step op arg pre = .ok post) :
    memoryExpansionCost pre op = cost (words next)-cost (words v) := by
  have hp := predicted pre op allowed
  have hm := RuntimeMemoryCharges.raw_expansion allowed raw
  change cost (memoryExpansionCost.μᵢ' pre op).toNat-cost pre.activeWords.toNat = _
  rw [hp,←hm,words_related related,words_related nextRelated]

theorem memory_component {op : Operation .EVM} {parent : Parent}
    {v next : View} {warm : Warm} {event : Event}
    (price : Price parent v warm next op event) :
    cost (words next)-cost (words v) ≤ eventWork event := by
  by_cases hs : op = .SSTORE
  · simp only [Price,if_pos hs] at price
    rw [price.1]
    exact Nat.zero_le _
  · simp only [Price,if_neg hs] at price
    obtain ⟨n,_,rfl⟩ := price
    simp only [eventWork]
    omega

/-- Opcode and memory charges are counted separately, so the coarse opcode
ratio never spends a memory summand twice. -/
theorem total_ratio {op : Operation .EVM} {arg : Option (UInt256 × Nat)}
    {pre post : EVM.State} {parent : Parent} {v next : View} {warm : Warm} {event : Event}
    (allowed : op ∈ allowedOps) (related : Related parent v pre)
    (nextRelated : Related parent next post)
    (raw : EvmYul.step op arg pre = .ok post)
    (price : Price parent v warm next op event) :
    C' pre op+memoryExpansionCost pre op ≤ 222*eventWork event := by
  have hb := ReferenceReplayCost.opcode_ratio pre related.stack.symm allowed price
  have hm := memory_component price
  rw [←raw_memory allowed related nextRelated raw] at hm
  omega

/-- This numerical transport applies to a work bound already derived from the
source ledger (transaction cap or SYSTEM grant). It does not produce that ledger
or turn the synthetic budget into gas actually supplied by Ethereum. -/
theorem word_fit {work : Nat} (bounded : work ≤ 30000000) :
    222*work+2301 < UInt256.size := by
  have small : 222*30000000+2301 < UInt256.size := by decide +kernel
  omega

#print axioms raw_memory
#print axioms memory_component
#print axioms total_ratio
#print axioms word_fit
end Eip8282.Audit.Integrator.ReferenceReplayMemoryCost

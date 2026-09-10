import Eip8282.Audit.Integrator.SystemExecutionResources
import Eip8282.Audit.Integrator.RuntimeMemoryCharges

/-! Exact source-formula memory differences on the same successful SYSTEM
execution, including its terminal RETURN. No independent capacity history or
intermediate span premise is supplied. Source interpreter replay is separate. -/
namespace Eip8282.Audit.Integrator.SystemMemoryResources
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall)
open RuntimeExecutionScope RuntimeMemoryCharges SystemExecutionResources
open ReferenceMemoryCapacity (cost cost_mono)
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

def Metered {image : Image} {steps cap outputBytes fuel : Nat} {pre : EVM.State}
    (h : Completed image steps cap outputBytes fuel pre) (total : Nat) : Prop :=
  ∃ initial,
    TraceCharges (D_J image.code ⟨0⟩) fuel pre h.trace (h.rem+2) h.exitState initial ∧
    total = initial + (cost h.finalState.activeWords.toNat - cost h.exitState.activeWords.toNat)

/-- Compose actual nonhalting charges and the actual terminal expansion. -/
theorem attach {image : Image} {steps cap outputBytes fuel : Nat} {pre : EVM.State}
    (h : Completed image steps cap outputBytes fuel pre) (hat : At image pre)
    (output_fit : outputBytes ≤ 32*cap) :
    ∃ total, Metered h total ∧ total + cost pre.activeWords.toNat = cost h.finalState.activeWords.toNat ∧
      h.finalState.activeWords.toNat ≤ cap ∧ total ≤ cost cap := by
  obtain ⟨initial,hc,he⟩ := from_runs hat h.run
  obtain ⟨len,hstack,hlen⟩ := h.output_operands
  have hop : h.exitState.stack.pop2 = some ([],UInt256.ofNat 0,len) := by rw [hstack]; rfl
  have hs : len.toNat = 0 ∨ (UInt256.ofNat 0).toNat + len.toNat ≤ 32*cap :=
    Or.inr (by change 0 + len.toNat ≤ 32*cap; omega)
  have hm := return_capacity h.halt.charge h.terminal hop h.exit_capacity hs
  have hmono := cost_mono hm.1
  have hcap := cost_mono hm.2
  refine ⟨initial+(cost h.finalState.activeWords.toNat-cost h.exitState.activeWords.toNat),
    ⟨initial,hc,rfl⟩,?_,hm.2,?_⟩ <;> omega

/-- Both capacities and the complete charge sum belong to the constructed
Deposit execution. The bound is conservative:400 words, not RETURN bytes. -/
theorem deposit (c : XiCall .deposit) (system : Deposit.callerWord c = sysW)
    (permission : c.env.perm = true) (gas : 2500000 ≤ c.gas.toNat)
    (fuel : 8502 ≤ c.fuel) :
    ∃ (h : Completed RuntimeExecutionScope.deposit 8500 400 11776 c.fuel c.entry) (total : Nat),
      Metered h total ∧ total = cost h.finalState.activeWords.toNat ∧
      h.finalState.activeWords.toNat ≤ 400 ∧ total ≤ 1512 := by
  obtain ⟨h⟩ := SystemExecutionResources.deposit c system permission gas fuel
  obtain ⟨total,hm,he,hcap,hb⟩ := attach h
    ⟨c.code_pinned,Or.inl RuntimeExecutionScope.deposit.entry⟩ (by decide)
  refine ⟨h,total,hm,?_,hcap,?_⟩
  · simpa [activeWords_entry,cost] using he
  · exact hb

theorem exit (c : XiCall .exit) (system : Exit.callerWord c = sysW)
    (permission : c.env.perm = true) (gas : 250000 ≤ c.gas.toNat)
    (fuel : 802 ≤ c.fuel) :
    ∃ (h : Completed RuntimeExecutionScope.exit 800 40 1088 c.fuel c.entry) (total : Nat),
      Metered h total ∧ total = cost h.finalState.activeWords.toNat ∧
      h.finalState.activeWords.toNat ≤ 40 ∧ total ≤ 123 := by
  obtain ⟨h⟩ := SystemExecutionResources.exit c system permission gas fuel
  obtain ⟨total,hm,he,hcap,hb⟩ := attach h
    ⟨c.code_pinned,Or.inl RuntimeExecutionScope.exit.entry⟩ (by decide)
  refine ⟨h,total,hm,?_,hcap,?_⟩
  · simpa [activeWords_entry,cost] using he
  · exact hb

#print axioms attach
#print axioms deposit
#print axioms exit
end Eip8282.Audit.Integrator.SystemMemoryResources

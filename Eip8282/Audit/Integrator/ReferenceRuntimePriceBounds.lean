import Eip8282.Audit.Integrator.ReferenceCopyLogGas
import Eip8282.Audit.Integrator.RuntimeMemoryCharges

/-! Source-formula ordinary prices bounded using the same actual step's memory
capacity. COPY/LOG lengths come from accepted execution, including length zero;
no source-offset bound or fixed iteration count is imposed. Initial resource
and capacity producers, source gas interpretation, and SSTORE remain separate.
-/
namespace Eip8282.Audit.Integrator.ReferenceRuntimePriceBounds
open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open RuntimeExecutionScope RuntimeMemoryMonotone
open ReferenceCopyLogGas
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

private theorem copy_bound {len cap : Nat} (h : len ≤ 32*cap) :
    copyCost len ≤ max 2100 (375+256*cap) := by
  have hc : (len+31)/32 ≤ cap := by omega
  unfold copyCost
  omega

private theorem log_bound {len cap : Nat} (h : len ≤ 32*cap) :
    logCost len ≤ max 2100 (375+256*cap) := by
  unfold logCost
  omega

/-- Every actual accepted runtime instruction except SSTORE supplies its price
and a uniform capacity-dependent bound. The post-cap is supplied by the
initial-energy producer at the full-trace consumer. -/
theorem accepted {image : Image} {pre mid post : EVM.State} {fuel gasCost cap : Nat}
    (hat : At image pre)
    (hz : Z (D_J image.code ⟨0⟩) (decodeAt pre).1 pre = .ok (mid,gasCost))
    (hs : StepOk fuel gasCost (decodeAt pre) mid post)
    (notStore : (decodeAt pre).1 ≠ .SSTORE)
    (capacity : post.activeWords.toNat ≤ cap) (warm : Bool) :
    ∃ n, ordinaryCost (decodeAt pre).1 warm pre.stack = some n ∧
      n ≤ max 2100 (375+256*cap) := by
  have he := RuntimeMemoryCharges.accepted_expansion hat hz hs
  by_cases hc : (decodeAt pre).1 = .CALLDATACOPY
  · have hz' : Z (D_J image.code ⟨0⟩) .CALLDATACOPY pre = .ok (mid,gasCost) := by
      simpa only [hc] using hz
    obtain ⟨rest,dest,source,len,pop,shape,price⟩ := accepted_copy hz' warm
    have hex : post.activeWords.toNat = MachineState.M pre.activeWords.toNat dest.toNat len.toNat := by
      simpa only [hc,span,shape,List.getElem!_cons_zero,List.getElem!_cons_succ] using he
    have hb : len.toNat ≤ 32*cap := by
      by_cases hzlen : len.toNat = 0
      · omega
      · have hm := (ReferenceMemoryCapacity.expansion_bounds
          pre.activeWords.toNat dest.toNat len.toNat).2 (by omega)
        rw [← hex] at hm
        omega
    exact ⟨copyCost len.toNat,by rw [hc]; exact price,copy_bound hb⟩
  · by_cases hl : (decodeAt pre).1 = .LOG0
    · have hz' : Z (D_J image.code ⟨0⟩) .LOG0 pre = .ok (mid,gasCost) := by
        simpa only [hl] using hz
      obtain ⟨rest,off,len,pop,shape,price⟩ := accepted_log hz' warm
      have hex : post.activeWords.toNat = MachineState.M pre.activeWords.toNat off.toNat len.toNat := by
        simpa only [hl,span,shape,List.getElem!_cons_zero,List.getElem!_cons_succ] using he
      have hb : len.toNat ≤ 32*cap := by
        by_cases hzlen : len.toNat = 0
        · omega
        · have hm := (ReferenceMemoryCapacity.expansion_bounds
            pre.activeWords.toNat off.toNat len.toNat).2 (by omega)
          rw [← hex] at hm
          omega
      exact ⟨logCost len.toNat,by rw [hl]; exact price,log_bound hb⟩
    · obtain ⟨n,hn,hbound⟩ := ReferenceOrdinaryGas.defined_bound warm
        ⟨opcode_allowed hat,hl,hc⟩ notStore
      exact ⟨n,by simp only [ordinaryCost,if_neg hc,if_neg hl]; exact hn,
        hbound.trans (Nat.le_max_left _ _)⟩

#print axioms accepted
end Eip8282.Audit.Integrator.ReferenceRuntimePriceBounds
